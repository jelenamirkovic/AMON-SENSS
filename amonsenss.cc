/*
#
# Copyright (C) 2018 University of Southern California.
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License,
# version 2, as published by the Free Software Foundation.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along
# with this program; if not, write to the Free Software Foundation, Inc.,
# 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
#
*/

#include <signal.h>
#include <stdio.h>
#include <iostream>
#include <algorithm>
#include <fstream>
#include <sched.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <errno.h>
#include <sys/poll.h>
#include <netinet/in_systm.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <netinet/udp.h>
#include <netinet/ip6.h>
#include <net/ethernet.h>
#include <sys/time.h>
#include <time.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <monetary.h>
#include <locale.h>
#include <regex.h>
#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include <cmath>
#include <pcap.h>
#include <dirent.h>


// Limits
#include<bits/stdc++.h> 

#include "utils.h"


using namespace std;


// Global variables
bool resetrunning = false;
char saveline[MAXLINE];
int numattack = 0;

// We store delimiters in this array
int* delimiters;

bool sim_filter = false;

unsigned int max_shufflelen = 0;
unsigned int max_shuffleoci = 0;

map<unsigned int, struct shuffle_cell> memshuffle;
extern vector<int> samplingrates;
int shuffle_index = 0;

// Something like strtok but it doesn't create new
// strings. Instead it replaces delimiters with 0
// in the original string
int parse(char* input, char delimiter, int** array)
{
  int pos = 0;
  memset(*array, 255, AR_LEN);
  int len = strlen(input);
  int found = 0;
  for(int i = 0; i<len; i++)
    {
      if (input[i] == delimiter)
	{
	  (*array)[pos] = i+1;
	  input[i] = 0;
	  pos++;
	  found++;
	}
    }
  return found;
}

// Variables/structs needed for detection
struct cell
{
  long int *databrick_p;	 // databrick volume
  double *databrick_s;           // databrick symmetry
  long int *databrick_sent;      // databrick pkts sent
  long int *databrick_rec;       // databrick pkts recvd
  unsigned int *wfilter_p;	 // volume w filter 
  int *wfilter_s;	         // symmetry w filter 
};

// Should we require destination prefix
bool noorphan = false;

// How many service ports are there
int numservices = 0;

// Save all flows for a given time slot
map<long, time_flow*> timeflows;


// We have multiple layers of stats - NUMB of
// them - this reduces false positives

// These are the bins where we store stats
cell cells[NUMB][QSIZE];
int cfront = 0;
int crear = 0;
bool cempty = true;

// Samples of flows for signatures
sample samples[NUMB];

// Signatures per bin
stat_r *signatures[NUMB];

// Is the bin abnormal or not
int *is_abnormal[NUMB];

// Did we detect an attack in a given bin
int *is_attack[NUMB];

// When we detected the attack
unsigned long* detection_time[NUMB];

// Did we complete training
bool training_done = false;
bool shuffle_done = false;
int BRICK_FINAL = 0;

int shuffled = 0;
int trained = 0;
const int MAX_SHUFFLES = 100;

// Current time
double curtime = 0;
double lasttime = 0;
double lastlogtime = 0;
double lastbintime = 0;

// Verbose bit
int verbose = 0;

double firsttime = 0;       // Beginning of trace 
long freshtime = 0;         // Where we last ended when processing data 
double firsttimeinfile = 0; // First time in the current file
long int allflows = 0;      // How many flows were processed total
long int processedflows = 0;// How many flows were processed this second
long updatetime = 0;        // Time of last stats update
long statstime = 0;         // Time when we move the stats to history 
char filename[MAXLINE];     // A string to hold filenames
struct timespec last_entry;

// Is this pcap file or flow file? Default is flow
bool is_pcap = false;
bool is_live = false;
bool is_nfdump = false;
bool is_flowride = false;

// Serialize access to statistics
pthread_mutex_t cells_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t samples_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t cnt_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t rst_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t final_lock = PTHREAD_MUTEX_INITIALIZER;

// Types of statistics. If this changes, update the entire section 
enum period{cur, hist};
enum type{n, avg, ss};
enum dim{vol, sym};

 // historical and current stats for attack detection
double* stats[NUMB][2][3][2];
double* cusum[NUMB][2];

// Parameters from as.config
map<string,double> parms;

// Keeping track of procesed flows
long int processedbytes = 0;
int nl = 0;
int l = 0;
int mal = 0;
int inserts = 0;
int cinserts = 0;

// Trim strings 
char *trim(char *str)
{
    size_t len = 0;
    char *frontp = str;
    char *endp = NULL;

    if( str == NULL ) { return NULL; }
    if( str[0] == '\0' ) { return str; }

    len = strlen(str);
    endp = str + len;

    while( isspace((unsigned char) *frontp) ) { ++frontp; }
    if( endp != frontp )
      {
	while( isspace((unsigned char) *(--endp)) && endp != frontp ) {}
      }

    if( str + len - 1 != endp )
      *(endp + 1) = '\0';
    else if( frontp != str &&  endp == frontp )
      *str = '\0';

    endp = str;
    if( frontp != str )
    {
      while( *frontp ) { *endp++ = *frontp++; }
      *endp = '\0';
    }

    return str;
}

// Parse configuration file and load into parms
void
parse_config(map <string,double>& parms)
{
  char *s, buff[256];
  FILE *fp = fopen ("amonsenss.config", "r");
  if (fp == NULL)
  {
    cout <<"Config file amonsenss.config does not exist. Please include it and re-run.. \n";
    exit (0);
  }
  cout << "Reading config file amonsenss.config ...";
  while ((s = fgets(buff, sizeof buff, fp)) != NULL)
  {
        // Skip blank lines and comment lines 
        if (buff[0] == '\n' || buff[0] == '#')
          continue;

	// Look for = sign and abort if that does not
	// exist
	char name[MAXLINE], value[MAXLINE];
	int found = -1;
	int i = 0;
	for(i=0; i<strlen(buff); i++)
	  {
	    if (buff[i] == '=')
	      {
		strncpy(name,buff, i);
		name[i] = 0;
		found = i;
	      }
	    else if((buff[i] == ' ' || buff[i] == '\n') && found >= 0)
	      {
		strncpy(value,buff+found+1,i-found-1);
		value[i-found-1] = 0;
		break;
	      }
	  }
	if (i > 0 && found > -1)
	  {
	    strncpy(value,buff+found+1,i-found-1);
	    value[i-found-1] = 0;
	  }
	if (found == -1)
	  continue;
	trim(name);
	trim(value);
	cout<<"Parm "<<name<<" val "<<value<<endl;
	parms.insert(pair<string,double>(name,strtod(value,0)));
  }
  fclose (fp);
}


// Check if the signature is subset or matches
// exactly the slot where anomaly was found.
// For example, if a source port's traffic was
// anomalous we have to have that source port in the
// signature
bool compliantsig(int i, flow_t sig)
{
  int loc = int(i/BRICK_FINAL);
  switch (loc)
    {
    case 0:
    case 1:
      return (sig.dst != 0 && (sig.dport != -1 || sig.sport != -1 || sig.proto == ICMP));
    case 2:
    case 4:
    case 5:
      return (sig.dst != 0 && (sig.sport != -1|| sig.proto == ICMP));
    case 3:
    case 6:
    case 7:
      return (sig.dst != 0 && (sig.dport != -1 || sig.proto == ICMP));
    case 8:
    case 9:
    case 10:
    case 11:
    case 12:
    case 13:
    case 14:
    case 15:
      return (sig.dst != 0 && sig.flags != 0);
    default:
      return false;
    }
}


void clearSamples(int index, int id)
{
  flow_t key;
  pthread_mutex_lock(&samples_lock);
  for (int s=1; s<NF; s++)
    {
      samples[id].bins[index].flows[s].flow = key;
      samples[id].bins[index].flows[s].len = 0;
      samples[id].bins[index].flows[s].oci = 0;
    }
  pthread_mutex_unlock(&samples_lock);
}

// Add a flow to the samples bin
void addSample(int index, flow_p* f, int way, int id)
{
  // Create some partial signatures for this flow, like src-dst combination,
  // src-sport, etc. Don't allow just protocol
  // Don't add samples for flags separately since they are already going
  // to separate bins
  for (int s=1; s<NF-8; s++)
    {
      pthread_mutex_lock(&samples_lock);
      
      flow_t k;
      k.proto = f->flow.proto;
      if ((s & 8) > 0)
	k.src = f->flow.src;
      if ((s & 4) > 0 && isservice(f->flow.sport))
	k.sport = f->flow.sport;
      if ((s & 2) > 0)
	k.dst = f->flow.dst;
      if ((s & 1) > 0 && isservice(f->flow.dport))
	k.dport = f->flow.dport;

      if (way == LHOST || way == LPREF || way == LHFPORT || way == LHLPORT || way == LPFPORT || way == LPLPORT
	  || way == LHSYN || way == LPSYN || way == LHSYNACK || way == LPSYNACK || way == LHRST || way == LPRST)
	{
	  k.dst = f->flow.dst;
	  if (way == LPREF || way == LPFPORT || way == LPLPORT || way == LPSYN || way == LPSYNACK || way == LPRST)
	    k.dst &= 0xffffff00;
	}
      if (way == FPORT || way == LHFPORT || way == LPFPORT)
	k.sport = f->flow.sport;
      if (way == LPORT || way == LHLPORT || way == LPLPORT) 
	k.dport = f->flow.dport;
      if (way >= LHSYN)
	k.flags = f->flow.flags;
      
      // Overload len so we can track frequency of contributions
      // Insert sample if it does not exist
      if (samples[id].bins[index].flows[s].flow == k)
	{
	  // Else increase contributions of this signature wrt symmetry
	  samples[id].bins[index].flows[s].len += abs(f->oci);
	  samples[id].bins[index].flows[s].oci += f->oci;
	}
      else	
	{
	  // Boyer Moore to find signatures that cover the most flows
	  if (empty(samples[id].bins[index].flows[s].flow))
	    {
	      samples[id].bins[index].flows[s].flow = k;
	      samples[id].bins[index].flows[s].len = abs(f->oci);
	      samples[id].bins[index].flows[s].oci = f->oci;
	    }
	  else
	    {
	      int olen = samples[id].bins[index].flows[s].len;
	      samples[id].bins[index].flows[s].len -= abs(f->oci);
	      int nlen = samples[id].bins[index].flows[s].len;
	      
	      // Replace this signature if there's another one,
	      // which covers more
	      if (samples[id].bins[index].flows[s].len < 0)
		{
		  samples[id].bins[index].flows[s].flow = k;
		  samples[id].bins[index].flows[s].len = abs(f->oci);
		  samples[id].bins[index].flows[s].oci = f->oci;
		}
	    }
	}
      pthread_mutex_unlock(&samples_lock);
    }
} 


// Does this flow match the given signature
int match(flow_t flow, flow_t sig)
{
  if (flow.proto != sig.proto && sig.proto != 0)
    {
      return 0;
    }
  if (empty(sig))
    {
      return 0;
    }
  if ((flow.src == sig.src || sig.src == 0) &&
      (flow.sport == sig.sport || sig.sport == -1) &&
      (flow.dst == sig.dst || sig.dst == 0) &&
      (flow.dport == sig.dport || sig.dport == -1) &&
      ((flow.flags & sig.flags) > 0 || sig.flags == 0))
    {
      return 1;
    }
  else
    {
      return 0;
    }
}

// Is this timestamp within the range, which we expect in a given input file
// this check is only for flow files, since they can have some very outdated flows
int malformed(double timestamp)
{
  // Give some space here in case we're off and have straggler flows
  if (timestamp < firsttimeinfile - 2*parms["file_interval"] || (parms["file_interval"] > 0 && timestamp > firsttimeinfile +
				      2*parms["file_interval"]))
    return 1;
  return 0;
}

// Function to detect values higher than mean + parms[num_std] * stdev 
double abnormal(int type, int index, cell* c, int id)
{
  // Look up std and mean
  double mean = stats[id][hist][avg][type][index];
  double std = sqrt(stats[id][hist][ss][type][index]/
		    (stats[id][hist][n][type][index]-1));
  // Look up current value
  double data;
  
  double ao = stats[id][cur][avg][type][index];

  if (type == vol)
    data = c->databrick_p[index];
  else
    data = c->databrick_s[index];

  // Project how avg would look if we add current value to it
  double ddata = stats[id][cur][avg][type][index] +
    (double)(data - stats[id][cur][avg][type][index])/(stats[id][cur][n][type][index]+1);

  data = ddata;
  
  // If we don't have enough samples return 0
  if (stats[id][hist][n][type][index] <
      parms["min_train"]*MIN_SAMPLES)
    return 0;

  // calculate cusum
  double tmp = cusum[id][type][index] + data - mean - 3*std;
  if (tmp < 0)
    tmp = 0;
  
  double rto = tmp/(std+1);

  if (rto > 0)
    return rto;
  else
    return 0;
}

// Print alert into the alerts file
void print_alert(int i, cell* c, int na, int id)
{
  int BRICKF= BRICK_UNIT + id*13;
  int pos = int(i/BRICKF);

  // 1 - local ip, 2 - local pref /24, 3 - foreign port, 4 - local port,
  // 5 - localip+forport, 6 - localip+localport, 7 - localpref+forport, 8 - localpref+localport
  // 9 - localip+syn, 10 - localpref+syn, 11 - localip+synack, 12 - localpref+synack, 13 - localip+rst, 14 - localpref+rst
  
  double diff = curtime - lasttime;
  if (diff < 1)
    diff = 1;
  double avgv = stats[id][hist][avg][vol][i];
  double stdv = sqrt(stats[id][hist][ss][vol][i]/(stats[id][hist][n][vol][i]-1));
  double avgs = stats[id][hist][avg][sym][i];
  double stds = sqrt(stats[id][hist][ss][sym][i]/(stats[id][hist][n][sym][i]-1));
  long int rate = c->databrick_p[i] - avgv - parms["num_std"]*stdv;
  long int roci = c->databrick_s[i] - avgs - parms["num_std"]*stds;
  
  // Write the start of the attack into alerts
  ofstream out;
  
  if (abs(roci) < parms["min_oci"])
    return;
  
  if (empty(signatures[id][i].sig))
    return;
  
  u_int32_t ip;
  unsigned short port;

  int matched = 1;
  for (int y = 0; y < NUMB; y++)
    {
      if (y == id)
	continue;
      for (int j = 0; j < NUMF*(BRICK_UNIT + y*13); j++)
	{
	  if(is_attack[y][j] && !empty(signatures[y][j].sig))
	    {
	      // Say we have a match if we match the dst of the signature in a layer
	      if (signatures[y][j].sig.dst == signatures[id][i].sig.dst)
		{
		  matched++;
		  break;
		}
	    }
	}
    }
  
  pthread_mutex_lock(&cnt_lock);

  
  char alertfile[MAXLINE];
  sprintf(alertfile, "alerts.txt");

  // Only print alerts that have matched all layers
  if (matched == NUMB)
    {
      out.open(alertfile, std::ios_base::app); 
      out<<na<<" "<<i/BRICKF<<" "<<(long)curtime<<" ";
      out<<"START "<<i<<" "<<abs(rate);
      out<<" "<<abs(roci)<<" ";
      out<<printsignature(signatures[id][i].sig)<<endl;
      out.close();
    }
  
  pthread_mutex_unlock(&cnt_lock);
  
  // Check if we should rotate file, if it exceeds 10MB
  ifstream in(alertfile, std::ifstream::ate | std::ifstream::binary);
  if (in.tellg() > 10000000)
    system("./rotate");
}

void alert_ready(cell* c, int bucket, int id)
{
  double volf = c->wfilter_p[bucket];
  double volb = c->databrick_p[bucket];
  if (volb == 0)
    volb = 1;
  double avgs = stats[id][hist][avg][sym][bucket];
  double stds = sqrt(stats[id][hist][ss][sym][bucket]/(stats[id][hist][n][sym][bucket]-1));
  double symf = abs(c->wfilter_s[bucket]);
  double symb = abs(c->databrick_s[bucket]) - (abs(avgs) + parms["num_std"]*abs(stds));
  if (symb < 0)
    symb = symf;
  double data = abs(c->databrick_s[bucket]);
  if (symb == 0)
    symb = 1;
  if (symf/symb >= parms["filter_thresh"])
    {
      pthread_mutex_lock(&cnt_lock);
      int na = numattack++;
      pthread_mutex_unlock(&cnt_lock);
      print_alert(bucket, c, na, id);
    }

  is_attack[id][bucket] = false;
  detection_time[id][bucket] = 0;
  clearSamples(bucket, id);
}

void checkReady(int bucket, cell* c, int id)
{  
  if (signatures[id][bucket].nm < MM)
    {
      strcpy(signatures[id][bucket].matches[signatures[id][bucket].nm++], saveline);

      if (signatures[id][bucket].nm == MM)
	{
	  alert_ready(c, bucket, id);
	}
    }
}

// Should we filter this flow?
bool shouldFilter(int bucket, flow_t flow, cell* c, int id)
{
  if (!empty(signatures[id][bucket].sig) && match(flow,signatures[id][bucket].sig))
    return true;
  else
    return false;
}

long votedtime = 0;
int votes = 0;
const int MINVOTES = 1; // setting this to higher number may help if flows are very perturbed

void findBestSignature(double curtime, int i, cell* c, int id)
{
  flow_t bestsig;
  int oci = 0;
  int maxoci = 0;
  double avgs = stats[id][hist][avg][sym][i];
  double stds = sqrt(stats[id][hist][ss][sym][i]/(stats[id][hist][n][sym][i]-1));
  int totoci = c->databrick_rec[i]; 
  
  // Go through candidate signatures
  for (int s=1; s<NF; s++)
    {
      if (empty(samples[id].bins[i].flows[s].flow))
	continue;

      double candrate = abs((double)samples[id].bins[i].flows[s].oci);

      if (!compliantsig(i, samples[id].bins[i].flows[s].flow))
	{
	  if (verbose)
	    cout<<"non compliant SIG: "<<i<<" for slot "<<s<<" candidate "<<printsignature(samples[id].bins[i].flows[s].flow)<<" v="<<samples[id].bins[i].flows[s].len<<" o="<<samples[id].bins[i].flows[s].oci<<" toto="<<totoci<<" candrate "<<candrate<<" divided "<<candrate/totoci<<endl;
	    continue;
	}

      // Print out each signature for debugging
      if (verbose)
	cout<<"SIG: "<<i<<" for slot "<<s<<" candidate "<<printsignature(samples[id].bins[i].flows[s].flow)<<" v="<<samples[id].bins[i].flows[s].len<<" o="<<samples[id].bins[i].flows[s].oci<<" toto="<<totoci<<" candrate "<<candrate<<" divided "<<candrate/totoci<<endl;
      
      // Potential candidate
      if (candrate/totoci > parms["filter_thresh"] && samples[id].bins[i].flows[s].oci > parms["min_oci"])
	{
	  // Is it a more specific signature?
	  if (bettersig(samples[id].bins[i].flows[s].flow, bestsig))
	    {
	      if (verbose)
		cout<<"SIG: changing to "<< printsignature(samples[id].bins[i].flows[s].flow)<<endl;
	      
	      bestsig = samples[id].bins[i].flows[s].flow;
	      oci = candrate;
	    }
	}
    }
  if (verbose)
    cout<<"SIG: "<<i<<" best sig "<<printsignature(bestsig)<<" Empty? "<<empty(bestsig)<<" oci "<<maxoci<<" out of "<<totoci<<endl;
  
  // Remember the signature if it is not empty and can filter
  // at least filter_thresh flows in the sample
  if (!empty(bestsig))
    {
      if (verbose)
	cout<<curtime<<" ISIG: "<<i<<" volume "<<c->databrick_p[i]<<" oci "<<c->databrick_s[i]<<" installed sig "<<printsignature(bestsig)<<endl;

      // insert signature and reset all the stats
      if (sim_filter)
	{
	  signatures[id][i].sig = bestsig;
	  signatures[id][i].vol = 0;
	  signatures[id][i].oci = 0;
	  signatures[id][i].nm = 0;	  
	}
      
      // Clear samples
      clearSamples(i, id);
    }
  // Did not find a good signature
  // drop the attack signal and try again later
  else
    {
      if (verbose)
	cout << "AT: Did not find good signature for attack "<<
	  " on bin "<<i<<" best sig "<<empty(bestsig)<<
	  " coverage "<<(float)oci/totoci<<" thresh "<<
	  parms["filter_thresh"]<<endl;
      is_attack[id][i] = false;
    }
}

void instant_detect(cell* c, double ltime, int i, int id)
{
  c->databrick_s[i] = (double)c->databrick_rec[i]/(c->databrick_sent[i] + 1);

  double avgv = stats[id][hist][avg][vol][i];
  double stdv = sqrt(stats[id][hist][ss][vol][i]/(stats[id][hist][n][vol][i]-1));
  double avgs = stats[id][hist][avg][sym][i];
  double stds = sqrt(stats[id][hist][ss][sym][i]/(stats[id][hist][n][sym][i]-1));
  int volume = c->databrick_p[i];
  int asym = c->databrick_s[i];

  if (!is_attack[id][i])
    {
      // If both volume and asymmetry are abnormal and training has completed
      double a = abnormal(vol, i, c, id);
      double b = abnormal(sym, i, c, id);
      int volume = c->databrick_p[i];
      int asym = c->databrick_s[i];

      if (training_done && a && b)
	{
	  double aavgs = abs(avgs);
	  if (aavgs == 0)
	    aavgs = 1;
	  double d = abs(abs(asym) - abs(avgs) - parms["num_std"]*abs(stds))/aavgs;
	  
	  is_abnormal[id][i] = a+b;
	  if (is_abnormal[id][i] > int(parms["attack_high"]))
	    is_abnormal[id][i] = int(parms["attack_high"]); 
	  
	  if (verbose && is_abnormal[id][i]) 
	    cout<<std::fixed<<ltime<<" id="<<id<<" abnormal for "<<i<<" points "<<is_abnormal[id][i]<<" oci "<<c->databrick_s[i]<<" ranges " <<avgs<<"+-"<<stds<<", vol "<<c->databrick_p[i]<<" ranges " <<avgv<<"+-"<<stdv<<" over mean "<<d<<" a "<<a<<" b "<<b<<" cusum thresh " << parms["cusum_thresh"]<<endl;

	  // If abnormal score is above attack_low
	  // and oci is above MIN_OCI
	  if (is_abnormal[id][i] >= int(parms["attack_low"])
	      && !is_attack[id][i]) 
	    {
	      // Signal attack detection 
	      is_attack[id][i] = true;

	      detection_time[id][i] = ltime;
	      if (verbose)
		cout<<"id="<<id<<" AT: Attack detected on "<<i<<" but not reported yet vol "<<c->databrick_p[i]<<" oci "<<c->databrick_s[i]<<" min oci "<<int(parms["min_oci"])<<endl;
	      
	      // Find the best signature
	      findBestSignature(ltime, i, c, id);
	    }
	}
    }
}


// After finding big hitters we allocate all memory
void malloc_all(int index, int BRICKF)
{
  for(int i=0; i<QSIZE; i++)
    { 
      cells[index][i].databrick_p = (long int*) malloc(BRICKF*sizeof(long int));
      cells[index][i].databrick_sent = (long int*) malloc(BRICKF*sizeof(long int));
      cells[index][i].databrick_rec = (long int*) malloc(BRICKF*sizeof(long int));
      cells[index][i].databrick_s = (double*) malloc(BRICKF*sizeof(long int));
      cells[index][i].wfilter_p = (unsigned int*) malloc(BRICKF*sizeof(unsigned int));
      cells[index][i].wfilter_s = (int*) malloc(BRICKF*sizeof(int));
    }
  signatures[index] = (stat_r*) malloc(BRICKF*sizeof(stat_r));
  is_abnormal[index] = (int*) malloc(BRICKF*sizeof(int));
  memset(is_abnormal[index], 0, BRICKF*sizeof(int));
  is_attack[index] = (int*) malloc(BRICKF*sizeof(int));
  memset(is_attack[index], 0, BRICKF*sizeof(int));  
  detection_time[index] = (unsigned long*) malloc(BRICKF*sizeof(unsigned long));
  memset(detection_time[index], 0, BRICKF*sizeof(unsigned long));  
  
  for(int i=0; i<2;i++)
    for(int j=0; j<3; j++)
      for(int k=0; k<2; k++)
	{
	  stats[index][i][j][k] = (double*) malloc(BRICKF*sizeof(double));
	  memset(stats[index][i][j][k], 0, BRICKF*sizeof(double));
	}

   for(int i=0; i<2;i++)
     cusum[index][i] =  (double*) malloc(BRICKF*sizeof(double));
   
   samples[index].bins = (sample_p*) malloc(BRICKF*sizeof(sample_p));
}

int FRACTION = 10000;

// This function finds big hitters (e.g., IPs, ports) and these
// are stored in a cell by themselves
void shuffle(unsigned int addr, int len, int oci, unsigned int curtime)
{
  if (memshuffle.find(addr) == memshuffle.end())
    {
      shuffle_cell c;
      c.len = len;
      c.oci = oci;
      memshuffle[addr] = c;
    }
  else
    {
      memshuffle[addr].len += len;
      memshuffle[addr].oci += oci;
    }
  if (memshuffle[addr].len > max_shufflelen)
    max_shufflelen = memshuffle[addr].len;
  if (memshuffle[addr].oci > max_shuffleoci)
    max_shuffleoci = memshuffle[addr].oci;

  // If there are too many, delete all that are
  // lower than small fraction of the max
  if (memshuffle.size() > BRICK_UNIT)
    {
      for (auto mit=memshuffle.begin(); mit != memshuffle.end(); )
	{
	  auto it = mit;
	  if (mit->second.len < max_shufflelen/FRACTION && mit->second.oci < max_shuffleoci/FRACTION)
	    {
	      mit++;
	      memshuffle.erase(it);
	    }
	  else
	    {
	      mit++;
	    }
	}
      shuffled++;
      if (shuffled > MAX_SHUFFLES && !shuffle_done)
	{
	  pthread_mutex_lock(&final_lock);
	  
	  shuffle_index = memshuffle.size();
	  int index = 0;
	  for (auto mit=memshuffle.begin(); mit != memshuffle.end(); mit++)
	    mit->second.index = index++;
	  
	  BRICK_FINAL = shuffle_index*NUMF+BRICK_DIMENSION;

	  // Malloc everything
	  for (int index = 0; index < NUMB; index++)
	    malloc_all(index, BRICK_FINAL + index*13*NUMF);
	  
	  shuffle_done = true;

	  pthread_mutex_unlock(&final_lock);
	}
    }
    if (curtime - firsttime >= parms["min_train"] && !shuffle_done)
    {
      pthread_mutex_lock(&final_lock);
      
      shuffle_index = memshuffle.size();
      int index = 0;
      for (auto mit=memshuffle.begin(); mit != memshuffle.end(); mit++)
	mit->second.index = index++;
      
      BRICK_FINAL = shuffle_index*NUMF+BRICK_DIMENSION;
      
      // Malloc everything
      for (int index = 0; index < NUMB; index++)
	malloc_all(index, BRICK_FINAL + index*13*NUMF);
      
      shuffle_done = true;
      
      pthread_mutex_unlock(&final_lock);
    }
}


// Main function, which processes each flow
void
amonProcessing(flow_t flow, int len, double start, double end, int oci)
{
  // Detect if the flow is malformed and reject it
  if (malformed(end))
    {
      mal++;
      return;
    }
  // Detect if it is UDP for port 443 or 4500 or 4501 or 80
  // and don't use it. It's most likely legitimate.
  if (flow.proto == UDP && ((isspecial(flow.sport) && !isservice(flow.dport)) ||
			    (isspecial(flow.dport) && !isservice(flow.sport))))
    return;

  if (flow.proto == ICMP)
    {
      flow.sport = -2;
      flow.dport = -2;
    }

  if (curtime == 0)
    curtime = end;
  if ((unsigned long)end > (unsigned long)curtime)
    {
      if (votes == 0)
	votedtime = (int)end;
      if ((int)end == votedtime)
	votes++;
      else
	votes--;
      if (votes >= MINVOTES)
	{
	  curtime = end;
	  votedtime = 0;
	  votes = 0;
	}
    }

  if (lasttime == 0)
    lasttime = curtime;

  flow_p fp(start, end, len, oci, flow);
  
  for (int index = 0; index < NUMB; index++)
    {

      pthread_mutex_lock(&final_lock);

      // This makes sure that bins in each layer are a little different
      // to reduce collisions
      int BRICKF = BRICK_FINAL + index*13*NUMF;
      pthread_mutex_unlock(&final_lock);

      int BRICKU = BRICK_UNIT+index*13;

      // indices for the databrick 
      int d_bucket = -1, s_bucket = -1;
      
      cell *c = &cells[index][crear];

      int is_filtered = false;

      if (!shuffle_done)
	{
	  if (flow.dlocal)
	    shuffle(flow.dst, len, oci, curtime);
	  else
	    shuffle(flow.src, len, oci, curtime);
	  return;
	}
      
      if (sim_filter)
	{
	  for (int way = LHOST; way <= LPRST; way++) // SERV is included in CLI
	    {
	      // Find buckets on which to work
	      if (way == LHOST || way == LPREF || way >= LHSYN)
		{
		  if (flow.dlocal)
		    {
		      d_bucket = myhash(flow.dst, 0, way, BRICKU);
		    		      
		      if (shouldFilter(d_bucket, flow, c, index))
			{
			  is_filtered = true;
			  c->wfilter_p[d_bucket] += len;
			  c->wfilter_s[d_bucket] += oci;
			  checkReady(d_bucket, c, index);
			}
		    }
		}
	      else if (way == FPORT) 
		{
		  if (flow.dlocal)
		    {
		      // traffic from FPORT
		      s_bucket = myhash(0, flow.sport, way, BRICKU);
		      if (shouldFilter(s_bucket, flow, c, index))
			{
			  is_filtered = true;
			  c->wfilter_p[s_bucket] += len;
			  c->wfilter_s[s_bucket] += oci;
			  checkReady(s_bucket, c, index);
			}
		    }
		}
	      else if (way == LPORT)
		{
		  if (flow.dlocal)
		    {
		      // traffic to LPORT
		      d_bucket = myhash(0, flow.dport, way, BRICKU);
		      if (shouldFilter(d_bucket, flow, c, index))
			{
			  is_filtered = true;
			  c->wfilter_p[d_bucket] += len;
			  c->wfilter_s[d_bucket] += oci;
			  checkReady(d_bucket, c, index);
			}
		    }
		}
	      else if (way == LHFPORT || way == LPFPORT || way == LHLPORT || way == LHFPORT)
		{
		  if (flow.dlocal)
		    {
		      short port;
		      if (way == LHFPORT || way == LPFPORT)
			port = flow.sport;
		      else
			port = flow.dport;
		      d_bucket = myhash(flow.dst, port, way, BRICKU);
		      if (shouldFilter(d_bucket, flow, c, index))
			{
			  is_filtered = true;
			  c->wfilter_p[d_bucket] += len;
			  c->wfilter_s[d_bucket] += oci;
			  checkReady(d_bucket, c, index);
			}
		    }
		}
	    }
	}
      
      for (int way = LHOST; way <= LPRST; way++) 
	{
	  // Find buckets on which to work
	  if (way == LHOST || way == LPREF || way == LHSYN || way == LPSYN || way == LHSYNACK
	      || way == LPSYNACK || way == LHACK || way == LPACK || way == LHRST || way == LPRST)
	    {
	      if (flow.dlocal)
		{
		  // traffic to LHOST/LPREF
		  d_bucket = myhash(flow.dst, 0, way, BRICKU);		  
		  
		  if (way == LHSYN  || way == LPSYN)
		    if (flow.flags != SYN || flow.proto != TCP)
		      continue;
		  if (way == LHSYNACK  || way == LPSYNACK)
		    if (flow.flags != SYNACK || flow.proto != TCP)
		      continue;
		  if (way == LHACK  || way == LPACK)
		    if (flow.flags != ACK || flow.proto != TCP)
		      continue;
		  if (way == LHRST  || way == LPRST)
		    if (flow.flags != RST || flow.proto != TCP)
		      continue;
		  c->databrick_p[d_bucket] += len;
		  c->databrick_rec[d_bucket] += oci;		  
		  
		  addSample(d_bucket, &fp, way, index);
		  instant_detect(c, curtime, d_bucket, index);
		}
	      if (flow.slocal)
		{
		  // traffic from LHOST/LPREF
		  s_bucket = myhash(flow.src, 0, way, BRICKU);

		  if (way == LHSYN || way == LPSYN)
		    if ((flow.flags != SYNACK && flow.flags != ACK && flow.flags != RST) || flow.proto != TCP)
		      continue;
		  if (way == LHSYNACK || way == LPSYNACK)
		    if (flow.flags != SYN || flow.proto != TCP)
		      continue;
		  if (way == LHACK || way == LPACK)
		    if ((flow.flags != PUSH && flow.flags != PUSHACK) || flow.proto != TCP)
		      continue;
		  if (way == LHRST || way == LPRST)
		    if (flow.flags != SYN || flow.proto != TCP)
		      continue;
		  c->databrick_p[s_bucket] -= len;
		  c->databrick_sent[s_bucket] += oci;
		  instant_detect(c, curtime, s_bucket, index);
		}	      
	    }
	  else if (way == FPORT)
	    {
	      if (flow.dlocal && isservice(flow.sport))
		{
		  // traffic from FPORT
		  s_bucket = myhash(0, flow.sport, way, BRICKU);
		  
		  c->databrick_p[s_bucket] += len;
		  c->databrick_rec[s_bucket] += oci;
		  
		  addSample(s_bucket, &fp, way, index);
		  instant_detect(c, curtime, s_bucket, index);
		}
	      if (flow.slocal && isservice(flow.dport))
		{
		  // traffic to FPORT
		  d_bucket = myhash(0, flow.dport, way, BRICKU);
		  
		  c->databrick_p[d_bucket] -= len;
		  c->databrick_sent[d_bucket] += oci;
		  instant_detect(c, curtime, d_bucket, index);
		}
	    }
	  else if (way == LPORT)
	    {
	      if (flow.dlocal && isservice(flow.dport))
		{
		  // traffic to LPORT		  
		  d_bucket = myhash(0, flow.dport, way, BRICKU);
		  		  
		  c->databrick_p[d_bucket] += len;
		  c->databrick_rec[d_bucket] += oci;

		  addSample(d_bucket, &fp, way, index);
		  instant_detect(c, curtime, d_bucket, index);
		}
	      if (flow.slocal && isservice(flow.sport))
		{
		  // traffic from LPORT
		  s_bucket = myhash(0, flow.sport, way, BRICKU);
		  
		  c->databrick_p[s_bucket] -= len;
		  c->databrick_sent[s_bucket] += oci;
		  instant_detect(c, curtime, s_bucket, index);
		}
	    }
	  else if (way == LHFPORT || way == LPFPORT)
	    {
	      if (flow.dlocal && isservice(flow.sport))
		{
		  // traffic from FPORT
		  s_bucket = myhash(flow.dst, flow.sport, way, BRICKU);
		  
		  c->databrick_p[s_bucket] += len;
		  c->databrick_rec[s_bucket] += oci;
		  		  
		  addSample(s_bucket, &fp, way, index);
		  instant_detect(c, curtime, s_bucket, index);
		}
	      if (flow.slocal && isservice(flow.dport))
		{
		  // traffic to FPORT
		  d_bucket = myhash(flow.src, flow.dport, way, BRICKU);
		  
		  c->databrick_p[d_bucket] -= len;
		  c->databrick_sent[d_bucket] += oci;
		  instant_detect(c, curtime, d_bucket, index);
		}
	    }
	  else if (way == LHLPORT || way == LPLPORT)
	    {
	      if (flow.dlocal && isservice(flow.dport))
		{
		  // traffic to LPORT
		  d_bucket = myhash(flow.dst, flow.dport, way, BRICKU);
		  
		  c->databrick_p[d_bucket] += len;
		  c->databrick_rec[d_bucket] += oci;

		  addSample(d_bucket, &fp, way, index);
		  instant_detect(c, curtime, d_bucket, index);
		}
	      if (flow.slocal && isservice(flow.sport))
		{
		  // traffic from LPORT
		  s_bucket = myhash(flow.src, flow.sport, way, BRICKU);
		  
		  c->databrick_p[s_bucket] -= len;
		  c->databrick_sent[s_bucket] += oci;
		  instant_detect(c, curtime, s_bucket, index);
		}
	    }
	}
    }
}

// Update statistics
void update_stats(cell* c, int index)
{
  if (!shuffle_done)
    return;

  pthread_mutex_lock(&final_lock);
  int BRICKF = BRICK_FINAL + index*13*NUMF;
  pthread_mutex_unlock(&final_lock);

  for (int i=0;i<BRICKF;i++)
    {
      for (int j=vol; j<=sym; j++)
	{
	  double data;
	  if (j == vol)
	    data = c->databrick_p[i];
	  else
	    {
	      c->databrick_s[i] = (double)c->databrick_rec[i]/(c->databrick_sent[i] + 1);
	      data = c->databrick_s[i];
	    }
	  // Only update if everything looks normal
	  if (!is_abnormal[index][i])
	    {
	      // Update avg and ss incrementally
	      stats[index][cur][n][j][i] += 1;
	      
	      if (stats[index][cur][n][j][i] == 1)
		{
		  stats[index][cur][avg][j][i] =  data;
		  stats[index][cur][ss][j][i] = 0;
		}
	      else
		{
		  double ao = stats[index][cur][avg][j][i];
		  stats[index][cur][avg][j][i] = stats[index][cur][avg][j][i] +
		    (double)(data - stats[index][cur][avg][j][i])/stats[index][cur][n][j][i];
		  stats[index][cur][ss][j][i] = stats[index][cur][ss][j][i] +
		    (data-ao)*(data - stats[index][cur][avg][j][i]);
		}
	    }
	}
    }      
  trained = (lasttime - firsttime);
  
  if (trained >= parms["min_train"])
    {
      if (!training_done)
	{
	  cout<<"Training has completed\n";
	  training_done = true;
	}
      firsttime = curtime;
      
      // This should now be done for all indexes
      for (int ind = 0; ind < NUMB; ind++)
	for (int x = ss; x >= n; x--)
	  for (int j = vol; j <= sym; j++)
	    for(int i = 0; i<BRICKF; i++)
	      {
		// Check if we have enough samples.
		// If the attack was long maybe we don't
		if (stats[ind][cur][n][j][i] <
		    parms["min_train"]*MIN_SAMPLES)
		  {
		    continue;
		  }
		if (stats[ind][cur][x][j][i] == 0)
		  stats[ind][hist][x][j][i] = 0.5*stats[ind][hist][x][j][i] + 0.5*stats[ind][cur][x][j][i];
		else
		  stats[ind][hist][x][j][i] = stats[ind][cur][x][j][i];
		
		stats[ind][cur][x][j][i] = 0;
	      }
      
    }
}


// This function detects an attack
void detect_attack(cell* c, double ltime, int id)
{
  pthread_mutex_lock(&final_lock);
  int BRICKF = BRICK_FINAL + id*13*NUMF;
  pthread_mutex_unlock(&final_lock);

  // For each bin
  for (int i=0;i<BRICKF;i++)
    {
      // Pull average and stdev for volume and symmetry
      double avgv = stats[id][hist][avg][vol][i];
      double stdv = sqrt(stats[id][hist][ss][vol][i]/(stats[id][hist][n][vol][i]-1));
      double avgs = stats[id][hist][avg][sym][i];
      double stds = sqrt(stats[id][hist][ss][sym][i]/(stats[id][hist][n][sym][i]-1));
      
      int volume = c->databrick_p[i];
      int asym = c->databrick_s[i];

      // Update cusum
      for (int type = 0; type <= 1; type++)
	{
	  int data = volume;
	  double mean = avgv;
	  double std = stdv;
	  if (type == 1)
	    {
	      data = asym;
	      mean = avgs;
	      std = stds;
	    }
	  double tmp = cusum[id][type][i] + data - mean - 3*std;
	  if (tmp > 0)    
	    cusum[id][type][i] = tmp;
	  else
	    cusum[id][type][i] = 0;
	}
      
      if (is_attack[id][i] == true)
	{
	  // Check if we have collected enough matches
	  if (signatures[id][i].nm == MM)
	    {
	      alert_ready(c, i, id); 
	    }
	  else
	    {
	      double diff = ltime - detection_time[id][i];
	      if (diff >= ADELAY)
		{
		  is_attack[id][i] = false;
		  detection_time[id][i] = 0;
		  clearSamples(i, id);
		}
	    }
	}
      else if (!is_attack[id][i])
	{
	  // Training is completed and both volume and symmetry are normal
	  if (training_done && !abnormal(vol, i, c, id) && !abnormal(sym, i, c, id))
	    {
	      // Reduce abnormal score
	      if (is_abnormal[id][i] > 0)
		{
		  is_abnormal[id][i] --;
		}
	      if (is_abnormal[id][i] == 0)
		clearSamples(i, id);
	    }
	}
    }
}

	
// Read pcap packet format
void
amonProcessingPcap(u_char* p, struct pcap_pkthdr *h,  double time) // (pcap_pkthdr* hdr, u_char* p, double time)
{
  // Start and end time of a flow are just pkt time
  double start = time;
  double end = time;
  double dur = 1;
  int pkts, bytes;

  struct ip ip;
  // Get source and destination IP and port and protocol 
  flow_t flow;
  
  struct ether_header ehdr;
  memcpy (&ehdr, p, sizeof (struct ether_header));
  int eth_type = ntohs (ehdr.ether_type);
  if (eth_type == 0x0800)
    {
      memcpy (&ip, p + sizeof (ehdr),sizeof (struct ip));   
      flow.src = ntohl (ip.ip_src.s_addr);
      flow.dst = ntohl (ip.ip_dst.s_addr);
      int proto = ip.ip_p;
      if (proto == IPPROTO_TCP)
	{
	  struct tcphdr *tcp = (struct tcphdr*)(p + sizeof (ehdr) + ip.ip_hl*4);
	  flow.sport = ntohs(tcp->th_sport);
	  flow.dport = ntohs(tcp->th_dport);
	}
      else if (proto == IPPROTO_UDP)
	{
	  struct udphdr *udp = (struct udphdr*)(p + sizeof (ehdr) + ip.ip_hl*4);
	  flow.sport = ntohs(udp->uh_sport);
	  flow.dport = ntohs(udp->uh_dport);
	}
      else
	{
	  flow.sport = 0;
	  flow.dport = 0;
	}
      pkts = 1;
      bytes = ntohs(ip.ip_len);
      flow.slocal = islocal(flow.src);
      flow.dlocal = islocal(flow.dst);
      flow.proto = proto;
      int oci = 1;
      amonProcessing(flow, bytes, start, end, oci); 
    }
}


// Read Flowride flow format
void
amonProcessingFlowride(char* line, double start)
{
  /* 1576613068700777885	ICMP	ACTIVE	x	129.82.138.44	46.167.131.0	0	0	1	0	60	0	0	8	0	1	0	60	0	1576613073700960814 */
  // Line is already parsed
  char send[MAXLINE], rend[MAXLINE];
  strncpy(send, line+delimiters[18],10);
  send[10] = 0;
  strncpy(rend, line+delimiters[18]+10,9);
  rend[9] = 0;
  double end = (double)atoi(send) + (double)atoi(rend)/1000000000;
  if (end > curtime)
    curtime = end;
  double dur = end - start;
  // Normalize duration
  if (dur < 1)
    dur = 1;
  if (dur > 3600)
    dur = 3600;

  // Hack for Flowride
  // assume 5 second interval for reports
  if (dur > 5)
    dur = 5;
  
  int pkts, bytes, rpkts, rbytes, pktsdir, pktsrev;

  // Get source and destination IP and port and protocol 
  flow_t flow;
  int proto;
  if (strcmp(line+delimiters[0], "UDP") == 0)
    proto = UDP;
  else if (strcmp(line+delimiters[0], "TCP") == 0)
    proto = TCP;
  else
    proto = 0;

  flow.src = todec(line+delimiters[3]);
  flow.sport = atoi(line+delimiters[5]); 
  flow.dst = todec(line+delimiters[4]);
  flow.dport = atoi(line+delimiters[6]); 
  flow.proto = proto;
  flow.slocal = islocal(flow.src);
  flow.dlocal = islocal(flow.dst);
  int pbytes = atoi(line+delimiters[16]);
  rbytes = atoi(line+delimiters[17]);
  pktsdir = atoi(line+delimiters[14]);
  pktsrev = atoi(line+delimiters[15]);
  // Closed flow, no need to do anything

  if (pktsdir == 0 && pktsrev == 0)
    return;
  processedbytes+=pbytes;

  // Cross-traffic, do nothing
  if (!flow.slocal && !flow.dlocal)
    {
      nl++;
      return;
    }
  l++;
  int flags = atoi(line+delimiters[11]);
  int ppkts = atoi(line+delimiters[14]);
  rpkts = atoi(line+delimiters[15]);
  pkts = (int)(ceil(ppkts/dur));
  bytes = (int)(ceil(pbytes/dur));
  rpkts = (int)(ceil(rpkts/dur));
  rbytes = (int)(ceil(rbytes/dur));

  /* Is this outstanding connection? For TCP, connections without 
     PUSH are outstanding. For UDP, connections that have a request
     but not a reply are outstanding. Because bidirectional flows
     may be broken into two unidirectional flows we have values of
     0, -1 and +1 for outstanding connection indicator or oci. For 
     TCP we use 0 (there is a PUSH) or 1 (no PUSH) and for UDP/ICMP we 
     use +1. */
  int oci, roci = 0;
  if (proto == TCP)
    {
      // Jelena: Temp ad-hoc fix for Flowride
      // fake a PSH flag for bunch of inc. cases
      if (pkts > 0 && bytes/pkts > 100)
	{
	  flags = flags | 8;
	}
      if (rpkts > 0 && rbytes/rpkts > 100)
	{
	  flags = flags | 8;
	}
      if (flags == 16)
	{
	  flags = flags | 8;
	}
      if ((flags & 1) > 0)
	{
	  flags = flags | 8;
	}
      // There is a PUSH flag
      if ((flags & 8) > 0)
	{
	  oci = 0;
	  roci = 0;
	}
      else
	{
	  oci = pkts;
	  roci = rpkts;
	}
    }
  else if (proto == UDP)
    {
      oci = pkts;
      roci = rpkts;
    }
  else
    // unknown proto
    {
      oci = pkts;
      roci = rpkts;
    }
  // Don't deal with TCP flows w PUSH flags 
  if (oci == 0)
    return;

  amonProcessing(flow, bytes, start, end, oci);
  // Now account for reverse flow too, if needed
  if (rbytes > 0)
    {
      flow_t rflow;
      rflow.src = flow.dst;
      rflow.sport = flow.dport;
      rflow.dst = flow.src;
      rflow.dport = flow.sport;
      rflow.proto = flow.proto;
      rflow.slocal = flow.dlocal;
      rflow.dlocal = flow.slocal;
      
      amonProcessing(rflow, rbytes, start, end, roci);
    }
  
}

// Read nfdump flow format
void amonProcessingNfdump (char* line, double time)
{
  /* 2|1453485557|768|1453485557|768|6|0|0|0|2379511808|44694|0|0|0|2792759296|995|0|0|0|0|2|0|1|40 */
  // Get start and end time of a flow
  char* tokene;
  strcpy(saveline, line);
  parse(line,'|', &delimiters);
  double start = (double)strtol(line+delimiters[0], &tokene, 10);
  start = start + strtol(line+delimiters[1], &tokene, 10)/1000.0;
  double end = (double)strtol(line+delimiters[2], &tokene, 10);
  end = end + strtol(line+delimiters[3], &tokene, 10)/1000.0;
  double dur = end - start;
  // Normalize duration
  if (dur < 0)
    dur = 0;
  if (dur > 3600)
    dur = 3600;
  int pkts, bytes;

  // Get source and destination IP and port and protocol 
  flow_t flow;
  int proto = atoi(line+delimiters[4]);
  flow.src = strtol(line+delimiters[8], &tokene, 10);
  flow.sport = atoi(line+delimiters[9]); 
  flow.dst = strtol(line+delimiters[13], &tokene, 10);
  flow.dport = atoi(line+delimiters[14]); 
  flow.proto = proto;
  int flags = atoi(line+delimiters[19]);
  flow.flags = flags;
  flow.slocal = islocal(flow.src);
  flow.dlocal = islocal(flow.dst);
  bytes = atoi(line+delimiters[22]);
  processedbytes+=bytes;

  // Cross-traffic, do nothing
  if (!flow.slocal && !flow.dlocal)
    {
      nl++;
      return;
    }
  l++;

  pkts = atoi(line+delimiters[21]);

  // Get the rate
  pkts = (int)(pkts/(dur+1))+1;
  bytes = (int)(bytes/(dur+1))+1;
  
  /* Is this outstanding connection? For TCP, connections without 
     PUSH are outstanding. For UDP, connections that have a request
     but not a reply are outstanding. Because bidirectional flows
     may be broken into two unidirectional flows we have values of
     0, -1 and +1 for outstanding connection indicator or oci. For 
     TCP we use 0 (there is a PUSH) or 1 (no PUSH) and for UDP/ICMP we 
     use +1 for requests and -1 for replies. */
  int oci;
  if (proto == TCP)
    {
      // There is a PUSH flag or just ACK
      // ignore these packets
      if ((flags & 8) > 0 || (flags == 16))
	oci = 0;
      else
	oci = pkts;
    }
  else if (proto == UDP || proto == ICMP)
    oci = pkts;
  else
    return;
  
  if (oci == 0)
    return;

  amonProcessing(flow, bytes, start, end, oci); 
}



// Ever so often go through flows and process what is ready
void *reset_transmit (void* lt)
{
  double ltime = *((double*) lt);
  // Make sure to note that you're running
  pthread_mutex_lock (&rst_lock);
  resetrunning = true;
  pthread_mutex_unlock (&rst_lock);
  
  // Serialize access to cells
  pthread_mutex_lock (&cells_lock);


  lasttime = curtime;
  // We will process this one now
  int current = cfront;

  // This one will be next for processing
  cfront = (cfront + 1)%QSIZE;
  if (cfront == crear)
    cempty = true;
  
  // Serialize access to cells
  pthread_mutex_unlock (&cells_lock);


  for (int index = 0; index < NUMB; index++)
    {
      cell* c = &cells[index][current];
  
      // Check if there is an attack that was waiting
      // a long time to be reported. Perhaps we had too specific
      // signature and we will never collect enough matches
      // Serialize access to stats
      
      if (training_done)
	detect_attack(c, ltime, index);
      
      update_stats(c, index);
    }

  // Now note that you're done
  pthread_mutex_lock (&rst_lock);
  resetrunning = false;
  pthread_mutex_unlock (&rst_lock);
  
  // Detect attack here
  pthread_exit (NULL);
}


// Save historical data for later run
void save_history()
{  
  // Only save if training has completed
  if (training_done)
    {
      ofstream out;
      out.open("as.dump", std::ios_base::out);
      out<<numattack<<" "<<BRICK_FINAL<<endl;
      for (int index = 0; index < NUMB; index++)
	{
	  int BRICKF=BRICK_FINAL + index*13*NUMF;
	  for (int t=cur; t<=hist; t++)
	    {
	      for (int i=0;i<BRICKF;i++)
		{
		  for (int j=vol; j<=sym; j++)
		    {
		      out<<t<<" "<<index<<" "<<i<<" "<<j<<" ";
		      out<<stats[index][t][n][j][i]<<" "<<stats[index][t][avg][j][i]<<" "<<stats[index][t][ss][j][i]<<endl;
		    }
		}
	    }
	}
      out.close();
    }
}


// Load historical data
void load_history()
{
  ifstream in;
  in.open("as.dump", std::ios_base::in);
  if (in.is_open())
    {
      in>>numattack>>BRICK_FINAL;
      for (int index = 0; index < NUMB; index++)
	malloc_all(index, BRICK_FINAL + index*13*NUMF);

      for (int index = 0; index < NUMB; index++)
	{
	  int BRICKF=BRICK_FINAL + index*13*NUMF;
	  for (int t=cur; t<=hist; t++)
	    {
	      for (int i=0;i<BRICKF;i++)
		{
		  for (int j=vol; j<=sym; j++)
		    {
		      in>>t>>index>>i>>j;
		      in>>stats[index][t][n][j][i]>>stats[index][t][avg][j][i]>>stats[index][t][ss][j][i];
		    }
		}
	    }
	}
      in.close();
      training_done = true;
      cout<<"Training data loaded"<<endl;
    }  
}

// Print help for the program
void
printHelp (void)
{
  printf ("amon-senss\n(C) 2018 University of Southern California.\n\n");

  printf ("-h                             Print this help\n");
  printf ("-S                             Streaming input from stdin\n");
  printf ("-r <file|folder|iface>         Input is in given file or folder, or live on the specified iface\n");
  printf ("-l                             Load historical data from as.dump\n");
  printf ("-F <pcap|plive|ft|nf|fr>       Input is in this format\n");
  printf ("\t pcap - libpcap format in a file\n");
  printf ("\t plive - libpcap live read from interface\n");
  printf ("\t ft - flowtools format in a file\n");
  printf ("\t nf - netflow format in a file\n");
  printf ("\t fr - Flowride format in a file\n");
  printf ("-s <file>                      Start from this given file in the input folder\n");
  printf ("-e <file>                      End with this given file in the input folder\n");
  printf ("-f                             Simulate filtering, without this we don't print alerts\n");
  printf ("-v                             Verbose\n");
}


// Define the function to be called when ctrl-c (SIGINT) is sent to process
void signal_callback_handler(int signum) {
   cout << "Caught signal " << signum << endl;
   // Terminate program
   save_history();
   exit(signum);
}

// Read one line from file according to format
double read_one_line(void* nf, char* format, char* line, u_char*& p,  struct pcap_pkthdr*& h)
{
  if (!strcmp(format, "nf") || !strcmp(format, "ft") || !strcmp(format,"fr"))
    {
      char* s = fgets(line, MAXLINE, (FILE*) nf);
      if (s == NULL)
	return -1;
      
      char tmpline[MAXLINE];
      strcpy(tmpline, line);
      
      // This is a hack to check if we reached the end of NetFlow file
      // Sometimes we do not get feof but we can still detect based on text
      // that is always in the end of the file      
      if (!strcmp(format, "nf") || !strcmp(format, "ft"))
	{
	  if (strstr(tmpline, "Sys") > 0)
	    return -1;
	  if (strstr(tmpline, "|") == NULL)
	    return 0;
	  int dl = parse(tmpline,'|', &delimiters);
	  double epoch = strtol(tmpline+delimiters[2],NULL,10);
	  int msec = atoi(tmpline+delimiters[3]);
	  epoch = epoch + msec/1000.0;
	  return epoch;
	}
      else {
	int dl = parse(line,'\t', &delimiters);
	if (dl != 19)
	  return 0;
	
	char sstart[MAXLINE], rstart[MAXLINE];
	strncpy(sstart, line+delimiters[18],10);
	sstart[10] = 0;
	strncpy(rstart, line+delimiters[18]+10,9);
	rstart[9] = 0;
	double epoch = (double)atoi(sstart)+(double)atoi(rstart)/1000000000;
	return epoch;
      }
    }
  else if (!strcmp(format,"pcap") || !strcmp(format,"plive"))
    {
      int rc = pcap_next_ex((pcap_t*)nf, &h, (const u_char **) &p);

      if (rc <= 0)
	return -1;
      
      struct ether_header* eth_header = (struct ether_header *) p;
      
      if (ntohs(eth_header->ether_type) != ETHERTYPE_IP) 
	return 0;
      double epoch = h->ts.tv_sec + h->ts.tv_usec/1000000.0;
      return epoch;
    }
  //Jelena add more formats
  return 0;
}

void process_one_line(char* line, void* nf, double epoch, char* format, u_char* p, struct pcap_pkthdr *h)
{
  if (!strcmp(format, "nf") || !strcmp(format, "ft"))
    amonProcessingNfdump (line, epoch);
  else if (!strcmp(format, "fr"))
    amonProcessingFlowride (line, epoch);
  else if (!strcmp(format, "pcap"))
    amonProcessingPcap(p, h, epoch);
  // add more formats
}

// Read from file according to format
void read_from_file(void* nf, char* format)
{
  // -1 means EOF, 0 means line without a flow
  char line[MAXLINE];
  double epoch;
  int num_pkts = 0;
  double start = time(0);
  u_char* p;
  long int nlines = 0;
  struct pcap_pkthdr *h;
  cout<<"Reading from file\n";
    
  while ((epoch = read_one_line(nf, format, line, p, h)) != -1)
    {
      nlines++;
      if (epoch == 0)
	continue;
      if (firsttime == 0)
	firsttime = epoch;
      num_pkts++;
      if (firsttimeinfile == 0)
	firsttimeinfile = epoch;
      allflows++;
      if (allflows % 1000000 == 0)
	{
	  double diff = time(0) - start;
	  cout<<"Processed "<<allflows<<", 1M in "<<diff<<endl;
	  start = time(0);
	}
      processedflows++;
      // Each second
      if (curtime - lasttime >= parms["interval"]) 
	{
	  pthread_mutex_lock (&cells_lock);
	  lastbintime = curtime;
	  
	  // This one we will work on next
	  crear = (crear + 1)%QSIZE;
	  if (crear == cfront && !cempty)
	    {
	      perror("QSIZE is too small\n");
	      exit(1);
	    }
	  // zero out stats
	  for (int index = 0; index < NUMB; index++)
	    {						 
	      cell* c = &cells[index][crear];

	      if (shuffle_done)
		{
		  int BRICKF = BRICK_FINAL + index*13*NUMF;
		  
		  memset(c->databrick_p, 0, BRICKF*sizeof(long int));
		  memset(c->databrick_sent, 0, BRICKF*sizeof(long int));
		  memset(c->databrick_rec, 0, BRICKF*sizeof(long int));
		  memset(c->databrick_s, 0, BRICKF*sizeof(double));
		  memset(c->wfilter_p, 0, BRICKF*sizeof(unsigned int));
		  memset(c->wfilter_s, 0, BRICKF*sizeof(int));
		}
	      // and it will soon be full
	    }
	  cempty = false;
	  pthread_mutex_unlock (&cells_lock);
	  
	  pthread_t thread_id;
	  pthread_create (&thread_id, NULL, reset_transmit, &lastbintime);
	  pthread_detach(thread_id);
	  processedflows = 0;
	  lasttime = curtime;
	}
      process_one_line(line, nf, epoch, format, p, h);
    }
  cout<<"Read "<<nlines<<" lines\n";
}

// Main program
int main (int argc, char *argv[])
{  
  delimiters = (int*)malloc(AR_LEN*sizeof(int));

  // Touch alerts file
  ofstream out;
  
  out.open("alerts.txt", std::ios_base::out);
  out<<"#attackID intID start-time bin bytes packets signature\n";
  out.close();
    
  char c, buf[32];
  vector<string> file_in;
  bool stream_in = false;
  char *startfile = NULL, *endfile = NULL;
  char* format;
  
  while ((c = getopt (argc, argv, "hvlr:s:e:F:fS")) != '?')
    {
      if ((c == 255) || (c == -1))
	break;

      switch (c)
	{
	case 'h':
	  printHelp ();
	  return (0);
	  break;
	case 'F':
	  format = strdup(optarg);
	  if (strcmp(format,"pcap") && strcmp(format,"plive") && strcmp(format,"ft") && strcmp(format,"nf") && strcmp(format,"fr"))
	    {
	      cerr<<"Unknown format "<<format<<endl;
	      exit(1);
	    }
	  break;
	case 'S':
	  stream_in = true;
	  break;
	case 'r':
	  file_in.push_back(strdup(optarg));
	  break;
	case 'f':
	  sim_filter = true;
	  break;
	case 'l':
	  load_history();
	  break;
	case 's':
	  startfile = strdup(optarg);
	  cout<<"Start file "<<startfile<<endl;
	  break;
	case 'e':
	  endfile = strdup(optarg);
	  cout<<"End file "<<endfile<<endl;
	  break;
	case 'v':
	  verbose = 1;
	  break;
	}
    }
  if (file_in.empty() && stream_in == 0)
    {
      cerr<<"You must specify an input folder, which holds Netflow records\n";
      exit(-1);
    }
  cout<<"Verbose "<<verbose<<endl;
  numservices = loadservices("services.txt");
  loadprefixes("localprefs.txt");

  // Parse configuration
  parse_config(parms);
  noorphan = (bool) parms["no_orphan"];
  signal(SIGINT, signal_callback_handler);

  clock_gettime(CLOCK_MONOTONIC, &last_entry);      
  // This is going to be a pointer to input
  // stream, either from nfdump or flow-tools */
  FILE* nf, * ft;
  unsigned long long num_pkts = 0;      

  // Read flows from a file
  if (stream_in)
    {
      read_from_file(stdin, format);
    }
  else 
    {
      int isdir = 0;
      vector<string> tracefiles, newfiles, *processfiles;
      vector<string> inputs;
      bool first = true;
      while(true)
	{
	  sleep(1);
	  inputs.clear();
	  newfiles.clear();
	  struct stat s;
	  for (auto it=file_in.begin(); it != file_in.end(); it++)
	    inputs.push_back(*it);
	  int i = 0;
	  // Recursively read if there are several directories that hold the files
	  while(i < inputs.size())
	    {
	      if(stat(inputs[i].c_str(),&s) == 0 )
		{
		  if(s.st_mode & S_IFDIR )
		    {
		      // it's a directory, read it and fill in 
		      // list of files
		      DIR *dir;
		      struct dirent *ent;
		      
		      if ((dir = opendir (inputs[i].c_str())) != NULL) {
			// Remember all the files and directories within directory 
			while ((ent = readdir (dir)) != NULL) {
			  if((strcmp(ent->d_name,".") != 0) && (strcmp(ent->d_name,"..") != 0)){
			    stat(ent->d_name,&s);
			    int timediff = time(0) - s.st_mtime;
			    if (timediff > 60)
			      inputs.push_back(string(inputs[i]) + "/" + string(ent->d_name));
			  }
			}
			closedir (dir);
		      } else {
			perror("Could not read directory ");
			exit(1);
		      }
		    }
		  else if(s.st_mode & S_IFREG)
		    {
		      if (find(tracefiles.begin(), tracefiles.end(), inputs[i]) != tracefiles.end())
			{
			}
		      else
			{
			  int timediff = time(0) - s.st_mtime;
			  if (timediff > 60)
			    {
			      tracefiles.push_back(inputs[i]);
			      if (!first)
				newfiles.push_back(inputs[i]);
			    }
			}
		    }
		  // Ignore other file types
		}
	      i++;
	    }
	  inputs.clear();
	  if (first)
	    processfiles = &tracefiles;
	  else
	    processfiles = &newfiles;

	  std::sort(processfiles->begin(), processfiles->end(), sortbyFilename());
	  for (vector<string>::iterator vit=processfiles->begin(); vit != processfiles->end(); vit++)
	    {
	      cout<<"Files to read "<<vit->c_str()<<endl;
	    }
	  int started = 1;
	  if (startfile != NULL)
	    started = 0;
	  double start = time(0);
	  // Go through processfiles and read each one

	  for (vector<string>::iterator vit=processfiles->begin(); vit != processfiles->end(); vit++)
	    {
	      const char* file = vit->c_str();
	      
	      if (!started && startfile && strstr(file,startfile) == NULL)
		{
		  continue;
		}
	      
	      started = 1;
	      startfile = 0;
	      
	      // Now read from file
	      char cmd[MAXLINE];
	      cout<<"Reading from "<<file<<endl;
	      firsttimeinfile = 0;
	      
	      if (!strcmp(format, "pcap") || !strcmp(format, "plive"))
		{
		  char ebuf[MAXLINE];
		  pcap_t *pt;
		  if (is_live)
		    pt = pcap_open_live(file, MAXLINE, 1, 1000, ebuf);
		  else
		    pt = pcap_open_offline (file, ebuf);
		  read_from_file(pt, format);
		}
	      else
		{
		  if (!strcmp(format, "nf"))
		    {
		      sprintf(cmd,"nfdump -r %s -o pipe 2>/dev/null", file);
		    }
		  else if (!strcmp(format, "ft"))
		    {
		      sprintf(cmd,"ft2nfdump -r %s | nfdump -r - -o pipe", file);
		    }
		  else if (!strcmp(format, "fr"))
		    {
		      sprintf(cmd,"gunzip -c %s", file);
		    }
		  nf = popen(cmd, "r");
		  if (nf == 0)
		    {
		      perror("nf is zero ");
		    }
		  read_from_file(nf, format);
		  pclose(nf);
		}
	      cout<<"Done with the file "<<file<<" time "<<time(0)<<" flows "<<allflows<<" training "<<training_done<<" shuffle "<<shuffle_done<<endl;
	      if (endfile && strstr(file,endfile) != 0)
		break;
	    }
	  first = false;
	}
    }
  save_history();
  return 0;
}
