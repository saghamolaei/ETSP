#include <iostream>
#include <vector>
#include <algorithm>
#include <map>
#include <set>
using namespace std;

//#define bound 0.2
#define N 1000
#define eps 0.01

#define vertex pair<double,double>

struct edge{
	vertex first;
	vertex second;
	bool vertical;
};

bool mark[N];
int par[N];
int s[N];
vertex p[N];
vertex P[N];
vector<edge> q(1);

int n;
vector<pair<double,pair<int,int> > > all;
vector<int> tree[N];

vertex V[2 * N];
vector<int> adj2[2 * N];
set<int> visited[2 * N];

vector<int> tsp,tsp2;

int match(int a)
{
	if (par[a] == a)
		return a;
	int temp =match(par[a]);
	s[temp]+=s[a];
	par[a] = temp;
	return temp;
}

bool merged(int a, int b)
{
	if (match(a) == match(b))
		return false;
	a = match(a);
	b = match(b);
	if (s[a] > s[b])
	{
		s[a] += s[b]+1;
		par[b] = a;
	}
	else
	{
		s[b] += s[a] + 1;
		par[a] = b;
	}
	return true;
}

double dist(int a, int b)
{
	return sqrt((p[a].first - p[b].first)*(p[a].first - p[b].first) + (p[a].second - p[b].second)*(p[a].second - p[b].second));
}

int comp(pair<double, pair<int, int> > a, pair<double, pair<int, int> > b)
{
	return (a.first < b.first);
}

bool isVertical(edge e)
{
	if (fabs(e.first.first - e.second.first) < eps)
		return true;
	if (fabs(e.first.second-e.second.second)<eps)
	return false;
	cerr << "error" << endl;
	return true;
}
bool compare(vertex a, vertex b)
{
	if (a.first - b.first < -eps && fabs(a.first - b.first)>eps)
	{
		//cout << a.first << " " << a.second << " < " << b.first << " " << b.second  << endl;
		return true;
	}
	if (fabs(a.first-b.first)<eps)
	{
		if (fabs(a.second - b.second) < eps)
		{
			//cout << a.first << " " << a.second << " > " << b.first << " " << b.second << endl;
			return false;
		}
		if (a.second - b.second < -eps)
		{
			//cout << a.first << " " << a.second << " <= " << b.first << " " << b.second  << endl;
			return true;
		}
	}
	//cout << a.first << " " << a.second << " > " << b.first << " " << b.second  << endl;
	return false;
}
int quadrant(vertex a)
{
	if (a.first > eps && a.second > eps)
		return 2;
	if (a.first < -eps && a.second >eps)
		return 4;
	if (a.first < -eps && a.second <-eps)
		return 6;
	if (a.first > eps && a.second < -eps)
		return 8;
	if (fabs(a.first) < eps && fabs(a.second) < eps)
		return 9;
	if (fabs(a.first) < eps && a.second >eps)
		return 3;
	if (fabs(a.first) < eps && a.second <-eps)
		return 7;
	if (fabs(a.second) < eps && a.first >eps)
		return 1;
	if (fabs(a.second) < eps && a.first <-eps)
		return 5;
}

int cross(vertex center, vertex old, vertex now)
{
	if (fabs(old.first-now.first)<eps && fabs(old.second-now.second)<eps)
		return 2;
	if (fabs(center.first-now.first) <eps && fabs(center.second-now.second)<eps)
		return 3;
	vertex a,b;
	a.first = now.first - center.first;
	a.second = now.second - center.second;
	b.first = old.first - center.first;
	b.second = old.second - center.second;
	int qa = quadrant(a), qb = quadrant(b);
	double product = b.first*a.second - b.second*a.first;

	//zero vector
	if (qa == 9 || qb == 9)
		return true;
	//same quadrant
	if (qa == qb)
	{
		if (qa % 2 == 0)
		{
			if (product > eps && fabs(product) > eps)
				return true;
			if (product < -eps && fabs(product) >eps)
				return false;
		}
		//colinear
		return 2;
	}
	//opposite
	if (fabs(product) < eps)
	{
		return 3;
	}
	//different quadrants
	if (qb % 2 == 1)
	{
		for (int i = 1; i < 4; i++)
		{
			if ((qb + i) % 9 == qa)
			{
				return true;
			}
		}
	}
	else
	{
		for (int i = 1; i <= 4; i++)
		{
			if ((qb + i) % 9 == qa)
			{
				return true;
			}
		}
		// the completely opposite direction was handled earlier
	}
	return false;
}

double euclidean(vertex a, vertex b)
{
	return sqrt((a.first - b.first)*(a.first - b.first) + (a.second - b.second)*(a.second - b.second));
}

void dfs2(int cur)
{
	int prev = tsp2.back();
	tsp2.push_back(cur);
	int u;
	do{
		u = -1;
		//left
		for (int i = 0; i < adj2[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if (cross(V[prev], V[cur], V[adj2[cur][i]]) == 1 && (u < 0 ||
					cross(V[cur], V[adj2[cur][u]], V[adj2[cur][i]]) == 1))
				{
					u = i;
				}
			}
		}
		// straight
		if (u == -1)
		for (int i = 0; i < adj2[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if ( cross(V[prev], V[cur], V[adj2[cur][i]]) == 2 &&
					(u < 0 ||(
						cross(V[cur], V[adj2[cur][u]], V[adj2[cur][i]]) == 1 || 
						(cross(V[cur], V[adj2[cur][u]], V[adj2[cur][i]]) == 2 
						&& euclidean(V[cur], V[adj2[cur][i]])<euclidean(V[cur], V[adj2[cur][u]]))
					)) )
				{
					u = i;
				}
			}
		}
		// right
		if (u == -1)
		for (int i = 0; i < adj2[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if (cross(V[prev], V[cur], V[adj2[cur][i]]) == 0 && (u < 0 ||
					cross(V[cur], V[adj2[cur][u]], V[adj2[cur][i]]) == 1))
				{
					u = i;
				}
			}
		}
		//opposite
		if (u == -1)
		for (int i = 0; i < adj2[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if (cross(V[prev], V[cur], V[adj2[cur][i]]) == 3 && (u < 0 ||
					euclidean(V[cur], V[adj2[cur][i]])<euclidean(V[cur], V[adj2[cur][u]])))
				{
					u = i;
				}
			}
		}
		if (u == -1)
		for (int i = 0; i < adj2[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				u = i;
			}
		}
		if (u != -1)
		{
			visited[cur].insert(u);
			dfs2(adj2[cur][u]);
		}
	} while (u != -1);
	return;
}

void dfs(int cur)
{
	int prev = tsp.back();
	tsp.push_back(cur);
	int u;
	do{
		u = -1;
		//left
		for (int i = 0; i < tree[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if (cross(P[prev], P[cur], P[tree[cur][i]]) == 1 && (u < 0 ||
					cross(P[cur], P[tree[cur][u]], P[tree[cur][i]]) == 1))
				{
					u = i;
				}
			}
		}
		// straight
		if (u == -1)
		for (int i = 0; i < tree[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if (cross(P[prev], P[cur], P[tree[cur][i]]) == 2 &&
					(u < 0 || (
					cross(P[cur], P[tree[cur][u]], P[tree[cur][i]]) == 1 ||
					(cross(P[cur], P[tree[cur][u]], P[tree[cur][i]]) == 2
					&& euclidean(P[cur], P[tree[cur][i]])<euclidean(P[cur], P[tree[cur][u]]))
					)))
				{
					u = i;
				}
			}
		}
		// right
		if (u == -1)
		for (int i = 0; i < tree[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if (cross(P[prev], P[cur], P[tree[cur][i]]) == 0 && (u < 0 ||
					cross(P[cur], P[tree[cur][u]], P[tree[cur][i]]) == 1))
				{
					u = i;
				}
			}
		}
		//opposite
		if (u == -1)
		for (int i = 0; i < tree[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				if (cross(P[prev], P[cur], P[tree[cur][i]]) == 3 && (u < 0 ||
					euclidean(P[cur], P[tree[cur][i]])<euclidean(P[cur], P[tree[cur][u]])))
				{
					u = i;
				}
			}
		}
		if (u == -1)
		for (int i = 0; i < tree[cur].size(); i++)
		{
			if (visited[cur].find(i) == visited[cur].end())
			{
				u = i;
			}
		}
		if (u != -1)
		{
			visited[cur].insert(u);
			dfs(tree[cur][u]);
		}
	} while (u != -1);
	return;
}


int main()
{
	//vector<int> tsp(n);
	double normalize_min_x, normalize_min_y, normalize_max_x, normalize_max_y;
	int i = 0;
	while (cin >> p[i].first >> p[i].second)
	{
		if (i == 0 || normalize_min_x > p[i].first)
		{
			normalize_min_x = p[i].first;
		}
		if (i == 0 || normalize_min_y > p[i].second)
		{
			normalize_min_y = p[i].second;
		}
		if (i == 0 || normalize_max_x < p[i].first)
		{
			normalize_max_x = p[i].first;
		}
		if (i == 0 || normalize_max_y < p[i].second)
		{
			normalize_max_y = p[i].second;
		}
		mark[i] = false;
		par[i] = i;
		s[i] = 1;
		i++;
	}
	n = i;
	sort(p, p + n,compare);
	int ss = 0;
	for (int i = 1; i < n; i++)
	if (!(fabs(p[i].first - p[ss].first) <2*eps && fabs(p[i].second - p[ss].second) < 2*eps ))
	{
		ss++;
		p[ss] = p[i];
	}
	n = ss+1;
	if (n < 3)
		return 0;
	for (int i = 0; i < n; i++)
	{
		if (fabs(normalize_max_x - normalize_min_x)>eps)
		p[i].first = 1000*(p[i].first - normalize_min_x) / (normalize_max_x - normalize_min_x);
		if (fabs(normalize_max_y - normalize_min_y)>eps)
		p[i].second = 1000 * (p[i].second - normalize_min_y) / (normalize_max_y - normalize_min_y);
	}
	int t = 0;
	pair<double, pair<int, int> > T;
	//build the graph
	for (int i = 0; i < n; i++)
	for (int j = 0; j < i; j++)
	{
		//if (dist(i, j) < bound)
		{
			all.push_back(T);
			all[t].first = dist(i, j);
			all[t].second = make_pair(i, j);
			t++;
		}
	}
	sort(all.begin(), all.end(), comp);
	double mst = 0;
	int cnt = 0;
	for (int i = 0; i < t && cnt <n; i++)
	{
		int u = all[i].second.first;
		int v = all[i].second.second;
		if (merged(u, v))
		{
			tree[u].push_back(v);
			tree[v].push_back(u);
			mst+=all[i].first;
			cnt++;
		}
	}
	
	double diam=0;
	bool diam_first = true;
	double sin_theta=0, cos_theta=0;
	int ip, jp;
	for (int i = 0; i < n; i++)
	for (int j = 0; j < n; j++)
	{
		if (i != j)
		if (diam_first || diam < dist(i, j))
		{
			diam_first = false;
			diam = dist(i, j);
			sin_theta = (p[j].second - p[i].second) / diam;
			cos_theta = (p[j].first - p[i].first) / diam;
			ip = i;
			jp = j;
		}
	}
	double snowflake = diam;
	//rotate!
	for (int i = 0; i < n; i++)
	{
		P[i].first = p[i].first*cos_theta + p[i].second*sin_theta;
		P[i].second = p[i].second*cos_theta - p[i].first*sin_theta;
	}
	q[0].first = P[ip];
	q[0].second = P[jp];
	q[0].vertical = isVertical(q[0]);
	// Prim for the snowflake tree
	for (int i = 0; i < n; i++)
	{
		mark[i] = false;
	}
	mark[ip] = mark[jp] = true;
	//find and add the farthest
	for (int i = 2; i < n; i++)
	{
		int next_point2 = -1, maxId=-1;
		double d,temp,maxi=-1;
		edge e;
		for (int j = 0; j < n; j++)
		{
			int next_point = -1;
			if (mark[j] == false)
			{
				//compute the distance
				for (int ii = 0; ii < q.size(); ii++)
				{
					if (q[ii].vertical)
					{
						if (P[j].second >= min(q[ii].first.second, q[ii].second.second) &&
							P[j].second <= max(q[ii].first.second, q[ii].second.second))
						{
							temp = fabs(P[j].first - q[ii].first.first);
							if (next_point == -1 || d > temp)
							{
								next_point = ii;
								d = temp;
							}
						}
					}
					else
					{
						if (P[j].first >= min(q[ii].first.first, q[ii].second.first) &&
							P[j].first <= max(q[ii].first.first, q[ii].second.first))
						{
							temp = fabs(P[j].second - q[ii].first.second);
							if (next_point == -1 || d > temp)
							{
								next_point = ii;
								d = temp;
							}
						}
					}
				}//end for
			}//end if
			if (mark[j] == false)
			{
				if (maxi == -1 || maxi < d)
				{
					maxi = d;
					maxId = j;
					next_point2 = next_point;
				}
			}
		}
		edge u, v;
		//update the candidate
		if (mark[maxId] == false)
		{
			mark[maxId] = true;
			if (q[next_point2].vertical)
			{
				e.first = P[maxId];
				e.second = make_pair(q[next_point2].first.first, P[maxId].second);
			}
			else
			{
				e.first = P[maxId];
				e.second = make_pair(P[maxId].first, q[next_point2].first.second);
			}
			e.vertical = isVertical(e);
			//add to the tree
			q.push_back(e);
			u = v = q[next_point2];
			u.first = e.second;
			v.second = e.second;
			q[next_point2] = u;
			if (euclidean(v.first, v.second) > eps)
				q.push_back(v);
			//update the sum
			snowflake += d;
		}
	}
	cout << mst << " ";
	cout << snowflake << " ";

	//make an adjacency list for the snowflake tree
	//first make the vertex list
	map<vertex, int, bool(*)(vertex,vertex)> mp(compare);
	int k = 0;
	for (int i = 0; i < q.size(); i++)
	{
		map<vertex, int, bool(*)(vertex, vertex) >::iterator it = mp.find(q[i].first);
		map<vertex, int, bool(*)(vertex, vertex) >::iterator jt = mp.find(q[i].second);
		if (it == mp.end())
		{
			mp[q[i].first] = k;
			V[k] = q[i].first;
			k++;
		}
		if (jt == mp.end())
		{
			mp[q[i].second] = k;
			V[k] = q[i].second;
			k++;
		}
	}
	for (int i = 0; i < q.size(); i++)
	{
		adj2[mp[q[i].first]].push_back(mp[q[i].second]);
		adj2[mp[q[i].second]].push_back(mp[q[i].first]);
	}
	int start = 0;
	for (int i = 1; i < k; i++)
	{
		if (V[i].first < V[start].first+eps || (fabs(V[i].first - V[start].first) < eps && V[i].second < V[start].second+eps))
			start = i;
	}
	tsp2.push_back(start);
	int ind = -1;
	for (int i = 0; i < adj2[start].size(); i++)
	{
		if (ind == -1 || cross(V[start], V[adj2[start][ind]], V[adj2[start][i]]) == 1)
			ind = i;
	}
	if (ind == -1)
	{
		for (int i = 0; i < adj2[start].size(); i++)
		{
			if (ind == -1 || (cross(V[start], V[adj2[start][ind]], V[adj2[start][i]]) == 2
				&& euclidean(V[start], V[adj2[start][ind]])>euclidean(V[start], V[adj2[start][i]])))
				ind = i;
		}
	}
	if (ind == -1)
	{
		for (int i = 0; i < adj2[start].size(); i++)
		{
			if (ind == -1 || (cross(V[start], V[adj2[start][ind]], V[adj2[start][i]]) == 0
				&& euclidean(V[start], V[adj2[start][ind]])>euclidean(V[start], V[adj2[start][i]])))
				ind = i;
		}
	}
	visited[start].insert(ind);
	dfs2(adj2[start][ind]);
	bool mark2[2 * N];
	for (int i = 0; i < k; i++)
	{
		mark2[i] = false;
	}
	int start2 = 0;
	set<vertex> input;
	for (int i = 0; i < n; i++)
	{
		input.insert(P[i]);
		if (P[i].first < P[start2].first || (fabs(P[i].first - P[start2].first) < eps && P[i].second < P[start2].second))
			start2 = i;
	}

	vector<int> sol2,sol;
	sol2.push_back(tsp2[0]);
	mark2[tsp2[0]] = true;
	double cost2 = 0, cost=0;
	for (int i = 0; i < tsp2.size(); i++)
		if (mark2[tsp2[i]] == false && input.find(V[tsp2[i]])!= input.end())
		{
			mark2[tsp2[i]] = true;
			cost2 += euclidean(V[tsp2[i]],V[sol2.back()]);
			sol2.push_back(tsp2[i]);
		}
	//close the tour
	cost2 += euclidean(V[sol2[0]], V[sol2.back()]);
	sol2.push_back(sol2[0]);
	cout << cost2 << " ";

	tsp.push_back(start2);
	ind = -1;
	for (int i = 0; i < tree[start2].size(); i++)
	{
		if (ind == -1 || cross(P[start2], P[tree[start2][ind]], P[tree[start2][i]]) ==1)
			ind = i;
	}
	if (ind == -1)
	{
		for (int i = 0; i < tree[start2].size(); i++)
		{
			if (ind == -1 || (cross(P[start2], P[tree[start2][ind]], P[tree[start2][i]]) == 2 
				&& euclidean(P[start2], P[tree[start2][ind]])>euclidean(P[start2], P[tree[start2][i]])))
				ind = i;
		}
	}
	//tsp.push_back(tree[start2][ind]);
	for (int i = 0; i < n; i++)
		visited[i].clear();
	visited[start2].insert(ind);
	dfs(tree[start2][ind]);
	for (int i = 0; i < n; i++)
		mark[i] = false;
	for (int i = 0; i < tsp.size(); i++)
	{
		if (mark[tsp[i]] == false)
		{
			mark[tsp[i]] = true;
			sol.push_back(tsp[i]);
		}
	}
	for (int i = 1; i < sol.size(); i++)
	{
		cost += euclidean(P[sol[i - 1]], P[sol[i]]);
	}
	cost += euclidean(P[sol.back()], P[sol[0]]);

	cout << cost << endl;
	sol.push_back(sol[0]);

	cout << "input: " << endl;
	for (int j = 0; j < n; j++)
	{
		cout << P[j].first << " " << P[j].second << endl;
	}
	cout << "\n MST, snowflake: ";
	cout << mst << " ";
	cout << snowflake << " " << snowflake / mst << endl;
	cout << "snowflake edges: " << endl;
	for (int i = 0; i < q.size(); i++)
	{
		cout << q[i].first.first << " " << q[i].first.second << " " << q[i].second.first << " " << q[i].second.second << endl;
	}
	cout << "MST edges: " << endl;
	for (int i = 0; i < n; i++)
	{
		for (int j = 0; j < tree[i].size(); j++)
		if (i < tree[i][j])
			cout << P[i].first << " " << P[i].second << " " << P[tree[i][j]].first << " " << P[tree[i][j]].second << endl;
	}
	cout << "Snow TSP:" << endl;
	for (int i = 0; i < sol2.size(); i++)
		cout << V[sol2[i]].first << " " << V[sol2[i]].second << endl;
	cout << "TSP built on MST (edges): " << endl;
	for (int i = 0; i < sol.size(); i++)
		cout << P[sol[i]].first << " " << P[sol[i]].second << endl;
	cout << endl;
	//cout << tsp.size() << " " << n << " " << tsp2.size() << " "  << k << endl;
	//cout << endl;
	//for (int i = 0; i < tsp.size(); i++)
	//	cout << P[tsp[i]].first << " " << P[tsp[i]].second << endl;
	return 0;
}