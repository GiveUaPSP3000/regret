#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<math.h>
#include<pthread.h>

#define MAX(a,b) ((a)>(b)?(a):(b)) //比较大小 
#define Height(p) ((p==NULL)?0:(((Pr *)(p))->height)) // 求高度 

/*结点数极值的宏定义*/
#define	MAXVER		150000											//头节点容量
#define MAXSIZE		80												//栈最大存储容量
#define INF			0x3f3f3f3f										//无穷大
#define BCJ			100000											//并查集种类数
#define MAXCYCLE	3500000											//总图行数
#define SUBMAXCYCLE	8000											//分图行数
#define	MX			500												//临时存储当前图的环的图的行数
#define MY			80												//临时存储当前图的环的图的列数

/*结点三状态的宏定义*/
#define	statenew	-1												//未访问状态
#define stateing	-2												//正在访问的状态
#define stated		-3												//已访问状态

/*子节点结构体定义*/
typedef struct {
	int id;
	int hashstate;													//在hash表中的位置
	struct HashNode *next;
}HashNode;

/*头结点结构体定义*/
typedef struct {
	int id;
	int state;														//结点当前状态（三状态）
	int ctype;														//并查集索引号（是否在其他图遍历过的结点）
	int stacknum;													//在当前栈的位置（可避免成环后的遍历）
	int maplocation[MX][2];											//在map中在第几个环以及其在环中的位置
	int maptop;														//当前maplocation记录到第几个了
	struct HashNode *next;
}HeadNode;

/*临时环存储图*/
typedef struct {
	HeadNode ***cyclemap;											//装载HeadNode指针的二维数组
	int *length;													//二维数组每行的长度
	int t;															//当前图的环的个数
}MAPNode;

typedef struct NN Pr;
/*输出结点*/
struct NN
{
	int Key;
	int height;
	Pr *Left;
	Pr *Right;
};

Pr *nodeCreate(int Key) //创建节点 
{
	Pr *p = (Pr *)malloc(sizeof(Pr));
	p->height = 0;
	p->Key = Key;
	p->Left = NULL;
	p->Right = NULL;
	return p;
}

Pr *lL(Pr *k2)
{
	Pr *k1 = k2->Left;
	k2->Left = k1->Right;
	k1->Right = k2;
	k2->height = MAX(Height(k2->Left), Height(k2->Right)) + 1;
	k1->height = MAX(Height(k1->Left), Height(k1->Right)) + 1;

	return k1;
}

Pr *rR(Pr *k1)
{
	Pr *k2 = k1->Right;
	k1->Right = k2->Left;
	k2->Left = k1;
	k1->height = MAX(Height(k1->Left), Height(k1->Right)) + 1;
	k2->height = MAX(Height(k2->Left), Height(k2->Right)) + 1;

	return k2;
}

Pr *lR(Pr *k3)
{
	k3->Left = rR(k3->Left);
	return lL(k3);
}

Pr *rL(Pr *k3)
{
	k3->Right = lL(k3->Right);
	return rR(k3);
}

/*线程传参结构体*/
typedef struct {
	Pr *prn;
	MAPNode *map;
	int len;
	int totall;
}Threadnode;

/*栈结构体定义*/
typedef struct node
{
	HeadNode **base;												//栈装的是存储指向HeadNode结点指针的数组
	int top;
}Sqstack;

/*初始化栈*/
void InitStack(Sqstack *S)
{
	S->base = (HeadNode **)malloc(sizeof(HeadNode*)*MAXSIZE);		//给栈分配数组空间
	if (!S->base)
		exit(0);
	S->top = 0;
}

/*结点入栈*/
void Push(Sqstack *S, HeadNode *i, int typenumber)
{
	i->stacknum = S->top;											//结点在栈的索引
	S->base[S->top++] = i;											//元素先入栈，指针后加一
	i->state = stateing;											//入栈元素都设置为正在访问状态
	i->ctype = typenumber;											//为入栈元素进行并查集
	i->maptop = 0;													//当前maplocation应记录第几个的
}

/*结点出栈*/
void Pop(Sqstack *S)
{
	HeadNode *i = S->base[--S->top];
	i->state = stated;
}

/*访问到正在访问的点，获得环*/
void Getnew(Sqstack *S, HeadNode *start, MAPNode *map)
{
	int i = start->stacknum;
	HeadNode **record = (HeadNode **)malloc(sizeof(HeadNode *)*MY);
	int ct = 0;
	int min = 0;
	for (; i < S->top; i++) {										//获得环,并求出环的最小点索引
		record[ct] = S->base[i];
		if (record[ct]->id < record[min]->id)
			min = ct;
		ct++;
		S->base[i]->maplocation[S->base[i]->maptop][0] = map->t;
		S->base[i]->maptop++;
	}																//当前min为record中最小值索引，ct为record元素个数
	int x = 0;
	map->length[map->t] = ct;										//map的length存放行的长度
	int l = min;
	do {															//将排好序的环放入cyclemap的maptop行中
		int pp = min % ct;
		map->cyclemap[map->t][x] = record[min%ct];
		map->cyclemap[map->t][x]->maplocation[map->cyclemap[map->t][x]->maptop - 1][1] = x;
		min++;
		x++;
	} while ((min + ct) % ct != l);
	map->t++;
}

/*访问到已经访问过的成环的点，获得环*/
void Getold(Sqstack *S, HeadNode *old, MAPNode *map) {
	int q = S->top - 1;
	int record[MAXCYCLE];
	memset(record, -1, sizeof(record));
	for (int i = 0; i < old->maptop; i++) {
		record[old->maplocation[i][0]] = old->maplocation[i][1];
	}
	while (q >= 0) {
		for (int i = 0; i < S->base[q]->maptop; i++) {
			int a = S->base[q]->maplocation[i][0];
			if (record[a] != -1) {
				HeadNode **u = (HeadNode**)malloc(sizeof(HeadNode)*MY);
				int b = record[a];														//从环的此点开始一直往后推，直到c位置
				record[a] = -1;
				int c = S->base[q]->maplocation[i][1];									//获得c位置
				int p = 0;
				int min = 0;
				for (int j = q; j < S->top; j++) {										//获得环,并求出环的最小点索引
					u[p] = S->base[j];
					if (u[p]->id < u[min]->id)
						min = p;
					p++;
					S->base[j]->maplocation[S->base[j]->maptop][0] = map->t;
					S->base[j]->maptop++;
				}
				HeadNode *l = map->cyclemap[a][b];
				int len = map->length[a];
				while (l->id != map->cyclemap[a][c]->id) {
					u[p] = l;
					if (u[p]->id < u[min]->id)
						min = p;
					p++;
					b = (b + 1) % len;
					l = map->cyclemap[a][b];
				}
				int x = 0;
				map->length[map->t] = p;												//map的length存放行的长度
				int k = min;
				do {																	//将排好序的环放入cyclemap的maptop行中
					map->cyclemap[map->t][x] = u[min%p];
					map->cyclemap[map->t][x]->maplocation[map->cyclemap[map->t][x]->maptop - 1][1] = x;
					min++;
					x++;
				} while ((min + p) % p != k);
				map->t++;
			}
		}
		q--;
	}
}

/*MAPNode初始化*/
MAPNode *CreatMAPNode() {
	MAPNode *map = (MAPNode *)malloc(sizeof(MAPNode));
	map->cyclemap = (HeadNode ***)malloc(sizeof(HeadNode **)*MAXCYCLE);
	map->length = (int *)malloc(sizeof(int)*MAXCYCLE);
	map->t = 0;
	for (int i = 0; i < MAXCYCLE; i++)
		map->cyclemap[i] = (HeadNode **)malloc(sizeof(HeadNode *)*MY);
	return map;
}

/*Hash表初始化*/
HeadNode **CreateHashMap() {
	HeadNode **hashmap = (HeadNode **)malloc(sizeof(HeadNode*)*MAXVER);
	for (int j = 0; j < MAXVER; j++) {
		hashmap[j] = (HeadNode *)malloc(sizeof(HeadNode));
		hashmap[j]->id = -1;
		hashmap[j]->state = statenew;								//所有元素设置为新元素
		hashmap[j]->ctype = 0;
		hashmap[j]->next = NULL;
	}
	return hashmap;
}

/*hash散列值获取*/
int hashval(HeadNode **hashmap, int key) {
	int pos = key % MAXVER;
	while (hashmap[pos]->id != -1 && hashmap[pos]->id != key)
		pos = (pos + 1) % MAXVER;
	return pos;
}

/*转出转入账户数据插入*/
void Put(HeadNode **hashmap, int *a) {
	int pos = hashval(hashmap, a[1]);
	HashNode *lnode = (HashNode*)malloc(sizeof(HashNode)), *hashnode;
	lnode->id = a[1];
	lnode->hashstate = pos;
	lnode->next = NULL;
	pos = hashval(hashmap, a[0]);
	if (hashmap[pos]->id != -1) {										//转出账户插入
		if (hashmap[pos]->next != NULL) {
			hashnode = hashmap[pos]->next;
			while (hashnode->next != NULL) hashnode = hashnode->next;
			hashnode->next = lnode;
		}
		else hashmap[pos]->next = lnode;
	}
	else {
		hashmap[pos]->id = a[0];
		hashmap[pos]->next = lnode;
	}
	if (hashmap[lnode->hashstate]->id == -1) {							//转入账户插入
		hashmap[lnode->hashstate]->id = a[1];
	}
}

/*邻接表的深度优先递归*/
void DFS(HeadNode **hashmap, Sqstack *S, MAPNode *map, int i, int typenumber)
{
	HashNode *q = hashmap[i]->next;
	while (q != NULL) {
		int a = hashmap[q->hashstate]->state;
		if (a == statenew) {
			Push(S, hashmap[q->hashstate], typenumber);
			DFS(hashmap, S, map, q->hashstate, typenumber);
		}
		else if (a == stateing) {
			Getnew(S, hashmap[q->hashstate], map);
		}
		else if (a == stated && hashmap[q->hashstate]->ctype == typenumber && hashmap[q->hashstate]->maptop > 0) {
			Getold(S, hashmap[q->hashstate], map);
		}
		q = q->next;
	}
	Pop(S);
}

int comp(MAPNode *map, int len, int a, int b) {
	for (int i = 0; i < len; i++) {
		if (map->cyclemap[a][i]->id != map->cyclemap[b][i]->id) {
			if (map->cyclemap[a][i]->id > map->cyclemap[b][i]->id)
				return 1;
			else return 0;
		}
	}
	return 2;
}

Pr *nodeInsert(MAPNode *map, Pr *root, int data, int len, int *totall) //插入 
{
	if (root == NULL)
	{
		root = nodeCreate(data);
		*totall+=1;
	}
	else if (comp(map, len, root->Key, data) == 1)
	{
		root->Left = nodeInsert(map,root->Left, data, len, totall);
		if (Height(root->Left) - Height(root->Right) == 2)
		{
			if (!comp(map, len, data, root->Left->Key))
			{
				root = lL(root);
			}
			else if (comp(map, len, data, root->Left->Key))
			{
				root = lR(root);
			}
		}
	}
	else if (comp(map, len, root->Key, data) == 0)
	{
		root->Right = nodeInsert(map, root->Right, data, len, totall);
		if (Height(root->Right) - Height(root->Left) == 2)
		{
			if (data > root->Right->Key)
			{
				root = rR(root);
			}
			else if (data <= root->Right->Key)
			{
				root = rL(root);
			}
		}
	}
	root->height = MAX(Height(root->Left), Height(root->Right)) + 1;

	return root;
}

void* px(Threadnode *threadnode) {
	for (int i = 0; i < threadnode->map->t; i++) {
		if (threadnode->map->length[i] == threadnode->len)
			threadnode->prn = nodeInsert(threadnode->map, threadnode->prn, i, threadnode->len,&(threadnode->totall));
	}
	//中序输出:中序遍历二叉查找树可以得到原关键字有序序列
	return NULL;
}

void InorderTraverse(MAPNode *map, Pr *pTree, FILE *fpWrite,int len)
{
	if (pTree) {
		InorderTraverse(map,pTree->Left, fpWrite, len);
		int j = 0;
		for (j = 0; j < len -1; j++) {
			fprintf(fpWrite, "%d,", map->cyclemap[pTree->Key][j]->id);
		}
		fprintf(fpWrite, "%d\n", map->cyclemap[pTree->Key][j]->id);
		InorderTraverse(map,pTree->Right, fpWrite, len);
	}
}

/*邻接表的深度遍历操作*/
void DFSTraverse(HeadNode **hashmap, Sqstack *S)
{
	MAPNode *map = CreatMAPNode();
	int typenumber = 0;
	for (int i = 0; i < MAXVER; i++) {
		if (hashmap[i]->ctype == 0 && hashmap[i]->id != -1) {
			typenumber++;
			Push(S, hashmap[i], typenumber);
			DFS(hashmap, S, map, i, typenumber);
		}
	}
	Pr *pr3 = NULL;
	Pr *pr4 = NULL;
	Pr *pr5 = NULL;
	Pr *pr6 = NULL;
	Pr *pr7 = NULL;
	Threadnode node3, node4, node5, node6, node7;
	node3.prn = pr3;
	node3.map = map;
	node3.len = 3;
	node3.totall = 0;
	node4.prn = pr4;
	node4.map = map;
	node4.len = 4;
	node4.totall = 0;
	node5.prn = pr5;
	node5.map = map;
	node5.len = 5;
	node5.totall = 0;
	node6.prn = pr6;
	node6.map = map;
	node6.len = 6;
	node6.totall = 0;
	node7.prn = pr7;
	node7.map = map;
	node7.len = 7;
	node7.totall = 0;
	pthread_t thread3, thread4, thread5, thread6, thread7;
	pthread_create(&thread3, NULL, px, &node3);
	pthread_create(&thread4, NULL, px, &node4);
	pthread_create(&thread5, NULL, px, &node5);
	pthread_create(&thread6, NULL, px, &node6);
	pthread_create(&thread7, NULL, px, &node7);
	pthread_join(thread3, NULL);
	pthread_join(thread4, NULL);
	pthread_join(thread5, NULL);
	pthread_join(thread6, NULL);
	pthread_join(thread7, NULL);
	FILE *fpWrite = fopen("//projects//student//result.txt", "w");
	fprintf(fpWrite, "%d\n", node3.totall + node4.totall + node5.totall + node6.totall + node7.totall);
	InorderTraverse(map, node3.prn, fpWrite, 3);
	InorderTraverse(map, node4.prn, fpWrite, 4);
	InorderTraverse(map, node5.prn, fpWrite, 5);
	InorderTraverse(map, node6.prn, fpWrite, 6);
	InorderTraverse(map, node7.prn, fpWrite, 7);
	fclose(fpWrite);
}

int main() {
	HeadNode **hashmap = CreateHashMap();
	int a[2];
	int b;
	FILE *fp = fopen("//data//test_data.txt", "r");
	while (!feof(fp))
	{
		fscanf(fp, "%d,%d,%d", &a[0], &a[1], &b);
		Put(hashmap, a);
	}
	fclose(fp);
	//创建栈
	Sqstack S;
	InitStack(&S);
	//深度遍历
	DFSTraverse(hashmap, &S);
	return 0;
}