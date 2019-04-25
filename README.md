# Graph
## path
- a sequence P of nodes v1, v2, ..., vk-1, vk with the property that each consecutive pair vi, vi+1 is joined by an edge in E.
- simple: path上沒有重複走過的點(distinct)
- cycle: path至少多於2個點，頭尾相連，中間的點distinct
- connected: 如果任意點到任意點之間都有path，則graph is connected
- distance: minimum number of edges in a u-v path
## tree
- An undirected graph is a tree if it is **connected** and does **not contain a cycle**
- G若滿足兩個條件即為樹:
    - G is connected.
    - G does not contain a cycle.
    - G has n-1 edges.
- rooted tree: a tree with its root at r
## BFS
- 從s(source)開始一層一層往外擴散直到visit所有可到達的點
- Layer ${L_i}$: i is the time that a node is reached.
    - $L_0$ = {s}
    - $L_{j+1}$ = $L_{j}$的鄰居中不屬於更上層layer的node
    - i: 從s到$L_{i}$的distance
- BFS Tree:
    - tree edge v.s. non tree edge
    - 一棵BFS tree中，若x屬於$L_{i}$，y屬於$L_{j}$，且(x,y)有edge連接(不一定是tree edge)，則i跟j最多差1
    - proof(by contradiction):
        1. 不失一般性，假設j>i，且j-i>1
        2. 根據定義，x屬於$L_{i}$，則x的鄰居不是屬於$L_{i+1}$就是屬於更上層的layer
        3. 因為(x,y)有edge連接，(x,y)必互為鄰居，且y屬於$L_{j}{\ }{\rightarrow}$ j ≤ i+1。
        4. ${\rightarrow}{\leftarrow}$
    - non tree edge: 跟自己同層(兄弟姊妹)或是差一層但不是父母(叔叔姪子...) 
                
![](https://i.imgur.com/k7PTTqf.png)

## DFS
- 從s開始一直走，直到走到dead end，再回頭換別條路
- ![](https://i.imgur.com/63bfSJj.png)
- 一條edge會被檢查兩次(去跟回)
- DFS tree
    - tree edge必連接爸爸跟小孩，non tree edge必連接祖先子孫(跨層)
    - 一棵DFS tree中，若(x,y)之間為non tree edge，則x, y為祖先子孫關係
    - proof:
        - 不失一般性，假設x先被看到
        - (x,y)為non tree edge表示x看y時y已經被explored
        - 但是在剛看到x時y還沒explored ${\rightarrow}$ y是在剛呼叫DFS(x)跟DFS(x)的遞迴完全結束的過程中被發現的
        - y必存在由x往下的tree之中 ${\rightarrow}$ y為x的子孫
## connected component
- A connected component containing s is the set of nodes that are **reachable** from s.
- 通常取到最大
- ![](https://i.imgur.com/CFVYXVt.png)
- ![](https://i.imgur.com/VnHa07g.png)
- Correctness:
    - 所有R裡面的node都reachable from s
        - 課本
    - 所有不屬於R的node都unreachable from s
        - 反證法
## Implementation
- Graph representing
    - A graph G(V,E):
        - |V| = the number of nodes = n
        - |E| = the number of edges = m
    - n – 1 (lower bound of edges, tree) ≤ m ≤  ${\binom{n}{2}}$ (upper bound of edges) ≤ n<sup>2</sup> for a connected graph
    - O(n) v.s O(n<sup>2</sup>)
    - Linear time (O(m+n)):
        - adjacency matrix:
            - graph G = (V, E) with n nodes, V = {1, ..., n}
            - adjacency matrix of G is an nxn martix A where
                -  A[u, v] = 1 if (u, v) ${\in}$ E;
                -  A[u, v] = 0, otherwise.
            - time
                - O(1): check if (u, v) ${\in}$ E
                - O(n): 找出任一點的所有鄰居(掃過row跟column)
                    - visit many 0 for sparse graph
             - space
                 - O(n<sup>2</sup>)
         - adjacency list:
             - adjacency list of G is an array Adj[] of n lists, one for each node represents its neighbors
                 - Adj[u] = a linked list of {v | (u, v) ${\in}$ E}.
             - degree of u: u有多少鄰居
             - time:
                 - O(deg(u)) time for checking one edge or all neighbors of a node.
             - space:
                 - undirected: n+2m ${\rightarrow}$O(n+m)
                 - directed: n+m ${\rightarrow}$O(n+m)
             - indegree and outdegree for directed graph
 - Implementing BFS
     - ![](https://i.imgur.com/d2laSvV.png)
 - Implementing DFS
     - ![](https://i.imgur.com/6Xl5axW.png)
 - Summary
     - ![](https://i.imgur.com/2ltkWku.png)
## Testing Bipartiteness
 - bipartite graph (bigraph): a graph whose nodes can be partitioned into sets X and Y in such a way that every edge has one one end in X and the other end in Y.
 - X and Y are two disjoint sets
 - No two nodes within the same set are adjacent
 - node可分成兩個group，group內的node不相連，所有edge的兩端必落在不同group
 - Check if bipartite: Color the nodes with blue and red (two-coloring)
 - If a graph G is bipartite, then it cannot contain an odd cycle.
     - ![](https://i.imgur.com/4nuFJ3n.png)
 - Procejure
     1. 假設G=(V,E)是connected
         - 若不是，不同的connected component分開執行
     2. 選一個任意起始點s塗成紅色
     3. 把s的鄰居塗成藍色
     4. 重複塗色直到整張圖都塗完顏色
     5. Test bipartiteness: 所有edge兩端都是不同顏色
     - 如果欲塗色的點已經被塗色而且其顏色跟欲塗的顏色不同，則不是bipartite graph
 - 可用BFS實作
     - time: O(m+n)
     - 在最後加上著色的動作
     - ![](https://i.imgur.com/t8mkzDo.png)
 - Correctness
     - 2 case:
         1. 沒有連接同層間node(兄弟姊妹)的edge${\rightarrow}$bipartite
         2. 有連接同層間node(兄弟姊妹)的edge${\rightarrow}$有odd cycle${\rightarrow}$not bipartite
     - BFS特性: Let x${\in}$L<sub>i</sub>, y${\in}$L<sub>j</sub>, and (x, y) ${\in}$E. Then i and j differ by at most 1.
         - edge兩端的layer差必小於等於1
     - proof case 2:
         1. 假設(x,y)是兩端皆在同個layer L<sub>j</sub>的edge
         2. z = lca(x, y) = lowest common ancestor
             - x跟y往上層layer看時最早的共同祖先
             - ![](https://i.imgur.com/9bKtjCJ.png)
         3. Let L<sub>i</sub> be the layer containing z
         4. 考慮經過x,y,z及(x,y)的cycle
         5. 長度為1+2(j-i)，為奇數

## Connectivity in Directed Graphs
- **directed** graph: **asymmetric** relationships
- Representation: Adjacency list
    - Each node is associated with two lists, to which and from which
- mutually reachable: 對node u跟v，有從u到v的path，也有從v到u的path
- strongly connected: every pair of nodes are mutually reachable
- Lemma: If u and v are mutually reachable, and v and w are mutually reachable, then u and w are mutually reachable.
    - ![](https://i.imgur.com/HdCvKrY.png)
- determine strongly connectivity in linear time
    1. 選擇graph G中的任意起始點s
    2. R = BFS(s, G)
    3. R<sup>rev</sup> = BFS(s, G<sup>rev</sup>)
        - 因為要雙向都有path可到達對方，把G的edge方向全部反轉再做一次，就可以知道是否有反向的path連結
    4. 如果(R = V = R<sup>rev</sup>)則為strongly connected
    - time: O(m+n)
- Strong Component
    - strong component containing s in a directed graph is the maximal set of all v s.t. s and v are mutually reachable.
    - Theorem: For any two nodes s and t in a directed graph, their strong components are either identical or disjoint.
        - directed graph中的任意兩點，不是在同個strong component就是在不同的strong component
        - proof:
            - Identical if s and t are mutually reachable
            - Disjoint if s and t are not mutually reachable
## Directed Acyclic Graphs (DAG)
- an undirected graph has no cycles: tree (or forest)
- DAG: directed graph without cycles
## Topological Ordering
- Given a directed graph G, a topological ordering is an ordering of its nodes as v1, v2, ..., vn so that for every edge (vi, vj), we have i<j.
    - node可以照順序排好，排好後edge的方向都相同
    - ![](https://i.imgur.com/FUU5aYy.png)

    - Precedence constraints: edge (vi, vj) means vi must precede vj
- Lemma: If G has a topological ordering, then G is a DAG.
    - If G is a DAG, then does G have a topological ordering?
        - yes
    - proof by contradiction:
        - assume graph has cycle
- Lemma: In every DAG G, there is a node with no incoming edges.
    - proof by contradiction:
        1. 假設某DAG中每一點都有incoming edge
        2. 任選一點v，挑一條他的incoming edge往回走
        3. 因為每個點都有incoming edge，此動作可以一直重複，沒有上限
        4. 重複n+1次後，因為只有n個點，我們必會走到重複的點上
        5. C為兩次走到重複點w之間走過的點，C是cycle${\rightarrow}$矛盾
        - ![](https://i.imgur.com/4HeQVIU.png)
- ![](https://i.imgur.com/Opejt6b.png)
- Lemma: If G is a DAG, then G has a topological ordering.
    - proof by induction
        1. base case: n=1時成立(只有一個點，直接編號1號)
        2. inductive step:
            - 假設n個點時成立: n個點的DAG有topological ordering
            - 對於一個有n+1點的DAG，把一個沒有incoming edge的點分出來
                - ![](https://i.imgur.com/ivfSmon.png)
            - 拿掉一個點及其連接的edge並不會創造cycle ${\rightarrow}$ G – {v}是有n個點的DAG
            - 根據假設，有n個點的DAG有topological ordering
            - 把v放在topological ordering的最前端是安全的(不會有cycle)
            - ${\rightarrow}$ G也有topological ordering
- Linear-Time Algorithm
    - ![](https://i.imgur.com/zeA10Jq.png)
    - time
    - O(n<sup>2</sup>): n個點執行n次函式，每次執行函式第1行找沒有incoming edge的點要掃過{n, n-1, n-2 ...}個點
    - O(m+n): 
        - Initialization: 建立adjacency list及紀錄indeg，把沒有incoming edge的點放到S
            - indeg(w) = # of incoming edges from undeleted nodes
            - S = set of nodes without incoming edges from undeleted nodes
            - O(m+n)
        - 原算法的line 3改為：
            1. Remove v from S
            2. 把所有從v連到w的indeg(w)減1，如果indeg(w)為0把w放進S
                - 單獨動作皆為O(1)
                - 這步會做m次(m條edge)
            - O(m+n) 
        - line 4改為check S


































