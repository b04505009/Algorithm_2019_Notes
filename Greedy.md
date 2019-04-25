# Greedy Algorithm
## Concept
- builds up a solution in small steps, **choosing a decision at each step myopically** to optimize some underlying criterion
- Intuitive and fast
- Usually not optimal
- prove optimality
    1. The greedy algorithm stays ahead.
    2. An exchange argument.
## Interval Scheduling Problem
- Given: Set of requests {1, 2, ..., n}, ith request corresponds to an interval with start time s(i) and finish time f(i)
    - interval i: $[s(i), f(i))$
- Find a compatible subset of requests of maximum size
    - compatible: 不重疊
    - maximum: optimal
- Repeat
    -  Use a simple rule to select a first request i1
    -  Once i<sub>1</sub> is selected, reject all requests incompatible with i<sub>1</sub>.
- ![](https://i.imgur.com/MDwxz2i.png)
- ![](https://i.imgur.com/MCIle6y.png)
    - A is a compatible set of requests because of line 5
- prove optimality
    - greedy algorithm **stays ahead**
    - 假設有最佳解O，證明|A| = |O| (不一定要完全相同，只要cardinality一樣就好)
    - First lemma: ![](https://i.imgur.com/6VTj6jl.png)
        - 還不知道k跟m誰大誰小
        - proof by induciton:
            - Basis step: for r = 1, f(i<sub>1</sub>) ≤ f(j<sub>1</sub>)
                - 因為i<sub>1</sub>必是所有人中結束時間最早的，而j<sub>1</sub>只是從O這個subset排序出來結束時間最早的
            - 假設r-1時成立: f(i<sub>r-1</sub>) ≤ f(j<sub>r-1</sub>) -- (1)
                - 因為O is compatible${\rightarrow}$f(j<sub>r-1</sub>) ≤ s(j<sub>r</sub>) -- (2)
                - (1) + (2) ${\rightarrow}$ f(i<sub>r-1</sub>) ≤ s(j<sub>r</sub>) ${\rightarrow}$ j<sub>r</sub>跟i<sub>r-1</sub>不重疊 ${\rightarrow}$ j<sub>r</sub> ${\in}$ R after i<sub>r-1</sub> is selected in line 5
                - According to line 3,f(i<sub>r</sub>) ≤ f(j<sub>r</sub>)
            - j<sub>r</sub>跟i<sub>r</sub>都在R裡(因為都跟i<sub>r-1</sub> compatible)，但greedy最後選擇i<sub>r</sub>，所以f(i<sub>r</sub>)<=f(j<sub>r</sub>)
        - ![](https://i.imgur.com/wfVGeGt.png)
        - small conclusion: greedy結果的每個finish time都小於O的finish time
    -  The greedy algorithm returns an optimal set A
        - Proof by contradiction
            - 假設A不是最佳解${\rightarrow}$|O|= m > k = |A|
            - 因為f(i<sub>k</sub>)≤f(j<sub>k</sub>)而且|O| > |A|${\rightarrow}$O裡至少有j<sub>k+1</sub>
                - ![](https://i.imgur.com/0ffJ1JM.png)
            - f(i<sub>k</sub>) ≤  f(j<sub>k</sub>) ≤ f(j<sub>k+1</sub>)${\rightarrow}$j<sub>k+1</sub>跟i<sub>k</sub> compatible${\rightarrow}$j<sub>k+1</sub>${\in}$R
            - greedy只有在R為空時才停止，但是卻在i<sub>k</sub>就停止了，矛盾
- Running time
    - O(n<sup>2</sup>):
        - Initialization: 
            - O(n log n): sort R in ascending order of f(i) (根據finish time排序)
        - line 5: 
            - 第一次檢查(n-1)個點跟i是否compatible，第二次(n-2)....總共O(n<sup>2</sup>)

    - O(n log n):
        - Initialization:
            - O(n log n): sort R in ascending order of f(i) (根據finish time排序)
            - O(n): construct S, S[i] = s(i)
                - 記錄所有人的start time
        - Lines 3 and 5:
            - O(n): 只需掃過R一次
            - 檢查compatible: 檢查f(i)是否小於s(j)
            - 只檢查下一個(j=i+1)是否跟i compatible，其餘的交給後面檢查
## Interval partitioning
- multiple resources
- use as few resources as possible
- a.k.a. the interval coloring problem: one resource = one color
- Given: Set of requests {1, 2, ..., n}, ith request corresponds an interval with start time s(i) and finish time f(i)
    - interval i: $[s(i), f(i))$
- Goal: Partition these requests into a **minimum** number of **compatible** subsets, each corresponds to one resource
    - 用最少資源跑完所有工作
- depth: a set of intervals is the maximum number that pass over any single point on the time-line.
    - 任意時刻需要的最大資源數(定義上不等於總共所需資源數)
- Lemma: 在interval partitioning的問題下，總共所需資源至少為depth (lower bound)
    - proof:
    - 在產生depth的那個時間點，有d個intervalI<sub>1</sub>, ..., I<sub>d</sub>都經過該時間點
    - 這d個interval都需要resources，所以至少需要d個這d個interval都需要resources
- Use only d resources (depth) to schedule all requests
    - prove the optimality
        1. 找到一個所有解都必須符合的bound
        2. 證明該演算法總是可以達到bound的結果
- Greedy Algorithm
    - ![](https://i.imgur.com/FeQjgeg.png)
        1. 把interval根據starting time排序
        2. 對1到n中第j個interval:
        3. ${\ \ \ \ }$把所有跟j不compatible的label排除
        4. ${\ \ \ \ }$如果能從{1, 2, ..., d}中找到沒被排除的label
        5. ${\ \ \ \ \ \ \ \ }$把label assign給j
        6. ${\ \ \ \ }$否則不label
    - Lines 3~5 implementation: 找到compatible with j的resource並label
        - 紀錄f(label<sub>i</sub>): label<sub>i</sub>的最後一個interval的finish time
        - check compatibility: f(label<sub>i</sub>) ≤ s(I<sub>j</sub>)
-  找出depth:
    -  ![](https://i.imgur.com/SAkUH3I.png)

    1. 把finish time跟start time一起排序
        - 若有finish time跟start time剛好切在同個時間點，則finish time優先
    2. 從頭掃到尾，resource遇到start time表示使用資源就加1，遇到finish time表示釋放資源就減1，紀錄resource的max值即為depth
- Optimality
    - The greedy algorithm assigns every interval a label, and no two overlapping intervals receive the same label.
        - proof:
            1. 所有interval都會得到label(line 6不會發生)
                - 假設interval I<sub>j</sub>跟前面的t個interval overlap${\rightarrow}$t+1個interval會重疊於s(j)
                - t+1 ≤ depth ${\rightarrow}$t ≤ depth - 1${\rightarrow}$至少還剩一個label可以assign給I<sub>j</sub>
            2. 兩個overlap的interval不會得到相同的label
                - 假設I<sub>i</sub>跟I<sub>j</sub> overlap，i < j
                - 當for迴圈執行到I<sub>j</sub>時，I<sub>i</sub>在line 3會被exclude(因為兩個overlap)
                - 所以不可能I<sub>i</sub>跟I<sub>j</sub>有相同label
        - 因為greedy只需要depth數量的label，符合lower bound${\rightarrow}$ Optimal!
- Interval graph (Intersection graph)
    - 每個interval對應一個node，若兩個interval overlap，則用edge連接兩個node
    - 相鄰的兩個點表示其overlap，必須assign不同顏色(resource)，可轉換成coloring問題
##  Scheduling to Minimize Lateness
- Given: A single resource is available starting at time s. A set of requests {1, 2, ..., n}, request i requires a contiguous interval of length t<sub>i</sub> and has a **deadline** d<sub>i</sub>
    -  所需作業時間及期限
- Goal: Schedule all requests without overlapping so as to minimize the maximum lateness
    - Lateness: l<sub>i</sub> = max{0, f(i) – d<sub>i</sub>}.
    - 遲交時間最小化
- ![](https://i.imgur.com/PYEwHO9.png)
    1. 所需時間短的不一定緊急
    2. 餘裕最小(越緊急的越先做): 若所需時間長，可能使其他工作遲交的時間太長
- ![](https://i.imgur.com/8n10ogQ.png)
    - no idle time
        - ![](https://i.imgur.com/tn5JTX8.png)
        - optimal的解如果中間有idle time，則idle time可被壓縮掉，不影響optimality
- **Exchange argument**: Gradually transform an optimal solution to the one found by the greedy algorithm without hurting its quality.
    - 對一個optimal solution，把其中不符合greedy rule的部分換成greedy的形式，仍能保持optimality
- **inversion (倒轉)**: An inversion in schedule S is a pair of requests i and j such that s(i) < s(j) but d<sub>j</sub> < d<sub>i</sub>
    - 比較早開始但是比較晚才要交
- Lemma 1: All schedules without inversions and without idle time have the same maximum lateness.
    - proof:
        - ![](https://i.imgur.com/Y95zvT7.png)
        - 如果兩種schedule沒有晚做但是要早交的情況，且中間沒有idle time，則這兩種schedule皆以deadline順序做排程，且只會在deadline相同的request上有不同的排序
        - 因為deadline時間相同，且所有相同deadline的request所需時間總和相同，所以lateness不會因schedule的順序改變
- Lemma 2: There is an optimal schedule with no inversions and no idle time
    - ![](https://i.imgur.com/7yCltgT.png)
        1. 如果有inversion發生在job i 跟 j，假設j被排在i之後，且d<sub>j</sub> < d<sub>i</sub>
        2. 把 i 跟 j 互換可以消除inversion
        3. 因為d<sub>j</sub> < d<sub>i</sub>，所以把j換到i前面不可能增加lateness (甚至可能減少lateness)，可維持optimality
        - 即使不相鄰也能有相同結論
- Theorem: The greedy schedule S is optimal.
    - proof by contradiction:
        - 假設O 為有inversion的optimal solution
        - 假設O沒有idle time (idle time可被壓縮)
        - 若O沒有inversion，則S = O (因為greedy的結果即為沒有inversion沒有idle time，又根據Lemma 1，可推得S 跟 O 有相同maximun lateness)
        - 若O有inversion，則當我們把inversion pair互換時，maximun lateness又可能變更小，與optimal的前提矛盾

## Shortest Paths
- Given:
    - Directed graph G = (V, E)
    - Length l<sub>e</sub> = length of edge e = (u, v) ${\in}$ E
        - 成本(距離、時間) ≥ 0
    - Source s
- Goal:
    - 從s到V中其他點的最短路徑P<sub>v</sub>
        - Length of path: path經過的length總和
- ![](https://i.imgur.com/i5X2TFf.png)
    - 檢查所有從S裡的node u到不在S裡的node v的最小距離d(u)+l<sub>e</sub>，把距離最小的node v放進S，更新d(v)
- Correctness
    - ![](https://i.imgur.com/cNUJVc9.png)
    - 一旦node u被放進S，d(u)即為最短距離，不會再因放入新的node改變
    - Proof by induction on |S|:
        - Basis step: S只有s在裡面，d(s)=0
        - Inductive step:
            - 假設|S| = k ≥ 1時敘述為真
            - 令下一個要被放進S的node為v，(u, v)為從s到v的最短路徑P<sub>v</sub>的最後一段edge，P<sub>v</sub> = P<sub>u</sub> + (u, v)
            - 根據假設，因u已經在S內，P<sub>u</sub>為s到u的最短路徑
            - 考慮其他從s到v路徑的可能路徑P，此路徑必會跨越S與不是S的點，另x為交界處S內的點，y為交界處S外的點
                - 如果沒有y，這輪應該選擇從x出發而非u
            - 因為line 4會選擇d'(v) = (d(u)+l<sub>e</sub>)最短的v點放入S，所以P不可能比P<sub>v</sub>還短
                - 若
            - ![](https://i.imgur.com/vFbTzmz.png)

                - d'(v)就已經比d(y)小了，且l<sub>e''=(y,v)</sub> ≥ 0
                - 所以新的距離d(v)也是最短的距離
                - Dijkstra重要設定: l<sub>e</sub> ≥ 0
            - ![](https://i.imgur.com/eV7RMAq.png)

- Implementation
    -  ![](https://i.imgur.com/9pdMY0g.png)
    -  ![](https://i.imgur.com/kJfzdVL.png)
    - 所有node放在min priority queue裡，每輪更新看得到的node的cost，每次從min priority queue中deque最小的node放進S
## Recap Heaps: Priority Queues
- Priority Queue
    - Each element has a priority (key)
    - Only the element with highest (or lowest) priority can be deleted
        - Max priority queue, or min priority queue
    - An element with arbitrary priority can be inserted into the queue at any time
    - ![](https://i.imgur.com/vvpoWA8.png)
- Heap
    - A max heap is
        - 爸媽的key比小孩大的tree
            - root的key最大
        – A complete binary tree
    - Implementation
        - ![](https://i.imgur.com/lOCJabD.png)
    - Insertion into a Max Heap
        - ![](https://i.imgur.com/eMWoKeF.png)
        - 把新node先放在尾端，如果新node的key比他爸媽的key大，把新node跟他爸媽交換(Bubble up)
        - Time complexity: O(lg n)
    - Deletion from a Max Heap
        - ![](https://i.imgur.com/VPt34b5.png)
        - 把root拿走(key最大)，把最尾端的node放到root，如果這個node比他的子孫小，把他跟他子孫交換(trickle down)
        - Time complexity: O(lg n)
    - Max Heapify
        - 從下面往上修正
        - ![](https://i.imgur.com/hMWKfZ4.png)
            - 數學歸納法，假設小孩已經是heap
        - ![](https://i.imgur.com/igPy4oD.png)
        - Time complexity: O(*n*lg n)
## Minimum Spanning Trees
- Given: Undirected graph G = (V, E)
- cost c<sub>e</sub> for each edge e = (u, v) ${\in}$ V
- Goal:
    - 找到一個edges的子集 T ⊆ E 使得:
        - 連結graph中所有點
        - 總成本最小
- (V, T)會是什麼？
    1. (V, T)一定要連起來
    2. (V, T)沒有cycle
        - 如果有cycle，拿掉cycle中某條edge，cycle中的點仍然保持連結，且cost減少
    - (V, T)是tree
- Greedy Algorithms
    - Kruskal's algorithm
        1. T = {}
        2. 把edge的cost從低到高排列
        3. 依序把edge e放進T，但如果e放進T會使T出現cycle，則捨棄
    - Prim's algorithm: (c.f. Dijkstra’s algorithm)
        1. 從任意點出發(因為最後T一定會連接所有點)
        2. 每次把從T看出去cost最小的edge放入T
    - Reverse-delete algorithm: (reverse of Kruskal’s algorithm)
        1. T = E
        2. 把edge的cost從高到低排列
        3. 依序把edge e從T拿掉，但如果e從T拿掉會破壞連結性(出現孤島)，則不拿掉e
    - Cut Property
        - Optimality of **Kruskal’s** & **Prim’s algorithms**
        - 假設所有cost c<sub>e</sub> 都不一樣
        - ![](https://i.imgur.com/ZNgGN9x.png)
            - 從所有點中劃分出一個subset，subset交界的edge中cost最小的edge e是safe edge，所有MST都應該包含e
            - Wrong Pf: Exchange argument
                - T為一個任意的spanning tree而且沒有包含e，希望證明T不是MST
                - T為spanning tree，T一定至少有一條edge通過subset交界
                - 因為e是交界上cost最小的edge，c<sub>e</sub> < c<sub>f</sub>
                - 所以T – {f} + {e}有更小的cost
                    - 但是T – {f} + {e}還是spanning tree嗎？
                    - Spanning tree: connected & acyclic
                    - maybe not connected
            - 需要滿足spanning tree的條件
            - Modified Pf: Exchange argument
                - ![](https://i.imgur.com/ob4y5Dg.png)

                - T為一個任意的spanning tree而且沒有包含e，希望證明T不是MST
                - T為spanning tree，T一定至少有一條edge e'通過subset交界，e'=(v',w')，v' ${\in}$ S and w' ${\in}$ V–S
                - T' = T – {e'} + {e}是spanning tree
                    - (V, T') is connected
                        - 因為T為spanning tree，所以S內所有點都相通，S外所有點也相通，交界處的e'被拿掉只有使內外斷絕連結，所以可以繞路改由e相通
                    - (V, T') must be acyclic
                        - 因為T為spanning tree，所以S內S外都沒有cycle，只有可能在交界處增加e時會產生cycle，但是因為我們同時拿掉了e'，所以不會有cycle
                    - c<sub>e</sub> < c<sub>e'</sub>，所以T'的cost比T小
                - ![](https://i.imgur.com/uYMfOfh.png)

    - Cycle Property
        - ![](https://i.imgur.com/Q6qTTqC.png)
            - Pf: Exchange argument! (Similar to Cut Property)
            - ![](https://i.imgur.com/X3JjlP5.png)

- Implementing MST Algorithms

    - Dijkstra’s Algorithm
        - ![](https://i.imgur.com/1sntc54.png)
    - Prim’s Algorithm
        - ![](https://i.imgur.com/E1KCtgl.png)
            - 只要看cost最小的tree edge就好，不用看從s出發的最小cost
    - Kruskal’s Algorithm
        - ![](https://i.imgur.com/EatJKbG.png)
        - 如果e<sub>i</sub>的兩個端點已經屬於同個tree，就捨棄e<sub>i</sub>
    - The Union-Find Data Structure
        - **Union-find** data structure represents **disjoint sets**
            - Disjoint sets: elements are disjoint
            - 每個set有一個代表
            - Operations:
                - MakeUnionFind(S): 建立一個set
                - Find(u): 找u屬於哪個set，return該set的代表
                - Union(A, B): 合併 A 跟 B，重新選擇新的代表
            - Implementation: **disjoint-set forest**
                - 代表為root，連結由小孩指向父母
                - Union: 把比較小的樹並到比較大的樹裡(union by rank)
                - Find: 找到之後直接把他直接指到root(path compression)
                - ![](https://i.imgur.com/1Po52A6.png)

            - Running time: union by rank + path compression
                - amortized running time per operation is O(α(n)), α(n) < 5
                    - amortized running time: 平均分攤的running time
            - Implementing Kruskal’s Algorithm
                - ![](https://i.imgur.com/L5pRoqw.png)
                    - 每個subtree用disjoint set表示，一開始有n個set
                    - Line 1: 排序(用heap)
                        - O(*m*lg m)
                    - Line 4: 只要find(u)不等於find(v)，就把e<sub>j</sub>放進T
                        - 每條edge有兩端，find兩次
                        - 2m次
                    - Line 5: 把e<sub>j</sub>並到T裡
                        - tree最多n-1條edge
                    - Comparison sort + simple disjoint set: O(m log n)
                    - Linear sort + union-find: O(m α(m, n))





        



  
   

