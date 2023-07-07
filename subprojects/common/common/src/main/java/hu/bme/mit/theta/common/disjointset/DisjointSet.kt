package hu.bme.mit.theta.common.disjointset

class DisjointSet<T> {
    private val parent = mutableMapOf<T, T>()
    private val rank = mutableMapOf<T, Int>()

    fun makeSet(x: T) {
        parent[x] = x
        rank[x] = 0
    }

    fun find(x: T): T {
        if (!parent.containsKey(x)) {
            throw IllegalArgumentException("Element $x is not in the set")
        }
        if (parent[x] != x) {
            parent[x] = find(parent[x]!!)
        }
        return parent[x]!!
    }

    fun union(x: T, y: T) {
        val xRoot = find(x)
        val yRoot = find(y)

        if (rank[xRoot]!! < rank[yRoot]!!) {
            parent[xRoot] = yRoot
        } else if (rank[xRoot]!! > rank[yRoot]!!) {
            parent[yRoot] = xRoot
        } else {
            parent[yRoot] = xRoot
            rank[xRoot] = rank[xRoot]!! + 1
        }
    }
}