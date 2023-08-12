#lang dssl2

# Final project: Trip Planner

# Koby Renfert

let eight_principles = ["Know your rights.",
     "Acknowledge your sources.",
     "Protect your work.",
     "Avoid suspicion.",
     "Do your own work.",
     "Never falsify a record or permit another person to do so.",
     "Never fabricate data, citations, or experimental results.",
     "Always tell the truth when discussing your work with your instructor."]

import cons
import 'project-lib/dictionaries.rkt'
import 'project-lib/graph.rkt'
import 'project-lib/binheap.rkt'
import sbox_hash

### Basic Types ###

#  - Latitudes and longitudes are numbers:
let Lat?  = num?
let Lon?  = num?

#  - Point-of-interest categories and names are strings:
let Cat?  = str?
let Name? = str?

### Raw Item Types ###

#  - Raw positions are 2-element vectors with a latitude and a longitude
let RawPos? = TupC[Lat?, Lon?]

#  - Raw road segments are 4-element vectors with the latitude and
#    longitude of their first endpoint, then the latitude and longitude
#    of their second endpoint
let RawSeg? = TupC[Lat?, Lon?, Lat?, Lon?]

#  - Raw points-of-interest are 4-element vectors with a latitude, a
#    longitude, a point-of-interest category, and a name
let RawPOI? = TupC[Lat?, Lon?, Cat?, Name?]

### Contract Helpers ###

# ListC[T] is a list of `T`s (linear time):
let ListC = Cons.ListC
# List of unspecified element type (constant time):
let List? = Cons.list?



interface TRIP_PLANNER:

    # Returns the positions of all the points-of-interest that belong to
    # the given category.
    def locate_all(
            self,
            dst_cat:  Cat?           # point-of-interest category
        )   ->        ListC[RawPos?] # positions of the POIs

    # Returns the shortest route, if any, from the given source position
    # to the point-of-interest with the given name.
    def plan_route(
            self,
            src_lat:  Lat?,          # starting latitude
            src_lon:  Lon?,          # starting longitude
            dst_name: Name?          # name of goal
        )   ->        ListC[RawPos?] # path to goal

    # Finds no more than `n` points-of-interest of the given category
    # nearest to the source position.
    def find_nearby(
            self,
            src_lat:  Lat?,          # starting latitude
            src_lon:  Lon?,          # starting longitude
            dst_cat:  Cat?,          # point-of-interest category
            n:        nat?           # maximum number of results
        )   ->        ListC[RawPOI?] # list of nearby POIs


class TripPlanner (TRIP_PLANNER):
    let node_to_id #convert each endpoint to an id number for the graph
    let id_to_node #bidirectionality to allow for node lookup based on graph vertex number
    let name_to_node #allow for searching by POI name to node 
    let cat_to_poi #lookup points of interest associated with a given category *** MULTIMAP DS
    let connections #graph of connections, depicting roads
    let numPoi
    let numRoads
    
    
    
    def djikstras(self, graph, start): #return array of predecessors to each node
        struct vertex:
            let vnum
            let weight
        let pred = [None; graph.len()]
        let dists = [inf; graph.len()]
        let pq = BinHeap(graph.len(), λ x, y: x.weight < y.weight)
        let visited = [False; graph.len()]
      
        def helper(beg, graph):
            if ((pq.len() == 0) and (visited[beg])): # base case _ stop running when the queue is empty
                return [pred, dists]
            if (visited[beg]): # now check if we've already visited the item next up
                let next = pq.find_min().vnum
                pq.remove_min()
                helper(next, graph)
            let pointer = graph.get_adjacent(beg)
            while (pointer != None):
                if (not visited[pointer.data]): # only compare distances if we have not 'visited' this yet
                    let edgeWeight = self.connections.get_edge(beg, pointer.data)
                    if ((dists[beg] + edgeWeight) < dists[pointer.data]): # check if current path is shorter
                        pred[pointer.data] = beg
                        
                        dists[pointer.data] = dists[beg] + edgeWeight
                        pq.insert(vertex(pointer.data, dists[pointer.data])) # add struct to priority queue
                        
                pointer = pointer.next
            visited[beg] = True
            if (pq.len() == 0):
                return [pred, dists]
            let next = pq.find_min().vnum
            pq.remove_min()
            helper(next, self.connections)
        let beg = self.node_to_id.get(start)
        dists[beg] = 0
        pq.insert(vertex(beg, 0))
        helper(beg, graph)
    
    
    def __init__(self, roadList, poiList):
        self.numRoads = len(roadList)
        self.numPoi = len(poiList)
        self.node_to_id = HashTable(((self.numRoads) * 2), make_sbox_hash())
        self.id_to_node = HashTable(((self.numRoads) * 2), make_sbox_hash())
        self.cat_to_poi = HashTable(self.numPoi, make_sbox_hash()) # *** THIS WILL BE A MULTIMAP DS
        self.name_to_node = HashTable(self.numPoi, make_sbox_hash())
        self.connections = WuGraph(self.numRoads * 2)
        
       
        
        let counter = 0 # Iterate thru each road - define start and endpoints
        for road in roadList: #if they don't exist yet in hash table, enter them - bidirectional
            let start = [road[0], road[1]]
            let end = [road[2], road[3]]
            if not (self.node_to_id.mem?(start)):
                self.node_to_id.put(start, counter) 
                self.id_to_node.put(counter, start)
                counter = counter + 1 #Iterate counter each time a new point is encountered
                
            if not (self.node_to_id.mem?(end)):
                self.node_to_id.put(end, counter)
                self.id_to_node.put(counter, end)
                counter = counter + 1
                
            let num1 = self.node_to_id.get(start) #get vertex numbers for start and end, then set edges
            let num2 = self.node_to_id.get(end)
            let weight = (((end[0] - start[0]) ** 2) + (((end[1] - start[1])) ** 2)).sqrt() #euclidian dist fxn
            self.connections.set_edge(num1, num2, weight) 
        
        for poi in poiList: #defining multi-map data structures where each value is a linked list of values
            let node = [poi[0], poi[1]]
            self.name_to_node.put(poi[3], node)
            if (not self.cat_to_poi.mem?(poi[2])):
                self.cat_to_poi.put(poi[2], cons(poi, None))
            else:
                self.cat_to_poi.put(poi[2], cons(poi, self.cat_to_poi.get(poi[2])))

            
            
    def locate_all(self, cat): #iterate through the linked list of poi values for the given cat (key)
        
        if (not self.cat_to_poi.mem?(cat)):
            return None
        let ptr = self.cat_to_poi.get(cat)
        let ret = None
        #let checker = AssociationList() #check for dupes in output
        let checker = [False; self.numRoads * 2] #array of nodes that have been added - direct addressing O(1) lookup
        while (ptr != None):
            let tup = [ptr.data[0], ptr.data[1]]
            if (not checker[self.node_to_id.get(tup)]): #if it's false, we haven't added it yet
                checker[self.node_to_id.get(tup)] = True #set it to true and add it to the list
                ret = cons(tup, ret) 
            ptr = ptr.next
        return ret
        
    def plan_route(self, src_lat, src_lon, dst_name):
        if (not self.name_to_node.mem?(dst_name)): #if the destination does not exist
            return None #checking first will prevent errors for dict.get
        let start = [src_lat, src_lon]
        let dest = self.name_to_node.get(dst_name) #a node 
        let pred = self.djikstras(self.connections, start)[0]
        let ret = None
        let dst_node = self.name_to_node.get(dst_name)
        let dst_id = self.node_to_id.get(dst_node)
        if ((dst_node[0] == src_lat) and (dst_node[1] == src_lon)): #case where the start is the destination, therefore pred is None
                return cons(dst_node, None)
        if (pred[dst_id] != None): #make sure it's reachable before this step
            ret = cons(self.id_to_node.get(dst_id), None) #add the destination node, then start adding predecessors
        let ptr = pred.get(dst_id)
        while (ptr != None):
            let target = self.id_to_node.get(ptr)
            ret = cons(target, ret)
            ptr = pred[ptr]
        return ret
        
        
        
    def find_nearby(self, src_lat, src_lon, dst_cat, n):
        if (not self.cat_to_poi.mem?(dst_cat)): #check if the category even exists
            return None #if not, return none and save time
        let pq = BinHeap(self.numPoi, λ x, y: x.weight < y.weight)
        struct poiWeight:
            let poi
            let weight
        let djikstra = self.djikstras(self.connections, [src_lat, src_lon]) # [pred, dists]
        let pred = djikstra[0]
        let dists = djikstra[1]
        let ptr = self.cat_to_poi.get(dst_cat) #point to linked list of poi objects
        while (ptr != None): 
            if ((ptr.data[0] == src_lat) and (ptr.data[1] == src_lon)): #case where it's the start point, and there is None as pred
                pq.insert(poiWeight(ptr.data, 0))
            if (pred[self.node_to_id.get([ptr.data[0], ptr.data[1]])] != None): #if not none, then it's reachable
                let weight = dists[self.node_to_id.get([ptr.data[0], ptr.data[1]])]
                pq.insert(poiWeight(ptr.data, weight))
            ptr = ptr.next
        let ret = None
        for i in range(n):
            if pq.len() == 0: #base case 
                break
            ret = cons(pq.find_min().poi, ret) 
            pq.remove_min()
        return ret
        
    
       
        


def my_first_example():
    return TripPlanner([[0,0, 0,1], [0,0, 1,0]],
                       [[0,0, "bar", "The Empty Bottle"],
                        [0,1, "food", "Pierogi"]])

test 'My first locate_all test':
    assert my_first_example().locate_all("food") == \
        cons([0,1], None)

test 'My first plan_route test':
   assert my_first_example().plan_route(0, 0, "Pierogi") == \
       cons([0,0], cons([0,1], None))

test 'My first find_nearby test':
    assert my_first_example().find_nearby(0, 0, "food", 1) == \
        cons([0,1, "food", "Pierogi"], None)

def comp():
    return TripPlanner([[0,0, 2,0], [0,0, 2,3], [0,0, 0,4], [2,0, 2,3], [0,4, 2,4], [2,4, 4,3], [3,0, 7,0]],
                       [[0,0, "food", "Starbucks"],
                        [0,4, "food", "Deli"],
                        [4,3, "food", "Mod"], 
                        [2,3, "food", "Lisas"], 
                        [3,0, "clothes", "Gear"],
                        [7,0, "food", "Frans"], 
                        [4,3, "food", "Portillos"]]) #use to check for dupes
                        
test 'comprehensive':
    assert comp().find_nearby(0, 0, "food", 1) == \
        cons([0,0, "food", "Starbucks"], None)
        
    assert comp().find_nearby(0, 0, "food", 3) == \
        cons([0,4, "food", "Deli"], cons([2,3, "food", "Lisas"], cons([0,0, "food", "Starbucks"], None)))
        
    assert comp().find_nearby(0, 0, "food", 2) == \
        cons([2,03, "food", "Lisas"], cons([0,0, "food", "Starbucks"], None))
        
    assert comp().plan_route(0, 0, "Lisas") == \
       cons([0,0], cons([2,3], None))
       
    assert comp().plan_route(0, 0, "Frans") == None
    
    assert comp().plan_route(3,0, "Frans") == \
        cons([3,0], cons([7,0], None))
        
    assert comp().find_nearby(3, 0, "food", 1) == \
        cons([7,0, "food", "Frans"], None)
        
    assert comp().locate_all("food") == \
        cons([0, 0], cons([0, 4], cons([2, 3], cons([7, 0], cons([4, 3], None)))))
      
    assert comp().find_nearby(0, 0, "clothes", 2) == \
        None
        
    assert comp().locate_all("clothes") == \
        cons([3, 0], None)
        
    assert comp().plan_route(0, 0, "Starbucks") == \
       cons([0,0], None)
        
test 'resub plan':
    let tp = TripPlanner(
      [[0, 0, 1, 0]],
      [[0, 0, 'bank', 'Union']])
    let result = tp.plan_route(0, 0, 'Union')
    assert Cons.to_vec(result) \
      == [[0, 0]]
      
      
    let tp1 = TripPlanner(
      [[0, 0, 1.5, 0],
       [1.5, 0, 2.5, 0],
       [2.5, 0, 3, 0]],
      [[1.5, 0, 'bank', 'Union'],
       [3, 0, 'barber', 'Tony']])
    let result1 = tp1.plan_route(0, 0, 'Judy')
    assert Cons.to_vec(result1) \
      == []
      
test 'resub nearby':
    let tp = TripPlanner(
      [[0, 0, 1.5, 0],
       [1.5, 0, 2.5, 0],
       [2.5, 0, 3, 0],
       [4, 0, 5, 0]],
      [[1.5, 0, 'bank', 'Union'],
       [3, 0, 'barber', 'Tony'],
       [5, 0, 'barber', 'Judy']])
    let result = tp.find_nearby(0, 0, 'food', 1)
    assert (Cons.to_vec(result)) \
      == []
      
    let tp1 = TripPlanner(
      [[-1.1, -1.1, 0, 0],
       [0, 0, 3, 0],
       [3, 0, 3, 3],
       [3, 3, 3, 4],
       [0, 0, 3, 4]],
      [[0, 0, 'food', 'Sandwiches'],
       [3, 0, 'bank', 'Union'],
       [3, 3, 'barber', 'Judy'],
       [3, 4, 'barber', 'Tony']])
    let result1 = tp1.find_nearby(-1.1, -1.1, 'barber', 1)
    assert (Cons.to_vec(result1)) \
      == [[3, 4, 'barber', 'Tony']]
        
        
