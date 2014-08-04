class Movie(object):
	@property	
 	def budget(self):
		print "RETURNING"
        	return self._budget
    
    	@budget.setter
    	def budget(self, value):
        	if value < 0:
			raise ValueError("Negative value not allowed: %s" % value)
		self._budget = value

m=Movie()
m.budget=12
print m.budget
try:
	m.budget=-1
except ValueError:
	print "WOOPS"
