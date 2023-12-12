class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y

class Segment:
    def __init__(self, p1, p2):
        self.p1 = p1
        self.p2 = p2

import matplotlib.pyplot as plt

# Function to plot a point
def plot_point(ax, point, label):
    ax.plot(point.x, point.y, 'o', label=label)
    ax.text(point.x, point.y, f'  {label}', verticalalignment='bottom', horizontalalignment='right')

# Function to plot a segment
def plot_segment(ax, segment):
    ax.plot([segment.p1.x, segment.p2.x], [segment.p1.y, segment.p2.y], label="")

# Create a figure and axis
fig, ax = plt.subplots()

# Define points and segments based on your proof
a = Point(x=1, y=1)
b = Point(x=1, y=2)
c = Point(x=1, y=-4)
p1 = Point(x=0, y=0)
p2 = Point(x=2, y=0)

segment_p1a = Segment(p1, a)
segment_p1b = Segment(p1, b)
segment_p1c = Segment(p1, c)
segment_p2a = Segment(p2, a)
segment_p2b = Segment(p2, b)
segment_p2c = Segment(p2, c)
segment_cb = Segment(c, b)
segment_pp = Segment(p1, p2)

# Plot points and segments
plot_point(ax, a, 'A')
plot_point(ax, b, 'B')
plot_point(ax, c, 'C')
plot_point(ax, p1, 'P1')
plot_point(ax, p2, 'P2')

plot_segment(ax, segment_p1a)
plot_segment(ax, segment_p1b)
plot_segment(ax, segment_p1c)
plot_segment(ax, segment_p2a)
plot_segment(ax, segment_p2b)
plot_segment(ax, segment_p2c)
plot_segment(ax, segment_cb)
plot_segment(ax, segment_pp)

# Set axis limits
ax.set_xlim([-1, 3])
ax.set_ylim([-5, 3])

# Add labels and legend
ax.set_xlabel('X-axis')
ax.set_ylabel('Y-axis')
# ax.legend()

# Show the plot
plt.show()
