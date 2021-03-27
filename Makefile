TARGET := out
CFLAGS := -Wall -g -O2
OBJS := bn.o main.o mlock_check.o

.PHONY: all clean

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CC) $(CFLAGS) $^ -o $@

clean:
	$(RM) $(TARGET) *.o 

%.o: %.c
	$(CC) $(CFLAGS) -c $^ -o $@

