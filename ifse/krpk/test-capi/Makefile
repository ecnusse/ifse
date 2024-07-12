OUTPUT_DIR=$(TEST_WORKING_DIR)

OBJECTS = $(SRC_FILES:%.cpp=$(OUTPUT_DIR)/%.o)

all: $(OBJECTS)
	$(CXX) $(LDFLAGS) $(OBJECTS) -o $(OUTPUT_DIR)/test

$(OBJECTS): $(OUTPUT_DIR)/%.o : $(SRC_DIR)/%.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@
