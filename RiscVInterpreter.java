import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;

import org.apache.tools.ant.util.StringUtils;

public class RiscVInterpreter {

    Boolean worked = false;
    String printResult = "";
    HashMap<Integer,Integer> memory;
    HashMap<String, Integer> regs;
    HashMap<String, String> equivs;
    ArrayList<String> lines;
    HashMap<String, Integer> labels;
    ArrayList<String> instructions;
    Integer address;
    StringBuilder printer;
    Boolean active;
    Boolean badbadbad = false;
    Boolean debug = false;

    // Instruction level parameters
    String regTo;
    String reg1;
    String reg2;
    Integer imm;
    String label;


    /* Constructor */
    public RiscVInterpreter(String program) {

        // We can't precompute a program that requires input
        if (program.contains("jal $input")) {
            return;
        }

        if (debug) {
            print(program);
        }

        // Initialize internals
        memory = new HashMap<Integer, Integer>();
        regs = new HashMap<String, Integer>();
        equivs = new HashMap<String, String>();
        labels = new HashMap<String, Integer>();
        instructions = new ArrayList<String>();
        printer = new StringBuilder();
        active = true;
        initRegs();

        // Process program instructions
        String[] strLines = program.split("\n");
        for (int i = 0; i < strLines.length; i++) {
            strLines[i] = strLines[i].trim();
        }
        lines = new ArrayList<String>(Arrays.asList(strLines));

        // Clean program instructions
        removeComments();
        makeEquivs();
        makeData();
        makeInstructionList();

        // Execute
        runProgram();

        if (!badbadbad) {
            worked = true;
        }
    }

    /* Initialize program registers */
    private void initRegs() {
        for (int i = 0; i <= 7; i++) {
            regs.put("a" + Integer.toString(i), 0);
        }
        for (int i = 0; i <= 6; i++) {
            regs.put("t" + Integer.toString(i), 0);
        }
        for (int i = 1; i <= 11; i++) {
            regs.put("s" + Integer.toString(i), 0);
        }
        regs.put("fp", 0);
        regs.put("sp", 0x7ffffff0);
        regs.put("gp", 0x10000000);
        regs.put("ra", 0);
        regs.put("zero", 0);
        regs.put("x0", 0);
    }

    /* Scrape and replace .equiv directives */
    private void makeEquivs() {
        ArrayList<Integer> indices = new ArrayList<Integer>();

        // Create dictionary of .equiv equivalencies
        for (int i = 0; i < lines.size(); ++i) {
            String line = lines.get(i);
            if (line.startsWith(".equiv")) {
                String[] fields = line.split(" ");
                fields[1] = fields[1].substring(0, fields[1].length() - 1);
                equivs.put(fields[1], fields[2]);
                indices.add(i);
            }
        }
        Collections.reverse(indices);
        for (Integer ind : indices) {
            lines.remove((int) ind); // remove in backwards order 
        }

        // replace equivalent string values + remove comments
        for (int i = 0; i < lines.size(); ++i) {
            String line = lines.get(i);
            if (line.startsWith(".string")) {
                continue;
            }
            for (String key : equivs.keySet()) {
                line = StringUtils.replace(line, key, equivs.get(key));
            }
            lines.set(i, line);
        }
    }

    /* Print memory hashmap in sequential order */
    private void printMemory() {
        ArrayList<Integer> hi = new ArrayList<Integer>(memory.keySet());
        Collections.sort(hi);
        for (Integer key : hi) {
            System.out.print(Integer.toHexString(key) + " ");
            System.out.println(Integer.toHexString(memory.get(key)));
        }
    }

    /* Initialize data portion of memory under .data directives */ 
    private void data(Integer i) {
        String line = lines.get(i);
        // Record labels
        if (line.contains(":")) {
            Integer ind = line.indexOf(":");
            String label = line.substring(0, ind);
            labels.put(label, address);
        } 

        // Place .word directives into memory
        else if (line.contains(".word")) {
            String[] word = line.split(" ");
            if (word[1].matches("-?(0|[1-9]\\d*)")) {
                Integer val = Integer.parseInt(word[1]);
                memory.put(address, val);
            } else if (labels.containsKey(word[1])) {
                Integer val = labels.get(word[1]);
                memory.put(address, val);
            }
            address += 4;
        }

        // Place .string directives into memory
        else if (line.contains(".string")) {
            Integer startInd = line.indexOf("\"");
            Integer endInd = line.lastIndexOf("\"");
            String literal = line.substring(startInd + 1, endInd);
            byte[] bytes = literal.getBytes(StandardCharsets.US_ASCII);
            byte[] padBytes = new byte[4 - (bytes.length % 4)];

            byte[] total = new byte[bytes.length + padBytes.length];
            System.arraycopy(bytes, 0, total, 0, bytes.length);
            System.arraycopy(padBytes, 0, total, bytes.length, padBytes.length);
            
            ByteBuffer inter = ByteBuffer.wrap(total).order(ByteOrder.LITTLE_ENDIAN);
            int lengthLeft = total.length;
            while (lengthLeft > 0) {
                memory.put(address, inter.getInt());
                lengthLeft -= 4;
                address += 4;
            } 
        }
    }

    /* Find and record labels within instruction space */
    private void setMainGlobals() {
        address = 0x0;
        Integer startInd = lines.indexOf(".globl main");
        Integer endInd = lines.lastIndexOf(".data");
        for (int i = startInd; i < endInd; i++) {
            String line = lines.get(i);
            if (line.contains(":")){
                String label = line.substring(0, line.indexOf(":"));
                labels.put(label, address);
            } else if(line.startsWith(".") || line.startsWith("#") || line.length() < 4) {
                // do nothing
            } else {
                address += 4;
            }
        }
    }

    /* Populate labels properly */
    private void makeData() {
        Integer startInd = lines.indexOf(".data");
        Integer endInd = lines.indexOf(".text");        
        address = 0x10000000;
        for (int i = startInd; i < endInd; i++) {
            data(i);
        }

        Integer startLast = lines.lastIndexOf(".data");
        for (int i = startLast; i < lines.size(); i++) {
            data(i);
        }
        setMainGlobals();

        address = 0x10000000;

        // Run two passes to catch forward references
        for (int i = startInd; i < endInd; i++) {
            data(i);
        }
        for (int i = startLast; i < lines.size(); i++) {
            data(i);
        }
    }

    /* Strip comments on surrounding code */
    private void removeComments() {
        ArrayList<Integer> removes = new ArrayList<Integer>();
        for (int i = 0; i < lines.size(); i++) {
            String line = lines.get(i);
            Integer commentInd = line.indexOf('#');
            if (commentInd >= 0) {
                line = line.substring(0, commentInd).trim();
            }
            if (line.length() == 0) {
                removes.add(i);
            }
            lines.set(i, line);
        }
        Collections.reverse(removes);
        for (Integer rem : removes) {
            lines.remove((int) rem);
        }
    }

    /* Make list of instructions */
    private void makeInstructionList() {
        Integer startInd = lines.indexOf(".globl main");
        Integer endInd = lines.lastIndexOf(".data");

        for(String line : lines.subList(startInd, endInd)) {
            if (line.startsWith(".")) {
                continue;
            } else if (line.contains(":")) {
                continue;
            } else {
                instructions.add(line);
            }
        }
    }

    /* Convert signed to unsigned integer (JAVA) */
    public long getUnsignedInt(int x) {
        return x & 0x00000000ffffffffL;
    }

    /* Perform system call */
    public void ecall() {
        switch(regs.get("a0")) {
            case 1: // int 
                printer.append(regs.get("a1"));
                break;
            case 11: // char 
                printer.append("\n");
                break;
            case 4: // str
                // a0 has address of null terminated string
                Integer value = memory.get(regs.get("a1"));
                Integer counter = 0;
                while (value != 0) {
                    counter++;
                    if ((value & 0xff) == 0) {
                        break;
                    }
                    char character = (char) (value & 0xff);
                    printer.append(character);
                    if (counter % 4 == 0) {
                        value = memory.get(regs.get("a1") + counter);
                    } else {
                        value = value >> 8;
                    }
                }
                break;
            case 9:
                regs.put("a0", 0x10008000);
                break;
            case 10: // exit goodly
                active = false;
                break;
            case 17: // exit BADLY
                active = false;
                String errorCode = regs.get("a1").toString();
                printer.append("Exited with error code " + errorCode + "\n");
                break;
            default:
                break;
        }
        return;
    }
    
    /* Run program */
    private void runProgram() {
        Integer pc = 0; // program counter
        Integer cycles = 0;

        // If program doesn't halt, then force terminate
        while (active && cycles < 300000) {
            String instruction = processInstruction(instructions.get(pc / 4));
            if (debug) {
                print(instructions.get(pc / 4));
            }
            switch(instruction) {
                case "lui":
                    regs.put(regTo, imm << 12);
                    break;
                case "add":
                    regs.put(regTo, regs.get(reg1) + regs.get(reg2));
                    break;
                case "jal": // check if works
                    regs.put("ra", pc + 4); // save next instruction
                    pc = labels.get(label) - 4; // cuz we advance later anyway
                    break;
                case "mv":
                    regs.put(regTo, regs.get(reg1));
                    break;
                case "addi":
                    regs.put(regTo, regs.get(reg1) + imm);
                    break;
                case "sw":
                    String[] splitInstr = instructions.get(pc / 4).split(" ");
                    if (splitInstr[2].contains("(")) {
                        memory.put(regs.get(reg1) + imm, regs.get(regTo));
                    } else {
                        memory.put(labels.get(label), regs.get(regTo));
                    }
                    break;
                case "li":
                    regs.put(regTo, imm);
                    break;
                case "lw":
                    splitInstr = instructions.get(pc / 4).split(" ");
                    if (splitInstr[2].contains("(")) {
                        regs.put(regTo, memory.get(regs.get(reg1) + imm));
                    } else {
                        regs.put(regTo, memory.get(labels.get(label)));
                    }
                    break;
                case "ecall":
                    ecall();
                    break;
                case "beq":
                    if (regs.get(regTo).equals(regs.get(reg1))) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bne":
                    if (!regs.get(regTo).equals(regs.get(reg1))) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "blt":
                    if (regs.get(regTo) < regs.get(reg1)) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bge":
                    if (regs.get(regTo) >= regs.get(reg1)) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bltu":
                    if (getUnsignedInt(regs.get(regTo)) < getUnsignedInt(regs.get(reg1))) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bgeu":
                    if (getUnsignedInt(regs.get(regTo)) >= getUnsignedInt(regs.get(reg1))) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "beqz":
                    if (regs.get(regTo).equals(0)) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bnez":
                    if (!regs.get(regTo).equals(0)) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bgtz":
                    if (regs.get(regTo) > 0) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bgez":
                    if (regs.get(regTo) >= 0) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "blez":
                    if (regs.get(regTo) <= 0) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "bltz":
                    if (regs.get(regTo) < 0) {
                        pc = labels.get(label) - 4;
                    }
                    break;
                case "jr":
                    pc = regs.get(regTo) - 4;
                    break;
                case "la":
                    regs.put(regTo, labels.get(label));
                    break;
                case "j":
                    pc = labels.get(label) - 4;
                    break;
                case "xor":
                    regs.put(regTo, regs.get(reg1) ^ regs.get(reg2));
                    break;
                case "div":
                    regs.put(regTo, regs.get(reg1) / regs.get(reg2));
                    break;
                case "slli":
                    regs.put(regTo, regs.get(reg1) << imm);
                    break;
                case "srli":
                    regs.put(regTo, regs.get(reg1) >> imm);
                    break;
                case "jalr":
                    regs.put("ra", pc + 4);
                    pc = regs.get(regTo) - 4;
                    break;
                case "mul":
                    regs.put(regTo, regs.get(reg1) * regs.get(reg2));
                    break;
                case "or":
                    regs.put(regTo, regs.get(reg1) | regs.get(reg2));
                    break;
                case "and":
                    regs.put(regTo, regs.get(reg1) & regs.get(reg2));
                    break;
                case "sub":
                    regs.put(regTo, regs.get(reg1) - regs.get(reg2));
                    break;
                case "lb":// CHECK
                    // add immediate, then clear last two bits
                    Integer actualMemoryAddress = regs.get(reg1) + imm;
                    Integer memoryAddress = (actualMemoryAddress >> 2) << 2;
                    Integer locatedWord = memory.get(memoryAddress);
                    byte[] bytes = ByteBuffer.allocate(4)
                                             .order(ByteOrder.LITTLE_ENDIAN)
                                             .putInt(locatedWord)
                                             .array();
                    Integer value = (int) bytes[actualMemoryAddress & 0x3];
                    regs.put(regTo, value);
                    break;
                case "sb":
                    byte store = (byte) ((int) regs.get(regTo));
                    actualMemoryAddress = regs.get(reg1) + imm;
                    memoryAddress = (actualMemoryAddress >> 2) << 2;
                    if (memory.containsKey(memoryAddress)) {
                        locatedWord =  memory.get(memoryAddress);
                    } else {
                        locatedWord = 0;
                    }
                    bytes = ByteBuffer.allocate(4)
                                      .order(ByteOrder.LITTLE_ENDIAN)
                                      .putInt(locatedWord)
                                      .array();
                    bytes[actualMemoryAddress & 0x3] = store;
                    value = ByteBuffer.wrap(bytes)
                                      .order(ByteOrder.LITTLE_ENDIAN)
                                      .getInt();
                    memory.put(memoryAddress, value);
                    break;
                case "rem":
                    Integer r1 = regs.get(reg1);
                    Integer r2 = regs.get(reg2);
                    Integer val = 0;
                    if (r2.equals(0)) {
                        val = 0;
                    } else if (r1.equals(Integer.MIN_VALUE) && r2.equals(-1)) {
                        val = 0;
                    } else {
                        val = r1 % r2;
                    }
                    regs.put(regTo, val);
                    break;
                default:
                    System.out.println("couldn't");   
                    System.out.println(instructions.get(pc / 4));
                    badbadbad = true;
                    active = false;
                    break;                 
            }
            if (debug) {
                print(regs);
            }
            pc += 4;
            cycles += 1;
        }

    }

    /* Print function */
    private void print(Object... stuff) {
        for (int i = 0; i < stuff.length - 1; i++) {
            System.out.print(stuff[i]);
            System.out.print(" ");
        } 
        System.out.println(stuff[stuff.length - 1]);
    }

    /* Grab registers and label from instruction */
    private String processInstruction(String instr) {
        String[] splitInstr = instr.split(" ");
        String instruction = splitInstr[0];
        if (instruction.equals("ecall")) {
            return instruction;
        }
        if (splitInstr[1].contains(",")) {
            splitInstr[1] = StringUtils.replace(splitInstr[1], ",", "");
        }
        if (splitInstr.length > 2) {
            if (splitInstr[2].contains(",")) {
                splitInstr[2] = StringUtils.replace(splitInstr[2], ",", "");
            }
            if (splitInstr[2].matches("-?(0|[1-9]\\d*)")) {
                imm = Integer.parseInt(splitInstr[2]);
            }    
            if (regs.containsKey(splitInstr[2])) {
                reg1 = splitInstr[2];
            } else {
                label = splitInstr[2];
            }
            if (splitInstr[2].contains("(")) {
                int firstParen = splitInstr[2].indexOf("(");
                int lastParen = splitInstr[2].indexOf(")");
                reg1 = splitInstr[2].substring(firstParen + 1, lastParen);
                String tempImm = splitInstr[2].substring(0, firstParen);
                if (tempImm.matches("-?(0|[1-9]\\d*)")) {
                    imm = Integer.parseInt(tempImm);
                } else {
                    Integer ind = Math.max(tempImm.indexOf("+"), tempImm.indexOf("-"));
                    Integer num1 = Integer.parseInt(tempImm.substring(0, ind));
                    Integer num2 = Integer.parseInt(tempImm.substring(ind + 1));
                    if (tempImm.contains("-")) {
                        imm = num1 - num2;
                    } else if (tempImm.contains("+")) {
                        imm = num1 + num2;
                    } else {
                        System.out.println("ERRORORORORR");
                    }
                }
            }
        }
        if (splitInstr.length > 3) {
            if (splitInstr[3].contains(",")) {
                splitInstr[3] = StringUtils.replace(splitInstr[3], ",", "");
            }
            if (splitInstr[3].matches("-?(0|[1-9]\\d*)")) {
                imm = Integer.parseInt(splitInstr[3]);
            }    
            if (regs.containsKey(splitInstr[3])) {
                reg2 = splitInstr[3];
            } else {
                label = splitInstr[3];
            }
        }
        if (instruction.equals("jal")) {
            if (regs.containsKey(splitInstr[1])) {
                label = splitInstr[2];
            } else {
                label = splitInstr[1];
            }
        }
        if (instruction.equals("j")) {
            label = splitInstr[1];
        }
        regTo = splitInstr[1];
        return instruction;
    }
}
