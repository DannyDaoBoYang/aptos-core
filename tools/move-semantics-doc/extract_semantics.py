import re

def extract_bytecode_semantics(file_path):
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Find the Bytecode enum
    enum_match = re.search(r'pub enum Bytecode \{(.+?)\n\}', content, re.DOTALL)
    if not enum_match:
        print("Could not find Bytecode enum")
        return []
    
    enum_content = enum_match.group(1)
    lines = enum_content.split('\n')
    
    bytecodes = []
    current_bc = None
    i = 0
    
    while i < len(lines):
        line = lines[i]
        
        # Check if this is a group attribute (start of new bytecode)
        if line.strip().startswith('#[group'):
            if current_bc and current_bc['name']:
                bytecodes.append(current_bc)
            
            current_bc = {
                'name': '',
                'group': '',
                'description': '',
                'semantics': '',
                'static_operands': '',
                'runtime_check_prologue': '',
                'runtime_check_epilogue': '',
            }
            
            # Extract group
            group_match = re.search(r'#\[group = "([^"]+)"\]', line)
            if group_match:
                current_bc['group'] = group_match.group(1)
        
        elif current_bc is not None:
            # Extract description (multi-line)
            if '#[description = r#"' in line:
                desc_lines = []
                i += 1
                while i < len(lines) and '"#]' not in lines[i]:
                    desc_lines.append(lines[i])
                    i += 1
                current_bc['description'] = '\n'.join(desc_lines).strip()
            
            elif '#[description = "' in line:
                match = re.search(r'#\[description = "([^"]*)"\]', line)
                if match:
                    current_bc['description'] = match.group(1)
            
            # Extract semantics (multi-line)
            elif '#[semantics = r#"' in line:
                sem_lines = []
                i += 1
                while i < len(lines) and '"#]' not in lines[i]:
                    sem_lines.append(lines[i])
                    i += 1
                current_bc['semantics'] = '\n'.join(sem_lines).strip()
            
            elif '#[semantics = "' in line:
                match = re.search(r'#\[semantics = "([^"]*)"\]', line)
                if match:
                    current_bc['semantics'] = match.group(1)
            
            # Extract static_operands
            elif '#[static_operands = "' in line:
                match = re.search(r'#\[static_operands = "([^"]*)"\]', line)
                if match:
                    current_bc['static_operands'] = match.group(1)
            
            # Extract runtime_check_prologue (multi-line)
            elif '#[runtime_check_prologue = r#"' in line:
                check_lines = []
                i += 1
                while i < len(lines) and '"#]' not in lines[i]:
                    check_lines.append(lines[i])
                    i += 1
                current_bc['runtime_check_prologue'] = '\n'.join(check_lines).strip()
            
            elif '#[runtime_check_prologue = "' in line:
                match = re.search(r'#\[runtime_check_prologue = "([^"]*)"\]', line)
                if match:
                    current_bc['runtime_check_prologue'] = match.group(1)
            
            # Extract runtime_check_epilogue (multi-line)
            elif '#[runtime_check_epilogue = r#"' in line:
                check_lines = []
                i += 1
                while i < len(lines) and '"#]' not in lines[i]:
                    check_lines.append(lines[i])
                    i += 1
                current_bc['runtime_check_epilogue'] = '\n'.join(check_lines).strip()
            
            elif '#[runtime_check_epilogue = "' in line:
                match = re.search(r'#\[runtime_check_epilogue = "([^"]*)"\]', line)
                if match:
                    current_bc['runtime_check_epilogue'] = match.group(1)
            
            # Check if this is the variant name
            elif re.match(r'^\s+[A-Z][a-zA-Z0-9]*', line):
                # Extract the variant name (without parameters)
                variant_match = re.match(r'^\s+([A-Z][a-zA-Z0-9]*)', line)
                if variant_match:
                    current_bc['name'] = variant_match.group(1)
        
        i += 1
    
    # Don't forget the last one
    if current_bc and current_bc['name']:
        bytecodes.append(current_bc)
    
    return bytecodes

def generate_markdown(bytecodes):
    print("# Move Bytecode Semantics")
    print()
    print("This document describes the semantics of Move bytecode instructions based on the interpreter implementation.")
    print()
    print("---")
    print()
    
    # Group by group
    groups = {}
    for bc in bytecodes:
        group = bc['group'] or 'ungrouped'
        if group not in groups:
            groups[group] = []
        groups[group].append(bc)
    
    # Sort groups
    group_order = [
        'control_flow',
        'stack_and_local',
        'reference',
        'arithmetic',
        'casting',
        'bitwise',
        'comparison',
        'boolean',
        'struct',
        'variant',
        'global',
        'vector',
    ]
    
    for group_name in group_order:
        if group_name not in groups:
            continue
            
        print(f"## {group_name.replace('_', ' ').title()}")
        print()
        
        for bc in groups[group_name]:
            print(f"### `{bc['name']}`")
            print()
            
            if bc['description']:
                print(bc['description'])
                print()
            
            if bc['static_operands']:
                print(f"**Static Operands:** `{bc['static_operands']}`")
                print()
            
            if bc['semantics']:
                print("**Semantics:**")
                print()
                print("```")
                print(bc['semantics'])
                print("```")
                print()
            
            if bc['runtime_check_prologue']:
                print("**Runtime Check (Prologue):**")
                print()
                print("```")
                print(bc['runtime_check_prologue'])
                print("```")
                print()
            
            if bc['runtime_check_epilogue']:
                print("**Runtime Check (Epilogue):**")
                print()
                print("```")
                print(bc['runtime_check_epilogue'])
                print("```")
                print()
            
            print("---")
            print()

if __name__ == '__main__':
    import sys
    file_path = sys.argv[1] if len(sys.argv) > 1 else 'third_party/move/move-binary-format/src/file_format.rs'
    bytecodes = extract_bytecode_semantics(file_path)
    generate_markdown(bytecodes)

