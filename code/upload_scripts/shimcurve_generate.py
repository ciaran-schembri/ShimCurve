from lmfdb import db

def create_label(entry, tiebreak):
    return '.'.join([str(entry[fld]) for fld in ['discB', 'discO', 'nrdmu', 'level']] + [str(tiebreak)])

def create_entry(line, base_entry):
    values = line.split('?')
    entry = {}
    entry.update(base_entry)
    entry['genus'] = int(values[0])
    entry['index'] = int(values[1])
    entry['cardH'] = int(values[2])
    entry['torsion'] = eval(values[3])
    entry['galEnd'] = db.gps_groups.lucky({'name' : values[4].split()[0]},
                                          'label')
    entry['autmuO_norms'] = [x for x in eval(values[5])]
    entry['is_split'] = eval(values[6])
    entry['generators'] = eval(magma.eval(O_str + 'gens := ' + values[7] + '; [Eltseq(B!g[1]) cat g[2] : g in gens];'))
    # !!!! TODO !!!! needs a way to tell if -1 is in the group (coarse/fine moduli)
    tt = values[8].split('|')
    entry['ram_data_n'] = eval(tt[0].split()[1].split('(')[1].split(')')[0])
    # !!!! TODO !!!! add handling of ram_data_elts
    return entry

def create_base_entry(table_lines):
    base_entry = {}
    ij = table_lines[0].split('|')[1].split('>')[0].split(',')
    base_entry['i_square'] = int(ij[0])
    base_entry['j_square'] = int(ij[1])
    B.<i,j,k> = QuaternionAlgebra(base_entry['i_square'],
                                  base_entry['j_square'])
    # magma.eval('B<i,j,k> := ' + table_lines[0] + 'Discriminant(B);')
    base_entry['discB'] = B.discriminant()
    O_str = 'B<i,j,k> := ' + table_lines[0] + 'O_basis := ' + table_lines[1] + 'O := QuaternionOrder(O_basis); '
    base_entry['discO'] = int(magma.eval(O_str + 'Discriminant(O);'))
    denoms_str = 'B<i,j,k> := ' + table_lines[0] + 'O_basis := ' + table_lines[1] + 'denoms := [Denominator(x) : x in O_basis];'
    base_entry['gensOdenominators'] = eval(magma.eval(denoms_str + 'denoms;'))
    nums_str = denoms_str + 'nums := [[denoms[i] * x : x in Eltseq(y)] : i->y in O_basis];'
    base_entry['gensOnumerators'] = eval(magma.eval(nums_str + 'nums;'))
    base_entry['level'] = int(table_lines[2][:-1])
    base_entry['mu'] = eval(table_lines[3][:-1])
    base_entry['nrdmu'] = int(magma.eval(O_str + 'mu := O!' + table_lines[3] + 'Norm(mu);' ))
    return base_entry

def create_entries(fname):
    table_file = open(fname)
    table_data = table_file.read()
    table_file.close()
    table_lines = table_data.split('\n')
    base_entry = create_base_entry(table_lines)
    entries = []
    tiebreak = 0
    for tiebreak, line in enumerate(table_lines[6:]):
        tiebreak += 1
        if line[:17] == 'QuaternionAlgebra':
            break
        entry = create_entry(line, base_entry)
        entry['label'] = create_label(entry, tiebreak)
        entry['coarse_label'] = entry['label']
        entry['q_gonality_bounds'] = [1, 2*entry['genus']-2]
        entry['qbar_gonality_bounds'] = [1, 2*entry['genus']-2]
        entries.append(entry)
    return entries
