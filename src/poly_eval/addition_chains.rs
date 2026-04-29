use std::collections::BTreeMap;

use feanor_math::integer::IntegerRingStore;

use crate::ZZi64;

pub fn addition_chain_lengths(k: usize, available: &[usize]) -> (Vec<usize>, Vec<usize>) {
    debug_assert!(available.is_sorted());
    let mut costs = vec![0, 0];
    let mut next = vec![0, 1];
    let mut available_i = 0;
    while available_i < available.len() && available[available_i] < 2 {
        available_i += 1;
    }
    for i in 2..=k {
        if available_i < available.len() && i == available[available_i] {
            costs.push(0);
            next.push(i);
            available_i += 1;
        } else {
            let next_power_two = 1 << ZZi64.abs_log2_ceil(&(i as i64)).unwrap();
            let potential_steps = (i - next_power_two / 2)..=(next_power_two / 2);
            let j = potential_steps.min_by_key(|j| costs[*j] + costs[i - j] + 1).unwrap();
            costs.push(costs[j] + costs[i - j] + 1);
            next.push(j);
        }
    }
    return (costs, next);
}

pub fn addition_chain_for(target: usize, shortest_addition_chain_list: &[usize]) -> Vec<(usize, (usize, usize))> {
    let mut open = vec![target];
    let mut closed = BTreeMap::new();
    while let Some(value) = open.pop() {
        if shortest_addition_chain_list[value] == value {
            continue;
        } else {
            let left = shortest_addition_chain_list[value];
            let right = value - left;
            closed.insert(value, (left, right));
            if !closed.contains_key(&left) {
                open.push(left);
            }
            if !closed.contains_key(&right) {
                open.push(right)
            }
        }
    }
    return closed.into_iter().collect();
}
