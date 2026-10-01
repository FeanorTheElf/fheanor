use std::ops::RangeInclusive;

pub fn minimum_somewhat_continuous_function<F>(range: RangeInclusive<usize>, mut f: F, steps: usize) -> usize
where
    F: FnMut(usize) -> i64,
{
    assert!(steps >= 1);
    let len = (range.end() - range.start() + 1) as usize;
    assert!(len > 0);
    if len == 1 {
        return *range.start();
    }
    let delta = usize::max(1, len / steps);
    let approx = (*range.start()..*range.end())
        .step_by(delta)
        .chain([*range.end()])
        .min_by_key(|x| f(*x))
        .unwrap();
    if delta > 1 {
        debug_assert!(2 * (len / 3) + 1 < len);
        return minimum_somewhat_continuous_function(
            usize::max(*range.start(), approx.saturating_sub(len as usize / 3))
                ..=usize::min(*range.end(), approx + len as usize / 3),
            f,
            steps,
        );
    } else {
        return approx;
    }
}
