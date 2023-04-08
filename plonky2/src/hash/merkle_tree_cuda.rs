use std::mem;

#[link(name = "merkletree_cuda")]
extern "C" {
    fn calculate_digests_caps(
        leaves: *const u64,
        num_leaves: u32,
        leave_len: u32,
        cap_height: u32,
    ) -> *mut u64;
}

#[allow(unused_mut)]
pub fn construct_tree<F, H: std::clone::Clone + std::fmt::Debug>(
    leaves: Vec<Vec<F>>,
    cap_height: usize,
) -> (Vec<H>, Vec<H>) {
    let num_leaves = leaves.len();
    let leave_len = leaves[0].len();

    let mut tmp: &[H];
    let mut digests: Vec<H>;
    let mut cap: Vec<H>;

    let flattened_leaves = leaves.into_iter().flatten().collect::<Vec<F>>();

    unsafe {
        let leaves_ptr = mem::transmute::<*const F, *const u64>(flattened_leaves.as_ptr());

        let digests_cap_ptr = mem::transmute::<*mut u64, *mut H>(calculate_digests_caps(
            leaves_ptr,
            num_leaves as u32,
            leave_len as u32,
            cap_height as u32,
        ));
        // let cap_start = digests_cap_ptr.add(num_digests);
        // digests = Vec::from_raw_parts(digests_cap_ptr as *mut _, num_digests, num_digests);

        // // cap = Vec::from_raw_parts(cap_start as *mut _, 1, 1);
        // let cap_slice = std::slice::from_raw_parts(cap_start, 1);
        // cap = cap_slice.to_vec();

        tmp = std::slice::from_raw_parts(digests_cap_ptr, 2 * num_leaves - (1 << cap_height));
        digests = tmp[..(2 * (num_leaves - (1 << cap_height)))].to_vec();
        cap = tmp[(2 * (num_leaves - (1 << cap_height)))..(2 * num_leaves - (1 << cap_height))]
            .to_vec();
    }

    (digests, cap)
}
