extern crate cc;

fn main() {
    /* Link CUDA Runtime (libcudart.so) */

    // Add link directory
    // - This path depends on where you install CUDA (i.e. depends on your Linux distribution)
    // - This should be set by `$LIBRARY_PATH`
    println!("cargo:rustc-link-search=native=/usr/local/cuda-11.1/lib64");
    println!("cargo:rustc-link-lib=cudart");

    /* Optional: Link CUDA Driver API (libcuda.so) */

    // println!("cargo:rustc-link-search=native=/usr/local/cuda/lib64/stub");
    // println!("cargo:rustc-link-lib=cuda");

    cc::Build::new()
        .cuda(true)
        .cudart("static")
        .flag("-gencode")
        .flag("arch=compute_75,code=sm_75")
        .file("merkletree-poseidon-cuda/field.cu")
        .file("merkletree-poseidon-cuda/poseidon.cu")
        .file("merkletree-poseidon-cuda/merkle_tree.cu")
        .file("merkletree-poseidon-cuda/cc_rust.cu")
        .compile("libmerkletree_cuda.a");
}
