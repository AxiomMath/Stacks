module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Isomorphisms on homology in a degree where the homology is a bare kernel

Let `u : X ⟶ Y` be a morphism of homological complexes in an abelian category and let `i` be a
degree with neighbours `j = c.prev i` and `c.next i = k`. Suppose both differentials into `i`
vanish, so that the homology in degree `i` is the cycles on both sides, and suppose moreover that
`X.X k` is zero, so that on the source the cycles are all of `X.X i`. Then `u` induces an
isomorphism on homology in degree `i` as soon as `u.f i` exhibits `X.X i` as the kernel of
`Y.d i k`, which is precisely the cycles of `Y` in degree `i`.

This is the degreewise criterion used when a complex has been truncated so that nothing sits above
the degree under consideration: the comparison with the cycles of the target is then the only thing
left to check, and a map which is already an isomorphism in that degree qualifies as soon as the
target also vanishes above it.

A lemma of independent interest is proved along the way: the map induced on the homology in a
degree depends only on the component of the morphism of complexes in that degree.

## Main results

* `HomologicalComplex.homologyMap_congr`: two morphisms of complexes which agree in a degree
  induce the same map on the homology in that degree.
* `HomologicalComplex.isIso_homologyMap_of_isKernel`: the criterion above, with the kernel
  property of `u.f i` given as a limit kernel fork.
* `HomologicalComplex.isIso_homologyMap_of_isIso_f_of_isZero`: the special case in which `Y.X k`
  vanishes too and `u.f i` is an isomorphism. The name is not
  `isIso_homologyMap_of_isIso_f`, which
  `StacksFrontier/Algebra/Homology/Embedding/StupidTruncHomology.lean` already uses in this
  namespace for the criterion asking that `u` be an isomorphism in three consecutive degrees.

## Implementation notes

The map induced on the cycles in a degree is determined by the component of the morphism in that
degree because the inclusion of the cycles is a monomorphism, and the map induced on homology is in
turn determined by the map on cycles because the projection onto homology is an epimorphism.

The proof of the criterion factors `HomologicalComplex.cyclesMap u i` through the inclusion of the
cycles of `X`, which is an isomorphism because `X.d i k` vanishes. Both `u.f i` and `Y.iCycles i`
are kernels of `Y.d i k` — the latter by `HomologicalComplex.cyclesIsKernel` — so the two limit
forks have canonically isomorphic points, and the resulting isomorphism `X.X i ≅ Y.cycles i` is
identified with the cofactor of `cyclesMap u i` by cancelling the monomorphism `Y.iCycles i`. The
passage from cycles to homology is then `HomologicalComplex.homologyπ_naturality`, both
projections `homologyπ` being isomorphisms since the differentials into `i` vanish.

For the special case, an isomorphism is a kernel of a zero map: the lift of a fork is obtained by
composing with the inverse.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {i1 : Type*} {c : ComplexShape i1}
  {X Y : HomologicalComplex C c} (u : X ⟶ Y)

/-- **The map induced on the homology in a degree depends only on the component of the morphism
of complexes in that degree.** -/
theorem homologyMap_congr {f g : X ⟶ Y} (n : i1) (h : f.f n = g.f n) :
    HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n := by
  have hcyc : HomologicalComplex.cyclesMap f n = HomologicalComplex.cyclesMap g n := by
    rw [← cancel_mono (Y.iCycles n), cyclesMap_i, cyclesMap_i, h]
  rw [← cancel_epi (X.homologyπ n), homologyπ_naturality, homologyπ_naturality, hcyc]

/-- **A morphism of complexes which realizes the source as the cycles of the target induces an
isomorphism on homology.** Let `i` be a degree with `c.prev i = j` and `c.next i = k`. If `X.X k`
is a zero object, if the differentials `X.d j i` and `Y.d j i` vanish, and if `u.f i` exhibits
`X.X i` as a kernel of `Y.d i k`, then `u` induces an isomorphism on the homology in degree `i`. -/
theorem isIso_homologyMap_of_isKernel (i j k : i1) (hji : c.prev i = j) (hik : c.next i = k)
    (hXk : IsZero (X.X k)) (hXd : X.d j i = 0) (hYd : Y.d j i = 0)
    (w : u.f i ≫ Y.d i k = 0) (hu : IsLimit (KernelFork.ofι (u.f i) w)) :
    IsIso (HomologicalComplex.homologyMap u i) := by
  have h1 : IsIso (X.iCycles i) := X.isIso_iCycles i k hik (hXk.eq_of_tgt _ _)
  have h2 : IsIso (X.homologyπ i) := X.isIso_homologyπ j i hji hXd
  have h3 : IsIso (Y.homologyπ i) := Y.isIso_homologyπ j i hji hYd
  have he : (IsLimit.conePointUniqueUpToIso hu (Y.cyclesIsKernel i k hik)).hom ≫ Y.iCycles i
      = u.f i :=
    IsLimit.conePointUniqueUpToIso_hom_comp hu (Y.cyclesIsKernel i k hik)
      WalkingParallelPair.zero
  have hc : HomologicalComplex.cyclesMap u i =
      X.iCycles i ≫ (IsLimit.conePointUniqueUpToIso hu (Y.cyclesIsKernel i k hik)).hom := by
    rw [← cancel_mono (Y.iCycles i), Category.assoc, he, cyclesMap_i]
  have h4 : IsIso (HomologicalComplex.cyclesMap u i) := by rw [hc]; infer_instance
  have hm : HomologicalComplex.homologyMap u i =
      inv (X.homologyπ i) ≫ HomologicalComplex.cyclesMap u i ≫ Y.homologyπ i := by
    rw [← homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [hm]
  infer_instance

/-- **A morphism of complexes which is an isomorphism in a degree above which both complexes
vanish induces an isomorphism on homology in that degree.** Let `i` be a degree with
`c.prev i = j` and `c.next i = k`. If `X.X k` and `Y.X k` are zero objects, if the differentials
`X.d j i` and `Y.d j i` vanish, and if `u.f i` is an isomorphism, then `u` induces an isomorphism
on the homology in degree `i`. -/
theorem isIso_homologyMap_of_isIso_f_of_isZero (i j k : i1)
    (hji : c.prev i = j) (hik : c.next i = k)
    (hXk : IsZero (X.X k)) (hYk : IsZero (Y.X k)) (hXd : X.d j i = 0) (hYd : Y.d j i = 0)
    (hu : IsIso (u.f i)) : IsIso (HomologicalComplex.homologyMap u i) := by
  have : IsIso (u.f i) := hu
  have w : u.f i ≫ Y.d i k = 0 := by rw [hYk.eq_of_tgt (Y.d i k) 0, comp_zero]
  refine isIso_homologyMap_of_isKernel u i j k hji hik hXk hXd hYd w
    (KernelFork.IsLimit.ofι _ _ (fun g' _ => g' ≫ inv (u.f i)) (fun g' _ => by simp)
      (fun g' _ m hm => by simp [← hm]))

end HomologicalComplex

end
