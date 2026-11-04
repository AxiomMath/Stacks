module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# Quasi-affineness descends along a norm

Let `f : X ⟶ Y` be a finite morphism of schemes carrying a norm `N` of degree `d > 0`
(`Stacks.Norm.MorphismNorm`). If `X` is quasi-affine then so is `Y`.

The proof is the source's. A quasi-affine scheme is one whose structure sheaf is ample
(Tag 01QE), so a point `y` of `Y` can be separated from the complement of an affine
neighbourhood `V` by a global function `g` on `X`: the fibre `f⁻¹{y}` is finite, and the
nonvanishing locus of a global section of a tensor power of `𝒪_X` is a basic open
`X_g` with `f⁻¹{y} ⊆ X_g ⊆ f⁻¹V` (Tag 09NV). The norm `N(g)` is then a global function
on `Y` whose basic open contains `y` and is contained in `V`, hence is affine; those
basic opens cover `Y`, which is quasi-affine by Mathlib's criterion.

The two halves of that last step are the two conditions on a norm other than
multiplicativity. A function which is a unit on all of `f⁻¹W` has a norm which is a unit on
`W`, because the norm is a monoid map compatible with restriction: this gives
`y ∈ Y_{N(g)}`. A function vanishing at a point `x` has a norm vanishing at `f x`: this
gives `Y_{N(g)} ⊆ V`, using that `f` is surjective — which positivity of the degree
forces: if not, the norm would carry `1 = f^#1` and `0 = f^#0` to the same section
over an open disjoint from the image.

## Main results

* `Stacks.Divisors.surjective_of_hasNormOfDegree`: a universally closed morphism carrying a
  norm of positive degree is surjective.
* `Stacks.Divisors.mem_basicOpen_norm_of_fibre_subset`: the norm of a function nonvanishing
  on the whole fibre over `y` is nonvanishing at `y`.
* `Stacks.Divisors.isQuasiAffine_of_isFinite_of_hasNormOfDegree`: **Tag 0BD1.**

## Implementation notes

`surjective_of_hasNormOfDegree` and `mem_basicOpen_norm_of_fibre_subset` assume only
`UniversallyClosed f`, which is all their proofs use; `IsFinite f` is not needed for either
and the surjectivity statement is of independent use elsewhere in the section.

Ampleness is `Stacks.Ample.IsAmple`, over the integer tensor powers of
`Stacks.Ample.tensorPowModule`, and the fact that every nonvanishing locus of a global
section of a power of `𝒪_X` is a basic open of `𝒪_X` is
`Stacks.Ample.NonvanishingBasis.exists_basicOpen_eq` applied to
`Stacks.Ample.unitTensorPowBasis`; no separate computation of the sections of a tensor power
of the structure sheaf is made here.

## References

* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Ample

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-- **A norm on a morphism with nonempty source has positive degree.** In degree `0` the norm
of the zero function is `0 ^ 0 = 1`, while a norm sends a function vanishing at a point of the
source to one vanishing at its image; so `1 = 0` in a residue field of the target. -/
theorem pos_of_morphismNorm (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d) (x : X) : 0 < d := by
  refine Nat.pos_of_ne_zero fun hd ↦ ?_
  have hone : N.app ⊤ (0 : Γ(X, f ⁻¹ᵁ (⊤ : Y.Opens))) = 1 := by
    rw [show (0 : Γ(X, f ⁻¹ᵁ (⊤ : Y.Opens))) = f.app ⊤ (0 : Γ(Y, ⊤)) from (map_zero _).symm,
      N.app_pullback, hd, pow_zero]
  have hzero := N.app_eq_zero_at_image (U := ⊤) (0 : Γ(X, f ⁻¹ᵁ (⊤ : Y.Opens))) x trivial
    (map_zero _)
  rw [hone] at hzero
  exact one_ne_zero ((map_one (Y.evaluation ⊤ (f.base x) trivial).hom).symm.trans hzero)

/-- **A morphism carrying a norm of positive degree is surjective.** Over an open `U` of the
target disjoint from the image the sections of the source vanish, so the norm sends the
pullbacks of `0` and of `1` to the same section of `𝒪_Y(U)`; those are `0` and `1`, and `U`
is empty. -/
theorem surjective_of_hasNormOfDegree (f : X ⟶ Y) [UniversallyClosed f] {d : ℕ} (hd : 0 < d)
    (N : MorphismNorm f d) : Surjective f := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hrange : IsClosed (Set.range f.base) := by
    simpa [Set.image_univ] using f.isClosedMap Set.univ isClosed_univ
  let U : Y.Opens := ⟨(Set.range f.base)ᶜ, hrange.isOpen_compl⟩
  have hyU : y ∈ U := by simpa [U, Set.mem_range] using hy
  have hpre : f ⁻¹ᵁ U = (⊥ : X.Opens) := by
    apply Opens.ext
    ext x
    simp [U]
  have : Subsingleton Γ(X, f ⁻¹ᵁ U) := by rw [hpre]; infer_instance
  have hone : N.app U (f.app U (1 : Γ(Y, U))) = 1 := by rw [N.app_pullback, one_pow]
  have hzero : N.app U (f.app U (0 : Γ(Y, U))) = 0 := by rw [N.app_pullback, zero_pow hd.ne']
  have h01 : (0 : Γ(Y, U)) = 1 :=
    hzero.symm.trans (congrArg (N.app U) (Subsingleton.elim _ _) |>.trans hone)
  have hz : (1 : Y.residueField y) = 0 := by
    simpa using (congrArg (Y.evaluation U y hyU).hom h01).symm
  exact one_ne_zero hz

/-- **The norm of a function nonvanishing on a whole fibre is nonvanishing at the image
point.** The complement of `X_g` is closed, hence so is its image; on the open complement
`W` of that image the restriction of `g` is a unit, so its norm is a unit on `W`, and `y`
lies in `W`. -/
theorem mem_basicOpen_norm_of_fibre_subset (f : X ⟶ Y) [UniversallyClosed f]
    (N : MorphismNormMap f) (y : Y) (g : Γ(X, ⊤))
    (hfibre : f.base ⁻¹' ({y} : Set Y) ⊆ (X.basicOpen g : Set X)) :
    y ∈ Y.basicOpen (N.app ⊤ g) := by
  have hclosed : IsClosed (f.base '' (X.basicOpen g : Set X)ᶜ) :=
    f.isClosedMap _ (X.basicOpen g).2.isClosed_compl
  let W : Y.Opens := ⟨(f.base '' (X.basicOpen g : Set X)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hyW : y ∈ W := by
    rintro ⟨x, hxC, hxy⟩
    exact hxC (hfibre (by simp [hxy]))
  have hpre : f ⁻¹ᵁ W ≤ X.basicOpen g := fun x hx => by
    by_contra hxg
    exact hx ⟨x, hxg, rfl⟩
  let i : W ⟶ (⊤ : Y.Opens) := homOfLE le_top
  have hgW : IsUnit (X.presheaf.map ((Opens.map f.base).map i).op g) := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ (f ⁻¹ᵁ W) _ fun x hx => ?_
    rw [X.presheaf.germ_res_apply ((Opens.map f.base).map i) x hx g]
    exact (X.mem_basicOpen g x trivial).mp (hpre hx)
  have hres : IsUnit (Y.presheaf.map i.op (N.app ⊤ g)) := by
    rw [← N.naturality i g]
    exact hgW.map (N.app W)
  refine (Y.mem_basicOpen (N.app ⊤ g) y trivial).mpr ?_
  rw [← Y.presheaf.germ_res_apply i y hyW (N.app ⊤ g)]
  exact (Y.presheaf.germ W y hyW).hom.isUnit_map hres

/-- **Stacks Project, Tag 0BD1.** The target of a finite morphism carrying a norm of positive
degree is quasi-affine as soon as its source is. -/
@[stacks 0BD1]
theorem isQuasiAffine_of_isFinite_of_hasNormOfDegree (f : X ⟶ Y) [IsFinite f]
    [Scheme.IsQuasiAffine X] {d : ℕ} (hd : 0 < d) (hN : HasNormOfDegree f d) :
    Scheme.IsQuasiAffine Y := by
  obtain ⟨N⟩ := hN
  have hsurj : Function.Surjective f.base := (surjective_of_hasNormOfDegree f hd N).1
  have : CompactSpace Y := by
    rw [← isCompact_univ_iff, ← Set.range_eq_univ.mpr hsurj, ← Set.image_univ]
    exact isCompact_univ.image f.continuous
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen Y fun y => ?_
  obtain ⟨R, j, hj, hyj, -⟩ :=
    Y.exists_affine_mem_range_and_range_subset (x := y) (U := ⊤) trivial
  have : IsOpenImmersion j := hj
  let V : Y.Opens := j ''ᵁ (⊤ : (Spec R).Opens)
  have hVaff : IsAffineOpen V := IsAffineOpen.image_of_isOpenImmersion (isAffineOpen_top _) j
  have hyV : y ∈ V := by simpa [V, Set.image_univ] using hyj
  obtain ⟨n, -, s, haff, hfibre, hsmall⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite
      (unitModule X)
      ((isQuasiAffine_iff_isAmple X).mp inferInstance)
      (f.finite_preimage_singleton y) (f ⁻¹ᵁ V) fun x hx => by
        show f.base x ∈ V
        rw [show f.base x = y from hx]
        exact hyV
  obtain ⟨g, hg⟩ :=
    (unitTensorPowBasis X (n : ℤ)).exists_basicOpen_eq s
  have hXg : Stacks.AmpleTheory.powNonvanishingOpen X (unitModule X) n s = X.basicOpen g :=
    Opens.ext hg
  rw [hXg] at haff hfibre hsmall
  refine ⟨N.app ⊤ g, ?_, ?_⟩
  · have hsub : (Y.basicOpen (N.app ⊤ g) : Set Y) ⊆ (V : Set Y) := by
      intro z hz
      obtain ⟨x, hxz⟩ := hsurj z
      by_contra hzV
      have hxg : x ∉ X.basicOpen g := fun hxg => hzV (by simpa [hxz] using hsmall hxg)
      have := N.app_eq_zero_at_image (U := ⊤) g x trivial
        ((X.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) x trivial g).2 hxg)
      rw [hxz] at this
      exact (Y.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) z trivial (N.app ⊤ g)).2 hz this
    have hbasic : Y.basicOpen (Y.presheaf.map (homOfLE (le_top (a := V))).op (N.app ⊤ g)) =
        Y.basicOpen (N.app ⊤ g) := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr hsub
    rw [← hbasic]
    exact hVaff.basicOpen _
  · exact mem_basicOpen_norm_of_fibre_subset f N.toMorphismNormMap y g hfibre

end Stacks.Divisors

end
