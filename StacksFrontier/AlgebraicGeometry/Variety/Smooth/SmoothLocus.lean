module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing

/-!
# The smooth locus of a scheme over a perfect field

For a scheme locally of finite type over a perfect field, smoothness at a point is equivalent to
regularity of the local ring at that point. The locus where a morphism is smooth is open, and
when the scheme is reduced and the ground field perfect it is dense.

## Main results

* `AlgebraicGeometry.smoothAt_locus_eq_regular_locus`: over a perfect field the smooth locus is
  the locus of regular local rings.
* `AlgebraicGeometry.isOpen_smoothAt_locus`: the smooth locus is open.
* `AlgebraicGeometry.dense_smoothAt_locus`: over a perfect field the smooth locus of a reduced
  scheme is dense.
* `AlgebraicGeometry.smoothAt_locus_eq_regular_locus_and_isOpen_and_dense`: the three assertions
  together.

## References

* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

add_to_stacks 0B8X "density of the smooth locus"
  AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField
add_to_sga "4½ Th_finitude 2.7" "Perfect-field clause"
  AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField
add_to_ega "IV 17.15.12" "special case"
  AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField
add_to_ega "IV 17.15.13" "special case"
  AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField

/-- For a scheme locally of finite type over a field, smoothness at a point is formal smoothness
of the stalk map. -/
private lemma smoothAt_iff_formallySmooth_stalkMap
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    InfinitesimalLifting.SmoothAt f x ↔ (f.stalkMap x).hom.FormallySmooth :=
  ⟨InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x,
    InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x⟩

/-- Over a perfect field, the points where a locally finite type scheme is smooth are exactly
the points whose local rings are regular. -/
@[stacks 0B8X "equality of the smooth and regular loci",
  ega "IV 17.15.2" "k perfect case",
  sga "1 II 5.4" "perfect k",
  ega "0 19.0.2" "more general",
  ega "IV 17.15.5" "special case",
  sga "6 XIV 4.2" "Clause"]
public theorem smoothAt_locus_eq_regular_locus
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    {x : X | InfinitesimalLifting.SmoothAt f x} =
      {x : X | IsRegularLocalRing (X.presheaf.stalk x)} := by
  ext x
  let U : (Spec (.of k)).Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top _
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU' : V ≤ f ⁻¹ᵁ U := by simp [U]
  let _ : Field Γ(Spec (.of k), U) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField k)).toField
  have : PerfectField Γ(Spec (.of k), U) :=
    PerfectField.of_ringEquiv
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  let _ : Algebra Γ(Spec (.of k), U) Γ(X, V) :=
    (f.appLE U V hVU').hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), U) Γ(X, V) :=
    f.finiteType_appLE hU hV hVU'
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  have : Algebra.IsSeparableExtension Γ(Spec (.of k), U) q.ResidueField :=
    ⟨fun L' _ => by
      obtain ⟨s, hs, hsep⟩ :=
        exists_isTranscendenceBasis_and_isSeparable_of_perfectField Γ(Spec (.of k), U) L'
      exact ⟨(s : Set L'), hs, hsep⟩⟩
  show InfinitesimalLifting.SmoothAt f x ↔ IsRegularLocalRing (X.presheaf.stalk x)
  rw [← Algebra.isSmoothAt_iff_isRegularLocalRing (k := Γ(Spec (.of k), U)) q (X.presheaf.stalk x)]
  exact (smoothAt_iff_formallySmooth_stalkMap k f x).trans
    (formallySmooth_stalkMap_iff U hU V hV hVU' hxV)

/-- The locus where a morphism of schemes is smooth is open. -/
@[stacks 0B8X "openness of the smooth locus"]
public theorem isOpen_smoothAt_locus
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsOpen {x : X | InfinitesimalLifting.SmoothAt f x} :=
  isOpen_iff_forall_mem_open.mpr fun _ ⟨U, hxU, hU⟩ => ⟨U, fun _ hy => ⟨U, hy, hU⟩, U.2, hxU⟩

/-- For a scheme locally of finite type over a field, the pointwise smooth locus coincides with
the open subscheme `Scheme.Hom.smoothLocus` cut out by formal smoothness of the stalk maps. -/
@[sga "4 XI 2.1" "partial"]
private lemma smoothAt_locus_eq_coe_smoothLocus
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    {x : X | InfinitesimalLifting.SmoothAt f x} = (f.smoothLocus : Set X) :=
  Set.ext fun x =>
    (smoothAt_iff_formallySmooth_stalkMap k f x).trans Scheme.Hom.mem_smoothLocus.symm

/-- Over a perfect field, the points where a reduced scheme locally of finite type is smooth are
dense. -/
@[stacks 0B8X "density of the smooth locus", sga "4½ Th_finitude 2.7" "Perfect-field clause"]
public theorem dense_smoothAt_locus
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Dense {x : X | InfinitesimalLifting.SmoothAt f x} := by
  rw [smoothAt_locus_eq_coe_smoothLocus k f]
  exact f.dense_smoothLocus_of_perfectField

/-- Let `k` be a perfect field and let `X` be a reduced scheme locally of finite type over `k`.
Then the set of points at which `X` is smooth over `k` is the set of points whose local ring is
regular, and that set is a dense open subset of `X`. -/
@[stacks 0B8X,
  ega "0 19.0.2" "IV, special case",
  ega "IV 17.15.12" "special case",
  ega "IV 6.12.5" "special case",
  ega "IV 6.8.7" "special case",
  ega "IV 7.8.3" "(iv), openness of Reg(X)",
  ega "IV 7.8.6" "(iii), special case",
  sga "1 II 4.14" "special case",
  sga "1 II 5.4" "more general",
  sga "4½ Th_finitude 2.7" "Perfect-field clause",
  sga "6 XIV 4.2" "Clause"]
public theorem smoothAt_locus_eq_regular_locus_and_isOpen_and_dense
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    {x : X | InfinitesimalLifting.SmoothAt f x} =
        {x : X | IsRegularLocalRing (X.presheaf.stalk x)} ∧
      IsOpen {x : X | InfinitesimalLifting.SmoothAt f x} ∧
      Dense {x : X | InfinitesimalLifting.SmoothAt f x} :=
  ⟨smoothAt_locus_eq_regular_locus k f, isOpen_smoothAt_locus f, dense_smoothAt_locus k f⟩

end AlgebraicGeometry

end
