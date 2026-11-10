module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingDvrHilbert
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks

/-!
# The degree of the zero cycle of a closed subscheme finite over a field

Let `k` be a field, let `X` be proper over `k` and let `Z ⊆ X` be a closed subscheme which is
finite over `k` and of delta-dimension at most zero. Then

`deg([Z]_0) = dim_k Γ(Z, 𝒪_Z)`.

This is the penultimate display in the proof of [Stacks, Tag 0AZ3]: the source computes

`deg([Z]_0) = ∑_{z ∈ Z} length_{𝒪_{Z,z}}(𝒪_{Z,z}) · [κ(z) : k] = dim_k Γ(Z, 𝒪_Z)`,

the first equality by the definition of the cycle of a closed subscheme ([Stacks, Tag 02QU]) and
of proper pushforward ([Stacks, Tag 02R4]), the second by [Stacks, Tag 02M0] "using that `Z` is
affine". That is what is proved here, in that order.

## Main results

* `Stacks.Chow.residueDegree_eq_finrank_residueField` — the residue degree of a morphism to the
  spectrum of a field is the degree of the residue field over that field.
* `Stacks.Chow.cycleDegree_cycleAssociatedToClosedSubscheme_eq_finrank_globalSections` — **the
  degree formula** displayed above.

## Implementation notes

**This is not [Stacks, Tag 0AZ2].** That tag is the same formula at a cycle *presented* as
`∑ nᵢ [Zᵢ]` over integral closed subschemes, and it is
`Stacks.Chow.cycleDegree_eq_sum_finrank`; its right-hand side is `∑ nᵢ dim_k Γ(Zᵢ, 𝒪_{Zᵢ})`,
a sum over the components. The statement here is about the fundamental cycle of a single closed
subscheme `Z` which is neither reduced nor irreducible, and its right-hand side is
`dim_k Γ(Z, 𝒪_Z)` for that `Z`. Deducing it from Tag 0AZ2 would still need
`∑ᵢ mult_i · [κ(zᵢ) : k] = dim_k Γ(Z, 𝒪_Z)`, which is the whole content; so the proof below
follows the source and uses the definition of pushforward directly, and Tag 0AZ2 is not invoked.

**Where the sum over the points comes from.** The cycle `[Z ⊆ X]_0` is the proper pushforward
along `Z ⟶ X` of the cycle `[Z ⊆ Z]_0` of `Z` in itself
(`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp` at
the identity), so by functoriality of pushforward ([Stacks, Tag 02R5]) the degree may be computed
on `Z`, where the pushforward formula of [Stacks, Tag 02R4] is a sum over all of `Z`: the fibre
of `Z ⟶ Spec(k)` is everything, the spectrum of a field having one point. No finiteness of the
support has to be arranged, and no presentation of the cycle by integral closed subschemes is
needed.

**Every point of `Z` is a generic point of a component**, which is what makes the coefficient of
`[Z ⊆ Z]_0` at `z` the multiplicity there: `Z` is finite over a field, hence a discrete space,
and in a discrete space every singleton is an irreducible component.

The two numerical inputs are
`AlgebraicGeometry.finrank_stalk_eq_length_mul_finrank_residueField` and
`AlgebraicGeometry.finrank_globalSections_eq_finsum_finrank_stalk` of
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks`, which are [Stacks, Tag 02M0]
for the local ring at a point and the affineness of `Z` respectively.

The `k`-algebra structure on `Γ(Z, 𝒪_Z)` is the one induced by the structure morphism, supplied
inside the statement; it is the structure `Stacks.Chow.cycleDegree_eq_sum_finrank` states its
right-hand side with, and the one that
`finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` (in the namespace
`Stacks.AlgebraicGeometry.ProperSectionsGeom`) produces, so the three compose with no transport.

## References

* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0AZ2](https://stacks.math.columbia.edu/tag/0AZ2)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The residue degree over a field -/

/-- **The residue degree of a morphism to the spectrum of a field is the degree of the residue
field.** The residue field of `Spec(k)` is `k` itself, so the tower `k ⊆ κ(g(y)) ⊆ κ(y)` has a
first step of degree one. -/
theorem residueDegree_eq_finrank_residueField (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ AlgebraicGeometry.Spec (.of k)) (y : Y) :
    letI : Algebra k (Y.presheaf.stalk y) :=
      ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
    g.residueDegree y = Module.finrank k (IsLocalRing.ResidueField (Y.presheaf.stalk y)) := by
  let : Algebra k (Y.presheaf.stalk y) :=
    ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
  let S := AlgebraicGeometry.Spec (CommRingCat.of k)
  let s := g.base y
  let K := S.residueField s
  let L : Type u := IsLocalRing.ResidueField (Y.presheaf.stalk y)
  let : Algebra k K := (((Scheme.ΓSpecIso (.of k)).inv ≫ S.Γevaluation s).hom).toAlgebra
  let : Algebra K L := (g.residueFieldMap y).hom.toAlgebra
  have : IsIso (S.Γevaluation s) := isIso_Γevaluation_of_isIntegral_of_subsingleton s
  have hBase : Module.finrank k K = 1 := by
    let eBase : k ≃+* K := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.trans
      (asIso (S.Γevaluation s)).commRingCatIsoToRingEquiv
    let e : k ≃ₐ[k] K := AlgEquiv.ofRingEquiv (f := eBase) (fun _ ↦ rfl)
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  have : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := K) (A := L) fun a ↦ by
      change Y.Γevaluation y (g.appTop ((Scheme.ΓSpecIso (.of k)).inv.hom a)) =
        g.residueFieldMap y (S.Γevaluation s ((Scheme.ΓSpecIso (.of k)).inv.hom a))
      exact (Scheme.Γevaluation_naturality_apply g y ((Scheme.ΓSpecIso (.of k)).inv.hom a)).symm
  have hmul : Module.finrank k K * Module.finrank K L = Module.finrank k L :=
    Module.finrank_mul_finrank k K L
  change Module.finrank K L = Module.finrank k L
  rw [← hmul, hBase, one_mul]

/-! ### The degree of the zero cycle of a closed subscheme -/

/-- Equal closed immersions have equal associated cycles. -/
private theorem cycleAssociatedToClosedSubscheme_congr_hom {C : ChowSituation.{u}}
    {Y Z : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] {a b : Z ⟶ Y}
    [IsClosedImmersion a] [IsClosedImmersion b] (hab : a = b) (d : ℤ)
    [LocallyOfFiniteType (a ≫ q)] [LocallyOfFiniteType (b ≫ q)] :
    cycleAssociatedToClosedSubscheme C q a d = cycleAssociatedToClosedSubscheme C q b d := by
  subst hab
  rfl

/-- **The degree of the zero cycle of a closed subscheme finite over a field.** For `X` proper
over `k` and `Z ⊆ X` closed, finite over `k` and of delta-dimension at most zero,

`deg([Z]_0) = dim_k Γ(Z, 𝒪_Z)`.

This is the penultimate display in the proof of [Stacks, Tag 0AZ3]: the coefficient of `[Z]_0`
at a point of `Z` is the length of the local ring there ([Stacks, Tag 02QU]), the weight with
which it enters the pushforward to `Spec(k)` is the degree of its residue field
([Stacks, Tag 02R4]), and the resulting sum of `length · [κ(z) : k]` over the points of `Z` is
`dim_k Γ(Z, 𝒪_Z)` by [Stacks, Tag 02M0], `Z` being affine. -/
theorem cycleDegree_cycleAssociatedToClosedSubscheme_eq_finrank_globalSections (k : Type u)
    [Field k] {X : Scheme.{u}} (p : X ⟶ AlgebraicGeometry.Spec (.of k)) [IsProper p]
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)]
    (hdim : schemeDeltaDimension (fieldChowSituation k) (I.subschemeι ≫ p) ≤ ((0 : ℤ) : EInt))
    (s : (fieldChowSituation k).S) :
    cycleDegree (fieldChowSituation k) p s
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p I.subschemeι 0) =
      letI : Algebra k Γ(I.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ p).appTop).hom.toAlgebra
      (Module.finrank k Γ(I.subscheme, ⊤) : ℤ) := by
  classical
  let : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ p).appTop).hom.toAlgebra
  have : Finite I.subscheme := finite_of_isFinite_over_field k (I.subschemeι ≫ p)
  have : JacobsonSpace I.subscheme := LocallyOfFiniteType.jacobsonSpace (I.subschemeι ≫ p)
  have : DiscreteTopology I.subscheme := inferInstance
  have : IsClosedImmersion (𝟙 I.subscheme ≫ I.subschemeι) := by
    rw [Category.id_comp]; infer_instance
  have : LocallyOfFiniteType ((𝟙 I.subscheme ≫ I.subschemeι) ≫ p) := by
    rw [Category.id_comp]; infer_instance
  -- the relative dimension vanishes at every point of the subscheme
  have hz0 : ∀ z : I.subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (I.subschemeι ≫ p) z = 0 :=
    fun z ↦ le_antisymm
      (StalkLocalSituation.relativeDimension_le_of_schemeDeltaDimension_le
        (fieldChowSituation k) _ hdim z)
      (relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) _ z)
  -- the cycle of `Z` in `X` is the pushforward of the cycle of `Z` in itself
  have hpf : properPushforward (fieldChowSituation k) (I.subschemeι ≫ p) p I.subschemeι rfl 0
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (I.subschemeι ≫ p)
        (𝟙 I.subscheme) 0) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) p I.subschemeι 0 :=
    (properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      (fieldChowSituation k) (I.subschemeι ≫ p) p I.subschemeι rfl (𝟙 I.subscheme) 0).trans
      (cycleAssociatedToClosedSubscheme_congr_hom (C := fieldChowSituation k) p
        (Category.id_comp I.subschemeι) 0)
  -- the fibre of `Z ⟶ Spec(k)` is all of `Z`
  have huniv : (I.subschemeι ≫ p).base ⁻¹' {s} = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [cycleDegree_apply, ← hpf, properPushforward_properPushforward, properPushforward_apply,
    huniv, finsum_mem_univ]
  -- each summand is the dimension of the stalk
  have hterm : ∀ z : I.subscheme,
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (I.subschemeι ≫ p)
            (𝟙 I.subscheme) 0).1 z *
          (if relativeDimension (fieldChowSituation k).dimensionFunction (I.subschemeι ≫ p) z =
              relativeDimension (fieldChowSituation k).dimensionFunction
                (𝟙 (fieldChowSituation k).S) ((I.subschemeι ≫ p).base z) then
            ((I.subschemeι ≫ p).residueDegree z : ℤ) else 0) =
        (letI : Algebra k (I.subscheme.presheaf.stalk z) :=
          ((I.subscheme.presheaf.germ ⊤ z (by simp)).hom.comp
            ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ p).appTop).hom).toAlgebra
        (Module.finrank k (I.subscheme.presheaf.stalk z) : ℤ)) := by
    intro z
    let : Algebra k (I.subscheme.presheaf.stalk z) :=
      ((I.subscheme.presheaf.germ ⊤ z (by simp)).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ p).appTop).hom).toAlgebra
    have hbase : relativeDimension (fieldChowSituation k).dimensionFunction
        (𝟙 (fieldChowSituation k).S) ((I.subschemeι ≫ p).base z) = 0 := by
      rw [relativeDimension_id]
      rfl
    have hcoeff : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (I.subschemeι ≫ p)
        (𝟙 I.subscheme) 0).1 z =
        ((Module.length (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z)).toNat :
          ℤ) := by
      have hgen : z ∈ genericPoints I.subscheme := mem_genericPoints_of_discreteTopology z
      have h := cycleAssociatedToClosedSubscheme_apply (fieldChowSituation k)
        (I.subschemeι ≫ p) (𝟙 I.subscheme) 0 ⟨z, hgen⟩ (by simpa using hz0 z)
      rw [componentMultiplicity_eq_length_stalk (𝟙 I.subscheme) ⟨z, hgen⟩] at h
      simpa using h
    rw [hcoeff, ite_eq_left (by rw [hz0 z, hbase]),
      residueDegree_eq_finrank_residueField k (I.subschemeι ≫ p) z,
      finrank_stalk_eq_length_mul_finrank_residueField k (I.subschemeι ≫ p) z]
    push_cast
    ring
  rw [finsum_congr hterm, finrank_globalSections_eq_finsum_finrank_stalk k (I.subschemeι ≫ p)]
  let : Fintype I.subscheme := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]

end Stacks.Chow

end
