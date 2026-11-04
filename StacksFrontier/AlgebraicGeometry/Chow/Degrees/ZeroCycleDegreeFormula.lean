module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.SimpleRing.Field
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a zero cycle as a sum of component degrees

Let `k` be a field and `X` a scheme proper over `k`. A zero cycle on `X` is a locally finite
sum `α = ∑ n_i [Z_i]` over integral closed subschemes `Z_i ⊆ X` of delta-dimension zero, and its
degree is `∑ n_i deg(Z_i)`, where `deg(Z_i) = dim_k Γ(Z_i, 𝒪_{Z_i})` is the degree of
`Z_i → Spec(k)`.

## Main results

* `Stacks.Chow.subsingleton_of_topologicalKrullDim_le_zero` — an irreducible sober space of
  Krull dimension zero has one point.
* `Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton` — on an integral scheme with one
  point the evaluation of a global section in the residue field is an isomorphism.
* `Stacks.Chow.residueDegree_eq_finrank_globalSections` — the residue degree of a morphism from
  an integral one-point scheme to the spectrum of a field is the dimension of its ring of global
  sections.
* `Stacks.Chow.subsingleton_subscheme_of_schemeDeltaDimension_eq_zero` — an integral closed
  subscheme of delta-dimension zero over a field has one point.
* `Stacks.Chow.residueDegree_genericPointOf_eq_finrank` — the residue degree at the generic point
  of an integral closed subscheme `Z` of delta-dimension zero is `dim_k Γ(Z, 𝒪_Z)`.
* `Stacks.Chow.cycleDegree_eq_sum_finrank` — the degree of `∑ n_i [Z_i]` is
  `∑ n_i dim_k Γ(Z_i, 𝒪_{Z_i})`.

## Implementation notes

An integral closed subscheme is given as an `AlgebraicGeometry.Scheme.IdealSheafData` together
with integrality of the associated subscheme, and its generic point in `X` is
`Stacks.Chow.genericPointOf`.

The `k`-algebra structure on `Γ(Z, 𝒪_Z)` is the one coming from the structure morphism
`Z ⟶ Spec(k)`, supplied inside the statement rather than as an instance, because it depends on
the morphism and not only on the two rings.

## References

* [Stacks Project, Tag 0AZ2](https://stacks.math.columbia.edu/tag/0AZ2)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Integral schemes of dimension zero -/

/-- An irreducible sober space of Krull dimension zero has a single point. -/
theorem subsingleton_of_topologicalKrullDim_le_zero {Y : Type*} [TopologicalSpace Y] [T0Space Y]
    [IrreducibleSpace Y] (h : topologicalKrullDim Y ≤ 0) : Subsingleton Y := by
  have hall (x : Y) : closure ({x} : Set Y) = Set.univ := by
    by_contra hne
    refine absurd h (not_le_of_gt (Order.krullDim_pos_iff.mpr ⟨
      ⟨closure ({x} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩,
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩,
      lt_of_le_of_ne (Set.subset_univ _)
        fun he ↦ hne (congrArg IrreducibleCloseds.carrier he)⟩))
  refine ⟨fun x y ↦ ?_⟩
  exact ((specializes_iff_closure_subset.mpr (by simp [hall x])).antisymm
    (specializes_iff_closure_subset.mpr (by simp [hall y]))).eq

/-- On an integral scheme with a single point, evaluating a global section in the residue field
at that point is an isomorphism of rings. -/
theorem isIso_Γevaluation_of_isIntegral_of_subsingleton {Y : Scheme.{u}} [IsIntegral Y]
    [Subsingleton Y] (x : Y) : IsIso (Y.Γevaluation x) := by
  have hgerm : Function.Surjective (Y.presheaf.germ ⊤ x trivial).hom := by
    intro t
    obtain ⟨U, hxU, s, hs⟩ := Y.presheaf.exists_germ_eq t
    have hU : U = ⊤ := le_antisymm le_top fun y _ ↦ Subsingleton.elim x y ▸ hxU
    subst hU
    exact ⟨s, hs⟩
  let _ : IsSimpleRing Γ(Y, ⊤) :=
    (isSimpleRing_iff_isField _).2 (isField_of_isIntegral_of_subsingleton Y)
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  change Function.Bijective ((Y.residue x).hom.comp (Y.presheaf.germ ⊤ x trivial).hom)
  exact ⟨RingHom.injective _, (Y.residue_surjective x).comp hgerm⟩

/-- **The degree of a one-point integral scheme over a field.** For `Y` integral with a single
point and `f : Y ⟶ Spec(k)`, the residue degree of `f` is the dimension of the ring of global
sections of `Y` as a `k`-vector space. -/
theorem residueDegree_eq_finrank_globalSections (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ AlgebraicGeometry.Spec (.of k)) [IsIntegral Y] [Subsingleton Y] (η : Y) :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    f.residueDegree η = Module.finrank k Γ(Y, ⊤) := by
  let S := AlgebraicGeometry.Spec (CommRingCat.of k)
  let y := f.base η
  let L := Y.residueField η
  let K := S.residueField y
  let A := Γ(Y, ⊤)
  let : Algebra k A := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra k K := (((Scheme.ΓSpecIso (.of k)).inv ≫ S.Γevaluation y).hom).toAlgebra
  let : Algebra K L := (f.residueFieldMap η).hom.toAlgebra
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsIso (S.Γevaluation y) := isIso_Γevaluation_of_isIntegral_of_subsingleton y
  let : IsIso (Y.Γevaluation η) := isIso_Γevaluation_of_isIntegral_of_subsingleton η
  have hBase : Module.finrank k K = 1 := by
    let eBase : k ≃+* K :=
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.trans
        (asIso (S.Γevaluation y)).commRingCatIsoToRingEquiv
    let e : k ≃ₐ[k] K := AlgEquiv.ofRingEquiv (f := eBase) (fun _ ↦ rfl)
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hTarget : Module.finrank k A = Module.finrank k L := by
    let eTarget : A ≃+* L := (asIso (Y.Γevaluation η)).commRingCatIsoToRingEquiv
    let e : A ≃ₐ[k] L := AlgEquiv.ofRingEquiv (f := eTarget) (by
      intro a
      change Y.Γevaluation η (f.appTop ((Scheme.ΓSpecIso (.of k)).inv.hom a)) =
        f.residueFieldMap η (S.Γevaluation y ((Scheme.ΓSpecIso (.of k)).inv.hom a))
      exact (Scheme.Γevaluation_naturality_apply f η ((Scheme.ΓSpecIso (.of k)).inv.hom a)).symm)
    exact e.toLinearEquiv.finrank_eq
  have hmul : Module.finrank k K * Module.finrank K L = Module.finrank k L :=
    Module.finrank_mul_finrank k K L
  change f.residueDegree η = Module.finrank k A
  rw [show f.residueDegree η = Module.finrank K L from rfl, ← hTarget] at *
  simpa [hBase] using hmul

/-! ### Components of a zero cycle over a field -/

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S)

/-- An integral closed subscheme of delta-dimension zero of a scheme locally of finite type over
a field has a single point. -/
theorem subsingleton_subscheme_of_schemeDeltaDimension_eq_zero [LocallyOfFiniteType p]
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension (fieldChowSituation k) (W.subschemeι ≫ p) = (0 : EInt)) :
    Subsingleton W.subscheme := by
  have := hW
  have hgen : IsGenericPoint (genericPoint W.subscheme) (Set.univ : Set W.subscheme) :=
    (IrreducibleSpace.isIrreducible_univ W.subscheme).isGenericPoint_genericPoint isClosed_univ
  refine subsingleton_of_topologicalKrullDim_le_zero (le_of_eq ?_)
  rw [topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ ↦ rfl) p W.subschemeι (genericPoint W.subscheme) hgen,
    show W.subschemeι.base (genericPoint W.subscheme) = genericPointOf W hW from rfl,
    relativeDimension_genericPointOf (fieldChowSituation k) p W hW hDim]
  rfl

/-- **The degree of an integral closed subscheme of delta-dimension zero.** The residue degree of
`p` at the generic point of such a subscheme `Z` is `dim_k Γ(Z, 𝒪_Z)`, the degree of
`Z → Spec(k)`. -/
theorem residueDegree_genericPointOf_eq_finrank [LocallyOfFiniteType p] (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension (fieldChowSituation k) (W.subschemeι ≫ p) = (0 : EInt)) :
    letI : Algebra k Γ(W.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (W.subschemeι ≫ p).appTop).hom.toAlgebra
    p.residueDegree (genericPointOf W hW) = Module.finrank k Γ(W.subscheme, ⊤) := by
  have := hW
  have := subsingleton_subscheme_of_schemeDeltaDimension_eq_zero k p W hW hDim
  rw [show genericPointOf W hW = W.subschemeι.base (genericPoint W.subscheme) from rfl,
    ← residueDegree_of_bijective_residueFieldMap_comp W.subschemeι p _
      (bijective_residueFieldMap_of_isClosedImmersion W.subschemeι (genericPoint W.subscheme))]
  exact residueDegree_eq_finrank_globalSections k (W.subschemeι ≫ p) (genericPoint W.subscheme)

/-- The degree `Stacks.Chow.cycleDegree` of a zero cycle on a scheme proper over a field,
presented as a finite sum `α = ∑ n_i [Z_i]` over integral closed subschemes of delta-dimension
zero, is `∑ n_i dim_k Γ(Z_i, 𝒪_{Z_i})`, where `dim_k Γ(Z_i, 𝒪_{Z_i})` is the degree of
`Z_i → Spec(k)`. -/
@[stacks 0AZ2]
theorem cycleDegree_eq_sum_finrank [IsProper p] (s : (fieldChowSituation k).S)
    (α : CycleGroup (fieldChowSituation k) p 0) {J : Type*} [Fintype J]
    (W : J → X.IdealSheafData) (hW : ∀ i, IsIntegral (W i).subscheme) (n : J → ℤ)
    (hDim : ∀ i, schemeDeltaDimension (fieldChowSituation k) ((W i).subschemeι ≫ p) = (0 : EInt))
    (hα : α.1 = ∑ i, @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
      (genericPointOf (W i) (hW i)) (n i)) :
    cycleDegree (fieldChowSituation k) p s α =
      ∑ i : J, n i *
        (letI : Algebra k Γ((W i).subscheme, ⊤) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ ((W i).subschemeι ≫ p).appTop).hom.toAlgebra
        (Module.finrank k Γ((W i).subscheme, ⊤) : ℤ)) := by
  classical
  have hfiber : p.base ⁻¹' {s} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hfinrank (i : J) : (p.residueDegree (genericPointOf (W i) (hW i)) : ℤ) =
      (letI : Algebra k Γ((W i).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ ((W i).subschemeι ≫ p).appTop).hom.toAlgebra
      (Module.finrank k Γ((W i).subscheme, ⊤) : ℤ)) := by
    exact_mod_cast residueDegree_genericPointOf_eq_finrank k p (W i) (hW i) (hDim i)
  rw [cycleDegree_apply, properPushforward_apply, hα, hfiber, finsum_mem_univ]
  simp_rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply, Finset.sum_mul]
  rw [← sum_finsum_comm Finset.univ
    (fun i x ↦ (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
      (genericPointOf (W i) (hW i)) (n i)) x *
      (if relativeDimension (fieldChowSituation k).dimensionFunction p x =
          relativeDimension (fieldChowSituation k).dimensionFunction
            (𝟙 (fieldChowSituation k).S) (p.base x) then
        (p.residueDegree x : ℤ) else 0))]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hp : relativeDimension (fieldChowSituation k).dimensionFunction p
        (genericPointOf (W i) (hW i)) = 0 :=
      relativeDimension_genericPointOf (fieldChowSituation k) p (W i) (hW i) (hDim i)
    have hs : relativeDimension (fieldChowSituation k).dimensionFunction
        (𝟙 (fieldChowSituation k).S) (p.base (genericPointOf (W i) (hW i))) = 0 := by
      rw [relativeDimension_id]
      rfl
    rw [finsum_eq_single _ (genericPointOf (W i) (hW i)) fun x hx ↦ by
      simp [Function.locallyFinsuppWithin.single_apply, hx],
      show (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        (genericPointOf (W i) (hW i)) (n i)) (genericPointOf (W i) (hW i)) = n i by
      simp [Function.locallyFinsuppWithin.single_apply],
      ite_eq_left_of_eq_true _ _ (eq_true (hp.trans hs.symm)), hfinrank i]
  · intro i _
    refine (Set.finite_singleton (genericPointOf (W i) (hW i))).subset fun x hx ↦ ?_
    by_contra hne
    simp only [Set.mem_singleton_iff] at hne
    exact hx (by simp [Function.locallyFinsuppWithin.single_apply, hne])

end Stacks.Chow

end
