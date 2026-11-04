module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilGlobalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.VanishingDifferentialsDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.HodgeDuality
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexCech
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyVanishingAboveDimension

/-!
# The de Rham cohomology of the point

Axiom (A5) of Weil Cohomology Theories, Section 0FID asks first that `H^*(Spec k) = F`. For de
Rham cohomology over a field `k` (Section 0FWC) this is the statement
`H^*_{dR}(Spec(k)/k) = k` in degree `0`: the relative differentials vanish, so the de Rham complex
is `𝒪` in degree `0`, whose cohomology on the one-point space `Spec k` vanishes in positive
degrees (Grothendieck's vanishing theorem, Tag 02UZ) and is `Γ(Spec k, 𝒪) = k` in degree `0`.

It is stated for every smooth projective `k`-scheme `X` whose structure morphism is an
isomorphism.

## Main results

* `Stacks.DeRhamWeil.subsingleton_piece_of_ne_zero`: `H^n_{dR}(X/k) = 0` for `n ≠ 0`.
* `Stacks.DeRhamWeil.bijective_smul_oneClass`: `k ⟶ H^0_{dR}(X/k)`, `c ↦ c · 1`, is bijective.
* `Stacks.DeRhamWeil.bijective_algebraMap_of_isIso`: **`H^*_{dR}(X/k) = k`**, i.e. the structure
  map `k ⟶ H^*_{dR}(X/k)` is bijective.

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.DerivedGlobalCupProduct (sectionsComplex globalClass)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.DeRhamWeil

/-- The scalars `f^{-1}𝒪_S` act on the degree-zero term `Ω⁰_{X/S}` of the de Rham complex through
the structure map `f^{-1}𝒪_S ⟶ 𝒪_X`. -/
theorem deRhamComplexNat_X_zero_smul {X S : Scheme.{u}} (p : X ⟶ S) (U : (X.Opens)ᵒᵖ)
    (a : (structureSheafRing (inverseImageBase p)).obj.obj U)
    (ω : ((deRhamComplexNat p).X 0).val.obj U) :
    a • ω = (show X.sheaf.obj.obj U from ((inverseImageStructureMap p).hom.app U).hom a) •
      (show ((Scheme.Hom.deRhamAlgebras p).exterior.piece 0).val.obj U from ω) :=
  rfl

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  [IsIso X.obj.hom]

/-- A scheme isomorphic over `k` to `Spec k` has a single point. -/
theorem subsingleton_of_isIso : Subsingleton ((toScheme k).obj X) :=
  (Scheme.homeoOfIso (asIso X.obj.hom)).injective.subsingleton

/-- `H^n_{dR}(X/k) = 0` for `n ≠ 0` when `X ≅ Spec k`. -/
theorem subsingleton_piece_of_ne_zero (n : ℤ) (hn : n ≠ 0) : Subsingleton (piece X n) := by
  have := (isProjective X).isProper
  change Subsingleton (Scheme.Hom.deRhamCohomologyBaseModule X.obj.hom n)
  refine ModuleCat.subsingleton_of_isZero ?_
  rcases lt_or_gt_of_ne hn with h | h
  · exact Scheme.Hom.isZero_deRhamCohomologyBaseModule_of_neg X.obj.hom n h
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
    have := subsingleton_of_isIso X
    have : Finite ((toScheme k).obj X) := Finite.of_subsingleton
    have := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper X.obj.hom
    have hΩ : ∀ m : ℕ, 0 < m → IsZero (Scheme.Hom.relativeDifferentialForms X.obj.hom (m : ℤ)) :=
      fun m hm => Scheme.Hom.isZero_relativeDifferentialForms_of_lt _ 0 _
        (by exact_mod_cast hm)
    have hdim : topologicalKrullDim ((toScheme k).obj X) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_zero_of_discreteTopology _
    exact Scheme.Hom.isZero_deRhamCohomologyBaseModule_of_isZero X.obj.hom hΩ q
      (Stacks.Cech.Hypercohomology.isZero_hypercohomology_singlePlus_zero_of_lt _ _ hdim
        (by exact_mod_cast h))

/-- `c ∈ k` as a global section of the base ring sheaf of the de Rham complex of `X ⟶ Spec k`. -/
abbrev cohScalar (c : k) : Stacks.Cohomology.GlobalKunneth.baseRing (inverseImageBase X.obj.hom) :=
  scalarHom X.obj.hom c

/-- The global section `1` of `Ω⁰_{X/k}`, as a cocycle of the global sections of the de Rham
complex. -/
abbrev oneCycleZero :
    (sectionsComplex (inverseImageBase X.obj.hom) (deRhamComplexInt X.obj.hom)).cycles 0 :=
  AlgebraicGeometry.SheafOfModules.deRhamOneCycle (algebras X) (differential X)

/-- The image of `c ∈ k` in `Γ(X, 𝒪_X)`. -/
abbrev formScalar (c : k) : X.obj.left.sheaf.obj.obj (op ⊤) :=
  (X.obj.hom.app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)

omit [IsIso X.obj.hom] in
/-- The unit of `H⁰_{dR}(X/k)` multiplied by `c ∈ k` is the class of the cocycle `c · 1`. -/
theorem smul_oneClass_eq_globalClass (c : k) :
    c • AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras X) (differential X) =
      globalClass (deRhamComplexInt X.obj.hom) 0 (cohScalar X c • oneCycleZero X) := by
  rw [smul_piece_def, AlgebraicGeometry.SheafOfModules.deRhamOneClass_eq_globalClass_one]
  exact (Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_smul (inverseImageBase X.obj.hom)
    (deRhamComplexInt X.obj.hom) 0 (cohScalar X c) (oneCycleZero X)).symm

omit [IsIso X.obj.hom] in
/-- The degree-zero form `c · 1` read through the degree-zero term of the extended de Rham
complex. -/
theorem extendXIso_hom_iCycles_smul_oneCycle (c : k) :
    ((deRhamComplexNat X.obj.hom).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom.val.app
        (op ⊤) ((sectionsComplex (inverseImageBase X.obj.hom)
          (deRhamComplexInt X.obj.hom)).iCycles 0 (cohScalar X c • oneCycleZero X)) =
      formScalar X c • (Scheme.Hom.deRhamAlgebras X.obj.hom).exterior.one.eval (op ⊤) := by
  let E := (deRhamComplexNat X.obj.hom).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  have h2 : E.hom.val.app (op ⊤)
      ((sectionsComplex (inverseImageBase X.obj.hom) (deRhamComplexInt X.obj.hom)).iCycles 0
        (oneCycleZero X)) =
      (Scheme.Hom.deRhamAlgebras X.obj.hom).exterior.one.eval (op ⊤) :=
    eq_of_heq ((extendXIso_hom_val_app_heq _ 0 (op ⊤) _).trans
      ((heq_of_eq (AlgebraicGeometry.SheafOfModules.iCycles_deRhamOneCycle (algebras X)
        (differential X))).trans
      (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ (op ⊤))))
  have h3 : ((inverseImageStructureMap X.obj.hom).hom.app (op ⊤)).hom (cohScalar X c) =
      formScalar X c :=
    congrArg (fun g => g.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))
      (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app X.obj.hom)
  rw [map_smul]
  refine (map_smul (E.hom.val.app (op ⊤)).hom (cohScalar X c) _).trans ?_
  rw [h2]
  refine (deRhamComplexNat_X_zero_smul X.obj.hom (op ⊤) (cohScalar X c) _).trans ?_
  exact congrArg (· • (Scheme.Hom.deRhamAlgebras X.obj.hom).exterior.one.eval (op ⊤)) h3

/-- **`H⁰_{dR}(X/k) = k`** for `X ≅ Spec k`: `c ↦ c · 1` is bijective. -/
theorem bijective_smul_oneClass :
    Function.Bijective (fun c : k =>
      c • AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras X) (differential X)) := by
  have := (isProjective X).isProper
  let E := (deRhamComplexNat X.obj.hom).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  let eE := Equiv.ofBijective _ (bijective_iso_hom_val_app E (op ⊤))
  let eC := Equiv.ofBijective _ (bijective_iCycles_zero X.obj.hom)
  have h1 : Function.Bijective (formScalar X) :=
    (ConcreteCategory.bijective_of_isIso (X.obj.hom.app ⊤)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)
  have e : (fun c : k =>
      c • AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras X) (differential X)) =
      globalClass (deRhamComplexInt X.obj.hom) 0 ∘ eC.symm ∘ eE.symm ∘
        (fun r : X.obj.left.sheaf.obj.obj (op ⊤) =>
          r • (Scheme.Hom.deRhamAlgebras X.obj.hom).exterior.one.eval (op ⊤)) ∘ formScalar X := by
    funext c
    simp only [Function.comp_apply]
    rw [smul_oneClass_eq_globalClass]
    congr 1
    apply eC.injective
    rw [Equiv.apply_symm_apply]
    apply eE.injective
    change _ = eE (eE.symm ((fun r : X.obj.left.sheaf.obj.obj (op ⊤) =>
      r • (Scheme.Hom.deRhamAlgebras X.obj.hom).exterior.one.eval (op ⊤)) (formScalar X c)))
    exact (extendXIso_hom_iCycles_smul_oneCycle X c).trans (eE.apply_symm_apply _).symm
  rw [e]
  exact (bijective_globalClass_zero X.obj.hom).comp (eC.symm.bijective.comp
    (eE.symm.bijective.comp ((bijective_smul_one_formsZero X.obj.hom (op ⊤)).comp h1)))

/-- **`H^*_{dR}(X/k) = k`** for a smooth projective `k`-scheme `X` whose structure morphism is an
isomorphism, for instance `Spec k` itself: the structure map `k ⟶ H^*_{dR}(X/k)` is bijective. This
is the first half of axiom (A5) of Section 0FID for de Rham cohomology (Section 0FWC). -/
theorem bijective_algebraMap_of_isIso :
    Function.Bijective (Algebra.linearMap k (cohomology X)) := by
  have happ : ∀ c : k, Algebra.linearMap k (cohomology X) c =
      DirectSum.of (piece X) 0
        (c • AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras X) (differential X)) :=
    fun c => DirectSum.algebraMap_apply _ _ c
  refine ⟨fun c d hcd => ?_, fun a => ?_⟩
  · rw [happ, happ] at hcd
    exact (bijective_smul_oneClass X).1 (DirectSum.of_injective 0 hcd)
  · obtain ⟨c, hc⟩ := (bijective_smul_oneClass X).2 (a 0)
    refine ⟨c, ?_⟩
    rw [happ]
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using hc
    · rw [(subsingleton_piece_of_ne_zero X n hn).elim (a n) 0, DirectSum.of_eq_of_ne 0 n _ hn]

end Stacks.DeRhamWeil

end
