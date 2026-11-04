module

public import Mathlib.CategoryTheory.Limits.MonoCoprod
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementClauses

/-!
# Extension by zero of objects supported over the closed complement of a square

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S` and set `T = |X| \ |U|`.  The parts of Stacks 08GG that concern extension by zero `j_!`
hold:

* clause (1)(b): for `E` in `D(𝒪_X)` supported on `T` the counit `j_!(E|_V) ⟶ E` is an
  isomorphism;
* clause (2)(a): for `F` in `D(𝒪_V)` supported on `j⁻¹T` the unit `F ⟶ (j_!F)|_V` is an
  isomorphism.

Extension by zero along an étale morphism is conservative, and being exact it reflects
isomorphisms, on modules and on the derived category.

## Main results

* `CategoryTheory.Functor.reflectsIsomorphisms_of_isZero_of_exact`: an exact functor of abelian
  categories detecting zero objects reflects isomorphisms.
* `AlgebraicGeometry.Space.isIso_of_isIso_mapDerivedCategory_etaleModuleLowerShriek`: extension
  by zero along an étale morphism reflects isomorphisms of the derived category.
* `AlgebraicGeometry.Space.isIso_derivedCounit_edsEtale_of_cohomologySupportedOn`: Stacks 08GG,
  clause (1)(b).
* `AlgebraicGeometry.Space.isIso_derivedUnit_edsEtale_of_cohomologySupportedOn`: Stacks 08GG,
  clause (2)(a).

## References

* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- **An exact functor of abelian categories which detects zero objects reflects
isomorphisms.** -/
theorem reflectsIsomorphisms_of_isZero_of_exact (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ X : C, IsZero (F.obj X) → IsZero X) : F.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    have hker : IsZero (Limits.kernel f) := hF _ (IsZero.of_iso
      (isZero_kernel_of_mono (F.map f)) (PreservesKernel.iso F f))
    have hcok : IsZero (Limits.cokernel f) := hF _ (IsZero.of_iso
      (isZero_cokernel_of_epi (F.map f)) (PreservesCokernel.iso F f))
    have : Mono f := Preadditive.mono_of_isZero_kernel' _ (kernelIsKernel f) hker
    have : Epi f := Preadditive.epi_of_isZero_cokernel' _ (cokernelIsCokernel f) hcok
    exact isIso_of_mono_of_epi f

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Extension by zero along an étale morphism is conservative -/

section Conservative

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- **Extension by zero along an étale morphism reflects isomorphisms of modules.** -/
instance etaleModuleLowerShriek_reflectsIsomorphisms :
    (etaleModuleLowerShriek B S hS f hf).ReflectsIsomorphisms :=
  Functor.reflectsIsomorphisms_of_isZero_of_exact _
    (isZero_of_isZero_etaleModuleLowerShriek B S hS f hf)

/-- **Extension by zero along an étale morphism reflects isomorphisms of the derived
category.** -/
theorem isIso_of_isIso_mapDerivedCategory_etaleModuleLowerShriek
    {K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (φ : K ⟶ L)
    (h : IsIso ((etaleModuleLowerShriek B S hS f hf).mapDerivedCategory.map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have := ((etaleModuleLowerShriek B S hS f hf).isIso_mapDerivedCategory_map_iff φ).1 h n
  exact isIso_of_reflects_iso _ (etaleModuleLowerShriek B S hS f hf)

end Conservative

/-! ### Stacks 08GG, clauses (1)(b) and (2)(a) -/

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- Extension by zero along the étale morphism `j : V ⟶ X` of an elementary distinguished
square, with its adjunction to restriction. -/
abbrev edsEtaleShriekAdjunction :=
  etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`.  For `E` in `D(𝒪_X)` supported on `T`, the counit
`j_!(E|_V) ⟶ E` is an isomorphism. -/
@[stacks 08GG "clause (1)(b): the derived counit j_!(E|_V) ⟶ E is an isomorphism for E in D(O_X)
supported on T = |X| \\ |U|, unconditionally"]
theorem isIso_derivedCounit_edsEtale_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    IsIso ((NatTrans.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq).counit).app E) := by
  let adjU := etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  let adjP := etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq)
  exact isIso_counit_mapDerivedCategory_of_cohomologySupportedOn B S hS hsq adjU
    (edsEtaleShriekAdjunction B S hS hsq)
    (edsShriekOpenComparison B S hS hsq adjU adjP)
    (edsShriekEtaleComparison B S hS hsq (edsEtaleShriekAdjunction B S hS hsq) adjP)
    (fun F => zero_edsShriekMayerVietoris B S hS hsq adjU (edsEtaleShriekAdjunction B S hS hsq)
      adjP F)
    (fun F => shortExact_edsShriekMayerVietoris B S hS hsq adjU
      (edsEtaleShriekAdjunction B S hS hsq) adjP F)
    E hE (fun hE' _ g hg hrange =>
      isZero_etaleModulePullback_mapDerivedCategory_of_range_subset B S hS g hg E hE' hrange)

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`.  For `F` in `D(𝒪_V)` supported on `j⁻¹T`, the unit
`F ⟶ (j_!F)|_V` is an isomorphism. -/
@[stacks 08GG "clause (2)(a): the unit F ⟶ (j_!F)|_V is an isomorphism for F in D(O_V) supported
on j^{-1}T, unconditionally"]
theorem isIso_derivedUnit_edsEtale_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso ((Adjunction.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq)).unit.app F) := by
  let adj := edsEtaleShriekAdjunction B S hS hsq
  let L := (etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
  have hc := isIso_derivedCounit_edsEtale_of_cohomologySupportedOn B S hS hsq (L.obj F)
    (cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn B S hS hsq F hF)
  have hc' : IsIso ((Adjunction.mapDerivedCategory adj).counit.app (L.obj F)) := by
    rw [← Adjunction.mapDerivedCategory_counit_eq adj]
    simp only [NatTrans.comp_app]
    infer_instance
  have hL : IsIso (L.map ((Adjunction.mapDerivedCategory adj).unit.app F)) := by
    rw [IsIso.eq_inv_of_inv_hom_id
      ((Adjunction.mapDerivedCategory adj).left_triangle_components F)]
    infer_instance
  exact isIso_of_isIso_mapDerivedCategory_etaleModuleLowerShriek B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) _ hL

end Square

end AlgebraicGeometry.Space

end
