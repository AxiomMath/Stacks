module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticColocalizationTriangle
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFppfModulesSerre
public import StacksFrontier.Algebra.Homology.DerivedCategory.KernelColocalization

/-!
# Splitting off the parasitic part of `D_𝓛(𝒪_𝒳)`, for a weak Serre class `𝓛`

Let `𝒳` be an algebraic stack, let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the morphism of
ringed topoi of **Stacks 0788** (2), and let `𝓛` be a weak Serre subcategory of `Mod(𝒪_𝒳)`.
This file develops, for `D_𝓛(𝒪_𝒳)` and its subcategory `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`, the
constructions and results which the source states for `𝓛 = LQCoh^fbc(𝒪_𝒳)`:

* the Verdier quotient `D_𝓛(𝒪_𝒳) / D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`, which for `𝓛 = LQCoh^fbc(𝒪_𝒳)` is
  `D_QCoh(𝒪_𝒳)` of **Stacks 07B6**;
* the canonical triangle `Lg_! g^* K ⟶ K ⟶ P ⟶` of **Stacks 07BA**, whose first term is left
  orthogonal to `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)` and whose third term lies in it, for every `K` in
  `D_𝓛(𝒪_𝒳)`, given a left adjoint `Lg_!` of `g^*` with `g^* Lg_! = id` and `Lg_! g^*`
  preserving `D_𝓛(𝒪_𝒳)`;
* the assertions of **Stacks 0H11** that follow by [Stacks, Tag 0H0P]: the parasitic part is
  left admissible, its left orthogonal `𝒜` is right admissible, and `𝒜` maps isomorphically
  onto the Verdier quotient, `𝒜` being a strictly full saturated triangulated subcategory both
  of `D_𝓛(𝒪_𝒳)` and of `D(𝒳_{fppf}, 𝒪_𝒳)`.

## Main definitions

In the namespace `AlgebraicGeometry.Stack.ParasiticQuotient`:

* `derivedParasitic 𝓛`: the subcategory `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)` of `D(𝒳_{fppf}, 𝒪_𝒳)`.
* `parasiticIn 𝓛` and `parasiticFreeIn 𝓛`: the parasitic part of `D_𝓛(𝒪_𝒳)` and its left
  orthogonal `𝒜`, as subcategories of `D_𝓛(𝒪_𝒳)`.
* `parasiticFree 𝓛`: the subcategory `𝒜` read inside `D(𝒳_{fppf}, 𝒪_𝒳)`.
* `quotientW 𝓛`, `quotient 𝓛` and `toQuotient 𝓛`: the class of morphisms of `D_𝓛(𝒪_𝒳)` with
  cone in `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`, the Verdier quotient, and the quotient functor.

## Main results

* `quotientW_eq_trW`: the inverted class is the class attached to the parasitic part of
  `D_𝓛(𝒪_𝒳)`, so the quotient is the Verdier quotient by that subcategory.
* `derivedParasitic_obj₃_of_distTriang` and `leftOrthogonal_parasiticFreePart`: the two halves
  of **Stacks 07BA** for `𝓛`, and `extensionProduct_eq_top` the resulting semiorthogonal
  decomposition of `D_𝓛(𝒪_𝒳)`.
* `isLeftAdmissible_parasiticIn`, `isRightAdmissible_parasiticFreeIn`,
  `isEquivalence_parasiticFreeIn_ι_comp`, `isSaturated_parasiticFreeIn`,
  `isSaturated_parasiticFree`, `isEquivalence_parasiticFreeToClass_comp`: the assertions of
  **Stacks 0H11** for `𝓛`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 0CQP](https://stacks.math.columbia.edu/tag/0CQP)
* [Stacks Project, Tag 0H0P](https://stacks.math.columbia.edu/tag/0H0P)
* [Stacks Project, Tag 0H11](https://stacks.math.columbia.edu/tag/0H11)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty DerivedCategory.KernelColocalization

namespace AlgebraicGeometry.Stack.ParasiticQuotient

universe u w t t'

open FlatFppf in
attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  (𝓛 : ObjectProperty (fppfModules B S hS 𝒳))

/-! ### The parasitic part, its left orthogonal and the Verdier quotient -/

/-- The parasitic modules of **Stacks 0773** on the fppf site, as a class of objects of
`AlgebraicGeometry.Stack.fppfModules`. -/
abbrev parasitic : ObjectProperty (fppfModules B S hS 𝒳) :=
  parasiticModules.{u, w, u} B S hS 𝒳 .fppf

/-- The subcategory `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)` of `D(𝒳_{fppf}, 𝒪_𝒳)`: the complexes all of whose
cohomology modules are parasitic and lie in `𝓛`. -/
abbrev derivedParasitic : ObjectProperty (DerivedCategory (fppfModules B S hS 𝒳)) :=
  derivedInter (parasitic B S hS 𝒳) 𝓛

/-- The parasitic part of `D_𝓛(𝒪_𝒳)`, as a subcategory of `D_𝓛(𝒪_𝒳)`. -/
abbrev parasiticIn : ObjectProperty (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  interIn (parasitic B S hS 𝒳) 𝓛

/-- The left orthogonal `𝒜` of the parasitic part inside `D_𝓛(𝒪_𝒳)`. -/
abbrev parasiticFreeIn : ObjectProperty (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  interLeftOrthogonalIn (parasitic B S hS 𝒳) 𝓛

/-- The subcategory `𝒜` read inside `D(𝒳_{fppf}, 𝒪_𝒳)`: the complexes with cohomology in `𝓛`
admitting no nonzero morphism to `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`. -/
abbrev parasiticFree : ObjectProperty (DerivedCategory (fppfModules B S hS 𝒳)) :=
  interLeftOrthogonal (parasitic B S hS 𝒳) 𝓛

/-- The class of morphisms of `D_𝓛(𝒪_𝒳)` whose cone lies in `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`. -/
abbrev quotientW : MorphismProperty (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  DerivedCategory.KernelColocalization.quotientW (parasitic B S hS 𝒳) 𝓛

/-- The Verdier quotient `D_𝓛(𝒪_𝒳) / D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`. For `𝓛 = LQCoh^fbc(𝒪_𝒳)` this is
`D_QCoh(𝒪_𝒳)` of **Stacks 07B6**. -/
abbrev quotient := DerivedCategory.KernelColocalization.quotient (parasitic B S hS 𝒳) 𝓛

/-- The quotient functor `D_𝓛(𝒪_𝒳) ⥤ D_𝓛(𝒪_𝒳) / D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`. -/
abbrev toQuotient : (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory ⥤ quotient B S hS 𝒳 𝓛 :=
  DerivedCategory.KernelColocalization.toQuotient (parasitic B S hS 𝒳) 𝓛

/-- The inclusion `𝒜 ⟶ D_𝓛(𝒪_𝒳)`, with `𝒜` presented as a subcategory of
`D(𝒳_{fppf}, 𝒪_𝒳)`. -/
abbrev parasiticFreeToClass :
    (parasiticFree B S hS 𝒳 𝓛).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  interLeftOrthogonalToClass (parasitic B S hS 𝒳) 𝓛

section WeakSerre

variable [𝓛.IsWeakSerreClass]

/-- The quotient is the Verdier quotient by the parasitic part of `D_𝓛(𝒪_𝒳)`. -/
theorem quotientW_eq_trW : quotientW B S hS 𝒳 𝓛 = (parasiticIn B S hS 𝒳 𝓛).trW :=
  DerivedCategory.KernelColocalization.quotientW_eq_trW _ _

/-! ### Stacks 07BA for `𝓛` -/

variable [HasDerivedCategory.{t'} (FlatFppf.flatFppfModules B S hS 𝒳)]
  (Lsh : DerivedCategory (FlatFppf.flatFppfModules B S hS 𝒳) ⥤
    DerivedCategory (fppfModules B S hS 𝒳))
  (adj : Lsh ⊣ FlatFppf.derivedModuleRestriction B S hS 𝒳)

/-- Restriction `g^*` to the flat-fppf site commutes with the shift. -/
instance commShift_derivedModuleRestriction :
    (FlatFppf.derivedModuleRestriction B S hS 𝒳).CommShift ℤ :=
  inferInstanceAs ((FlatFppf.moduleRestriction B S hS 𝒳).mapDerivedCategory.CommShift ℤ)

/-- Restriction `g^*` to the flat-fppf site is a triangulated functor. -/
instance isTriangulated_derivedModuleRestriction :
    (FlatFppf.derivedModuleRestriction B S hS 𝒳).IsTriangulated :=
  inferInstanceAs (FlatFppf.moduleRestriction B S hS 𝒳).mapDerivedCategory.IsTriangulated

/-- **Stacks 07B9** (2)(b): `g^* K = 0` exactly when all cohomology modules of `K` are
parasitic. -/
lemma isZero_derivedModuleRestriction_iff (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    IsZero ((FlatFppf.derivedModuleRestriction B S hS 𝒳).obj K) ↔
      ∀ n : ℤ, parasitic B S hS 𝒳 ((DerivedCategory.homologyFunctor _ n).obj K) :=
  FlatFppf.isZero_derivedModuleRestriction_iff_forall_isParasitic B S hS 𝒳 K

omit [𝓛.IsWeakSerreClass] in
include adj in
/-- **Stacks 07BA** for `𝓛`, the orthogonality: `Hom(Lg_! g^* K, P') = 0` for `P'` in
`D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`. -/
theorem leftOrthogonal_parasiticFreePart (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    (derivedParasitic B S hS 𝒳 𝓛).leftOrthogonal (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K) :=
  leftOrthogonal_obj_counit _ 𝓛 adj (isZero_derivedModuleRestriction_iff B S hS 𝒳) K

/-- **Stacks 07BA** for `𝓛`, the cone: if `K` and `Lg_! g^* K` lie in `D_𝓛(𝒪_𝒳)`, every cone on
the counit `Lg_! g^* K ⟶ K` lies in `D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`. -/
theorem derivedParasitic_obj₃_of_distTriang (hunit : IsIso adj.unit)
    (K : DerivedCategory (fppfModules B S hS 𝒳)) (hK : DerivedCategoryB.derivedCategoryB 𝓛 K)
    (hK' : DerivedCategoryB.derivedCategoryB 𝓛 (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K))
    (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
    (c : P ⟶ (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (FlatFppf.parasiticFreePartHom B S hS 𝒳 Lsh adj K) b c ∈
      distTriang (DerivedCategory (fppfModules B S hS 𝒳))) :
    derivedParasitic B S hS 𝒳 𝓛 P :=
  derivedInter_obj₃_of_distTriang _ 𝓛 adj (isZero_derivedModuleRestriction_iff B S hS 𝒳) hunit
    K hK hK' P b c hT

/-- **Stacks 07BA** for `𝓛`, as a semiorthogonal decomposition of `D_𝓛(𝒪_𝒳)`: every object is an
extension of a parasitic object by an object of `𝒜`, the extension being the canonical one on
`Lg_! g^* K ⟶ K`, provided `Lg_! g^*` preserves `D_𝓛(𝒪_𝒳)`. -/
theorem extensionProduct_eq_top (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    (parasiticFreeIn B S hS 𝒳 𝓛).extensionProduct (parasiticIn B S hS 𝒳 𝓛) = ⊤ :=
  DerivedCategory.KernelColocalization.extensionProduct_eq_top _ 𝓛 adj
    (isZero_derivedModuleRestriction_iff B S hS 𝒳) hunit hshriek

/-! ### Stacks 0H11 for `𝓛` -/

/-- **Stacks 0H11** for `𝓛`, first assertion: the parasitic part of `D_𝓛(𝒪_𝒳)` is left
admissible. -/
theorem isLeftAdmissible_parasiticIn (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    (parasiticIn B S hS 𝒳 𝓛).IsLeftAdmissible :=
  isLeftAdmissible_interIn _ 𝓛 adj (isZero_derivedModuleRestriction_iff B S hS 𝒳) hunit hshriek

/-- **Stacks 0H11** for `𝓛`, second assertion: the left orthogonal `𝒜` of the parasitic part is
right admissible in `D_𝓛(𝒪_𝒳)`, and the parasitic part is the right orthogonal of `𝒜`. -/
theorem isRightAdmissible_parasiticFreeIn (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    (parasiticFreeIn B S hS 𝒳 𝓛).IsRightAdmissible ∧
      parasiticIn B S hS 𝒳 𝓛 = (parasiticFreeIn B S hS 𝒳 𝓛).rightOrthogonal :=
  isRightAdmissible_interLeftOrthogonalIn _ 𝓛 adj (isZero_derivedModuleRestriction_iff B S hS 𝒳)
    hunit hshriek

/-- **Stacks 0H11** for `𝓛`, third assertion: `𝒜 ⟶ D_𝓛(𝒪_𝒳) ⟶ D_𝓛(𝒪_𝒳) / D_{Parasitic ∩ 𝓛}(𝒪_𝒳)`
is an equivalence. -/
theorem isEquivalence_parasiticFreeIn_ι_comp (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    ((parasiticFreeIn B S hS 𝒳 𝓛).ι ⋙ toQuotient B S hS 𝒳 𝓛).IsEquivalence :=
  isEquivalence_interLeftOrthogonalIn_ι_comp _ 𝓛 adj
    (isZero_derivedModuleRestriction_iff B S hS 𝒳) hunit hshriek

/-- **Stacks 0H11** for `𝓛`, last assertion inside `D_𝓛(𝒪_𝒳)`: `𝒜` is a strictly full saturated
triangulated subcategory. -/
theorem isSaturated_parasiticFreeIn (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    (parasiticFreeIn B S hS 𝒳 𝓛).IsClosedUnderIsomorphisms ∧
      (parasiticFreeIn B S hS 𝒳 𝓛).IsSaturated ∧
      (parasiticFreeIn B S hS 𝒳 𝓛).IsTriangulated :=
  isSaturated_interLeftOrthogonalIn _ 𝓛 adj (isZero_derivedModuleRestriction_iff B S hS 𝒳) hunit
    hshriek

omit [HasDerivedCategory.{t'} (FlatFppf.flatFppfModules B S hS 𝒳)] in
/-- **Stacks 0H11** for `𝓛`, last assertion inside `D(𝒳_{fppf}, 𝒪_𝒳)`: `𝒜` read there is a
strictly full saturated triangulated subcategory. -/
theorem isSaturated_parasiticFree :
    (parasiticFree B S hS 𝒳 𝓛).IsClosedUnderIsomorphisms ∧
      (parasiticFree B S hS 𝒳 𝓛).IsSaturated ∧ (parasiticFree B S hS 𝒳 𝓛).IsTriangulated :=
  isSaturated_interLeftOrthogonal _ 𝓛

/-- **Stacks 0H11** for `𝓛`, the identification inside `D(𝒳_{fppf}, 𝒪_𝒳)`: with `𝒜` presented
as a subcategory of `D(𝒳_{fppf}, 𝒪_𝒳)`, the composition with the quotient functor is still an
equivalence. -/
theorem isEquivalence_parasiticFreeToClass_comp (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (FlatFppf.parasiticFreePart B S hS 𝒳 Lsh K)) :
    (parasiticFreeToClass B S hS 𝒳 𝓛 ⋙ toQuotient B S hS 𝒳 𝓛).IsEquivalence :=
  isEquivalence_interLeftOrthogonalToClass_comp _ 𝓛 adj
    (isZero_derivedModuleRestriction_iff B S hS 𝒳) hunit hshriek

end WeakSerre

end AlgebraicGeometry.Stack.ParasiticQuotient
