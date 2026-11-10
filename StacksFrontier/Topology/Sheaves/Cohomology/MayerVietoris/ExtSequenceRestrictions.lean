module

public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The maps of the Mayer--Vietoris Ext sequence are the restrictions

Let `X` be a ringed space which is the union of two open subspaces `U` and `V`, and let `E`,
`F` be objects of `D(𝒪_X)`. Stacks 08BW is the Mayer--Vietoris long exact sequence

`⋯ ⟶ Ext^{n-1}(E|_{U∩V}, F|_{U∩V}) ⟶ Ext^n(E, F) ⟶
  Ext^n(E|_U, F|_U) × Ext^n(E|_V, F|_V) ⟶ Ext^n(E|_{U∩V}, F|_{U∩V}) ⟶ ⋯`

whose maps, in the source, are the restrictions to the relevant opens. The exactness is
`Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence`, which quantifies over its
three maps without saying what they are. This file says what they are.

## Main definitions

* `CategoryTheory.Adjunction`-level: `Stacks.ExtensionByZero.adjShiftedHomEquiv`, the
  identification `Hom(L(R E), F⟦n⟧) ≃ Ext^n(R E, R F)` attached to an adjunction `L ⊣ R`.
* `Stacks.ExtensionByZero.derivedJShriekRestrictionAdjunction`: Stacks 08BT as an adjunction
  `D(j_!) ⊣ D(j^*)` of the functors induced on the unbounded derived categories.
* `Stacks.ExtensionByZero.extensionRestrictionShiftedHomEquiv`: the identification
  `Ext^n_X(j_{U!}(E|_U), F) ≃ Ext^n_U(E|_U, F|_U)` it gives.
* `Stacks.ExtensionByZero.mvRestriction`, `Stacks.ExtensionByZero.mvToOverlap`,
  `Stacks.ExtensionByZero.mvDifference` and `Stacks.ExtensionByZero.mvBoundary`: the four maps
  of the Mayer--Vietoris sequence, read through that identification.

## Main results

* `Stacks.ExtensionByZero.derivedExtensionRestrictionCanonicalCounit_eq`: **the canonical
  derived counit `R(j_!j^*) ⟶ ᵀ` used by the extension-by-zero triangle of Stacks 08BU is the
  counit of the derived adjunction of Stacks 08BT.**
* `Stacks.ExtensionByZero.mvRestriction_apply`: the first map of the sequence is the pair of
  the two restrictions.
* `Stacks.ExtensionByZero.mvToOverlap_restriction`: a comparison of extension-by-zero functors
  which factors the counit of the smaller open through the counit of the larger one induces,
  on Ext groups, the restriction map from the larger open to the smaller.
* `Stacks.ExtensionByZero.mvDifference_apply`: the second map of the sequence is the
  difference of the two maps of the previous item.
* `Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence_restrictions`:
  **Stacks 08BW** with all of that in the statement.

## Implementation notes

The three derived functors of extension-by-zero-of-the-restriction are not constructed here
and need no K-injective resolutions: `j^*` and `j_!` are exact, so the functors they induce
degreewise on the homotopy categories already invert quasi-isomorphisms, and
`Stacks.ExtensionByZero.derivedExtensionRestriction` -- with the structure map
`Stacks.ExtensionByZero.derivedExtensionRestrictionFactorsh` -- is a right derived functor
along `HomotopyCategory.quasiIso` for that reason alone. The content of this file is the
second half: identifying the counit that the triangle of Stacks 08BU is built from.

That identification is `CategoryTheory.Functor.rightDerived_ext`: both the counit of Stacks
08BU and the counit of the derived adjunction factor the degreewise counit through the
structure map, so they agree. The derived adjunction is obtained by localizing the degreewise
adjunction `j_! ⊣ j^*` twice -- once to the homotopy categories
(`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction`) and once along
`DerivedCategory.Qh` (`CategoryTheory.Adjunction.localization`) -- and
`CategoryTheory.Adjunction.localization_counit_app` describes its counit at an object of the
homotopy category, which is exactly the factorization needed.

The adjunction and the identification it gives are marked `local irreducible` past that
point. Both are localizations, and a `rw` or an `exact` that unfolds either exhausts the
heartbeat budget; the two crossings where the localization of the comparison
`Functor.mapHomotopyCategoryCompIso` has to be seen as an identity are paid in term mode,
where the conversion check runs at default transparency. For the same reason the small
computations below (`mvToOverlap_neg`, `mvDifference_apply`, `mvToOverlap_restriction`) are
written as `Eq.trans` chains rather than as `rw` chains: `rw` has to re-check its motive at a
lower transparency, and on these morphism groups that does not terminate.

The maps from `U` and from `V` to the overlap are *not* produced from a restriction-of-a-
restriction functor, which would need the two spellings `ExtensionByZeroModules.resRing (U ⊓ V)`
and `resRing` of an open of `U` to be identified. They are produced from the comparison maps
of the Mayer--Vietoris triangle of Stacks 08BU, and `mvToOverlap_restriction` is what says
that such a comparison really does restrict: it carries the restriction of `x` to `U` to the
restriction of `x` to `U ∩ V`. The Mayer--Vietoris sign of the second comparison is absorbed by
negating it, so that both induced maps are restriction maps and the second map of the sequence
is literally their difference.

## References

* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules

universe u

namespace Stacks.ExtensionByZero

attribute [local instance] HasDerivedCategory.standard jShriek_additive

/-! ### Shifted morphism groups across an adjunction -/

section Generic

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasShift A ℤ] [HasShift B ℤ]

/-- An adjunction `L ⊣ R` identifies the morphisms from `L (R E)` into the `n`-th shift of `F`
with the shifted morphisms from `R E` to `R F`. -/
def adjShiftedHomEquiv (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    [L.Additive] [R.CommShift ℤ] (E F : B) (n : ℤ) :
    (L.obj (R.obj E) ⟶ F⟦n⟧) ≃+ ShiftedHom (R.obj E) (R.obj F) n where
  toFun x := adj.homAddEquiv (R.obj E) (F⟦n⟧) x ≫ (R.commShiftIso n).hom.app F
  invFun x := (adj.homAddEquiv (R.obj E) (F⟦n⟧)).symm
    (x ≫ (R.commShiftIso n).inv.app F)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [Preadditive.add_comp]

/-- Across the identification, precomposition with the counit is the action of the right
adjoint on shifted morphisms: it is restriction. -/
theorem adjShiftedHomEquiv_counit (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    [L.Additive] [R.CommShift ℤ] (E F : B) (n : ℤ) (x : ShiftedHom E F n) :
    adjShiftedHomEquiv L R adj E F n (adj.counit.app E ≫ x) = x.map R := by
  simp [adjShiftedHomEquiv, ShiftedHom.map, adj.homEquiv_unit, Category.assoc]

end Generic

/-! ### Stacks 08BT as an adjunction of the derived functors -/

section Adjunction

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- Extension by zero from `U` preserves finite limits. -/
local instance jShriekPFL : PreservesFiniteLimits (jShriek U O) :=
  (jShriek_additive_and_exact O U).2.1

/-- Extension by zero from `U` preserves finite colimits. -/
local instance jShriekPFC : PreservesFiniteColimits (jShriek U O) :=
  (jShriek_additive_and_exact O U).2.2

/-- Restriction to `U` preserves finite limits. -/
local instance jStarPFL : PreservesFiniteLimits (jStar U O) :=
  (jStar_additive_and_exact O U).2.1

/-- Restriction to `U` preserves finite colimits. -/
local instance jStarPFC : PreservesFiniteColimits (jStar U O) :=
  (jStar_additive_and_exact O U).2.2

/-- The functor induced by extension by zero on homotopy categories commutes with the localization
functors to the derived categories. -/
local instance catCommSqJShriek :
    CatCommSq ((jShriek U O).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh (jShriek U O).mapDerivedCategory :=
  ⟨(jShriek U O).mapDerivedCategoryFactorsh.symm⟩

/-- The functor induced by restriction on homotopy categories commutes with the localization
functors to the derived categories. -/
local instance catCommSqJStar :
    CatCommSq ((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh (jStar U O).mapDerivedCategory :=
  ⟨(jStar U O).mapDerivedCategoryFactorsh.symm⟩

/-- **Stacks 08BT on the unbounded derived categories, as an adjunction.** Extension by zero
from an open subspace is left adjoint to restriction, degreewise; both functors are exact, so
the adjunction descends through the homotopy categories to the derived categories. -/
def derivedJShriekRestrictionAdjunction :
    (jShriek U O).mapDerivedCategory ⊣ derivedRestriction O U :=
  (Adjunction.mapHomotopyCategoryAdjunction (jShriekAdjunction U O)
      (ComplexShape.up ℤ)).localization
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U O)) (ComplexShape.up ℤ))
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) _ _

private lemma factorsh_hom_comp_homotopyCounit
    (K : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :
    (derivedExtensionRestrictionFactorsh O U).hom.app K ≫
        (homotopyExtensionRestrictionCounit O U).app K =
      (derivedJShriekRestrictionAdjunction O U).counit.app (DerivedCategory.Qh.obj K) := by
  have hf : (derivedExtensionRestrictionFactorsh O U).hom.app K =
      (jShriek U O).mapDerivedCategory.map
          ((jStar U O).mapDerivedCategoryFactorsh.hom.app K) ≫
        (jShriek U O).mapDerivedCategoryFactorsh.hom.app
            (((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (jStar U O ⋙ jShriek U O))
              (ComplexShape.up ℤ)).hom.app K) := by
    simp [derivedExtensionRestrictionFactorsh]
  have hc : (derivedJShriekRestrictionAdjunction O U).counit.app (DerivedCategory.Qh.obj K) =
      (jShriek U O).mapDerivedCategory.map
          ((jStar U O).mapDerivedCategoryFactorsh.hom.app K) ≫
        (jShriek U O).mapDerivedCategoryFactorsh.hom.app
            (((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Adjunction.mapHomotopyCategoryAdjunction (jShriekAdjunction U O)
              (ComplexShape.up ℤ)).counit.app K) :=
    Adjunction.localization_counit_app _ _ _ _ _ _ _ K
  have e1 : (NatTrans.mapHomotopyCategory (jShriekAdjunction U O).counit
          (ComplexShape.up ℤ)).app K ≫ (homotopyIdentityComparison O).app K =
      (Adjunction.mapHomotopyCategoryAdjunction (jShriekAdjunction U O)
        (ComplexShape.up ℤ)).counit.app K :=
    Category.comp_id _
  have e2 : (homotopyExtensionRestrictionCounit O U).app K =
      DerivedCategory.Qh.map
        ((Adjunction.mapHomotopyCategoryAdjunction (jShriekAdjunction U O)
          (ComplexShape.up ℤ)).counit.app K) :=
    congrArg DerivedCategory.Qh.map e1
  have hstep : DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (jStar U O ⋙ jShriek U O))
          (ComplexShape.up ℤ)).hom.app K) ≫
      (homotopyExtensionRestrictionCounit O U).app K =
    DerivedCategory.Qh.map
      ((Adjunction.mapHomotopyCategoryAdjunction (jShriekAdjunction U O)
        (ComplexShape.up ℤ)).counit.app K) :=
    (congrArg (fun t => DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (jStar U O ⋙ jShriek U O))
          (ComplexShape.up ℤ)).hom.app K) ≫ t) e2).trans
      ((CategoryTheory.Functor.map_comp DerivedCategory.Qh _ _).symm.trans
        (congrArg DerivedCategory.Qh.map (Category.id_comp _)))
  rw [hf, hc, Category.assoc, Category.assoc, hstep]

/-- **The canonical derived counit used by the extension-by-zero triangle of Stacks 08BU is
the counit of the derived adjunction of Stacks 08BT.** -/
theorem derivedExtensionRestrictionCanonicalCounit_eq :
    derivedExtensionRestrictionCanonicalCounit O U =
      (derivedJShriekRestrictionAdjunction O U).counit := by
  have h1 : (derivedExtensionRestrictionFactorsh O U).inv ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (derivedExtensionRestrictionCanonicalCounit O U) =
      homotopyExtensionRestrictionCounit O U :=
    Functor.rightDerived_fac (derivedExtensionRestriction O U)
      (derivedExtensionRestrictionFactorsh O U).inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) _ _
  have h2 : (derivedExtensionRestrictionFactorsh O U).inv ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (derivedJShriekRestrictionAdjunction O U).counit =
      homotopyExtensionRestrictionCounit O U := by
    refine NatTrans.ext (funext fun K => ?_)
    rw [NatTrans.comp_app, Functor.whiskerLeft_app,
      ← factorsh_hom_comp_homotopyCounit O U K, ← Category.assoc, Iso.inv_hom_id_app,
      Category.id_comp]
  exact Functor.rightDerived_ext (RF := derivedExtensionRestriction O U)
    (α := (derivedExtensionRestrictionFactorsh O U).inv)
    (W := HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
    (G := 𝟭 (DerivedCategory (SheafOfModules.{u} O)))
    (γ₁ := derivedExtensionRestrictionCanonicalCounit O U)
    (γ₂ := (derivedJShriekRestrictionAdjunction O U).counit) (h1.trans h2.symm)

/-- The identification of Stacks 08BT on shifted morphism groups: morphisms from
`j_{U!}(E|_U)` into the `n`-th shift of `F` are the shifted morphisms from `E|_U` to `F|_U`. -/
def extensionRestrictionShiftedHomEquiv
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    ((derivedExtensionRestriction O U).obj E ⟶ F⟦n⟧) ≃+
      ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n :=
  adjShiftedHomEquiv _ _ (derivedJShriekRestrictionAdjunction O U) E F n

/-- **The identification of Stacks 08BT carries precomposition with the canonical counit of
Stacks 08BU to restriction.** This is what makes the maps of the Mayer--Vietoris sequence the
restriction maps. -/
theorem extensionRestrictionShiftedHomEquiv_canonicalCounit
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    extensionRestrictionShiftedHomEquiv O U E F n
        ((derivedExtensionRestrictionCanonicalCounit O U).app E ≫ x) =
      ShiftedHom.map x (derivedRestriction O U) := by
  rw [derivedExtensionRestrictionCanonicalCounit_eq]
  change adjShiftedHomEquiv (jShriek U O).mapDerivedCategory (derivedRestriction O U)
      (derivedJShriekRestrictionAdjunction O U) E F n
      ((derivedJShriekRestrictionAdjunction O U).counit.app E ≫ x) =
    ShiftedHom.map x (derivedRestriction O U)
  exact adjShiftedHomEquiv_counit _ _ (derivedJShriekRestrictionAdjunction O U) E F n x

-- Neither the derived adjunction nor the identification it gives is ever unfolded below:
-- both are localizations, and unfolding either defeats the elaborator.  Everything past this
-- point goes through `extensionRestrictionShiftedHomEquiv_canonicalCounit` instead.
attribute [local irreducible] derivedJShriekRestrictionAdjunction
  extensionRestrictionShiftedHomEquiv

end Adjunction

/-! ### The maps of the Mayer--Vietoris sequence -/

section Maps

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The canonical counit of Stacks 08BT at an object, with the identity functor on its target
evaluated away. -/
def mvCounitApp (U : Opens X) (E : DerivedCategory (SheafOfModules.{u} O)) :
    (derivedExtensionRestriction O U).obj E ⟶ E :=
  (derivedExtensionRestrictionCanonicalCounit O U).app E

/-- The identification `extensionRestrictionShiftedHomEquiv` carries precomposition with
`mvCounitApp` to restriction of shifted morphisms. -/
theorem extensionRestrictionShiftedHomEquiv_mvCounitApp (U : Opens X)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    extensionRestrictionShiftedHomEquiv O U E F n (mvCounitApp O U E ≫ x) =
      ShiftedHom.map x (derivedRestriction O U) :=
  extensionRestrictionShiftedHomEquiv_canonicalCounit O U E F n x

/-- If a comparison `i` of extension-by-zero functors factors the canonical counit for `W` through
that for `U`, then it does so at every object. -/
theorem mvCounitApp_comp_of_comp (U W : Opens X)
    (i : derivedExtensionRestriction O W ⟶ derivedExtensionRestriction O U)
    (hi : i ≫ derivedExtensionRestrictionCanonicalCounit O U =
      derivedExtensionRestrictionCanonicalCounit O W)
    (E : DerivedCategory (SheafOfModules.{u} O)) :
    i.app E ≫ mvCounitApp O U E = mvCounitApp O W E :=
  NatTrans.congr_app hi E

/-- The two identifications of Stacks 08BT for `U` and `V`, taken together. -/
def mvPairEquiv (U V : Opens X) (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (((derivedExtensionRestriction O U).obj E ⟶ F⟦n⟧) ×
        ((derivedExtensionRestriction O V).obj E ⟶ F⟦n⟧)) ≃+
      (ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n ×
        ShiftedHom ((derivedRestriction O V).obj E) ((derivedRestriction O V).obj F) n) :=
  AddEquiv.prodCongr (extensionRestrictionShiftedHomEquiv O U E F n)
    (extensionRestrictionShiftedHomEquiv O V E F n)

/-- The restriction map of the Mayer--Vietoris sequence, read through the identifications of
Stacks 08BT as a map into the shifted morphism groups of the two open subspaces. -/
def mvRestriction (U V : Opens X) (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (E ⟶ F⟦n⟧) →+
      (ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n ×
        ShiftedHom ((derivedRestriction O V).obj E) ((derivedRestriction O V).obj F) n) :=
  (mvPairEquiv O U V E F n : _ →+ _).comp
    (shiftedHomRestriction (mvCounitApp O U E) (mvCounitApp O V E) F n)

/-- **The restriction map of the Mayer--Vietoris sequence is the pair of the two
restrictions.** -/
theorem mvRestriction_apply (U V : Opens X)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    mvRestriction O U V E F n x =
      (ShiftedHom.map x (derivedRestriction O U),
        ShiftedHom.map x (derivedRestriction O V)) :=
  Prod.ext (extensionRestrictionShiftedHomEquiv_mvCounitApp O U E F n x)
    (extensionRestrictionShiftedHomEquiv_mvCounitApp O V E F n x)

/-- A comparison `i` of the extension-by-zero functors of two opens, read through the
identifications of Stacks 08BT as a map of the shifted morphism groups of the two open
subspaces. -/
def mvToOverlap (U W : Opens X)
    (i : derivedExtensionRestriction O W ⟶ derivedExtensionRestriction O U)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n →+
      ShiftedHom ((derivedRestriction O W).obj E) ((derivedRestriction O W).obj F) n :=
  (extensionRestrictionShiftedHomEquiv O W E F n : _ →+ _).comp
    ((shiftedHomPrecomp (i.app E) F n).comp
      ((extensionRestrictionShiftedHomEquiv O U E F n).symm : _ →+ _))

/-- `mvToOverlap` sends `y` to the image under the identification for `W` of `i` precomposed with
the preimage of `y` under the identification for `U`. -/
theorem mvToOverlap_apply (U W : Opens X)
    (i : derivedExtensionRestriction O W ⟶ derivedExtensionRestriction O U)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ)
    (y : ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n) :
    mvToOverlap O U W i E F n y =
      extensionRestrictionShiftedHomEquiv O W E F n
        (i.app E ≫ (extensionRestrictionShiftedHomEquiv O U E F n).symm y) :=
  rfl

private lemma symm_equiv_map (U : Opens X)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    (extensionRestrictionShiftedHomEquiv O U E F n).symm
        (ShiftedHom.map x (derivedRestriction O U)) = mvCounitApp O U E ≫ x :=
  (AddEquiv.symm_apply_eq _).2
    (extensionRestrictionShiftedHomEquiv_mvCounitApp O U E F n x).symm

/-- **A comparison compatible with the canonical counits restricts restrictions.** If the
comparison `i` factors the counit of the smaller open `W` through the counit of the larger
open `U`, then the map it induces carries the restriction of `x` to `U` to the restriction of
`x` to `W`: it is the restriction map from `U` to `W`. -/
theorem mvToOverlap_restriction (U W : Opens X)
    (i : derivedExtensionRestriction O W ⟶ derivedExtensionRestriction O U)
    (hi : i ≫ derivedExtensionRestrictionCanonicalCounit O U =
      derivedExtensionRestrictionCanonicalCounit O W)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧) :
    mvToOverlap O U W i E F n (ShiftedHom.map x (derivedRestriction O U)) =
      ShiftedHom.map x (derivedRestriction O W) :=
  (congrArg (extensionRestrictionShiftedHomEquiv O W E F n)
      ((congrArg (fun t => i.app E ≫ t) (symm_equiv_map O U E F n x)).trans
        ((Category.assoc (i.app E) (mvCounitApp O U E) x).symm.trans
          (congrArg (fun t => t ≫ x) (mvCounitApp_comp_of_comp O U W i hi E))))).trans
    (extensionRestrictionShiftedHomEquiv_mvCounitApp O W E F n x)

/-- Negating a comparison negates the map it induces. -/
theorem mvToOverlap_neg (U W : Opens X)
    (i : derivedExtensionRestriction O W ⟶ derivedExtensionRestriction O U)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ)
    (y : ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n) :
    mvToOverlap O U W (-i) E F n y = -mvToOverlap O U W i E F n y :=
  (congrArg (extensionRestrictionShiftedHomEquiv O W E F n)
      (Preadditive.neg_comp _ _)).trans
    (map_neg (extensionRestrictionShiftedHomEquiv O W E F n) _)

/-- The difference map of the Mayer--Vietoris sequence, read through the identifications of
Stacks 08BT. -/
def mvDifference (U V : Opens X)
    (iU : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O U)
    (iV : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O V)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n ×
        ShiftedHom ((derivedRestriction O V).obj E) ((derivedRestriction O V).obj F) n) →+
      ShiftedHom ((derivedRestriction O (U ⊓ V)).obj E)
        ((derivedRestriction O (U ⊓ V)).obj F) n :=
  (extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F n : _ →+ _).comp
    ((shiftedHomDifference (iU.app E) (iV.app E) F n).comp
      ((mvPairEquiv O U V E F n).symm : _ →+ _))

/-- **The difference map is the difference of the two restrictions to the overlap.** -/
theorem mvDifference_apply (U V : Opens X)
    (iU : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O U)
    (iV : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O V)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ)
    (xU : ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n)
    (xV : ShiftedHom ((derivedRestriction O V).obj E) ((derivedRestriction O V).obj F) n) :
    mvDifference O U V iU iV E F n (xU, xV) =
      mvToOverlap O U (U ⊓ V) iU E F n xU -
        mvToOverlap O V (U ⊓ V) (-iV) E F n xV :=
  (map_add (extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F n) _ _).trans
    ((congrArg (fun t => mvToOverlap O U (U ⊓ V) iU E F n xU + t)
        ((neg_neg (mvToOverlap O V (U ⊓ V) iV E F n xV)).symm.trans
          (congrArg Neg.neg (mvToOverlap_neg O V (U ⊓ V) iV E F n xV)).symm)).trans
      (sub_eq_add_neg _ _).symm)

/-- Precomposing with an additive equivalence and then with its inverse is the identity. -/
private lemma symm_comp_comp_addEquiv {M N P : Type*} [AddZeroClass M] [AddZeroClass N]
    [AddZeroClass P] (e : N ≃+ P) (f : M →+ N) :
    (e.symm : P →+ N).comp ((e : N →+ P).comp f) = f :=
  AddMonoidHom.ext fun x => e.symm_apply_apply (f x)

/-- The ladder square identifying the restriction map with the first map of the sequence of
Stacks 08BU. -/
theorem mvRestriction_ladder (U V : Opens X)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (shiftedHomRestriction (mvCounitApp O U E) (mvCounitApp O V E) F n).comp
        (AddEquiv.refl (E ⟶ F⟦n⟧)) =
      ((mvPairEquiv O U V E F n).symm : _ →+ _).comp (mvRestriction O U V E F n) :=
  (symm_comp_comp_addEquiv _ _).symm

/-- The ladder square identifying the difference map with the second map of the sequence of
Stacks 08BU. -/
theorem mvDifference_ladder (U V : Opens X)
    (iU : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O U)
    (iV : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O V)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (shiftedHomDifference (iU.app E) (iV.app E) F n).comp
        ((mvPairEquiv O U V E F n).symm : _ →+ _) =
      ((extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F n).symm : _ →+ _).comp
        (mvDifference O U V iU iV E F n) :=
  (symm_comp_comp_addEquiv _ _).symm

/-- The boundary map of the Mayer--Vietoris sequence, read through the identification of
Stacks 08BT. -/
def mvBoundary (W : Opens X)
    (bd : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
      ((derivedExtensionRestriction O W).obj E ⟶ F⟦n⟧) →+ (E ⟶ F⟦n + 1⟧))
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    ShiftedHom ((derivedRestriction O W).obj E) ((derivedRestriction O W).obj F) n →+
      (E ⟶ F⟦n + 1⟧) :=
  (bd E F n).comp ((extensionRestrictionShiftedHomEquiv O W E F n).symm : _ →+ _)

/-- The ladder square identifying the boundary map with the connecting map of the sequence of
Stacks 08BU. -/
theorem mvBoundary_ladder (W : Opens X)
    (bd : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
      ((derivedExtensionRestriction O W).obj E ⟶ F⟦n⟧) →+ (E ⟶ F⟦n + 1⟧))
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (bd E F n).comp ((extensionRestrictionShiftedHomEquiv O W E F n).symm : _ →+ _) =
      ((AddEquiv.refl (E ⟶ F⟦n + 1⟧)) : _ →+ _).comp (mvBoundary O W bd E F n) :=
  AddMonoidHom.ext fun _ => rfl

end Maps

/-! ### Stacks 08BW with its maps named -/

section MayerVietoris

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (U V : Opens X)

/-- **Stacks 08BW, with every map of the sequence named.** For a ringed space covered by two
open subspaces `U` and `V` and objects `E`, `F` of `D(𝒪_X)`, the Mayer--Vietoris sequence

`⋯ ⟶ Ext^{n-1}(E|_{U∩V}, F|_{U∩V}) ⟶ Ext^n(E, F) ⟶
  Ext^n(E|_U, F|_U) × Ext^n(E|_V, F|_V) ⟶ Ext^n(E|_{U∩V}, F|_{U∩V}) ⟶ ⋯`

is exact at each of its three kinds of spot and in every integer degree, its first map is
the pair of the two restrictions and its second map is the difference of two further
restrictions to the intersection. -/
@[stacks 08BW "the long exact sequence, with its first map the pair of the restrictions to \
  the two opens and its second map the difference of two restrictions to their intersection"]
theorem exists_mayerVietoris_ext_longExactSequence_restrictions (hUV : U ⊔ V = ⊤) :
    ∃ (restriction : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          (E ⟶ F⟦n⟧) →+
            (ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n ×
              ShiftedHom ((derivedRestriction O V).obj E)
                ((derivedRestriction O V).obj F) n))
      (restrictionUW : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n →+
            ShiftedHom ((derivedRestriction O (U ⊓ V)).obj E)
              ((derivedRestriction O (U ⊓ V)).obj F) n)
      (restrictionVW : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          ShiftedHom ((derivedRestriction O V).obj E) ((derivedRestriction O V).obj F) n →+
            ShiftedHom ((derivedRestriction O (U ⊓ V)).obj E)
              ((derivedRestriction O (U ⊓ V)).obj F) n)
      (difference : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          (ShiftedHom ((derivedRestriction O U).obj E) ((derivedRestriction O U).obj F) n ×
              ShiftedHom ((derivedRestriction O V).obj E)
                ((derivedRestriction O V).obj F) n) →+
            ShiftedHom ((derivedRestriction O (U ⊓ V)).obj E)
              ((derivedRestriction O (U ⊓ V)).obj F) n)
      (boundary : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          ShiftedHom ((derivedRestriction O (U ⊓ V)).obj E)
              ((derivedRestriction O (U ⊓ V)).obj F) n →+ (E ⟶ F⟦n + 1⟧)),
      (∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧),
          restriction E F n x =
            (ShiftedHom.map x (derivedRestriction O U),
              ShiftedHom.map x (derivedRestriction O V))) ∧
      (∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧),
          restrictionUW E F n (ShiftedHom.map x (derivedRestriction O U)) =
            ShiftedHom.map x (derivedRestriction O (U ⊓ V))) ∧
      (∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (x : E ⟶ F⟦n⟧),
          restrictionVW E F n (ShiftedHom.map x (derivedRestriction O V)) =
            ShiftedHom.map x (derivedRestriction O (U ⊓ V))) ∧
      (∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ)
          (xU : ShiftedHom ((derivedRestriction O U).obj E)
            ((derivedRestriction O U).obj F) n)
          (xV : ShiftedHom ((derivedRestriction O V).obj E)
            ((derivedRestriction O V).obj F) n),
          difference E F n (xU, xV) =
            restrictionUW E F n xU - restrictionVW E F n xV) ∧
      (∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          Function.Exact (restriction E F n) (difference E F n)) ∧
      (∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          Function.Exact (difference E F n) (boundary E F n)) ∧
      (∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
          Function.Exact (boundary E F n) (restriction E F (n + 1))) := by
  have key := exists_mayerVietoris_hom_longExactSequence O U V hUV
    (derivedExtensionRestriction O U) (derivedExtensionRestriction O V)
    (derivedExtensionRestriction O (U ⊓ V))
    (derivedExtensionRestrictionFactorsh O U).inv
    (derivedExtensionRestrictionFactorsh O V).inv
    (derivedExtensionRestrictionFactorsh O (U ⊓ V)).inv
  obtain ⟨iU, iV, bd, hiU, hiV, hex⟩ := key
  have hiU' : iU ≫ derivedExtensionRestrictionCanonicalCounit O U =
      derivedExtensionRestrictionCanonicalCounit O (U ⊓ V) := hiU
  have hiV2 : iV ≫ derivedExtensionRestrictionCanonicalCounit O V =
      -derivedExtensionRestrictionCanonicalCounit O (U ⊓ V) := hiV
  have hiV' : (-iV) ≫ derivedExtensionRestrictionCanonicalCounit O V =
      derivedExtensionRestrictionCanonicalCounit O (U ⊓ V) :=
    (Preadditive.neg_comp _ _).trans ((congrArg Neg.neg hiV2).trans (neg_neg _))
  refine ⟨fun E F n => mvRestriction O U V E F n,
    fun E F n => mvToOverlap O U (U ⊓ V) iU E F n,
    fun E F n => mvToOverlap O V (U ⊓ V) (-iV) E F n,
    fun E F n => mvDifference O U V iU iV E F n,
    fun E F n => mvBoundary O (U ⊓ V) bd E F n,
    fun E F n x => mvRestriction_apply O U V E F n x,
    fun E F n x => mvToOverlap_restriction O U (U ⊓ V) iU hiU' E F n x,
    fun E F n x => mvToOverlap_restriction O V (U ⊓ V) (-iV) hiV' E F n x,
    fun E F n xU xV => mvDifference_apply O U V iU iV E F n xU xV,
    fun E F n => ?_, fun E F n => ?_, fun E F n => ?_⟩
  · exact Function.Exact.of_ladder_addEquiv_of_exact' (AddEquiv.refl (E ⟶ F⟦n⟧))
      (mvPairEquiv O U V E F n).symm
      (extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F n).symm
      (mvRestriction_ladder O U V E F n) (mvDifference_ladder O U V iU iV E F n)
      (hex E F n).1
  · exact Function.Exact.of_ladder_addEquiv_of_exact'
      (mvPairEquiv O U V E F n).symm
      (extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F n).symm
      (AddEquiv.refl (E ⟶ F⟦n + 1⟧))
      (mvDifference_ladder O U V iU iV E F n) (mvBoundary_ladder O (U ⊓ V) bd E F n)
      (hex E F n).2.1
  · exact Function.Exact.of_ladder_addEquiv_of_exact'
      (extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F n).symm
      (AddEquiv.refl (E ⟶ F⟦n + 1⟧))
      (mvPairEquiv O U V E F (n + 1)).symm
      (mvBoundary_ladder O (U ⊓ V) bd E F n) (mvRestriction_ladder O U V E F (n + 1))
      (hex E F n).2.2

end MayerVietoris

end Stacks.ExtensionByZero

end
