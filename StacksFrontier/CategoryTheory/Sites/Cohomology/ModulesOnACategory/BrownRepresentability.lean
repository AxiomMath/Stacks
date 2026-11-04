module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import StacksFrontier.Homology.Injectives.DerivedCategory.Existence
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent objects of `D(O)` for a category with a final object

Let `C` be a category with the chaotic topology and `O : Cᵒᵖ ⥤ RingCat` a presheaf of rings, so
that `Mod(O)` is `PresheafOfModules O` and `D(O)` is its derived category. For `U : Cᵒᵖ` the
derived sections `RΓ(U, -) : D(O) ⥤ D(O(U))` are induced by the exact evaluation functor at `U`.
A morphism `U → V` of `C` is written as `a : V ⟶ U` in `Cᵒᵖ`, with restriction ring map
`O.map a : O(V) → O(U)`.

Derived base change `- ⊗^L_{O(V)} O(U)` is supplied by a `BaseChangeData O`: a left adjoint of
the derived restriction of scalars along each `O.map a`, with its functoriality isomorphism. The
comparison map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is the adjoint transpose of the derived
restriction map, and `QC(O) ⊆ D(O)` is the full subcategory of the `K` all of whose comparison
maps are isomorphisms ([Stacks, Tag 0GYV]).

For a final object `X` of `C` and `R = O(X)`, a `MorphismOfSites` consists of a derived pullback
`Lf^* : D(R) ⥤ D(O)`, left adjoint to `Rf_* = RΓ(X, -)`, with the isomorphisms
`RΓ(U, Lf^*P) ≅ P ⊗^L_R O(U)` of [Stacks, Tag 0GZ1] compatible with the restriction maps. Then
`Lf^*` and `Rf_*` are quasi-inverse equivalences between `D(R)` and `QC(O)`
([Stacks, Tag 0H0R]).

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData`: derived base change along
  the restriction maps of `O`.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.comparison`: the comparison map
  `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)`.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.QC`: the full subcategory `QC(O)` of `D(O)`.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.MorphismOfSites`: the morphism of sites
  `(C, O) → (pt, O(X))` for a final object `X`.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.RGamma_jointly_conservative`: a morphism of
  `D(O)` inducing isomorphisms on all `RΓ(U, -)` is an isomorphism.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.main_equivalence_of_morphismOfSites`: `Lf^*`
  lands in `QC(O)`, the unit of `Lf^* ⊣ Rf_*` is an isomorphism, and its counit is an isomorphism
  on `QC(O)`.

## References

* [Stacks Project, Tag 0H0R](https://stacks.math.columbia.edu/tag/0H0R)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GZ1](https://stacks.math.columbia.edu/tag/0GZ1)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits CategoryTheory.Functor

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

noncomputable section

universe w u v r

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

-- The derived categories `D(O(U))` use the standard localization model; `D(O)` uses the
-- small-Hom model `derivedPresheafCategory`.
attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars along `O.map a` preserves finite limits. -/
instance rsPreservesFiniteLimits {U V : Cᵒᵖ} (a : V ⟶ U) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- Restriction of scalars along `O.map a` preserves finite colimits. -/
instance rsPreservesFiniteColimits {U V : Cᵒᵖ} (a : V ⟶ U) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- Evaluation at `U` followed by restriction of scalars along `O.map a` is additive. -/
instance evalRsAdditive {U V : Cᵒᵖ} (a : V ⟶ U) :
    (PresheafOfModules.evaluation.{max u v r w} O U ⋙
      ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).Additive := by
  apply Functor.instAdditiveComp

/-- Evaluation at `U` followed by restriction of scalars along `O.map a` preserves finite
limits. -/
instance evalRsPreservesFiniteLimits {U V : Cᵒᵖ} (a : V ⟶ U) :
    PreservesFiniteLimits
      (PresheafOfModules.evaluation.{max u v r w} O U ⋙
        ModuleCat.restrictScalars.{max u v r w} (O.map a).hom) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- Evaluation at `U` followed by restriction of scalars along `O.map a` preserves finite
colimits. -/
instance evalRsPreservesFiniteColimits {U V : Cᵒᵖ} (a : V ⟶ U) :
    PreservesFiniteColimits
      (PresheafOfModules.evaluation.{max u v r w} O U ⋙
        ModuleCat.restrictScalars.{max u v r w} (O.map a).hom) := by
  constructor; intro J _ _; constructor; intro F; infer_instance

/-- The derived category of presheaves of `O`-modules, with morphisms in the module universe; it
exists because presheaves of modules form a Grothendieck abelian category (Tag 079Q). -/
noncomputable instance derivedPresheafCategory :
    HasDerivedCategory.{max u v r w} (PresheafOfModules.{max u v r w} O) :=
  letI : IsGrothendieckAbelian.{max u v r w} (PresheafOfModules.{max u v r w} O) :=
    Stacks.SheafOfModules.presheafModulesGrothendieck.{u, v, r, w} O
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

/-- `D(O)`, the derived category of `O`-modules, which for the chaotic topology are the presheaves
of `O`-modules. -/
abbrev DMod : Type _ :=
  DerivedCategory.{max u v r w} (PresheafOfModules.{max u v r w} O)

/-- `RΓ(U, -) : D(O) ⥤ D(O(U))`, derived sections over `U`: the functor induced on derived
categories by the exact functor `PresheafOfModules.evaluation O U`. -/
abbrev RGamma (U : Cᵒᵖ) : DMod.{w} O ⥤ DerivedCategory (ModuleCat.{max u v r w} (O.obj U)) :=
  (PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategory

/-- The derived restriction of scalars `D(O(U)) ⥤ D(O(V))` along `O.map a : O(V) → O(U)` for
`a : V ⟶ U` in `Cᵒᵖ`. -/
abbrev DRestrict {U V : Cᵒᵖ} (a : V ⟶ U) :
    DerivedCategory (ModuleCat.{max u v r w} (O.obj U)) ⥤
      DerivedCategory (ModuleCat.{max u v r w} (O.obj V)) :=
  (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategory

/-- Derived sections over `U` regarded `O(V)`-linearly: the functor induced on derived categories
by the exact composite `evaluation U ⋙ restrictScalars (O.map a)`. -/
abbrev RGammaRestrict {U V : Cᵒᵖ} (a : V ⟶ U) :
    DMod.{w} O ⥤ DerivedCategory (ModuleCat.{max u v r w} (O.obj V)) :=
  (PresheafOfModules.evaluation.{max u v r w} O U ⋙
    ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategory

/-- `RGammaRestrict O a` lifts `evaluation U ⋙ restrictScalars (O.map a)`, applied to complexes,
through the localization functor `DerivedCategory.Q`. -/
instance liftRGammaRestrict {U V : Cᵒᵖ} (a : V ⟶ U) :
    Localization.Lifting (DerivedCategory.Q)
      (HomologicalComplex.quasiIso (PresheafOfModules O) (ComplexShape.up ℤ))
      ((PresheafOfModules.evaluation.{max u v r w} O U ⋙
        ModuleCat.restrictScalars.{max u v r w} (O.map
          a).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (RGammaRestrict.{w} O a) :=
  ⟨(PresheafOfModules.evaluation.{max u v r w} O U ⋙ ModuleCat.restrictScalars.{max u v r w} (O.map
      a).hom).mapDerivedCategoryFactors⟩

/-- The derived restriction natural transformation `RΓ(V, -) ⟶ restrictScalars RΓ(U, -)`, induced
through the localization by the restriction maps
`PresheafOfModules.restriction O a : evaluation V ⟶ evaluation U ⋙ restrictScalars (O.map a)`. -/
def restrictionD {U V : Cᵒᵖ} (a : V ⟶ U) : RGamma.{w} O V ⟶ RGammaRestrict.{w} O a :=
  Localization.liftNatTrans (DerivedCategory.Q)
    (HomologicalComplex.quasiIso (PresheafOfModules O) (ComplexShape.up ℤ))
    ((PresheafOfModules.evaluation.{max u v r w} O V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    ((PresheafOfModules.evaluation.{max u v r w} O U ⋙
      ModuleCat.restrictScalars.{max u v r w} (O.map
        a).hom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (RGamma.{w} O V) (RGammaRestrict.{w} O a)
    (whiskerRight (NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
      (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- `RΓ(U, -) ⋙ DRestrict a` lifts `evaluation U ⋙ restrictScalars (O.map a)`, applied to
complexes, through the localization functor `DerivedCategory.Q`. -/
instance liftComp {U V : Cᵒᵖ} (a : V ⟶ U) :
    Localization.Lifting (DerivedCategory.Q)
      (HomologicalComplex.quasiIso (PresheafOfModules O) (ComplexShape.up ℤ))
      ((PresheafOfModules.evaluation.{max u v r w} O U ⋙
        ModuleCat.restrictScalars.{max u v r w} (O.map
          a).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (RGamma.{w} O U ⋙ DRestrict.{w} O a) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryFactors
      (DRestrict.{w} O a) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _
      (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm⟩

/-- The isomorphism `RGammaRestrict a ≅ RΓ(U, -) ⋙ DRestrict a` induced by the identity of
complexes. -/
def RGammaRestrictIso {U V : Cᵒᵖ} (a : V ⟶ U) :
    RGammaRestrict.{w} O a ≅ RGamma.{w} O U ⋙ DRestrict.{w} O a :=
  Localization.liftNatIso (DerivedCategory.Q)
    (HomologicalComplex.quasiIso (PresheafOfModules O) (ComplexShape.up ℤ))
    ((PresheafOfModules.evaluation.{max u v r w} O U ⋙
      ModuleCat.restrictScalars.{max u v r w} (O.map
        a).hom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((PresheafOfModules.evaluation.{max u v r w} O U ⋙
      ModuleCat.restrictScalars.{max u v r w} (O.map
        a).hom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (RGammaRestrict.{w} O a) (RGamma.{w} O U ⋙ DRestrict.{w} O a)
    (Iso.refl _)

/-- The derived restriction map `RΓ(V, K) ⟶ DRestrict a (RΓ(U, K))` in `D(O(V))`. -/
def restrictionMap {U V : Cᵒᵖ} (a : V ⟶ U) (K : DMod.{w} O) :
    (RGamma.{w} O V).obj K ⟶ (DRestrict.{w} O a).obj ((RGamma.{w} O U).obj K) :=
  (restrictionD.{w} O a).app K ≫ (RGammaRestrictIso.{w} O a).hom.app K

/-- The canonical derived restriction map on an object of the form `Q(P)` for a complex `P` of
`O`-modules: it is the image under `Q` of the restriction map of complexes, up to the canonical
factorizations of the derived functors of evaluation and of restriction of scalars. -/
lemma restrictionMap_Q {U V : Cᵒᵖ} (a : V ⟶ U)
    (P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    restrictionMap.{w} O a (DerivedCategory.Q.obj P) =
      (PresheafOfModules.evaluation.{max u v r w} O V).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (PresheafOfModules.restriction O a) (ComplexShape.up ℤ)).app P) ≫
      (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategoryFactors.inv.app
        (((PresheafOfModules.evaluation.{max u v r w} O U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      (DRestrict.{w} O a).map
        ((PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryFactors.inv.app P) := by
  simp only [restrictionMap, restrictionD, Localization.liftNatTrans_app, comp_obj,
    Localization.Lifting.iso, whiskerRight_app, RGammaRestrictIso, Localization.liftNatIso,
    liftComp, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerLeft_inv, Category.assoc, isoWhiskerRight_inv, NatTrans.comp_app,
    associator_hom_app, whiskerLeft_app, associator_inv_app, Category.comp_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, NatIso.cancel_natIso_hom_left]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

/-- The canonical derived restriction maps along `a : V ⟶ U` in `Cᵒᵖ`, assembled into a natural
transformation `RΓ(V, -) ⟶ DRestrict a (RΓ(U, -))`. -/
def restrictionNatTrans {U V : Cᵒᵖ} (a : V ⟶ U) :
    RGamma.{w} O V ⟶ RGamma.{w} O U ⋙ DRestrict.{w} O a :=
  restrictionD.{w} O a ≫ (RGammaRestrictIso.{w} O a).hom

/-- The components of `restrictionNatTrans` are the canonical derived restriction maps. -/
lemma restrictionNatTrans_app {U V : Cᵒᵖ} (a : V ⟶ U) (K : DMod.{w} O) :
    (restrictionNatTrans.{w} O a).app K = restrictionMap.{w} O a K :=
  rfl

section Bookkeeping

universe t₁ t₂ s₁ s₂

variable {E₁ : Type t₁} [Category.{s₁} E₁] {E₂ : Type t₂} [Category.{s₂} E₂]

/-- A naturality square `hn`, a factorization `hM` and two cancelling pairs of morphisms `hcB`,
`hbA` combine into the commuting square `L ≫ R.map (aA ≫ bA ≫ cA) = (aB ≫ bB ≫ cB) ≫ M`. -/
lemma comp_map_eq_comp_of_naturality {R : E₁ ⥤ E₂}
    {x₀ x₁ x₂ x₃ x₄ : E₂} {y₀ y₁ y₂ y₃ : E₁}
    {L : x₀ ⟶ R.obj y₀} {aB : x₀ ⟶ x₁} {aA : y₀ ⟶ y₁}
    {bB : x₁ ⟶ x₂} {cB : x₂ ⟶ x₃} {cBinv : x₃ ⟶ x₂}
    {bA : y₁ ⟶ y₂} {bAinv : y₂ ⟶ y₁} {cA : y₂ ⟶ y₃}
    {m : x₂ ⟶ x₄} {n : x₄ ⟶ R.obj y₂} {M : x₃ ⟶ R.obj y₃}
    (hn : aB ≫ bB ≫ m ≫ n ≫ R.map bAinv = L ≫ R.map aA)
    (hM : M = cBinv ≫ m ≫ n ≫ R.map cA)
    (hcB : cB ≫ cBinv = 𝟙 x₂) (hbA : bAinv ≫ bA = 𝟙 y₂) :
    L ≫ R.map (aA ≫ bA ≫ cA) = (aB ≫ bB ≫ cB) ≫ M := by
  rw [hM, Functor.map_comp, Functor.map_comp, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc cB cBinv, hcB, Category.id_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Category.assoc bAinv bA, hbA, Category.id_comp]

end Bookkeeping

/-- Derived base change on `O`: for every `a : V ⟶ U` in `Cᵒᵖ`, a derived base change
`- ⊗^L_{O(V)} O(U)`, given as a left adjoint of the derived restriction of scalars `DRestrict a`
(so determined up to unique isomorphism), together with the functoriality of base change
(tag 0FNG). -/
structure BaseChangeData where
  /-- Derived base change `- ⊗^L_{O(V)} O(U)` along `a : V ⟶ U` in `Cᵒᵖ`. -/
  baseChange : ∀ {U V : Cᵒᵖ} (_ : V ⟶ U),
    DerivedCategory (ModuleCat.{max u v r w} (O.obj V)) ⥤
      DerivedCategory (ModuleCat.{max u v r w} (O.obj U))
  /-- The base change is left adjoint to the derived restriction of scalars. -/
  baseChangeAdj : ∀ {U V : Cᵒᵖ} (a : V ⟶ U), baseChange a ⊣ DRestrict.{w} O a
  /-- Base change of a composite is the composite of base changes (functoriality, tag 0FNG):
  for `a : W ⟶ V`, `b : V ⟶ U` in `Cᵒᵖ`, `baseChange (a ≫ b) ≅ baseChange a ⋙ baseChange b`. -/
  baseChangeComp : ∀ {U V W : Cᵒᵖ} (a : W ⟶ V) (b : V ⟶ U),
    baseChange (a ≫ b) ≅ baseChange a ⋙ baseChange b

variable {O}

/-- The comparison map `c_{a,K} : RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` in `D(O(U))` of tag 0GYV:
the adjoint transpose, under `baseChange a ⊣ DRestrict a`, of the derived restriction map
`restrictionMap a K`. -/
def comparison (bc : BaseChangeData.{w} O) {U V : Cᵒᵖ} (a : V ⟶ U) (K : DMod.{w} O) :
    (bc.baseChange a).obj ((RGamma.{w} O V).obj K) ⟶ (RGamma.{w} O U).obj K :=
  ((bc.baseChangeAdj a).homEquiv _ _).symm (restrictionMap.{w} O a K)

/-- `K ∈ QC(O)` (tag 0GYV): for every morphism `U → V` in `C` (`a : V ⟶ U` in `Cᵒᵖ`) the
comparison map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism. -/
def IsQC (bc : BaseChangeData.{w} O) (K : DMod.{w} O) : Prop :=
  ∀ {U V : Cᵒᵖ} (a : V ⟶ U), IsIso (comparison.{w} bc a K)

/-- The full subcategory `QC(O) ⊆ D(O)` of tag 0GYV, of the `K ∈ D(O)` with `IsQC bc K`. -/
abbrev QC (bc : BaseChangeData.{w} O) : Type _ :=
  ObjectProperty.FullSubcategory (fun K => IsQC.{w} bc K)

/-- The canonical inclusion functor `QC(O) ⥤ D(O)`. -/
abbrev QCι (bc : BaseChangeData.{w} O) : QC.{w} bc ⥤ DMod.{w} O :=
  ObjectProperty.ι _

/-- For `K = Lf^*P`, the composite of isomorphisms
`RΓ(V, K) ⊗^L_{O(V)} O(U) ≅ (P ⊗^L_R O(V)) ⊗^L_{O(V)} O(U) ≅ P ⊗^L_R O(U) ≅ RΓ(U, K)` given by
`pullbackIso` and `baseChangeComp`, using that `X ← V ← U` is the unique morphism `X ← U`. -/
def pullbackComparisonIso (bc : BaseChangeData.{w} O) {X : C} (hX : IsTerminal X)
    (Lpullback : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ⥤ DMod.{w} O)
    (pullbackIso : ∀ (U : C),
      Lpullback ⋙ RGamma.{w} O (Opposite.op U) ≅ bc.baseChange (hX.from U).op)
    {U V : C} (a : (Opposite.op V) ⟶ (Opposite.op U))
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))) :
    (bc.baseChange a).obj ((RGamma.{w} O (Opposite.op V)).obj (Lpullback.obj P)) ⟶
      (RGamma.{w} O (Opposite.op U)).obj (Lpullback.obj P) :=
  (bc.baseChange a).map ((pullbackIso V).hom.app P) ≫
    (bc.baseChangeComp (hX.from V).op a).inv.app P ≫
    eqToHom (by rw [show (hX.from V).op ≫ a = (hX.from U).op from
      Quiver.Hom.unop_inj (hX.hom_ext _ _)]) ≫
    (pullbackIso U).inv.app P

/-- The morphism of sites `f : (C, O) → (pt, R)` for a final object `X` of `C` and `R = O(X)`,
with `Rf_* = RGamma O (op X)`. It consists of a derived pullback `Lf^* = Lpullback` with

* `adj : Lpullback ⊣ RGamma O (op X)`, the adjunction `Lf^* ⊣ Rf_*`;
* `pullbackIso` (tag 0GZ1): the natural isomorphism `RΓ(U, Lf^*P) ≅ P ⊗^L_R O(U)`, the base
  change being along the restriction `R = O(X) → O(U)`;
* `comparisonCompat`: the comparison map at `Lf^*P` is the isomorphism
  `pullbackComparisonIso`, that is, `pullbackIso` is compatible with the restriction maps. -/
structure MorphismOfSites (bc : BaseChangeData.{w} O) (X : C) (hX : IsTerminal X) where
  /-- The derived pullback `Lf^* : D(R) ⥤ D(O)`, where `R = O(X)`. -/
  Lpullback : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ⥤ DMod.{w} O
  /-- The adjunction `Lf^* ⊣ Rf_*`, where `Rf_* = RΓ(X, -)`. -/
  adj : Lpullback ⊣ RGamma.{w} O (Opposite.op X)
  /-- Tag 0GZ1: `RΓ(U, Lf^*P) ≅ P ⊗^L_R O(U)` naturally in `P`, with the base change along the
  unique morphism `op X ⟶ op U` (the restriction `R = O(X) → O(U)`). -/
  pullbackIso : ∀ (U : C),
    Lpullback ⋙ RGamma.{w} O (Opposite.op U) ≅ bc.baseChange (hX.from U).op
  /-- Compatibility of `pullbackIso` with the canonical restriction maps: the comparison map at
  `Lf^*P` for `a : op V ⟶ op U` equals the canonical base-change-of-base-change isomorphism. -/
  comparisonCompat : ∀ {U V : C} (a : (Opposite.op V) ⟶ (Opposite.op U))
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))),
    comparison.{w} bc a (Lpullback.obj P) =
      pullbackComparisonIso.{w} bc hX Lpullback pullbackIso a P

variable {X : C} {hX : IsTerminal X}

/-- Assertion (1) of [Stacks, Tag 0H0R]: `Lf^*` lands in `QC(O)`. -/
theorem main_Lpullback_isQC (bc : BaseChangeData.{w} O) (mos : MorphismOfSites.{w} bc X hX)
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))) :
    IsQC.{w} bc (mos.Lpullback.obj P) := by
  intro U V a
  rw [mos.comparisonCompat a P]
  unfold pullbackComparisonIso
  infer_instance

/-- Restriction of scalars along `O.map (𝟙 Y)` is isomorphic to the identity functor. -/
def restrictScalarsIdIso (Y : Cᵒᵖ) :
    ModuleCat.restrictScalars.{max u v r w} (O.map (𝟙 Y)).hom ≅
      𝟭 (ModuleCat.{max u v r w} (O.obj Y)) :=
  eqToIso (by rw [O.map_id]; rfl) ≪≫ ModuleCat.restrictScalarsId (O.obj Y)

/-- The derived restriction of scalars along `O.map (𝟙 Y)` is isomorphic to the identity
functor. -/
def DRestrictId (Y : Cᵒᵖ) : DRestrict.{w} O (𝟙 Y) ≅ 𝟭 _ :=
  Localization.liftNatIso (DerivedCategory.Q)
    (HomologicalComplex.quasiIso (ModuleCat.{max u v r w} (O.obj Y)) (ComplexShape.up ℤ))
    ((ModuleCat.restrictScalars.{max u v r w} (O.map (𝟙 Y)).hom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    (DerivedCategory.Q)
    (DRestrict.{w} O (𝟙 Y)) (𝟭 _)
    (isoWhiskerRight (NatIso.mapHomologicalComplex (restrictScalarsIdIso.{w} (O := O) Y)
        (ComplexShape.up ℤ)) _ ≪≫
      isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)) _ ≪≫
      Functor.leftUnitor _)

/-- Base change along `𝟙 Y` is isomorphic to the identity functor, being left adjoint to
`DRestrict O (𝟙 Y) ≅ 𝟭`. -/
def baseChangeId (bc : BaseChangeData.{w} O) (Y : Cᵒᵖ) : bc.baseChange (𝟙 Y) ≅ 𝟭 _ := by
  have adj' : bc.baseChange (𝟙 Y) ⊣ 𝟭 _ := (bc.baseChangeAdj (𝟙 Y)).ofNatIsoRight
    (DRestrictId.{w} Y)
  exact adj'.leftAdjointUniq Adjunction.id

/-- The isomorphism `Lf^* ⋙ Rf_* ≅ 𝟭` on `D(R)`, that is `RΓ(X, Lf^*P) ≅ P`. -/
def unitIso (bc : BaseChangeData.{w} O) (mos : MorphismOfSites.{w} bc X hX) :
    mos.Lpullback ⋙ RGamma.{w} O (Opposite.op X) ≅ 𝟭 _ := by
  have hid : (hX.from X).op = 𝟙 (Opposite.op X) :=
    Quiver.Hom.unop_inj (hX.hom_ext _ _)
  refine (mos.pullbackIso X) ≪≫ ?_
  rw [hid]
  exact baseChangeId.{w} bc (Opposite.op X)

/-- Assertion (2) of [Stacks, Tag 0H0R]: the unit `P ⟶ Rf_* Lf^* P` is an isomorphism;
equivalently `Lf^*` is fully faithful and `RΓ(X, Lf^*P) ≅ P` canonically. -/
theorem main_unit_isIso (bc : BaseChangeData.{w} O) (mos : MorphismOfSites.{w} bc X hX)
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))) :
    IsIso (mos.adj.unit.app P) := by
  have := mos.adj.isIso_unit_of_iso (unitIso.{w} bc mos)
  infer_instance

/-- The derived-sections functors `RΓ(U, -)` are jointly conservative: a morphism `g` of `D(O)`
such that `RΓ(U, g)` is an isomorphism for every `U : Cᵒᵖ` is an isomorphism. -/
theorem RGamma_jointly_conservative {K K' : DMod.{w} O} (g : K ⟶ K')
    (h : ∀ U : Cᵒᵖ, IsIso ((RGamma.{w} O U).map g)) : IsIso g := by
  have homiso : ∀ {A : Type _} [inst : Category A] [Abelian A] [HasDerivedCategory A]
      {K K' : DerivedCategory A} (g : K ⟶ K'),
      (∀ n : ℤ, IsIso ((DerivedCategory.homologyFunctor A n).map g)) → IsIso g := by
    intro A _ _ _ K K' g hg
    have hker : (DerivedCategory.homologyFunctor A 0).homologicalKernel.trW g := by
      rw [(DerivedCategory.homologyFunctor A 0).mem_homologicalKernel_trW_iff g]
      intro n
      simpa only [DerivedCategory.shift_homologyFunctor] using hg n
    rw [(DerivedCategory.homologyFunctor A 0).homologicalKernel.trW_iff g] at hker
    obtain ⟨Z, g', hh, hT, hZmem⟩ := hker
    rw [Functor.mem_homologicalKernel_iff] at hZmem
    simp only [DerivedCategory.shift_homologyFunctor] at hZmem
    have hZ : IsZero Z := by
      have hle : Z.IsLE 0 := by rw [DerivedCategory.isLE_iff]; intro i _; exact hZmem i
      have hge : Z.IsGE 1 := by rw [DerivedCategory.isGE_iff]; intro i _; exact hZmem i
      exact DerivedCategory.TStructure.t.isZero Z 0 1 (by norm_num)
    have hg' : g ≫ g' = 0 := hZ.eq_of_tgt _ _
    have hc : IsZero ((Pretriangulated.contractibleTriangle K).obj₃) := by
      rw [Pretriangulated.contractibleTriangle_obj₃]; exact isZero_zero _
    let φ : Pretriangulated.contractibleTriangle K ⟶ Pretriangulated.Triangle.mk g g' hh :=
      Pretriangulated.Triangle.homMk _ _ (𝟙 K) g
        (0 : (Pretriangulated.contractibleTriangle K).obj₃ ⟶ Z)
        (by simp) (by simp [hg']) (hc.eq_of_src _ _)
    have h1 : IsIso φ.hom₁ := by
      simp only [φ, Pretriangulated.Triangle.homMk_hom₁]; exact IsIso.id K
    have h3 : IsIso φ.hom₃ := ⟨0, hc.eq_of_src _ _, hZ.eq_of_src _ _⟩
    have hiso := Pretriangulated.isIso₂_of_isIso₁₃ φ
      (Pretriangulated.contractible_distinguished K) hT h1 h3
    have e2 : φ.hom₂ = g := by simp only [φ, Pretriangulated.Triangle.homMk_hom₂]
    rwa [e2] at hiso
  refine homiso g fun n => ?_
  set M := (DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) n).map g with hMdef
  have hpsh : IsIso ((PresheafOfModules.toPresheaf O).map M) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    let F := PresheafOfModules.evaluation.{max u v r w} O U
    have liftA : Localization.Lifting (DerivedCategory.Q)
        (HomologicalComplex.quasiIso (PresheafOfModules.{max u v r w} O) (ComplexShape.up ℤ))
        (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{max u v r w} (O.obj U))
            (ComplexShape.up ℤ) n)
        (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor
          (ModuleCat.{max u v r w} (O.obj U)) n) :=
      ⟨(Functor.associator _ _ _).symm ≪≫
       isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
       Functor.associator _ _ _ ≪≫
       isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors
         (ModuleCat.{max u v r w} (O.obj U)) n)⟩
    have liftB : Localization.Lifting (DerivedCategory.Q)
        (HomologicalComplex.quasiIso (PresheafOfModules.{max u v r w} O) (ComplexShape.up ℤ))
        (HomologicalComplex.homologyFunctor (PresheafOfModules.{max u v r w} O)
          (ComplexShape.up ℤ) n ⋙ F)
        (DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) n ⋙ F) :=
      ⟨(Functor.associator _ _ _).symm ≪≫
       isoWhiskerRight (DerivedCategory.homologyFunctorFactors
         (PresheafOfModules.{max u v r w} O) n) F⟩
    let hcComm :
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            HomologicalComplex.homologyFunctor (ModuleCat.{max u v r w} (O.obj U))
              (ComplexShape.up ℤ) n ≅
        HomologicalComplex.homologyFunctor (PresheafOfModules.{max u v r w} O)
          (ComplexShape.up ℤ) n ⋙ F :=
      isoWhiskerLeft _
          (HomologicalComplex.homologyFunctorIso (ModuleCat.{max u v r w} (O.obj U))
            (ComplexShape.up ℤ) n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Iso.refl (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v r w} (O.obj U))
            (ComplexShape.up ℤ) n))
        (ShortComplex.homologyFunctor (ModuleCat.{max u v r w} (O.obj U))) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (HomologicalComplex.shortComplexFunctor (PresheafOfModules.{max u v r w} O)
          (ComplexShape.up ℤ) n) (ShortComplex.homologyFunctorIso F) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight
        (HomologicalComplex.homologyFunctorIso (PresheafOfModules.{max u v r w} O)
          (ComplexShape.up ℤ) n).symm F
    let derivedComm :
        F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor
          (ModuleCat.{max u v r w} (O.obj U)) n ≅
        DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) n ⋙ F :=
      Localization.liftNatIso (DerivedCategory.Q)
        (HomologicalComplex.quasiIso (PresheafOfModules.{max u v r w} O) (ComplexShape.up ℤ))
        (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{max u v r w} (O.obj U))
            (ComplexShape.up ℤ) n)
        (HomologicalComplex.homologyFunctor (PresheafOfModules.{max u v r w} O)
          (ComplexShape.up ℤ) n ⋙ F)
        _ _ hcComm
    have hRU : IsIso ((RGamma.{w} O U).map g) := h U
    have hRHS : IsIso ((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max u v r w} O) n ⋙ F).map
        g) := by
      rw [← NatIso.isIso_map_iff derivedComm g]
      simp only [Functor.comp_map]
      exact Functor.map_isIso (DerivedCategory.homologyFunctor
        (ModuleCat.{max u v r w} (O.obj U)) n) _
    have heq : ((PresheafOfModules.toPresheaf O).map M).app U =
        (forget₂ (ModuleCat (O.obj U)) Ab).map ((F.map M)) := rfl
    rw [heq]
    have : IsIso (F.map M) := by
      simpa only [hMdef, Functor.comp_map] using hRHS
    exact Functor.map_isIso (forget₂ (ModuleCat (O.obj U)) Ab) _
  exact isIso_of_reflects_iso M (PresheafOfModules.toPresheaf O)

/-- The comparison maps are natural in `K`: for `g : K ⟶ K'` in `D(O)`,
`(baseChange a).map (RΓ(V, g)) ≫ comparison bc a K' = comparison bc a K ≫ RΓ(U, g)`. -/
theorem comparison_naturality (bc : BaseChangeData.{w} O) {U V : Cᵒᵖ} (a : V ⟶ U)
    {K K' : DMod.{w} O} (g : K ⟶ K') :
    (bc.baseChange a).map ((RGamma.{w} O V).map g) ≫ comparison.{w} bc a K' =
      comparison.{w} bc a K ≫ (RGamma.{w} O U).map g := by
  show (bc.baseChange a).map ((RGamma.{w} O V).map g) ≫
        ((bc.baseChangeAdj a).homEquiv _ _).symm ((restrictionNatTrans.{w} O a).app K') =
      ((bc.baseChangeAdj a).homEquiv _ _).symm ((restrictionNatTrans.{w} O a).app K) ≫
        (RGamma.{w} O U).map g
  rw [← (bc.baseChangeAdj a).homEquiv_naturality_left_symm,
    ← (bc.baseChangeAdj a).homEquiv_naturality_right_symm]
  exact congrArg _ ((restrictionNatTrans.{w} O a).naturality g)

/-- The canonical comparison maps of `bc` along a fixed `a : V ⟶ U`, assembled into a natural
transformation `RΓ(V, -) ⋙ (- ⊗^L_{O(V)} O(U)) ⟶ RΓ(U, -)`. -/
noncomputable abbrev comparisonNatTrans (bc : BaseChangeData.{w} O) {U V : Cᵒᵖ} (a : V ⟶ U) :
    (RGamma.{w} O V ⋙ bc.baseChange a) ⟶ RGamma.{w} O U where
  app K := comparison.{w} bc a K
  naturality _ _ g := comparison_naturality.{w} bc a g

/-- `Rf_*` carries the counit `Lf^* Rf_* K ⟶ K` to an isomorphism. -/
theorem RGamma_counit_isIso (bc : BaseChangeData.{w} O) (mos : MorphismOfSites.{w} bc X hX)
  (K : DMod.{w} O) :
    IsIso ((RGamma.{w} O (Opposite.op X)).map (mos.adj.counit.app K)) := by
  have := main_unit_isIso.{w} bc mos ((RGamma.{w} O (Opposite.op X)).obj K)
  have : IsIso (mos.adj.unit.app ((RGamma.{w} O (Opposite.op X)).obj K) ≫
      (RGamma.{w} O (Opposite.op X)).map (mos.adj.counit.app K)) := by
    rw [mos.adj.right_triangle_components]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left (mos.adj.unit.app _) _

/-- Assertion (3) of [Stacks, Tag 0H0R]: for every `K ∈ QC(O)` the counit `Lf^* Rf_* K ⟶ K`
is an isomorphism; equivalently every object of `QC(O)` is of the form `Lf^* P`. -/
theorem main_counit_isIso (bc : BaseChangeData.{w} O) (mos : MorphismOfSites.{w} bc X hX)
    (K : DMod.{w} O) (hK : IsQC.{w} bc K) :
    IsIso (mos.adj.counit.app K) := by
  apply RGamma_jointly_conservative.{w} (mos.adj.counit.app K)
  intro U
  set ε := mos.adj.counit.app K with hε
  set a : (Opposite.op X) ⟶ U := (hX.from U.unop).op with ha
  have hsq := comparison_naturality.{w} bc a ε
  have h1 : IsIso (comparison.{w} bc a ((𝟭 (DMod.{w} O)).obj K)) := hK a
  have h2 : IsIso (comparison.{w} bc a ((RGamma.{w} O (Opposite.op X) ⋙ mos.Lpullback).obj K)) :=
    main_Lpullback_isQC.{w} bc mos ((RGamma.{w} O (Opposite.op X)).obj K) a
  have h3 : IsIso ((RGamma.{w} O (Opposite.op X)).map ε) := RGamma_counit_isIso.{w} bc mos K
  have h3' : IsIso ((bc.baseChange a).map ((RGamma.{w} O (Opposite.op X)).map ε)) :=
    Functor.map_isIso _ _
  have hL : IsIso ((bc.baseChange a).map ((RGamma.{w} O (Opposite.op X)).map ε) ≫
      comparison.{w} bc a ((𝟭 (DMod.{w} O)).obj K)) := IsIso.comp_isIso
  rw [hsq] at hL
  exact IsIso.of_isIso_comp_left
    (comparison.{w} bc a ((RGamma.{w} O (Opposite.op X) ⋙ mos.Lpullback).obj K))
    ((RGamma.{w} O U).map ε)

/-- [Stacks, Tag 0H0R], relative to a morphism of sites `mos` over a base-change datum `bc`: the
adjunction `Lf^* ⊣ Rf_*` exhibits `Lf^*` and `Rf_*` as mutually quasi-inverse equivalences between
`D(R)` and `QC(O)`. That is, `Lf^*` lands in `QC(O)` (1), the unit is an isomorphism on all of
`D(R)` (2), and the counit is an isomorphism on all objects of `QC(O)` (3). -/
theorem main_equivalence_of_morphismOfSites (bc : BaseChangeData.{w} O)
    (mos : MorphismOfSites.{w} bc X hX) :
    (∀ P, IsQC.{w} bc (mos.Lpullback.obj P)) ∧
    (∀ P, IsIso (mos.adj.unit.app P)) ∧
    (∀ K, IsQC.{w} bc K → IsIso (mos.adj.counit.app K)) :=
  ⟨main_Lpullback_isQC.{w} bc mos, main_unit_isIso.{w} bc mos, main_counit_isIso.{w} bc mos⟩

end

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence
