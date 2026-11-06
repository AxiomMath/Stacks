module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.AcyclicityAndBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormulaInDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.ResolutionLevelFormula
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 01F1 part (1): the canonical comparison in every degree

Stacks 01F1 part (1) compares the cohomology over an open `U` of a sheaf of `R`-modules,
computed in modules and then forgotten, with the cohomology of the underlying abelian sheaf.
The clause *canonical comparison in every degree* says that the comparison carries the class of
a cocycle of an injective resolution `I` of the module sheaf to the class of its image under any
comparison `φ` of `I` with an injective resolution `J` of the underlying abelian sheaf.

`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq`
reduces that clause to one statement about the second factor of the comparison: the constructive
form of Stacks 03FD, `ModuleSheafCohomology.sectionsComparisonIso`, computed at `M` on a pair
`(I, J)` of injective resolutions by `φ`.  **This file proves that statement**, and so the
clause, unconditionally.

## Main results

* `sectionsDerivedComparison`, `sectionsDerivedComparison_fac` and
  `isIso_sectionsDerivedComparison`: the canonical map of Stacks 015M for the pair
  (forget the coefficient sheaf, sections over `U`), at a **general** sheaf of rings `R` on a
  topological space.  `Stacks.Cohomology.ModuleComparison.abelianSectionsComparison` is the same
  map for the structure sheaf of a ringed space; the acyclicity input
  `rightAcyclic_toSheaf_obj_of_injective` is already general, so nothing but the statement had to
  move.
* `sectionsTwoStepIso` and `sectionsTwoStepIso_hom_app_eq`: the degreewise isomorphism that
  invertible map assembles, and **its resolution-level formula** — the comparison is computed at
  `M` on *any* pair `(I, J)` of injective resolutions by *any* comparison `φ` extending the
  identity.  This is the part (1) analogue of
  `Stacks.Cohomology.ModulePushforwardComparison`'s
  `rightDerivedToSheafAbelianPushforwardIso_hom_app_eq`.
* `mapExactFunctor_extMk`: **the effect of `CategoryTheory.Abelian.Ext.mapExactFunctor` on a
  class presented by a cocycle of an injective resolution**, at a general exact functor of
  abelian categories.
* `extFunctorObjIsoRightDerived_succ_hom_app_comp` and
  `extFunctorObjIsoRightDerived_succ_π_comp`: **the resolution-level reading of
  `ModuleSheafCohomology.extFunctorObjIsoRightDerived` in positive degree**, for a left exact
  functor on any abelian category with `Ext` corepresented by an object.
* `comparisonIso_hom_app_succ_eq`: **the comparison of Stacks 03FD as a resolution-level formula
  in positive degree**, abstractly in the exact functor, the corepresented functor and the
  corepresentation data.  This is `comparisonIso_hom_eq_extMapComp` with both of its `Ext`
  identifications read on resolutions.
* `descOfExact` and `exists_mapResolutionComparison`: the comparison of the image of an injective
  resolution under an exact functor with an injective resolution of the image exists.  This is
  `CategoryTheory.InjectiveResolution.desc` with the source resolution weakened to a resolution
  by arbitrary objects.
* `sectionsComparisonIso_hom_app_succ_eq`: **the resolution-level formula for Stacks 03FD at
  sections over `U`**, on any pair of resolutions — the hypothesis of
  `rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq`, discharged.
* `rightDerivedSectionsForgetIso_cocycles`: **Stacks 01F1 part (1), canonical comparison in every
  degree**, unconditionally.  This is the clause, and it carries the tag.
* `sectionsComparisonIso_eq_two_step_succ`: in positive degree the comparison of Stacks 03FD *is*
  the two-step comparison of Stacks 015M.  This discharges the hypothesis of
  `rightDerivedSectionsForgetIso_cocycles_of_eq_two_step_succ`.

## Implementation notes

Both comparisons being identified are canonical:

* `ModuleSheafCohomology.sectionsComparisonIso` is `ModuleSheafCohomology.comparisonIso`, the
  unique morphism of `δ`-functors normalized in degree zero
  (`ModuleSheafCohomology.comparisonIso_hom_eq`), where the `δ`-structure on both sides is
  transported from `Ext` along `ModuleSheafCohomology.extFunctorObjIsoRightDerived`;
* `sectionsTwoStepIso` is assembled from the units of the two bounded below right derived
  functors, and its `δ`-structure, if one wants one, is the one the long exact sequence of
  `D⁺` induces through
  `Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard`.

In degree zero they agree: `sectionsForgetIso_zero_eq` normalizes the first and
`Stacks.Cohomology.ModuleComparison.rightDerivedFunctorPlus_sections_forget_iso_unit` the
second.  In positive degree the first is `DeltaFunctor.IsUniversal.isoOfIso`, built by effacement
induction, and `comparisonIso_hom_eq_extMapComp` is what replaces that construction by a formula:
the `Ext`-level map `e ↦ Ext.mk₀ b ∘ F(e)`, conjugated by the two identifications of `Ext` with
right derived functors.  Turning that formula into a statement about cocycles needs two readings,
both supplied here:

* `mapExactFunctor_extMk`, the effect of `Ext.mapExactFunctor` on `extMk`.  Mathlib has
  `CategoryTheory.InjectiveResolution.mk₀_comp_extMk` and
  `CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀`, `_comp` and `_extClass`, but nothing applying
  `Ext.mapExactFunctor` to `extMk`, and the image of an injective resolution under
  `SheafOfModules.toSheaf` is a resolution by `Ext`-acyclic objects rather than by injectives, so
  `CategoryTheory.InjectiveResolution.extEquivCohomologyClass` does not apply to it; the proof
  goes through the quasi-isomorphism `F.map I.ι'` in the localized category instead, with the
  comparison `resolutionCochainMap` of the image of `I.cochainComplex` with `J.cochainComplex`
  supplied by `ComplexShape.Embedding.liftExtend`;
* `extFunctorObjIsoRightDerived_succ_π_comp`, the reading of
  `ModuleSheafCohomology.extFunctorObjIsoRightDerived` itself.  In positive degree that
  isomorphism is `ModuleSheafCohomology.rightDerivedCoyonedaSuccIso` on the **chosen**
  resolution, transported along the corepresentation by `ModuleSheafCohomology.rightDerivedIso`,
  and the three factors of `ModuleSheafCohomology.rightDerivedCoyonedaSuccIso_app` are collapsed
  by `CategoryTheory.ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom`, by
  `homologyπ_comp_homologyFunctorIso'_hom_app` and by
  `CategoryTheory.InjectiveResolution.rightDerived_app_eq`.

Composing the two readings is `comparisonIso_hom_app_succ_eq`; the cocycle transport it produces
is `extCocycleComp`, and `extCocycleComp_comp_cyclesMap` identifies it with `φ` on cycles.  That
last identification uses only naturality **inside the abelian category of module sheaves** — of
the corepresentation `β` at the cocycle, evaluated at the identity, and of `α.inv` at `φ`.  In
particular no naturality of `ModuleSheafCohomology.tensorSheafHomIso` in the abelian presheaf is
needed, so the visibility cascade that the docstring of
`StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef` warns of is not
reopened.

`comparisonIso_hom_app_succ_eq` is stated on the pair of *chosen* resolutions, which is where
`ModuleSheafCohomology.rightDerivedCoyonedaSuccIso` lives; `sectionsComparisonIso_hom_app_succ_eq`
moves it to an arbitrary pair at no cost, because `sectionsTwoStepIso_hom_app_eq` already says
that the right-hand side is the same for every pair.

The theorems `rightDerivedSectionsForgetIso_cocycles_of_eq_two_step` and its `_succ` variant are
kept: they are the conditional forms of the clause, and their hypothesis is now discharged by
`sectionsComparisonIso_eq_two_step_succ`.  They remain untagged — a clause tag must not sit on a
statement carrying its own content as a hypothesis — and the tag sits on
`rightDerivedSectionsForgetIso_cocycles`.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.Cohomology.ModulePushforwardComparison

universe u

namespace Stacks.Cohomology.ModuleComparison

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] ModuleSheafCohomology.toSheaf_preservesFiniteColimits

/-! ### `Ext` on a pair of resolutions across an exact functor

This section closes the first of the two inputs listed in the implementation notes above: the
effect of `CategoryTheory.Abelian.Ext.mapExactFunctor` on a class presented by a cocycle of an
injective resolution.  Everything here is general — an exact functor `F : B ⥤ A` of abelian
categories, an injective resolution `I` of `Z` in `B`, an injective resolution `J` of `F.obj Z`
in `A`, and a comparison `φ` of the image of `I` with `J` extending the identity.

Nothing in the argument leaves the category of cochain complexes except the localization
bookkeeping: an `Ext`-class presented as `I.extMk t` is, by definition, the class of the
cocycle `t` composed with the formal inverse of the quasi-isomorphism `I.ι'`, so transporting it
along `F` is `CategoryTheory.LocalizerMorphism.smallShiftedHomMap` applied to a composite, which
splits by `smallShiftedHomMap_comp`, `smallShiftedHomMap_mk` and `smallShiftedHomMap_mk₀Inv`.
What is left is an identity between honest morphisms of cochain complexes, and that is
`equivHomShift_symm_extMkCocycle_comp`. -/

section ExtOnResolutions

open CategoryTheory.Abelian CochainComplex CochainComplex.HomComplex Localization

universe w w' v v' u'

/-! #### Localization bookkeeping -/

section Localizer

variable {C₁ : Type u} [Category.{v} C₁] {C₂ : Type u'} [Category.{v'} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂)
  {M : Type*} [AddMonoid M] [HasShift C₁ M] [HasShift C₂ M]
  [Φ.functor.CommShift M]
  [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M] [W₁.RespectsIso] [W₂.RespectsIso]
  {X₁ Y₁ : C₁} {X₂ Y₂ : C₂}
  [HasSmallLocalizedShiftedHom.{w} W₁ M X₁ Y₁] [HasSmallLocalizedShiftedHom.{w} W₁ M Y₁ X₁]
  [HasSmallLocalizedShiftedHom.{w} W₁ M X₁ X₁] [HasSmallLocalizedShiftedHom.{w} W₁ M Y₁ Y₁]
  [HasSmallLocalizedShiftedHom.{w'} W₂ M X₂ Y₂] [HasSmallLocalizedShiftedHom.{w'} W₂ M Y₂ X₂]
  [HasSmallLocalizedShiftedHom.{w'} W₂ M X₂ X₂] [HasSmallLocalizedShiftedHom.{w'} W₂ M Y₂ Y₂]
  (eX : Φ.functor.obj X₁ ≅ X₂) (eY : Φ.functor.obj Y₁ ≅ Y₂)

omit [HasSmallLocalizedShiftedHom.{w} W₁ M Y₁ Y₁] in
/-- **A localizer morphism carries a formal inverse to a formal inverse.**  Mathlib has the
action of `CategoryTheory.LocalizerMorphism.smallShiftedHomMap` on `mk`, `mk₀` and composites;
this is the missing case `mk₀Inv`.  It is forced by the `mk₀` case, because precomposition with
`mk₀` of the morphism is a bijection. -/
lemma smallShiftedHomMap_mk₀Inv (m₀ : M) (hm₀ : m₀ = 0) (f : X₁ ⟶ Y₁) (hf : W₁ f)
    (hFf : W₂ (Φ.functor.map f)) :
    Φ.smallShiftedHomMap eY eX (SmallShiftedHom.mk₀Inv m₀ hm₀ f hf) =
      SmallShiftedHom.mk₀Inv m₀ hm₀ (eX.inv ≫ Φ.functor.map f ≫ eY.hom)
        (MorphismProperty.RespectsIso.precomp _ _ _
          (MorphismProperty.RespectsIso.postcomp _ _ _ hFf)) := by
  subst hm₀
  apply (SmallShiftedHom.precompEquiv (eX.inv ≫ Φ.functor.map f ≫ eY.hom)
    (MorphismProperty.RespectsIso.precomp _ _ _
      (MorphismProperty.RespectsIso.postcomp _ _ _ hFf))).injective
  change SmallShiftedHom.comp _ _ (add_zero _) = SmallShiftedHom.comp _ _ (add_zero _)
  rw [SmallShiftedHom.mk₀_comp_mk₀Inv]
  rw [show SmallShiftedHom.mk₀ W₂ (0 : M) rfl (eX.inv ≫ Φ.functor.map f ≫ eY.hom) =
      Φ.smallShiftedHomMap eX eY (SmallShiftedHom.mk₀ W₁ (0 : M) rfl f) from
    (Φ.smallShiftedHomMap_mk₀ eX eY _ rfl f).symm]
  rw [← Φ.smallShiftedHomMap_comp eX eY eX, SmallShiftedHom.mk₀_comp_mk₀Inv,
    Φ.smallShiftedHomMap_mk₀ eX eX _ rfl]
  simp

end Localizer

section ShiftedHomAlgebra

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- A triple composite of shifted homomorphisms in which the outer two factors are of degree
zero and the inner right factor is an identity.  This is the shape that
`CategoryTheory.LocalizerMorphism.smallShiftedHomMap_mk` produces when the intermediate
comparison isomorphism is `Iso.refl`; recorded abstractly, where there is no defeq wall between
the two spellings of the intermediate object. -/
lemma shiftedHom_mk₀_comp_comp_mk₀ {X Y Y' T : D} {a : ℤ} (u : X ⟶ Y) (f : ShiftedHom Y Y' a)
    (v : Y' ⟶ T) :
    ShiftedHom.comp
        (ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl u)
          (ShiftedHom.comp f (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 Y')) (zero_add a)) (add_zero a))
        (ShiftedHom.mk₀ (0 : ℤ) rfl v) (zero_add a) = (u ≫ f) ≫ v⟦a⟧' := by
  rw [ShiftedHom.comp_mk₀_id, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

end ShiftedHomAlgebra

section Mk₀InvCongr

variable {D : Type u} [Category.{v} D] {W : MorphismProperty D} {M : Type*} [AddMonoid M]
  [HasShift D M] [W.IsCompatibleWithShift M] [W.RespectsIso] {X Y : D}
  [HasSmallLocalizedShiftedHom.{w} W M Y X]

omit [W.IsCompatibleWithShift M] in
/-- `CategoryTheory.Localization.SmallShiftedHom.mk₀Inv` depends only on the morphism, not on
the proof that it belongs to the class being inverted. -/
lemma smallShiftedHom_mk₀Inv_congr (m₀ : M) (hm₀ : m₀ = 0) (a b : X ⟶ Y) (hab : a = b)
    (ha : W a) (hb : W b) :
    SmallShiftedHom.mk₀Inv.{w} (W := W) m₀ hm₀ a ha =
      SmallShiftedHom.mk₀Inv m₀ hm₀ b hb := by
  subst hab; rfl

end Mk₀InvCongr

section QuasiIsoLocalization

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- `CategoryTheory.Localization.SmallShiftedHom.mk` is multiplicative: the class of a composite
of shifted homomorphisms of cochain complexes is the composite of the classes. -/
lemma smallShiftedHom_mk_comp {K L N : CochainComplex C ℤ} {a b c : ℤ}
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ L N]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K N]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ N N]
    (f : ShiftedHom K L a) (g : ShiftedHom L N b) (h : b + a = c) :
    (SmallShiftedHom.mk (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) f).comp
        (SmallShiftedHom.mk _ g) h =
      SmallShiftedHom.mk _ (f.comp g h) := by
  apply (SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  simp [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk, ShiftedHom.map_comp]

/-- Congruence for `CategoryTheory.Localization.SmallShiftedHom.comp`.  Stated as a lemma rather
than used through `rw` because the two factors cross the junction between a functor applied to a
single complex and the single complex of its value, where a rewrite motive is not type-correct. -/
lemma smallShiftedHom_comp_congr {K L N : CochainComplex C ℤ} {a b c : ℤ}
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ L N]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K N]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ N N]
    (α α' : SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) K L a)
    (β β' : SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) L N b)
    (hα : α = α') (hβ : β = β') (h : b + a = c) :
    SmallShiftedHom.comp α β h = SmallShiftedHom.comp α' β' h := by
  subst hα; subst hβ; rfl

/-- **Factorizing a formal inverse.**  If `a ≫ ψ = b` with `a` and `b` quasi-isomorphisms, then
the formal inverse of `a` is `ψ` followed by the formal inverse of `b`.  This is what replaces
the formal inverse of the image of the augmentation of one resolution by the comparison of
resolutions followed by the formal inverse of the augmentation of the other. -/
lemma smallShiftedHom_mk₀Inv_eq_mk₀_comp {K K' L : CochainComplex C ℤ}
    (a : L ⟶ K) (ψ : K ⟶ K') (b : L ⟶ K')
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ L L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K K]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K K']
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K' L]
    [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K' K']
    (hab : a ≫ ψ = b)
    (ha : HomologicalComplex.quasiIso C (ComplexShape.up ℤ) a)
    (hb : HomologicalComplex.quasiIso C (ComplexShape.up ℤ) b) :
    SmallShiftedHom.mk₀Inv (0 : ℤ) rfl a ha =
      SmallShiftedHom.comp (SmallShiftedHom.mk₀
          (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (0 : ℤ) rfl ψ)
        (SmallShiftedHom.mk₀Inv (0 : ℤ) rfl b hb) (zero_add _) := by
  apply (SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀Inv, SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp_mk₀]
  congr 1
  rw [← cancel_epi (isoOfHom DerivedCategory.Q _ a ha).hom, Iso.hom_inv_id, isoOfHom_hom,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, hab, ← isoOfHom_hom _ _ b hb,
    Iso.hom_inv_id]

end QuasiIsoLocalization

/-! #### Cocycles along an additive functor -/

section CocycleMap

variable {B : Type u} [Category.{v} B] [Preadditive B]
  {A : Type u'} [Category.{v'} A] [Preadditive A]
  (F : B ⥤ A) [F.Additive]
  {K L : CochainComplex B ℤ} {n : ℤ}

/-- **A cocycle pushed along an additive functor.**  `CochainComplex.HomComplex.Cochain.map`
degreewise, which is again a cocycle because `CochainComplex.HomComplex.δ_map` commutes the
differential of the Hom complex with the functor. -/
def cocycleMap (x : Cocycle K L n) :
    Cocycle ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
  Cocycle.mk (x.1.map F) (n + 1) rfl (by simp [δ_map])

/-- **`cocycleMap` is the action of the functor on the morphism a cocycle corresponds to.**  The
identification `CochainComplex.HomComplex.Cocycle.equivHomShift` of cocycles of degree `n` with
morphisms into the `n`-fold shift commutes with an additive functor, because the components of
the commutation isomorphism of `Functor.mapHomologicalComplex` with the shift are identities. -/
lemma cocycleMap_equivHomShift_symm (x : Cocycle K L n) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Cocycle.equivHomShift.symm x) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L =
      Cocycle.equivHomShift.symm (cocycleMap F x) := by
  ext p
  simp [Cocycle.equivHomShift_symm_apply, cocycleMap,
    Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]

end CocycleMap

/-! #### The comparison of the image of a resolution with a resolution of the image -/

section Resolutions

variable {B : Type u} [Category.{v} B] [Abelian B]
  {A : Type u'} [Category.{v'} A] [Abelian A]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {Z : B} (I : InjectiveResolution Z) (J : InjectiveResolution (F.obj Z))
  (φ : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ⟶ J.cocomplex)

/-- The degree `k` component of `resolutionRestrictionMap`, given a name so that its type
ascription is the clean spelling: the restriction of the image of `I.cochainComplex` to `ℕ` in
degree `k` is the image of `I.cocomplex.X k` only up to the structural isomorphisms, across which
`Category.assoc` does not rewrite. -/
def resolutionRestrictionComp (k : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).restriction
      ComplexShape.embeddingUpNat).X k ⟶ J.cocomplex.X k :=
  (HomologicalComplex.restrictionXIso
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex)
      ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl).hom ≫
    F.map (I.cochainComplexXIso (k : ℤ) k rfl).hom ≫ φ.f k

/-- The comparison `φ` read on the restriction to `ℕ` of the image of `I.cochainComplex`. -/
def resolutionRestrictionMap :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).restriction
      ComplexShape.embeddingUpNat) ⟶ J.cocomplex where
  f k := resolutionRestrictionComp F I J φ k
  comm' k l (hkl : (ComplexShape.up ℕ).Rel k l) := by
    have hkl' : k + 1 = l := hkl
    rw [HomologicalComplex.restriction_d_eq _ _ (i := k) (j := l)
      (i' := (k : ℤ)) (j' := (l : ℤ)) rfl rfl]
    dsimp only [resolutionRestrictionComp]
    rw [Functor.mapHomologicalComplex_obj_d, I.cochainComplex_d (k : ℤ) (l : ℤ) k l rfl rfl]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    have hc : ∀ {T : A} (u : F.obj (I.cocomplex.X l) ⟶ T),
        F.map (I.cochainComplexXIso (l : ℤ) l rfl).inv ≫
          F.map (I.cochainComplexXIso (l : ℤ) l rfl).hom ≫ u = u := fun u => by
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
    rw [hc, φ.comm k l, Functor.mapHomologicalComplex_obj_d]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- `resolutionRestrictionMap` extends to the whole of `ℤ`.  The lower boundary of the embedding
of `ℕ` in `ℤ` is the single degree `0`, and there the condition is about the differential out of
degree `-1`, where `I.cochainComplex` is zero. -/
lemma resolutionRestrictionMap_hasLift :
    ComplexShape.embeddingUpNat.HasLift (resolutionRestrictionMap F I J φ) := by
  rintro (_ | m) hj i' hi'
  · have hi'' : i' = -1 := by
      have h0 : i' + 1 = (0 : ℤ) := hi'
      lia
    subst hi''
    rw [Functor.mapHomologicalComplex_obj_d,
      show I.cochainComplex.d (-1) (ComplexShape.embeddingUpNat.f 0) = 0 from
        (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by lia)).eq_of_src _ _,
      Functor.map_zero]
    exact Limits.zero_comp
  · exact absurd hj (ComplexShape.embeddingUpNat.not_boundaryGE_next
      (show (ComplexShape.up ℕ).Rel m (m + 1) from rfl))

/-- **The comparison `φ`, on cochain complexes indexed by `ℤ`.**  The image under `F` of the
`ℤ`-indexed form of the resolution `I` maps to the `ℤ`-indexed form of `J`, by `φ` in
nonnegative degrees and by zero elsewhere. -/
def resolutionCochainMap : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex ⟶
    J.cochainComplex :=
  ComplexShape.embeddingUpNat.liftExtend (resolutionRestrictionMap F I J φ)
    (resolutionRestrictionMap_hasLift F I J φ)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The components of `resolutionCochainMap` in nonnegative degrees. -/
lemma resolutionCochainMap_f (k : ℕ) :
    (resolutionCochainMap F I J φ).f (k : ℤ) =
      F.map (I.cochainComplexXIso (k : ℤ) k rfl).hom ≫ φ.f k ≫
        (J.cochainComplexXIso (k : ℤ) k rfl).inv := by
  rw [resolutionCochainMap, ComplexShape.embeddingUpNat.liftExtend_f _ _
    (i := k) (i' := (k : ℤ)) rfl]
  dsimp [resolutionRestrictionMap, resolutionRestrictionComp,
    HomologicalComplex.restrictionXIso, InjectiveResolution.cochainComplexXIso]
  cat_disch

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- **`resolutionCochainMap` is compatible with the augmentations.**  Both sides are morphisms
out of a single complex, so only degree `0` is at issue, and there the claim is the hypothesis
`hφ` conjugated by the structural isomorphisms. -/
lemma ι'_comp_resolutionCochainMap (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    ((F.mapCochainComplexSingleFunctor 0).app Z).inv ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι' ≫
          resolutionCochainMap F I J φ = J.ι' := by
  have hpsi0 : (resolutionCochainMap F I J φ).f (0 : ℤ) =
      F.map (I.cochainComplexXIso (0 : ℤ) 0 (by simp)).hom ≫ φ.f 0 ≫
        (J.cochainComplexXIso (0 : ℤ) 0 (by simp)).inv := resolutionCochainMap_f F I J φ 0
  have hι : I.ι'.f (0 : ℤ) ≫ (I.cochainComplexXIso (0 : ℤ) 0 (by simp)).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫ I.ι.f 0 := by
    rw [InjectiveResolution.ι'_f_zero_assoc, Iso.inv_hom_id]
    exact congrArg
      (fun u => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫ u)
      (Category.comp_id (I.ι.f 0))
  have hsplit : F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫
        I.ι.f 0) =
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫
        F.map (I.ι.f 0) := F.map_comp _ _
  have heY : (((F.mapCochainComplexSingleFunctor 0).app Z).inv).f (0 : ℤ) ≫
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj Z)).hom := by
    rw [Functor.mapCochainComplexSingleFunctor, Iso.app_inv,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hJι : J.ι'.f (0 : ℤ) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj Z)).hom ≫ J.ι.f 0 ≫
        (J.cochainComplexXIso (0 : ℤ) 0 (by simp)).inv := InjectiveResolution.ι'_f_zero J
  apply HomologicalComplex.from_single_hom_ext (j := (0 : ℤ))
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, hpsi0, ← Functor.map_comp_assoc, hι, hsplit,
    Category.assoc, ← Category.assoc _ (F.map (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 Z).hom), heY, hJι, ← hφ]
  exact congrArg
    (fun u => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj Z)).hom ≫ u)
    (Category.assoc (F.map (I.ι.f 0)) (φ.f 0)
      (J.cochainComplexXIso (0 : ℤ) 0 (by simp)).inv).symm

/-- The image of an injective resolution under an exact functor is cohomologically concentrated
in degree zero.  Needed so that `CategoryTheory.HasExt` supplies the smallness instances for
shifted homomorphisms out of and into it. -/
instance isLE_mapHomologicalComplex_cochainComplex :
    CochainComplex.IsLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) 0 := by
  simp only [← HomologicalComplex.isSupported_iff_of_quasiIso
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι')]
  infer_instance

/-- The cocycle of the Hom complex of `I.cochainComplex` attached to a cocycle
`t : Wo ⟶ I.cocomplex.X n` of `I.cocomplex`.  This is the cocycle whose class is
`CategoryTheory.InjectiveResolution.extMk t`. -/
def extMkCocycle {Wo : B} {n m : ℕ} (t : Wo ⟶ I.cocomplex.X n) (hm : n + 1 = m)
    (ht : t ≫ I.cocomplex.d n m = 0) :
    Cocycle ((CochainComplex.singleFunctor B 0).obj Wo) I.cochainComplex (n : ℤ) :=
  Cocycle.fromSingleMk (t ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add (n : ℤ)) m (by lia)
    (by simp [I.cochainComplex_d _ _ n m rfl rfl, reassoc_of% ht])

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The image of a cocycle of `I.cocomplex` under `F`, followed by `φ`, is a cocycle of
`J.cocomplex`. -/
lemma extMk_map_comp_eq_zero {Wo : B} {n m : ℕ} (t : Wo ⟶ I.cocomplex.X n) (_hm : n + 1 = m)
    (ht : t ≫ I.cocomplex.d n m = 0) :
    (F.map t ≫ φ.f n) ≫ J.cocomplex.d n m = 0 := by
  rw [Category.assoc, φ.comm n m, Functor.mapHomologicalComplex_obj_d,
    ← Functor.map_comp_assoc, ht, Functor.map_zero]
  exact Limits.zero_comp

/-- The cocycle of the Hom complex of `J.cochainComplex` attached to the image of `t` followed
by the comparison `φ`. -/
def extMkCocycleMap {Wo : B} {n m : ℕ} (t : Wo ⟶ I.cocomplex.X n) (hm : n + 1 = m)
    (ht : t ≫ I.cocomplex.d n m = 0) :
    Cocycle ((CochainComplex.singleFunctor A 0).obj (F.obj Wo)) J.cochainComplex (n : ℤ) :=
  Cocycle.fromSingleMk ((F.map t ≫ φ.f n) ≫ (J.cochainComplexXIso n n rfl).inv)
    (zero_add (n : ℤ)) m (by lia)
    (by
      rw [Category.assoc, Category.assoc, J.cochainComplex_d _ _ n m rfl rfl,
        Iso.inv_hom_id_assoc, ← Category.assoc (φ.f n) (J.cocomplex.d n m), φ.comm n m,
        Functor.mapHomologicalComplex_obj_d, Category.assoc, ← Functor.map_comp_assoc, ht,
        Functor.map_zero]
      simp)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- **The cocycle identity.**  Pushing the cocycle of `t` along `F`, composing with
`resolutionCochainMap` and reading the source through the single-complex comparison gives the
cocycle of `F t ≫ φ`.  Degree zero is the only degree where either side is nonzero, and there
the claim is `resolutionCochainMap_f` after cancelling the structural isomorphisms. -/
lemma extMkCocycleMap_eq {Wo : B} {n m : ℕ} (t : Wo ⟶ I.cocomplex.X n) (hm : n + 1 = m)
    (ht : t ≫ I.cocomplex.d n m = 0) :
    ((cocycleMap F (extMkCocycle I t hm ht)).postcomp
          (resolutionCochainMap F I J φ)).precomp
        ((F.mapCochainComplexSingleFunctor 0).app Wo).inv =
      extMkCocycleMap F I J φ t hm ht := by
  dsimp only [extMkCocycle, extMkCocycleMap]
  have hcan : ∀ {Y Y' : B} (e : Y ≅ Y') {T : A} (w : F.obj Y' ⟶ T),
      F.map e.inv ≫ F.map e.hom ≫ w = w := by
    intro Y Y' e T w
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  ext p r hpr
  by_cases hp : p = 0
  · subst hp
    obtain rfl : r = (n : ℤ) := by lia
    simp only [Cocycle.precomp, Cocycle.postcomp, cocycleMap, Cocycle.mk_coe,
      Cochain.comp_v _ _ (zero_add (n : ℤ)) 0 0 (n : ℤ) (add_zero 0) (by simp),
      Cochain.comp_v _ _ (add_zero (n : ℤ)) 0 (n : ℤ) (n : ℤ) (by simp) (by simp),
      Cochain.ofHom_v, Cochain.map_v, Cocycle.fromSingleMk, Cochain.fromSingleMk_v,
      Functor.mapCochainComplexSingleFunctor, Iso.app_inv,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      resolutionCochainMap_f F I J φ n, CategoryTheory.Functor.map_comp, Category.assoc, hcan]
  · simp only [Cocycle.precomp, Cocycle.postcomp, cocycleMap, Cocycle.mk_coe,
      Cochain.comp_v _ _ (zero_add (n : ℤ)) p p r (add_zero p) hpr,
      Cochain.comp_v _ _ (add_zero (n : ℤ)) p r r hpr (by simp),
      Cochain.ofHom_v, Cochain.map_v,
      Cocycle.fromSingleMk, Cochain.fromSingleMk_v_eq_zero _ _ _ _ _ hp,
      Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

variable [HasExt.{w} B] [HasExt.{w'} A]

/-- A single complex in the composite spelling `F ⋙ singleFunctor` is cohomologically
concentrated in degree zero.  The spelling matters: instance search is keyed syntactically, and
`CategoryTheory.LocalizerMorphism.smallShiftedHomMap` produces this spelling. -/
instance isGE_comp_singleFunctor (Wo : B) :
    CochainComplex.IsGE ((F ⋙ CochainComplex.singleFunctor A 0).obj Wo) 0 :=
  inferInstanceAs (CochainComplex.IsGE ((CochainComplex.singleFunctor A 0).obj (F.obj Wo)) 0)

/-- A single complex in the composite spelling `F ⋙ singleFunctor` is cohomologically
concentrated in degree zero. -/
instance isLE_comp_singleFunctor (Wo : B) :
    CochainComplex.IsLE ((F ⋙ CochainComplex.singleFunctor A 0).obj Wo) 0 :=
  inferInstanceAs (CochainComplex.IsLE ((CochainComplex.singleFunctor A 0).obj (F.obj Wo)) 0)

/-- Smallness of shifted homomorphisms from a single complex to the image of the resolution. -/
instance hasSmallLocalizedShiftedHom_single_mapCochainComplex (Wo : B) :
    HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ℤ
      ((F ⋙ CochainComplex.singleFunctor A 0).obj Wo)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) :=
  HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0

/-- Smallness of shifted homomorphisms from the image of the resolution to a single complex. -/
instance hasSmallLocalizedShiftedHom_mapCochainComplex_single (Wo : B) :
    HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ℤ
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex)
      ((F ⋙ CochainComplex.singleFunctor A 0).obj Wo) :=
  HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0

/-- Smallness of shifted homomorphisms from the image of the resolution to the resolution of the
image. -/
instance hasSmallLocalizedShiftedHom_mapCochainComplex_cochainComplex :
    HasSmallLocalizedShiftedHom.{w'} (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ℤ
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) J.cochainComplex :=
  HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [HasExt.{w} B] [HasExt.{w'} A] in
/-- **The shifted-homomorphism identity underlying `mapExactFunctor_extMk`.**  The morphism that
the cocycle of `t` becomes after `F`, read through the single-complex comparison and followed by
`resolutionCochainMap`, is the morphism of the cocycle of `F t ≫ φ`.  This is
`cocycleMap_equivHomShift_symm` followed by `extMkCocycleMap_eq`. -/
lemma equivHomShift_symm_extMkCocycle_comp
    {Wo : B} {n m : ℕ} (t : Wo ⟶ I.cocomplex.X n) (hm : n + 1 = m)
    (ht : t ≫ I.cocomplex.d n m = 0) :
    (((F.mapCochainComplexSingleFunctor 0).app Wo).inv ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm (extMkCocycle I t hm ht))
          (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
        (resolutionCochainMap F I J φ)⟦(n : ℤ)⟧' =
      Cocycle.equivHomShift.symm (extMkCocycleMap F I J φ t hm ht) := by
  rw [ShiftedHom.map, cocycleMap_equivHomShift_symm, Category.assoc,
    ← Cocycle.equivHomShift_symm_postcomp, ← Cocycle.equivHomShift_symm_precomp,
    extMkCocycleMap_eq F I J φ t hm ht]

/-- **`CategoryTheory.Abelian.Ext.mapExactFunctor` on a class presented by a cocycle.**  For an
exact `F`, an injective resolution `I` of `Z`, an injective resolution `J` of `F.obj Z` and a
comparison `φ` of the image of `I` with `J` extending the identity, the class of a cocycle `t`
of `I` is carried to the class of the cocycle `F t ≫ φ` of `J`.

This is the input that turns `comparisonIso_hom_eq_extMapComp` into a resolution-level formula
for the comparison of Stacks 03FD; see the implementation notes of this file.  Mathlib has
`CategoryTheory.InjectiveResolution.extMk_comp_mk₀`, which moves the resolution inside one
abelian category, and `CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀`, `_comp` and `_extClass`,
but nothing applying `Ext.mapExactFunctor` to `extMk`: the image of an injective resolution
under an exact functor is a resolution by `Ext`-acyclic objects rather than by injectives, so
`CategoryTheory.InjectiveResolution.extEquivCohomologyClass` does not apply to it.  The proof
instead goes through `resolutionCochainMap`, the comparison of the image of `I.cochainComplex`
with `J.cochainComplex`, whose formal inverse of the augmentation is factorized by
`smallShiftedHom_mk₀Inv_eq_mk₀_comp`. -/
theorem mapExactFunctor_extMk (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    {Wo : B} {n m : ℕ} (t : Wo ⟶ I.cocomplex.X n) (hm : n + 1 = m)
    (ht : t ≫ I.cocomplex.d n m = 0) :
    (I.extMk t m hm ht).mapExactFunctor F =
      J.extMk (F.map t ≫ φ.f n) m hm (extMk_map_comp_eq_zero F I J φ t hm ht) := by
  have hI : HomologicalComplex.quasiIso B (ComplexShape.up ℤ) I.ι' :=
    (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  have hJ : HomologicalComplex.quasiIso A (ComplexShape.up ℤ) J.ι' :=
    (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  have hFI : HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι') :=
    (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).map _ hI
  have ha : HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
      (((F.mapCochainComplexSingleFunctor 0).app Z).inv ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι') :=
    MorphismProperty.RespectsIso.precomp _ _ _ hFI
  have hL : Ext.mapExactFunctor F (I.extMk t m hm ht) =
      (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
          (ComplexShape.up ℤ)).smallShiftedHomMap
        ((F.mapCochainComplexSingleFunctor 0).app Wo)
        ((F.mapCochainComplexSingleFunctor 0).app Z)
        (SmallShiftedHom.comp
          (SmallShiftedHom.mk (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
            (Cocycle.equivHomShift.symm (extMkCocycle I t hm ht)))
          (SmallShiftedHom.mk₀Inv (0 : ℤ) rfl I.ι' hI) (zero_add _)) := rfl
  have h1 := (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).smallShiftedHomMap_comp
    ((F.mapCochainComplexSingleFunctor 0).app Wo)
    (Iso.refl ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex))
    ((F.mapCochainComplexSingleFunctor 0).app Z)
    (SmallShiftedHom.mk (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
      (Cocycle.equivHomShift.symm (extMkCocycle I t hm ht)))
    (SmallShiftedHom.mk₀Inv (0 : ℤ) rfl I.ι' hI) (zero_add ((n : ℤ)))
  have h2 := smallShiftedHomMap_mk₀Inv (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)) ((F.mapCochainComplexSingleFunctor 0).app Z)
    (Iso.refl ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex))
    (0 : ℤ) rfl I.ι' hI hFI
  have h3 := (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).smallShiftedHomMap_mk
    ((F.mapCochainComplexSingleFunctor 0).app Wo)
    (Iso.refl ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex))
    (Cocycle.equivHomShift.symm (extMkCocycle I t hm ht))
  have hcid : ((F.mapCochainComplexSingleFunctor 0).app Z).inv ≫
      (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).functor.map
          I.ι' ≫
        (Iso.refl ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex)).hom =
      ((F.mapCochainComplexSingleFunctor 0).app Z).inv ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι' :=
    congrArg (fun g => ((F.mapCochainComplexSingleFunctor 0).app Z).inv ≫ g)
      (Category.comp_id ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι'))
  have h2' := h2.trans (smallShiftedHom_mk₀Inv_congr (0 : ℤ) rfl _ _ hcid _ ha)
  have h4 := smallShiftedHom_mk₀Inv_eq_mk₀_comp
    (((F.mapCochainComplexSingleFunctor 0).app Z).inv ≫
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι')
    (resolutionCochainMap F I J φ) J.ι'
    ((Category.assoc _ _ _).trans (ι'_comp_resolutionCochainMap F I J φ hφ)) ha hJ
  refine hL.trans (h1.trans ?_)
  refine (smallShiftedHom_comp_congr _ _ _ _ h3 h2' _).trans ?_
  refine (smallShiftedHom_comp_congr _ _ _ _ rfl h4 _).trans ?_
  refine (SmallShiftedHom.comp_assoc _ _ _ _ (zero_add ((n : ℤ))) (zero_add (0 : ℤ))
    (by simp)).symm.trans ?_
  refine (smallShiftedHom_comp_congr _ _ _ _
    (smallShiftedHom_mk_comp _ _ (zero_add ((n : ℤ)))) rfl _).trans ?_
  refine (smallShiftedHom_comp_congr _ _ _ _
    (congrArg (SmallShiftedHom.mk _) ?_) rfl _).trans rfl
  exact (shiftedHom_mk₀_comp_comp_mk₀ _ _ _).trans
    (equivHomShift_symm_extMkCocycle_comp F I J φ t hm ht)

end Resolutions

end ExtOnResolutions

/-! ### The resolution-level reading of `extFunctorObjIsoRightDerived`

This section closes the second of the two inputs listed in the implementation notes: the reading,
on an injective resolution, of the identification
`ModuleSheafCohomology.extFunctorObjIsoRightDerived` of `Ext` out of a corepresenting object with
the right derived functors of the corepresented functor.  In positive degree that identification
is `ModuleSheafCohomology.rightDerivedCoyonedaSuccIso` on the *chosen* resolution, transported
along the corepresentation by `ModuleSheafCohomology.rightDerivedIso`, and nothing here is
specific to sheaves: everything is stated for a left exact `H : A ⥤ Ab` corepresented by an
object `X` of an abelian category with `Ext`.

The final theorem of the section, `comparisonIso_hom_app_succ_eq`, is
`comparisonIso_hom_eq_extMapComp` turned into a resolution-level formula: it combines this
reading on both sides with `mapExactFunctor_extMk` and
`CategoryTheory.InjectiveResolution.mk₀_comp_extMk`.  The only input it needs beyond those is the
naturality of the corepresentation `β` **in the abelian category `B`**, which is free; no
naturality of `ModuleSheafCohomology.tensorSheafHomIso` in the abelian presheaf is involved, and
so the visibility cascade that `ModuleCohomologyComparisonDef` warns of is not reopened.

Every reassociation is written as a term against one of the bracket helpers below.  A `rw` cannot
be used: `(ModuleSheafCohomology.extLeftHomologyData I X n).H` and
`(ModuleSheafCohomology.extFunctorObj X (n + 1)).obj Z` are definitionally equal but not
syntactically so, and a rewrite motive built at `instances` transparency is not type-correct
across that junction. -/

section ExtReading

open CategoryTheory.Abelian ModuleSheafCohomology

universe v uA uB

/-! #### Bracket helpers

Each of these is an identity in an abstract category, where the junctions listed above do not
exist, so that the concrete instantiations below are pure applications. -/

section Brackets

variable {D : Type uA} [Category.{v} D]

/-- **The reassociation behind the resolution-level reading.**  The composite `a ≫ b ≫ p ≫ E`
collapses to `cm ≫ pi2 ≫ s` as soon as `E` factors through the inverse of `rIso` (`F3`), `rIso`
factors through `gIso` and `f ≫ hI` (`F4`), the transported transformation `DD` factors through
`gIso` (`F6`), and the two commutation squares `F1`, `F2`, `F7` hold. -/
theorem extReadingBracket {O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 : D}
    (a : O1 ⟶ O2) (b : O2 ⟶ O3) (p : O3 ⟶ O4) (E : O4 ⟶ O5)
    (pi1 : O1 ⟶ O6) (f : O6 ⟶ O7) (hI : O7 ⟶ O4) (piS : O2 ⟶ O7)
    (rIso : O8 ≅ O4) (gIso : O8 ≅ O6) (dd : O6 ⟶ O10) (s : O10 ⟶ O5)
    (cm : O1 ⟶ O9) (pi2 : O9 ⟶ O10) (DD : O8 ⟶ O5)
    (F1 : b ≫ p = piS ≫ hI) (F2 : a ≫ piS = pi1 ≫ f) (F3 : E = rIso.inv ≫ DD)
    (F4 : rIso.hom = gIso.hom ≫ f ≫ hI) (F6 : DD = gIso.hom ≫ dd ≫ s)
    (F7 : pi1 ≫ dd = cm ≫ pi2) :
    a ≫ b ≫ p ≫ E = cm ≫ pi2 ≫ s := by
  have h1 : f ≫ hI = gIso.inv ≫ rIso.hom := by rw [F4, Iso.inv_hom_id_assoc]
  simp [F3, F6, reassoc_of% F1, reassoc_of% F2, reassoc_of% h1, reassoc_of% F7]

/-- Cancelling two isomorphisms on the left of an identity. -/
theorem extReadingCancel {A1 A2 A3 Bo : D} (e1 : A1 ≅ A2) (e2 : A2 ≅ A3) (u : A3 ⟶ Bo)
    (w : A1 ⟶ Bo) (h : e1.hom ≫ e2.hom ≫ u = w) : u = e2.inv ≫ e1.inv ≫ w := by
  rw [← h]
  simp

/-- Two morphisms out of a common source agree once they agree after a monomorphism, in the shape
in which the cycles of a complex are compared through their inclusion. -/
theorem extReadingMono {Ko L1 V W : D} (e : Ko ⟶ L1) (u : L1 ⟶ V) (vv : Ko ⟶ V) (i : V ⟶ W)
    [Mono i] (p : L1 ⟶ W) (q : Ko ⟶ W)
    (H1 : u ≫ i = p) (H2 : vv ≫ i = q) (H3 : e ≫ p = q) : e ≫ u = vv := by
  rw [← cancel_mono i, Category.assoc, H1, H2, H3]

/-- Collapsing a three-fold composite against a family of inclusions. -/
theorem extReadingCollapse3 {O0 O1 O2 O3 V W : D}
    (a : O0 ⟶ O1) (b : O1 ⟶ O2) (c : O2 ⟶ O3) (i : O3 ⟶ W)
    (i2 : O2 ⟶ V) (i1 : O1 ⟶ V) (i0 : O0 ⟶ V) (m : V ⟶ W)
    (h3 : c ≫ i = i2 ≫ m) (h2 : b ≫ i2 = i1) (h1 : a ≫ i1 = i0) :
    (a ≫ b ≫ c) ≫ i = i0 ≫ m := by
  rw [← h1, ← h2]
  simp [h3]

/-- Collapsing a four-fold composite against a family of inclusions. -/
theorem extReadingCollapse4 {O0 O1 O2 O3 O4 V V' W : D}
    (a : O0 ⟶ O1) (b : O1 ⟶ O2) (c : O2 ⟶ O3) (d : O3 ⟶ O4) (i : O4 ⟶ W)
    (i3 : O3 ⟶ V') (i2 : O2 ⟶ V) (i1 : O1 ⟶ V) (i0 : O0 ⟶ V)
    (mc : V ⟶ V') (md : V' ⟶ W)
    (h4 : d ≫ i = i3 ≫ md) (h3 : c ≫ i3 = i2 ≫ mc) (h2 : b ≫ i2 = i1) (h1 : a ≫ i1 = i0) :
    (a ≫ b ≫ c ≫ d) ≫ i = i0 ≫ mc ≫ md := by
  rw [← h1, ← h2]
  simp [h4, reassoc_of% h3]

/-- **The assembly of the resolution-level formula.**  Reading the two sides of a comparison
`cmp` on a pair of resolutions, the identity `cmp = g1 ≫ hpsi ≫ g2inv` follows from: the
`Ext`-level formula for `cmp` (`f1`), the invertibility of the identification `Eg` of `Ext` with
the derived functor (`f2`, `f2'`), the effect of the `Ext`-level map on a class presented by a
cocycle (`f3`), the two resolution-level readings (`f4`, `f5`), and the compatibility of the
cocycle transport with the chain map (`f7`, `f8`).  Everything is cancelled against the
epimorphism `pY`, the projection of cocycles onto their `Ext` classes. -/
theorem extReadingAssemble {KY EY RD1 KX EX RD2 CX1 CX2 CX CY1 CY2 CY H1 H2 : D}
    (pY : KY ⟶ EY) (Eg : EY ⟶ RD1) (cmp : RD1 ⟶ RD2) (Einv : RD1 ⟶ EY)
    (EM : EY ⟶ EX) (EG : EX ⟶ RD2) (pX : KX ⟶ EX) (e : KY ⟶ KX)
    (u1 : KX ⟶ CX1) (u2 : CX1 ⟶ CX2) (u3 : CX2 ⟶ CX) (piL : CX ⟶ H2) (g2inv : H2 ⟶ RD2)
    (w1 : KY ⟶ CY1) (w2 : CY1 ⟶ CY2) (w3 : CY2 ⟶ CY) (piK : CY ⟶ H1)
    (g1inv : H1 ⟶ RD1) (g1 : RD1 ⟶ H1) (hpsi : H1 ⟶ H2) (cmpsi : CY ⟶ CX)
    (hpY : Epi pY) (f1 : cmp = Einv ≫ EM ≫ EG) (f2 : Eg ≫ Einv = 𝟙 EY)
    (f2' : Einv ≫ Eg = 𝟙 RD1)
    (f3 : pY ≫ EM = e ≫ pX) (f4 : pX ≫ EG = u1 ≫ u2 ≫ u3 ≫ piL ≫ g2inv)
    (f5 : pY ≫ Eg = w1 ≫ w2 ≫ w3 ≫ piK ≫ g1inv) (f6 : g1inv ≫ g1 = 𝟙 H1)
    (f7 : piK ≫ hpsi = cmpsi ≫ piL) (f8 : e ≫ u1 ≫ u2 ≫ u3 = w1 ≫ w2 ≫ w3 ≫ cmpsi) :
    cmp = g1 ≫ hpsi ≫ g2inv := by
  have hL : (pY ≫ Eg) ≫ cmp = w1 ≫ w2 ≫ w3 ≫ piK ≫ hpsi ≫ g2inv := by
    rw [f1]
    simp [reassoc_of% f2, reassoc_of% f3, f4, reassoc_of% f8, ← reassoc_of% f7]
  have hR : (pY ≫ Eg) ≫ g1 ≫ hpsi ≫ g2inv = w1 ≫ w2 ≫ w3 ≫ piK ≫ hpsi ≫ g2inv := by
    rw [f5]
    simp [reassoc_of% f6]
  have := hpY
  have : IsSplitEpi Eg := IsSplitEpi.mk' ⟨Einv, f2'⟩
  have : Epi (pY ≫ Eg) := epi_comp _ _
  exact (cancel_epi (pY ≫ Eg)).1 (hL.trans hR.symm)

end Brackets

/-! #### `homologyπ` through the short complex in three degrees -/

section Bridge

variable {C : Type uA} [Category.{v} C] [Abelian C]

/-- **`HomologicalComplex.homologyπ` through `HomologicalComplex.homologyFunctorIso'`.**  The
identification of the degree `j` homology of a complex with the homology of its short complex in
degrees `i, j, k` carries the projection of the cycles to the projection of the cycles of that
short complex.  `HomologicalComplex.homologyFunctorIso'` is `HomologicalComplex.natIsoSc'` on
homology, so this is `CategoryTheory.ShortComplex.homologyπ_naturality`; it is the extra lemma
bridging `HomologicalComplex.homologyπ` and
`CategoryTheory.ShortComplex.LeftHomologyData.π`. -/
theorem homologyπ_comp_homologyFunctorIso'_hom_app (c : ComplexShape ℕ)
    (K : HomologicalComplex C c) (i j k : ℕ) (hi : c.prev j = i) (hk : c.next j = k) :
    K.homologyπ j ≫ (HomologicalComplex.homologyFunctorIso' C c i j k hi hk).hom.app K =
      (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyπ :=
  (congrArg (fun g => K.homologyπ j ≫ g)
      (Category.id_comp (ShortComplex.homologyMap (K.isoSc' i j k hi hk).hom))).trans
    (ShortComplex.homologyπ_naturality (K.isoSc' i j k hi hk).hom)

end Bridge

/-! #### The reading itself -/

section Reading

variable {A : Type uA} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]

/-- **The resolution-level reading of `ModuleSheafCohomology.extFunctorObjIsoRightDerived` in
positive degree.**  For a left exact `H : A ⥤ Ab` corepresented by `X`, the identification of
`Ext X Z (n + 1)` with `(H.rightDerived (n + 1)).obj Z` carries the class of a cocycle of the
chosen injective resolution `I` of `Z` to the class of the image of that cocycle under the
corepresentation, read on `I`.

The three factors of `ModuleSheafCohomology.rightDerivedCoyonedaSuccIso_app` are collapsed in
turn: `CategoryTheory.ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom` for
`ModuleSheafCohomology.extLeftHomologyData`, `homologyπ_comp_homologyFunctorIso'_hom_app` for the
passage to the short complex in degrees `n, n + 1, n + 2`, and
`CategoryTheory.InjectiveResolution.rightDerived_app_eq` for the transport along the
corepresentation by `ModuleSheafCohomology.rightDerivedIso`. -/
theorem extFunctorObjIsoRightDerived_succ_hom_app_comp
    (H : A ⥤ Ab.{v}) [H.Additive] [PreservesFiniteLimits H] (X : A)
    (α : H ≅ preadditiveCoyoneda.obj (op X)) (Z : A) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution Z).cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).hom ≫
        (extLeftHomologyData (injectiveResolution Z) X n).cyclesIso.hom ≫
        (extLeftHomologyData (injectiveResolution Z) X n).π ≫
        (extFunctorObjIsoRightDerived H X α (n + 1)).hom.app Z =
      HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex α.inv (ComplexShape.up ℕ)).app
            (injectiveResolution Z).cocomplex) (n + 1) ≫
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution Z).cocomplex).homologyπ (n + 1) ≫
        ((injectiveResolution Z).isoRightDerivedObj H (n + 1)).inv :=
  extReadingBracket _ _ _ _ _ _ _ _ ((rightDerivedCoyonedaSuccIso X n).app Z)
    ((injectiveResolution Z).isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) (n + 1))
    ((HomologicalComplex.homologyFunctor Ab.{v} (ComplexShape.up ℕ) (n + 1)).map
      ((NatTrans.mapHomologicalComplex α.inv (ComplexShape.up ℕ)).app
        (injectiveResolution Z).cocomplex))
    _ _ _ ((NatTrans.rightDerived α.inv (n + 1)).app Z)
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _
      (extLeftHomologyData (injectiveResolution Z) X n)).symm
    (homologyπ_comp_homologyFunctorIso'_hom_app (ComplexShape.up ℕ) _ n (n + 1) (n + 2)
      hi hk).symm
    rfl
    (rightDerivedCoyonedaSuccIso_hom_app X Z n hi hk)
    (InjectiveResolution.rightDerived_app_eq α.inv (injectiveResolution Z) (n + 1))
    (HomologicalComplex.homologyπ_naturality _ (n + 1))

/-- **The resolution-level reading, solved for the projection of the cocycles.**  This is
`extFunctorObjIsoRightDerived_succ_hom_app_comp` with the two isomorphisms identifying the
cocycles of the Hom complex with the cycles of the complex moved to the other side; it is the
form the assembly of `comparisonIso_hom_app_succ_eq` consumes. -/
theorem extFunctorObjIsoRightDerived_succ_π_comp
    (H : A ⥤ Ab.{v}) [H.Additive] [PreservesFiniteLimits H] (X : A)
    (α : H ≅ preadditiveCoyoneda.obj (op X)) (Z : A) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    (extLeftHomologyData (injectiveResolution Z) X n).π ≫
        (extFunctorObjIsoRightDerived H X α (n + 1)).hom.app Z =
      (extLeftHomologyData (injectiveResolution Z) X n).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution Z).cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex α.inv (ComplexShape.up ℕ)).app
            (injectiveResolution Z).cocomplex) (n + 1) ≫
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution Z).cocomplex).homologyπ (n + 1) ≫
        ((injectiveResolution Z).isoRightDerivedObj H (n + 1)).inv :=
  extReadingCancel _ _ _ _ (extFunctorObjIsoRightDerived_succ_hom_app_comp H X α Z n hi hk)

end Reading

/-! #### The comparison of Stacks 03FD on a cocycle -/

section CocycleTransport

variable {A : Type uA} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]
  {B : Type uB} [Category.{v} B] [Abelian B] [HasExt.{v} B] [HasInjectiveResolutions B]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The transport of cocycles underlying the comparison of Stacks 03FD.**  A cocycle
`t : Y ⟶ I.cocomplex.X (n + 1)` of the Hom complex of an injective resolution `I` of `Z` is
carried to the cocycle `b ≫ F t ≫ φ` of the Hom complex of an injective resolution `J` of
`F.obj Z`.  That the image is again a cocycle is `extMk_map_comp_eq_zero`. -/
def extCocycleComp {Z : B} (I : InjectiveResolution Z) (J : InjectiveResolution (F.obj Z))
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    {X : A} {Y : B} (b : X ⟶ F.obj Y) (n : ℕ) :
    (homShortComplex I Y n).g.hom.ker →+ (homShortComplex J X n).g.hom.ker where
  toFun t := ⟨b ≫ F.map t.val ≫ φ.f (n + 1), by
    have ht : (t.val : Y ⟶ I.cocomplex.X (n + 1)) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 :=
      t.property
    change (b ≫ F.map t.val ≫ φ.f (n + 1)) ≫ J.cocomplex.d (n + 1) (n + 2) = 0
    rw [Category.assoc, Category.assoc,
      ← Category.assoc (F.map t.val) (φ.f (n + 1)) (J.cocomplex.d (n + 1) (n + 2)),
      extMk_map_comp_eq_zero F I J φ t.val rfl ht, Limits.comp_zero]⟩
  map_zero' := by
    apply Subtype.ext
    change b ≫ F.map (0 : Y ⟶ I.cocomplex.X (n + 1)) ≫ φ.f (n + 1) = 0
    rw [F.map_zero, Limits.zero_comp, Limits.comp_zero]
  map_add' t t' := Subtype.ext (by
    change b ≫ F.map ((t.val : Y ⟶ I.cocomplex.X (n + 1)) +
          (t'.val : Y ⟶ I.cocomplex.X (n + 1))) ≫ φ.f (n + 1) =
        b ≫ F.map (t.val : Y ⟶ I.cocomplex.X (n + 1)) ≫ φ.f (n + 1) +
          b ≫ F.map (t'.val : Y ⟶ I.cocomplex.X (n + 1)) ≫ φ.f (n + 1)
    exact (congrArg (fun g => b ≫ g ≫ φ.f (n + 1))
        (CategoryTheory.Functor.map_add (F := F) (f := (t.val : Y ⟶ I.cocomplex.X (n + 1)))
          (g := (t'.val : Y ⟶ I.cocomplex.X (n + 1))))).trans
      ((congrArg (fun g => b ≫ g)
          (Preadditive.add_comp _ _ _ (F.map (t.val : Y ⟶ I.cocomplex.X (n + 1)))
            (F.map (t'.val : Y ⟶ I.cocomplex.X (n + 1))) (φ.f (n + 1)))).trans
        (Preadditive.comp_add _ _ _ b _ _)))

omit [HasInjectiveResolutions A] [HasInjectiveResolutions B] in
/-- **The `Ext`-level map of Stacks 03FD on a class presented by a cocycle.**  The map
`e ↦ Ext.mk₀ b ∘ F e` of `extMapComp` carries the class of a cocycle `t` to the class of
`extCocycleComp` applied to `t`.  This is `mapExactFunctor_extMk` followed by
`CategoryTheory.InjectiveResolution.mk₀_comp_extMk`, which is what absorbs the unit
`ModuleSheafCohomology.compUnit` of the comparison. -/
lemma extMapComp_π {Z : B} (I : InjectiveResolution Z) (J : InjectiveResolution (F.obj Z))
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    {X : A} {Y : B} (b : X ⟶ F.obj Y) (n : ℕ) :
    (extLeftHomologyData I Y n).π ≫ (extMapComp F b (n + 1)).app Z =
      AddCommGrpCat.ofHom (extCocycleComp F I J φ b n) ≫ (extLeftHomologyData J X n).π := by
  ext t
  change (Ext.mk₀ b).comp
      ((I.extMk (t.val : Y ⟶ I.cocomplex.X (n + 1)) (n + 2) rfl t.property).mapExactFunctor F)
      (zero_add _) = _
  rw [mapExactFunctor_extMk F I J φ hφ (t.val : Y ⟶ I.cocomplex.X (n + 1)) rfl t.property,
    InjectiveResolution.mk₀_comp_extMk]
  rfl

variable (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G]
  (X : A) (α : G ≅ preadditiveCoyoneda.obj (op X)) (Y : B)
  (β : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))

omit [HasInjectiveResolutions A] [HasInjectiveResolutions B] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G] in
/-- **The cocycle transport is the corepresentation applied to the comparison of resolutions.**
Reading both sides through the inclusions of the cocycles, the transport `extCocycleComp` becomes
the degree `n + 1` component of the chain map `φ` composed with the corepresentation.

Only two naturalities are used, and both are naturality in the abelian category `B`: that of `β`
at the cocycle `t`, evaluated at the identity of `Y` — which is what recovers `β` from
`ModuleSheafCohomology.compUnit` — and that of `α.inv` at `φ.f (n + 1)`.  Naturality of
`ModuleSheafCohomology.tensorSheafHomIso` in the abelian presheaf is *not* needed. -/
lemma extCocycleComp_comp_i {Z : B} (I : InjectiveResolution Z)
    (J : InjectiveResolution (F.obj Z))
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (n : ℕ) :
    AddCommGrpCat.ofHom (extCocycleComp F I J φ (compUnit F X Y β) n) ≫
        (extLeftHomologyData J X n).i ≫ α.inv.app (J.cocomplex.X (n + 1)) =
      (extLeftHomologyData I Y n).i ≫
        (compCorepresentation F G X α Y β).inv.app (I.cocomplex.X (n + 1)) ≫
          G.map (φ.f (n + 1)) := by
  ext t
  have hβ : β.hom.app (I.cocomplex.X (n + 1)) (t.val : Y ⟶ I.cocomplex.X (n + 1)) =
      compUnit F X Y β ≫ F.map (t.val : Y ⟶ I.cocomplex.X (n + 1)) :=
    (congrArg (fun u : Y ⟶ I.cocomplex.X (n + 1) =>
          β.hom.app (I.cocomplex.X (n + 1)) u)
        (Category.id_comp (t.val : Y ⟶ I.cocomplex.X (n + 1)))).symm.trans
      (NatTrans.naturality_apply β.hom (t.val : Y ⟶ I.cocomplex.X (n + 1)) (𝟙 Y))
  have hα : ∀ u : X ⟶ F.obj (I.cocomplex.X (n + 1)),
      α.inv.app (J.cocomplex.X (n + 1)) (u ≫ φ.f (n + 1)) =
        G.map (φ.f (n + 1)) (α.inv.app (F.obj (I.cocomplex.X (n + 1))) u) := fun u =>
    NatTrans.naturality_apply α.inv (φ.f (n + 1)) u
  change α.inv.app (J.cocomplex.X (n + 1))
      (compUnit F X Y β ≫ F.map (t.val : Y ⟶ I.cocomplex.X (n + 1)) ≫ φ.f (n + 1)) =
    G.map (φ.f (n + 1))
      (α.inv.app (F.obj (I.cocomplex.X (n + 1)))
        (β.hom.app (I.cocomplex.X (n + 1)) (t.val : Y ⟶ I.cocomplex.X (n + 1))))
  rw [hβ, ← hα]
  exact congrArg (fun u : X ⟶ J.cocomplex.X (n + 1) => α.inv.app (J.cocomplex.X (n + 1)) u)
    (Category.assoc (compUnit F X Y β) (F.map (t.val : Y ⟶ I.cocomplex.X (n + 1)))
      (φ.f (n + 1))).symm

omit [HasInjectiveResolutions A] [HasInjectiveResolutions B] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] in
/-- **The cocycle transport on cycles.**  `extCocycleComp_comp_i`, read on the cycles of the two
complexes rather than through the inclusions of the cocycles.  The inclusion of the cycles is a
monomorphism, so this is that lemma together with the compatibility of
`HomologicalComplex.cyclesMap`, `HomologicalComplex.cyclesIsoSc'` and
`CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso` with those inclusions. -/
lemma extCocycleComp_comp_cyclesMap {Z : B} (I : InjectiveResolution Z)
    (J : InjectiveResolution (F.obj Z))
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (n : ℕ) (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    AddCommGrpCat.ofHom (extCocycleComp F I J φ (compUnit F X Y β) n) ≫
        ((extLeftHomologyData J X n).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          J.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex α.inv (ComplexShape.up ℕ)).app J.cocomplex) (n + 1)) =
      (extLeftHomologyData I Y n).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op Y)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex (compCorepresentation F G X α Y β).inv
            (ComplexShape.up ℕ)).app I.cocomplex) (n + 1) ≫
        HomologicalComplex.cyclesMap
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1) :=
  extReadingMono _ _ _ (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).iCycles
      (n + 1)) _ _
    (extReadingCollapse3 _ _ _ _ _ _ _ _
      (HomologicalComplex.cyclesMap_i
        ((NatTrans.mapHomologicalComplex α.inv (ComplexShape.up ℕ)).app J.cocomplex) (n + 1))
      (HomologicalComplex.cyclesIsoSc'_inv_iCycles _ n (n + 1) (n + 2) hi hk)
      (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
        (extLeftHomologyData J X n)))
    (extReadingCollapse4 _ _ _ _ _ _ _ _ _ _ _
      (HomologicalComplex.cyclesMap_i
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1))
      (HomologicalComplex.cyclesMap_i
        ((NatTrans.mapHomologicalComplex (compCorepresentation F G X α Y β).inv
          (ComplexShape.up ℕ)).app I.cocomplex) (n + 1))
      (HomologicalComplex.cyclesIsoSc'_inv_iCycles _ n (n + 1) (n + 2) hi hk)
      (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
        (extLeftHomologyData I Y n)))
    (extCocycleComp_comp_i F G X α Y β I J φ n)

variable [EnoughInjectives B]

/-- **The comparison of Stacks 03FD as a resolution-level formula, in positive degree.**  Given a
comparison `φ` of the image under `F` of the chosen injective resolution of `M` with the chosen
injective resolution of `F.obj M`, extending the identity, the component at `M` of
`ModuleSheafCohomology.comparisonIso` in degree `n + 1` is computed on that pair by `φ`.

This is `comparisonIso_hom_eq_extMapComp` — the `Ext`-level formula — read through
`extFunctorObjIsoRightDerived_succ_π_comp` on both sides, with `extMapComp_π` for the effect of
the `Ext`-level map on a class presented by a cocycle and `extCocycleComp_comp_cyclesMap` for the
compatibility of the resulting cocycle transport with `φ`.  Degree zero is not covered and does
not need to be: there the comparison is `ModuleSheafCohomology.degreeZeroIso`. -/
theorem comparisonIso_hom_app_succ_eq
    (h : ∀ (I : B) [Injective I] (m : ℕ) (e : Ext.{v} X (F.obj I) (m + 1)), e = 0)
    (n : ℕ) (M : B)
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution M).cocomplex ⟶ (injectiveResolution (F.obj M)).cocomplex)
    (hφ : F.map ((injectiveResolution M).ι.f 0) ≫ φ.f 0 =
      (injectiveResolution (F.obj M)).ι.f 0) :
    (comparisonIso F G X α Y β h (n + 1)).hom.app M =
      ((injectiveResolution M).isoRightDerivedObj (F ⋙ G) (n + 1)).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor Ab.{v} (ComplexShape.up ℕ) (n + 1)).map φ ≫
        ((injectiveResolution (F.obj M)).isoRightDerivedObj G (n + 1)).inv := by
  have hi : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  have hk : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  exact extReadingAssemble
    (extLeftHomologyData (injectiveResolution M) Y n).π
    ((extFunctorObjIsoRightDerived (F ⋙ G) Y
      (compCorepresentation F G X α Y β) (n + 1)).hom.app M)
    _
    ((extFunctorObjIsoRightDerived (F ⋙ G) Y
      (compCorepresentation F G X α Y β) (n + 1)).inv.app M)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    inferInstance
    (NatTrans.congr_app (comparisonIso_hom_eq_extMapComp F G X α Y β h (n + 1)) M)
    ((extFunctorObjIsoRightDerived (F ⋙ G) Y
      (compCorepresentation F G X α Y β) (n + 1)).hom_inv_id_app M)
    ((extFunctorObjIsoRightDerived (F ⋙ G) Y
      (compCorepresentation F G X α Y β) (n + 1)).inv_hom_id_app M)
    (extMapComp_π F (injectiveResolution M) (injectiveResolution (F.obj M)) φ hφ
      (compUnit F X Y β) n)
    (extFunctorObjIsoRightDerived_succ_π_comp G X α (F.obj M) n hi hk)
    (extFunctorObjIsoRightDerived_succ_π_comp (F ⋙ G) Y
      (compCorepresentation F G X α Y β) M n hi hk)
    (Iso.inv_hom_id _)
    (HomologicalComplex.homologyπ_naturality
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1))
    (extCocycleComp_comp_cyclesMap F G X α Y β (injectiveResolution M)
      (injectiveResolution (F.obj M)) φ n hi hk)

end CocycleTransport

end ExtReading

/-! ### A comparison of the image of an injective resolution with an injective resolution

`CategoryTheory.InjectiveResolution.desc` descends a morphism to a cochain map between injective
resolutions; of the *source* resolution it uses only the exactness of the complex and the
monomorphism out of the resolved object.  This section records the construction with the source
weakened accordingly, so that it applies to the image of an injective resolution under an exact
functor — a resolution by `Ext`-acyclic objects, not by injectives — and reads off the existence
of the comparison `φ` that the resolution-level formulas quantify over.

Nothing here is new mathematics: it is `CategoryTheory.InjectiveResolution.descFZero`,
`descFOne` and `descFSucc` with `InjectiveResolution.exact₀` and
`InjectiveResolution.exact_succ` replaced by hypotheses, assembled by
`CochainComplex.mkHom`. -/

section DescFromExact

universe v uA uB

variable {C : Type uA} [Category.{v} C] [Abelian C] {Z : C} {K : CochainComplex C ℕ}

/-- The degree-zero component of `descOfExact`: the augmentation of the target resolution,
factored through the monomorphism `κ` by injectivity of `I.cocomplex.X 0`.  The instance
`Mono κ` is supplied by hand because the source of `I.ι.f 0` is the degree-zero term of a single
complex, which is only definitionally the resolved object. -/
def descExactFZero (κ : Z ⟶ K.X 0) (hmono : Mono κ) (I : InjectiveResolution Z) :
    K.X 0 ⟶ I.cocomplex.X 0 :=
  @Injective.factorThru C _ (I.cocomplex.X 0) Z (K.X 0) (I.injective 0) (I.ι.f 0) κ hmono

/-- `descExactFZero` extends the augmentation of the target resolution. -/
lemma comp_descExactFZero (κ : Z ⟶ K.X 0) (hmono : Mono κ) (I : InjectiveResolution Z) :
    κ ≫ descExactFZero κ hmono I = I.ι.f 0 :=
  @Injective.comp_factorThru C _ (I.cocomplex.X 0) Z (K.X 0) (I.injective 0) (I.ι.f 0) κ hmono

/-- The degree-one component of `descOfExact`, obtained from exactness of `K` at degree zero by
`CategoryTheory.ShortComplex.Exact.descToInjective`. -/
def descExactFOne (κ : Z ⟶ K.X 0) (hmono : Mono κ) (hκ : κ ≫ K.d 0 1 = 0)
    (he0 : (ShortComplex.mk κ (K.d 0 1) hκ).Exact) (I : InjectiveResolution Z) :
    K.X 1 ⟶ I.cocomplex.X 1 :=
  he0.descToInjective (descExactFZero κ hmono I ≫ I.cocomplex.d 0 1)
    (by
      change κ ≫ descExactFZero κ hmono I ≫ I.cocomplex.d 0 1 = 0
      rw [← Category.assoc, comp_descExactFZero κ hmono I]
      exact I.ι_f_zero_comp_complex_d)

/-- The commuting square in degrees zero and one. -/
lemma descExactFOne_comm (κ : Z ⟶ K.X 0) (hmono : Mono κ) (hκ : κ ≫ K.d 0 1 = 0)
    (he0 : (ShortComplex.mk κ (K.d 0 1) hκ).Exact) (I : InjectiveResolution Z) :
    descExactFZero κ hmono I ≫ I.cocomplex.d 0 1 =
      K.d 0 1 ≫ descExactFOne κ hmono hκ he0 I :=
  (he0.comp_descToInjective _ _).symm

/-- The inductive step of `descOfExact`: exactness of `K` in degree `n + 1` extends a commuting
square to the next degree. -/
def descExactFSucc
    (hes : ∀ n : ℕ, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (I : InjectiveResolution Z) (n : ℕ) (g : K.X n ⟶ I.cocomplex.X n)
    (g' : K.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : g ≫ I.cocomplex.d n (n + 1) = K.d n (n + 1) ≫ g') :
    Σ' g'' : K.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      g' ≫ I.cocomplex.d (n + 1) (n + 2) = K.d (n + 1) (n + 2) ≫ g'' :=
  ⟨(hes n).descToInjective (g' ≫ I.cocomplex.d (n + 1) (n + 2))
      (by
        change K.d n (n + 1) ≫ g' ≫ I.cocomplex.d (n + 1) (n + 2) = 0
        rw [← Category.assoc, ← w, Category.assoc, I.cocomplex.d_comp_d, Limits.comp_zero]),
    ((hes n).comp_descToInjective _ _).symm⟩

/-- **A resolution by not necessarily injective objects maps to an injective resolution.**  Let
`κ : Z ⟶ K.X 0` be a monomorphism making the cochain complex `K` a resolution of `Z` — exact in
degree zero against `κ` and exact in every positive degree — and let `I` be an injective
resolution of `Z`.  Then `K` maps to `I.cocomplex` compatibly with the augmentations.  This is
`CategoryTheory.InjectiveResolution.desc` with the source resolution weakened to the data above,
which is what the image of an injective resolution under an exact functor satisfies. -/
@[ega "0 11.5.2.2" "partial"]
def descOfExact (κ : Z ⟶ K.X 0) (hmono : Mono κ) (hκ : κ ≫ K.d 0 1 = 0)
    (he0 : (ShortComplex.mk κ (K.d 0 1) hκ).Exact)
    (hes : ∀ n : ℕ, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (I : InjectiveResolution Z) : K ⟶ I.cocomplex :=
  CochainComplex.mkHom K I.cocomplex (descExactFZero κ hmono I)
    (descExactFOne κ hmono hκ he0 I) (descExactFOne_comm κ hmono hκ he0 I)
    fun n p => descExactFSucc hes I n p.1 p.2.1 p.2.2

/-- `descOfExact` extends the augmentation of the target resolution. -/
lemma comp_descOfExact_f_zero (κ : Z ⟶ K.X 0) (hmono : Mono κ) (hκ : κ ≫ K.d 0 1 = 0)
    (he0 : (ShortComplex.mk κ (K.d 0 1) hκ).Exact)
    (hes : ∀ n : ℕ, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (I : InjectiveResolution Z) :
    κ ≫ (descOfExact κ hmono hκ he0 hes I).f 0 = I.ι.f 0 :=
  comp_descExactFZero κ hmono I

variable {A : Type uA} [Category.{v} A] [Abelian A] {B : Type uB} [Category.{v} B] [Abelian B]

/-- **The comparison of resolutions the resolution-level formulas quantify over exists.**  For an
exact functor `F`, an injective resolution `I` of `Z` and an injective resolution `J` of
`F.obj Z`, there is a cochain map from the image of `I` under `F` to `J` extending the identity
of `F.obj Z`.  Exactness of `F` makes the image of `I` a resolution of `F.obj Z`
(`CategoryTheory.ShortComplex.Exact.map` applied to `InjectiveResolution.exact₀` and
`InjectiveResolution.exact_succ`), and `descOfExact` does the rest. -/
@[ega "0 11.5.2.2" "special case"]
theorem exists_mapResolutionComparison (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {Z : B} (I : InjectiveResolution Z)
    (J : InjectiveResolution (F.obj Z)) :
    ∃ φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex,
      F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0 := by
  have hκ : F.map (I.ι.f 0) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1 = 0 := by
    change F.map (I.ι.f 0) ≫ F.map (I.cocomplex.d 0 1) = 0
    rw [← CategoryTheory.Functor.map_comp, I.ι_f_zero_comp_complex_d, F.map_zero]
  have hmono : Mono (F.map (I.ι.f 0)) := inferInstance
  have he0 := I.exact₀.map F
  have hes : ∀ n : ℕ, ((I.cocomplex.sc' n (n + 1) (n + 2)).map F).Exact :=
    fun n => (I.exact_succ n).map F
  refine ⟨descOfExact (F.map (I.ι.f 0)) hmono hκ he0 hes J, ?_⟩
  exact comp_descOfExact_f_zero
    (K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (F.map (I.ι.f 0)) hmono hκ he0 hes J

end DescFromExact

section Space

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- Sections over the open `U`, as a functor on abelian sheaves.  A reducible abbreviation for
the functor that both sides of the comparison of Stacks 01F1 part (1) derive. -/
abbrev sectionsOver :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)

/-- The unit of the bounded below right derived functor of the forgetful functor to abelian
sheaves is invertible, because that functor is exact.  Recorded as a lemma so that it can be
made a local instance: the statements below mention `singleFunctorPlusRightDerivedIso`, whose
elaboration needs it. -/
theorem isIso_toSheaf_rightDerivedFunctorPlusUnit' :
    IsIso (SheafOfModules.toSheaf R).rightDerivedFunctorPlusUnith :=
  Stacks.Cohomology.HigherDirectImage.isIso_rightDerivedFunctorPlusUnit _

attribute [local instance] isIso_toSheaf_rightDerivedFunctorPlusUnit'

/-- **The canonical map of Stacks 015M for forgetting the coefficient sheaf followed by sections
over `U`**, at a general sheaf of rings on a topological space.  It is the descent of
`Stacks.Cohomology.ModulePushforwardComparison.derivedCompositionUnitOf` along the unit of the
right derived functor of the composite. -/
def sectionsDerivedComparison :
    (SheafOfModules.toSheaf R ⋙ sectionsOver U).rightDerivedFunctorPlus ⟶
      (SheafOfModules.toSheaf R).rightDerivedFunctorPlus ⋙
        (sectionsOver U).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc _
    (SheafOfModules.toSheaf R ⋙ sectionsOver U).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} R)) _
    (derivedCompositionUnitOf (SheafOfModules.toSheaf R) (sectionsOver U))

/-- The equation characterizing `sectionsDerivedComparison`: it intertwines the unit of the
right derived functor of the composite with the composite unit of Stacks 05T2. -/
theorem sectionsDerivedComparison_fac :
    (SheafOfModules.toSheaf R ⋙ sectionsOver U).rightDerivedFunctorPlusUnith ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (sectionsDerivedComparison R U) =
      derivedCompositionUnitOf (SheafOfModules.toSheaf R) (sectionsOver U) :=
  Functor.rightDerived_fac _ _ _ _ _

/-- **Stacks 015M for sections over `U`.**  The canonical map is invertible, because the
underlying abelian sheaf of an injective sheaf of modules is right acyclic for sections over `U`
(`rightAcyclic_toSheaf_obj_of_injective`, the acyclicity input of Tag 03FD). -/
instance isIso_sectionsDerivedComparison : IsIso (sectionsDerivedComparison R U) :=
  (Functor.isIso_iff_rightAcyclic_obj_injective (SheafOfModules.toSheaf R) (sectionsOver U)
      (sectionsDerivedComparison R U) (sectionsDerivedComparison_fac R U)).2
    fun I hI => rightAcyclic_toSheaf_obj_of_injective (Opens.grothendieckTopology X) U R I hI

/-- **The two-step comparison of Stacks 01F1 part (1), degreewise.**  The isomorphism of
right derived functors that the invertible map of Stacks 015M assembles, in the shape that
`Stacks.Cohomology.ModulePushforwardComparison.derivedPlusToStandard_trans_hom_app_eq`
computes. -/
def sectionsTwoStepIso (n : ℕ) :
    (SheafOfModules.toSheaf R ⋙ sectionsOver U).rightDerived n ≅
      SheafOfModules.toSheaf R ⋙ (sectionsOver U).rightDerived n :=
  (derivedPlusToStandard (SheafOfModules.toSheaf R ⋙ sectionsOver U) n).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} R) 0)
      (Functor.isoWhiskerRight (asIso (sectionsDerivedComparison R U))
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (n : ℤ))) ≪≫
    Functor.isoWhiskerRight (singleFunctorPlusRightDerivedIso (SheafOfModules.toSheaf R))
      ((sectionsOver U).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf R) (derivedPlusToStandard (sectionsOver U) n)

/-- **The resolution-level formula for the two-step comparison of Stacks 01F1 part (1).**  The
comparison is computed at `M` on any pair of injective resolutions `(I, J)` by any comparison
`φ` of resolutions extending the identity of the underlying abelian sheaf.

This is `derivedPlusToStandard_trans_hom_app_eq`, which is abstract in the pair of functors,
instantiated at the forgetful functor and sections over `U`; the characterizing equation of the
comparison is `sectionsDerivedComparison_fac`. -/
theorem sectionsTwoStepIso_hom_app_eq (n : ℕ) (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (sectionsTwoStepIso R U n).hom.app M =
      (I.isoRightDerivedObj (SheafOfModules.toSheaf R ⋙ sectionsOver U) n).hom ≫
        ((sectionsOver U).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).map φ ≫
        (J.isoRightDerivedObj (sectionsOver U) n).inv :=
  derivedPlusToStandard_trans_hom_app_eq (SheafOfModules.toSheaf R) (sectionsOver U)
    (sectionsDerivedComparison R U) (sectionsDerivedComparison_fac R U) n I J φ hφ

/-- The augmentation of `I'` followed by degree zero of the comparison `desc (𝟙 Z) I I'` is the
augmentation of `I`. -/
private theorem desc_id_comp_ι_f_zero {C : Type*} [Category C] [Abelian C] {Z : C}
    (I I' : InjectiveResolution Z) : I'.ι.f 0 ≫ (InjectiveResolution.desc (𝟙 Z) I I').f 0 =
      I.ι.f 0 :=
  (InjectiveResolution.desc_commutes_zero _ I I').trans (Category.id_comp _)

/-- **The resolution-level formula for the comparison of Stacks 03FD, in positive degree.**  The
constructive Stacks 03FD isomorphism `ModuleSheafCohomology.sectionsComparisonIso` is computed at
`M` on *any* pair `(I, J)` of injective resolutions by *any* comparison `φ` of resolutions
extending the identity.  This is the hypothesis `hΞ` of
`rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq`, discharged.

`comparisonIso_hom_app_succ_eq` proves it on the pair of *chosen* resolutions, for a comparison
of those built from `φ` by `CategoryTheory.InjectiveResolution.desc` on both sides.  Transporting
to the given pair costs nothing extra: `sectionsTwoStepIso_hom_app_eq` already says that the
right-hand side is the same for every pair, being the two-step comparison in all cases. -/
theorem sectionsComparisonIso_hom_app_succ_eq (n : ℕ) (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (ModuleSheafCohomology.sectionsComparisonIso
        (Opens.grothendieckTopology X) R U (n + 1)).hom.app M =
      (I.isoRightDerivedObj (SheafOfModules.toSheaf R ⋙ sectionsOver U) (n + 1)).hom ≫
        ((sectionsOver U).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
            (ComplexShape.up ℕ) (n + 1)).map φ ≫
        (J.isoRightDerivedObj (sectionsOver U) (n + 1)).inv := by
  obtain ⟨ψ, hψ⟩ :
      ∃ ψ : ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex ⟶
          (injectiveResolution ((SheafOfModules.toSheaf R).obj M)).cocomplex,
        (SheafOfModules.toSheaf R).map ((injectiveResolution M).ι.f 0) ≫ ψ.f 0 =
          (injectiveResolution ((SheafOfModules.toSheaf R).obj M)).ι.f 0 := by
    refine ⟨((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (𝟙 M) I (injectiveResolution M)) ≫ φ ≫
      InjectiveResolution.desc (𝟙 ((SheafOfModules.toSheaf R).obj M))
        (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) J, ?_⟩
    change (SheafOfModules.toSheaf R).map ((injectiveResolution M).ι.f 0) ≫
        (SheafOfModules.toSheaf R).map
            ((InjectiveResolution.desc (𝟙 M) I (injectiveResolution M)).f 0) ≫
          φ.f 0 ≫ (InjectiveResolution.desc (𝟙 ((SheafOfModules.toSheaf R).obj M))
            (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) J).f 0 = _
    rw [← CategoryTheory.Functor.map_comp_assoc, desc_id_comp_ι_f_zero I (injectiveResolution M),
      ← Category.assoc ((SheafOfModules.toSheaf R).map (I.ι.f 0)) (φ.f 0) _, hφ]
    exact desc_id_comp_ι_f_zero _ _
  exact (comparisonIso_hom_app_succ_eq _ _ _ _ _ _ _ n M ψ hψ).trans
    ((sectionsTwoStepIso_hom_app_eq R U (n + 1) M (injectiveResolution M)
        (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) ψ hψ).symm.trans
      (sectionsTwoStepIso_hom_app_eq R U (n + 1) M I J φ hφ))

/-- **Stacks 01F1, part (1), canonical comparison in every degree.**  In every degree the
comparison sends a cocycle to the same cocycle in an abelian injective resolution, for any
comparison `φ` of resolutions extending the identity and any induced map `c` on cocycles.

Degree zero is `rightDerivedSectionsForgetIso_cocycles_zero`; in positive degree this is
`rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq` with its hypothesis discharged by
`sectionsComparisonIso_hom_app_succ_eq`. -/
@[stacks 01F1 "part (1), canonical comparison in every degree"]
theorem rightDerivedSectionsForgetIso_cocycles (n : ℕ) (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    let E := SheafOfModules.evaluation R (op U)
    let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
    let A := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles n) ⟶ L.cycles n)
      (_ : c ≫ L.iCycles n = G.map (K.iCycles n) ≫ A.map (φ.f n)),
      G.map (K.homologyπ n ≫ (I.isoRightDerivedObj E n).inv) ≫
          (rightDerivedSectionsForgetIso R U n).hom.app M ≫
          (J.isoRightDerivedObj A n).hom =
        c ≫ L.homologyπ n := by
  cases n with
  | zero => exact rightDerivedSectionsForgetIso_cocycles_zero R U M I J φ hφ
  | succ m =>
      exact rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq R U (m + 1) M I J φ hφ
        (sectionsComparisonIso_hom_app_succ_eq R U m M I J φ hφ)

/-- **The comparison of Stacks 03FD *is* the two-step comparison of Stacks 015M, in positive
degree.**  Both sides are canonical — the first is the unique morphism of `δ`-functors normalized
in degree zero, the second is assembled from the units of the two bounded below right derived
functors — and this identifies them.  It is the hypothesis of
`rightDerivedSectionsForgetIso_cocycles_of_eq_two_step_succ`, discharged.

Two isomorphisms of functors agree as soon as their components do, and at each `M` both are
computed on one and the same pair of resolutions: `sectionsComparisonIso_hom_app_succ_eq` for the
first and `sectionsTwoStepIso_hom_app_eq` for the second.  The pair is the chosen one and the
comparison of resolutions is the one `exists_mapResolutionComparison` produces. -/
theorem sectionsComparisonIso_eq_two_step_succ (n : ℕ) :
    ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X) R U (n + 1) =
      sectionsTwoStepIso R U (n + 1) := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  obtain ⟨φ, hφ⟩ := exists_mapResolutionComparison (SheafOfModules.toSheaf R)
    (injectiveResolution M) (injectiveResolution ((SheafOfModules.toSheaf R).obj M))
  exact (sectionsComparisonIso_hom_app_succ_eq R U n M (injectiveResolution M)
      (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) φ hφ).trans
    (sectionsTwoStepIso_hom_app_eq R U (n + 1) M (injectiveResolution M)
      (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) φ hφ).symm

/-- **Stacks 01F1, part (1), canonical comparison in every degree, granted that the comparison
of Stacks 03FD is the two-step comparison of Stacks 015M.**  In every degree the comparison
sends a cocycle to the same cocycle in an abelian injective resolution, for any comparison `φ`
of resolutions extending the identity and any induced map `c` on cocycles.

The hypothesis `hΞ` identifies two named isomorphisms and says nothing about cocycles; what it
costs is discussed in the implementation notes of this file.  Granted it, the clause follows
from `sectionsTwoStepIso_hom_app_eq` through
`rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq`. -/
theorem rightDerivedSectionsForgetIso_cocycles_of_eq_two_step (n : ℕ)
    (hΞ : ModuleSheafCohomology.sectionsComparisonIso
      (Opens.grothendieckTopology X) R U n = sectionsTwoStepIso R U n)
    (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    let E := SheafOfModules.evaluation R (op U)
    let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
    let A := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles n) ⟶ L.cycles n)
      (_ : c ≫ L.iCycles n = G.map (K.iCycles n) ≫ A.map (φ.f n)),
      G.map (K.homologyπ n ≫ (I.isoRightDerivedObj E n).inv) ≫
          (rightDerivedSectionsForgetIso R U n).hom.app M ≫
          (J.isoRightDerivedObj A n).hom =
        c ≫ L.homologyπ n := by
  refine rightDerivedSectionsForgetIso_cocycles_of_hom_app_eq R U n M I J φ hφ ?_
  rw [hΞ]
  exact sectionsTwoStepIso_hom_app_eq R U n M I J φ hφ

/-- **Stacks 01F1, part (1), canonical comparison in every degree, granted the identification
of the two comparisons in positive degree only.**  Degree zero is unconditional — it is
`rightDerivedSectionsForgetIso_cocycles_zero` — so the identification of
`ModuleSheafCohomology.sectionsComparisonIso` with `sectionsTwoStepIso` is owed only in positive
degree, which is exactly where the first is built by effacement induction and has no formula. -/
theorem rightDerivedSectionsForgetIso_cocycles_of_eq_two_step_succ
    (hΞ : ∀ m : ℕ, ModuleSheafCohomology.sectionsComparisonIso
      (Opens.grothendieckTopology X) R U (m + 1) = sectionsTwoStepIso R U (m + 1))
    (n : ℕ) (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    let E := SheafOfModules.evaluation R (op U)
    let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
    let A := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles n) ⟶ L.cycles n)
      (_ : c ≫ L.iCycles n = G.map (K.iCycles n) ≫ A.map (φ.f n)),
      G.map (K.homologyπ n ≫ (I.isoRightDerivedObj E n).inv) ≫
          (rightDerivedSectionsForgetIso R U n).hom.app M ≫
          (J.isoRightDerivedObj A n).hom =
        c ≫ L.homologyπ n := by
  cases n with
  | zero => exact rightDerivedSectionsForgetIso_cocycles_zero R U M I J φ hφ
  | succ m =>
      exact rightDerivedSectionsForgetIso_cocycles_of_eq_two_step R U (m + 1) (hΞ m) M I J φ hφ

end Space

end Stacks.Cohomology.ModuleComparison

end
