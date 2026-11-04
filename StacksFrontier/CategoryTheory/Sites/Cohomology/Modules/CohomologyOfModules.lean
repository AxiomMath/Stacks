module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of modules on a ringed site, and higher direct images

Let `(C, J)` be a site and `O` a sheaf of rings on it. `GlobalSectionRing O` is the ring
`Γ(C, O)` of compatible families of sections of `O`, and `globalSectionsFunctor O` sends a
sheaf of `O`-modules to its `Γ(C, O)`-module of compatible global sections. The named
equivalences `globalSectionsEquivTerminalHom` and `globalSectionRingEquivTerminalHom`
identify these with the source's definition of global sections as maps out of the terminal
presheaf, which is what makes the construction correct on a site with no final object.

`globalModuleCohomology O n` is the `n`-th right derived functor of this module-valued
functor, and `globalModuleCohomologyIso` identifies it canonically with the cohomology of the
global sections of any injective resolution — the displayed equation of the source — while
`globalModuleCohomologyIso_hom_naturality` records that the identification is compatible with
maps of modules and of resolutions. `cohomologyFunctor` is the same construction written out
on a small site, and `exists_universal_cohomologyDeltaFunctor` is the assertion that these
functors, together with their action on morphisms, form a universal cohomological
`δ`-functor: the higher right derived functors vanish on injective objects, so Stacks 010T
applies.

For higher direct images along a morphism of ringed topoi there is nothing new to construct:
they are the right derived functors of the module pushforward
`Stacks.Sheaves.RingedToposModules.pushforwardModules`, and Mathlib's
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` already computes the right derived
functors of an arbitrary additive functor from an arbitrary injective resolution. Tag 071I is
therefore registered against those declarations rather than restated.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionsFunctor`: global sections of a sheaf of
  `O`-modules, as a module over `Γ(C, O)`.
* `Stacks.Cohomology.SiteModules.globalModuleCohomology`: its right derived functors, the
  cohomology of `O`-modules on the whole site.
* `Stacks.Cohomology.SiteModules.cohomologyFunctor`: the same on a small site, with the module
  universe equal to the site's.

## Main results

* `Stacks.Cohomology.SiteModules.globalModuleCohomologyIso` and
  `globalModuleCohomologyIso_hom_naturality`: cohomology is the cohomology of the global
  sections of an injective resolution, naturally.
* `Stacks.Cohomology.SiteModules.exists_universal_cohomologyDeltaFunctor`: the cohomology
  functors form a universal cohomological `δ`-functor.
* `Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives`: sheaves of `O`-modules on an
  arbitrary site have enough injectives once the module universe contains the site and the
  structure rings. This is what makes the derived functors above exist; it is not an
  assumption imposed on the user.

## Implementation notes

The site's objects, its morphisms, the structure sheaf of rings and the modules all live in
independent universes. For the derived functors the module universe is enlarged to
`max u v r w`: sheafification of abelian presheaves and the free modules on the lifted
representables are available there, which is what supplies the Grothendieck abelian structure
and hence enough injectives.

The source states the computation by an injective resolution as an equality of modules; a
formalisation can only give a canonical isomorphism, since the right derived functor is built
from a *chosen* resolution while the statement compares it with an *arbitrary* one. Its
naturality is the content that the equality is used for.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 071I](https://stacks.math.columbia.edu/tag/071I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe t u v r w w'

namespace Stacks.Cohomology.SiteModules

section GlobalSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w'} R)

/-- The pointwise additive group structure on the compatible global sections of a sheaf of
modules. -/
instance sectionsAddCommGroup : AddCommGroup M.sections :=
  let S : AddSubgroup (∀ X, M.val.obj X) := AddGrpCat.sectionsAddSubgroup
    (M.val.presheaf ⋙ forget₂ AddCommGrpCat AddGrpCat)
  S.toAddCommGroup

/-- Global sections of an `R`-module are a module over the ring of global sections of `R`. -/
instance sectionsModule : Module (RingCat.sectionsSubring R.obj) M.sections where
  smul r s := M.val.sectionsMk (fun X ↦ r.1 X • s.eval X) (by
    intro X Y f
    rw [M.val.map_smul, M.val.sections_property s f]
    exact congrArg (fun r ↦ r • s.eval Y) (r.2 f))
  one_smul s := Subtype.ext <| funext fun X ↦ one_smul (R.obj.obj X) (s.eval X)
  mul_smul r t s := Subtype.ext <| funext fun X ↦ mul_smul (r.1 X) (t.1 X) (s.eval X)
  smul_zero r := Subtype.ext <| funext fun X ↦ (show r.1 X • (0 : M.val.obj X) = 0 from smul_zero _)
  smul_add r s t := Subtype.ext <| funext fun X ↦ smul_add (r.1 X) (s.eval X) (t.eval X)
  add_smul r t s := Subtype.ext <| funext fun X ↦ add_smul (r.1 X) (t.1 X) (s.eval X)
  zero_smul s := Subtype.ext <| funext fun X ↦ zero_smul (R.obj.obj X) (s.eval X)

/-- The zero global section evaluates to zero on every object. -/
@[simp]
lemma sections_zero_eval (X : Cᵒᵖ) : (0 : M.sections).eval X = 0 := rfl

/-- Addition of global sections is computed objectwise. -/
@[simp]
lemma sections_add_eval (s t : M.sections) (X : Cᵒᵖ) :
    (s + t).eval X = s.eval X + t.eval X := rfl

/-- Scalar multiplication by a global section of the ring sheaf is computed objectwise. -/
@[simp]
lemma sections_smul_eval (r : RingCat.sectionsSubring R.obj) (s : M.sections) (X : Cᵒᵖ) :
    (r • s).eval X = r.1 X • s.eval X := rfl

/-- Global sections of sheaves of modules, valued in modules over the global sections of the
sheaf of rings. -/
def globalSectionsFunctor : SheafOfModules.{w'} R ⥤
    ModuleCat.{max u w'} (RingCat.sectionsSubring R.obj) where
  obj M := ModuleCat.of _ M.sections
  map f := ModuleCat.ofHom
    { toFun := SheafOfModules.sectionsMap f
      map_add' s t := Subtype.ext <| funext fun X ↦ (f.val.app X).hom.map_add _ _
      map_smul' r s := Subtype.ext <| funext fun X ↦ (f.val.app X).hom.map_smul (r.1 X) (s.eval X) }
  map_id M := by
    ext s X
    rfl
  map_comp f g := by
    ext s X
    rfl

/-- The global sections functor on sheaves of modules is additive. -/
instance globalSectionsFunctor_additive : (globalSectionsFunctor.{u, v, w, w'} R).Additive where
  map_add {X Y} f g := by
    ext s
    rfl

/-- The map on global sections induced by a morphism of sheaves of modules is computed by
applying the morphism objectwise. -/
@[simp]
lemma globalSectionsFunctor_map_eval {M N : SheafOfModules.{w'} R} (f : M ⟶ N)
    (s : M.sections) (X : Cᵒᵖ) :
    ((globalSectionsFunctor R).map f s).eval X = f.val.app X (s.eval X) := rfl

end GlobalSections

/-- **Stacks Project, Tag 071H.** The cohomology of sheaves of modules on a small site, with
scalars in the ring of global sections of the structure sheaf. -/
@[stacks 071H "cohomology of modules on the whole site", ega "0 12.1.2" "more general"]
abbrev cohomologyFunctor {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (i : ℕ) :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} (RingCat.sectionsSubring R.obj) :=
  (globalSectionsFunctor R).rightDerived i

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J RingCat.{r})

/-- The ring `Γ(C, O)` of compatible families of sections of the structure sheaf. -/
abbrev GlobalSectionRing := RingCat.sectionsSubring O.obj

/-- Global sections of an `O`-module, as compatible families on the whole site. -/
abbrev GlobalSections (M : SheafOfModules.{w} O) := M.sections

/-- Global sections of a module are maps out of the terminal presheaf of sets, as in the
source. -/
def globalSectionsEquivTerminalHom (M : SheafOfModules.{w} O) :
    GlobalSections O M ≃ Presheaf.globalSections (M.val.presheaf ⋙ forget _) :=
  (Presheaf.globalSectionsEquivSections (M.val.presheaf ⋙ forget _)).symm

/-- The scalars are the global sections of `O` in the source's terminal-presheaf
formulation. -/
def globalSectionRingEquivTerminalHom :
    GlobalSectionRing O ≃ Presheaf.globalSections (O.obj ⋙ forget RingCat) :=
  (Presheaf.globalSectionsEquivSections (O.obj ⋙ forget RingCat)).symm

/-- Forgetting the module structure recovers Mathlib's functor of compatible sections. -/
def globalSectionsFunctorForget :
    globalSectionsFunctor.{u, v, r, w} O ⋙ forget _ ≅ SheafOfModules.sectionsFunctor O :=
  Iso.refl _

/-- Evaluation of a global scalar at an object of the site. -/
def globalSectionEval (X : Cᵒᵖ) : GlobalSectionRing O →+* O.obj.obj X where
  toFun a := a.val X
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The global scalar action is the sectionwise `O`-action. -/
@[simp] theorem globalSections_smul_apply (M : SheafOfModules.{w} O)
    (a : GlobalSectionRing O) (s : GlobalSections O M) (X : Cᵒᵖ) :
    (a • s).eval X = globalSectionEval O X a • s.eval X := rfl

namespace InjectiveSetup

/-- The additive map between free modules induced by a ring map and a map of bases. -/
private def freeMapAddHom {A B : Type*} [Ring A] [Ring B] (φ : A →+* B)
    {I K : Type*} (g : I → K) : (I →₀ A) →+ (K →₀ B) :=
  (Finsupp.mapDomain.addMonoidHom g).comp (Finsupp.mapRange.addMonoidHom (φ : A →+ B))

@[simp]
private lemma freeMapAddHom_single {A B : Type*} [Ring A] [Ring B] (φ : A →+* B)
    {I K : Type*} (g : I → K) (i : I) (a : A) :
    freeMapAddHom φ g (Finsupp.single i a) = Finsupp.single (g i) (φ a) := by
  simp [freeMapAddHom, Finsupp.mapDomain_single]

private lemma freeMapAddHom_smul {A B : Type*} [Ring A] [Ring B] (φ : A →+* B)
    {I K : Type*} (g : I → K) (a : A) (x : I →₀ A) :
    freeMapAddHom φ g (a • x) = φ a • freeMapAddHom φ g x := by
  have h : Finsupp.mapRange.addMonoidHom (φ : A →+ B) (a • x) =
      φ a • Finsupp.mapRange.addMonoidHom (φ : A →+ B) x := by
    ext i; simp
  simp only [freeMapAddHom, AddMonoidHom.coe_comp, Function.comp_apply, h,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_smul]

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{r})

/-- The index set of the free module on a lifted representable. -/
private abbrev Basis (X : C) (Y : Cᵒᵖ) := ULift.{t} (Y.unop ⟶ X)

/-- The underlying abelian presheaf of the free module on a lifted representable. -/
private def generatorPresheaf (X : C) : Cᵒᵖ ⥤ AddCommGrpCat.{max u v r w} where
  obj Y := AddCommGrpCat.of (Basis.{max u v r w} X Y →₀ R.obj Y)
  map {Y _} f := AddCommGrpCat.ofHom (freeMapAddHom (R.map f).hom
    (fun g : Basis.{max u v r w} X Y ↦ ULift.up (f.unop ≫ g.down)))
  map_id _ := by ext : 1; exact Finsupp.addHom_ext fun _ _ ↦ by simp
  map_comp _ _ := by ext : 1; exact Finsupp.addHom_ext fun _ _ ↦ by simp

private instance generatorModule (X : C) (Y : Cᵒᵖ) :
    Module (R.obj Y) ((generatorPresheaf.{u, v, r, w} R X).obj Y) :=
  inferInstanceAs (Module (R.obj Y) (Basis.{max u v r w} X Y →₀ R.obj Y))

/-- Free modules on the lifted representables, used to supply a small separating family. -/
private def generator (X : C) : PresheafOfModules.{max u v r w} R :=
  PresheafOfModules.ofPresheaf (generatorPresheaf.{u, v, r, w} R X)
    (fun {_ _} f a m ↦ freeMapAddHom_smul (R.map f).hom _ a m)

/-- The map out of the free module on the representable at `X` determined by a section of `M`
over `X`. -/
private def generatorDesc {X : C} (M : PresheafOfModules.{max u v r w} R) (m : M.obj (op X)) :
    generator.{u, v, r, w} R X ⟶ M :=
  PresheafOfModules.homMk
    { app Y := AddCommGrpCat.ofHom
        (Finsupp.lift (M.obj Y) (R.obj Y) (Basis.{max u v r w} X Y)
          (fun g ↦ M.restrictₛₗ g.down.op m)).toAddMonoidHom
      naturality := by
        intro Y Z f
        apply AddCommGrpCat.hom_ext
        apply Finsupp.addHom_ext
        intro i a
        change Finsupp.lift (M.obj Z) (R.obj Z) (Basis.{max u v r w} X Z)
              (fun g ↦ M.restrictₛₗ g.down.op m)
            (freeMapAddHom (R.map f).hom
              (fun g : Basis.{max u v r w} X Y ↦ ULift.up (f.unop ≫ g.down))
              (Finsupp.single i a)) =
          M.map f (Finsupp.lift (M.obj Y) (R.obj Y) (Basis.{max u v r w} X Y)
            (fun g ↦ M.restrictₛₗ g.down.op m) (Finsupp.single i a))
        simp only [freeMapAddHom_single, Finsupp.lift_apply, Finsupp.sum_single_index,
          zero_smul, map_smul]
        rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply,
          CategoryTheory.op_comp, Quiver.Hom.op_unop, PresheafOfModules.map_comp_apply]
        rfl }
    (fun Y a x ↦ map_smul (Finsupp.lift (M.obj Y) (R.obj Y) (Basis.{max u v r w} X Y)
      (fun g ↦ M.restrictₛₗ g.down.op m)) a x)

private lemma generatorDesc_app_apply {X : C} (M : PresheafOfModules.{max u v r w} R)
    (m : M.obj (op X)) (Y : Cᵒᵖ) (x : Basis.{max u v r w} X Y →₀ R.obj Y) :
    (generatorDesc.{u, v, r, w} R M m).app Y x =
      Finsupp.lift (M.obj Y) (R.obj Y) (Basis.{max u v r w} X Y)
        (fun g ↦ M.restrictₛₗ g.down.op m) x := rfl

private lemma generatorDesc_app_single_one {X : C} (M : PresheafOfModules.{max u v r w} R)
    (m : M.obj (op X)) :
    (generatorDesc.{u, v, r, w} R M m).app (op X)
      (Finsupp.single (ULift.up (𝟙 X)) 1) = m := by
  rw [generatorDesc_app_apply, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul,
    PresheafOfModules.restrictₛₗ_apply]
  simp

private lemma generatorDesc_comp_app_single {X : C} {M N : PresheafOfModules.{max u v r w} R}
    (m : M.obj (op X)) (φ : M ⟶ N) :
    (generatorDesc.{u, v, r, w} R M m ≫ φ).app (op X)
        (Finsupp.single (ULift.up (𝟙 X)) 1) = φ.app (op X) m :=
  congrArg (φ.app (op X)) (generatorDesc_app_single_one R M m)

/-- The family of free modules on the lifted representables. -/
private def generators : ObjectProperty (PresheafOfModules.{max u v r w} R) :=
  .ofObj (generator.{u, v, r, w} R)

private theorem generators_isSeparating :
    (generators.{u, v, r, w} R).IsSeparating := by
  intro M N f g h
  apply PresheafOfModules.hom_ext
  intro X
  ext m
  exact (generatorDesc_comp_app_single R m f).symm.trans
    ((congrArg (fun k ↦ k.app X (Finsupp.single (ULift.up (𝟙 X.unop)) (1 : R.obj X)))
      (h _ ⟨X.unop⟩ (generatorDesc.{u, v, r, w} R M m))).trans
        (generatorDesc_comp_app_single R m g))

private instance : HasSeparator (PresheafOfModules.{max u v r w} R) :=
  ⟨_, (generators_isSeparating.{u, v, r, w} R).isSeparator_coproduct⟩

private instance : IsGrothendieckAbelian.{max u v r w}
    (PresheafOfModules.{max u v r w} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun D _ _ ↦ ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := D) ⋙ PresheafOfModules.toPresheaf R) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (PresheafOfModules.toPresheaf R)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R)⟩⟩⟩⟩

end InjectiveSetup

open InjectiveSetup

/-- Abelian sheaves admit sheafification in any universe containing the site. -/
theorem site_hasSheafify_addCommGrp : HasSheafify J AddCommGrpCat.{max u v w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u v w, v, u} J

/-- Sheafification in the ambient universe inverts exactly the locally bijective maps. -/
theorem site_wEqualsLocallyBijective_addCommGrp :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} := by
  have : ((equivSmallModel.{max u v w} C).inverse.inducedTopology J).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w} :=
    @smallSiteWEqualsLocallyBijective.{max u v w} (SmallModel.{max u v w} C)
      (smallCategorySmallModel.{max u v w, v, u} C) _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u v w}
    (A := AddCommGrpCat.{max u v w}) J

private theorem smallModelSheafify :
    HasSheafify ((equivSmallModel.{max u v w} C).inverse.inducedTopology J)
      AddCommGrpCat.{max u v w} :=
  @smallSiteHasSheafify.{max u v w} (SmallModel.{max u v w} C)
    (smallCategorySmallModel.{max u v w, v, u} C) _

attribute [local instance] site_hasSheafify_addCommGrp in
/-- **Abelian sheaves on any site form a Grothendieck abelian category** in any universe
containing the site.

This is the abelian-sheaf counterpart of `moduleSheavesGrothendieck`, and like
`site_hasSheafify_addCommGrp` it is obtained by transporting the small-site statement along the
equivalence with the small model of the site. -/
@[sga "4 II 6.7" "special case"]
theorem site_isGrothendieckAbelian_addCommGrp :
    IsGrothendieckAbelian.{max u v w} (Sheaf J AddCommGrpCat.{max u v w}) :=
  have : HasSheafify ((equivSmallModel.{max u v w} C).inverse.inducedTopology J)
      AddCommGrpCat.{max u v w} := smallModelSheafify
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v w} J AddCommGrpCat.{max u v w}

attribute [local instance] site_hasSheafify_addCommGrp site_isGrothendieckAbelian_addCommGrp in
/-- **Abelian sheaves on any site have enough injectives** in any universe containing the site:
they form a Grothendieck abelian category. -/
@[ega "0 12.2.1" "partial",
  sga "4 II 6.9" "Remark 6.9, special case",
  sga "4 V 0.2.1" "abelian sheaves on sites"]
theorem site_enoughInjectives_addCommGrp :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max u v w}) :=
  IsGrothendieckAbelian.enoughInjectives

attribute [local instance] site_hasSheafify_addCommGrp site_isGrothendieckAbelian_addCommGrp in
/-- **`Ext`-groups of abelian sheaves on any site exist** in the universe of the morphisms of the
sheaf category, in any universe containing the site. -/
theorem site_hasExt_addCommGrp : HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max u v w}) :=
  inferInstance

/-- The category of sheaves of modules in an ambient universe is abelian. -/
instance moduleSheavesAbelian : Abelian (SheafOfModules.{max u v r w} O) := by
  have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  infer_instance

/-- Sheaves of modules in an ambient universe form a Grothendieck abelian category. -/
instance moduleSheavesGrothendieck : IsGrothendieckAbelian.{max u v r w}
    (SheafOfModules.{max u v r w} O) := by
  have := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  exact {
    hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
    ab5OfSize := ⟨fun K _ _ ↦
      (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).hasExactColimitsOfShape K⟩
    hasSeparator :=
      .of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)) }

/-- Sheaves of modules in the ambient universe have enough injectives. This is a consequence
of the generator and sheafification constructions, not an extra hypothesis. -/
@[ega "0 12.2.1" "partial", sga "4 II 6.9" "more general", sga "4 V 0.2.1" "special case"]
instance moduleSheavesEnoughInjectives :
    EnoughInjectives (SheafOfModules.{max u v r w} O) := by
  have := moduleSheavesGrothendieck.{u, v, r, w} O
  exact IsGrothendieckAbelian.enoughInjectives

/-- **Stacks Project, Tag 071H.** Cohomology of `O`-modules on the whole site, valued in
`Γ(C, O)`-modules. The independent module universe is enlarged to contain the site and the
structure rings. -/
@[stacks 071H]
def globalModuleCohomology (n : ℕ) :
    SheafOfModules.{max u v r w} O ⥤ ModuleCat.{max u v r w} (GlobalSectionRing O) :=
  (globalSectionsFunctor.{u, v, r, max u v r w} O).rightDerived n

/-- **Stacks Project, Tag 071H.** The source's equation: global module cohomology is
canonically the cohomology of the sectionwise global sections of any injective resolution,
over the ring `Γ(C, O)`. -/
@[stacks 071H]
def globalModuleCohomologyIso (M : SheafOfModules.{max u v r w} O)
    (I : InjectiveResolution M) (n : ℕ) :
    (globalModuleCohomology.{u, v, r, w} O n).obj M ≅
      (((globalSectionsFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology n :=
  I.isoRightDerivedObj (globalSectionsFunctor O) n

/-- The computation is natural in the module and in a compatible map of resolutions. -/
@[reassoc]
theorem globalModuleCohomologyIso_hom_naturality
    {M N : SheafOfModules.{max u v r w} O} (f : M ⟶ N)
    (I : InjectiveResolution M) (K : InjectiveResolution N)
    (φ : I.cocomplex ⟶ K.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (n : ℕ) :
    (globalModuleCohomology.{u, v, r, w} O n).map f ≫
        (globalModuleCohomologyIso O N K n).hom =
      (globalModuleCohomologyIso O M I n).hom ≫
        ((globalSectionsFunctor O).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ _ n).map φ :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ comm (globalSectionsFunctor O) n

add_to_stacks 071H "The canonical computation from a chosen injective resolution."
  CategoryTheory.InjectiveResolution.isoRightDerivedObj

add_to_stacks 071H "Naturality of the canonical computation, including change of resolution."
  CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality

/-- **Stacks Project, Tag 071H.** The cohomology functors, with their given action on
morphisms, form a universal cohomological `δ`-functor. -/
@[stacks 071H "the universal cohomological delta-functor"]
theorem exists_universal_cohomologyDeltaFunctor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    ∃ H : DeltaFunctor (SheafOfModules.{u} R)
        (ModuleCat.{u} (RingCat.sectionsSubring R.obj)),
      (∀ i, H.functor i = cohomologyFunctor R i) ∧ H.IsUniversal := by
  refine ⟨Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (globalSectionsFunctor R), fun _ ↦ rfl, ?_⟩
  apply DeltaFunctor.isUniversal_of_isZero_injective
  intro n I hI
  exact Functor.isZero_rightDerived_obj_injective_succ _ n I

/-! ### Higher direct images of modules, Tag 071I -/

add_to_stacks 071I "the higher direct image functors" CategoryTheory.Functor.rightDerived
add_to_sga "1 XI 4.8" "more general" CategoryTheory.Functor.rightDerived
add_to_sga "2 VIII 1.2" CategoryTheory.Functor.rightDerived
add_to_sga "3 I 5.2" "more general" CategoryTheory.Functor.rightDerived
add_to_sga "4 V 2.4.2" CategoryTheory.Functor.rightDerived
add_to_sga "4 V 6.0" "more general" CategoryTheory.Functor.rightDerived
add_to_sga "4½ Arcata 1.6.5" "more general" CategoryTheory.Functor.rightDerived
add_to_sga "4½ Arcata 2.3.3" "more general" CategoryTheory.Functor.rightDerived
add_to_sga "4½ Etat_0 4.1.5" "special case" CategoryTheory.Functor.rightDerived
add_to_ega "0 11.4.3" "partial" CategoryTheory.Functor.rightDerived
add_to_ega "0 12.2.1" "more general" CategoryTheory.Functor.rightDerived
add_to_ega "0 13.2.4" "more general" CategoryTheory.Functor.rightDerived
add_to_ega "0 13.6.1" CategoryTheory.Functor.rightDerived

add_to_stacks 071I "computation using an injective resolution"
  CategoryTheory.InjectiveResolution.isoRightDerivedObj

add_to_stacks 071I "naturality of the injective-resolution computation"
  CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality

end Stacks.Cohomology.SiteModules
