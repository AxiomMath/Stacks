module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef

/-!
# Derived sections of a sheaf of modules over an object of a locally small site

Let `(C, J)` be a site whose objects need not form a small type, `𝒪` a sheaf of rings on it and
`F` a sheaf of `𝒪`-modules. Sections of `F` over an object `U` of `C` can be derived in two
places: in the category of sheaves of `𝒪`-modules, where the sections functor
`CategoryTheory.SheafOfModules.evaluation` is module valued, and in the category of abelian
sheaves, where `CategoryTheory.Sheaf.H'` is the `Ext`-group out of the free abelian sheaf on the
representable at `U`. This file transports a vanishing statement from the second to the first:
if the cohomology of the underlying abelian sheaf of `F` over `U` vanishes in a positive degree,
then the right derived sections of `F` in that degree vanish as well.

## Main results

* `Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits`: the forgetful functor from
  sheaves of modules to abelian sheaves is exact, being sheafification after the forgetful functor
  to presheaves of modules.
* `Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`: the acyclicity behind Stacks
  03FD on such a site — the underlying abelian sheaf of an injective sheaf of modules has
  vanishing positive-degree `Ext` against every sectionwise torsion-free abelian sheaf.
* `Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`: positive-degree
  cohomology of the underlying abelian sheaf over `U` controls the right derived module-valued
  sections over `U`.

## Implementation notes

The comparison is the one of Stacks 03FD: the forgetful functor from sheaves of modules to
abelian sheaves is exact, and the two sections functors are corepresented in a compatible way,
by the sheafified extension of scalars of the free abelian presheaf on the representable at `U`
on the module side and by its sheafification on the abelian side. What makes the comparison work
is that the underlying abelian sheaf of an *injective* sheaf of modules, while not injective, is
still `Ext`-acyclic against sheafifications of sectionwise torsion-free presheaves
(`ext_eq_zero_of_isTorsionFree`), and the free abelian presheaf on a representable is one.

`ModuleSheafCohomology` proves the same comparison, but only for a site whose objects form a
small type: there the sheafification hypotheses are automatic, whereas here they must be carried
as explicit instance arguments and the `Ext`-universe is the morphism universe of the site
enlarged by the universe of the objects. The big sites of schemes are of the second kind — their
objects form a type one universe above their morphisms — so the small-site statements do not
apply to them. The ingredients that are already stated for an arbitrary site
(`ModuleSheafCohomology.isTorsionFree_sheafify`, `comparisonIso`,
`extFunctorObjIsoRightDerived`, and the extension-of-scalars adjunction on presheaves —
`tensorPresheaf`, `tensorPresheafMap`, `tensorPresheafLift`, `tensorPresheafUnit` and the
lemmas about them) are used from there; the rest is proved here. The adjunction is stated with
the universes of the site free, so it applies verbatim here even though the comparison built on
it there does not.

The acyclicity `ext_eq_zero_of_isTorsionFree` is stated with the coefficient universe and the
`Ext`-universe free, independently of the universes of the site, so that it also applies to
coefficients strictly larger than the morphisms of the site; the comparison below uses it with
the coefficients taken to be the morphism universe.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open scoped TensorProduct

universe t w v u u'

namespace CategoryTheory.SheafOfModules

/-- Sections over an object of the site are an additive functor on sheaves of modules: both the
module structure on the sections and the addition of morphisms are computed sectionwise. -/
public instance evaluation_additive {C : Type u'} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v}) (U : Cᵒᵖ) :
    (SheafOfModules.evaluation R U).Additive where
  map_add := rfl

end CategoryTheory.SheafOfModules

namespace Stacks.Cohomology.ObjectSections

/-! ### Sectionwise torsion-free abelian sheaves -/

section TorsionFree

variable {D : Type u'} [Category.{u} D] (K : GrothendieckTopology D) [HasSheafify K Ab.{v}]

/-- A subsheaf of a sectionwise torsion-free abelian sheaf is sectionwise torsion-free. -/
private lemma isTorsionFree_of_mono {F G : Sheaf K Ab.{v}} (f : F ⟶ G) [Mono f]
    (hG : ∀ X, Module.IsTorsionFree ℤ (G.obj.obj X)) (X : Dᵒᵖ) :
    Module.IsTorsionFree ℤ (F.obj.obj X) := by
  have := hG X
  exact Function.Injective.moduleIsTorsionFree (f.hom.app X)
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance) (map_zsmul _)

/-- The sheafification of the free abelian presheaf on a presheaf of types is sectionwise
torsion-free. -/
private lemma isTorsionFree_sheafify_free (Q : Dᵒᵖ ⥤ Type v) (X : Dᵒᵖ) :
    Module.IsTorsionFree ℤ (((presheafToSheaf K Ab.{v}).obj (Q ⋙ AddCommGrpCat.free)).obj.obj X) :=
  ModuleSheafCohomology.isTorsionFree_sheafify K _ (fun Y => by
    show Module.IsTorsionFree ℤ (FreeAbelianGroup (Q.obj Y))
    exact Module.Flat.isTorsionFree) X

/-- Every abelian sheaf is an epimorphic image of a sectionwise torsion-free one, namely of the
sheafification of the free abelian presheaf on its underlying presheaf of sets. -/
private lemma exists_isTorsionFree_epi (F : Sheaf K Ab.{v}) :
    ∃ (G : Sheaf K Ab.{v}) (p : G ⟶ F),
      (∀ X, Module.IsTorsionFree ℤ (G.obj.obj X)) ∧ Epi p := by
  let P := F.obj ⋙ forget Ab.{v} ⋙ AddCommGrpCat.free
  let ε : P ⟶ F.obj :=
    { app X := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun x : F.obj.obj X => x))
      naturality _ _ f := by
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro x
        show FreeAbelianGroup.lift (fun x => x)
            (FreeAbelianGroup.map (F.obj.map f) (FreeAbelianGroup.of x)) =
          F.obj.map f (FreeAbelianGroup.lift (fun x => x) (FreeAbelianGroup.of x))
        simp }
  have hε : Epi ε := by
    have (X : Dᵒᵖ) : Epi (ε.app X) := by
      rw [AddCommGrpCat.epi_iff_surjective]
      intro x
      exact ⟨FreeAbelianGroup.of x, FreeAbelianGroup.lift_apply_of _ x⟩
    exact NatTrans.epi_of_epi_app ε
  refine ⟨(presheafToSheaf K Ab.{v}).obj P,
    (presheafToSheaf K Ab.{v}).map ε ≫ (sheafificationAdjunction K Ab.{v}).counit.app F,
    isTorsionFree_sheafify_free K (F.obj ⋙ forget Ab.{v}), inferInstance⟩

end TorsionFree

/-! ### Extension of scalars of an abelian presheaf -/

section TensorPresheaf

variable {D : Type u'} [Category.{u} D] (R : Dᵒᵖ ⥤ RingCat.{v})

/-- Extension of scalars corepresents additive maps out of the original abelian presheaf,
naturally in the presheaf of modules. -/
private def tensorPresheafCoyonedaIso (P : Dᵒᵖ ⥤ Ab.{v}) :
    preadditiveCoyoneda.obj (op (ModuleSheafCohomology.tensorPresheaf R P)) ≅
      PresheafOfModules.toPresheaf R ⋙ preadditiveCoyoneda.obj (op P) :=
  NatIso.ofComponents
    (fun M => (ModuleSheafCohomology.tensorPresheafHomAddEquiv R P M).toAddCommGrpIso)
    (fun {M N} map => by
      have key : ∀ ψ : ModuleSheafCohomology.tensorPresheaf R P ⟶ M,
          ModuleSheafCohomology.tensorPresheafUnit R P ≫
              (PresheafOfModules.toPresheaf R).map (ψ ≫ map) =
            (ModuleSheafCohomology.tensorPresheafUnit R P ≫
              (PresheafOfModules.toPresheaf R).map ψ) ≫
              (PresheafOfModules.toPresheaf R).map map := by
        intro ψ
        rw [CategoryTheory.Functor.map_comp]
        exact (Category.assoc _ _ _).symm
      ext φ
      exact key φ)

end TensorPresheaf

/-! ### `Ext`-acyclicity of the underlying abelian sheaf of an injective sheaf of modules -/

section Acyclicity

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{v}] [J.WEqualsLocallyBijective Ab.{v}]
  [HasExt.{w} (Sheaf J Ab.{v})]

omit [J.WEqualsLocallyBijective Ab.{v}] [HasExt.{w} (Sheaf J Ab.{v})] in
/-- Tensoring a short exact sequence of abelian sheaves with sectionwise torsion-free last term
by a presheaf of rings preserves the inclusion on the underlying presheaves. -/
private lemma mono_tensorPresheafMap_of_shortExact
    (R : Cᵒᵖ ⥤ RingCat.{v}) (S : ShortComplex (Sheaf J Ab.{v}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono (ModuleSheafCohomology.tensorPresheafMap R S.f.hom) := by
  have := hS.mono_f
  apply PresheafOfModules.mono_of_injective
  intro X
  have := hP X
  let E := sheafToPresheaf J Ab.{v} ⋙ (evaluation Cᵒᵖ Ab.{v}).obj X
  have hE : (S.map E).Exact :=
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
      inferInstance S hS).1
  exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree
    (S.f.hom.app X).hom.toIntLinearMap (S.g.hom.app X).hom.toIntLinearMap
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
    ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp hE) (R.obj X)

omit [HasExt.{w} (Sheaf J Ab.{v})] in
/-- Morphisms to the underlying abelian sheaf of an injective sheaf of modules extend across a
short exact sequence whose last term is sectionwise torsion-free. -/
private lemma exists_extension_of_isTorsionFree
    (R : Sheaf J RingCat.{v}) (I : SheafOfModules.{v} R) [Injective I]
    (S : ShortComplex (Sheaf J Ab.{v})) (hS : S.ShortExact)
    (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X))
    (f : S.X₁ ⟶ (SheafOfModules.toSheaf R).obj I) :
    ∃ g : S.X₂ ⟶ (SheafOfModules.toSheaf R).obj I, S.f ≫ g = f := by
  have : Injective I.val := ModuleSheafCohomology.injective_forget_obj R I
  have := mono_tensorPresheafMap_of_shortExact J R.obj S hS hP
  let fp : S.X₁.obj ⟶ (PresheafOfModules.toPresheaf R.obj).obj I.val := f.hom
  let g := Injective.factorThru (ModuleSheafCohomology.tensorPresheafLift R.obj fp)
    (ModuleSheafCohomology.tensorPresheafMap R.obj S.f.hom)
  have hg : ModuleSheafCohomology.tensorPresheafMap R.obj S.f.hom ≫ g =
      ModuleSheafCohomology.tensorPresheafLift R.obj fp :=
    Injective.comp_factorThru _ _
  have key : S.f.hom ≫ ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₂.obj ≫
      (PresheafOfModules.toPresheaf R.obj).map g = fp := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (ModuleSheafCohomology.tensorPresheafUnit_naturality R.obj S.f.hom)).trans
        ((Category.assoc _ _ _).trans ((congrArg
          (ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₁.obj ≫ ·)
            (CategoryTheory.Functor.map_comp _ _ _).symm).trans ?_)))
    rw [hg]
    exact ModuleSheafCohomology.tensorPresheafUnit_comp_lift R.obj fp
  exact ⟨⟨ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₂.obj ≫
    (PresheafOfModules.toPresheaf R.obj).map g⟩, Sheaf.hom_ext key⟩

/-- **The acyclicity input of Stacks 03FD, on a site whose objects need not be small.** The
underlying abelian sheaf of an injective sheaf of modules has vanishing positive-degree `Ext`
against every sectionwise torsion-free abelian sheaf.

`ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree` is the same statement for a site whose
objects form a small type, where the sheafification and `Ext` hypotheses are automatic. Here
they are instance arguments and the coefficient universe is unconstrained. -/
public lemma ext_eq_zero_of_isTorsionFree [EnoughInjectives (Sheaf J Ab.{v})]
    (R : Sheaf J RingCat.{v}) (I : SheafOfModules.{v} R) [Injective I]
    (X : Sheaf J Ab.{v}) (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U))
    (n : ℕ) (e : Ext.{w} X ((SheafOfModules.toSheaf R).obj I) (n + 1)) : e = 0 := by
  apply ModuleSheafCohomology.ext_eq_zero_of_resolving (fun F : Sheaf J Ab.{v} =>
    ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) ?_ (exists_isTorsionFree_epi J)
    ((SheafOfModules.toSheaf R).obj I) ?_ n X hX e
  · intro F G f hf hG
    exact isTorsionFree_of_mono J f hG
  · apply ModuleSheafCohomology.ext_one_eq_zero_of_extension
    intro S hS hP f
    exact exists_extension_of_isTorsionFree J R I S hS hP f

omit [HasExt.{w} (Sheaf J Ab.{v})] in
/-- Forgetting a sheaf of modules to its underlying abelian sheaf preserves finite colimits: it
is sheafification after the forgetful functor to presheaves of modules, up to the natural
isomorphism `PresheafOfModules.sheafificationCompToSheaf`, and sheafification is a left
adjoint. -/
public lemma toSheaf_preservesFiniteColimits (R : Sheaf J RingCat.{v}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) := by
  let sheafification := PresheafOfModules.sheafification (𝟙 R.obj)
  let adjunction := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let counitIso := asIso adjunction.counit
  have composite : PreservesFiniteColimits (sheafification ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  have : PreservesColimitsOfSize.{0, 0} sheafification :=
    adjunction.leftAdjoint_preservesColimits
  refine ⟨fun {index} _ _ => ⟨fun {diagram} => ?_⟩⟩
  let forgetful := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have comparison : (diagram ⋙ forgetful) ⋙ sheafification ≅ diagram :=
    NatIso.ofComponents (fun point => counitIso.app (diagram.obj point)) fun map =>
      counitIso.hom.naturality (diagram.map map)
  have : PreservesColimit (diagram ⋙ forgetful)
      (sheafification ⋙ SheafOfModules.toSheaf R) :=
    (composite.preservesFiniteColimits index).preservesColimit
  have : PreservesColimit ((diagram ⋙ forgetful) ⋙ sheafification)
      (SheafOfModules.toSheaf R) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves sheafification (colimit.isColimit (diagram ⋙ forgetful)))
      (isColimitOfPreserves (sheafification ⋙ SheafOfModules.toSheaf R)
        (colimit.isColimit (diagram ⋙ forgetful)))
  exact preservesColimit_of_iso_diagram _ comparison

end Acyclicity

/-! ### Corepresentation of sections over an object -/

section Corepresentation

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}]

/-- For an adjunction `F ⊣ G` with additive left adjoint between preadditive categories with the
same morphism universe, morphisms out of `Y` after `G` are the morphisms out of `F.obj Y`. -/
def coyonedaAdjunctionIso {A : Type*} [Category.{t} A] [Preadditive A]
    {B : Type*} [Category.{t} B] [Preadditive B] {F : B ⥤ A} {G : A ⥤ B}
    (adj : F ⊣ G) [F.Additive] (Y : B) :
    G ⋙ preadditiveCoyoneda.obj (op Y) ≅ preadditiveCoyoneda.obj (op (F.obj Y)) :=
  NatIso.ofComponents (fun Z => (adj.homAddEquiv Y Z).symm.toAddCommGrpIso)
    (fun {_ _} g => by ext f; exact adj.homEquiv_naturality_right_symm f g)

/-- Morphisms out of the sheafified extension of scalars of an abelian presheaf `P` are the
morphisms out of the sheafification of `P` into the underlying abelian sheaf. Both sides are
corepresentations transported along an adjunction, so the identification is the composite of the
module sheafification adjunction, the corepresentation by the extension of scalars, and the
abelian sheafification adjunction. -/
private def tensorSheafHomIso (R : Sheaf J RingCat.{u}) (P : Cᵒᵖ ⥤ Ab.{u}) :
    preadditiveCoyoneda.obj (op
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
        (ModuleSheafCohomology.tensorPresheaf R.obj P))) ≅
    SheafOfModules.toSheaf R ⋙ preadditiveCoyoneda.obj
      (op ((presheafToSheaf J Ab.{u}).obj P)) :=
  have : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).left_adjoint_additive
  have : (presheafToSheaf J Ab.{u}).Additive :=
    (sheafificationAdjunction J Ab.{u}).left_adjoint_additive
  (coyonedaAdjunctionIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))
      (ModuleSheafCohomology.tensorPresheaf R.obj P)).symm ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars (𝟙 R.obj)) (tensorPresheafCoyonedaIso R.obj P) ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
        (coyonedaAdjunctionIso (sheafificationAdjunction J Ab.{u}) P)

/-- The sheaf of modules corepresenting sections over `U`: the sheafified extension of scalars
of the free abelian presheaf on the representable at `U`. -/
abbrev sectionObject (R : Sheaf J RingCat.{u}) (U : C) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (ModuleSheafCohomology.tensorPresheaf R.obj (yoneda.obj U ⋙ AddCommGrpCat.free))

/-- Sections over `U` of a sheaf of modules are the morphisms out of `sectionObject`. -/
private def sectionHomAddEquiv (R : Sheaf J RingCat.{u}) (U : C) (M : SheafOfModules.{u} R) :
    (sectionObject J R U ⟶ M) ≃+ M.val.obj (op U) :=
  (Iso.addCommGroupIsoToAddEquiv ((tensorSheafHomIso J R
    (yoneda.obj U ⋙ AddCommGrpCat.free)).app M)).trans
      (((sheafificationAdjunction J Ab.{u}).homAddEquiv
        (yoneda.obj U ⋙ AddCommGrpCat.free) ((SheafOfModules.toSheaf R).obj M)).trans
          (ModuleSheafCohomology.freeEvaluationHomAddEquiv U M.val.presheaf))

/-- The corepresentation of sections over `U` turns composition into restriction of sections. -/
private lemma sectionHomAddEquiv_comp (R : Sheaf J RingCat.{u}) (U : C)
    {M N : SheafOfModules.{u} R} (a : sectionObject J R U ⟶ M) (f : M ⟶ N) :
    sectionHomAddEquiv J R U N (a ≫ f) =
      f.val.app (op U) (sectionHomAddEquiv J R U M a) := by
  have h := ConcreteCategory.congr_hom
    ((tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free)).hom.naturality f) a
  show ModuleSheafCohomology.freeEvaluationHomAddEquiv U N.val.presheaf
      ((sheafificationAdjunction J Ab.{u}).homEquiv _ _
        (((tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free)).hom.app N) (a ≫ f))) =
    f.val.app (op U) (ModuleSheafCohomology.freeEvaluationHomAddEquiv U M.val.presheaf
      ((sheafificationAdjunction J Ab.{u}).homEquiv _ _
        (((tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free)).hom.app M) a)))
  rw [show ((tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free)).hom.app N)
      (a ≫ f) = ((tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free)).hom.app M) a ≫
      (SheafOfModules.toSheaf R).map f from h]
  exact congrArg (ModuleSheafCohomology.freeEvaluationHomAddEquiv U N.val.presheaf)
    ((sheafificationAdjunction J Ab.{u}).homEquiv_naturality_right
      (((tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free)).hom.app M) a)
      ((SheafOfModules.toSheaf R).map f))

end Corepresentation

/-! ### The comparison -/

section Comparison

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}]
  [HasExt.{max u' u} (Sheaf J Ab.{u})] [EnoughInjectives (Sheaf J Ab.{u})]

/-- `Ext` out of `sectionObject` into a sheaf of modules is controlled by the cohomology of the
underlying abelian sheaf over `U`: both are computed by the comparison of Stacks 03FD, whose
acyclicity hypothesis is `ext_eq_zero_of_isTorsionFree` applied to the free abelian presheaf on
the representable at `U`. -/
private lemma sectionObject_ext_subsingleton (R : Sheaf J RingCat.{u})
    [EnoughInjectives (SheafOfModules.{u} R)] [HasExt.{max u' u} (SheafOfModules.{u} R)]
    (F : SheafOfModules.{u} R) (U : C) (n : ℕ)
    (hF : IsZero (Sheaf.H'.{max u' u} ((SheafOfModules.toSheaf R).obj F) n U)) :
    Subsingleton (Ext.{max u' u} (sectionObject J R U) F n) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    toSheaf_preservesFiniteColimits J R
  let P := yoneda.obj U ⋙ AddCommGrpCat.free
  let X := (presheafToSheaf J Ab.{u}).obj P
  let G := preadditiveCoyoneda.obj (op X)
  let β := tensorSheafHomIso J R P
  have h : ∀ (I : SheafOfModules.{u} R) [Injective I] (m : ℕ)
      (e : Ext.{max u' u} X ((SheafOfModules.toSheaf R).obj I) (m + 1)), e = 0 :=
    fun I _ m e => ext_eq_zero_of_isTorsionFree J R I _
      (isTorsionFree_sheafify_free J (yoneda.obj U)) m e
  let c : extFunctorObj (sectionObject J R U) n ≅
      SheafOfModules.toSheaf R ⋙ extFunctorObj X n :=
    ModuleSheafCohomology.extFunctorObjIsoRightDerived _ (sectionObject J R U)
        (ModuleSheafCohomology.compCorepresentation (SheafOfModules.toSheaf R) G X
          (Iso.refl _) (sectionObject J R U) β) n ≪≫
      ModuleSheafCohomology.comparisonIso (SheafOfModules.toSheaf R) G X (Iso.refl _)
          (sectionObject J R U) β h n ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
          (ModuleSheafCohomology.extFunctorObjIsoRightDerived G X (Iso.refl _) n).symm
  have hsub : Subsingleton (Ext.{max u' u} X ((SheafOfModules.toSheaf R).obj F) n) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hF
  exact ⟨fun x y =>
    (ConcreteCategory.bijective_of_isIso (c.app F).hom).injective (hsub.elim _ _)⟩

end Comparison

/-- **Positive-degree cohomology over an object controls the right derived sections.** If the
cohomology of the underlying abelian sheaf of `F` over `U` vanishes in degree `n + 1`, then the
`(n + 1)`-st right derived functor of module-valued sections over `U`, evaluated at `F`,
vanishes.

The sections functor is corepresented by `sectionObject`, so the terms of an injective
resolution of `F` are carried to the groups of morphisms out of `sectionObject`, and
`sectionObject_ext_subsingleton` says that the resulting complex of sections is exact in degree
`n + 1`. -/
public theorem subsingleton_rightDerived_evaluation {C : Type u'} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
    [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}]
    [HasExt.{max u' u} (Sheaf J Ab.{u})] [EnoughInjectives (Sheaf J Ab.{u})]
    [EnoughInjectives (SheafOfModules.{u} R)] [HasExt.{max u' u} (SheafOfModules.{u} R)]
    (F : SheafOfModules.{u} R) (U : C) (n : ℕ)
    (hF : IsZero (Sheaf.H'.{max u' u} ((SheafOfModules.toSheaf R).obj F) (n + 1) U)) :
    Subsingleton (((SheafOfModules.evaluation R (op U)).rightDerived (n + 1)).obj F) := by
  let I := injectiveResolution F
  let E := SheafOfModules.evaluation R (op U)
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hex : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    let a := (sectionHomAddEquiv J R U (I.cocomplex.X (n + 1))).symm x
    have hax : sectionHomAddEquiv J R U (I.cocomplex.X (n + 1)) a = x :=
      (sectionHomAddEquiv J R U (I.cocomplex.X (n + 1))).apply_symm_apply x
    have ha : a ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
      apply (sectionHomAddEquiv J R U (I.cocomplex.X (n + 2))).injective
      rwa [sectionHomAddEquiv_comp, map_zero, hax]
    have he : I.extMk a (n + 2) rfl ha = 0 :=
      (sectionObject_ext_subsingleton J R F U (n + 1) hF).elim _ _
    obtain ⟨b, hb⟩ := (I.extMk_eq_zero_iff a (n + 2) rfl ha n rfl).mp he
    refine ⟨sectionHomAddEquiv J R U (I.cocomplex.X n) b, ?_⟩
    show (I.cocomplex.d n (n + 1)).val.app (op U) _ = x
    rw [← sectionHomAddEquiv_comp, hb, hax]
  exact ModuleCat.isZero_iff_subsingleton.mp
    (hex.isZero_homology.of_iso (I.isoRightDerivedObj E (n + 1)))

end Stacks.Cohomology.ObjectSections

end
