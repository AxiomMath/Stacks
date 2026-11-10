module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-!
# Cohomology over an object does not change on a bigger site

Let `G : C ⥤ D` be a continuous and cocontinuous functor between essentially small sites which
preserves fibre products and equalizers. Restriction of abelian sheaves along `G` does not change
the cohomology over an object `U` of `C`, where cohomology over an object is Mathlib's
`Ext`-based `CategoryTheory.Sheaf.cohomologyPresheafFunctor`: the `Ext`-groups out of the free
abelian sheaf on `yoneda.obj U`.

The comparison is the objectwise counterpart of
`Stacks.Cohomology.BiggerSite.sheafCohomologyIso`, and is proved the same way: cohomology over
`U` is `Ext` out of the free abelian sheaf on `yoneda.obj U`, so the comparison is an instance of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`, `Ext` out of the image of a left
adjoint being computed on the other side of the adjunction. The left adjoint is lower shriek, the
right adjoint is restriction, and what replaces the identification of the two constant sheaves is
`freeYonedaSheafPullbackIso`: lower shriek carries the free abelian sheaf on `yoneda.obj U` to
the free abelian sheaf on `yoneda.obj (G.obj U)`, both corepresenting sections over `U`.

## Main definitions

* `Stacks.Cohomology.BiggerSite.freeYonedaSheaf`: the free abelian sheaf on the Yoneda presheaf
  of an object, the object whose `Ext`-groups are the cohomology over that object.
* `Stacks.Cohomology.BiggerSite.freeYonedaSheafPullbackIso`: lower shriek carries the free
  abelian sheaf on an object to the free abelian sheaf on its image.
* `Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso`: restriction along `G` does not
  change cohomology over an object, naturally in the abelian sheaf, for an arbitrary `Ext`
  universe.

## Main results

* `Stacks.Cohomology.BiggerSite.hasExt_sheaf` and
  `Stacks.Cohomology.BiggerSite.hasInjectiveResolutions_sheaf`: abelian sheaves on an essentially
  small site have `Ext`-groups in their own morphism universe and injective resolutions.
* `Stacks.Cohomology.BiggerSite.hasPointwiseLeftKanExtension_op` and
  `Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op`: abelian presheaves on an
  essentially small site have pointwise Kan extensions along any functor out of it.
* `Stacks.Cohomology.BiggerSite.freeYonedaSheafHomEquiv`: the free abelian sheaf on `yoneda.obj U`
  corepresents sections over `U`.

## Implementation notes

`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` needs the `Ext`-groups to live in the
morphism universe of the two sheaf categories, so `extFunctorObjFreeYonedaIso` is stated there and
`extFunctorObjIsoChgUniv` moves it to an arbitrary `Ext` universe. Unlike the global comparison,
whose two sides are `Ext`-groups in two different universes once the `Ext` universe is free, the
two sides here are `Ext`-groups out of two *different* objects in *one* universe, so the
comparison remains an isomorphism of functors and nothing has to be phrased with `AddEquiv`.

The `Ext`-universe hypotheses are named instance binders throughout:
`CategoryTheory.Abelian.HasExt` is an abbreviation, so an instance for one universe is not
reliably distinguished from an instance for another by instance search, and these declarations
are used with two of them in scope at once.

Essential smallness is what makes the hypotheses of the comparison derivable from the site data
alone: it gives the Kan extensions along `G.op` with coefficients in the morphism universe of the
sites, which the generic instances provide only for coefficients in the universe of the objects.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w' a v uA uB u u'

namespace Stacks.Cohomology.BiggerSite

/-! ### Abelian sheaves on an essentially small site -/

section EssentiallySmallSite

variable {C : Type u} [Category.{a} C] [EssentiallySmall.{a} C]

/-- **Abelian sheaves on an essentially small site form a Grothendieck abelian category**, with
coefficients in the morphism universe of the site. -/
theorem isGrothendieckAbelian_sheaf (J : GrothendieckTopology C) [HasSheafify J Ab.{a}] :
    IsGrothendieckAbelian.{a, max u a, max u (a + 1)} (Sheaf J Ab.{a}) := by
  let e := equivSmallModel.{a} C
  let : ∀ X : Cᵒᵖ, HasLimitsOfShape (StructuredArrow X e.inverse.op) Ab.{a} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{a} _ _
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{a, a, a, a + 1, u} J Ab.{a}

/-- **`Ext`-groups of abelian sheaves on an essentially small site live in the morphism universe
of that sheaf category.** The category has enough injectives, being Grothendieck abelian, and
its hom-types already lie in that universe. -/
theorem hasExt_sheaf (J : GrothendieckTopology C) [HasSheafify J Ab.{a}] :
    HasExt.{max u a} (Sheaf J Ab.{a}) := by
  let := isGrothendieckAbelian_sheaf J
  exact hasExt_of_enoughInjectives _

/-- **Abelian sheaves on an essentially small site have injective resolutions.** -/
theorem hasInjectiveResolutions_sheaf (J : GrothendieckTopology C) [HasSheafify J Ab.{a}] :
    HasInjectiveResolutions (Sheaf J Ab.{a}) := by
  let := isGrothendieckAbelian_sheaf J
  infer_instance

variable {D : Type u'} [Category.{a} D]

/-- **Abelian presheaves on an essentially small site have pointwise left Kan extensions along
the opposite of any functor out of it**, with coefficients in the morphism universe of the site.
The comma categories computing the extension are essentially small, so the colimits exist. -/
theorem hasPointwiseLeftKanExtension_op (G : C ⥤ D) (P : Cᵒᵖ ⥤ Ab.{a}) :
    G.op.HasPointwiseLeftKanExtension P := by
  intro Y
  let : HasColimitsOfShape (CostructuredArrow G.op Y) Ab.{a} :=
    hasColimitsOfShape_of_essentiallySmall.{a} _ _
  infer_instance

/-- **Abelian presheaves on an essentially small site have pointwise right Kan extensions along
the opposite of any functor out of it**, with coefficients in the morphism universe of the site.
The comma categories computing the extension are essentially small, so the limits exist. -/
theorem hasPointwiseRightKanExtension_op (G : C ⥤ D) (P : Cᵒᵖ ⥤ Ab.{a}) :
    G.op.HasPointwiseRightKanExtension P := by
  intro Y
  let : HasLimitsOfShape (StructuredArrow Y G.op) Ab.{a} :=
    hasLimitsOfShape_of_essentiallySmall.{a} _ _
  infer_instance

end EssentiallySmallSite

/-! ### The free abelian sheaf on an object -/

section FreeYoneda

variable {C : Type u} [Category.{a} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{a}]

/-- **The free abelian sheaf on an object of a site**: the sheafification of the free abelian
presheaf on `yoneda.obj U`. Its `Ext`-groups are the cohomology over `U`, which is how
`CategoryTheory.Sheaf.cohomologyPresheafFunctor` is defined. -/
def freeYonedaSheaf (U : C) : Sheaf J Ab.{a} :=
  (presheafToSheaf J Ab.{a}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- **The free abelian sheaf on `U` corepresents sections over `U`.** A morphism from it to an
abelian sheaf `F` is a section of `F` over `U`: sheafification is left adjoint to the inclusion
of sheaves, the free abelian presheaf functor is left adjoint to the underlying presheaf of sets,
and a morphism out of `yoneda.obj U` is an element of the value at `U`. -/
def freeYonedaSheafHomEquiv (U : C) (F : Sheaf J Ab.{a}) :
    (freeYonedaSheaf J U ⟶ F) ≃ ToType (F.obj.obj (op U)) :=
  ((sheafificationAdjunction J Ab.{a}).homEquiv _ F).trans
    (((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj U) F.obj).trans
      yonedaEquiv)

/-- **`freeYonedaSheafHomEquiv` is natural in the abelian sheaf.** -/
theorem freeYonedaSheafHomEquiv_comp (U : C) {F F' : Sheaf J Ab.{a}}
    (g : freeYonedaSheaf J U ⟶ F) (f : F ⟶ F') :
    freeYonedaSheafHomEquiv J U F' (g ≫ f) =
      f.hom.app (op U) (freeYonedaSheafHomEquiv J U F g) := by
  simp only [freeYonedaSheafHomEquiv]
  rfl

end FreeYoneda

/-! ### Lower shriek of the free abelian sheaf on an object -/

section Pullback

variable {C : Type u} [Category.{a} C] {D : Type u'} [Category.{a} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsContinuous J K] [HasSheafify J Ab.{a}] [HasSheafify K Ab.{a}]
  [lanG : ∀ P : Cᵒᵖ ⥤ Ab.{a}, G.op.HasPointwiseLeftKanExtension P]

/-- **Sections over `U` of a restricted sheaf, read on the free abelian sheaf.** A morphism from
lower shriek of the free abelian sheaf on `U` to an abelian sheaf `F` on the bigger site is a
section of `F` over `G.obj U`. -/
def freeYonedaSheafPullbackHomEquiv (U : C) (F : Sheaf K Ab.{a}) :
    ((Functor.sheafPullbackConstruction.sheafPullback G Ab.{a} J K).obj
        (freeYonedaSheaf J U) ⟶ F) ≃ ToType (F.obj.obj (op (G.obj U))) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a} J K).homEquiv
    (freeYonedaSheaf J U) F).trans (freeYonedaSheafHomEquiv J U _)

/-- **`freeYonedaSheafPullbackHomEquiv` is natural in the abelian sheaf.** -/
theorem freeYonedaSheafPullbackHomEquiv_comp (U : C) {F F' : Sheaf K Ab.{a}}
    (g : (Functor.sheafPullbackConstruction.sheafPullback G Ab.{a} J K).obj
      (freeYonedaSheaf J U) ⟶ F) (f : F ⟶ F') :
    freeYonedaSheafPullbackHomEquiv J K G U F' (g ≫ f) =
      f.hom.app (op (G.obj U)) (freeYonedaSheafPullbackHomEquiv J K G U F g) := by
  change freeYonedaSheafHomEquiv J U _
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a} J K).homEquiv
      (freeYonedaSheaf J U) F' (g ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right]
  exact freeYonedaSheafHomEquiv_comp J U _ _

/-- **Lower shriek carries the free abelian sheaf on `U` to the free abelian sheaf on `G.obj U`.**
Both corepresent sections over `G.obj U` on the bigger site — the first because restriction of a
sheaf has `G.obj U`-sections over `U`, the second directly — so they agree. This is the
objectwise counterpart of
`Stacks.Cohomology.BiggerSite.constantSheafCompSheafPullbackIso`. -/
def freeYonedaSheafPullbackIso (U : C) :
    (Functor.sheafPullbackConstruction.sheafPullback G Ab.{a} J K).obj (freeYonedaSheaf J U) ≅
      freeYonedaSheaf K (G.obj U) := by
  refine Iso.unop (Coyoneda.fullyFaithful.preimageIso
    (X := op (freeYonedaSheaf K (G.obj U)))
    (Y := op ((Functor.sheafPullbackConstruction.sheafPullback G Ab.{a} J K).obj
      (freeYonedaSheaf J U))) ?_)
  refine NatIso.ofComponents (fun F => ?_) ?_
  · exact Equiv.toIso ((freeYonedaSheafHomEquiv K (G.obj U) F).trans
      (freeYonedaSheafPullbackHomEquiv J K G U F).symm)
  · intro F F' f
    ext g
    refine (freeYonedaSheafPullbackHomEquiv J K G U F').injective ?_
    change freeYonedaSheafPullbackHomEquiv J K G U F'
        ((freeYonedaSheafPullbackHomEquiv J K G U F').symm
          (freeYonedaSheafHomEquiv K (G.obj U) F' (g ≫ f))) =
      freeYonedaSheafPullbackHomEquiv J K G U F'
        ((freeYonedaSheafPullbackHomEquiv J K G U F).symm
          (freeYonedaSheafHomEquiv K (G.obj U) F g) ≫ f)
    rw [Equiv.apply_symm_apply, freeYonedaSheafHomEquiv_comp,
      freeYonedaSheafPullbackHomEquiv_comp, Equiv.apply_symm_apply]

end Pullback

/-! ### Change of the `Ext` universe in an `Ext`-functor comparison -/

section ChgUniv

variable {A : Type uA} [Category.{v} A] [Abelian A] {B : Type uB} [Category.{v} B] [Abelian B]

/-- **The change of `Ext` universe is compatible with the functoriality of `Ext` in its second
variable.** -/
theorem extChgUnivAddEquiv_extFunctorObj_map [extA : HasExt.{w} A] [extA' : HasExt.{w'} A]
    {X Y Y' : A} (f : Y ⟶ Y') (p : ℕ) (x : Ext.{w} X Y p) :
    SimplicialComponent.extChgUnivAddEquiv.{w, w'} ((extFunctorObj.{w} X p).map f x) =
      (extFunctorObj.{w'} X p).map f
        (SimplicialComponent.extChgUnivAddEquiv.{w, w'} x) := by
  change Ext.chgUniv.{w'} (x.comp (Ext.mk₀ f) (add_zero p)) =
    (Ext.chgUniv.{w'} x).comp (Ext.mk₀ f) (add_zero p)
  rw [extChgUniv_comp, extChgUniv_mk₀]

/-- **An isomorphism of `Ext`-functors transported to another `Ext` universe.** If `Ext` out of
`X : A` is computed, along a functor `R : A ⥤ B`, by `Ext` out of `Y : B`, then the same holds
with the `Ext`-groups taken in any other universe: both sides of the comparison are
`Ext`-groups in the new universe, and the change of universe is additive and natural. -/
def extFunctorObjIsoChgUniv [extA : HasExt.{w} A] [extA' : HasExt.{w'} A]
    [extB : HasExt.{w} B] [extB' : HasExt.{w'} B] (R : A ⥤ B) (X : A) (Y : B) (p : ℕ)
    (iso : extFunctorObj.{w'} X p ≅ R ⋙ extFunctorObj.{w'} Y p) :
    R ⋙ extFunctorObj.{w} Y p ≅ extFunctorObj.{w} X p :=
  NatIso.ofComponents
    (fun Z => (SimplicialComponent.extChgUnivAddEquiv.{w, w'}.trans
      ((iso.symm.app Z).addCommGroupIsoToAddEquiv.trans
        SimplicialComponent.extChgUnivAddEquiv.{w', w})).toAddCommGrpIso)
    (by
      intro Z Z' f
      ext x
      have h₁ : SimplicialComponent.extChgUnivAddEquiv.{w, w'}
            ((extFunctorObj.{w} Y p).map (R.map f) x) =
          (extFunctorObj.{w'} Y p).map (R.map f)
            (SimplicialComponent.extChgUnivAddEquiv.{w, w'} x) :=
        extChgUnivAddEquiv_extFunctorObj_map.{w, w'} (R.map f) p x
      have h₂ := NatTrans.naturality_apply iso.symm.hom f
        (SimplicialComponent.extChgUnivAddEquiv.{w, w'} x)
      have h₃ : SimplicialComponent.extChgUnivAddEquiv.{w', w}
            ((extFunctorObj.{w'} X p).map f ((iso.symm.app Z).hom
              (SimplicialComponent.extChgUnivAddEquiv.{w, w'} x))) =
          (extFunctorObj.{w} X p).map f
            (SimplicialComponent.extChgUnivAddEquiv.{w', w}
              ((iso.symm.app Z).hom
                (SimplicialComponent.extChgUnivAddEquiv.{w, w'} x))) :=
        extChgUnivAddEquiv_extFunctorObj_map.{w', w} f p _
      exact (congrArg (fun z => SimplicialComponent.extChgUnivAddEquiv.{w', w}
          ((iso.symm.app Z').hom z)) h₁).trans
        ((congrArg SimplicialComponent.extChgUnivAddEquiv.{w', w} h₂).trans h₃))

end ChgUniv

/-! ### Cohomology over an object on the bigger site -/

section Objectwise

variable {C : Type u} [Category.{a} C] {D : Type u} [Category.{a} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [HasSheafify J Ab.{a}] [HasSheafify K Ab.{a}]
  [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan G] [PreservesLimitsOfShape WalkingParallelPair G]
  [lanG : ∀ P : Cᵒᵖ ⥤ Ab.{a}, G.op.HasPointwiseLeftKanExtension P]
  [ranG : ∀ P : Cᵒᵖ ⥤ Ab.{a}, G.op.HasPointwiseRightKanExtension P]
  [extJ : HasExt.{max u a} (Sheaf J Ab.{a})] [extK : HasExt.{max u a} (Sheaf K Ab.{a})]
  [injJ : HasInjectiveResolutions (Sheaf J Ab.{a})]
  [injK : HasInjectiveResolutions (Sheaf K Ab.{a})]

/-- **Stacks 03YU, statement 2.** Restriction of abelian sheaves along `G` does not change the
`Ext`-groups out of the free abelian sheaf on an object, naturally in the abelian sheaf. The
`Ext` universe is the common morphism universe of the two sheaf categories.

This is `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` for the adjunction between
lower shriek and restriction, at the identification `freeYonedaSheafPullbackIso` of the two free
abelian sheaves. -/
def extFunctorObjFreeYonedaIso (U : C) (p : ℕ) :
    extFunctorObj.{max u a} (freeYonedaSheaf K (G.obj U)) p ≅
      G.sheafPushforwardContinuous Ab.{a} J K ⋙
        extFunctorObj.{max u a} (freeYonedaSheaf J U) p :=
  have : (G.sheafPushforwardContinuous Ab.{a} J K).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a} J K).isRightAdjoint
  have : (G.sheafPushforwardContinuous Ab.{a} J K).Additive :=
    have : HasLimitsOfShape (Discrete WalkingPair) (Dᵒᵖ ⥤ Ab.{a}) := inferInstance
    have : HasBinaryProducts (Sheaf K Ab.{a}) :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf K Ab.{a})
    Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits (G.sheafPushforwardContinuous Ab.{a} J K) :=
    preservesFiniteColimits_sheafPushforwardContinuous J K G Ab.{a}
  have : (G.sheafPushforwardContinuous Ab.{a} J K).PreservesInjectiveObjects :=
    preservesInjectiveObjects_sheafPushforwardContinuous J K G
  have : (Functor.sheafPullbackConstruction.sheafPullback G Ab.{a} J K).Additive :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a}
      J K).left_adjoint_additive
  ExtComparison.extFunctorObjIsoCompOfIso
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a} J K)
    (freeYonedaSheafPullbackIso J K G U) p

end Objectwise

section ObjectwiseChgUniv

variable {C : Type u} [Category.{a} C] [EssentiallySmall.{a} C]
  {D : Type u} [Category.{a} D] [EssentiallySmall.{a} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [HasSheafify J Ab.{a}] [HasSheafify K Ab.{a}]
  [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan G] [PreservesLimitsOfShape WalkingParallelPair G]
  [HasExt.{w} (Sheaf J Ab.{a})] [HasExt.{w} (Sheaf K Ab.{a})]

/-- **Stacks 03YU, statement 2, at an arbitrary `Ext` universe.** For a continuous and
cocontinuous functor between essentially small sites which preserves fibre products and
equalizers, restriction of abelian sheaves along `G` does not change cohomology over an object
`U` of the smaller site, naturally in the abelian sheaf. Cohomology over an object is Mathlib's
`CategoryTheory.Sheaf.cohomologyPresheafFunctor`, whose `Ext` universe is independent of the
sites.

Essential smallness supplies the remaining hypotheses of `extFunctorObjFreeYonedaIso`: the Kan
extensions along `G.op` with coefficients in the morphism universe of the sites, and the
`Ext`-groups and injective resolutions of the two sheaf categories. -/
def cohomologyPresheafFunctorIso (U : C) (p : ℕ) :
    G.sheafPushforwardContinuous Ab.{a} J K ⋙ Sheaf.cohomologyPresheafFunctor J p ⋙
        (evaluation Cᵒᵖ Ab.{w}).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor K p ⋙ (evaluation Dᵒᵖ Ab.{w}).obj (op (G.obj U)) :=
  extFunctorObjIsoChgUniv.{w, max u a}
      (extA' := hasExt_sheaf K) (extB' := hasExt_sheaf J) _ _ _ p
    (extFunctorObjFreeYonedaIso J K G
      (lanG := fun P => hasPointwiseLeftKanExtension_op G P)
      (ranG := fun P => hasPointwiseRightKanExtension_op G P)
      (extJ := hasExt_sheaf J) (extK := hasExt_sheaf K)
      (injJ := hasInjectiveResolutions_sheaf J) (injK := hasInjectiveResolutions_sheaf K) U p)

end ObjectwiseChgUniv

end Stacks.Cohomology.BiggerSite

end
