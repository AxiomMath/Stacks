module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.ComponentCohomology

/-!
# Global sheaf cohomology does not change on a bigger site

Let `G : C ⥤ D` be a continuous functor between sites carrying a terminal object of `C` to a
terminal object of `D`. Restriction of abelian sheaves along `G` does not change global
cohomology, where cohomology is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H`.

The argument never passes through a global sections functor. Global cohomology *is* `Ext` out of
the constant sheaf `ℤ`, so the comparison is an instance of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`: `Ext` out of the image of a left
adjoint is computed on the other side of the adjunction. The left adjoint here is lower shriek,
the right adjoint is restriction, and the identification of the two constant sheaves is
`constantSheafCompSheafPullbackIso`. Because `extFunctorObjIsoCompOfIso` is stated for abstract
abelian categories, no site is required to be small: the two sheaf categories need only share
their morphism universe, which they do as soon as the two sites have their objects in one
universe.

## Main definitions

* `Stacks.Cohomology.BiggerSite.constantSheafCompSheafPullbackIso`: lower shriek carries the
  constant sheaf on the smaller site to the constant sheaf on the bigger one.
* `Stacks.Cohomology.BiggerSite.sheafCohomologyIso`: restriction along `G` does not change
  global cohomology, naturally in the abelian sheaf.
* `Stacks.Cohomology.BiggerSite.sheafHAddEquiv`: its value at a sheaf, for an arbitrary `Ext`
  universe.

## Main results

* `Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous`: restriction
  along a continuous *and cocontinuous* functor is right exact, being itself a left adjoint.
* `Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous`:
  restriction preserves injective abelian sheaves.
* `Stacks.Cohomology.BiggerSite.sheafHAddEquiv_naturality`: the comparison commutes with
  morphisms of abelian sheaves.

## Implementation notes

`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` needs the `Ext`-groups to live in
the morphism universe of the two categories, so `sheafCohomologyIso` is stated there. The
objectwise form `sheafHAddEquiv` is stated for an arbitrary `Ext` universe, the two being
bridged by `Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv`. The two cohomology
groups then lie in `AddCommGrpCat` at two different universes, so that bridge is an additive
equivalence and not an isomorphism of a category; this is why `sheafHAddEquiv` and its
naturality are phrased with `AddEquiv` and elements rather than as an isomorphism of functors.

`extChgUniv_comp` and `extChgUniv_mk₀` say that the change of `Ext` universe is compatible with
composition of `Ext`-classes and with the class of a morphism. Both hold because
`CategoryTheory.Abelian.Ext.homEquiv_chgUniv` says the change of universe commutes with the
identification of an `Ext`-group with a group of morphisms of the derived category, and that
identification is how composition on `Ext` is defined.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w' a vA uA v v' u u'

namespace Stacks.Cohomology.BiggerSite

/-! ### The constant sheaf and lower shriek -/

section ConstantSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  (A : Type uA) [Category.{vA} A] [G.IsContinuous J K]

/-- **Sections of a restricted sheaf over an object are sections over its image.**
Restriction along `G` followed by sections over `e : C` is sections over `G e`. -/
def sheafPushforwardContinuousCompSheafSectionsIso (e : C) :
    G.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op e) ≅
      (sheafSections K A).obj (op (G.obj e)) :=
  Iso.refl _

variable [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension P]

/-- **Lower shriek carries the constant sheaf to the constant sheaf.** If `G` carries a terminal
object of `C` to a terminal object of `D`, then the left adjoint of restriction along `G` takes
the constant sheaf with value `X` on the smaller site to the constant sheaf with value `X` on
the bigger one, naturally in `X`.

Both functors are left adjoint to the same functor: the constant sheaf functor on `C` followed
by lower shriek is left adjoint to restriction followed by sections over the terminal object of
`C`, and that composite is sections over the terminal object of `D`. -/
def constantSheafCompSheafPullbackIso {eC : C} {eD : D} (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : G.obj eC = eD) :
    constantSheaf J A ⋙ Functor.sheafPullbackConstruction.sheafPullback G A J K ≅
      constantSheaf K A :=
  (((constantSheafAdj J A heC).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K)).ofNatIsoRight
    (sheafPushforwardContinuousCompSheafSectionsIso J K G A eC ≪≫
      eqToIso (congrArg (fun X : D => (sheafSections K A).obj (op X)) hu))).leftAdjointUniq
    (constantSheafAdj K A heD)

end ConstantSheaf

/-! ### Exactness of restriction, and preservation of injectives -/

section Exactness

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)

/-- **Restriction along a cocontinuous functor is right exact.** A continuous and cocontinuous
functor of sites makes restriction of sheaves a left adjoint — of the pushforward built from the
right Kan extension — so restriction preserves finite colimits. -/
theorem preservesFiniteColimits_sheafPushforwardContinuous (A : Type uA) [Category.{vA} A]
    [G.IsContinuous J K] [G.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P] :
    PreservesFiniteColimits (G.sheafPushforwardContinuous A J K) := by
  have := (G.sheafAdjunctionCocontinuous A J K).isLeftAdjoint
  infer_instance

variable [G.IsContinuous J K] [HasSheafify J Ab.{a}] [HasSheafify K Ab.{a}]
  [HasPullbacks C] [HasEqualizers C] [PreservesLimitsOfShape WalkingCospan G]
  [PreservesLimitsOfShape WalkingParallelPair G]
  [∀ P : Cᵒᵖ ⥤ Ab.{a}, G.op.HasPointwiseLeftKanExtension P]

/-- **Restriction preserves injective abelian sheaves.** Restriction along `G` has lower shriek
as a left adjoint, and lower shriek is exact when `C` has fibre products and equalizers which
`G` preserves (Stacks 04BH); a functor with an exact left adjoint preserves injective objects
(Stacks 015Z). -/
theorem preservesInjectiveObjects_sheafPushforwardContinuous :
    (G.sheafPushforwardContinuous Ab.{a} J K).PreservesInjectiveObjects := by
  let R := G.sheafPushforwardContinuous Ab.{a} J K
  let L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{a} J K
  let adj : L ⊣ R := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a} J K
  let hlim : PreservesFiniteLimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits G J K
  let hcolim : PreservesFiniteColimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits Ab.{a} G J K
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  let : L.Additive := adj.left_adjoint_additive
  exact preservesInjectiveObjects_of_isExact R L adj ⟨hlim, hcolim⟩

end Exactness

/-! ### Change of the `Ext` universe -/

section ExtUniverse

variable {E : Type uA} [Category.{vA} E] [Abelian E] [HasExt.{w} E] [HasExt.{w'} E]

/-- **The change of `Ext` universe commutes with composition.** -/
theorem extChgUniv_comp {X Y Z : E} {i j n : ℕ} (α : Ext.{w} X Y i) (β : Ext.{w} Y Z j)
    (h : i + j = n) :
    Ext.chgUniv.{w'} (α.comp β h) = (Ext.chgUniv.{w'} α).comp (Ext.chgUniv.{w'} β) h := by
  let := HasDerivedCategory.standard E
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.homEquiv_chgUniv]

/-- **The change of `Ext` universe fixes the class of a morphism.** -/
theorem extChgUniv_mk₀ {X Y : E} (f : X ⟶ Y) :
    Ext.chgUniv.{w'} (Ext.mk₀.{w} f) = Ext.mk₀.{w'} f := by
  let := HasDerivedCategory.standard E
  apply Ext.ext
  simp only [Ext.homEquiv_chgUniv, Ext.mk₀_hom]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J Ab.{a}] [HasExt.{w} (Sheaf J Ab.{a})]

/-- **`CategoryTheory.Sheaf.functorH` acts on morphisms by `CategoryTheory.Sheaf.H.map`.** -/
theorem functorH_map_apply {F F' : Sheaf J Ab.{a}} (f : F ⟶ F') (p : ℕ)
    (x : Sheaf.H.{w} F p) :
    (Sheaf.functorH.{w, a} J p).map f x = Sheaf.H.map.{w, a} f p x :=
  rfl

variable [HasExt.{w'} (Sheaf J Ab.{a})]

/-- **The change of `Ext` universe is compatible with the functoriality of cohomology.** -/
theorem extChgUnivAddEquiv_sheafH_map {F F' : Sheaf J Ab.{a}} (f : F ⟶ F') (p : ℕ)
    (x : Sheaf.H.{w} F p) :
    SimplicialComponent.extChgUnivAddEquiv.{w, w'} (Sheaf.H.map.{w, a} f p x) =
      Sheaf.H.map.{w', a} f p (SimplicialComponent.extChgUnivAddEquiv.{w, w'} x) := by
  change Ext.chgUniv.{w'} (x.comp (Ext.mk₀ f) (add_zero p)) =
    (Ext.chgUniv.{w'} x).comp (Ext.mk₀ f) (add_zero p)
  rw [extChgUniv_comp, extChgUniv_mk₀]

end ExtUniverse

/-! ### Global cohomology on the bigger site -/

section Global

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsContinuous J K] [HasSheafify J Ab.{a}] [HasSheafify K Ab.{a}]
  [extJ : HasExt.{max u a} (Sheaf J Ab.{a})] [extK : HasExt.{max u a} (Sheaf K Ab.{a})]
  [injJ : HasInjectiveResolutions (Sheaf J Ab.{a})]
  [injK : HasInjectiveResolutions (Sheaf K Ab.{a})]
  [lanG : ∀ P : Cᵒᵖ ⥤ Ab.{a}, G.op.HasPointwiseLeftKanExtension P]
  [rexG : PreservesFiniteColimits (G.sheafPushforwardContinuous Ab.{a} J K)]
  [injG : (G.sheafPushforwardContinuous Ab.{a} J K).PreservesInjectiveObjects]

/-- **Stacks 03YU, statement 1.** Restriction of abelian sheaves along a continuous functor
carrying a terminal object to a terminal object does not change global cohomology, naturally in
the abelian sheaf. The `Ext` universe is the common morphism universe of the two sheaf
categories.

Global cohomology is `Ext` out of the constant sheaf `ℤ`, so this is
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` for the adjunction between lower
shriek and restriction, at the identification `constantSheafCompSheafPullbackIso` of the two
constant sheaves. -/
def sheafCohomologyIso {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : G.obj eC = eD) (p : ℕ) :
    G.sheafPushforwardContinuous Ab.{a} J K ⋙ Sheaf.functorH J p ≅ Sheaf.functorH K p :=
  have : (G.sheafPushforwardContinuous Ab.{a} J K).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a} J K).isRightAdjoint
  have : (G.sheafPushforwardContinuous Ab.{a} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (Functor.sheafPullbackConstruction.sheafPullback G Ab.{a} J K).Additive :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a}
      J K).left_adjoint_additive
  (ExtComparison.extFunctorObjIsoCompOfIso
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{a} J K)
      ((constantSheafCompSheafPullbackIso J K G Ab.{a} heC heD hu).app
        (AddCommGrpCat.of (ULift.{a} ℤ))) p).symm

/-- **The naturality of `sheafCohomologyIso`, read on elements.** -/
theorem sheafCohomologyIso_symm_app_functorH_map {eC : C} {eD : D} (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : G.obj eC = eD) {F F' : Sheaf K Ab.{a}} (f : F ⟶ F') (p : ℕ)
    (y : ToType ((Sheaf.functorH.{max u a, a} K p).obj F)) :
    (sheafCohomologyIso J K G heC heD hu p).symm.hom.app F'
        ((Sheaf.functorH.{max u a, a} K p).map f y) =
      (G.sheafPushforwardContinuous Ab.{a} J K ⋙ Sheaf.functorH.{max u a, a} J p).map f
        ((sheafCohomologyIso J K G heC heD hu p).symm.hom.app F y) :=
  NatTrans.naturality_apply (sheafCohomologyIso J K G heC heD hu p).symm.hom f y

/-- **The comparison of global cohomology commutes with morphisms of abelian sheaves**, at the
morphism universe of the two sites. This is
`sheafCohomologyIso_symm_app_functorH_map` with the action of `CategoryTheory.Sheaf.functorH`
on morphisms spelled out as `CategoryTheory.Sheaf.H.map`. -/
theorem sheafCohomologyIso_symm_app_sheafH_map {eC : C} {eD : D} (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : G.obj eC = eD) {F F' : Sheaf K Ab.{a}} (f : F ⟶ F') (p : ℕ)
    (y : Sheaf.H.{max u a} F p) :
    (sheafCohomologyIso J K G heC heD hu p).symm.hom.app F'
        (Sheaf.H.map.{max u a, a} f p y) =
      Sheaf.H.map.{max u a, a} ((G.sheafPushforwardContinuous Ab.{a} J K).map f) p
        ((sheafCohomologyIso J K G heC heD hu p).symm.hom.app F y) :=
  sheafCohomologyIso_symm_app_functorH_map J K G heC heD hu f p y

variable [HasExt.{w} (Sheaf J Ab.{a})] [HasExt.{w} (Sheaf K Ab.{a})]

/-- **Stacks 03YU, statement 1, at an arbitrary `Ext` universe.** The global cohomology of an
abelian sheaf on the bigger site agrees with the global cohomology of its restriction. The two
groups lie in `AddCommGrpCat` at two different universes when the `Ext` universe is not the
morphism universe of the sites, so the comparison is an additive equivalence rather than an
isomorphism of a category. -/
def sheafHAddEquiv {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : G.obj eC = eD) (F : Sheaf K Ab.{a}) (p : ℕ) :
    Sheaf.H.{w} F p ≃+
      Sheaf.H.{w} ((G.sheafPushforwardContinuous Ab.{a} J K).obj F) p :=
  (SimplicialComponent.extChgUnivAddEquiv.{w, max u a}).trans
    ((((sheafCohomologyIso J K G heC heD hu p).symm.app F).addCommGroupIsoToAddEquiv).trans
      SimplicialComponent.extChgUnivAddEquiv.{max u a, w})

/-- **The comparison of global cohomology commutes with morphisms of abelian sheaves.** -/
theorem sheafHAddEquiv_naturality {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : G.obj eC = eD) {F F' : Sheaf K Ab.{a}} (f : F ⟶ F') (p : ℕ) (x : Sheaf.H.{w} F p) :
    sheafHAddEquiv J K G heC heD hu F' p (Sheaf.H.map.{w, a} f p x) =
      Sheaf.H.map.{w, a} ((G.sheafPushforwardContinuous Ab.{a} J K).map f) p
        (sheafHAddEquiv J K G heC heD hu F p x) := by
  have h₁ : SimplicialComponent.extChgUnivAddEquiv.{w, max u a} (Sheaf.H.map.{w, a} f p x) =
      Sheaf.H.map.{max u a, a} f p
        (SimplicialComponent.extChgUnivAddEquiv.{w, max u a} x) :=
    extChgUnivAddEquiv_sheafH_map.{w, max u a} f p x
  have h₂ := sheafCohomologyIso_symm_app_sheafH_map J K G heC heD hu f p
    (SimplicialComponent.extChgUnivAddEquiv.{w, max u a} x)
  have h₃ : SimplicialComponent.extChgUnivAddEquiv.{max u a, w}
        (Sheaf.H.map.{max u a, a} ((G.sheafPushforwardContinuous Ab.{a} J K).map f) p
          ((sheafCohomologyIso J K G heC heD hu p).symm.hom.app F
            (SimplicialComponent.extChgUnivAddEquiv.{w, max u a} x))) =
      Sheaf.H.map.{w, a} ((G.sheafPushforwardContinuous Ab.{a} J K).map f) p
        (SimplicialComponent.extChgUnivAddEquiv.{max u a, w}
          ((sheafCohomologyIso J K G heC heD hu p).symm.hom.app F
            (SimplicialComponent.extChgUnivAddEquiv.{w, max u a} x))) :=
    extChgUnivAddEquiv_sheafH_map.{max u a, w} _ p _
  exact (congrArg SimplicialComponent.extChgUnivAddEquiv.{max u a, w}
    ((congrArg ((sheafCohomologyIso J K G heC heD hu p).symm.hom.app F') h₁).trans h₂)).trans h₃

end Global

end Stacks.Cohomology.BiggerSite

end
