module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOverABase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# The Leray isomorphism over a map of base rings

Let `φ : A ⟶ B` be a map of commutative rings and let

```
X' --g--> X
|         |
f'        f
v         v
Spec B -> Spec A
```

be a commutative square of schemes. [Stacks, Tag 0D5W] identifies derived global sections of a
derived direct image with derived global sections on the source; read over the base rings it says
that the two functors

`RΓ_A(X, Rg_* -)` and `RΓ_B(X', -)` with scalars restricted along `φ`

from `D(𝒪_{X'})` to `D(A)` agree. This file constructs that identification as the canonical
comparison of right derived functors, and from it the map

`θ : RΓ_A(X, F) ⟶ RΓ_B(X', Lg^* F)`

of `D(A)` that pulls a class back along `g`: derived global sections of the unit `F ⟶ Rg_* Lg^* F`
of the derived adjunction, followed by the Leray identification. Its adjoint
`RΓ_A(X, F) ⊗^L_A B ⟶ RΓ_B(X', Lg^* F)` is the base-change map of derived global sections.

## Main definitions

* `AlgebraicGeometry.LerayOver.sectionsIso`: the underived identification
  `Γ_A(X, g_* -) = Γ_B(X', -)` of `A`-linear functors.
* `AlgebraicGeometry.LerayOver.lerayUnit`: the canonical transformation from the underived
  functor to `Rg_* ⋙ RΓ_A(X, -)`.
* `AlgebraicGeometry.LerayOver.lerayIso`: **the Leray isomorphism over `φ`**,
  `RΓ_B(X', -) ⋙ res_φ ≅ Rg_* ⋙ RΓ_A(X, -)`.
* `AlgebraicGeometry.LerayOver.pullbackSectionsMap`: the map `θ` displayed above.

## Main results

* `AlgebraicGeometry.LerayOver.isIso_derivedSectionsOverOpenUnit_app_pushforward`: the unit of
  derived sections over an open is invertible at the direct image of a K-injective complex, which
  is the content of [Stacks, Tag 0D5W].
* `AlgebraicGeometry.LerayOver.lerayHom_fac`: the equation characterizing the Leray
  comparison.

## Implementation notes

Everything is stated in the ringed-space spelling
`SheafOfModules (structureSheafRing X.toRingedSpace)` of the category of `𝒪_X`-modules, with the
total right derived functor of `AlgebraicGeometry.homotopyBaseSections f` standing for
`AlgebraicGeometry.derivedGlobalSectionsOver f`, to which it is definitionally equal. Derived
direct image and derived pullback are those of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`,
at the standard model.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit derivedPullback derivedAdjunction
    isIso_derivedPushforwardUnit_app_of_isKInjective)
open Stacks.Cohomology.SiteCohomologyPresheaf
  (totalRightDerivedCompUnit isRightDerivedFunctor_totalRightDerived_comp)

universe u

namespace AlgebraicGeometry.LerayOver

attribute [local instance] HasDerivedCategory.standard

/-- The quasi-isomorphisms of the homotopy category of complexes of `𝒪_X`-modules, in the
ringed-space spelling. -/
abbrev qis (X : Scheme.{u}) :
    MorphismProperty (HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (ComplexShape.up ℤ)

section Sections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- `RΓ_A(X, -) : D(𝒪_X) ⥤ D(A)` in the ringed-space spelling: the total right derived functor of
`A`-linear global sections. It is `AlgebraicGeometry.derivedGlobalSectionsOver f` by `rfl`. -/
abbrev sections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (homotopyBaseSections f).totalRightDerived DerivedCategory.Qh (qis X)

/-- The unit of `AlgebraicGeometry.LerayOver.sections`. -/
abbrev sectionsUnit : homotopyBaseSections f ⟶ DerivedCategory.Qh ⋙ sections f :=
  (homotopyBaseSections f).totalRightDerivedUnit DerivedCategory.Qh (qis X)

/-- The ring map `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` of a scheme over `A`. -/
abbrev structureRingHom : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

end Sections

/-! ### The content of Tag 0D5W: the unit at a direct image of a K-injective complex -/

section Unit

variable {X Y : RingedSpace.{u, u}} (g : X ⟶ Y) (V : Opens Y.carrier)

open Stacks.Cohomology.DerivedSectionsLeray in
/-- **The unit of derived sections over an open is invertible at the direct image of a
K-injective complex.** This is the content of [Stacks, Tag 0D5W]. -/
theorem isIso_derivedSectionsOverOpenUnit_app_pushforward
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    IsIso ((derivedSectionsOverOpenUnit Y V).app
      (((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I))) := by
  have h₁ := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _
    (derivedPreimageSectionsUnit g V) I
  have h₂ := isIso_lerayComparison g V
  have hU : IsIso ((lerayUnit g V).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := by
    rw [← lerayComparison_fac]
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have h₃ := isIso_derivedPushforwardUnit_app_of_isKInjective g I inferInstance
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hU
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hU)

end Unit

/-! ### The `A`-linear form of the unit -/

section LinearUnit

open Stacks.Cohomology.DerivedSectionsLeray

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (g : X' ⟶ X)

/-- `A`-linear derived global sections are derived sections over `⊤` with scalars restricted
along `A ⟶ Γ(X, 𝒪_X)`, on the homotopy category: the two underived functors agree on the nose. -/
abbrev sectionsSourceIso :
    homotopySectionsOverOpen X.toRingedSpace ⊤ ⋙ (restrictScalarsOver f).mapDerivedCategory ≅
      homotopyBaseSections f :=
  homotopyCompBaseIso (sectionsOverOpen X.toRingedSpace ⊤) (restrictScalarsOver f)
    (baseSections f) (Iso.refl _)

/-- **The unit of `RΓ_A(X, -)` is invertible at the direct image of a K-injective complex.** -/
theorem isIso_sectionsUnit_app_pushforward
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    IsIso ((sectionsUnit f).app
      (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
          (ComplexShape.up ℤ)).obj I))) := by
  let Fh := homotopySectionsOverOpen X.toRingedSpace ⊤
  let T := (restrictScalarsOver f).mapDerivedCategory
  have hΓ := isIso_derivedSectionsOverOpenUnit_app_pushforward g.toLRSHom.toShHom ⊤ I
  have := isRightDerivedFunctor_totalRightDerived_comp Fh T
  refine Functor.isIso_rightDerivedUnit_app_of_iso _ _ (totalRightDerivedCompUnit Fh T)
    (sectionsUnit f) (qis X) (sectionsSourceIso f) _ ?_
  rw [Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedCompUnit_app]
  exact Functor.map_isIso _ _

end LinearUnit

/-! ### The underived identification -/

section Underived

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))

include w in
/-- The two ring maps `A ⟶ Γ(X', 𝒪_{X'})` around the square agree. -/
theorem structureRingHom_comp_eq :
    (structureRingHom f').comp φ = g.appTop.hom.comp (structureRingHom f) := by
  have h := congrArg (fun t => Scheme.Hom.appTop t) w
  simp only [Scheme.Hom.comp_appTop] at h
  have key : CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f'.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫ g.appTop := by
    rw [h, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact congrArg CommRingCat.Hom.hom key

/-- `A`-linear global sections on `X'` through `g`, read as restriction of scalars along the
composite ring map `A ⟶ Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})`. -/
abbrev compositeSections :
    SheafOfModules.{u} (structureSheafRing X'.toRingedSpace) ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation (structureSheafRing X'.toRingedSpace) (op (⊤ : Opens X'.carrier)) ⋙
    ModuleCat.restrictScalars (g.appTop.hom.comp (structureRingHom f))

/-- `Γ_A(X, g_* -)` is `compositeSections f g`. -/
def pushforwardSectionsIso :
    modulePushforward g.toLRSHom.toShHom ⋙ baseSections f ≅ compositeSections f g :=
  (Iso.refl _ : _ ≅ SheafOfModules.evaluation (structureSheafRing X'.toRingedSpace)
      (op (⊤ : Opens X'.carrier)) ⋙
        (ModuleCat.restrictScalars g.appTop.hom ⋙ restrictScalarsOver f)) ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp' (structureRingHom f) g.appTop.hom
      _ rfl).symm

include w in
/-- `Γ_B(X', -)` with scalars restricted along `φ` is `compositeSections f g`. -/
def baseSectionsRestrictIso :
    baseSections f' ⋙ ModuleCat.restrictScalars φ ≅ compositeSections f g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp' φ (structureRingHom f') _
      (structureRingHom_comp_eq φ f f' g w).symm).symm

/-- **Sections of a direct image are sections of the source.** `Γ_A(X, g_* -) = Γ_B(X', -)` with
scalars restricted along `φ`, as functors of `𝒪_{X'}`-modules to `A`-modules: the underlying
groups are equal and the two actions of `A` agree by `structureRingHom_comp_eq`. -/
def sectionsIso :
    modulePushforward g.toLRSHom.toShHom ⋙ baseSections f ≅
      baseSections f' ⋙ ModuleCat.restrictScalars φ :=
  pushforwardSectionsIso f g ≪≫ (baseSectionsRestrictIso φ f f' g w).symm

end Underived

/-! ### The Leray isomorphism -/

section Leray

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))

/-- `Γ_B(X', -)` with scalars restricted along `φ`, read on the homotopy category. -/
abbrev restrictedSections :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  homotopyBaseSections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory

include w in
/-- **The Leray unit.** The canonical transformation from `Γ_B(X', -)` restricted to `A` to
`Rg_* ⋙ RΓ_A(X, -)`: the identification with `Γ_A(X, g_* -)` (`sectionsIso`), followed by the
unit of `RΓ_A(X, -)` and then the unit of `Rg_*`. -/
def lerayUnit :
    restrictedSections φ f' ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward g.toLRSHom.toShHom ⋙ sections f) :=
  (homotopyCompBaseIso (baseSections f') (ModuleCat.restrictScalars φ) (compositeSections f g)
      (baseSectionsRestrictIso φ f f' g w)).hom ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f g) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ))
      (sectionsUnit f) ≫
    Functor.whiskerRight (derivedPushforwardUnit g.toLRSHom.toShHom) (sections f)

/-- **[Stacks, Tag 0D5W] over a map of base rings, as a statement about derived functors.**
`Rg_* ⋙ RΓ_A(X, -)`, with the Leray unit, is a right derived functor of `Γ_B(X', -)` restricted
to `A`. -/
theorem isRightDerivedFunctor_lerayUnit :
    (derivedPushforward g.toLRSHom.toShHom ⋙ sections f).IsRightDerivedFunctor
      (lerayUnit φ f f' g w) (qis X') := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I hI => ?_
  have h₁ := isIso_sectionsUnit_app_pushforward f g I
  have h₂ := isIso_derivedPushforwardUnit_app_of_isKInjective g.toLRSHom.toShHom I hI
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- The Leray comparison `RΓ_B(X', -) ⋙ res_φ ⟶ Rg_* ⋙ RΓ_A(X, -)`, induced by the Leray unit
through the universal property of the right derived functor `RΓ_B(X', -) ⋙ res_φ`. -/
def lerayHom :
    sections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory ⟶
      derivedPushforward g.toLRSHom.toShHom ⋙ sections f :=
  (sections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory).rightDerivedDesc
    (Functor.whiskerRight (sectionsUnit f') (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (qis X') _ (lerayUnit φ f f' g w)

/-- The equation characterizing the Leray comparison: composed with the unit of
`RΓ_B(X', -) ⋙ res_φ` it is the Leray unit. -/
theorem lerayHom_fac :
    Functor.whiskerRight (sectionsUnit f') (ModuleCat.restrictScalars φ).mapDerivedCategory ≫
        Functor.whiskerLeft DerivedCategory.Qh (lerayHom φ f f' g w) =
      lerayUnit φ f f' g w :=
  (sections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory).rightDerived_fac
    (Functor.whiskerRight (sectionsUnit f') (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (qis X') _ (lerayUnit φ f f' g w)

/-- The Leray comparison `lerayHom` is an isomorphism. -/
instance isIso_lerayHom : IsIso (lerayHom φ f f' g w) :=
  have := isRightDerivedFunctor_lerayUnit φ f f' g w
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (sections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (L := DerivedCategory.Qh)
    (Functor.whiskerRight (sectionsUnit f') (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (qis X') _ (lerayUnit φ f f' g w)).1 inferInstance

/-- **The Leray isomorphism over `φ`** ([Stacks, Tag 0D5W]):
`RΓ_B(X', -) ⋙ res_φ ≅ Rg_* ⋙ RΓ_A(X, -)` as functors `D(𝒪_{X'}) ⥤ D(A)`. -/
def lerayIso :
    sections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory ≅
      derivedPushforward g.toLRSHom.toShHom ⋙ sections f :=
  asIso (lerayHom φ f f' g w)

/-- **Pulling derived global sections back along `g`**: the map
`RΓ_A(X, F) ⟶ RΓ_B(X', Lg^* F)` of `D(A)`, derived global sections of the unit
`F ⟶ Rg_* Lg^* F` of the derived adjunction followed by the inverse Leray isomorphism. -/
def pullbackSectionsMap
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (sections f).obj F ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
      ((sections f').obj ((derivedPullback g.toLRSHom.toShHom).obj F)) :=
  (sections f).map ((derivedAdjunction g.toLRSHom.toShHom).unit.app F) ≫
    (lerayIso φ f f' g w).inv.app ((derivedPullback g.toLRSHom.toShHom).obj F)

end Leray

end AlgebraicGeometry.LerayOver

end
