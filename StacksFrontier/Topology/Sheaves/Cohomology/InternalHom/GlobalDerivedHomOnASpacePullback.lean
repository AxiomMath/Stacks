module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.GlobalDerivedHomOnASpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsTerminalObject
import StacksCore.Tactic.StacksAttribute

/-!
# The global derived hom along a morphism of ringed spaces

Let `f : (Y, O_Y) ⟶ (X, O_X)` be a morphism of ringed spaces and let `K`, `L` be objects of
`D(O_X)`. Stacks 0B6A asserts a canonical map

`RHom_X(K, L) ⟶ RHom_Y(Lf^*K, Lf^*L)`

in `D(Γ(X, O_X))`, obtained by taking global sections of the map
`Lf^* RSheafHom(K, L) ⟶ RSheafHom(Lf^*K, Lf^*L)` of Stacks 08I3. The target is an object of
`D(Γ(Y, O_Y))`, read in `D(Γ(X, O_X))` by restriction of scalars along the ring map
`Γ(X, O_X) ⟶ Γ(Y, O_Y)` of `f`. This file constructs the map.

## Main definitions

* `Stacks.SheafOfModules.globalSectionEvalTop`: the evaluation `Γ(X, O_X) ⟶ O_X(X)` of a
  compatible family of global sections at the whole space, and
  `Stacks.SheafOfModules.globalSectionEvalTopEquiv`: it is a ring isomorphism.
* `Stacks.SheafOfModules.ringedSpaceGlobalSectionRingMap`: the ring map `Γ(X, O_X) ⟶ Γ(Y, O_Y)` of a
  morphism of ringed spaces.
* `Stacks.SheafOfModules.globalSectionsTopIso`: global sections valued in `Γ(X, O_X)`-modules,
  computed on the ringed site of `X`, are sections over the whole space with scalars restricted
  along `globalSectionEvalTop`.
* `Stacks.SheafOfModules.derivedGlobalSectionsTopIso`: derived global sections valued in
  `Γ(X, O_X)`-modules, computed on the ringed site of `X`, are derived sections over the whole
  space with scalars restricted along `globalSectionEvalTop`.
* `Stacks.SheafOfModules.globalDerivedHomPullbackMap`: **the canonical map
  `RHom_X(K, L) ⟶ RHom_Y(Lf^*K, Lf^*L)` of Stacks 0B6A** in `D(Γ(X, O_X))`.

## Implementation notes

*The map on global sections.* Taking global sections of a map of `D(O_Y)` gives a map of
`D(Γ(Y, O_Y))`; what turns the source `RΓ(Y, Lf^* RSheafHom(K, L))` into
`RΓ(X, RSheafHom(K, L))` is the canonical map `RΓ(X, N) ⟶ RΓ(Y, Lf^*N)` of `D(Γ(X, O_X))`,
`Stacks.Cohomology.DerivedSectionsPullback.sectionsPullback`: derived global sections of the unit
`N ⟶ Rf_* Lf^* N` of the adjunction of Stacks 079W, followed by the identification
`RΓ(X, Rf_* -) = RΓ(Y, -)` of Stacks 0D5W. The map of this file is that map at
`N = RSheafHom(K, L)`, followed by derived global sections of the map of Stacks 08I3, and by the
identification of derived global sections on `Y` with scalars through `Γ(X, O_X)` with the
`Γ(Y, O_Y)`-valued ones followed by restriction of scalars
(`Stacks.Cohomology.DerivedSectionsPullback.changeScalarsIso`).

*Two readings of derived global sections.* The global derived hom
`Stacks.SheafOfModules.globalDerivedHom` takes derived global sections on the ringed site of `X`,
valued in modules over the ring `Γ(X, O_X)` of compatible families of global sections; the maps
above are stated for derived sections over the open `X` of the space, valued in modules over
`O_X(X)` with scalars restricted along a ring map. The open `X` is a terminal object of the site,
so a compatible family is its value there
(`Stacks.Cohomology.SiteModules.bijective_globalSectionsEval`), and the two underived functors are
isomorphic (`globalSectionsTopIso`). The universal property of each right derived functor gives a
comparison map to the other (`derivedGlobalSectionsToTop`, `derivedGlobalSectionsFromTop`), the two
are mutually inverse by the uniqueness clause of the same universal properties, and
`derivedGlobalSectionsTopIso` is the resulting isomorphism.

The two readings name the structure sheaf at two spellings,
`Stacks.SheafOfModules.Tensor.ringSheaf` and `structureSheafRing`, that agree only after
unfolding. Instance search does not identify the quasi-isomorphism classes and localization
functors of the two, so each comparison is stated through the universal property of its own
source, where every instance is the one that source was built with, and the equations between
them are proved by `change` and transitivity rather than by rewriting.

## References

* [Stacks Project, Tag 0B6A](https://stacks.math.columbia.edu/tag/0B6A)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.SiteModules Stacks.Cohomology.DerivedSectionsPullback
open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The ring of global sections of a ringed space -/

section Ring

variable (Z : RingedSpace.{u, u})

/-- The whole space is a terminal object of the site of opens. -/
def isTerminalTopOpens : IsTerminal (⊤ : Opens Z.carrier) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

/-- The evaluation `Γ(Z, O_Z) ⟶ O_Z(Z)` of a compatible family of global sections of the
structure sheaf at the whole space. -/
abbrev globalSectionEvalTop :
    GlobalSectionRing (Tensor.ringSheaf (ringedSite Z.sheaf).O) →+*
      (structureSheafRing Z).obj.obj (op ⊤) :=
  globalSectionEval (Tensor.ringSheaf (ringedSite Z.sheaf).O) (op ⊤)

/-- A compatible family of global sections of the structure sheaf is determined by, and may be
prescribed arbitrarily as, its value on the whole space. -/
theorem bijective_globalSectionEvalTop : Function.Bijective (globalSectionEvalTop Z) := by
  let O := Tensor.ringSheaf (ringedSite Z.sheaf).O
  have key : ∀ (s : GlobalSectionRing O) (W : (Opens Z.carrier)ᵒᵖ),
      (O.obj ⋙ forget RingCat).map ((isTerminalTopOpens Z).from W.unop).op (s.1 (op ⊤)) =
        s.1 W :=
    fun s W ↦ s.2 ((isTerminalTopOpens Z).from W.unop).op
  refine ⟨fun s t hst ↦ Subtype.ext (funext fun W ↦ ?_), fun x ↦ ?_⟩
  · rw [← key s W, ← key t W]
    exact congrArg _ hst
  · refine ⟨⟨fun W ↦ (O.obj ⋙ forget RingCat).map ((isTerminalTopOpens Z).from W.unop).op
      (show (O.obj ⋙ forget RingCat).obj (op ⊤) from x), ?_⟩, ?_⟩
    · intro W W' g
      change (O.obj ⋙ forget RingCat).map g
        ((O.obj ⋙ forget RingCat).map ((isTerminalTopOpens Z).from W.unop).op _) = _
      rw [← Functor.map_comp_apply,
        show ((isTerminalTopOpens Z).from W.unop).op ≫ g =
          ((isTerminalTopOpens Z).from W'.unop).op from
          Quiver.Hom.unop_inj ((isTerminalTopOpens Z).hom_ext _ _)]
    · change (O.obj ⋙ forget RingCat).map ((isTerminalTopOpens Z).from ⊤).op
        (show (O.obj ⋙ forget RingCat).obj (op ⊤) from x) = x
      rw [show ((isTerminalTopOpens Z).from ⊤).op = 𝟙 (op ⊤) from
        Quiver.Hom.unop_inj ((isTerminalTopOpens Z).hom_ext _ _), Functor.map_id_apply]

/-- The ring `Γ(Z, O_Z)` of compatible families of global sections of the structure sheaf is the
ring `O_Z(Z)` of sections over the whole space. -/
def globalSectionEvalTopEquiv :
    GlobalSectionRing (Tensor.ringSheaf (ringedSite Z.sheaf).O) ≃+*
      (structureSheafRing Z).obj.obj (op ⊤) :=
  RingEquiv.ofBijective (globalSectionEvalTop Z) (bijective_globalSectionEvalTop Z)

variable {Y X : RingedSpace.{u, u}} (f : Y ⟶ X)

/-- **The ring map `Γ(X, O_X) ⟶ Γ(Y, O_Y)` of a morphism of ringed spaces** `f : Y ⟶ X`, on
compatible families of global sections: `f^♯ : O_X(X) ⟶ O_Y(Y)` read through the evaluations at
the whole spaces. -/
def ringedSpaceGlobalSectionRingMap :
    GlobalSectionRing (Tensor.ringSheaf (ringedSite X.sheaf).O) →+*
      GlobalSectionRing (Tensor.ringSheaf (ringedSite Y.sheaf).O) :=
  (globalSectionEvalTopEquiv Y).symm.toRingHom.comp
    ((globalRingHom f).comp (globalSectionEvalTop X))

/-- The ring map of `f` on compatible families of global sections lifts `f^♯` on sections over the
whole spaces. -/
theorem globalSectionEvalTop_comp_ringedSpaceGlobalSectionRingMap :
    (globalRingHom f).comp (globalSectionEvalTop X) =
      (globalSectionEvalTop Y).comp (ringedSpaceGlobalSectionRingMap f) :=
  RingHom.ext fun _ ↦ ((globalSectionEvalTopEquiv Y).apply_symm_apply _).symm

end Ring

/-! ### The two readings of derived global sections -/

section Sections

variable (Z : RingedSpace.{u, u})

/-- The universe lift of modules into the universe they already live in is the identity. -/
def uliftFunctorIsoId (R : Type u) [Ring R] : ModuleCat.uliftFunctor.{u} R ≅ 𝟭 (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun M ↦ (ULift.moduleEquiv (R := R) (M := M)).toModuleIso) (fun _ ↦ rfl)

/-- **Global sections on the ringed site are sections over the whole space.** The
`Γ(Z, O_Z)`-module of compatible families of global sections of an `O_Z`-module is its module of
sections over `Z`, with scalars restricted along `globalSectionEvalTop`: the whole space is a
terminal object of the site (`Stacks.Cohomology.SiteModules.globalSectionsIsoEvaluation`). -/
def globalSectionsTopIso :
    RingedSite.globalSectionsModules (ringedSite Z.sheaf) ≅
      scalarSections Z (globalSectionEvalTop Z) :=
  globalSectionsIsoEvaluation.{u, u, u, u} (Tensor.ringSheaf (ringedSite Z.sheaf).O)
      (isTerminalTopOpens Z) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (uliftFunctorIsoId _) ≪≫
      Functor.rightUnitor _)

/-- `globalSectionsTopIso` read on the homotopy category and followed by the localization. -/
def homotopyGlobalSectionsTopIso :
    RingedSite.homotopyGlobalSectionsModules (ringedSite Z.sheaf) ≅
      homotopyScalarSections Z (globalSectionEvalTop Z) :=
  Functor.isoWhiskerRight
    (@Stacks.Cohomology.LinearDerivedSections.mapHomotopyCategoryIso _ _ _ _
      (SheafOfModules.instPreadditive _) _ _ _ _
      (globalSectionsFunctor_additive.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Z.sheaf).O))
      { map_add := rfl } (globalSectionsTopIso Z) (ComplexShape.up ℤ))
    DerivedCategory.Qh

/-- **Derived global sections on the ringed site, compared with derived sections over the whole
space**: the canonical map `RΓ(Z, -) ⟶ RΓ(Z, -)` from the right derived functor of
`Γ(Z, O_Z)`-valued global sections on the ringed site of `Z` to derived sections over the whole
space with scalars restricted along `globalSectionEvalTop`, given by the universal property of the
first applied to `globalSectionsTopIso` followed by the unit of the second. -/
def derivedGlobalSectionsToTop :
    RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf) ⟶
      derivedScalarSections Z (globalSectionEvalTop Z) :=
  (RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf)).rightDerivedDesc
    (RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (derivedScalarSections Z (globalSectionEvalTop Z))
    ((homotopyGlobalSectionsTopIso Z).hom ≫ derivedScalarSectionsUnit Z (globalSectionEvalTop Z))

/-- **Derived sections over the whole space, compared with derived global sections on the ringed
site**: the canonical map in the other direction, given by the universal property of derived
sections over the whole space applied to the inverse of `globalSectionsTopIso` followed by the
unit of derived global sections on the ringed site. -/
def derivedGlobalSectionsFromTop :
    derivedScalarSections Z (globalSectionEvalTop Z) ⟶
      RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf) :=
  (derivedScalarSections Z (globalSectionEvalTop Z)).rightDerivedDesc
    (derivedScalarSectionsUnit Z (globalSectionEvalTop Z))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf))
    ((homotopyGlobalSectionsTopIso Z).inv ≫
      RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf))

/-- The comparison `derivedGlobalSectionsToTop` composed after the unit of derived global sections
on the ringed site is `globalSectionsTopIso` followed by the unit of derived sections over the
whole space. -/
theorem derivedGlobalSectionsModulesUnit_comp_toTop
    (K : HomotopyCategory (SheafOfModules.{u} (Tensor.ringSheaf (ringedSite Z.sheaf).O))
      (ComplexShape.up ℤ)) :
    (RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf)).app K ≫
        (derivedGlobalSectionsToTop Z).app (DerivedCategory.Qh.obj K) =
      (homotopyGlobalSectionsTopIso Z).hom.app K ≫
        (derivedScalarSectionsUnit Z (globalSectionEvalTop Z)).app K :=
  Functor.rightDerived_fac_app (RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf))
    (RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (derivedScalarSections Z (globalSectionEvalTop Z))
    ((homotopyGlobalSectionsTopIso Z).hom ≫ derivedScalarSectionsUnit Z (globalSectionEvalTop Z)) K

/-- The comparison `derivedGlobalSectionsFromTop` composed after the unit of derived sections over
the whole space is the inverse of `globalSectionsTopIso` followed by the unit of derived global
sections on the ringed site. -/
theorem derivedScalarSectionsUnit_comp_fromTop
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (derivedScalarSectionsUnit Z (globalSectionEvalTop Z)).app K ≫
        (derivedGlobalSectionsFromTop Z).app (DerivedCategory.Qh.obj K) =
      (homotopyGlobalSectionsTopIso Z).inv.app K ≫
        (RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf)).app K :=
  Functor.rightDerived_fac_app (derivedScalarSections Z (globalSectionEvalTop Z))
    (derivedScalarSectionsUnit Z (globalSectionEvalTop Z))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf))
    ((homotopyGlobalSectionsTopIso Z).inv ≫
      RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf)) K

/-- The two comparisons of derived global sections compose to the identity on the ringed site. -/
theorem derivedGlobalSectionsToTop_comp_fromTop :
    derivedGlobalSectionsToTop Z ≫ derivedGlobalSectionsFromTop Z = 𝟙 _ := by
  refine (RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf)).rightDerived_ext
    (RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  change (RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf)).app K ≫
      ((derivedGlobalSectionsToTop Z).app _ ≫ (derivedGlobalSectionsFromTop Z).app _) =
    (RingedSite.derivedGlobalSectionsModulesUnit (ringedSite Z.sheaf)).app K ≫ 𝟙 _
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.comp_id _).symm)
  refine (congrArg (· ≫ (derivedGlobalSectionsFromTop Z).app _)
    (derivedGlobalSectionsModulesUnit_comp_toTop Z K)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((homotopyGlobalSectionsTopIso Z).hom.app K ≫ ·)
    (derivedScalarSectionsUnit_comp_fromTop Z K)).trans ?_
  exact Iso.hom_inv_id_app_assoc _ _ _

/-- The two comparisons of derived global sections compose to the identity over the whole
space. -/
theorem derivedGlobalSectionsFromTop_comp_toTop :
    derivedGlobalSectionsFromTop Z ≫ derivedGlobalSectionsToTop Z = 𝟙 _ := by
  refine (derivedScalarSections Z (globalSectionEvalTop Z)).rightDerived_ext
    (derivedScalarSectionsUnit Z (globalSectionEvalTop Z))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  change (derivedScalarSectionsUnit Z (globalSectionEvalTop Z)).app K ≫
      ((derivedGlobalSectionsFromTop Z).app _ ≫ (derivedGlobalSectionsToTop Z).app _) =
    (derivedScalarSectionsUnit Z (globalSectionEvalTop Z)).app K ≫ 𝟙 _
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.comp_id _).symm)
  refine (congrArg (· ≫ (derivedGlobalSectionsToTop Z).app _)
    (derivedScalarSectionsUnit_comp_fromTop Z K)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((homotopyGlobalSectionsTopIso Z).inv.app K ≫ ·)
    (derivedGlobalSectionsModulesUnit_comp_toTop Z K)).trans ?_
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- **Derived global sections on the ringed site are derived sections over the whole space**:
`RΓ(Z, -) : D(O_Z) ⥤ D(Γ(Z, O_Z))`, the right derived functor of global sections on the ringed
site of `Z`, is derived sections over `Z` with scalars restricted along `globalSectionEvalTop`. -/
def derivedGlobalSectionsTopIso :
    RingedSite.derivedGlobalSectionsModules (ringedSite Z.sheaf) ≅
      derivedScalarSections Z (globalSectionEvalTop Z) where
  hom := derivedGlobalSectionsToTop Z
  inv := derivedGlobalSectionsFromTop Z
  hom_inv_id := derivedGlobalSectionsToTop_comp_fromTop Z
  inv_hom_id := derivedGlobalSectionsFromTop_comp_toTop Z

end Sections

/-! ### The canonical map of Stacks 0B6A -/

variable {Y X : RingedSpace.{u, u}} (f : Y ⟶ X)

/-- **Stacks 0B6A, the canonical map `RHom_X(K, L) ⟶ RHom_Y(Lf^*K, Lf^*L)`** in `D(Γ(X, O_X))`
for a morphism of ringed spaces `f : (Y, O_Y) ⟶ (X, O_X)` and objects `K`, `L` of `D(O_X)`; the
target, an object of `D(Γ(Y, O_Y))`, is read in `D(Γ(X, O_X))` by restriction of scalars along
the ring map `ringedSpaceGlobalSectionRingMap f : Γ(X, O_X) ⟶ Γ(Y, O_Y)`.

It is obtained by taking global sections of the map
`Lf^* RSheafHom(K, L) ⟶ RSheafHom(Lf^*K, Lf^*L)` of Stacks 08I3
(`Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap`), preceded by the
canonical map `RΓ(X, N) ⟶ RΓ(Y, Lf^*N)` at `N = RSheafHom(K, L)`
(`Stacks.Cohomology.DerivedSectionsPullback.sectionsPullback`: derived global sections of the unit
of `Lf^* ⊣ Rf_*`, then `RΓ(X, Rf_* -) = RΓ(Y, -)`). Derived global sections are passed between
the ringed site and the open `X` (resp. `Y`) of the space by `derivedGlobalSectionsTopIso`, and the
scalars of `Γ(Y, O_Y)` are restricted to `Γ(X, O_X)` by
`Stacks.Cohomology.DerivedSectionsPullback.changeScalarsIso`. -/
@[stacks 0B6A "the canonical map RHom_X(K, L) → RHom_Y(Lf^*K, Lf^*L) in D(Γ(X, O_X)) of a \
morphism of ringed spaces f : Y → X, by global sections of the map of Remark 08I3"]
def globalDerivedHomPullbackMap
    (K L : DerivedCategory (StructureSheafModules X.sheaf)) :
    ((globalDerivedHom X.sheaf).obj (op K)).obj L ⟶
      (derivedRestrictScalars (ringedSpaceGlobalSectionRingMap f)).obj
        (((globalDerivedHom Y.sheaf).obj
            (op ((derivedPullback f).obj K))).obj ((derivedPullback f).obj L)) :=
  (derivedGlobalSectionsTopIso X).hom.app _ ≫
    sectionsPullback f (globalSectionEvalTop X) _ ≫
      (derivedScalarSections Y ((globalRingHom f).comp (globalSectionEvalTop X))).map
        (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap f K L) ≫
        (changeScalarsIso Y (ringedSpaceGlobalSectionRingMap f)
          (globalSectionEvalTop_comp_ringedSpaceGlobalSectionRingMap f)).hom.app _ ≫
          (derivedRestrictScalars (ringedSpaceGlobalSectionRingMap f)).map
            ((derivedGlobalSectionsTopIso Y).inv.app _)

end Stacks.SheafOfModules

end
