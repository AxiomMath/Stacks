module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.VerticalPasting
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality

/-!
# The derived base change map and a Mayer–Vietoris cover of the source

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes with `g` and `g'` flat. This file proves two statements about
the base change map `β : g^* Rf_* ⟶ Rf'_* (g')^*` of [Stacks, Tag 02N7].

* **Vertical pasting.** For a flat `j : U ⟶ X` and a square `h ≫ j = j' ≫ g'` over it, at a
  bounded below complex `K` of injective `𝒪_U`-modules at which the base change map of the
  square of `j` is invertible, the base change map of the composite square `U ⟶ X ⟶ S` is
  invertible at `K` exactly when `β` is invertible at `j_* K`.
* **Mayer–Vietoris.** For a cover `X = U ∪ V` by two opens and a bounded below complex `I` of
  injective `𝒪_X`-modules, `β` is invertible at `I` as soon as, for `W` each of `U`, `V` and
  `U ∩ V`, the base change maps of the square of the inclusion `W ⟶ X` and of the composite
  square `W ⟶ X ⟶ S` are invertible at `I|_W`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_schemeBaseChange_comp_iff`
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_schemeBaseChange_of_cover`

## References

* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeDerived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

attribute [local instance] abelianModules enoughInjectivesModules

/-- Pushforward along a flat morphism of schemes preserves injective modules. -/
theorem preservesInjectiveObjects_pushforward {A B : Scheme.{u}} (j : A ⟶ B) [Flat j] :
    (modulePushforward j.toLRSHom.toShHom).PreservesInjectiveObjects :=
  modulePushforward_preservesInjectiveObjects _ (isFlat_toShHom j)

/-- Pushforward of sheaves of modules along a composite of morphisms of schemes is the composite
of the pushforwards. -/
theorem modulePushforward_comp_eq {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    modulePushforward (a ≫ b).toLRSHom.toShHom =
      modulePushforward a.toLRSHom.toShHom ⋙ modulePushforward b.toLRSHom.toShHom :=
  rfl

section Vertical

variable {U U' X X' S S' : Scheme.{u}} {j : U ⟶ X} {j' : U' ⟶ X'} {h : U' ⟶ U}
  {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
  (wj : h ≫ j = j' ≫ g') (wf : g' ≫ f = f' ≫ g)

include wj wf in
/-- The underived base change map of the outer rectangle is the base change map of the lower
square at `j_* M` followed by `f'_*` of the base change map of the upper square at `M`. -/
theorem schemeModuleBaseChange_vertical_app (M : _root_.SheafOfModules.{u}
    (structureSheafRing U.toRingedSpace)) :
    (schemeModuleBaseChange (j ≫ f) (j' ≫ f') g h
        (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.vertical_comm wj wf)).app M =
      (schemeModuleBaseChange f f' g g' wf).app
          ((modulePushforward j.toLRSHom.toShHom).obj M) ≫
        (modulePushforward f'.toLRSHom.toShHom).map
          ((schemeModuleBaseChange j j' g' h wj).app M) := by
  rw [moduleBaseChange_eq, moduleBaseChange_eq, moduleBaseChange_eq]
  exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_vertical_app wj wf M

variable [Flat g] [Flat g'] [Flat h] [Flat j] [Flat j']

include wj wf in
/-- **Vertical pasting for the derived base change map, at a complex of injectives.** If the
base change map of the square of `j` is invertible at a bounded below complex `K` of injective
`𝒪_U`-modules, then the base change map of the composite square is invertible at `K` exactly
when the base change map of the square of `f` is invertible at `j_* K`. -/
theorem isIso_schemeBaseChange_comp_iff
    (K : HomotopyCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing U.toRingedSpace)))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n))
    (htop : IsIso ((schemeBaseChange j j' g' h wj).app (DerivedCategory.Plus.Qh.obj K))) :
    IsIso ((schemeBaseChange (j ≫ f) (j' ≫ f') g h
        (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.vertical_comm wj wf)).app
          (DerivedCategory.Plus.Qh.obj K)) ↔
      IsIso ((schemeBaseChange f f' g g' wf).app (DerivedCategory.Plus.Qh.obj
        ((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K))) := by
  have := preservesInjectiveObjects_pushforward j
  have := preservesInjectiveObjects_pushforward j'
  have := isIso_pullbackUnit g'
  have := isIso_pullbackUnit h
  have hρ : ∀ M : _root_.SheafOfModules.{u} (structureSheafRing U.toRingedSpace),
      HEq ((schemeModuleBaseChange (j ≫ f) (j' ≫ f') g h
        (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.vertical_comm wj wf)).app M)
      ((schemeModuleBaseChange f f' g g' wf).app
          ((modulePushforward j.toLRSHom.toShHom).obj M) ≫
        (modulePushforward f'.toLRSHom.toShHom).map
          ((schemeModuleBaseChange j j' g' h wj).app M)) :=
    fun M => heq_of_eq (schemeModuleBaseChange_vertical_app wj wf M)
  exact Stacks.Cohomology.BaseChange.isIso_derived_comp_app_iff'
    (modulePushforward j.toLRSHom.toShHom) (modulePushforward j'.toLRSHom.toShHom)
    (modulePullback h.toLRSHom.toShHom) (modulePushforward f.toLRSHom.toShHom)
    (modulePushforward f'.toLRSHom.toShHom) (modulePullback g.toLRSHom.toShHom)
    (modulePullback g'.toLRSHom.toShHom) (schemeModuleBaseChange j j' g' h wj)
    (schemeModuleBaseChange f f' g g' wf)
    (Stacks.Cohomology.FlatBaseChange.flatPullbackComparison g.toLRSHom.toShHom
      (isFlat_toShHom g))
    (Stacks.Cohomology.FlatBaseChange.flatPullbackComparison g'.toLRSHom.toShHom
      (isFlat_toShHom g'))
    (modulePushforward (j ≫ f).toLRSHom.toShHom) (modulePushforward_comp_eq j f)
    (modulePushforward (j' ≫ f').toLRSHom.toShHom) (modulePushforward_comp_eq j' f')
    (schemeModuleBaseChange (j ≫ f) (j' ≫ f') g h
      (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.vertical_comm wj wf))
    hρ
    K hK htop

end Vertical

/-! ### Restricting a resolution to an open -/

section Resolution

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [Flat j]

/-- In `D⁺(𝒪_Y)`, pulling back a bounded below complex `K` along a flat `j` computes the derived
pullback of `K`. -/
def pullbackQhIso (K : HomotopyCategory.Plus
      (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    DerivedCategory.Plus.Qh.obj
        ((modulePullback j.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K) ≅
      (modulePullback j.toLRSHom.toShHom).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj K) :=
  (Stacks.Cohomology.FlatBaseChange.flatPullbackComparison j.toLRSHom.toShHom
    (isFlat_toShHom j)).app K

/-- **The pullback of a resolution is a resolution.** If `K` is a bounded below complex with
`Qh K ≅ F` in `D⁺(𝒪_X)`, then `Qh (j^* K) ≅ j^* F` in `D⁺(𝒪_Y)`, for `j` flat. -/
def pullbackResolutionIso (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (K : HomotopyCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (e : DerivedCategory.Plus.Qh.obj K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj F) :
    DerivedCategory.Plus.Qh.obj
        ((modulePullback j.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((modulePullback j.toLRSHom.toShHom).obj F) :=
  pullbackQhIso j K ≪≫ (modulePullback j.toLRSHom.toShHom).rightDerivedFunctorPlus.mapIso
      (e ≪≫ (Functor.singleFunctorPlusIsoCompQh 0).app F) ≪≫
    (pullbackQhIso j _).symm ≪≫
    DerivedCategory.Plus.Qh.mapIso
      ((Functor.mapHomotopyCategoryPlusSingleFunctor
        (modulePullback j.toLRSHom.toShHom) 0).app F) ≪≫
    ((Functor.singleFunctorPlusIsoCompQh 0).app _).symm

end Resolution

/-! ### A cover of the source by two opens -/

section Cover

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
  (w : g' ≫ f = f' ≫ g) [Flat g] [Flat g']

/-- Restriction to an open followed by pushforward back is pullback followed by pushforward along
the inclusion of the open subscheme. -/
def restrictPushIso (W : X.Opens) :
    Stacks.Cohomology.RestrictionCover.restrictPush (structureSheafRing X.toRingedSpace) W ≅
      modulePullback W.ι.toLRSHom.toShHom ⋙ modulePushforward W.ι.toLRSHom.toShHom :=
  Functor.isoWhiskerRight
    (Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso X.toRingedSpace W)
    (modulePushforward W.ι.toLRSHom.toShHom)

include w in
/-- **The restriction step.** Let `I` be a bounded below complex of injective `𝒪_X`-modules with
`I ≅ F` in `D⁺(𝒪_X)`. If the base change maps of the square of the inclusion of an open `W` and of
the composite square `W ⟶ X ⟶ S` are invertible at `F|_W`, then `β` is invertible at the
restriction of `I` to `W`, pushed forward back to `X`. -/
theorem isIso_schemeBaseChange_restrictPush (W : X.Opens)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (I : CochainComplex.Plus (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hI : ∀ n, Injective (I.obj.X n))
    (e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj F)
    (hT : IsIso ((schemeBaseChange W.ι (g' ⁻¹ᵁ W).ι g' (g' ∣_ W) (morphismRestrict_ι g' W)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ((modulePullback W.ι.toLRSHom.toShHom).obj F))))
    (hC : IsIso ((schemeBaseChange (W.ι ≫ f) ((g' ⁻¹ᵁ W).ι ≫ f') g (g' ∣_ W)
      (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.vertical_comm
        (morphismRestrict_ι g' W) w)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((modulePullback W.ι.toLRSHom.toShHom).obj F)))) :
    IsIso ((schemeBaseChange f f' g g' w).app
      (Stacks.Cohomology.RestrictionCover.plusQ (structureSheafRing X.toRingedSpace)
        ((Stacks.Cohomology.RestrictionCover.restrictPush (structureSheafRing X.toRingedSpace)
          W).mapCochainComplexPlus.obj I))) := by
  let K := (HomotopyCategory.Plus.quotient _).obj I
  let K' := (modulePullback W.ι.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K
  have hK' : ∀ n : ℤ, Injective (K'.obj.as.X n) := fun n =>
    have := Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects
      W.ι.toLRSHom.toShHom
    Functor.PreservesInjectiveObjects.injective_obj (hI n)
  let e' := pullbackResolutionIso W.ι F K e
  exact Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _
    (DerivedCategory.Plus.Qh.mapIso
      ((Stacks.Cohomology.BaseChange.mapPlusIso (restrictPushIso W)).app K))
    ((isIso_schemeBaseChange_comp_iff (morphismRestrict_ι g' W) w K' hK'
      (Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _ e' hT)).1
      (Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _ e' hC))

include w in
/-- **Mayer–Vietoris for the derived base change map.** Let `X = U ∪ V` be a cover by two opens and
let `F` be an `𝒪_X`-module. If, for `W` each of `U`, `V` and `U ∩ V`, the base change maps of the
square of the inclusion of `W` and of the composite square `W ⟶ X ⟶ S` are invertible at `F|_W`,
then the base change map `β` of the square is invertible at `F`. -/
theorem isIso_schemeBaseChange_of_cover (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hT : ∀ W ∈ ({U, V, U ⊓ V} : Set X.Opens),
      IsIso ((schemeBaseChange W.ι (g' ⁻¹ᵁ W).ι g' (g' ∣_ W) (morphismRestrict_ι g' W)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((modulePullback W.ι.toLRSHom.toShHom).obj F))))
    (hC : ∀ W ∈ ({U, V, U ⊓ V} : Set X.Opens),
      IsIso ((schemeBaseChange (W.ι ≫ f) ((g' ⁻¹ᵁ W).ι ≫ f') g (g' ∣_ W)
        (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.vertical_comm
          (morphismRestrict_ι g' W) w)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((modulePullback W.ι.toLRSHom.toShHom).obj F)))) :
    IsIso ((schemeBaseChange f f' g g' w).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  have := natTransCommShift_schemeBaseChange f f' g g' w
  let R := Stacks.DerivedIndexing.resPlus.obj F
  let I : CochainComplex.Plus (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    ⟨R.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).1 R.property⟩
  have hI : ∀ n, Injective (I.obj.X n) := Stacks.DerivedIndexing.injective_resPlus_obj_X F
  let e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj F :=
    (Stacks.DerivedIndexing.singleIsoResPlusQh.app F).symm
  have key := fun W (hW : W ∈ ({U, V, U ⊓ V} : Set X.Opens)) =>
    isIso_schemeBaseChange_restrictPush w W F I hI e (hT W hW) (hC W hW)
  exact Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _ e.symm
    (Stacks.Cohomology.RestrictionCover.isIso_app_of_restrictionCover _
      (schemeBaseChange f f' g g' w) U V hUV I hI
      (key U (by simp)) (key V (by simp)) (key _ (by simp)))

end Cover

end Stacks.AlgebraicGeometry.FlatBaseChangeDerived

end
