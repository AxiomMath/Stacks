module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.Modules.ClosedImmersion
public import StacksFrontier.Topology.Sheaves.RingedSpace.Comp
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of thickenings of ringed spaces

A *thickening* of ringed spaces is a morphism `i : X ⟶ X'` whose underlying continuous map is a
homeomorphism, whose map on structure sheaves is surjective, and whose kernel ideal is locally
nilpotent. A *morphism of thickenings* is a commutative square of ringed spaces whose horizontal
arrows are thickenings. This file records the square, its two kernel ideal sheaves `I` and `J`,
and the canonical maps relating `(f')^* J` to `I`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.HasLocallyNilpotentKernel`,
  `AlgebraicGeometry.RingedSpaceThickening.IsThickening` and
  `AlgebraicGeometry.RingedSpaceThickening.IsFirstOrderThickening`: the thickening and
  square-zero conditions on a morphism of ringed spaces.
* `AlgebraicGeometry.RingedSpaceThickening.closedQuotientOfIsThickening`: a thickening as a
  `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.
* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings`: the commutative square.
* `MorphismOfThickenings.idealI`, `MorphismOfThickenings.idealJ`: its two kernel ideal sheaves
  `I = ker(i^♯)` on `X'` and `J = ker(t^♯)` on `S'`.
* `MorphismOfThickenings.ambientIdealMap`: the composite `(f')^* J ⟶ 𝒪_{X'}` obtained by pulling
  back `J ⟶ 𝒪_{S'}` and applying `(f')^♯`.
* `MorphismOfThickenings.idealMap`: the canonical map `(f')^* J ⟶ I`.
* `MorphismOfThickenings.reducedPullbackIdeal`: `f^* J`, as the `𝒪_{X'}`-module
  `i_* f^* t^* J`.
* `MorphismOfThickenings.reducedPullbackComparison`: the comparison `i^* (f')^* J ≅ f^* t^* J`
  induced by the commutative square.
* `MorphismOfThickenings.firstOrderSurjection`: the canonical reduction map
  `(f')^* J ⟶ i_* f^* t^* J`.
* `MorphismOfThickenings.IsStrict`: the square is a *strict* morphism of thickenings when
  `(f')^* J ⟶ I` is surjective.

## Main results

* `isIso_unit_app_idealSheaf`: for a first-order thickening the kernel ideal already is a
  module on the reduced space.
* `epi_unit_app_of_isThickening`: for a thickening the unit of `i^* ⊣ i_*` is an epimorphism
  at every module.
* `MorphismOfThickenings.firstOrderSurjection_epi`: the reduction map is surjective when both
  thickenings are first order.
* `MorphismOfThickenings.firstOrderIdealMap`: the ideal map then factors uniquely through the
  reduction, giving the map `f^* J ⟶ I`.

## Implementation notes

The underlying spaces of a thickening are not identified: modules on the thickened space are
moved to the ambient space by module pushforward. So `f^* J`, viewed as an `𝒪_{X'}`-module, is
`reducedPullbackIdeal = i_* f^* t^* J`, and `firstOrderSurjection` is the unit of `i^* ⊣ i_*`
followed by the pushforward of `reducedPullbackComparison`. Local nilpotence is stated
sectionwise and locally on the ambient topological space.

Two vocabularies for the same functors are used: `RingedSpaceModuleAdjunction.modulePullback`
and `RingedSpaceModuleAdjunction.modulePushforward`, and the root-level `pullback` and
`pullbackComp`. They agree definitionally — `ringCatSheaf` and `structureSheafRing` have the same
body, and `toRingCatSheafHom` and `structureSheafHom` both whisker `f.hom.c` with
`forget₂ CommRingCat RingCat`.

`IsThickening` here is a condition on a morphism of ringed spaces. It is a different notion from
the scheme-level `Stacks.Thickenings.IsThickening`.

## References

* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

/-! ### The pullback of the structure sheaf, and maps into it -/

namespace RingedSpaceModuleAdjunction

/-- The canonical map `f^* 𝒪_Y ⟶ 𝒪_X`, i.e. `SheafOfModules.pullbackObjUnitToUnit` with the
right-adjointness of `f_*` supplied. -/
noncomputable def pullbackUnitToUnit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)) ⟶
      SheafOfModules.unit (structureSheafRing X) :=
  let _hadj : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)

/-- The adjunction `f^* ⊣ f_*` transposes `f^* 𝒪_Y ⟶ 𝒪_X` to the unit map `𝒪_Y ⟶ f_* 𝒪_X`. -/
private lemma homEquiv_pullbackUnitToUnit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitToUnit f) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) :=
  Equiv.apply_symm_apply ((modulePullbackPushforwardAdjunction f).homEquiv _ _) _

/-- Transposing `f^* M ⟶ 𝒪_X` across the adjunction `f^* ⊣ f_*` turns `a : M ⟶ 𝒪_Y` pulled back
and followed by `f^* 𝒪_Y ⟶ 𝒪_X` into `a` followed by `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X`. -/
lemma homEquiv_map_comp_pullbackUnitToUnit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (M : SheafOfModules (structureSheafRing Y))
    (a : M ⟶ SheafOfModules.unit (structureSheafRing Y)) :
    (modulePullbackPushforwardAdjunction f).homEquiv _ _
      ((modulePullback f).map a ≫ pullbackUnitToUnit f) =
        a ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) := by
  let _hadj : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  have hnat : (modulePullbackPushforwardAdjunction f).unit.app M ≫
      (modulePushforward f).map ((modulePullback f).map a) =
      a ≫ (modulePullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit (structureSheafRing Y)) := by
    simp
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hnat, Category.assoc,
    ← Adjunction.homEquiv_unit,
    homEquiv_pullbackUnitToUnit]
  rfl

/-- A map `h : K ⟶ 𝒪_Y` killed by `f^♯` pulls back to zero on `𝒪_X`. -/
lemma map_comp_pullbackUnitToUnit_eq_zero {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : SheafOfModules (structureSheafRing Y))
    (h : K ⟶ SheafOfModules.unit (structureSheafRing Y))
    (hh : h ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) = 0) :
    (modulePullback f).map h ≫ pullbackUnitToUnit f = 0 := by
  let _hadj : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  let adj := modulePullbackPushforwardAdjunction f
  have hz : (adj.homEquiv _ _)
      ((modulePullback f).map h ≫ pullbackUnitToUnit f) = 0 := by
    rwa [homEquiv_map_comp_pullbackUnitToUnit]
  apply (adj.homEquiv _ _).injective
  rw [hz]
  rfl

/-- `(f ≫ g)_* ≅ f_* ⋙ g_*`, in the `modulePushforward` spelling. This points from the
pushforward along the composite to the composite of the pushforwards, the reverse of
`CategoryTheory.SheafOfModules.pushforwardComp`. It is equal by `rfl` to `pushforwardComp`; see
`modulePushforwardCompSymm_eq_pushforwardComp`. -/
noncomputable def modulePushforwardCompSymm {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforward (f ≫ g) ≅ modulePushforward f ⋙ modulePushforward g :=
  (modulePushforwardComp f g).symm

/-- The two spellings of the pushforward comparison agree on the nose. -/
lemma modulePushforwardCompSymm_eq_pushforwardComp {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : modulePushforwardCompSymm f g = pushforwardComp f g := rfl

/-- `(f ≫ g)^* ≅ g^* ⋙ f^*`, in the `modulePullback` spelling: both sides are left adjoint to
`(f ≫ g)_*`, so they agree by uniqueness of left adjoints. It is equal by `rfl` to
`pullbackComp`; see `modulePullbackCompUniq_eq_pullbackComp`. -/
noncomputable def modulePullbackCompUniq {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback (f ≫ g) ≅ modulePullback g ⋙ modulePullback f :=
  letI : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  letI : (SheafOfModules.pushforward (structureSheafHom g)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint g
  letI : (SheafOfModules.pushforward (structureSheafHom (f ≫ g))).IsRightAdjoint :=
    modulePushforward_isRightAdjoint (f ≫ g)
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (f ≫ g))
    (((modulePullbackPushforwardAdjunction g).comp
      (modulePullbackPushforwardAdjunction f)).ofNatIsoRight (modulePushforwardCompSymm f g).symm)

/-- The two spellings of the pullback comparison agree on the nose. -/
lemma modulePullbackCompUniq_eq_pullbackComp {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : modulePullbackCompUniq f g = pullbackComp f g := rfl

/-- The comparison `(f ≫ g)^* ≅ g^* ⋙ f^*` is compatible with the maps to the structure
sheaves: on the unit module it carries the two-step map `f^* g^* 𝒪_Z ⟶ f^* 𝒪_Y ⟶ 𝒪_X` to the
one-step map `(f ≫ g)^* 𝒪_Z ⟶ 𝒪_X`. -/
lemma modulePullbackCompUniq_hom_app_unit_comp {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (modulePullbackCompUniq f g).hom.app (SheafOfModules.unit (structureSheafRing Z)) ≫
      (modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f =
    pullbackUnitToUnit (f ≫ g) := by
  let _hf : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  let _hg : (SheafOfModules.pushforward (structureSheafHom g)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint g
  let _hfg : (SheafOfModules.pushforward (structureSheafHom (f ≫ g))).IsRightAdjoint :=
    modulePushforward_isRightAdjoint (f ≫ g)
  let adjf := modulePullbackPushforwardAdjunction f
  let adjg := modulePullbackPushforwardAdjunction g
  let adjfg := modulePullbackPushforwardAdjunction (f ≫ g)
  let e := modulePushforwardCompSymm f g
  let adjseq := (adjg.comp adjf).ofNatIsoRight e.symm
  let α := modulePullbackCompUniq f g
  let p₁ := pullbackUnitToUnit f
  let p₂ := pullbackUnitToUnit g
  let pfg := pullbackUnitToUnit (f ≫ g)
  let q₁ := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)
  let q₂ := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g)
  let qfg := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (f ≫ g))
  change SheafOfModules.unit (structureSheafRing Z) ⟶ (modulePushforward (f ≫ g)).obj
    (SheafOfModules.unit (structureSheafRing X)) at qfg
  change SheafOfModules.unit (structureSheafRing Y) ⟶ (modulePushforward f).obj
    (SheafOfModules.unit (structureSheafRing X)) at q₁
  change SheafOfModules.unit (structureSheafRing Z) ⟶ (modulePushforward g).obj
    (SheafOfModules.unit (structureSheafRing Y)) at q₂
  let z : ((modulePullback g ⋙ modulePullback f).obj (SheafOfModules.unit (structureSheafRing Z))) ⟶
      SheafOfModules.unit (structureSheafRing X) := (modulePullback f).map p₂ ≫ p₁
  have hseq : (adjg.comp adjf).homEquiv _ _ z = q₂ ≫
      (modulePushforward g).map q₁ := by
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply, z]
    rw [adjf.homEquiv_naturality_left, adjg.homEquiv_naturality_right,
      homEquiv_pullbackUnitToUnit, homEquiv_pullbackUnitToUnit]
  have hq : qfg ≫ e.hom.app (SheafOfModules.unit (structureSheafRing X)) =
      q₂ ≫ (modulePushforward g).map q₁ := by
    ext U
    rfl
  apply (adjfg.homEquiv _ _).injective
  show adjfg.homEquiv _ _ (α.hom.app _ ≫ z) = adjfg.homEquiv _ _ pfg
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc]
  unfold α modulePullbackCompUniq
  rw [Adjunction.unit_leftAdjointUniq_hom_app adjfg adjseq, ← Adjunction.homEquiv_unit adjseq,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    ← Adjunction.homEquiv_unit adjfg]
  show ((adjg.comp adjf).homEquiv _ _ z) ≫ e.symm.hom.app _ = _
  rw [hseq, ← hq]
  rw [homEquiv_pullbackUnitToUnit (f ≫ g)]
  show qfg ≫ (e.hom.app (SheafOfModules.unit (structureSheafRing X)) ≫
    e.symm.hom.app (SheafOfModules.unit (structureSheafRing X))) = qfg
  simp only [Iso.symm_hom, e.hom_inv_id_app]
  simp

/-- The comparison `(f ≫ g)^* ≅ g^* ⋙ f^*` carries the pullback along `f` and `g` of a map
`h : M ⟶ 𝒪_Z`, followed by `f^* g^* 𝒪_Z ⟶ f^* 𝒪_Y ⟶ 𝒪_X`, to the pullback of `h` along `f ≫ g`
followed by `(f ≫ g)^* 𝒪_Z ⟶ 𝒪_X`. -/
lemma modulePullbackCompUniq_map_comp_pullbackUnitToUnit {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules (structureSheafRing Z))
    (h : M ⟶ SheafOfModules.unit (structureSheafRing Z)) :
    (modulePullbackCompUniq f g).hom.app M ≫
        (modulePullback f).map ((modulePullback g).map h) ≫
        (modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f =
      (modulePullback (f ≫ g)).map h ≫ pullbackUnitToUnit (f ≫ g) := by
  let α := modulePullbackCompUniq f g
  calc
    α.hom.app M ≫ (modulePullback f).map ((modulePullback g).map h) ≫
        (modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f =
      α.hom.app M ≫ (modulePullback f).map
        ((modulePullback g).map h ≫ pullbackUnitToUnit g) ≫ pullbackUnitToUnit f := by
          simp only [Functor.map_comp, Category.assoc]
    _ = α.hom.app M ≫ (modulePullback g ⋙ modulePullback f).map h ≫
        (modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f := by
          simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    _ = (modulePullback (f ≫ g)).map h ≫ α.hom.app _ ≫
        (modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f := by
          rw [← Category.assoc, ← α.hom.naturality h]
          rfl
    _ = (modulePullback (f ≫ g)).map h ≫
        ((modulePullbackCompUniq f g).hom.app (SheafOfModules.unit (structureSheafRing Z)) ≫
          (modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f) := by rfl
    _ = (modulePullback (f ≫ g)).map h ≫ pullbackUnitToUnit (f ≫ g) := by
          rw [modulePullbackCompUniq_hom_app_unit_comp]

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpaceThickening

/-- The kernel of the structure-sheaf map of a morphism of ringed spaces is locally nilpotent
when every kernel section is nilpotent after restriction to a neighbourhood of each point. -/
def HasLocallyNilpotentKernel {X X' : RingedSpace.{u, u}} (i : X ⟶ X') : Prop :=
  ∀ (U : Opens X') (a : (structureSheafRing X').obj.obj (op U)),
    (structureSheafHom i).hom.app (op U) a = 0 →
      ∀ x : X', x ∈ U →
        ∃ (V : Opens X') (hVU : V ≤ U), x ∈ V ∧
          IsNilpotent ((structureSheafRing X').obj.map (homOfLE hVU).op a)

/-- A thickening of ringed spaces: the underlying continuous map is a homeomorphism, the
structure-sheaf map is surjective, and its kernel ideal is locally nilpotent. -/
def IsThickening {X X' : RingedSpace.{u, u}} (i : X ⟶ X') : Prop :=
  IsIso i.hom.base ∧
    Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)) ∧
      HasLocallyNilpotentKernel i

/-- A first-order thickening is a thickening whose kernel ideal has square zero on every open
subset. -/
def IsFirstOrderThickening {X X' : RingedSpace.{u, u}} (i : X ⟶ X') : Prop :=
  IsThickening i ∧
    ∀ U : Opens X',
      (RingHom.ker ((structureSheafHom i).hom.app (op U)).hom) ^ 2 = ⊥

/-! ### A thickening as a closed quotient morphism -/

/-- The structure-sheaf map of a thickening is locally surjective. -/
theorem isLocallySurjective_of_isThickening {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hi : IsThickening i) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X'.carrier)
      (structureSheafHom i).hom := by
  have : Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)) := hi.2.1
  exact ⟨fun s => (Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))).imageSieve_mem s⟩

/-- A thickening, as a closed quotient morphism of ringed spaces: its underlying map is a
homeomorphism, hence a closed embedding, and its comorphism is locally surjective. -/
noncomputable def closedQuotientOfIsThickening {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hi : IsThickening i) : ClosedQuotientMorphismOfRingedSpaces.{u} where
  X := X'
  Z := X
  i := i
  isClosedEmbedding := by
    change Topology.IsClosedEmbedding i.hom.base
    exact ((TopCat.isIso_iff_isHomeomorph i.hom.base).mp hi.1).isClosedEmbedding
  isLocallySurjective := ⟨fun s => (isLocallySurjective_of_isThickening i hi).imageSieve_mem s⟩

/-- If `a • f m = 0` for a monomorphism `f`, then `a • m = 0`. -/
private theorem smul_eq_zero_of_mono {X' : RingedSpace.{u, u}}
    {N P : SheafOfModules.{u} (structureSheafRing X')} (f : N ⟶ P) [Mono f]
    (U : Opens X') (a : (structureSheafRing X').obj.obj (op U)) (m : N.val.obj (op U))
    (h : a • f.val.app (op U) m = 0) : a • m = 0 := by
  have hinj : Function.Injective (f.val.app (op U)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    show Mono ((SheafOfModules.evaluation (R := structureSheafRing X') (op U)).map f)
    infer_instance
  apply hinj
  rw [_root_.map_smul, _root_.map_zero]
  exact h

/-- A section of the kernel ideal of a first-order thickening annihilates every section of
that ideal: the product of two sections of `ℐ` lies in `ℐ ^ 2 = ⊥`. -/
private theorem squareZero_kernel_smul_eq_zero {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hsq : ∀ U : Opens X', (RingHom.ker ((structureSheafHom i).hom.app (op U)).hom) ^ 2 = ⊥)
    (U : Opens X') (a : (structureSheafRing X').obj.obj (op U))
    (ha : a ∈ RingHom.ker ((structureSheafHom i).hom.app (op U)).hom)
    (m : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op U)) : a • m = 0 := by
  let q := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)
  let j := kernel.ι q
  let b : (structureSheafRing X').obj.obj (op U) := j.val.app (op U) m
  let I : Ideal ((structureSheafRing X').obj.obj (op U)) :=
    RingHom.ker ((structureSheafHom i).hom.app (op U)).hom
  have hbm : b ∈ I := by
    show ((structureSheafHom i).hom.app (op U)).hom b = 0
    have h' := congrArg (fun k : AlgebraicGeometry.SheafOfModules.idealSheaf i ⟶
      (modulePushforward i).obj (SheafOfModules.unit (structureSheafRing X)) => k.val.app (op U) m)
      (kernel.condition q)
    exact h'
  have hmulI : I * I = ⊥ := by
    have hp : I ^ 2 = ⊥ := hsq U
    rwa [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one] at hp
  have hab : a * b = 0 := by
    have hmem : a * b ∈ I * I := Ideal.mul_mem_mul ha hbm
    rw [hmulI] at hmem
    simpa using hmem
  exact smul_eq_zero_of_mono j U a m hab

/-- For a first-order thickening the kernel ideal is already a module on the reduced space: the
unit of `i^* ⊣ i_*` at it is an isomorphism. -/
theorem isIso_unit_app_idealSheaf {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) :
    IsIso ((modulePullbackPushforwardAdjunction i).unit.app
      (AlgebraicGeometry.SheafOfModules.idealSheaf i)) := by
  let S := closedQuotientOfIsThickening i hi.1
  have : (modulePushforward i).Full := S.full_modulePushforward
  have : (modulePushforward i).Faithful := S.faithful_modulePushforward
  refine ((modulePullbackPushforwardAdjunction i).isIso_unit_app_iff_mem_essImage).2 ?_
  exact (S.modulePushforward_essImage_iff _).2 (squareZero_kernel_smul_eq_zero i hi.2)

/-- For an adjunction `L ⊣ R` out of an abelian category, if the unit at the image of `η_A` is an
isomorphism, then `η_A` is an epimorphism. -/
lemma epi_unit_app_of_isIso_unit_app_image {C : Type*} {D : Type*} [Category C]
    [Category D] [Abelian C] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C)
    (h : IsIso (adj.unit.app (Abelian.image (adj.unit.app A)))) :
    Epi (adj.unit.app A) := by
  set n := adj.unit.app A with hn
  set e := Abelian.image.ι n with he
  set p := Abelian.factorThruImage n with hp
  set β := R.map (L.map p) ≫ inv (adj.unit.app (Abelian.image n)) with hβ
  have hnat : e ≫ adj.unit.app (R.obj (L.obj A)) =
      adj.unit.app (Abelian.image n) ≫ R.map (L.map e) := adj.unit.naturality e
  have hkey : β ≫ e ≫ adj.unit.app (R.obj (L.obj A)) = R.map (L.map n) := by
    rw [hnat, hβ, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp,
      ← Functor.map_comp, hp, he, Abelian.image.fac]
  have hsplit : β ≫ e = 𝟙 (R.obj (L.obj A)) := by
    calc β ≫ e = (β ≫ e) ≫ 𝟙 (R.obj (L.obj A)) := (Category.comp_id (β ≫ e)).symm
      _ = (β ≫ e) ≫ adj.unit.app (R.obj (L.obj A)) ≫ R.map (adj.counit.app (L.obj A)) := by
          rw [adj.right_triangle_components]
      _ = (β ≫ e ≫ adj.unit.app (R.obj (L.obj A))) ≫ R.map (adj.counit.app (L.obj A)) := by
          simp only [Category.assoc]
      _ = R.map (L.map n ≫ adj.counit.app (L.obj A)) := by rw [hkey, Functor.map_comp]
      _ = R.map (𝟙 (L.obj A)) := by
          rw [hn]
          exact congrArg (fun f => R.map f) (adj.left_triangle_components A)
      _ = 𝟙 (R.obj (L.obj A)) := R.map_id _
  have : IsSplitEpi e := IsSplitEpi.mk' ⟨β, hsplit⟩
  have hcomp : Epi (p ≫ e) := epi_comp _ _
  rwa [hp, he, Abelian.image.fac] at hcomp

/-- For a thickening the unit of `i^* ⊣ i_*` is an epimorphism at every module. -/
theorem epi_unit_app_of_isThickening {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (hi : IsThickening i) (M : SheafOfModules.{u} (structureSheafRing X')) :
    Epi ((modulePullbackPushforwardAdjunction i).unit.app M) := by
  let S := closedQuotientOfIsThickening i hi
  have : (modulePushforward i).Full := S.full_modulePushforward
  have : (modulePushforward i).Faithful := S.faithful_modulePushforward
  refine epi_unit_app_of_isIso_unit_app_image (modulePullbackPushforwardAdjunction i) M ?_
  refine (modulePullbackPushforwardAdjunction i).isIso_unit_app_iff_mem_essImage.2 ?_
  refine (S.modulePushforward_essImage_iff _).2 ?_
  intro U a ha m
  refine smul_eq_zero_of_mono (X' := X') (Abelian.image.ι _) U a m ?_
  have h0 : ∀ (c : (structureSheafRing X).obj.obj (op ((opensMap i).obj U))) (s : _), c = 0 →
      c • s = (0 : ((modulePullback i).obj M).val.obj (op ((opensMap i).obj U))) :=
    fun c s hc => by rw [hc, zero_smul]
  exact h0 _ _ ha

/-- A morphism of thickenings: a commutative square of ringed spaces whose horizontal arrows are
thickenings. -/
@[stacks 08KZ "the commutative square"]
structure MorphismOfThickenings where
  /-- The upper-left ringed space. -/
  X : RingedSpace.{u, u}
  /-- The upper-right ringed space. -/
  X' : RingedSpace.{u, u}
  /-- The lower-left ringed space. -/
  S : RingedSpace.{u, u}
  /-- The lower-right ringed space. -/
  S' : RingedSpace.{u, u}
  /-- The upper thickening `i : X ⟶ X'`. -/
  i : X ⟶ X'
  /-- The lower thickening `t : S ⟶ S'`. -/
  t : S ⟶ S'
  /-- The morphism on the reduced (left-hand) ringed spaces. -/
  f : X ⟶ S
  /-- The morphism on the ambient (right-hand) ringed spaces. -/
  f' : X' ⟶ S'
  /-- The upper horizontal arrow is a thickening. -/
  i_isThickening : IsThickening i
  /-- The lower horizontal arrow is a thickening. -/
  t_isThickening : IsThickening t
  /-- The displayed square commutes. -/
  comm : i ≫ f' = f ≫ t

namespace MorphismOfThickenings

/-- The ideal `I = ker(i^♯)` on `X'`. -/
noncomputable abbrev idealI (D : MorphismOfThickenings.{u}) :
    SheafOfModules.{u} (structureSheafRing D.X') :=
  AlgebraicGeometry.SheafOfModules.idealSheaf D.i

/-- The ideal `J = ker(t^♯)` on `S'`. -/
noncomputable abbrev idealJ (D : MorphismOfThickenings.{u}) :
    SheafOfModules.{u} (structureSheafRing D.S') :=
  AlgebraicGeometry.SheafOfModules.idealSheaf D.t

/-- The map from `(f')^* J` to the structure sheaf of `X'` obtained by pulling back the
inclusion `J ⟶ 𝒪_{S'}` and then applying `(f')^♯`. -/
noncomputable def ambientIdealMap (D : MorphismOfThickenings.{u}) :
    (modulePullback D.f').obj D.idealJ ⟶ SheafOfModules.unit (structureSheafRing D.X') :=
  let _hadj : (SheafOfModules.pushforward (structureSheafHom D.f')).IsRightAdjoint :=
    modulePushforward_isRightAdjoint D.f'
  (modulePullback D.f').map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t))) ≫
      SheafOfModules.pullbackObjUnitToUnit (structureSheafHom D.f')

/-- The canonical map `(f')^* J ⟶ I`: after inclusion into `𝒪_{X'}`, it is the restriction of
`(f')^♯` to the pullback of `J`. -/
@[stacks 08KZ "the canonical ideal map"]
noncomputable def idealMap (D : MorphismOfThickenings.{u}) :
    { g : (modulePullback D.f').obj D.idealJ ⟶ D.idealI //
      g ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i)) =
        D.ambientIdealMap } := by
  refine ⟨kernel.lift (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom D.i)) D.ambientIdealMap ?_, ?_⟩
  · let hJ := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t))
    have hzero_t := map_comp_pullbackUnitToUnit_eq_zero D.t D.idealJ hJ (kernel.condition _)
    have hzero_ft :
        (modulePullback (D.f ≫ D.t)).map hJ ≫ pullbackUnitToUnit (D.f ≫ D.t) = 0 := by
      have hcomp := modulePullbackCompUniq_map_comp_pullbackUnitToUnit D.f D.t D.idealJ hJ
      have hleft :
          (modulePullbackCompUniq D.f D.t).hom.app D.idealJ ≫
            (modulePullback D.f).map ((modulePullback D.t).map hJ) ≫
            (modulePullback D.f).map (pullbackUnitToUnit D.t) ≫
            pullbackUnitToUnit D.f = 0 := by
        let _hf : (SheafOfModules.pushforward (structureSheafHom D.f)).IsRightAdjoint :=
          modulePushforward_isRightAdjoint D.f
        let _hl : (modulePullback D.f).IsLeftAdjoint :=
          (modulePullbackPushforwardAdjunction D.f).isLeftAdjoint
        let _hz : Functor.PreservesZeroMorphisms (modulePullback D.f) :=
          Functor.preservesZeroMorphisms_of_isLeftAdjoint (modulePullback D.f)
        have hmapzero : (modulePullback D.f).map
            (0 : (modulePullback D.t).obj D.idealJ ⟶
              SheafOfModules.unit (structureSheafRing D.S)) = 0 := Functor.map_zero _ _ _
        calc
          _ = (modulePullbackCompUniq D.f D.t).hom.app D.idealJ ≫
              (modulePullback D.f).map
                ((modulePullback D.t).map hJ ≫ pullbackUnitToUnit D.t) ≫
              pullbackUnitToUnit D.f := by
                simp only [Functor.map_comp, Category.assoc]
          _ = 0 := by rw [hzero_t, hmapzero]; simp
      exact hcomp.symm.trans hleft
    have hcomp := modulePullbackCompUniq_map_comp_pullbackUnitToUnit D.i D.f' D.idealJ hJ
    have hpullzero :
        (modulePullback D.i).map D.ambientIdealMap ≫ pullbackUnitToUnit D.i = 0 := by
      rw [← D.comm] at hzero_ft
      have h' : (modulePullbackCompUniq D.i D.f').hom.app D.idealJ ≫
          (modulePullback D.i).map ((modulePullback D.f').map hJ) ≫
          (modulePullback D.i).map (pullbackUnitToUnit D.f') ≫
          pullbackUnitToUnit D.i =
          (modulePullbackCompUniq D.i D.f').hom.app D.idealJ ≫ 0 := by
        rw [hcomp, hzero_ft]
        simp
      have h : (modulePullbackCompUniq D.i D.f').hom.app D.idealJ ≫
          (modulePullback D.i).map D.ambientIdealMap ≫ pullbackUnitToUnit D.i =
          (modulePullbackCompUniq D.i D.f').hom.app D.idealJ ≫ 0 := by
        have hd : (modulePullback D.i).map D.ambientIdealMap =
            (modulePullback D.i).map ((modulePullback D.f').map hJ) ≫
              (modulePullback D.i).map (pullbackUnitToUnit D.f') :=
          (modulePullback D.i).map_comp _ _
        rw [hd, Category.assoc]
        exact h'
      exact (cancel_epi ((modulePullbackCompUniq D.i D.f').hom.app D.idealJ)).1 h
    let _hi : (SheafOfModules.pushforward (structureSheafHom D.i)).IsRightAdjoint :=
      modulePushforward_isRightAdjoint D.i
    rw [← homEquiv_map_comp_pullbackUnitToUnit D.i _ D.ambientIdealMap, hpullzero]
    rfl
  · simp

/-- The module `f^* J`, as an `𝒪_{X'}`-module: `i_* (f^* (t^* J))`. -/
noncomputable abbrev reducedPullbackIdeal (D : MorphismOfThickenings.{u}) :
    SheafOfModules.{u} (structureSheafRing D.X') :=
  (modulePushforward D.i).obj
    ((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ))

/-- The canonical comparison `i^* (f')^* J ≅ f^* t^* J` induced by the commutative square. The
outer isomorphisms are functoriality of pullback under composition, and the middle one
transports along `i ≫ f' = f ≫ t`. -/
noncomputable def reducedPullbackComparison (D : MorphismOfThickenings.{u}) :
    (modulePullback D.i).obj ((modulePullback D.f').obj D.idealJ) ≅
      (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) :=
  (modulePullbackCompUniq D.i D.f').symm.app D.idealJ ≪≫
    eqToIso (congrArg (fun h : D.X ⟶ D.S' => (modulePullback h).obj D.idealJ) D.comm) ≪≫
      (modulePullbackCompUniq D.f D.t).app D.idealJ

/-- The canonical reduction map `(f')^* J ⟶ i_* f^* t^* J`: the unit of `i^* ⊣ i_*`, followed by
the pushforward of `reducedPullbackComparison`. -/
@[stacks 08KZ "the first-order canonical map"]
noncomputable def firstOrderSurjection (D : MorphismOfThickenings.{u})
    (_hi : IsFirstOrderThickening D.i) (_ht : IsFirstOrderThickening D.t) :
    (modulePullback D.f').obj D.idealJ ⟶ D.reducedPullbackIdeal :=
  (modulePullbackPushforwardAdjunction D.i).unit.app _ ≫
    (modulePushforward D.i).map D.reducedPullbackComparison.hom

/-- When both thickenings are first order, the canonical reduction map
`(f')^* J ⟶ i_* f^* t^* J` is an epimorphism. -/
@[stacks 08KZ "surjectivity of the first-order canonical map"]
theorem firstOrderSurjection_epi (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) :
    Epi (D.firstOrderSurjection hi ht) := by
  have : Epi ((modulePullbackPushforwardAdjunction D.i).unit.app
      ((modulePullback D.f').obj D.idealJ)) :=
    epi_unit_app_of_isThickening D.i hi.1 _
  show Epi ((modulePullbackPushforwardAdjunction D.i).unit.app _ ≫
    (modulePushforward D.i).map D.reducedPullbackComparison.hom)
  infer_instance

/-- If both thickenings are first order, the canonical ideal map `(f')^* J ⟶ I` factors uniquely
through the reduction `(f')^* J ⟶ i_* f^* J`, giving a map `f^* J ⟶ I`. -/
@[stacks 08KZ "the first-order factorization"]
noncomputable def firstOrderIdealMap (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) :
    { g : D.reducedPullbackIdeal ⟶ D.idealI //
      D.firstOrderSurjection hi ht ≫ g = D.idealMap.1 ∧
        ∀ g' : D.reducedPullbackIdeal ⟶ D.idealI,
          D.firstOrderSurjection hi ht ≫ g' = D.idealMap.1 → g' = g } := by
  let η := (modulePullbackPushforwardAdjunction D.i).unit
  let a := D.idealMap.1
  let c := D.reducedPullbackComparison
  have : IsIso (η.app D.idealI) := isIso_unit_app_idealSheaf D.i hi
  let g : D.reducedPullbackIdeal ⟶ D.idealI :=
    (modulePushforward D.i).map c.inv ≫
      (modulePullback D.i ⋙ modulePushforward D.i).map a ≫ inv (η.app D.idealI)
  have hfac : D.firstOrderSurjection hi ht ≫ g = a := by
    have hleft : η.app ((modulePullback D.f').obj D.idealJ) ≫
        (modulePushforward D.i).map c.hom ≫ (modulePushforward D.i).map c.inv =
        η.app ((modulePullback D.f').obj D.idealJ) := by
      rw [← CategoryTheory.Functor.map_comp, c.hom_inv_id, CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    change η.app _ ≫ (modulePushforward D.i).map c.hom ≫
      ((modulePushforward D.i).map c.inv ≫
        (modulePullback D.i ⋙ modulePushforward D.i).map a ≫ inv (η.app D.idealI)) = a
    simp only [← Category.assoc, hleft]
    rw [← η.naturality a]
    simp
  refine ⟨g, hfac, ?_⟩
  intro g' hg'
  have : Epi (D.firstOrderSurjection hi ht) := D.firstOrderSurjection_epi hi ht
  exact (cancel_epi (D.firstOrderSurjection hi ht)).1 (hg'.trans hfac.symm)

/-- A morphism of thickenings is *strict* when the canonical map `(f')^* J ⟶ I` of ideal sheaves
is surjective, i.e. an epimorphism of sheaves of `𝒪_{X'}`-modules. -/
@[stacks 08L1 "strict morphism of thickenings"]
noncomputable abbrev IsStrict (D : MorphismOfThickenings.{u}) : Prop := Epi D.idealMap.1

end MorphismOfThickenings

end AlgebraicGeometry.RingedSpaceThickening

end
