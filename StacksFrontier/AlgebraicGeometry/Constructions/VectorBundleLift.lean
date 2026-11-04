module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleClassifyingMap

/-!
# Morphisms into a vector bundle, and the zero section as the lift of `0`

Let `X` be a scheme and `ℱ` a quasi-coherent `𝒪_X`-module, with vector bundle
`p : 𝐕(ℱ) = Spec_X(Sym(ℱ)) ⟶ X`. For a scheme `Y` over `X`, morphisms `Y ⟶ 𝐕(ℱ)` over `X` are
the same as morphisms of `𝒪_X`-modules `ℱ ⟶ (Y ⟶ X)_* 𝒪_Y`: the classifying map
`AlgebraicGeometry.Scheme.Modules.vectorBundleClassifyingMap` is injective by
`AlgebraicGeometry.Scheme.Modules.vectorBundle_hom_ext`, and here it is shown to be surjective, by
the universal property of the relative spectrum together with the universal property of `Sym(ℱ)`.

The **zero section** `0 : X ⟶ 𝐕(ℱ)` is here the section of `p` whose classifying map is `0`, the
lift of the zero module map (`vectorBundleLiftZero`). It is
compatible with the morphisms `𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)` induced by `f : ℱ ⟶ 𝒢`, and with base change:
for `g : T ⟶ S` the square

  `T ⟶ 𝐕(g^* M)`
  `↓        ↓`
  `S ⟶ 𝐕(M)`

of zero sections is cartesian. Finally, if `ℰ ⟶ ℱ ⟶ ℱ' ⟶ 0` is exact (that is, `ℱ ⟶ ℱ'` is a
cokernel of `ℰ ⟶ ℱ`), then `𝐕(ℱ') ⟶ 𝐕(ℱ)` identifies `𝐕(ℱ')` with the fibre of
`𝐕(ℱ) ⟶ 𝐕(ℰ)` over the zero section:

  `𝐕(ℱ') = 𝐕(ℱ) ×_{𝐕(ℰ)} X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.vectorBundleLift`: the morphism `Y ⟶ 𝐕(ℱ)` over `X` with a
  given classifying map, and `vectorBundleHomEquivOfClassifyingMap` the resulting bijection.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleLiftZeroOver`: the zero section as a morphism
  of schemes over `X`, and `vectorBundleLiftZero` its underlying morphism of schemes.

## Main results

* `AlgebraicGeometry.Scheme.Modules.vectorBundleClassifyingMap_vectorBundleLift`: surjectivity of
  the classifying map.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleLiftZero_toBase`: the zero section is a section
  of the projection; `vectorBundleLiftZero_comp_vectorBundleMap`: it is compatible with `𝐕(f)`.
* `isPullback_vectorBundleLiftZero_vectorBundlePullbackProjection` (in the same namespace):
  zero sections are stable under base change.
* `AlgebraicGeometry.Scheme.Modules.isPullback_vectorBundleMap_of_isColimit` and
  `isPullback_vectorBundleMap_of_shortExact`: the vector bundle of a cokernel is the fibre over
  the zero section.

## Implementation notes

The classifying map of a morphism `Y ⟶ 𝐕(ℱ)` has target the module
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` of the pushed-forward structure sheaf, an
object of `X.Modules`, while `ℱ` is an object of `SheafOfModules X.ringCatSheaf`. Instance search
does not identify the two categories, which are the same by a semireducible definition, so the
zero morphisms between such objects are supplied by a local instance.

**Relation to `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection`.** The module
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSection` builds the zero section by
another route, as the section of the relative spectrum cut out by the augmentation
`Sym(ℱ) ⟶ 𝒪_X` (`Stacks.RelativeSpec.retractionSection`). This file characterizes morphisms into
`𝐕(ℱ)` by their classifying maps, and that characterization is what the base change and cokernel
statements below use, so the zero section here is defined as the lift of `0` and named for it:
`vectorBundleLiftZero`. The two constructions are not identified in this file.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec.AlgebraSheaf

/-- The zero morphism from a sheaf of modules to an object of `X.Modules`. Instance search does
not see through `AlgebraicGeometry.Scheme.Modules`, a semireducible definition, to find the zero
morphisms of `SheafOfModules X.ringCatSheaf` for a target presented in `X.Modules`. -/
local instance zeroHomOfSheafOfModules {X : Scheme.{u}} (A : SheafOfModules.{u} X.ringCatSheaf)
    (B : X.Modules) : Zero (A ⟶ B) :=
  HasZeroMorphisms.zero (C := SheafOfModules.{u} X.ringCatSheaf) A B

section Lift

variable {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]

/-- **The morphism into a vector bundle with a given classifying map.** A morphism of modules
`c : ℱ ⟶ (Y ⟶ X)_* 𝒪_Y` extends to a morphism of `𝒪_X`-algebras `Sym(ℱ) ⟶ (Y ⟶ X)_* 𝒪_Y`, which
by the universal property of the relative spectrum is a morphism `Y ⟶ 𝐕(ℱ)` over `X`. -/
def vectorBundleLift {Y : Over X} (c : F ⟶ underlyingModule (pushforwardAlgebra Y.hom)) :
    Y ⟶ vectorBundleOver X (F := F) :=
  haveI := isAffineHom_vectorBundleOver X (F := F)
  (overHomEquivAlgebraHom Y (vectorBundleOver X (F := F))).symm
    ((vectorBundlePushforwardIso X (F := F)).hom ≫ algebraLift (pushforwardAlgebra Y.hom) F c)

/-- The canonical map on pushed-forward structure sheaves of `vectorBundleLift F c` is the
algebra map `Sym(ℱ) ⟶ (Y ⟶ X)_* 𝒪_Y` extending `c`. -/
theorem pushforwardAlgebraMap_vectorBundleLift {Y : Over X}
    (c : F ⟶ underlyingModule (pushforwardAlgebra Y.hom)) :
    pushforwardAlgebraMap (vectorBundleLift F c) =
      (vectorBundlePushforwardIso X (F := F)).hom ≫ algebraLift (pushforwardAlgebra Y.hom) F c :=
  have := isAffineHom_vectorBundleOver X (F := F)
  (overHomEquivAlgebraHom_apply (vectorBundleLift F c)).symm.trans (Equiv.apply_symm_apply _ _)

/-- **Surjectivity of the classifying map**: the classifying map of `vectorBundleLift F c` is
`c`. -/
@[simp]
theorem vectorBundleClassifyingMap_vectorBundleLift {Y : Over X}
    (c : F ⟶ underlyingModule (pushforwardAlgebra Y.hom)) :
    vectorBundleClassifyingMap F (vectorBundleLift F c) = c := by
  rw [vectorBundleClassifyingMap, pushforwardAlgebraMap_vectorBundleLift, Iso.inv_hom_id_assoc]
  exact symmetricAlgebraSheafι_comp_algebraLift _ F c

/-- A morphism into a vector bundle is the lift of its classifying map. -/
@[simp]
theorem vectorBundleLift_vectorBundleClassifyingMap {Y : Over X}
    (m : Y ⟶ vectorBundleOver X (F := F)) :
    vectorBundleLift F (vectorBundleClassifyingMap F m) = m :=
  vectorBundle_hom_ext F (vectorBundleClassifyingMap_vectorBundleLift F _)

/-- **Morphisms into a vector bundle are classified by module maps**: for `Y` over `X`, morphisms
`Y ⟶ 𝐕(ℱ)` over `X` are in bijection with morphisms of modules `ℱ ⟶ (Y ⟶ X)_* 𝒪_Y`. -/
@[simps]
def vectorBundleHomEquivOfClassifyingMap (Y : Over X) :
    (Y ⟶ vectorBundleOver X (F := F)) ≃ (F ⟶ underlyingModule (pushforwardAlgebra Y.hom)) where
  toFun m := vectorBundleClassifyingMap F m
  invFun c := vectorBundleLift F c
  left_inv m := vectorBundleLift_vectorBundleClassifyingMap F m
  right_inv c := vectorBundleClassifyingMap_vectorBundleLift F c

/-- A morphism into a vector bundle whose classifying map is `c` is the lift of `c`. -/
private theorem eq_vectorBundleLift_of_vectorBundleClassifyingMap_eq {Y : Over X}
    (m : Y ⟶ vectorBundleOver X (F := F)) (c : F ⟶ underlyingModule (pushforwardAlgebra Y.hom))
    (h : vectorBundleClassifyingMap F m = c) : m = vectorBundleLift F c :=
  vectorBundle_hom_ext F (h.trans (vectorBundleClassifyingMap_vectorBundleLift F c).symm)

/-- The lift is natural in the scheme over `X`. -/
theorem comp_vectorBundleLift {Y Y' : Over X} (k : Y' ⟶ Y)
    (c : F ⟶ underlyingModule (pushforwardAlgebra Y.hom)) :
    k ≫ vectorBundleLift F c =
      vectorBundleLift F (c ≫ underlyingModuleMap (pushforwardAlgebraMap k)) :=
  eq_vectorBundleLift_of_vectorBundleClassifyingMap_eq F _ _ (by
    rw [vectorBundleClassifyingMap_comp, vectorBundleClassifyingMap_vectorBundleLift])

/-- The lift is natural in the module: following it by `𝐕(f)` precomposes the classifying map
with `f`. -/
theorem vectorBundleLift_comp_vectorBundleMap {G : SheafOfModules.{u} X.ringCatSheaf}
    [G.IsQuasicoherent] (f : F ⟶ G) {Y : Over X}
    (c : G ⟶ underlyingModule (pushforwardAlgebra Y.hom)) :
    vectorBundleLift G c ≫ vectorBundleMap X f = vectorBundleLift F (f ≫ c) :=
  eq_vectorBundleLift_of_vectorBundleClassifyingMap_eq F _ _ (by
    rw [vectorBundleClassifyingMap_comp_vectorBundleMap,
      vectorBundleClassifyingMap_vectorBundleLift])

end Lift

section ZeroSection

variable {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]

/-- **The zero section of `𝐕(ℱ)`, as a morphism of schemes over `X`**: the morphism
`X ⟶ 𝐕(ℱ)` over `X` whose classifying map is `0`, i.e. the one given by the augmentation
`Sym(ℱ) ⟶ 𝒪_X` killing `ℱ`. -/
def vectorBundleLiftZeroOver : Over.mk (𝟙 X) ⟶ vectorBundleOver X (F := F) :=
  vectorBundleLift F 0

/-- The classifying map of the zero section is `0`. -/
@[simp]
theorem vectorBundleClassifyingMap_vectorBundleLiftZeroOver :
    vectorBundleClassifyingMap F (vectorBundleLiftZeroOver F) = 0 :=
  vectorBundleClassifyingMap_vectorBundleLift F 0

/-- The classifying map of a morphism factoring through the zero section is `0`. -/
theorem vectorBundleClassifyingMap_comp_vectorBundleLiftZeroOver {Y : Over X}
    (k : Y ⟶ Over.mk (𝟙 X)) :
    vectorBundleClassifyingMap F (k ≫ vectorBundleLiftZeroOver F) = 0 :=
  (vectorBundleClassifyingMap_comp F k _).trans ((congrArg (· ≫ _)
    (vectorBundleClassifyingMap_vectorBundleLiftZeroOver F)).trans zero_comp)

/-- **A morphism into `𝐕(ℱ)` with classifying map `0` factors through the zero section**, through
the structure morphism of its source. -/
theorem eq_comp_vectorBundleLiftZeroOver {Y : Over X} (k : Y ⟶ Over.mk (𝟙 X))
    (m : Y ⟶ vectorBundleOver X (F := F)) (h : vectorBundleClassifyingMap F m = 0) :
    m = k ≫ vectorBundleLiftZeroOver F :=
  vectorBundle_hom_ext F
    (h.trans (vectorBundleClassifyingMap_comp_vectorBundleLiftZeroOver F k).symm)

/-- **The zero section `0 : X ⟶ 𝐕(ℱ)` of the vector bundle of a quasi-coherent module.** -/
def vectorBundleLiftZero : X ⟶ vectorBundle X F :=
  (vectorBundleLiftZeroOver F).left

/-- The zero section is a section of the projection `𝐕(ℱ) ⟶ X`. -/
@[reassoc (attr := simp)]
theorem vectorBundleLiftZero_toBase :
    vectorBundleLiftZero F ≫ vectorBundleToBase X F = 𝟙 X :=
  Over.w (vectorBundleLiftZeroOver F)

/-- The zero section is compatible with `𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)`, as morphisms over `X`. -/
theorem vectorBundleLiftZeroOver_comp_vectorBundleMap {G : SheafOfModules.{u} X.ringCatSheaf}
    [G.IsQuasicoherent] (f : F ⟶ G) :
    vectorBundleLiftZeroOver G ≫ vectorBundleMap X f = vectorBundleLiftZeroOver F :=
  (vectorBundleLift_comp_vectorBundleMap F f 0).trans (congrArg (vectorBundleLift F) comp_zero)

/-- **The zero section is compatible with `𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)`.** -/
@[reassoc (attr := simp)]
theorem vectorBundleLiftZero_comp_vectorBundleMap {G : SheafOfModules.{u} X.ringCatSheaf}
    [G.IsQuasicoherent] (f : F ⟶ G) :
    vectorBundleLiftZero G ≫ (vectorBundleMap X f).left = vectorBundleLiftZero F :=
  congrArg CommaMorphism.left (vectorBundleLiftZeroOver_comp_vectorBundleMap F f)

/-- The morphism `𝐕(0) : 𝐕(𝒢) ⟶ 𝐕(ℱ)` induced by the zero map is the projection to `X` followed
by the zero section. -/
theorem vectorBundleMap_zero_left {G : SheafOfModules.{u} X.ringCatSheaf} [G.IsQuasicoherent] :
    (vectorBundleMap X (0 : F ⟶ G)).left =
      vectorBundleToBase X G ≫ vectorBundleLiftZero F := by
  refine congrArg CommaMorphism.left (eq_comp_vectorBundleLiftZeroOver F
    (Over.homMk (vectorBundleToBase X G) :
      vectorBundleOver X (F := G) ⟶ Over.mk (𝟙 X)) _ ?_)
  rw [vectorBundleClassifyingMap_vectorBundleMap]
  exact zero_comp

end ZeroSection

section BaseChange

variable {T S : Scheme.{u}} (g : T ⟶ S) (M : S.Modules) [_root_.SheafOfModules.IsQuasicoherent M]

/-- The zero section of `𝐕(g^* M)` followed by `𝐕(g^* M) ⟶ 𝐕(M)` is `g` followed by the zero
section of `𝐕(M)`. -/
@[reassoc]
theorem vectorBundleLiftZero_comp_vectorBundlePullbackProjection :
    vectorBundleLiftZero ((pullback g).obj M) ≫ (vectorBundlePullbackProjection g M).left =
      g ≫ vectorBundleLiftZero M := by
  refine congrArg CommaMorphism.left (eq_comp_vectorBundleLiftZeroOver M
    (Over.homMk g : (Over.map g).obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 S))
    ((Over.map g).map (vectorBundleLiftZeroOver ((pullback g).obj M)) ≫
      vectorBundlePullbackProjection g M) ?_)
  rw [vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection]
  erw [vectorBundleClassifyingMap_vectorBundleLiftZeroOver]
  exact (congrArg ((pullbackPushforwardAdjunction g).unit.app M ≫ ·)
    (Functor.map_zero (pushforward g) _ _)).trans comp_zero

/-- **The base change square of a vector bundle is cartesian**: `𝐕(g^* M) ⟶ 𝐕(M)` exhibits
`𝐕(g^* M)` as the fibre product `𝐕(M) ×_S T`. -/
theorem isPullback_vectorBundlePullbackProjection :
    IsPullback (vectorBundlePullbackProjection g M).left
      (vectorBundleToBase T ((pullback g).obj M)) (vectorBundleToBase S M) g :=
  IsPullback.of_iso_pullback ⟨Over.w (vectorBundlePullbackProjection g M)⟩
    (vectorBundlePullbackIso g M).symm
    (by rw [Iso.symm_hom, vectorBundlePullbackProjection_left])
    (by rw [Iso.symm_hom, Iso.inv_comp_eq, vectorBundlePullbackIso_hom_vectorBundleToBase])

/-- **Zero sections are stable under base change**: for `g : T ⟶ S` the square
```
T ----0----> 𝐕(g^* M)
|               |
g               |
v               v
S ----0----> 𝐕(M)
```
is cartesian. It is the left half of a pasting whose right half is the cartesian base change
square `isPullback_vectorBundlePullbackProjection`, and whose outer square has identities as its
horizontal sides. -/
theorem isPullback_vectorBundleLiftZero_vectorBundlePullbackProjection :
    IsPullback (vectorBundleLiftZero ((pullback g).obj M)) g
      (vectorBundlePullbackProjection g M).left (vectorBundleLiftZero M) := by
  refine IsPullback.of_right ?_ (vectorBundleLiftZero_comp_vectorBundlePullbackProjection g M)
    (isPullback_vectorBundlePullbackProjection g M).flip
  exact (congrArg₂ (fun x y => IsPullback x g g y)
    (vectorBundleLiftZero_toBase ((pullback g).obj M))
    (vectorBundleLiftZero_toBase M)).mpr (IsPullback.id_horiz g)

end BaseChange

section Cokernel

variable {X : Scheme.{u}} {E F F' : SheafOfModules.{u} X.ringCatSheaf} [E.IsQuasicoherent]
  [F.IsQuasicoherent] [F'.IsQuasicoherent]

/-- **The vector bundle of a cokernel is the fibre over the zero section.** Let `a : ℰ ⟶ ℱ` and
`b : ℱ ⟶ ℱ'` be morphisms of quasi-coherent modules such that `b` is a cokernel of `a`. Then
```
𝐕(ℱ') --𝐕(b)--> 𝐕(ℱ)
  |               |
  p              𝐕(a)
  v               v
  X  -----0----> 𝐕(ℰ)
```
is cartesian: `𝐕(ℱ') = 𝐕(ℱ) ×_{𝐕(ℰ)} X`. A point `u : T ⟶ 𝐕(ℱ)` lying over the zero section of
`𝐕(ℰ)` has classifying map `κ` with `a ≫ κ = 0`, so `κ` factors uniquely through `b`. -/
theorem isPullback_vectorBundleMap_of_isColimit (a : E ⟶ F) (b : F ⟶ F') (w : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b w)) :
    IsPullback (vectorBundleMap X b).left (vectorBundleToBase X F') (vectorBundleMap X a).left
      (vectorBundleLiftZero E) := by
  have comm : (vectorBundleMap X b).left ≫ (vectorBundleMap X a).left =
      vectorBundleToBase X F' ≫ vectorBundleLiftZero E := by
    rw [← vectorBundleMap_zero_left E, ← w, vectorBundleMap_comp]
    rfl
  have hfst : ∀ s : PullbackCone (vectorBundleMap X a).left (vectorBundleLiftZero E),
      s.fst ≫ vectorBundleToBase X F = s.snd := fun s => by
    rw [← vectorBundleMap_left_comp X a, ← Category.assoc, s.condition, Category.assoc,
      vectorBundleLiftZero_toBase, Category.comp_id]
  let u : ∀ s : PullbackCone (vectorBundleMap X a).left (vectorBundleLiftZero E),
      Over.mk s.snd ⟶ vectorBundleOver X (F := F) := fun s => Over.homMk s.fst (hfst s)
  have hκ : ∀ s : PullbackCone (vectorBundleMap X a).left (vectorBundleLiftZero E),
      a ≫ vectorBundleClassifyingMap F (u s) = 0 := fun s => by
    rw [← vectorBundleClassifyingMap_comp_vectorBundleMap, show u s ≫ vectorBundleMap X a =
      (Over.homMk s.snd : Over.mk s.snd ⟶ Over.mk (𝟙 X)) ≫ vectorBundleLiftZeroOver E from
        Over.OverMorphism.ext s.condition]
    exact vectorBundleClassifyingMap_comp_vectorBundleLiftZeroOver E _
  let κ := fun s => CokernelCofork.IsColimit.desc' hb (vectorBundleClassifyingMap F (u s)) (hκ s)
  have hlift : ∀ s : PullbackCone (vectorBundleMap X a).left (vectorBundleLiftZero E),
      vectorBundleLift F' (κ s).1 ≫ vectorBundleMap X b = u s := fun s =>
    (vectorBundleLift_comp_vectorBundleMap F b _).trans ((congrArg (vectorBundleLift F)
      (κ s).2).trans (vectorBundleLift_vectorBundleClassifyingMap F (u s)))
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm (fun s => (vectorBundleLift F' (κ s).1).left)
    (fun s => congrArg CommaMorphism.left (hlift s))
    (fun s => Over.w (vectorBundleLift F' (κ s).1)) (fun s m h₁ h₂ => ?_)⟩⟩
  let m' : Over.mk s.snd ⟶ vectorBundleOver X (F := F') := Over.homMk m h₂
  refine congrArg CommaMorphism.left
    (eq_vectorBundleLift_of_vectorBundleClassifyingMap_eq F' m' _ ?_)
  refine Cofork.IsColimit.hom_ext hb ?_
  refine Eq.trans ?_ (κ s).2.symm
  refine (vectorBundleClassifyingMap_comp_vectorBundleMap F b m').symm.trans ?_
  exact congrArg (vectorBundleClassifyingMap F) (Over.OverMorphism.ext h₁)

/-- **The vector bundle of the cokernel in a short exact sequence is the fibre over the zero
section**: for a short exact sequence `0 ⟶ ℰ ⟶ ℱ ⟶ ℱ' ⟶ 0` of quasi-coherent modules,
`𝐕(ℱ') = 𝐕(ℱ) ×_{𝐕(ℰ)} X`. Only right exactness is used; see
`isPullback_vectorBundleMap_of_isColimit`. -/
theorem isPullback_vectorBundleMap_of_shortExact (a : E ⟶ F) (b : F ⟶ F') (w : a ≫ b = 0)
    (hS : (ShortComplex.mk a b w).ShortExact) :
    IsPullback (vectorBundleMap X b).left (vectorBundleToBase X F') (vectorBundleMap X a).left
      (vectorBundleLiftZero E) :=
  isPullback_vectorBundleMap_of_isColimit a b w hS.gIsCokernel

end Cokernel

end AlgebraicGeometry.Scheme.Modules

end
