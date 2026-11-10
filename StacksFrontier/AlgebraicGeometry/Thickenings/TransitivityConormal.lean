module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Thickenings.Transitivity
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence of a composition of universal first-order thickenings

Let `Z --i--→ Y --p--→ X` be morphisms of schemes, let `Z ⊂ Z'` be a universal first-order
thickening of `Z` over `X` and `Y ⊂ Y'` one of `Y` over `X`. By part (1) of
[Stacks Project, Tag 06AE], proved in
`StacksFrontier.AlgebraicGeometry.Thickenings.Transitivity`, the fibre product `Y ×_{Y'} Z'` is a
universal first-order thickening of `Z` over `Y`. Part (2) of that tag asserts that the two
canonical maps of [Stacks Project, Tag 01R4] between the resulting conormal sheaves form an
exact sequence
```
i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0 .
```
This file constructs the two maps and proves that the sequence is exact.

## Main definitions

* `Stacks.Thickenings.transitivityConormalLeftMap` is the first arrow `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}`,
  the map of [Stacks Project, Tag 01R4] for the square of inclusions over the morphism
  `Z' ⟶ Y'` of `Stacks.Thickenings.transitivityMap`.
* `Stacks.Thickenings.transitivityConormalRightMap` is the second arrow `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}`,
  the map of [Stacks Project, Tag 01R4] for the square of inclusions over the projection
  `Y ×_{Y'} Z' ⟶ Z'`, read through the identification of pullback along the identity with the
  identity functor.
* `Stacks.Thickenings.transitivityConormalShortComplex` is the sequence as a two-term complex,
  the two arrows composing to zero.

## Main results

* `Stacks.Thickenings.isPullback_relativeInclusion_inclusion`: the square defining the second
  arrow is cartesian, because the inclusion of `Z` into `Z'` is a monomorphism.
* `Stacks.Thickenings.epi_transitivityConormalRightMap` is exactness at `𝒞_{Z/Y}`: the second
  arrow is an epimorphism, which is the `⟶ 0` at the right-hand end of the sequence.
* `Stacks.Thickenings.transitivityConormalShortComplex_exact` is exactness at `𝒞_{Z/X}`.

## Implementation notes

The conormal sheaves are `Stacks.Thickenings.immersionConormalSheaf` of the three inclusions,
which is the sheaf `Stacks.Thickenings.universalConormalSheaf` of [Stacks Project, Tag 04F4] is
built from; `𝒞_{Z/Y}` is taken at the thickening `Y ×_{Y'} Z'` produced by part (1), which is a
universal first-order thickening of `i` and so computes that conormal sheaf.

Exactness at the middle term `𝒞_{Z/X}` is deduced from the corresponding statement for a pair of
immersions, [Stacks Project, Tag 062S], applied to the chain `Z ⟶ Y ×_{Y'} Z' ⟶ Z'`. That
sequence has the same middle and right-hand terms as this one and the same right-hand arrow, and
its left-hand term receives an epimorphism from `i^* 𝒞_{Y/X}`, namely the pullback along
`Z ⟶ Y ×_{Y'} Z'` of the map of [Stacks Project, Tag 01R4] for the square of projections of the
fibre product, which is surjective by the cartesian case of [Stacks Project, Tag 0473]. The two
left-hand arrows agree over that epimorphism because the map of [Stacks Project, Tag 01R4] is
compatible with vertical composition of squares; that compatibility is checked on affine charts
through `Stacks.Immersion.immersionConormalSheafMap_unique`, and since the upper square's
right-hand vertical is the identity of `Z'`, the intermediate chart can be taken to be the outer
one, so no covering argument is needed.

Surjectivity of the second arrow is the cartesian case of [Stacks Project, Tag 0473],
`Stacks.Immersion.epi_immersionConormalSheafMap`, for its defining square.

## References

* [Stacks Project, Tag 06AE](https://stacks.math.columbia.edu/tag/06AE)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.Immersion

universe u

namespace Stacks.Thickenings

variable {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ X)
  (tZ : UniversalFirstOrderThickening (i ≫ p)) (tY : UniversalFirstOrderThickening p)

/-- **The first arrow `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal sequence of part (2) of
[Stacks Project, Tag 06AE].** It is the canonical map of [Stacks Project, Tag 01R4] for the
square of inclusions with vertical maps `i` and the morphism `Z' ⟶ Y'` of
`Stacks.Thickenings.transitivityMap`. -/
@[stacks 06AE "part (2): the first arrow i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}"]
def transitivityConormalLeftMap :
    (modulePullback i.toLRSHom.toShHom).obj
        (conormalSheaf tY.inclusion.liftCoborder.toLRSHom.toShHom) ⟶
      conormalSheaf tZ.inclusion.liftCoborder.toLRSHom.toShHom :=
  immersionConormalSheafMap tZ.inclusion tY.inclusion i (transitivityMap i p tZ tY)
    (toShHom_square (inclusion_comp_transitivityMap i p tZ tY).symm)

/-- **The square defining the second arrow of the conormal sequence is cartesian**: the square
with edges `Z ⟶ Y ×_{Y'} Z'`, `𝟙 Z`, the projection `Y ×_{Y'} Z' ⟶ Z'` and the inclusion
`Z ⟶ Z'`. -/
theorem isPullback_relativeInclusion_inclusion :
    IsPullback (relativeInclusion i p tZ tY) (𝟙 Z)
      (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) tZ.inclusion := by
  have : Mono tZ.inclusion := inferInstance
  exact IsPullback.of_vert_isIso_mono
    (CommSq.mk (by rw [relativeInclusion_comp_snd, Category.id_comp]))

/-- **The second arrow `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the conormal sequence of part (2) of
[Stacks Project, Tag 06AE].** It is the canonical map of [Stacks Project, Tag 01R4] for the
square of inclusions with vertical maps `𝟙 Z` and the projection `Y ×_{Y'} Z' ⟶ Z'`, read
through the identification of pullback along the identity with the identity functor. -/
@[stacks 06AE "part (2): the second arrow 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}"]
def transitivityConormalRightMap :
    conormalSheaf tZ.inclusion.liftCoborder.toLRSHom.toShHom ⟶
      conormalSheaf (relativeInclusion i p tZ tY).liftCoborder.toLRSHom.toShHom :=
  ((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
      (conormalSheaf tZ.inclusion.liftCoborder.toLRSHom.toShHom)).inv ≫
    immersionConormalSheafMap (relativeInclusion i p tZ tY) tZ.inclusion (𝟙 Z)
      (pullback.snd tY.inclusion (transitivityMap i p tZ tY))
      (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w)

/-- **Part (2) of [Stacks Project, Tag 06AE], exactness at `𝒞_{Z/Y}`.** The second arrow
`𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the conormal sequence is an epimorphism, which is the `⟶ 0` at the
right-hand end of the canonical sequence `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`. -/
@[stacks 06AE "part (2): exactness at the right term", sga "6 VIII 2.6" "right exactness"]
theorem epi_transitivityConormalRightMap :
    Epi (transitivityConormalRightMap i p tZ tY) := by
  have h := epi_immersionConormalSheafMap (relativeInclusion i p tZ tY) tZ.inclusion (𝟙 Z)
    (pullback.snd tY.inclusion (transitivityMap i p tZ tY))
    (isPullback_relativeInclusion_inclusion i p tZ tY)
  change Epi (((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
      (conormalSheaf tZ.inclusion.liftCoborder.toLRSHom.toShHom)).inv ≫
    immersionConormalSheafMap (relativeInclusion i p tZ tY) tZ.inclusion (𝟙 Z)
      (pullback.snd tY.inclusion (transitivityMap i p tZ tY))
      (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w))
  exact @epi_comp _ _ _ _ _ _ inferInstance _ h

/-! ### Vanishing of a stacked pair of conormal maps -/

/-- Pullback of sheaves of modules along a morphism of ringed spaces preserves the zero
morphism. -/
private theorem modulePullback_map_zero {A B : RingedSpace.{u, u}} (k : A ⟶ B)
    (M N : SheafOfModules.{u} (structureSheafRing B)) :
    (modulePullback k).map (0 : M ⟶ N) = 0 := by
  have h := Adjunction.homEquiv_naturality_left (modulePullbackPushforwardAdjunction k)
    (0 : M ⟶ N) (𝟙 ((modulePullback k).obj N))
  rw [Category.comp_id] at h
  have hz : (modulePullbackPushforwardAdjunction k).homEquiv _ _
      (0 : (modulePullback k).obj M ⟶ (modulePullback k).obj N) = 0 := by
    simp only [Adjunction.homEquiv_unit, modulePushforward_map_zero, comp_zero]
  exact ((modulePullbackPushforwardAdjunction k).homEquiv _ _).injective
    (h.trans (zero_comp.trans hz.symm))

/-- **A two-step pullback of the structure-sheaf map kills the ideal sheaf when the composite
factors through the morphism defining it.** For `k₁ ≫ k₂ = v ≫ j` the composite
`k₁^* k₂^* ℐ_j ⟶ k₁^* 𝒪 ⟶ 𝒪` vanishes. -/
private theorem map_pullbackIdealSheafι_comp_unitToUnit_eq_zero
    {A₀ A₁ A₂ W : RingedSpace.{u, u}} (k₁ : A₀ ⟶ A₁) (k₂ : A₁ ⟶ A₂) {j : W ⟶ A₂} {v : A₀ ⟶ W}
    (hfac : k₁ ≫ k₂ = v ≫ j) :
    (modulePullback k₁).map ((modulePullback k₂).map (idealSheafι j) ≫
          modulePullbackUnitToUnit k₂) ≫
        modulePullbackUnitToUnit k₁ = 0 := by
  have hz : (modulePullbackPushforwardAdjunction k₁).homEquiv _ _
      (0 : (modulePullback k₁).obj ((modulePullback k₂).obj (idealSheaf j)) ⟶
        SheafOfModules.unit (structureSheafRing A₀)) = 0 := by
    simp only [Adjunction.homEquiv_unit, modulePushforward_map_zero, comp_zero]
  have h := Adjunction.homEquiv_naturality_left (modulePullbackPushforwardAdjunction k₁)
    ((modulePullback k₂).map (idealSheafι j) ≫ modulePullbackUnitToUnit k₂)
    (modulePullbackUnitToUnit k₁)
  rw [homEquiv_modulePullbackUnitToUnit] at h
  exact ((modulePullbackPushforwardAdjunction k₁).homEquiv _ _).injective
    (h.trans ((pullbackIdealSheaf_comp_eq_zero hfac).trans hz.symm))

/-- `Stacks.ClosedImmersion.conormalSheafMap` read through the pullback comparison of its square:
it is the pullback along the upper horizontal map of
`Stacks.ClosedImmersion.idealSheafMap`, preceded by the inverse of
`RingedSpaceModuleAdjunction.modulePullbackSquareIso`. -/
private theorem conormalSheafMap_eq {A₀ A₁ B₀ B₁ : RingedSpace.{u, u}} {i₀ : A₀ ⟶ B₀}
    {i₁ : A₁ ⟶ B₁} {f : A₀ ⟶ A₁} {k : B₀ ⟶ B₁} (comm : i₀ ≫ k = f ≫ i₁) :
    conormalSheafMap comm =
      (modulePullbackSquareIso f k i₀ i₁ comm).inv.app (idealSheaf i₁) ≫
        (modulePullback i₀).map (idealSheafMap comm) := by
  rw [← modulePullbackSquareIso_hom_app_comp_conormalSheafMap comm, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

/-- **The ideal-sheaf maps of a vertically stacked pair of squares compose to zero when the
composite of the two right-hand verticals factors through the bottom horizontal map.** -/
private theorem idealSheafMap_comp_eq_zero {A₀ A₁ A₂ B₀ B₁ B₂ : RingedSpace.{u, u}}
    {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {i₂ : A₂ ⟶ B₂} {f₁ : A₀ ⟶ A₁} {k₁ : B₀ ⟶ B₁}
    {f₂ : A₁ ⟶ A₂} {k₂ : B₁ ⟶ B₂} {v : B₀ ⟶ A₂}
    (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂) (hfac : k₁ ≫ k₂ = v ≫ i₂) :
    (modulePullback k₁).map (idealSheafMap commB) ≫ idealSheafMap commA = 0 := by
  have hmono : Mono (idealSheafι i₀) := mono_idealSheafι i₀
  refine (cancel_mono (idealSheafι i₀)).mp ?_
  rw [zero_comp, Category.assoc, idealSheafMap_comp_ι commA, ← Category.assoc,
    ← Functor.map_comp, idealSheafMap_comp_ι commB]
  exact map_pullbackIdealSheafι_comp_unitToUnit_eq_zero k₁ k₂ hfac

/-- **The conormal maps of a vertically stacked pair of squares of ringed spaces compose to zero
when the composite of the two right-hand verticals factors through the bottom horizontal map.** -/
private theorem conormalSheafMap_comp_eq_zero {A₀ A₁ A₂ B₀ B₁ B₂ : RingedSpace.{u, u}}
    {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {i₂ : A₂ ⟶ B₂} {f₁ : A₀ ⟶ A₁} {k₁ : B₀ ⟶ B₁}
    {f₂ : A₁ ⟶ A₂} {k₂ : B₁ ⟶ B₂} {v : B₀ ⟶ A₂}
    (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂) (hfac : k₁ ≫ k₂ = v ≫ i₂) :
    (modulePullback f₁).map (conormalSheafMap commB) ≫ conormalSheafMap commA = 0 := by
  have hnat := (modulePullbackSquareIso f₁ k₁ i₀ i₁ commA).inv.naturality (idealSheafMap commB)
  simp only [Functor.comp_map] at hnat
  have key : (modulePullback f₁).map ((modulePullback i₁).map (idealSheafMap commB)) ≫
      (modulePullbackSquareIso f₁ k₁ i₀ i₁ commA).inv.app (idealSheaf i₁) ≫
        (modulePullback i₀).map (idealSheafMap commA) = 0 := by
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp,
      idealSheafMap_comp_eq_zero commA commB hfac, modulePullback_map_zero, comp_zero]
  rw [conormalSheafMap_eq commB, conormalSheafMap_eq commA, Functor.map_comp]
  simp only [Category.assoc]
  rw [key, comp_zero]

/-- `Stacks.Immersion.immersionConormalSheafMap` written out: the ringed-space conormal map of
the square, conjugated by `Stacks.Immersion.conormalSheafSelfIso` on each side. -/
private theorem immersionConormalSheafMap_eq {Z₀ Z₁ X₀ X₁ : Scheme.{u}} (i₀ : Z₀ ⟶ X₀)
    (i₁ : Z₁ ⟶ X₁) [IsImmersion i₀] [IsImmersion i₁] (f : Z₀ ⟶ Z₁) (k : X₀ ⟶ X₁)
    (comm : i₀.toLRSHom.toShHom ≫ k.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ i₁.toLRSHom.toShHom) :
    immersionConormalSheafMap i₀ i₁ f k comm =
      (modulePullback f.toLRSHom.toShHom).map (conormalSheafSelfIso i₁).inv ≫
        conormalSheafMap comm ≫ (conormalSheafSelfIso i₀).hom :=
  rfl

/-- **The conormal maps of a vertically stacked pair of squares of immersions of schemes compose
to zero when the composite of the two right-hand verticals factors through the bottom horizontal
map.** -/
private theorem map_immersionConormalSheafMap_comp_eq_zero {Z₀ Z₁ Z₂ X₀ X₁ X₂ : Scheme.{u}}
    (i₀ : Z₀ ⟶ X₀) (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂)
    [IsImmersion i₀] [IsImmersion i₁] [IsImmersion i₂]
    (f₁ : Z₀ ⟶ Z₁) (k₁ : X₀ ⟶ X₁) (f₂ : Z₁ ⟶ Z₂) (k₂ : X₁ ⟶ X₂) (v : X₀ ⟶ Z₂)
    (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂) (hfac : k₁ ≫ k₂ = v ≫ i₂) :
    (modulePullback f₁.toLRSHom.toShHom).map
        (immersionConormalSheafMap i₁ i₂ f₂ k₂ (toShHom_square commB)) ≫
      immersionConormalSheafMap i₀ i₁ f₁ k₁ (toShHom_square commA) = 0 := by
  rw [immersionConormalSheafMap_eq i₁ i₂ f₂ k₂, immersionConormalSheafMap_eq i₀ i₁ f₁ k₁,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  slice_lhs 2 3 => rw [conormalSheafMap_comp_eq_zero (toShHom_square commA)
    (toShHom_square commB) (toShHom_square hfac)]
  simp

/-- **A stacked pair of conormal maps of immersions, read through a comparison with the identity
functor, composes to zero**: `Stacks.Thickenings.map_immersionConormalSheafMap_comp_eq_zero`
with the pullback along the upper left vertical map, an endomorphism of the source, replaced by a
natural transformation `α` out of the identity functor. -/
private theorem immersionConormalSheafMap_comp_eq_zero {Z₀ Z₂ X₀ X₁ X₂ : Scheme.{u}}
    (i₀ : Z₀ ⟶ X₀) (i₁ : Z₀ ⟶ X₁) (i₂ : Z₂ ⟶ X₂)
    [IsImmersion i₀] [IsImmersion i₁] [IsImmersion i₂]
    (f₁ : Z₀ ⟶ Z₀) (k₁ : X₀ ⟶ X₁) (f₂ : Z₀ ⟶ Z₂) (k₂ : X₁ ⟶ X₂) (v : X₀ ⟶ Z₂)
    (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂) (hfac : k₁ ≫ k₂ = v ≫ i₂)
    (α : 𝟭 (SheafOfModules.{u} (structureSheafRing Z₀.toLocallyRingedSpace.toRingedSpace)) ⟶
      modulePullback f₁.toLRSHom.toShHom) :
    immersionConormalSheafMap i₁ i₂ f₂ k₂ (toShHom_square commB) ≫
        α.app (immersionConormalSheaf i₁) ≫
          immersionConormalSheafMap i₀ i₁ f₁ k₁ (toShHom_square commA) = 0 := by
  have hnat := α.naturality (immersionConormalSheafMap i₁ i₂ f₂ k₂ (toShHom_square commB))
  simp only [Functor.id_map] at hnat
  rw [← Category.assoc, hnat, Category.assoc,
    map_immersionConormalSheafMap_comp_eq_zero i₀ i₁ i₂ f₁ k₁ f₂ k₂ v commA commB hfac,
    comp_zero]

/-! ### The sequence is a complex -/

/-- **The two arrows of the conormal sequence of part (2) of [Stacks Project, Tag 06AE] compose
to zero.** -/
@[stacks 06AE "part (2): the two arrows of the sequence compose to zero"]
theorem transitivityConormalLeftMap_comp_rightMap :
    transitivityConormalLeftMap i p tZ tY ≫ transitivityConormalRightMap i p tZ tY = 0 :=
  immersionConormalSheafMap_comp_eq_zero (relativeInclusion i p tZ tY) tZ.inclusion
    tY.inclusion (𝟙 Z) (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) i
    (transitivityMap i p tZ tY) (relativeToBase i p tZ tY)
    (isPullback_relativeInclusion_inclusion i p tZ tY).w
    (inclusion_comp_transitivityMap i p tZ tY).symm pullback.condition.symm
    ((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv)

/-- **The conormal sequence of part (2) of [Stacks Project, Tag 06AE]** as a two-term complex of
`𝒪_Z`-modules, `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}`. -/
@[stacks 06AE "part (2): the sequence as a short complex"]
def transitivityConormalShortComplex :
    ShortComplex (SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) :=
  ShortComplex.mk (transitivityConormalLeftMap i p tZ tY)
    (transitivityConormalRightMap i p tZ tY)
    (transitivityConormalLeftMap_comp_rightMap i p tZ tY)

/-! ### Vertical composition of the canonical map -/

/-- **The transpose of a composite read through the pullback composition isomorphism.** For
`ψ : f₂^* M ⟶ M'` and `χ : f₁^* M' ⟶ N` the transpose along `(f₁ ≫ f₂)^* ⊣ (f₁ ≫ f₂)_*` of
`(f₁ ≫ f₂)^* M ≅ f₁^* f₂^* M ⟶ f₁^* M' ⟶ N` is the transpose of `ψ`, followed by the pushforward
along `f₂` of the transpose of `χ`, followed by the pushforward comparison of the composite. -/
private theorem homEquiv_modulePullbackComp_comp {A₀ A₁ A₂ : RingedSpace.{u, u}}
    (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) {M : SheafOfModules.{u} (structureSheafRing A₂)}
    {M' : SheafOfModules.{u} (structureSheafRing A₁)}
    {N : SheafOfModules.{u} (structureSheafRing A₀)}
    (ψ : (modulePullback f₂).obj M ⟶ M') (χ : (modulePullback f₁).obj M' ⟶ N) :
    (modulePullbackPushforwardAdjunction (f₁ ≫ f₂)).homEquiv M N
        ((modulePullbackComp f₁ f₂).hom.app M ≫ (modulePullback f₁).map ψ ≫ χ) =
      ((modulePullbackPushforwardAdjunction f₂).homEquiv M M' ψ ≫
          (modulePushforward f₂).map
            ((modulePullbackPushforwardAdjunction f₁).homEquiv M' N χ)) ≫
        (modulePushforwardComp f₁ f₂).hom.app N := by
  rw [Stacks.CategoryTheory.homEquiv_conjugate'
      ((modulePullbackPushforwardAdjunction f₂).comp
      (modulePullbackPushforwardAdjunction f₁))
      (modulePullbackPushforwardAdjunction (f₁ ≫ f₂)) (modulePullbackComp f₁ f₂).hom,
    conjugateEquiv_modulePullbackComp_hom]
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

/-- `Stacks.Thickenings.homEquiv_modulePullbackComp_comp` for morphisms of schemes, with the
composite vertical map spelled `(f₁ ≫ f₂).toLRSHom.toShHom`, which is the spelling
`Stacks.Immersion.IsInducedConormalSheafMap` produces. -/
private theorem homEquiv_modulePullbackComp_comp_scheme {Z₀ Z₁ Z₂ : Scheme.{u}}
    (f₁ : Z₀ ⟶ Z₁) (f₂ : Z₁ ⟶ Z₂)
    {M : SheafOfModules.{u} (structureSheafRing Z₂.toLocallyRingedSpace.toRingedSpace)}
    {M' : SheafOfModules.{u} (structureSheafRing Z₁.toLocallyRingedSpace.toRingedSpace)}
    {N : SheafOfModules.{u} (structureSheafRing Z₀.toLocallyRingedSpace.toRingedSpace)}
    (ψ : (modulePullback f₂.toLRSHom.toShHom).obj M ⟶ M')
    (χ : (modulePullback f₁.toLRSHom.toShHom).obj M' ⟶ N) :
    (modulePullbackPushforwardAdjunction (f₁ ≫ f₂).toLRSHom.toShHom).homEquiv M N
        ((modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app M ≫
          (modulePullback f₁.toLRSHom.toShHom).map ψ ≫ χ) =
      ((modulePullbackPushforwardAdjunction f₂.toLRSHom.toShHom).homEquiv M M' ψ ≫
          (modulePushforward f₂.toLRSHom.toShHom).map
            ((modulePullbackPushforwardAdjunction f₁.toLRSHom.toShHom).homEquiv M' N χ)) ≫
        (modulePushforwardComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app N :=
  homEquiv_modulePullbackComp_comp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom ψ χ

/-- `Stacks.Thickenings.homEquiv_modulePullbackComp_comp_scheme` on a section over an open `W` of
the target: the two pushforward comparisons are identities on sections, so the right-hand side is
the transpose of `χ` over `f₂ ⁻¹ᵁ W` applied to the transpose of `ψ` over `W`. -/
private theorem homEquiv_modulePullbackComp_comp_val_app {Z₀ Z₁ Z₂ : Scheme.{u}}
    (f₁ : Z₀ ⟶ Z₁) (f₂ : Z₁ ⟶ Z₂)
    {M : SheafOfModules.{u} (structureSheafRing Z₂.toLocallyRingedSpace.toRingedSpace)}
    {M' : SheafOfModules.{u} (structureSheafRing Z₁.toLocallyRingedSpace.toRingedSpace)}
    {N : SheafOfModules.{u} (structureSheafRing Z₀.toLocallyRingedSpace.toRingedSpace)}
    (ψ : (modulePullback f₂.toLRSHom.toShHom).obj M ⟶ M')
    (χ : (modulePullback f₁.toLRSHom.toShHom).obj M' ⟶ N)
    (W : Z₂.Opens) (s : M.val.obj (op W)) :
    ((modulePullbackPushforwardAdjunction (f₁ ≫ f₂).toLRSHom.toShHom).homEquiv M N
        (((modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app M ≫
            (modulePullback f₁.toLRSHom.toShHom).map ψ) ≫ χ)).val.app (op W) s =
      ((modulePullbackPushforwardAdjunction f₁.toLRSHom.toShHom).homEquiv M' N χ).val.app
        (op (f₂ ⁻¹ᵁ W))
        (((modulePullbackPushforwardAdjunction f₂.toLRSHom.toShHom).homEquiv M M' ψ).val.app
          (op W) s) :=
  congrArg (fun t => t.val.app (op W) s)
    ((congrArg
          (fun t =>
            (modulePullbackPushforwardAdjunction (f₁ ≫ f₂).toLRSHom.toShHom).homEquiv M N t)
          (Category.assoc
            ((modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app M)
            ((modulePullback f₁.toLRSHom.toShHom).map ψ) χ)).trans
      (homEquiv_modulePullbackComp_comp_scheme f₁ f₂ ψ χ))

/-- **Pullback of sections along the identity morphism is the identity.** -/
private theorem appLE_id {X₀ : Scheme.{u}} (U : X₀.Opens) (h : U ≤ (𝟙 X₀) ⁻¹ᵁ U) :
    Scheme.Hom.appLE (𝟙 X₀) U U h = 𝟙 Γ(X₀, U) :=
  X₀.presheaf.map_id (op U)

/-- **The canonical map of [Stacks Project, Tag 01R4] is compatible with vertical composition of
squares whose upper right-hand vertical is an identity**, for `i₁` whose range has coborder
everything. -/
private theorem immersionConormalSheafMap_comp_id {Z₀ Z₁ Z₂ X₀ X₂ : Scheme.{u}}
    (i₀ : Z₀ ⟶ X₀) (i₁ : Z₁ ⟶ X₀) (i₂ : Z₂ ⟶ X₂)
    [IsImmersion i₀] [IsImmersion i₁] [IsImmersion i₂] (htop : i₁.coborderRange = ⊤)
    (f₁ : Z₀ ⟶ Z₁) (f₂ : Z₁ ⟶ Z₂) (k₂ : X₀ ⟶ X₂)
    (commA : i₀ ≫ 𝟙 X₀ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂)
    (commT : i₀ ≫ k₂ = (f₁ ≫ f₂) ≫ i₂) :
    immersionConormalSheafMap i₀ i₂ (f₁ ≫ f₂) k₂ (toShHom_square commT) =
      ((modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app
            (conormalSheaf i₂.liftCoborder.toLRSHom.toShHom) ≫
          (modulePullback f₁.toLRSHom.toShHom).map
            (immersionConormalSheafMap i₁ i₂ f₂ k₂ (toShHom_square commB))) ≫
        immersionConormalSheafMap i₀ i₁ f₁ (𝟙 X₀) (toShHom_square commA) := by
  refine (immersionConormalSheafMap_unique i₀ i₂ (f₁ ≫ f₂) k₂ commT _ ?_).symm
  intro U hU V hV hUV I J eZ heZ eW heW a b hab
  obtain ⟨I₁, e₁, he₁⟩ :=
    exists_affineModel_of_le_coborderRange i₁ U hU (by rw [htop]; exact le_top)
  have hUU : U ≤ (𝟙 X₀) ⁻¹ᵁ U := by simp
  have hmem : (k₂.appLE V U hUV).hom (a : Γ(X₂, V)) ∈ I₁ :=
    immersionConormalSheafMap_ideal_mem i₁ i₂ f₂ k₂ commB U hU V hV hUV I₁ J e₁ he₁ eW heW a
  have hid : ∀ x : Γ(X₀, U), (Scheme.Hom.appLE (𝟙 X₀) U U hUU).hom x = x := fun x => by
    rw [appLE_id]
    rfl
  have hB := isInducedConormalSheafMap_immersionConormalSheafMap i₁ i₂ f₂ k₂ commB
    U hU V hV hUV I₁ J e₁ he₁ eW heW a ⟨_, hmem⟩ rfl
  have hA := isInducedConormalSheafMap_immersionConormalSheafMap i₀ i₁ f₁ (𝟙 X₀) commA
    U hU U hU hUU I I₁ eZ heZ e₁ he₁ ⟨_, hmem⟩ b (hab.trans (hid _).symm)
  refine Eq.trans (val_map_congr
    (homOfLE (preimage_le_preimage_of_square commT U V hUV))
    (homEquiv_modulePullbackComp_comp_val_app f₁ f₂ _ _ _ _)) ?_
  have hB₂ : i₁ ⁻¹ᵁ U ≤ f₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ V) := preimage_le_preimage_of_square commB U V hUV
  have hA₂ : i₀ ⁻¹ᵁ U ≤ f₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U) := preimage_le_preimage_of_square commA U U hUU
  have hnat := val_app_naturality
    ((modulePullbackPushforwardAdjunction f₁.toLRSHom.toShHom).homEquiv _ _
      (immersionConormalSheafMap i₀ i₁ f₁ (𝟙 X₀) (toShHom_square commA)))
    (homOfLE hB₂)
    (((modulePullbackPushforwardAdjunction f₂.toLRSHom.toShHom).homEquiv _ _
      (immersionConormalSheafMap i₁ i₂ f₂ k₂ (toShHom_square commB))).val.app (op (i₂ ⁻¹ᵁ V))
        ((Stacks.Conormal.affineConormalIsoCotangent i₂ V hV J eW heW).inv.hom (J.toCotangent a)))
  rw [modulePushforward_obj_val_map, hB] at hnat
  refine Eq.trans (val_map_unique _
    ((TopologicalSpace.Opens.map f₁.toLRSHom.toShHom.hom.base).map (homOfLE hB₂))
    (homOfLE hA₂) _ _).symm ?_
  exact (val_map_congr (homOfLE hA₂) hnat.symm).trans hA

/-- **The canonical map of [Stacks Project, Tag 01R4] transported along an equality of the
vertical map of its square.** -/
private theorem immersionConormalSheafMap_congr_left {Z₀ Z₂ X₀ X₂ : Scheme.{u}}
    (i₀ : Z₀ ⟶ X₀) (i₂ : Z₂ ⟶ X₂) [IsImmersion i₀] [IsImmersion i₂]
    {f f' : Z₀ ⟶ Z₂} (hf : f = f') (k : X₀ ⟶ X₂)
    (comm : i₀ ≫ k = f ≫ i₂) (comm' : i₀ ≫ k = f' ≫ i₂) :
    immersionConormalSheafMap i₀ i₂ f k (toShHom_square comm) =
      (modulePullbackCongr (congrArg (fun q : Z₀ ⟶ Z₂ => q.toLRSHom.toShHom) hf)).hom.app
          (conormalSheaf i₂.liftCoborder.toLRSHom.toShHom) ≫
        immersionConormalSheafMap i₀ i₂ f' k (toShHom_square comm') := by
  subst hf
  exact (Category.id_comp _).symm

/-! ### Exactness at the middle term -/

/-- The coborder of the range of a closed immersion is everything, its range being closed. -/
private theorem coborderRange_eq_top {Z₀ X₀ : Scheme.{u}} (f : Z₀ ⟶ X₀)
    [IsClosedImmersion f] : f.coborderRange = ⊤ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  change x ∈ coborder (Set.range f.base)
  rw [IsClosed.coborder_eq f.isClosedEmbedding.isClosed_range]
  trivial

/-- **The conormal sequence of [Stacks Project, Tag 062S] for a chain of immersions `a`, `b` whose
composite is a given immersion `c`**, the vanishing of the composite. The two maps are arguments
pinned by equations, so that a complex built from them is spelled as the caller spells it. -/
private theorem conormalSequence_comp_zero_of_eq {Z₀ P₀ Z₁ : Scheme.{u}} (a : Z₀ ⟶ P₀)
    (b : P₀ ⟶ Z₁) [IsImmersion a] [IsImmersion b] {c : Z₀ ⟶ Z₁} [IsImmersion c]
    (hc : a ≫ b = c)
    (L : (modulePullback a.toLRSHom.toShHom).obj
          (conormalSheaf b.liftCoborder.toLRSHom.toShHom) ⟶
        conormalSheaf c.liftCoborder.toLRSHom.toShHom)
    (R : conormalSheaf c.liftCoborder.toLRSHom.toShHom ⟶
        conormalSheaf a.liftCoborder.toLRSHom.toShHom)
    (hL : L = immersionConormalSheafMap c b a (𝟙 Z₁)
      (toShHom_square (by rw [Category.comp_id, hc])))
    (hR : R = ((modulePullbackId Z₀.toLocallyRingedSpace.toRingedSpace).app
          (conormalSheaf c.liftCoborder.toLRSHom.toShHom)).inv ≫
        immersionConormalSheafMap a c (𝟙 Z₀) b
          (toShHom_square (by rw [Category.id_comp, hc]))) :
    L ≫ R = 0 := by
  subst hL hR hc
  exact Stacks.Immersion.conormalSequence_comp_zero a b

/-- **The conormal sequence of [Stacks Project, Tag 062S] for a chain of immersions `a`, `b` whose
composite is a given immersion `c`**, exactness at the middle term. -/
@[sga "6 VIII 2.6" "partial"]
private theorem conormalSequence_exact_of_eq {Z₀ P₀ Z₁ : Scheme.{u}} (a : Z₀ ⟶ P₀)
    (b : P₀ ⟶ Z₁) [IsImmersion a] [IsImmersion b] {c : Z₀ ⟶ Z₁} [IsImmersion c]
    (hc : a ≫ b = c)
    (L : (modulePullback a.toLRSHom.toShHom).obj
          (conormalSheaf b.liftCoborder.toLRSHom.toShHom) ⟶
        conormalSheaf c.liftCoborder.toLRSHom.toShHom)
    (R : conormalSheaf c.liftCoborder.toLRSHom.toShHom ⟶
        conormalSheaf a.liftCoborder.toLRSHom.toShHom)
    (hL : L = immersionConormalSheafMap c b a (𝟙 Z₁)
      (toShHom_square (by rw [Category.comp_id, hc])))
    (hR : R = ((modulePullbackId Z₀.toLocallyRingedSpace.toRingedSpace).app
          (conormalSheaf c.liftCoborder.toLRSHom.toShHom)).inv ≫
        immersionConormalSheafMap a c (𝟙 Z₀) b
          (toShHom_square (by rw [Category.id_comp, hc]))) :
    (ShortComplex.mk L R (conormalSequence_comp_zero_of_eq a b hc L R hL hR)).Exact := by
  subst hL hR hc
  exact Stacks.Immersion.conormalSequence_exact a b

/-- The coborder of the range of the projection `Y ×_{Y'} Z' ⟶ Z'` is everything: it is a closed
immersion, being the inclusion of the thickening produced by part (1). -/
private theorem coborderRange_snd_eq_top :
    (pullback.snd tY.inclusion (transitivityMap i p tZ tY)).coborderRange = ⊤ :=
  have : IsClosedImmersion (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) :=
    (isFirstOrderThickening_relative_snd i p tZ tY).1
  coborderRange_eq_top _

/-- The square of the second arrow, with the identity of `Z'` for its lower horizontal map. -/
private theorem transitivityConormalSquareA :
    tZ.inclusion ≫ 𝟙 tZ.ambient =
      relativeInclusion i p tZ tY ≫
        pullback.snd tY.inclusion (transitivityMap i p tZ tY) := by
  rw [Category.comp_id, relativeInclusion_comp_snd]

/-- The square of the projections of the fibre product `Y ×_{Y'} Z'`. -/
private theorem transitivityConormalSquareB :
    pullback.snd tY.inclusion (transitivityMap i p tZ tY) ≫ transitivityMap i p tZ tY =
      relativeToBase i p tZ tY ≫ tY.inclusion :=
  pullback.condition.symm

/-- The square of the first arrow, with `i` factored through `Y ×_{Y'} Z'`. -/
private theorem transitivityConormalSquareT :
    tZ.inclusion ≫ transitivityMap i p tZ tY =
      (relativeInclusion i p tZ tY ≫ relativeToBase i p tZ tY) ≫ tY.inclusion := by
  rw [relativeInclusion_comp_fst, inclusion_comp_transitivityMap]

/-- **The comparison `i^* 𝒞_{Y/X} ⟶ (pr₂)^* 𝒞_{(Y ×_{Y'} Z')/Z'}`** from the left-hand term of the
conormal sequence of part (2) of [Stacks Project, Tag 06AE] to the left-hand term of the sequence
of [Stacks Project, Tag 062S] for the chain `Z ⟶ Y ×_{Y'} Z' ⟶ Z'`: the pullback along
`Z ⟶ Y ×_{Y'} Z'` of the map of [Stacks Project, Tag 01R4] for the square of projections of the
fibre product, read through the two pullback comparisons. -/
private def transitivityConormalComparison :
    (modulePullback i.toLRSHom.toShHom).obj
        (conormalSheaf tY.inclusion.liftCoborder.toLRSHom.toShHom) ⟶
      (modulePullback (relativeInclusion i p tZ tY).toLRSHom.toShHom).obj
        (conormalSheaf (pullback.snd tY.inclusion
          (transitivityMap i p tZ tY)).liftCoborder.toLRSHom.toShHom) :=
  (modulePullbackCongr (congrArg (fun q : Z ⟶ Y => q.toLRSHom.toShHom)
          (relativeInclusion_comp_fst i p tZ tY).symm)).hom.app
        (conormalSheaf tY.inclusion.liftCoborder.toLRSHom.toShHom) ≫
    (modulePullbackComp (relativeInclusion i p tZ tY).toLRSHom.toShHom
          (relativeToBase i p tZ tY).toLRSHom.toShHom).hom.app
        (conormalSheaf tY.inclusion.liftCoborder.toLRSHom.toShHom) ≫
      (modulePullback (relativeInclusion i p tZ tY).toLRSHom.toShHom).map
        (immersionConormalSheafMap
          (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) tY.inclusion
          (relativeToBase i p tZ tY) (transitivityMap i p tZ tY)
          (toShHom_square (transitivityConormalSquareB i p tZ tY)))

/-- **The comparison of the two left-hand terms is an epimorphism.** -/
private theorem epi_transitivityConormalComparison :
    Epi (transitivityConormalComparison i p tZ tY) := by
  have hpe : (modulePullback
      (relativeInclusion i p tZ tY).toLRSHom.toShHom).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (modulePullbackPushforwardAdjunction (relativeInclusion i p tZ tY).toLRSHom.toShHom)
  have hq : Epi (immersionConormalSheafMap
      (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) tY.inclusion
      (relativeToBase i p tZ tY) (transitivityMap i p tZ tY)
      (toShHom_square (transitivityConormalSquareB i p tZ tY))) :=
    epi_immersionConormalSheafMap _ tY.inclusion _ _
      (IsPullback.of_hasPullback tY.inclusion (transitivityMap i p tZ tY)).flip
  have hmap : Epi ((modulePullback (relativeInclusion i p tZ tY).toLRSHom.toShHom).map
      (immersionConormalSheafMap
        (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) tY.inclusion
        (relativeToBase i p tZ tY) (transitivityMap i p tZ tY)
        (toShHom_square (transitivityConormalSquareB i p tZ tY)))) :=
    @Functor.PreservesEpimorphisms.preserves _ _ _ _ _ hpe _ _ _ hq
  have hinner := @epi_comp _ _ _ _ _
    ((modulePullbackComp (relativeInclusion i p tZ tY).toLRSHom.toShHom
          (relativeToBase i p tZ tY).toLRSHom.toShHom).hom.app
        (conormalSheaf tY.inclusion.liftCoborder.toLRSHom.toShHom))
    inferInstance _ hmap
  exact @epi_comp _ _ _ _ _
    ((modulePullbackCongr (congrArg (fun q : Z ⟶ Y => q.toLRSHom.toShHom)
            (relativeInclusion_comp_fst i p tZ tY).symm)).hom.app
        (conormalSheaf tY.inclusion.liftCoborder.toLRSHom.toShHom))
    inferInstance _ hinner

/-- **The first arrow of the conormal sequence factored through the chain of immersions
`Z ⟶ Y ×_{Y'} Z' ⟶ Z'`.** It is `Stacks.Thickenings.transitivityConormalComparison` followed by
the left-hand map of the sequence of [Stacks Project, Tag 062S] for that chain. -/
private theorem transitivityConormalLeftMap_eq :
    transitivityConormalLeftMap i p tZ tY =
      transitivityConormalComparison i p tZ tY ≫
        immersionConormalSheafMap tZ.inclusion
          (pullback.snd tY.inclusion (transitivityMap i p tZ tY))
          (relativeInclusion i p tZ tY) (𝟙 tZ.ambient)
          (toShHom_square (transitivityConormalSquareA i p tZ tY)) := by
  change immersionConormalSheafMap tZ.inclusion tY.inclusion i (transitivityMap i p tZ tY)
      (toShHom_square (inclusion_comp_transitivityMap i p tZ tY).symm) = _
  rw [immersionConormalSheafMap_congr_left tZ.inclusion tY.inclusion
      (relativeInclusion_comp_fst i p tZ tY).symm (transitivityMap i p tZ tY)
      (inclusion_comp_transitivityMap i p tZ tY).symm (transitivityConormalSquareT i p tZ tY),
    immersionConormalSheafMap_comp_id tZ.inclusion
      (pullback.snd tY.inclusion (transitivityMap i p tZ tY)) tY.inclusion
      (coborderRange_snd_eq_top i p tZ tY) (relativeInclusion i p tZ tY)
      (relativeToBase i p tZ tY) (transitivityMap i p tZ tY)
      (transitivityConormalSquareA i p tZ tY) (transitivityConormalSquareB i p tZ tY)
      (transitivityConormalSquareT i p tZ tY)]
  exact (Category.assoc _ _ _).symm

/-- **The two arrows of the conormal sequence of [Stacks Project, Tag 062S] for the chain
`Z ⟶ Y ×_{Y'} Z' ⟶ Z'` compose to zero**, its right-hand arrow being the second arrow of the
sequence of part (2) of [Stacks Project, Tag 06AE]. -/
private theorem transitivityConormalRelative_comp_zero :
    immersionConormalSheafMap tZ.inclusion
        (pullback.snd tY.inclusion (transitivityMap i p tZ tY))
        (relativeInclusion i p tZ tY) (𝟙 tZ.ambient)
        (toShHom_square (transitivityConormalSquareA i p tZ tY)) ≫
      transitivityConormalRightMap i p tZ tY = 0 :=
  conormalSequence_comp_zero_of_eq (relativeInclusion i p tZ tY)
    (pullback.snd tY.inclusion (transitivityMap i p tZ tY))
    (relativeInclusion_comp_snd i p tZ tY) _ _ rfl rfl

/-- **The conormal sequence of [Stacks Project, Tag 062S] for the chain `Z ⟶ Y ×_{Y'} Z' ⟶ Z'` is
exact at its middle term.** -/
private theorem transitivityConormalRelative_exact :
    (ShortComplex.mk _ _ (transitivityConormalRelative_comp_zero i p tZ tY)).Exact :=
  conormalSequence_exact_of_eq (relativeInclusion i p tZ tY)
    (pullback.snd tY.inclusion (transitivityMap i p tZ tY))
    (relativeInclusion_comp_snd i p tZ tY) _ _ rfl rfl

/-- **Part (2) of [Stacks Project, Tag 06AE], exactness at `𝒞_{Z/X}`.** The conormal sequence
`i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` is exact at its middle term; with
`Stacks.Thickenings.epi_transitivityConormalRightMap` this makes
`i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` exact. -/
@[stacks 06AE "part (2): exactness at the middle term",
  sga "6 VIII 2.2" "partial",
  sga "6 VIII 2.6" "partial"]
theorem transitivityConormalShortComplex_exact :
    (transitivityConormalShortComplex i p tZ tY).Exact :=
  (@ShortComplex.exact_iff_of_epi_of_isIso_of_mono _ _ _
    (transitivityConormalShortComplex i p tZ tY)
    (ShortComplex.mk _ _ (transitivityConormalRelative_comp_zero i p tZ tY))
    { τ₁ := transitivityConormalComparison i p tZ tY
      τ₂ := 𝟙 (transitivityConormalShortComplex i p tZ tY).X₂
      τ₃ := 𝟙 (transitivityConormalShortComplex i p tZ tY).X₃
      comm₁₂ := (transitivityConormalLeftMap_eq i p tZ tY).symm.trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
    (epi_transitivityConormalComparison i p tZ tY)
    (inferInstanceAs (IsIso (𝟙 (transitivityConormalShortComplex i p tZ tY).X₂)))
    (inferInstanceAs (Mono (𝟙 (transitivityConormalShortComplex i p tZ tY).X₃)))).mpr
    (transitivityConormalRelative_exact i p tZ tY)

end Stacks.Thickenings

end
