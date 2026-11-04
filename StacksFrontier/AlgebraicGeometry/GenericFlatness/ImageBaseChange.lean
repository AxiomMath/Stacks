module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.IdealSheafComap

/-!
# Base change of the scheme-theoretic image

Let `f : X ⟶ Y` be a morphism of schemes over a base `T`. The scheme-theoretic image of `f` is
the closed subscheme of `Y` cut out by the kernel ideal sheaf `f.ker`, and one says that
*formation of the scheme-theoretic image of `f / T` commutes with arbitrary base change* when for
every `T' ⟶ T` the kernel of the base changed morphism is the inverse image of `f.ker`. This is
the property occurring in clause (3) of [Stacks, Tag 0H41], and it is written down here as
`AlgebraicGeometry.ImageCommutesWithBaseChange`.

The file then proves the formal properties of that condition which the proof of Stacks 0H41
needs: it is invariant under isomorphisms of the morphism, stable under further base change,
local on an affine cover of the base, insensitive to precomposition with a morphism admitting
local sections, and it holds for a morphism of affine schemes over an affine base whose map on
global sections has flat target and flat cokernel.

## Main definitions

* `AlgebraicGeometry.ImageCommutesWithBaseChange`: formation of the scheme-theoretic image of a
  morphism over `T` commutes with arbitrary base change on `T`.

## Main results

* `Stacks.GenericFlatness.imageCommutesWithBaseChange_of_isIso`,
  `Stacks.GenericFlatness.imageCommutesWithBaseChange_pullback` and
  `Stacks.GenericFlatness.imageCommutesWithBaseChange_comp`: invariance under isomorphism and
  stability under base change.
* `Stacks.GenericFlatness.imageCommutesWithBaseChange_of_isAffine_base`: it suffices to test the
  condition on affine `T'`.
* `Stacks.GenericFlatness.imageCommutesWithBaseChange_of_flat_appTop`: the affine case, from
  flatness of the target and of the cokernel on global sections.
* `Stacks.GenericFlatness.imageCommutesWithBaseChange_of_openCover_lifts`: the condition passes
  from `p ≫ f` to `f` when `p` admits sections over an open cover of its target, which is how the
  affine case is spread to a morphism with an affine cover of the source.
* `Stacks.GenericFlatness.overPullback_map_left_fst` and
  `Stacks.GenericFlatness.overPullback_map_left_snd`: the two projections of a base changed
  morphism in an over-category.

## Implementation notes

Base change is taken with Mathlib's `CategoryTheory.Over.pullback`, so a morphism over `T` is an
arrow of `CategoryTheory.Over T` and its base change along `g : T' ⟶ T` is
`(Over.pullback g).map f`; the underlying morphism of schemes is its `.left`. The kernel ideal
sheaf is Mathlib's `AlgebraicGeometry.Scheme.Hom.ker`, whose closed subscheme is the
scheme-theoretic image, and the inverse image of ideal sheaves is
`AlgebraicGeometry.Scheme.IdealSheafData.comap`; equality of these two ideal sheaves is the
statement that the canonical comparison of the two scheme-theoretic images is an isomorphism.

## References

* [Stacks Project, Tag 0H41](https://stacks.math.columbia.edu/tag/0H41)
* [Stacks Project, Tag 01R6](https://stacks.math.columbia.edu/tag/01R6)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Clause (3) of Stacks 0H41.** Formation of the scheme-theoretic image of a morphism `f`
over `T` commutes with arbitrary base change on `T`: for every `g : T' ⟶ T` the kernel ideal
sheaf of the base change of `f` along `g` is the inverse image of the kernel ideal sheaf of
`f`. -/
def ImageCommutesWithBaseChange {T : Scheme.{u}} {X Y : Over T} (f : X ⟶ Y) : Prop :=
  ∀ {T' : Scheme.{u}} (g : T' ⟶ T),
    (((Over.pullback g).map f).left).ker = f.left.ker.comap (pullback.fst Y.hom g)

end AlgebraicGeometry

namespace Stacks.GenericFlatness

/-! ### Base change squares in the over-category -/

/-- The first projection of a base changed morphism over `T`. -/
@[reassoc]
theorem overPullback_map_left_fst {T T' : Scheme.{u}} (g : T' ⟶ T)
    {X Y : Over T} (f : X ⟶ Y) :
    ((Over.pullback g).map f).left ≫ pullback.fst Y.hom g =
      pullback.fst X.hom g ≫ f.left := by
  simp [Over.pullback_map_left, pullback.lift_fst]

/-- The second projection of a base changed morphism over `T`. -/
@[reassoc]
theorem overPullback_map_left_snd {T T' : Scheme.{u}} (g : T' ⟶ T)
    {X Y : Over T} (f : X ⟶ Y) :
    ((Over.pullback g).map f).left ≫ pullback.snd Y.hom g = pullback.snd X.hom g := by
  simp [Over.pullback_map_left, pullback.lift_snd]

/-- Base changing twice, along `g` and then along `h`, agrees with base changing once along
`h ≫ g`, through the canonical comparison isomorphism of iterated fibre products. -/
private theorem overPullback_map_left_comparison {T T' T'' : Scheme.{u}}
    {X Y : Over T} (f : X ⟶ Y) (g : T' ⟶ T) (h : T'' ⟶ T') :
    ((Over.pullback h).map ((Over.pullback g).map f)).left ≫
        (pullbackLeftPullbackSndIso Y.hom g h).hom =
      (pullbackLeftPullbackSndIso X.hom g h).hom ≫
        ((Over.pullback (h ≫ g)).map f).left := by
  have hY : pullback.fst (pullback.snd Y.hom g) h
      = pullback.fst ((Over.pullback g).obj Y).hom h := rfl
  have hY' : pullback.snd (pullback.snd Y.hom g) h
      = pullback.snd ((Over.pullback g).obj Y).hom h := rfl
  have hX : pullback.fst (pullback.snd X.hom g) h
      = pullback.fst ((Over.pullback g).obj X).hom h := rfl
  have hX' : pullback.snd (pullback.snd X.hom g) h
      = pullback.snd ((Over.pullback g).obj X).hom h := rfl
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullbackLeftPullbackSndIso_hom_snd, pullbackLeftPullbackSndIso_hom_fst_assoc,
      hY, hY', hX, hX', overPullback_map_left_fst, overPullback_map_left_snd,
      overPullback_map_left_fst_assoc]

/-- The base change of a morphism over `T` along `g : T' ⟶ T` sits in a fibre square over the
original morphism. -/
theorem isPullback_overPullback_map {T T' : Scheme.{u}}
    {X Y : Over T} (f : X ⟶ Y) (g : T' ⟶ T) :
    IsPullback ((Over.pullback g).map f).left (pullback.fst X.hom g)
      (pullback.fst Y.hom g) f.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd Y.hom g) (h₂₂ := Y.hom) ?_
    (overPullback_map_left_fst g f) (IsPullback.of_hasPullback Y.hom g).flip
  rw [overPullback_map_left_snd, Over.w]
  exact (IsPullback.of_hasPullback X.hom g).flip

/-- Base change preserves commuting squares of morphisms over `T`. -/
private theorem overPullback_map_left_comm {T T' : Scheme.{u}}
    {X X' Y Y' : Over T} (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : f' ≫ b = a ≫ f) (g : T' ⟶ T) :
    ((Over.pullback g).map f').left ≫ ((Over.pullback g).map b).left =
      ((Over.pullback g).map a).left ≫ ((Over.pullback g).map f).left := by
  simpa only [Functor.map_comp, Over.comp_left] using
    congrArg (fun q ↦ ((Over.pullback g).map q).left) w

/-- A fibre square of morphisms over `T` stays a fibre square after base change. -/
theorem isPullback_overPullback_map_of_isPullback {T T' : Scheme.{u}}
    {X X' Y Y' : Over T} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (h : IsPullback f'.left a.left b.left f.left) (g : T' ⟶ T) :
    IsPullback ((Over.pullback g).map f').left ((Over.pullback g).map a).left
      ((Over.pullback g).map b).left ((Over.pullback g).map f).left := by
  have hrect := (isPullback_overPullback_map f' g).paste_vert h
  rw [← (isPullback_overPullback_map a g).w, ← (isPullback_overPullback_map b g).w] at hrect
  exact IsPullback.of_bot hrect
    (overPullback_map_left_comm f f' a b (Over.OverMorphism.ext h.w) g)
    (isPullback_overPullback_map f g)

/-! ### Kernel ideal sheaves in a fibre square -/

/-- In a fibre square whose right-hand edge is an open immersion, the kernel ideal sheaf of the
restricted morphism is the inverse image of the kernel ideal sheaf. -/
theorem ker_eq_comap_of_isPullback_of_isOpenImmersion {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    [QuasiCompact f] [IsOpenImmersion b] (h : IsPullback f' a b f) :
    f'.ker = f.ker.comap b := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' a b h U

/-- The image of an ideal sheaf under an isomorphism is the inverse image under its inverse. -/
private theorem map_eq_comap_inv {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (e : X ⟶ Y) [IsIso e] : I.map e = I.comap (inv e) := by
  apply le_antisymm
  · simpa only [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id] using
      Scheme.IdealSheafData.comap_mono (inv e) (I.comap_map_le e)
  · apply Scheme.IdealSheafData.le_map_iff_comap_le.mpr
    simp only [← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id,
      Scheme.IdealSheafData.comap_id, le_refl]

/-- In a commuting square whose horizontal edges are isomorphisms, the kernel ideal sheaf of the
top morphism is the inverse image of the kernel ideal sheaf of the bottom one. -/
theorem ker_eq_comap_of_isIso_square {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    [IsIso a] [IsIso b] (w : f' ≫ b = a ≫ f) :
    f'.ker = f.ker.comap b := by
  simpa only [Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp,
    map_eq_comap_inv, ← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id,
    Scheme.IdealSheafData.comap_id] using congrArg (fun k : X' ⟶ Y ↦ k.ker.comap b) w

/-- If the kernel ideal sheaf of `F` is an inverse image of `I` along `c`, then so is that of a
morphism `F'` related to `F` by a square of isomorphisms, along any `e ≫ d` equal to `b ≫ c`. -/
private theorem ker_eq_comap_comap_of_isIso_square {X Y X' Y' Z Y₂ : Scheme.{u}}
    (F : X ⟶ Y) (F' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y) [IsIso a] [IsIso b]
    (w : F' ≫ b = a ≫ F) {I : Z.IdealSheafData} {c : Y ⟶ Z} (hF : F.ker = I.comap c)
    (d : Y₂ ⟶ Z) (e : Y' ⟶ Y₂) (h : e ≫ d = b ≫ c) :
    F'.ker = (I.comap d).comap e := by
  rw [ker_eq_comap_of_isIso_square _ _ a b w, hF, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, h]

/-- **An ideal sheaf is determined by its inverse images along a family of open immersions
covering the scheme.** Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.eq_of_comap_eq_of_iUnion_range_eq_univ` asks the sources
to be affine; refining each of them by its affine cover removes that hypothesis. -/
theorem idealSheafData_eq_of_comap_eq {X : Scheme.{u}} {ι : Type*} {Z : ι → Scheme.{u}}
    (p : ∀ i, Z i ⟶ X) (hp : ∀ i, IsOpenImmersion (p i))
    (hcov : ⋃ i, Set.range (p i).base = Set.univ)
    {I J : X.IdealSheafData} (h : ∀ i, I.comap (p i) = J.comap (p i)) : I = J := by
  have := hp
  refine Scheme.IdealSheafData.eq_of_comap_eq_of_iUnion_range_eq_univ
    (Z := fun ij : (i : ι) × (Z i).affineCover.I₀ ↦ (Z ij.1).affineCover.X ij.2)
    (fun ij ↦ (Z ij.1).affineCover.f ij.2 ≫ p ij.1) ?_ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (hcov.ge (Set.mem_univ x))
    obtain ⟨j, z, hz⟩ := (Z i).affineCover.exists_eq y
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, z, by simp only [Scheme.Hom.comp_apply, hz, hy]⟩
  · rintro ⟨i, j⟩
    simpa only [Scheme.IdealSheafData.comap_comp] using
      congrArg (fun K : (Z i).IdealSheafData ↦ K.comap ((Z i).affineCover.f j)) (h i)

/-- The form of `Stacks.GenericFlatness.idealSheafData_eq_of_comap_eq` for an open cover. -/
theorem idealSheafData_eq_of_comap_eq_openCover {X : Scheme.{u}}
    (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  idealSheafData_eq_of_comap_eq 𝒰.f 𝒰.map_prop 𝒰.iUnion_range h

/-! ### Formal properties of compatibility with base change -/

/-- Compatibility with base change is invariant under isomorphisms of the morphism over `T`. -/
theorem imageCommutesWithBaseChange_of_isIso {T : Scheme.{u}}
    {X Y X' Y' : Over T} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X' ≅ X) (eY : Y' ≅ Y) (w : f' ≫ eY.hom = eX.hom ≫ f)
    (hf : ImageCommutesWithBaseChange f) : ImageCommutesWithBaseChange f' := by
  have hX : IsIso eX.hom.left := (Over.forget T).map_isIso eX.hom
  have hY : IsIso eY.hom.left := (Over.forget T).map_isIso eY.hom
  have hw : f'.left ≫ eY.hom.left = eX.hom.left ≫ f.left := congrArg (fun k ↦ k.left) w
  intro T' g
  have hXg : IsIso ((Over.pullback g).map eX.hom).left :=
    (Over.forget T').map_isIso ((Over.pullback g).map eX.hom)
  have hYg : IsIso ((Over.pullback g).map eY.hom).left :=
    (Over.forget T').map_isIso ((Over.pullback g).map eY.hom)
  rw [ker_eq_comap_of_isIso_square _ _ _ _ hw]
  exact ker_eq_comap_comap_of_isIso_square _ _ _ _ (overPullback_map_left_comm f f' _ _ w g)
    (hf g) _ _ (overPullback_map_left_fst g eY.hom).symm

/-- Compatibility with base change is stable under base change. -/
theorem imageCommutesWithBaseChange_pullback {T T' : Scheme.{u}}
    {X Y : Over T} {f : X ⟶ Y} (hf : ImageCommutesWithBaseChange f)
    (g : T' ⟶ T) : ImageCommutesWithBaseChange ((Over.pullback g).map f) := by
  intro T'' h
  rw [hf g]
  exact ker_eq_comap_comap_of_isIso_square _ _ _ _ (overPullback_map_left_comparison f g h)
    (hf (h ≫ g)) _ _ (by simp)

/-- Compatibility with base change over `T` passes to compatibility over any `U ⟶ T` factoring
through a morphism over which it is already known. -/
theorem imageCommutesWithBaseChange_comp {S T U : Scheme.{u}}
    {X Y : Over S} {f : X ⟶ Y} (g : T ⟶ S) (h : U ⟶ T)
    (hf : ImageCommutesWithBaseChange ((Over.pullback g).map f)) :
    ImageCommutesWithBaseChange ((Over.pullback (h ≫ g)).map f) :=
  imageCommutesWithBaseChange_of_isIso
    ((Over.pullbackComp h g).app X) ((Over.pullbackComp h g).app Y)
    ((Over.pullbackComp h g).hom.naturality f)
    (imageCommutesWithBaseChange_pullback hf h)

/-! ### Reduction to an affine base -/

/-- When the structure morphism of the target is affine, compatibility with base change only has
to be tested on affine bases. -/
theorem imageCommutesWithBaseChange_of_isAffine_base {T : Scheme.{u}}
    {X Y : Over T} (f : X ⟶ Y) [QuasiCompact f.left] [IsAffineHom Y.hom]
    (h : ∀ {T' : Scheme.{u}} [IsAffine T'] (g : T' ⟶ T),
      (((Over.pullback g).map f).left).ker =
        f.left.ker.comap (pullback.fst Y.hom g)) :
    ImageCommutesWithBaseChange f := by
  intro T' g
  let Xg := (Over.pullback g).obj X
  let Yg := (Over.pullback g).obj Y
  let fg := (Over.pullback g).map f
  have : IsAffineHom Yg.hom :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback Y.hom g) ‹_›
  have : QuasiCompact fg.left :=
    MorphismProperty.of_isPullback (isPullback_overPullback_map f g).flip inferInstance
  have hoi : ∀ i, IsOpenImmersion (pullback.fst Yg.hom (T'.affineCover.f i)) := fun i ↦
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback Yg.hom (T'.affineCover.f i)).flip (T'.affineCover.map_prop i)
  have := hoi
  refine idealSheafData_eq_of_comap_eq (fun i ↦ pullback.fst Yg.hom (T'.affineCover.f i)) hoi
    ?_ ?_
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨i, t, ht⟩ := T'.affineCover.exists_eq (Yg.hom y)
    have hmem : y ∈ Set.range (pullback.fst Yg.hom (T'.affineCover.f i)).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    exact Set.mem_iUnion.mpr ⟨i, hmem⟩
  intro i
  show fg.left.ker.comap (pullback.fst Yg.hom (T'.affineCover.f i)) = _
  rw [← ker_eq_comap_of_isPullback_of_isOpenImmersion fg.left
    ((Over.pullback (T'.affineCover.f i)).map fg).left
    (pullback.fst Xg.hom (T'.affineCover.f i))
    (pullback.fst Yg.hom (T'.affineCover.f i))
    (isPullback_overPullback_map fg (T'.affineCover.f i))]
  exact ker_eq_comap_comap_of_isIso_square _ _
    (pullbackLeftPullbackSndIso X.hom g (T'.affineCover.f i)).hom
    (pullbackLeftPullbackSndIso Y.hom g (T'.affineCover.f i)).hom
    (overPullback_map_left_comparison f g (T'.affineCover.f i))
    (h (T'.affineCover.f i ≫ g)) _ _
    (pullbackLeftPullbackSndIso_hom_fst Y.hom g (T'.affineCover.f i)).symm

/-! ### The affine case -/

/-- For morphisms of affine schemes over an affine base whose map on global sections has flat
target and flat cokernel, the kernel ideal sheaf commutes with base change. -/
private theorem ker_baseChange_of_flat_appTop
    {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (X Y : Over T) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) (g : T' ⟶ T)
    [Algebra Γ(T, ⊤) Γ(Y.left, ⊤)] [Algebra Γ(T, ⊤) Γ(X.left, ⊤)]
    (hY : algebraMap Γ(T, ⊤) Γ(Y.left, ⊤) = Y.hom.appTop.hom)
    (hX : algebraMap Γ(T, ⊤) Γ(X.left, ⊤) = X.hom.appTop.hom)
    (φ : Γ(Y.left, ⊤) →ₐ[Γ(T, ⊤)] Γ(X.left, ⊤)) (hφ : φ.toRingHom = f.left.appTop.hom)
    [Module.Flat Γ(T, ⊤) Γ(X.left, ⊤)]
    [Module.Flat Γ(T, ⊤) (Γ(X.left, ⊤) ⧸ LinearMap.range φ.toLinearMap)] :
    (((Over.pullback g).map f).left).ker =
      f.left.ker.comap (pullback.fst Y.hom g) := by
  have : IsAffine ((Over.pullback g).obj Y).left :=
    inferInstanceAs (IsAffine (pullback Y.hom g))
  have : IsAffine ((Over.pullback g).obj X).left :=
    inferInstanceAs (IsAffine (pullback X.hom g))
  let _ : Algebra Γ(T, ⊤) Γ(T', ⊤) := g.appTop.hom.toAlgebra
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine, Scheme.ker_of_isAffine f.left,
    Scheme.ker_of_isAffine ((Over.pullback g).map f).left]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rw [← hφ]
  apply ker_eq_map_of_isPushout_of_flat φ
    (pullback.fst Y.hom g).appTop.hom (pullback.fst X.hom g).appTop.hom
    (pullback.snd Y.hom g).appTop.hom (pullback.snd X.hom g).appTop.hom
  · simpa only [hY, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using
      isPushout_appTop_of_isPullback (IsPullback.of_hasPullback Y.hom g)
  · simpa only [hX, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using
      isPushout_appTop_of_isPullback (IsPullback.of_hasPullback X.hom g)
  · rw [hφ]
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun k ↦ k.appTop.hom) (isPullback_overPullback_map f g).w
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun k ↦ k.appTop.hom) (overPullback_map_left_snd g f)

/-- **The affine case of clause (3) of Stacks 0H41.** Flatness of the target module and of the
cokernel of the map on global sections gives compatibility with arbitrary base change for a
morphism of affine schemes over an affine base. -/
theorem imageCommutesWithBaseChange_of_flat_appTop
    {T : Scheme.{u}} [IsAffine T]
    (X Y : Over T) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y)
    [Algebra Γ(T, ⊤) Γ(Y.left, ⊤)] [Algebra Γ(T, ⊤) Γ(X.left, ⊤)]
    (hY : algebraMap Γ(T, ⊤) Γ(Y.left, ⊤) = Y.hom.appTop.hom)
    (hX : algebraMap Γ(T, ⊤) Γ(X.left, ⊤) = X.hom.appTop.hom)
    (φ : Γ(Y.left, ⊤) →ₐ[Γ(T, ⊤)] Γ(X.left, ⊤)) (hφ : φ.toRingHom = f.left.appTop.hom)
    [Module.Flat Γ(T, ⊤) Γ(X.left, ⊤)]
    [Module.Flat Γ(T, ⊤) (Γ(X.left, ⊤) ⧸ LinearMap.range φ.toLinearMap)] :
    ImageCommutesWithBaseChange f :=
  imageCommutesWithBaseChange_of_isAffine_base f fun g ↦
    ker_baseChange_of_flat_appTop X Y f g hY hX φ hφ

/-! ### Spreading the affine case along a cover of the source -/

/-- A morphism admitting sections over an open cover of its target has trivial kernel ideal
sheaf. -/
private theorem ker_eq_bot_of_openCover_lifts {X Z : Scheme.{u}}
    (p : Z ⟶ X) (𝒰 : X.OpenCover) (l : ∀ i, 𝒰.X i ⟶ Z)
    (hl : ∀ i, l i ≫ p = 𝒰.f i) : p.ker = ⊥ := by
  have h : p.ker ≤ ⨅ i, (𝒰.f i).ker :=
    le_iInf fun i ↦ hl i ▸ (l i).le_ker_comp p
  have hU : (⨅ i, (𝒰.f i).ker) = ⊥ := by
    simpa using Scheme.Hom.iInf_ker_openCover_map_comp (𝟙 X) 𝒰
  exact le_bot_iff.mp (hU ▸ h)

/-- The sections of `p` over an open cover of its target base change to sections of the base
change of `p` over the base changed cover. -/
private noncomputable def overPullbackLifts {T T' : Scheme.{u}}
    {Z X : Over T} (p : Z ⟶ X) (g : T' ⟶ T)
    (𝒰 : X.left.OpenCover) (l : ∀ i, 𝒰.X i ⟶ Z.left)
    (hl : ∀ i, l i ≫ p.left = 𝒰.f i) (i : 𝒰.I₀) :
    pullback (pullback.fst X.hom g) (𝒰.f i) ⟶ ((Over.pullback g).obj Z).left :=
  pullback.lift (pullback.snd (pullback.fst X.hom g) (𝒰.f i) ≫ l i)
    (pullback.fst (pullback.fst X.hom g) (𝒰.f i) ≫ pullback.snd X.hom g) (by
      rw [Category.assoc, ← p.w, ← Category.assoc (l i), hl i,
        ← Category.assoc, ← pullback.condition, Category.assoc, pullback.condition,
        Category.assoc])

@[reassoc]
private theorem overPullbackLifts_fst {T T' : Scheme.{u}}
    {Z X : Over T} (p : Z ⟶ X) (g : T' ⟶ T)
    (𝒰 : X.left.OpenCover) (l : ∀ i, 𝒰.X i ⟶ Z.left)
    (hl : ∀ i, l i ≫ p.left = 𝒰.f i) (i : 𝒰.I₀) :
    overPullbackLifts p g 𝒰 l hl i ≫ pullback.fst Z.hom g =
      pullback.snd (pullback.fst X.hom g) (𝒰.f i) ≫ l i := pullback.lift_fst _ _ _

@[reassoc]
private theorem overPullbackLifts_snd {T T' : Scheme.{u}}
    {Z X : Over T} (p : Z ⟶ X) (g : T' ⟶ T)
    (𝒰 : X.left.OpenCover) (l : ∀ i, 𝒰.X i ⟶ Z.left)
    (hl : ∀ i, l i ≫ p.left = 𝒰.f i) (i : 𝒰.I₀) :
    overPullbackLifts p g 𝒰 l hl i ≫ pullback.snd Z.hom g =
      pullback.fst (pullback.fst X.hom g) (𝒰.f i) ≫ pullback.snd X.hom g :=
  pullback.lift_snd _ _ _

private theorem overPullbackLifts_comp {T T' : Scheme.{u}}
    {Z X : Over T} (p : Z ⟶ X) (g : T' ⟶ T)
    (𝒰 : X.left.OpenCover) (l : ∀ i, 𝒰.X i ⟶ Z.left)
    (hl : ∀ i, l i ≫ p.left = 𝒰.f i) (i : 𝒰.I₀) :
    overPullbackLifts p g 𝒰 l hl i ≫ ((Over.pullback g).map p).left =
      (𝒰.pullback₁ (pullback.fst X.hom g)).f i := by
  apply pullback.hom_ext
  · rw [Category.assoc, overPullback_map_left_fst, overPullbackLifts_fst_assoc, hl]
    exact pullback.condition.symm
  · rw [Category.assoc, overPullback_map_left_snd, overPullbackLifts_snd]
    rfl

/-- **Clause (3) of Stacks 0H41 descends along a cover of the source.** If `p : Z ⟶ X` admits
sections over an open cover of `X`, then compatibility with base change for `p ≫ f` gives it for
`f`: both morphisms have the same scheme-theoretic image, before and after any base change. -/
theorem imageCommutesWithBaseChange_of_openCover_lifts {T : Scheme.{u}}
    {Z X Y : Over T} (p : Z ⟶ X) (f : X ⟶ Y)
    (𝒰 : X.left.OpenCover) (l : ∀ i, 𝒰.X i ⟶ Z.left)
    (hl : ∀ i, l i ≫ p.left = 𝒰.f i)
    (hf : ImageCommutesWithBaseChange (p ≫ f)) : ImageCommutesWithBaseChange f := by
  intro T' g
  have hbot : ((Over.pullback g).map p).left.ker = ⊥ :=
    ker_eq_bot_of_openCover_lifts _ (𝒰.pullback₁ (pullback.fst X.hom g))
      (overPullbackLifts p g 𝒰 l hl) (overPullbackLifts_comp p g 𝒰 l hl)
  simpa only [Functor.map_comp, Over.comp_left, Scheme.Hom.ker_comp,
    ker_eq_bot_of_openCover_lifts p.left 𝒰 l hl, hbot,
    Scheme.IdealSheafData.map_bot] using hf g

/-- The form of `Stacks.GenericFlatness.imageCommutesWithBaseChange_of_openCover_lifts` needed
after a base change of the whole situation. -/
theorem imageCommutesWithBaseChange_of_openCover_lifts_pullback
    {T T' : Scheme.{u}} {Z X Y : Over T} (p : Z ⟶ X) (f : X ⟶ Y)
    (𝒰 : X.left.OpenCover) (l : ∀ i, 𝒰.X i ⟶ Z.left)
    (hl : ∀ i, l i ≫ p.left = 𝒰.f i) (g : T' ⟶ T)
    (hf : ImageCommutesWithBaseChange ((Over.pullback g).map (p ≫ f))) :
    ImageCommutesWithBaseChange ((Over.pullback g).map f) := by
  refine imageCommutesWithBaseChange_of_openCover_lifts ((Over.pullback g).map p)
    ((Over.pullback g).map f) (𝒰.pullback₁ (pullback.fst X.hom g))
    (overPullbackLifts p g 𝒰 l hl) (overPullbackLifts_comp p g 𝒰 l hl) ?_
  rwa [Functor.map_comp] at hf

end Stacks.GenericFlatness

end
