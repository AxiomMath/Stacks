module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal

/-!
# The base change map attached to a map out of a derived pullback

For a commutative square `g' ≫ f = f' ≫ g` of algebraic spaces, `K ∈ D(𝒪_X)` and
`φ : L(g')^*K ⟶ K'` in `D(𝒪_{X'})`, the composite

`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'`

of the base change map of Stacks 07A7 with `Rf'_*φ` is the map whose invertibility Stacks 0DKH
asserts. Its invertibility is étale local on `Y'`: along an étale `h : Y'' ⟶ Y'` with base change
`X'' ⟶ X'`, the pullback of the composite is, up to the étale base change isomorphism, the
composite for the outer rectangle with `φ` restricted to `X''`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeComp`

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso`
* `AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeComp_horizontal`
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_rectangle`
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_chart`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace Stacks.CategoryTheory.BaseChangeComp

/-- Bookkeeping for the horizontal pasting of base change maps followed by a map: if
`i ≫ L(bc) ≫ bc'_M ≫ R(c) = r` and `bc'` is natural along `φ`, then
`i ≫ L(bc ≫ R'(φ)) ≫ bc'_{K'} = r ≫ R(c⁻¹ ≫ G(φ))`. -/
theorem comp_horizontal {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* C₄] (L : C₁ ⥤ C₂) (R' : C₃ ⥤ C₁) (R : C₄ ⥤ C₂) (G : C₃ ⥤ C₄)
    {A : C₂} {P : C₁} {M K' : C₃} {Q : C₄} (i : A ⟶ L.obj P) (bc : P ⟶ R'.obj M)
    (bcM : L.obj (R'.obj M) ⟶ R.obj (G.obj M)) (bcK : L.obj (R'.obj K') ⟶ R.obj (G.obj K'))
    (c : G.obj M ≅ Q) (r : A ⟶ R.obj Q) (φ : M ⟶ K')
    (hH : i ≫ L.map bc ≫ bcM ≫ R.map c.hom = r)
    (hN : L.map (R'.map φ) ≫ bcK = bcM ≫ R.map (G.map φ)) :
    i ≫ L.map (bc ≫ R'.map φ) ≫ bcK = r ≫ R.map (c.inv ≫ G.map φ) := by
  rw [L.map_comp, Category.assoc, hN, ← hH]
  simp only [Category.assoc, ← R.map_comp, Iso.hom_inv_id_assoc]

/-- If `i ≫ L(m) ≫ j` is invertible with `i` and `j` invertible, then `L(m)` is invertible. -/
theorem isIso_map_of_isIso_comp {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] (L : C₁ ⥤ C₂)
    {A D : C₂} {P Q : C₁} (i : A ⟶ L.obj P) (m : P ⟶ Q) (j : L.obj Q ⟶ D) (hi : IsIso i) (hj : IsIso j)
    {z : A ⟶ D} (e : i ≫ L.map m ≫ j = z) (hz : IsIso z) : IsIso (L.map m) := by
  have h : IsIso (i ≫ L.map m ≫ j) := e ▸ hz
  have : IsIso (L.map m ≫ j) := IsIso.of_isIso_comp_left i _
  exact IsIso.of_isIso_comp_right _ j

/-- Bookkeeping for pasting along a first square with invertible base change map: if
`i ≫ L(bc) ≫ bc' ≫ R(c) = r` with `i` and `bc` invertible, then `r ≫ R(ψ)` is invertible as soon
as `bc' ≫ R(c ≫ ψ)` is. -/
theorem isIso_comp_of_isIso_horizontal {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] (L : C₁ ⥤ C₂) (R' : C₃ ⥤ C₁) (R : C₄ ⥤ C₂) (G : C₃ ⥤ C₄)
    {A : C₂} {P : C₁} {M : C₃} {Q Q' : C₄} (i : A ⟶ L.obj P) (bc : P ⟶ R'.obj M)
    (bc' : L.obj (R'.obj M) ⟶ R.obj (G.obj M)) (c : G.obj M ≅ Q) (r : A ⟶ R.obj Q)
    (ψ : Q ⟶ Q') (hH : i ≫ L.map bc ≫ bc' ≫ R.map c.hom = r) (hi : IsIso i) (hbc : IsIso bc)
    (h : IsIso (bc' ≫ R.map (c.hom ≫ ψ))) : IsIso (r ≫ R.map ψ) := by
  rw [← hH]
  have e : (i ≫ L.map bc ≫ bc' ≫ R.map c.hom) ≫ R.map ψ =
      i ≫ L.map bc ≫ (bc' ≫ R.map (c.hom ≫ ψ)) := by
    simp only [Category.assoc, R.map_comp]
  rw [e]
  infer_instance

/-- A base change map followed by a map, transported along isomorphisms of its source and
target objects: with `e : K ≅ K₁`, `e' : K' ≅ K₁'` and `G(e) ≫ φ₁ = φ ≫ e'`, the map attached to
`φ₁` is the one attached to `φ` conjugated by `L(R'(e))` and `R(e')`. -/
theorem comp_of_iso {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] (R' : C₁ ⥤ C₂) (R : C₃ ⥤ C₄) (L : C₂ ⥤ C₄) (G : C₁ ⥤ C₃)
    {K K₁ : C₁} {K' K₁' : C₃} (e : K ≅ K₁) (e' : K' ≅ K₁')
    (bc : L.obj (R'.obj K) ⟶ R.obj (G.obj K)) (bc₁ : L.obj (R'.obj K₁) ⟶ R.obj (G.obj K₁))
    (φ : G.obj K ⟶ K') (φ₁ : G.obj K₁ ⟶ K₁')
    (hn : L.map (R'.map e.hom) ≫ bc₁ = bc ≫ R.map (G.map e.hom))
    (h : G.map e.hom ≫ φ₁ = φ ≫ e'.hom) :
    bc₁ ≫ R.map φ₁ = L.map (R'.map e.inv) ≫ (bc ≫ R.map φ) ≫ R.map e'.hom := by
  have h₁ : bc₁ = L.map (R'.map e.inv) ≫ bc ≫ R.map (G.map e.hom) := by
    rw [← hn, ← Category.assoc, ← L.map_comp, ← R'.map_comp, e.inv_hom_id, R'.map_id,
      L.map_id, Category.id_comp]
  rw [h₁, Category.assoc, Category.assoc, ← R.map_comp, h, R.map_comp, Category.assoc]

/-- The invertibility of a base change map followed by a map only depends on the source and
target objects up to isomorphism. -/
theorem isIso_comp_iff_of_iso {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] (R' : C₁ ⥤ C₂) (R : C₃ ⥤ C₄) (L : C₂ ⥤ C₄) (G : C₁ ⥤ C₃)
    {K K₁ : C₁} {K' K₁' : C₃} (e : K ≅ K₁) (e' : K' ≅ K₁')
    (bc : L.obj (R'.obj K) ⟶ R.obj (G.obj K)) (bc₁ : L.obj (R'.obj K₁) ⟶ R.obj (G.obj K₁))
    (φ : G.obj K ⟶ K') (φ₁ : G.obj K₁ ⟶ K₁')
    (hn : L.map (R'.map e.hom) ≫ bc₁ = bc ≫ R.map (G.map e.hom))
    (h : G.map e.hom ≫ φ₁ = φ ≫ e'.hom) :
    IsIso (bc ≫ R.map φ) ↔ IsIso (bc₁ ≫ R.map φ₁) := by
  rw [comp_of_iso R' R L G e e' bc bc₁ φ φ₁ hn h]
  constructor
  · intro _
    infer_instance
  · exact isIso_map_of_isIso_comp (𝟭 _) (L.map (R'.map e.inv)) (bc ≫ R.map φ) (R.map e'.hom)
      inferInstance inferInstance rfl

end Stacks.CategoryTheory.BaseChangeComp

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **The base change map attached to `φ : L(g')^*K ⟶ K'`**: the composite
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` of the base change map of Stacks 07A7 with `Rf'_*φ`. -/
def smallEtaleDerivedBaseChangeComp (w : g' ≫ f = f' ≫ g)
    (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    (smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) ⟶
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).obj K' :=
  smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K ≫
    (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map φ

/-- At `K' = L(g')^*K` and `φ = 𝟙` the composite is the base change map of Stacks 07A7. -/
theorem smallEtaleDerivedBaseChangeComp_id (w : g' ≫ f = f' ≫ g)
    (K : _) :
    smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K _ (𝟙 _) =
      smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K := by
  unfold smallEtaleDerivedBaseChangeComp
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The invertibility of the composite only depends on `K`, `K'` and `φ` up to
isomorphism**: for `e : K ≅ K₁`, `e' : K' ≅ K₁'` and `L(g')^*(e) ≫ φ₁ = φ ≫ e'`, the composite
attached to `φ` is invertible if and only if the one attached to `φ₁` is. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso (w : g' ≫ f = f' ≫ g) (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') (K₁ : _) (K₁' : _)
    (φ₁ : (smallEtaleDerivedModulePullback B S hS g').obj K₁ ⟶ K₁')
    (e : K ≅ K₁) (e' : K' ≅ K₁')
    (h : (smallEtaleDerivedModulePullback B S hS g').map e.hom ≫ φ₁ = φ ≫ e'.hom) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K' φ) ↔
      IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K₁ K₁' φ₁) :=
  Stacks.CategoryTheory.BaseChangeComp.isIso_comp_iff_of_iso
    (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f))
    (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f'))
    (smallEtaleDerivedModulePullback B S hS g) (smallEtaleDerivedModulePullback B S hS g') e e'
    (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K)
    (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K₁) φ φ₁
    (smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f g f' g' w e.hom) h

end Square

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (f'' : X'' ⟶ Y'') (g' : X' ⟶ X) (g'' : X'' ⟶ X') (g : Y' ⟶ Y) (h : Y'' ⟶ Y')

/-- **The composite is compatible with horizontal pasting.** For a second square
`g'' ≫ f' = f'' ≫ h`, the pullback along `h` of the composite attached to `φ`, followed by the
base change map of the second square at `K'`, is the composite for the outer rectangle attached
to `L(g'')^*φ`. -/
theorem smallEtaleDerivedBaseChangeComp_horizontal (w : g' ≫ f = f' ≫ g)
    (w' : g'' ≫ f' = f'' ≫ h)
    (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    (smallEtaleDerivedModulePullbackCompIso B S hS h g).inv.app
          ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) ≫
        (smallEtaleDerivedModulePullback B S hS h).map
          (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K' φ) ≫
        smallEtaleDerivedModuleBaseChangeMap B S hS f' h f'' g'' w' K' =
      smallEtaleDerivedBaseChangeComp B S hS f (h ≫ g) f'' (g'' ≫ g')
        (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g'' g h w w') K
        ((smallEtaleDerivedModulePullback B S hS g'').obj K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS g'').map φ) := by
  exact Stacks.CategoryTheory.BaseChangeComp.comp_horizontal
    (smallEtaleDerivedModulePullback B S hS h)
    (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f'))
    (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f''))
    (smallEtaleDerivedModulePullback B S hS g'') _
    (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K) _ _
    ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').app K) _ φ
    (smallEtaleDerivedBaseChangeMap_horizontal B S hS f f' f'' g' g'' g h w w' K)
    (smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f' h f'' g'' w' φ)

/-- **Pasting along a square with invertible base change map.** If the base change map of the
first square `g' ≫ f = f' ≫ g` at `K` is invertible, then the composite for the outer rectangle
attached to `ψ` is invertible as soon as the composite for the second square at `L(g')^*K`
attached to the corresponding map is. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_rectangle (w : g' ≫ f = f' ≫ g)
    (w' : g'' ≫ f' = f'' ≫ h) (K : _)
    (hBC : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K)) (K'' : _)
    (ψ : (smallEtaleDerivedModulePullback B S hS (g'' ≫ g')).obj K ⟶ K'')
    (hψ : IsIso (smallEtaleDerivedBaseChangeComp B S hS f' h f'' g'' w'
      ((smallEtaleDerivedModulePullback B S hS g').obj K) K''
      ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app K ≫ ψ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f (h ≫ g) f'' (g'' ≫ g')
      (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g'' g h w w') K K'' ψ) :=
  Stacks.CategoryTheory.BaseChangeComp.isIso_comp_of_isIso_horizontal
    (smallEtaleDerivedModulePullback B S hS h)
    (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f'))
    (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f''))
    (smallEtaleDerivedModulePullback B S hS g'') _
    (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K) _
    ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').app K) _ ψ
    (smallEtaleDerivedBaseChangeMap_horizontal B S hS f f' f'' g' g'' g h w w' K)
    (Iso.isIso_inv ((smallEtaleDerivedModulePullbackCompIso B S hS h g).app _)) hBC hψ

end Horizontal

section Local

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- **The invertibility of the composite is étale local on `Y'`.** If, for every affine étale
chart `V` of `Y'` with base change `X'_V ⟶ X'`, the composite for the outer rectangle attached to
the restriction of `φ` to `X'_V` is invertible, then so is the composite attached to `φ`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_chart (w : g' ≫ f = f' ≫ g)
    (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : ∀ V : SmallEtale B S hS Y'.1, IsAffineChart B S hS Y'.1 V →
      IsIso (smallEtaleDerivedBaseChangeComp B S hS f (chartToSpace B S hS Y' V ≫ g)
        (chartBaseChangeProjection B S hS f' V) (chartBaseChangeInclusion B S hS f' V ≫ g')
        (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' _ g' _ g _ w
          (isPullback_chartBaseChangeInclusion B S hS f' V).w) K
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' V)).obj K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeInclusion B S hS f' V) g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' V)).map
            φ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K' φ) := by
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Y'.1) _ fun V => ?_
  have sq := isPullback_chartBaseChangeInclusion B S hS f' V.1
  have hBC := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f'
    (chartToSpace B S hS Y' V.1) (chartBaseChangeProjection B S hS f' V.1)
    (chartBaseChangeInclusion B S hS f' V.1) sq (isEtale_chartToSpace B S hS Y' V.1)
    (relativelyRepresentable_chartToSpace B S hS Y' V.1) K'
  have hE := smallEtaleDerivedBaseChangeComp_horizontal B S hS f f'
    (chartBaseChangeProjection B S hS f' V.1) g' (chartBaseChangeInclusion B S hS f' V.1) g
    (chartToSpace B S hS Y' V.1) w sq.w K K' φ
  exact Stacks.CategoryTheory.BaseChangeComp.isIso_map_of_isIso_comp _ _ _ _
    (Iso.isIso_inv ((smallEtaleDerivedModulePullbackCompIso B S hS
      (chartToSpace B S hS Y' V.1) g).app _)) hBC hE (h V.1 V.2)

end Local

end AlgebraicGeometry.Space

end
