module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeTransitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ObstructionClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.LerayEdgeInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageCocycle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystem

/-!
# The obstruction class of [Stacks, Tag 0F07] on the pieces of an open-closed decomposition

Hypothesis (3) of the dévissage of [Stacks, Tag 0F06], for the property `P` of the proof of
[Stacks, Tag 0F07] (`Stacks.EtaleCohomology.ObstructionSurvives`): if `P(W)` holds and `W` is
the union of a closed subscheme `Z` and its quasi-compact open complement `O`, then `P(O)` or
`P(Z)` holds. The source's proof is followed. The restriction `F'` of the sheaf to `W` embeds into
`j_* J ⊕ i_* I`, with `J` and `I` injective sheaves of `ℤ/nℤ`-modules containing the restrictions
of `F'` to `O` and `Z`; by part (2) of [Stacks, Tag 0F03] the obstruction class stays nonzero in
one summand; base change along `BC(f, n, q)` and the injectivity of the Leray edge map carry it
to a nonzero class over that piece, which by part (3) of [Stacks, Tag 0F03] is not in the image
of the base change map there.

## Main results

* `Stacks.EtaleCohomology.pullbackCompHom_restriction` — the comparisons of inverse images along
  composites restrict along a cartesian square.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_pullbackClass_restriction` — the pullback map of
  the obstruction class restricts along a cartesian square.
* `Stacks.EtaleCohomology.mono_biprodLift_homEquiv` — a sheaf embeds into the direct images of
  embeddings of its restrictions to an open subscheme and a closed subscheme with complementary
  supports.
* `Stacks.EtaleCohomology.obstructionSurvives_of_stalk_ne_zero_of_baseChangeHolds` — `P` passes
  to a piece over which the image of the class under an injective embedding survives.
* `Stacks.EtaleCohomology.obstructionSurvives_open_or_closed` — hypothesis (3) of the dévissage.

## Implementation notes

The comparisons `f⁻¹ g⁻¹ ≅ (f ≫ g)⁻¹` are used through `Stacks.EtaleCohomology.pullbackCompHom`
and `Stacks.EtaleCohomology.pullbackCompInv`, whose types are written with iterated inverse
images: with the components of the natural isomorphism the intermediate objects of a composite
are written in two ways, and identifying them makes the kernel unfold the sheafification.

## References

* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F06](https://stacks.math.columbia.edu/tag/0F06)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The named comparison of inverse images along a composite of `Stacks.EtaleCohomology`'s
pasting file is the one of the colimit files. -/
theorem smallEtalePullbackAbCompIso'_eq_comp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtalePullbackAbCompIso' f g fg hfg = smallEtalePullbackAbComp' f g fg hfg := by
  rw [smallEtalePullbackAbComp'_eq_leftAdjointCompIso, smallEtalePullbackAbCompIso'_def]
  rfl

/-- **The base change map of a commutative square, transposed along the top edge.** For a
commutative square `h ≫ f' = e ≫ g` with common diagonal `P`, the inverse image along `h` of the
base change map `f'⁻¹ g_* ⟶ h_* e⁻¹`, followed by the counit of `h`, is the comparison
`h⁻¹ f'⁻¹ ≅ P⁻¹ ≅ e⁻¹ g⁻¹` followed by `e⁻¹` of the counit of `g`. -/
theorem smallEtalePullbackAb_map_baseChangeAb_comp_counit {S T X' Y : Scheme.{u}} (f' : X' ⟶ S)
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (P : Y ⟶ S) (hPh : P = h ≫ f')
    (hPe : P = e ≫ g) (M : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtalePullbackAb h).map ((smallEtaleBaseChangeAb f' g h e w).app M) ≫
        (smallEtaleAdjunctionAb h).counit.app ((smallEtalePullbackAb e).obj M) =
      (smallEtalePullbackAbComp' h f' P hPh).hom.app ((smallEtalePushforwardAb g).obj M) ≫
        (smallEtalePullbackAbComp' e g P hPe).inv.app ((smallEtalePushforwardAb g).obj M) ≫
          (smallEtalePullbackAb e).map ((smallEtaleAdjunctionAb g).counit.app M) := by
  rw [smallEtaleBaseChangeAb_eq_mateEquiv f' g h e w P hPh hPe]
  refine (mateEquiv_counit (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb h)
    (TwoSquare.mk _ _ _ _ ((smallEtalePullbackAbCompIso' h f' P hPh).hom ≫
      (smallEtalePullbackAbCompIso' e g P hPe).inv)) M).trans ?_
  rw [smallEtalePullbackAbCompIso'_eq_comp', smallEtalePullbackAbCompIso'_eq_comp']
  simp

section Restriction

/-- The comparison `f⁻¹ g⁻¹ X ⟶ (fg)⁻¹ X` of inverse images along a named composite, at a sheaf,
with its source written as an iterated inverse image. -/
def pullbackCompHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (M : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtalePullbackAb f).obj ((smallEtalePullbackAb g).obj M) ⟶
      (smallEtalePullbackAb fg).obj M :=
  (smallEtalePullbackAbComp' f g fg hfg).hom.app M

/-- The inverse of `Stacks.EtaleCohomology.pullbackCompHom`. -/
def pullbackCompInv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (M : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtalePullbackAb fg).obj M ⟶
      (smallEtalePullbackAb f).obj ((smallEtalePullbackAb g).obj M) :=
  (smallEtalePullbackAbComp' f g fg hfg).inv.app M

/-- `Stacks.EtaleCohomology.pullbackCompHom` followed by `Stacks.EtaleCohomology.pullbackCompInv`
is the identity. -/
@[reassoc (attr := simp)]
theorem pullbackCompHom_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (M : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    pullbackCompHom f g fg hfg M ≫ pullbackCompInv f g fg hfg M = 𝟙 _ :=
  (smallEtalePullbackAbComp' f g fg hfg).hom_inv_id_app M

/-- `Stacks.EtaleCohomology.pullbackCompInv` followed by `Stacks.EtaleCohomology.pullbackCompHom`
is the identity. -/
@[reassoc (attr := simp)]
theorem pullbackCompInv_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (M : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    pullbackCompInv f g fg hfg M ≫ pullbackCompHom f g fg hfg M = 𝟙 _ :=
  (smallEtalePullbackAbComp' f g fg hfg).inv_hom_id_app M

/-- The associativity pentagon, in the vocabulary of `Stacks.EtaleCohomology.pullbackCompHom`. -/
theorem pullbackCompHom_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh)
    (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    pullbackCompHom f g fg hfg ((smallEtalePullbackAb h).obj G) ≫ pullbackCompHom fg h fgh h₁ G =
      (smallEtalePullbackAb f).map (pullbackCompHom g h gh hgh G) ≫
        pullbackCompHom f gh fgh h₂ G :=
  smallEtalePullbackAbComp'_assoc_app f g h fg hfg gh hgh fgh h₁ h₂ G

/-- `Stacks.EtaleCohomology.pullbackCompHom` is natural in the sheaf. -/
@[reassoc]
theorem pullbackCompHom_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) {M N : Sheaf (smallEtaleTopology Z) Ab.{u + 1}} (φ : M ⟶ N) :
    (smallEtalePullbackAb f).map ((smallEtalePullbackAb g).map φ) ≫ pullbackCompHom f g fg hfg N =
      pullbackCompHom f g fg hfg M ≫ (smallEtalePullbackAb fg).map φ :=
  (smallEtalePullbackAbComp' f g fg hfg).hom.naturality φ

/-- `Stacks.EtaleCohomology.pullbackCompInv` is natural in the sheaf. -/
@[reassoc]
theorem pullbackCompInv_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) {M N : Sheaf (smallEtaleTopology Z) Ab.{u + 1}} (φ : M ⟶ N) :
    (smallEtalePullbackAb fg).map φ ≫ pullbackCompInv f g fg hfg N =
      pullbackCompInv f g fg hfg M ≫
        (smallEtalePullbackAb f).map ((smallEtalePullbackAb g).map φ) :=
  (smallEtalePullbackAbComp' f g fg hfg).inv.naturality φ

/-- The rearrangement behind `pullbackCompHom_restriction`, on morphisms of an abstract
category. -/
private theorem restriction_algebra' {C : Type*} [Category* C] {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ Z : C}
    (p₁ : X₁ ⟶ X₂) (p₂ : X₂ ⟶ X₃) (a₁ : X₁ ⟶ X₄) (a₂ : X₄ ⟶ X₃) (q₁ : X₅ ⟶ X₂) (q₁' : X₂ ⟶ X₅)
    (b₁ : X₅ ⟶ X₆) (b₂ : X₆ ⟶ X₃) (b₂' : X₃ ⟶ X₆) (c₁ : X₇ ⟶ X₆) (c₁' : X₆ ⟶ X₇)
    (c₂ : X₇ ⟶ X₈) (c₂' : X₈ ⟶ X₇) (c₃ : X₈ ⟶ X₃) (c₃' : X₃ ⟶ X₈) (k : X₇ ⟶ Z)
    (hq : q₁' ≫ q₁ = 𝟙 _) (hb : b₂ ≫ b₂' = 𝟙 _) (hb' : b₂' ≫ b₂ = 𝟙 _) (hc₁ : c₁' ≫ c₁ = 𝟙 _)
    (hc₂ : c₂ ≫ c₂' = 𝟙 _) (hc₃ : c₃ ≫ c₃' = 𝟙 _)
    (h₁ : a₁ ≫ a₂ = p₁ ≫ p₂) (h₂ : b₁ ≫ b₂ = q₁ ≫ p₂) (h₃ : c₁ ≫ b₂ = c₂ ≫ c₃) :
    a₁ ≫ a₂ ≫ c₃' ≫ c₂' ≫ k = p₁ ≫ q₁' ≫ b₁ ≫ c₁' ≫ k := by
  have e : b₂ ≫ c₃' ≫ c₂' = c₁' := by
    rw [← Category.id_comp (b₂ ≫ _), ← hc₁, Category.assoc, reassoc_of% h₃, reassoc_of% hc₃, hc₂,
      Category.comp_id]
  have e₃ : c₃' ≫ c₂' = b₂' ≫ c₁' := by
    rw [← Category.id_comp (c₃' ≫ c₂'), ← hb', Category.assoc, e]
  have e₂ : p₂ = q₁' ≫ b₁ ≫ b₂ := by rw [h₂, reassoc_of% hq]
  rw [reassoc_of% h₁, reassoc_of% e₃, e₂]
  simp only [Category.assoc, reassoc_of% hb]

variable {X_V T₀ Y₀ W Y' W' Y'' : Scheme.{u}} {h₀ : Y₀ ⟶ X_V} {e₀ : Y₀ ⟶ T₀}
  {π : W ⟶ T₀} {h' : Y' ⟶ X_V} {e' : Y' ⟶ W} {y : Y' ⟶ Y₀} (hy : y ≫ e₀ = e' ≫ π)
  (v : W' ⟶ W) (v' : Y'' ⟶ Y') (e'' : Y'' ⟶ W') (hv : v' ≫ e' = e'' ≫ v)

include hy hv in
/-- **The comparison of inverse images restricts along a cartesian square.** For `y ≫ e₀ = e' ≫ π`
and `v' ≫ e' = e'' ≫ v`, the identification of `(v' ≫ y)⁻¹ e₀⁻¹` with `e''⁻¹ (v ≫ π)⁻¹`, followed
by a map `k` out of `e''⁻¹ v⁻¹ π⁻¹`, is `v'⁻¹` of the identification of `y⁻¹ e₀⁻¹` with
`e'⁻¹ π⁻¹` followed by the comparison `v'⁻¹ e'⁻¹ ≅ e''⁻¹ v⁻¹` and `k`. -/
theorem pullbackCompHom_restriction (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1})
    {Z : Sheaf (smallEtaleTopology Y'') Ab.{u + 1}}
    (k : (smallEtalePullbackAb e'').obj ((smallEtalePullbackAb v).obj
      ((smallEtalePullbackAb π).obj F₀)) ⟶ Z) :
    pullbackCompHom v' y (v' ≫ y) rfl ((smallEtalePullbackAb e₀).obj F₀) ≫
        pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
          pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀)
            (by rw [Category.assoc, hy, ← Category.assoc, hv, Category.assoc]) F₀ ≫
        (smallEtalePullbackAb e'').map (pullbackCompInv v π (v ≫ π) rfl F₀) ≫ k =
      (smallEtalePullbackAb v').map (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀) ≫
        (smallEtalePullbackAb v').map (pullbackCompInv e' π (y ≫ e₀) hy F₀) ≫
        pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePullbackAb π).obj F₀) ≫
        pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePullbackAb π).obj F₀) ≫ k := by
  have hP₁ : (v' ≫ y) ≫ e₀ = v' ≫ (y ≫ e₀) := Category.assoc _ _ _
  have hP₂ : (v' ≫ y) ≫ e₀ = (v' ≫ e') ≫ π := by
    rw [Category.assoc, hy, Category.assoc]
  have hP₃ : (v' ≫ y) ≫ e₀ = e'' ≫ (v ≫ π) := by
    rw [hP₂, hv, Category.assoc]
  refine restriction_algebra' _ _ _ _ _ _ _ (pullbackCompHom (v' ≫ e') π ((v' ≫ y) ≫ e₀) hP₂ F₀)
    (pullbackCompInv (v' ≫ e') π ((v' ≫ y) ≫ e₀) hP₂ F₀)
    (pullbackCompHom e'' v (v' ≫ e') hv ((smallEtalePullbackAb π).obj F₀)) _
    ((smallEtalePullbackAb e'').map (pullbackCompHom v π (v ≫ π) rfl F₀)) _
    (pullbackCompHom e'' (v ≫ π) ((v' ≫ y) ≫ e₀) hP₃ F₀) _ k ?_ (by simp) (by simp) (by simp) ?_
    (by simp)
    (pullbackCompHom_assoc v' y e₀ (v' ≫ y) rfl (y ≫ e₀) rfl ((v' ≫ y) ≫ e₀) rfl hP₁ F₀)
    (pullbackCompHom_assoc v' e' π (v' ≫ e') rfl (y ≫ e₀) hy ((v' ≫ y) ≫ e₀) hP₂ hP₁ F₀)
    (pullbackCompHom_assoc e'' v π (v' ≫ e') hv (v ≫ π) rfl ((v' ≫ y) ≫ e₀) hP₂ hP₃ F₀)
  · rw [← Functor.map_comp, pullbackCompInv_hom, CategoryTheory.Functor.map_id]
  · rw [← Functor.map_comp, pullbackCompHom_inv, CategoryTheory.Functor.map_id]

include hy hv in
/-- `pullbackCompHom_restriction` with a map out of `v⁻¹ π⁻¹ F₀` and its adjoint. -/
theorem pullbackCompHom_restriction_adjoint (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1})
    {I : Sheaf (smallEtaleTopology W') Ab.{u + 1}}
    (k : (smallEtalePullbackAb v).obj ((smallEtalePullbackAb π).obj F₀) ⟶ I) :
    pullbackCompHom v' y (v' ≫ y) rfl ((smallEtalePullbackAb e₀).obj F₀) ≫
        pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
          pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀)
            (by rw [Category.assoc, hy, ← Category.assoc, hv, Category.assoc]) F₀ ≫
        (smallEtalePullbackAb e'').map (pullbackCompInv v π (v ≫ π) rfl F₀) ≫
          (smallEtalePullbackAb e'').map k =
      (smallEtalePullbackAb v').map (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀ ≫
          pullbackCompInv e' π (y ≫ e₀) hy F₀ ≫
          (smallEtalePullbackAb e').map ((smallEtaleAdjunctionAb v).homEquiv _ _ k)) ≫
        pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePushforwardAb v).obj I) ≫
        pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePushforwardAb v).obj I) ≫
        (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I) := by
  rw [pullbackCompHom_restriction hy v v' e'' hv F₀]
  have h₁ := pullbackCompHom_naturality_assoc v' e' (v' ≫ e') rfl
    ((smallEtaleAdjunctionAb v).homEquiv _ _ k)
    (pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePushforwardAb v).obj I) ≫
      (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I))
  have h₂ := pullbackCompInv_naturality_assoc e'' v (v' ≫ e') hv
    ((smallEtaleAdjunctionAb v).homEquiv _ _ k)
    ((smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I))
  have h₃ : (smallEtalePullbackAb e'').map ((smallEtalePullbackAb v).map
        ((smallEtaleAdjunctionAb v).homEquiv _ _ k)) ≫
      (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I) =
      (smallEtalePullbackAb e'').map k := by
    rw [← Functor.map_comp]
    exact congrArg _ (((smallEtaleAdjunctionAb v).homEquiv_counit _ _ _).symm.trans
      (Equiv.symm_apply_apply _ _))
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h₁, h₂, h₃]

private theorem compat_algebra {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    {L : X₀ ⟶ X₄} (i : X₀ ⟶ X₁) (m : X₁ ⟶ X₂) (B : X₂ ⟶ X₃) (R₁ : X₃ ⟶ X₄) (n : X₂ ⟶ X₅)
    (B' : X₅ ⟶ X₆) (R₂ : X₃ ⟶ X₆) (R₃ : X₄ ⟶ X₇) (R₄ : X₆ ⟶ X₇)
    (mn : X₁ ⟶ X₅) (hmn : mn = m ≫ n)
    (hp : L = i ≫ m ≫ B ≫ R₁) (hn : n ≫ B' = B ≫ R₂) (hsi : R₁ ≫ R₃ = R₂ ≫ R₄) :
    L ≫ R₃ = i ≫ mn ≫ B' ≫ R₄ := by
  rw [hp, hmn]
  simp only [Category.assoc]
  rw [hsi, reassoc_of% hn]

variable (r : ℕ) (h₀' : Y₀ ⟶ X_V) (hyh : h' ≫ 𝟙 X_V = y ≫ h₀')

include hy hv hyh in
/-- **The pullback class restricts along a cartesian square.** In the situation of
`pullbackCompHom_restriction_adjoint`, with `h' ≫ 𝟙 = y ≫ h₀`, the pullback map along
`v' ≫ y` of [Stacks, Tag 0F07] followed by `R^r` of `e''⁻¹ k` is `𝟙⁻¹` of the pullback map along
`y` followed by `R^r h'_* e'⁻¹` of the adjoint of `k`, followed by the base change map of the
square `v' ≫ h' = v' ≫ h'` and the transposed base change of `v_* I` along `e'`. -/
theorem higherBaseChangeMapAb_pullbackClass_restriction
    (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) {I : Sheaf (smallEtaleTopology W') Ab.{u + 1}}
    (k : (smallEtalePullbackAb v).obj ((smallEtalePullbackAb π).obj F₀) ⟶ I) :
    (higherBaseChangeMapAb (𝟙 X_V) h₀' (v' ≫ h') (v' ≫ y)
        (by rw [Category.assoc, hyh, Category.assoc]) r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
        (pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
          pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀)
            (by rw [Category.assoc, hy, ← Category.assoc, hv, Category.assoc]) F₀ ≫
          (smallEtalePullbackAb e'').map (pullbackCompInv v π (v ≫ π) rfl F₀) ≫
          (smallEtalePullbackAb e'').map k) =
    pullbackCompInv (𝟙 X_V) (𝟙 X_V) (𝟙 X_V) (by simp) _ ≫
      (smallEtalePullbackAb (𝟙 X_V)).map
        ((higherBaseChangeMapAb (𝟙 X_V) h₀' h' y hyh r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
          ((smallEtalePushforwardAb h').rightDerived r).map
            (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀ ≫ pullbackCompInv e' π (y ≫ e₀) hy F₀ ≫
              (smallEtalePullbackAb e').map ((smallEtaleAdjunctionAb v).homEquiv _ _ k))) ≫
      (higherBaseChangeMapAb (𝟙 X_V) h' (v' ≫ h') v' (by simp) r).app
        ((smallEtalePullbackAb e').obj ((smallEtalePushforwardAb v).obj I)) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
        (pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePushforwardAb v).obj I) ≫
          pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePushforwardAb v).obj I) ≫
          (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I)) := by
  have hp : (higherBaseChangeMapAb (𝟙 X_V) h₀' (v' ≫ h') (v' ≫ y)
        (by rw [Category.assoc, hyh, Category.assoc]) r).app ((smallEtalePullbackAb e₀).obj F₀) =
      pullbackCompInv (𝟙 X_V) (𝟙 X_V) (𝟙 X_V) (by simp) _ ≫
        (smallEtalePullbackAb (𝟙 X_V)).map
          ((higherBaseChangeMapAb (𝟙 X_V) h₀' h' y hyh r).app ((smallEtalePullbackAb e₀).obj F₀)) ≫
        (higherBaseChangeMapAb (𝟙 X_V) h' (v' ≫ h') v' (by simp) r).app
          ((smallEtalePullbackAb y).obj ((smallEtalePullbackAb e₀).obj F₀)) ≫
        ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
          (pullbackCompHom v' y (v' ≫ y) rfl ((smallEtalePullbackAb e₀).obj F₀)) :=
    higherBaseChangeMapAb_paste_app_named h₀' h' (v' ≫ h') (𝟙 X_V) (𝟙 X_V) y v' (𝟙 X_V)
      (by simp) (v' ≫ y) rfl _ hyh (by simp) r _
  have hn := (higherBaseChangeMapAb (𝟙 X_V) h' (v' ≫ h') v' (by simp) r).naturality
    (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀ ≫ pullbackCompInv e' π (y ≫ e₀) hy F₀ ≫
      (smallEtalePullbackAb e').map ((smallEtaleAdjunctionAb v).homEquiv _ _ k))
  simp only [Functor.comp_map] at hn
  have hsi : ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
        (pullbackCompHom v' y (v' ≫ y) rfl ((smallEtalePullbackAb e₀).obj F₀)) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
        (pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
          pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀)
            (by rw [Category.assoc, hy, ← Category.assoc, hv, Category.assoc]) F₀ ≫
          (smallEtalePullbackAb e'').map (pullbackCompInv v π (v ≫ π) rfl F₀) ≫
          (smallEtalePullbackAb e'').map k) =
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
        ((smallEtalePullbackAb v').map (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀ ≫
          pullbackCompInv e' π (y ≫ e₀) hy F₀ ≫
          (smallEtalePullbackAb e').map ((smallEtaleAdjunctionAb v).homEquiv _ _ k))) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
        (pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePushforwardAb v).obj I) ≫
          pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePushforwardAb v).obj I) ≫
          (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg _
      (pullbackCompHom_restriction_adjoint hy v v' e'' hv F₀ k)).trans (Functor.map_comp _ _ _))
  exact compat_algebra _ _ _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _) hp hn hsi

omit hy in
include hv in
/-- **The restriction comparison is injective.** The base change map of the square
`v' ≫ h' = v' ≫ h'` at `e'⁻¹ v_* I`, followed by the transposed base change of `v_* I` along `e'`,
is `𝟙⁻¹ R^r h'_*` of the base change map `e'⁻¹ v_* I ⟶ v'_* e''⁻¹ I` followed by the Leray edge
map of `v'` at `e''⁻¹ I`; so it is a monomorphism when the first is invertible and the second
injective. -/
theorem mono_higherBaseChangeMapAb_restrictionComparison
    {I : Sheaf (smallEtaleTopology W') Ab.{u + 1}}
    (hβ : IsIso ((smallEtaleBaseChangeAb e' v v' e'' hv).app I))
    (hL : Mono (lerayEdge h' (v' ≫ h') v' (by simp) r ((smallEtalePullbackAb e'').obj I))) :
    Mono ((higherBaseChangeMapAb (𝟙 X_V) h' (v' ≫ h') v' (by simp) r).app
        ((smallEtalePullbackAb e').obj ((smallEtalePushforwardAb v).obj I)) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived r).map
        (pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePushforwardAb v).obj I) ≫
          pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePushforwardAb v).obj I) ≫
          (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I))) := by
  have hm : (smallEtalePullbackAb v').map ((smallEtaleBaseChangeAb e' v v' e'' hv).app I) ≫
      (smallEtaleAdjunctionAb v').counit.app ((smallEtalePullbackAb e'').obj I) =
      pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePushforwardAb v).obj I) ≫
        pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePushforwardAb v).obj I) ≫
        (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I) :=
    smallEtalePullbackAb_map_baseChangeAb_comp_counit e' v v' e'' hv (v' ≫ e') rfl hv I
  have he : (smallEtaleAdjunctionAb v').homEquiv _ _
      (pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePushforwardAb v).obj I) ≫
        pullbackCompInv e'' v (v' ≫ e') hv ((smallEtalePushforwardAb v).obj I) ≫
        (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app I)) =
      (smallEtaleBaseChangeAb e' v v' e'' hv).app I := by
    rw [← hm]
    exact (congrArg _ ((smallEtaleAdjunctionAb v').homEquiv_counit _ _ _).symm).trans
      (Equiv.apply_symm_apply _ _)
  rw [higherBaseChangeMapAb_app_comp_map_eq, he]
  have : Mono (lerayEdge h' (v' ≫ h') v' (by simp) r
      ((smallEtalePullbackAb e'').obj ((𝟭 (Sheaf (smallEtaleTopology W') Ab.{u + 1})).obj I))) := hL
  infer_instance

end Restriction

/-- `θ ≫ 𝟙⁻¹ φ = φ ≫ ι⁻¹` for the comparison `θ : 𝟙⁻¹ ⟶ 𝟙⁻¹ 𝟙⁻¹` and `ι : 𝟙⁻¹ ≅ 𝟭`. -/
@[reassoc]
theorem pullbackCompInv_id_comp_map {X : Scheme.{u}} {M N : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb (𝟙 X)).obj M ⟶ N) :
    pullbackCompInv (𝟙 X) (𝟙 X) (𝟙 X) (by simp) M ≫ (smallEtalePullbackAb (𝟙 X)).map φ =
      φ ≫ (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app N := by
  rw [← cancel_mono ((smallEtalePullbackAbIdOf (𝟙 X) rfl).hom.app N), Category.assoc,
    Category.assoc, Iso.inv_hom_id_app]
  refine Eq.trans ?_ (Category.comp_id φ).symm
  have hn := (smallEtalePullbackAbIdOf (𝟙 X) rfl).hom.naturality φ
  simp only [Functor.id_map] at hn
  rw [hn]
  have : pullbackCompInv (𝟙 X) (𝟙 X) (𝟙 X) (by simp) M ≫
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).hom.app ((smallEtalePullbackAb (𝟙 X)).obj M) = 𝟙 _ := by
    rw [← smallEtalePullbackAbComp'_id_left_hom_app (𝟙 X) rfl (𝟙 X) (by simp) M]
    exact (smallEtalePullbackAbComp' (𝟙 X) (𝟙 X) (𝟙 X) (by simp)).inv_hom_id_app M
  rw [reassoc_of% this]

/-- **The property `P` of [Stacks, Tag 0F07] passes to a cartesian piece.** Let `P(W, π)` be
witnessed by the cartesian square `Y' = X_V ×_V W` with pullback map along `y`, let `v : W' ⟶ W`,
let `Y'' = Y' ×_W W'` be cartesian, and let `k : v⁻¹ π⁻¹ F₀ ⟶ I` embed into an injective sheaf
of `ℤ/nℤ`-modules. If the base change map `e'⁻¹ v_* I ⟶ v'_* e''⁻¹ I` is invertible, the Leray
edge map of `v'` at `e''⁻¹ I` is injective in degree `q + 1`, and the image of the obstruction
class `ξ` under the pullback map followed by `R^{q+1} h'_* e'⁻¹` of the adjoint `π⁻¹F₀ ⟶ v_* I` of
`k` is nonzero, then `P(W', v ≫ π)` holds. -/
theorem obstructionSurvives_of_stalk_ne_zero {V X_V T₀ Y₀ W Y' W' Y'' : Scheme.{u}}
    {fV : X_V ⟶ V} {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V} {e₀ : Y₀ ⟶ T₀}
    {F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}} {q : ℕ} {x : GeometricPoint X_V}
    {ξ : obstructionStalk h₀ e₀ F₀ (q + 1) x} {π : W ⟶ T₀} {h' : Y' ⟶ X_V} {e' : Y' ⟶ W}
    {g' : W ⟶ V} (hg : g' = π ≫ g₀) (sq' : IsPullback h' e' fV g') {y : Y' ⟶ Y₀}
    (hy : y ≫ e₀ = e' ≫ π) (hyh : h' ≫ 𝟙 X_V = y ≫ h₀) (v : W' ⟶ W) (v' : Y'' ⟶ Y')
    (e'' : Y'' ⟶ W') (sqv : IsPullback v' e'' e' v) (n : ℤ)
    (I : SheafOfModules.{u + 1} (etaleZModRingSheaf W' n)) [Injective I]
    (k : (smallEtalePullbackAb v).obj ((smallEtalePullbackAb π).obj F₀) ⟶
      (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I) (hk : Mono k)
    (hβ : IsIso ((smallEtaleBaseChangeAb e' v v' e'' sqv.w).app
      ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I)))
    (hL : Mono (lerayEdge h' (v' ≫ h') v' (by simp) (q + 1)
      ((smallEtalePullbackAb e'').obj ((SheafOfModules.toSheaf.{u + 1}
        (etaleZModRingSheaf W' n)).obj I))))
    (hne : (smallEtaleStalkAb x.hom).map
      ((higherBaseChangeMapAb (𝟙 X_V) h₀ h' y hyh (q + 1)).app
          ((smallEtalePullbackAb e₀).obj F₀) ≫
        ((smallEtalePushforwardAb h').rightDerived (q + 1)).map
          (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀ ≫ pullbackCompInv e' π (y ≫ e₀) hy F₀ ≫
            (smallEtalePullbackAb e').map ((smallEtaleAdjunctionAb v).homEquiv _ _ k))) ξ ≠ 0) :
    ObstructionSurvives fV g₀ h₀ e₀ F₀ (q + 1) x ξ W' (v ≫ π) := by
  have hyv : (v' ≫ y) ≫ e₀ = e'' ≫ (v ≫ π) := by
    rw [Category.assoc, hy, ← Category.assoc, sqv.w, Category.assoc]
  have hyhv : (v' ≫ h') ≫ 𝟙 X_V = (v' ≫ y) ≫ h₀ := by
    rw [Category.assoc, hyh, Category.assoc]
  have sqc : IsPullback (v' ≫ h') e'' fV (v ≫ g') := sqv.paste_horiz sq'
  refine ⟨Y'', v' ≫ h', e'', v ≫ g', by rw [hg, Category.assoc], sqc, v' ≫ y, hyv, hyhv,
    fun η hη => hne ?_⟩
  let k' := pullbackCompInv v π (v ≫ π) rfl F₀ ≫ k
  have hk' : Mono k' := by
    have : IsIso (pullbackCompInv v π (v ≫ π) rfl F₀) :=
      ⟨pullbackCompHom v π (v ≫ π) rfl F₀, by simp, by simp⟩
    exact mono_comp _ _
  have hz := higherBaseChangeMapAb_app_comp_map_eq_zero_of_injective n q fV (v ≫ g')
    (v' ≫ h') e'' sqc I k' hk'
  have := mono_higherBaseChangeMapAb_restrictionComparison v v' e'' sqv.w (q + 1) hβ hL
  have hres := (higherBaseChangeMapAb_pullbackClass_restriction hy v v' e'' sqv.w (q + 1) h₀ hyh
    F₀ k).trans (pullbackCompInv_id_comp_map_assoc _ _)
  have hinj := (AddCommGrpCat.mono_iff_injective ((smallEtaleStalkAb x.hom).map
    ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app _ ≫
      ((higherBaseChangeMapAb (𝟙 X_V) h' (v' ≫ h') v' (by simp) (q + 1)).app
        ((smallEtalePullbackAb e').obj ((smallEtalePushforwardAb v).obj
          ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I))) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived (q + 1)).map
        (pullbackCompHom v' e' (v' ≫ e') rfl ((smallEtalePushforwardAb v).obj
            ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I)) ≫
          pullbackCompInv e'' v (v' ≫ e') sqv.w ((smallEtalePushforwardAb v).obj
            ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I)) ≫
          (smallEtalePullbackAb e'').map ((smallEtaleAdjunctionAb v).counit.app
            ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I))))))).1
    inferInstance
  refine hinj ?_
  rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← hres]
  have hk'' : pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
        pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀) hyv F₀ ≫
        (smallEtalePullbackAb e'').map (pullbackCompInv v π (v ≫ π) rfl F₀) ≫
        (smallEtalePullbackAb e'').map k =
      (pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
        pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀) hyv F₀) ≫
        (smallEtalePullbackAb e'').map k' := by
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  rw [hk'']
  have hm : (higherBaseChangeMapAb (𝟙 X_V) h₀ (v' ≫ h') (v' ≫ y) hyhv (q + 1)).app
        ((smallEtalePullbackAb e₀).obj F₀) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived (q + 1)).map
        ((pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
          pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀) hyv F₀) ≫
          (smallEtalePullbackAb e'').map k') =
      ((higherBaseChangeMapAb (𝟙 X_V) h₀ (v' ≫ h') (v' ≫ y) hyhv (q + 1)).app
        ((smallEtalePullbackAb e₀).obj F₀) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived (q + 1)).map
        (pullbackCompHom (v' ≫ y) e₀ ((v' ≫ y) ≫ e₀) rfl F₀ ≫
          pullbackCompInv e'' (v ≫ π) ((v' ≫ y) ≫ e₀) hyv F₀)) ≫
      ((smallEtalePushforwardAb (v' ≫ h')).rightDerived (q + 1)).map
        ((smallEtalePullbackAb e'').map k') := by
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  rw [hm, (smallEtaleStalkAb x.hom).map_comp, ConcreteCategory.comp_apply]
  refine (congrArg _ hη.symm).trans ?_
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact (congrArg (fun z => (smallEtaleStalkAb x.hom).map z η) hz).trans (by simp)

/-- **The stalk of the adjoint of an injection is injective at a geometric point lifting to the
source.** For `v : T' ⟶ T`, `k : v⁻¹F ⟶ I` a monomorphism and a geometric point `x` of `T'`,
the stalk at `x ≫ v` of the adjoint `F ⟶ v_* I` of `k` is injective: through the identification
of the stalk at `x ≫ v` with the stalk at `x` of `v⁻¹`, it is followed by the stalk of the counit
to give the stalk of `k`. -/
theorem mono_smallEtaleStalkAb_map_homEquiv {T' T : Scheme.{u}} (v : T' ⟶ T) {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ T') {F : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    {I : Sheaf (smallEtaleTopology T') Ab.{u + 1}} (k : (smallEtalePullbackAb v).obj F ⟶ I)
    [Mono k] :
    Mono ((smallEtaleStalkAb (x ≫ v)).map ((smallEtaleAdjunctionAb v).homEquiv _ _ k)) := by
  have hn := (smallEtalePullbackStalkAbIso v x).inv.naturality
    ((smallEtaleAdjunctionAb v).homEquiv _ _ k)
  have hc : (smallEtaleStalkAb x).map ((smallEtalePullbackAb v).map
      ((smallEtaleAdjunctionAb v).homEquiv _ _ k)) ≫
      (smallEtaleStalkAb x).map ((smallEtaleAdjunctionAb v).counit.app I) =
      (smallEtaleStalkAb x).map k := by
    rw [← Functor.map_comp]
    exact congrArg _ (((smallEtaleAdjunctionAb v).homEquiv_counit _ _ _).symm.trans
      (Equiv.symm_apply_apply _ _))
  have hfac : (smallEtaleStalkAb (x ≫ v)).map ((smallEtaleAdjunctionAb v).homEquiv _ _ k) ≫
      ((smallEtalePullbackStalkAbIso v x).inv.app _ ≫
        (smallEtaleStalkAb x).map ((smallEtaleAdjunctionAb v).counit.app I)) =
      (smallEtalePullbackStalkAbIso v x).inv.app F ≫ (smallEtaleStalkAb x).map k := by
    rw [← Category.assoc, hn]
    simp only [Functor.comp_map, Category.assoc]
    rw [hc]
  exact mono_of_mono_fac hfac

section OpenClosed

variable {W : Scheme.{u}} (O : W.Opens) (J : W.IdealSheafData)
  (hO : (O : Set W) = (J.support : Set W)ᶜ)

/-- The geometric points of `W` through the algebraic closures of the residue fields of the open
subscheme `O` and of the closed subscheme cut out by `J`. -/
abbrev openClosedPointField : O.toScheme ⊕ J.subscheme → Type u
  | .inl y => AlgebraicClosure (O.toScheme.residueField y)
  | .inr z => AlgebraicClosure (J.subscheme.residueField z)

/-- Each `openClosedPointField O J t` is a field. -/
instance (t : O.toScheme ⊕ J.subscheme) : Field (openClosedPointField O J t) := by
  cases t <;> exact inferInstanceAs (Field (AlgebraicClosure _))

/-- Each `openClosedPointField O J t` is separably closed. -/
instance (t : O.toScheme ⊕ J.subscheme) : IsSepClosed (openClosedPointField O J t) := by
  cases t <;> exact inferInstanceAs (IsSepClosed (AlgebraicClosure _))

/-- The geometric points of `W` above the points of `O` and of the subscheme of `J`. -/
def openClosedPoint : ∀ t : O.toScheme ⊕ J.subscheme,
    Spec (.of (openClosedPointField O J t)) ⟶ W
  | .inl y => O.toScheme.algClosedPointHom y ≫ O.ι
  | .inr z => J.subscheme.algClosedPointHom z ≫ J.subschemeι

include hO in
/-- When `O` is the complement of the support of `J`, every point of `W` lies in the image of
some `openClosedPoint O J t`. -/
theorem iUnion_range_openClosedPoint :
    ⋃ t, Set.range (openClosedPoint O J t) = Set.univ := by
  refine Set.eq_univ_of_forall fun w => Set.mem_iUnion.2 ?_
  by_cases hw : w ∈ (O : Set W)
  · refine ⟨.inl ⟨w, hw⟩, Classical.arbitrary _, ?_⟩
    simp only [openClosedPoint, Scheme.Hom.comp_apply]
    rw [Scheme.algClosedPointHom_apply O.toScheme ⟨w, hw⟩]
    rfl
  · have : w ∈ (J.support : Set W) := by
      by_contra h
      exact hw (hO ▸ h)
    rw [← J.range_subschemeι] at this
    obtain ⟨z, rfl⟩ := this
    refine ⟨.inr z, Classical.arbitrary _, ?_⟩
    simp [openClosedPoint]

include hO in
/-- **An abelian sheaf embeds into the direct images of embeddings of its restrictions to an open
subscheme and to a closed subscheme with complementary supports.** This is the injectivity of
`F ⟶ j_*J ⊕ i_*I` in the proof of [Stacks, Tag 0F07], checked on stalks: a geometric point of
`W` lies over `O` or over the subscheme of `J`, and there the corresponding unit is injective. -/
theorem mono_biprodLift_homEquiv {F : Sheaf (smallEtaleTopology W) Ab.{u + 1}}
    {I₁ : Sheaf (smallEtaleTopology O.toScheme) Ab.{u + 1}}
    {I₂ : Sheaf (smallEtaleTopology J.subscheme) Ab.{u + 1}}
    (φ₁ : (smallEtalePullbackAb O.ι).obj F ⟶ I₁) [Mono φ₁]
    (φ₂ : (smallEtalePullbackAb J.subschemeι).obj F ⟶ I₂) [Mono φ₂] :
    Mono (biprod.lift ((smallEtaleAdjunctionAb O.ι).homEquiv _ _ φ₁)
      ((smallEtaleAdjunctionAb J.subschemeι).homEquiv _ _ φ₂)) := by
  refine mono_of_geometricStalkAb_family (openClosedPoint O J)
    (iUnion_range_openClosedPoint O J hO) _ fun t => ?_
  cases t with
  | inl y =>
    have : Mono ((smallEtaleStalkAb (openClosedPoint O J (.inl y))).map
        ((smallEtaleAdjunctionAb O.ι).homEquiv _ _ φ₁)) :=
      mono_smallEtaleStalkAb_map_homEquiv O.ι (O.toScheme.algClosedPointHom y) φ₁
    have h : (smallEtaleStalkAb (openClosedPoint O J (.inl y))).map (biprod.lift
        ((smallEtaleAdjunctionAb O.ι).homEquiv _ _ φ₁)
        ((smallEtaleAdjunctionAb J.subschemeι).homEquiv _ _ φ₂)) ≫
      (smallEtaleStalkAb (openClosedPoint O J (.inl y))).map biprod.fst =
      (smallEtaleStalkAb (openClosedPoint O J (.inl y))).map
          ((smallEtaleAdjunctionAb O.ι).homEquiv _ _ φ₁) := by
      rw [← Functor.map_comp, biprod.lift_fst]
    exact mono_of_mono_fac h
  | inr z =>
    have : Mono ((smallEtaleStalkAb (openClosedPoint O J (.inr z))).map
        ((smallEtaleAdjunctionAb J.subschemeι).homEquiv _ _ φ₂)) :=
      mono_smallEtaleStalkAb_map_homEquiv J.subschemeι (J.subscheme.algClosedPointHom z) φ₂
    have h : (smallEtaleStalkAb (openClosedPoint O J (.inr z))).map (biprod.lift
        ((smallEtaleAdjunctionAb O.ι).homEquiv _ _ φ₁)
        ((smallEtaleAdjunctionAb J.subschemeι).homEquiv _ _ φ₂)) ≫
      (smallEtaleStalkAb (openClosedPoint O J (.inr z))).map biprod.snd =
      (smallEtaleStalkAb (openClosedPoint O J (.inr z))).map
          ((smallEtaleAdjunctionAb J.subschemeι).homEquiv _ _ φ₂) := by
      rw [← Functor.map_comp, biprod.lift_snd]
    exact mono_of_mono_fac h

end OpenClosed

section Elements

variable {C : Type*} [Category* C] [Abelian C] (Φ : C ⥤ AddCommGrpCat.{u + 1})

/-- An element outside the image of `Φ t` maps to a nonzero element under `Φ q` when the map of
cokernels induced by a square `t ≫ q = p ≫ t'` is injective and `Φ` is exact. -/
theorem map_apply_ne_zero_of_mono_cokernelMap [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] {A B A' B' : C} (t : A ⟶ B) (t' : A' ⟶ B') (p : A ⟶ A')
    (q : B ⟶ B') (w : t ≫ q = p ≫ t') (hm : Mono (cokernel.map t t' p q w)) (ξ : Φ.obj B)
    (hξ : ∀ η, Φ.map t η ≠ ξ) : Φ.map q ξ ≠ 0 := by
  intro h0
  have hex : ((ShortComplex.mk t (cokernel.π t) (cokernel.condition t)).map Φ).Exact :=
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel t)).map Φ
  have hinj : Function.Injective (Φ.map (cokernel.map t t' p q w)) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hz : Φ.map (cokernel.π t) ξ = 0 := by
    refine hinj ?_
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.π_desc,
      Functor.map_comp, ConcreteCategory.comp_apply, h0, map_zero]
  obtain ⟨η, hη⟩ := (ShortComplex.ab_exact_iff _).1 hex ξ hz
  exact hξ η hη

/-- An element of `Φ X` whose image in `Φ (G₁ ⊞ G₂)` is nonzero has a nonzero image in one of the
two summands. -/
theorem map_fst_ne_zero_or_map_snd_ne_zero [Φ.Additive] {X G₁ G₂ : C} (m : X ⟶ G₁ ⊞ G₂)
    (ξ : Φ.obj X) (h : Φ.map m ξ ≠ 0) :
    Φ.map (m ≫ biprod.fst) ξ ≠ 0 ∨ Φ.map (m ≫ biprod.snd) ξ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  have e : m = m ≫ biprod.fst ≫ biprod.inl + m ≫ biprod.snd ≫ biprod.inr := by
    rw [← Preadditive.comp_add, biprod.total, Category.comp_id]
  have h₁ : Φ.map ((m ≫ biprod.fst) ≫ (biprod.inl : G₁ ⟶ G₁ ⊞ G₂)) ξ = 0 := by
    rw [Functor.map_comp, ConcreteCategory.comp_apply, hc.1, map_zero]
  have h₂ : Φ.map ((m ≫ biprod.snd) ≫ (biprod.inr : G₂ ⟶ G₁ ⊞ G₂)) ξ = 0 := by
    rw [Functor.map_comp, ConcreteCategory.comp_apply, hc.2, map_zero]
  rw [e, Functor.map_add, AddCommGrpCat.hom_add_apply, ← Category.assoc, ← Category.assoc, h₁, h₂,
    add_zero]

end Elements

/-- A biproduct of two abelian sheaves annihilated by `n` is annihilated by `n`. -/
theorem zsmul_biprod_eq_zero {X : Scheme.{u}} {A B : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (n : ℤ) (hA : ∀ (U : X.Etale) (x : A.obj.obj (Opposite.op U)), n • x = 0)
    (hB : ∀ (U : X.Etale) (x : B.obj.obj (Opposite.op U)), n • x = 0) :
    ∀ (U : X.Etale) (x : (A ⊞ B).obj.obj (Opposite.op U)), n • x = 0 := by
  intro U
  refine (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ n).1 ?_ (Opposite.op U)
  have hA' := (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff A n).2 (fun V => hA V.unop)
  have hB' := (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff B n).2 (fun V => hB V.unop)
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Preadditive.zsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id biprod.fst,
      ← Preadditive.comp_zsmul, hA', comp_zero]
  · rw [Preadditive.zsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id biprod.snd,
      ← Preadditive.comp_zsmul, hB', comp_zero]

/-- **The obstruction property passes to a piece of the base, given `BC(f, n, q)`.** In the
situation of `Stacks.EtaleCohomology.obstructionSurvives_of_stalk_ne_zero`, with `X_V = X ×_S V`,
`BC(f, n, q)` and `v : W' ⟶ W` quasi-compact and quasi-separated, the base change hypotheses
hold: `BC(f, n, q)` for the cartesian square `Y' ×_W W'` over `W' ⟶ W` gives the base change
isomorphism in degree zero and the vanishing of `R^a v'_* e''⁻¹ I` for `0 < a ≤ q`, hence the
injectivity of the Leray edge map. -/
theorem obstructionSurvives_of_stalk_ne_zero_of_baseChangeHolds
    {X S V X_V T₀ Y₀ W Y' W' : Scheme.{u}}
    {f : X ⟶ S} {n : ℤ} {q : ℕ} (hbc : BaseChangeHolds f n (q : ℤ)) {sv : V ⟶ S} {pv : X_V ⟶ X}
    {fV : X_V ⟶ V} (hpv : IsPullback pv fV f sv) {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V} {e₀ : Y₀ ⟶ T₀}
    {F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}} {x : GeometricPoint X_V}
    {ξ : obstructionStalk h₀ e₀ F₀ (q + 1) x} {π : W ⟶ T₀} {h' : Y' ⟶ X_V} {e' : Y' ⟶ W}
    {g' : W ⟶ V} (hg : g' = π ≫ g₀) (sq' : IsPullback h' e' fV g') {y : Y' ⟶ Y₀}
    (hy : y ≫ e₀ = e' ≫ π) (hyh : h' ≫ 𝟙 X_V = y ≫ h₀) (v : W' ⟶ W) [QuasiCompact v]
    [QuasiSeparated v] (I : SheafOfModules.{u + 1} (etaleZModRingSheaf W' n)) [Injective I]
    (k : (smallEtalePullbackAb v).obj ((smallEtalePullbackAb π).obj F₀) ⟶
      (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I) (hk : Mono k)
    (hne : (smallEtaleStalkAb x.hom).map
      ((higherBaseChangeMapAb (𝟙 X_V) h₀ h' y hyh (q + 1)).app
          ((smallEtalePullbackAb e₀).obj F₀) ≫
        ((smallEtalePushforwardAb h').rightDerived (q + 1)).map
          (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀ ≫ pullbackCompInv e' π (y ≫ e₀) hy F₀ ≫
            (smallEtalePullbackAb e').map ((smallEtaleAdjunctionAb v).homEquiv _ _ k))) ξ ≠ 0) :
    ObstructionSurvives fV g₀ h₀ e₀ F₀ (q + 1) x ξ W' (v ≫ π) := by
  have sqv : IsPullback (pullback.fst e' v) (pullback.snd e' v) e' v :=
    IsPullback.of_hasPullback _ _
  have hpY : IsPullback (h' ≫ pv) e' f (g' ≫ sv) := sq'.paste_horiz hpv
  have hJ : ∀ (U : W'.Etale) (z : ((SheafOfModules.toSheaf.{u + 1}
      (etaleZModRingSheaf W' n)).obj I).obj.obj (Opposite.op U)), n • z = 0 :=
    fun U z => zsmul_toSheaf_etaleZModRingSheaf_eq_zero W' n I U z
  have hBC : ∀ a : ℕ, a ≤ q → IsIso ((higherBaseChangeMapAb e' v (pullback.fst e' v)
      (pullback.snd e' v) sqv.w a).app
        ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I)) :=
    fun a ha => hbc (g' ≫ sv) (h' ≫ pv) e' hpY v (pullback.fst e' v) (pullback.snd e' v) sqv _
      hJ a (by exact_mod_cast ha)
  have hβ := (isIso_higherBaseChangeMapAb_zero_app_iff e' v (pullback.fst e' v)
    (pullback.snd e' v) sqv.w _).1 (hBC 0 (Nat.zero_le _))
  have hL := mono_lerayEdge h' (pullback.fst e' v ≫ h') (pullback.fst e' v) (by simp) (q + 1)
    ((smallEtalePullbackAb (pullback.snd e' v)).obj
      ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf W' n)).obj I)) fun a ha har => by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hz := isZero_higherBaseChangeSource_toSheaf_succ e' v (etaleZModRingSheaf W' n) I b
    have := hBC (b + 1) (by omega)
    exact hz.of_iso (asIso ((higherBaseChangeMapAb e' v (pullback.fst e' v)
      (pullback.snd e' v) sqv.w (b + 1)).app _)).symm
  exact obstructionSurvives_of_stalk_ne_zero hg sq' hy hyh v (pullback.fst e' v)
    (pullback.snd e' v) sqv n I k hk hβ hL hne

/-- The image of the obstruction class in `R^{q+1} h'_* e'⁻¹` of a map out of `π⁻¹ F₀`. -/
private theorem stalk_pullbackClass_map_eq {X_V T₀ Y₀ W Y' : Scheme.{u}} {h₀ : Y₀ ⟶ X_V}
    {e₀ : Y₀ ⟶ T₀} {F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}} {r : ℕ}
    {x : GeometricPoint X_V} (ξ : obstructionStalk h₀ e₀ F₀ r x) {π : W ⟶ T₀}
    {h' : Y' ⟶ X_V} {e' : Y' ⟶ W} {y : Y' ⟶ Y₀} (hy : y ≫ e₀ = e' ≫ π)
    (hyh : h' ≫ 𝟙 X_V = y ≫ h₀) {G : Sheaf (smallEtaleTopology W) Ab.{u + 1}}
    (a : (smallEtalePullbackAb π).obj F₀ ⟶ G) :
    (smallEtalePullbackAb e' ⋙ (smallEtalePushforwardAb h').rightDerived r ⋙
        smallEtaleStalkAb x.hom).map a ((smallEtaleStalkAb x.hom).map
      ((higherBaseChangeMapAb (𝟙 X_V) h₀ h' y hyh r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
        ((smallEtalePushforwardAb h').rightDerived r).map
          ((smallEtalePullbackAbComp' y e₀ (y ≫ e₀) rfl).hom.app F₀ ≫
            (smallEtalePullbackAbComp' e' π (y ≫ e₀) hy).inv.app F₀)) ξ) =
    (smallEtaleStalkAb x.hom).map
      ((higherBaseChangeMapAb (𝟙 X_V) h₀ h' y hyh r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
        ((smallEtalePushforwardAb h').rightDerived r).map
          (pullbackCompHom y e₀ (y ≫ e₀) rfl F₀ ≫ pullbackCompInv e' π (y ≫ e₀) hy F₀ ≫
            (smallEtalePullbackAb e').map a)) ξ := by
  rw [Functor.comp_map, Functor.comp_map, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp, Category.assoc]
  rfl

/-- **Hypothesis (3) of the dévissage of [Stacks, Tag 0F06] for the property `P` of
[Stacks, Tag 0F07].** Assume `BC(f, n, q)`, `X_V = X ×_S V` and `g₀ : T₀ ⟶ V` quasi-compact and
quasi-separated with `T₀` quasi-separated, let `F₀` on `T₀` be annihilated by `n`, and let `W`
over `T₀` be quasi-compact and quasi-separated with a closed subscheme `Z` and quasi-compact open
complement `O`. If `P(W)` holds for an obstruction class `ξ` in degree `q + 1`, then `P(O)` or
`P(Z)` holds.

This is the source's argument: the restriction `F'` of `F₀` to `W` embeds into
`j_* J ⊕ i_* I` with `J`, `I` injective sheaves of `ℤ/nℤ`-modules on `O` and `Z` containing the
restrictions of `F'` (`Stacks.EtaleCohomology.mono_biprodLift_homEquiv`); by part (2) of
[Stacks, Tag 0F03] the image of the class in one of the two summands is nonzero; and the Leray
edge map of the base change of `j` (resp. `i`) carries it to a nonzero class in
`R^{q+1}(h' ∘ j')_* e_O⁻¹ J` (resp. its analogue for `Z`), which by part (3) of
[Stacks, Tag 0F03] is not in the image of the base change map over `O` (resp. `Z`). -/
theorem obstructionSurvives_open_or_closed {X S : Scheme.{u}} {f : X ⟶ S} {n : ℤ} {q : ℕ}
    (hbc : BaseChangeHolds f n (q : ℤ)) {V X_V T₀ Y₀ : Scheme.{u}} {sv : V ⟶ S} {pv : X_V ⟶ X}
    {fV : X_V ⟶ V} (hpv : IsPullback pv fV f sv) {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V} {e₀ : Y₀ ⟶ T₀}
    [QuasiCompact g₀] [QuasiSeparated g₀] [QuasiSeparatedSpace T₀]
    {F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}}
    (hF : ∀ (U : T₀.Etale) (z : F₀.obj.obj (Opposite.op U)), n • z = 0)
    {x : GeometricPoint X_V} {ξ : obstructionStalk h₀ e₀ F₀ (q + 1) x}
    {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W] (π : W ⟶ T₀)
    (J : W.IdealSheafData) [CompactSpace J.subscheme] [QuasiSeparatedSpace J.subscheme]
    (O : W.Opens) (hO : (O : Set W) = (J.support : Set W)ᶜ)
    [CompactSpace O.toScheme] [QuasiSeparatedSpace O.toScheme]
    (hP : ObstructionSurvives fV g₀ h₀ e₀ F₀ (q + 1) x ξ W π) :
    ObstructionSurvives fV g₀ h₀ e₀ F₀ (q + 1) x ξ O.toScheme (O.ι ≫ π) ∨
      ObstructionSurvives fV g₀ h₀ e₀ F₀ (q + 1) x ξ J.subscheme (J.subschemeι ≫ π) := by
  obtain ⟨Y', h', e', g', hg, sq', y, hy, hyh, hne⟩ := hP
  have : QuasiCompact g' := hg ▸ inferInstance
  have : QuasiSeparated g' := hg ▸ inferInstance
  have hF' : ∀ (U : W.Etale) (z : ((smallEtalePullbackAb π).obj F₀).obj.obj (Opposite.op U)),
      n • z = 0 := fun U z =>
    zsmul_eq_zero_of_additive (smallEtalePullbackAb π) F₀ n (fun V z => hF V.unop z)
      (Opposite.op U) z
  have hFO : ∀ (U : O.toScheme.Etale) (z : ((smallEtalePullbackAb O.ι).obj
      ((smallEtalePullbackAb π).obj F₀)).obj.obj (Opposite.op U)), n • z = 0 := fun U z =>
    zsmul_eq_zero_of_additive (smallEtalePullbackAb O.ι) _ n (fun V z => hF' V.unop z)
      (Opposite.op U) z
  have hFZ : ∀ (U : J.subscheme.Etale) (z : ((smallEtalePullbackAb J.subschemeι).obj
      ((smallEtalePullbackAb π).obj F₀)).obj.obj (Opposite.op U)), n • z = 0 := fun U z =>
    zsmul_eq_zero_of_additive (smallEtalePullbackAb J.subschemeι) _ n (fun V z => hF' V.unop z)
      (Opposite.op U) z
  let kO := torsionEtaleInjectiveEmbedding _ hFO
  let kZ := torsionEtaleInjectiveEmbedding _ hFZ
  have hm := mono_biprodLift_homEquiv O J hO kO kZ
  have hG := zsmul_biprod_eq_zero n
    (fun U z => zsmul_eq_zero_of_additive (smallEtalePushforwardAb O.ι) _ n
      (fun V z => zsmul_toSheaf_etaleZModRingSheaf_eq_zero O.toScheme n
        (Injective.under (torsionEtaleModule _ hFO)) V.unop z) (Opposite.op U) z)
    (fun U z => zsmul_eq_zero_of_additive (smallEtalePushforwardAb J.subschemeι) _ n
      (fun V z => zsmul_toSheaf_etaleZModRingSheaf_eq_zero J.subscheme n
        (Injective.under (torsionEtaleModule _ hFZ)) V.unop z) (Opposite.op U) z)
  have hcok := mono_cokernelMap_higherBaseChangeMapAb_app_of_annihilated f n q sv pv fV g' h' e'
    hbc hpv sq' _ hm hF' (fun U z => hG U z)
  have h1 := map_apply_ne_zero_of_mono_cokernelMap (smallEtaleStalkAb x.hom) _ _ _ _ _ hcok _ hne
  have : (smallEtaleStalkAb x.hom).Additive := Functor.additive_of_preserves_binary_products _
  have : ((smallEtalePushforwardAb h').rightDerived (q + 1)).Additive :=
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (smallEtalePushforwardAb h')).additive (q + 1)
  have : ((smallEtalePushforwardAb h').rightDerived (q + 1) ⋙ smallEtaleStalkAb x.hom).Additive :=
    inferInstance
  have : (smallEtalePullbackAb e' ⋙ (smallEtalePushforwardAb h').rightDerived (q + 1) ⋙
    smallEtaleStalkAb x.hom).Additive := inferInstance
  have h2 := map_fst_ne_zero_or_map_snd_ne_zero
    (smallEtalePullbackAb e' ⋙ (smallEtalePushforwardAb h').rightDerived (q + 1) ⋙
      smallEtaleStalkAb x.hom) _ _ h1
  rw [biprod.lift_fst, biprod.lift_snd, stalk_pullbackClass_map_eq,
    stalk_pullbackClass_map_eq] at h2
  rcases h2 with h2 | h2
  · exact Or.inl (obstructionSurvives_of_stalk_ne_zero_of_baseChangeHolds hbc hpv hg sq' hy hyh
      O.ι _ kO inferInstance h2)
  · exact Or.inr (obstructionSurvives_of_stalk_ne_zero_of_baseChangeHolds hbc hpv hg sq' hy hyh
      J.subschemeι _ kZ inferInstance h2)

end Stacks.EtaleCohomology
