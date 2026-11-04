module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneChartMap

/-!
# Clause (1) of Stacks 0D2Z at a scheme point of `U(ψ)`, assembled from three squares

Clause (1) of [Stacks, Tag 0D2Z] on the algebraic space `U(ψ)` is descended from the identity
`w^*(ψ_P leg) ≫ χ_w = w^*(ψ leg)` at the scheme points `w : W ⟶ U(ψ)` (the hypothesis `hone` of
`…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points`), where
`χ_w = (chartTargetIso w) ∘ θ_w^a ∘ (chartSourceIso w)` is the chart map.  The identity is pasted
from three squares:

* the **source square** `w^*(ψ_P leg) ≫ chartSourceIso w = K ≫ (c_w^*ψ)^a`
  (`…InvertibleTwistingRestriction.clauseOneSourceShaped_square`), where `c_w^*ψ` is the inverse
  image along the section `c_w` of `ψ` of Tag 01NR;
* the **middle square** `c_w^*ψ ≫ θ_w = Ψ`, clause (1) of [Stacks, Tag 01O9] on the scheme `W`;
* the **target square** `K ≫ Ψ^a ≫ chartTargetIso w = w^*(ψ leg)`.

The legs and the chart map live over the site of `s.shrink`, the source square over the site of
`s`: the two are the same site by definition but not syntactically, and the kernel compares two
spellings of one morphism by unfolding both.  The paste is therefore proved at variables over two
sites `B₁ = B₂` (`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_squares`), with
the leaves of the two spellings heterogeneously equal, and each leaf is compared in its own
lemma by `subst`.

## Main results

* `…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_squares`: **the paste of the
  three squares, at variables, read over a second spelling of the site.**
* `…InvertibleTwistingRestriction.eqToHom_heq_of_site`,
  `…InvertibleTwistingRestriction.representedQuasicoherentSchemeEquivalence_functor_map_hom_heq`:
  the leaves of the two spellings.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

section Generic

/-- **The point identity of clause (1) of Stacks 0D2Z pasted from three squares, the source
square read over a second spelling of the site.**  Over the site `B₂`, let `p : Y ⟶ X` be a
morphism of algebraic spaces, `a : G ⟶ H` and `b : G ⟶ I` morphisms of modules on `X` (the two
legs) and `χ = J ≫ Θ ≫ T : p^*H ⟶ p^*I` (the chart map), with

* the source square `p^*a ≫ J = K ≫ Φ`, given over a site `B₁ = B₂` for `a = e ≫ i ≫ m` and
  heterogeneously equal leaves,
* the middle square `Φ ≫ Θ = Ψ`,
* the target square `K ≫ Ψ ≫ T = p^*b`.

Then `p^*a ≫ χ = p^*b`. -/
theorem modulePullback_map_comp_eq_of_squares {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {Y₁ X₁ : AlgebraicSpaces B₁ S₁ hS₁} {p₁ : Y₁ ⟶ X₁}
    {G₁ M₁ N₁ H₁ : Modules.{u, u} B₁ S₁ hS₁ X₁.1 X₁.2} {E₁ C₁ : Modules.{u, u} B₁ S₁ hS₁ Y₁.1 Y₁.2}
    {e₁ : G₁ ⟶ M₁} {i₁ : M₁ ⟶ N₁} {m₁ : N₁ ⟶ H₁}
    {J₁ : (modulePullback B₁ S₁ hS₁ p₁).obj H₁ ⟶ E₁}
    {K₁ : (modulePullback B₁ S₁ hS₁ p₁).obj G₁ ⟶ C₁} {Φ₁ : C₁ ⟶ E₁}
    (hsrc : (modulePullback B₁ S₁ hS₁ p₁).map (e₁ ≫ i₁ ≫ m₁) ≫ J₁ = K₁ ≫ Φ₁)
    {Y₂ X₂ : AlgebraicSpaces B₂ S₂ hS₂} (p₂ : Y₂ ⟶ X₂)
    {G₂ M₂ N₂ H₂ I₂ : Modules.{u, u} B₂ S₂ hS₂ X₂.1 X₂.2}
    {E₂ F₂ C₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2}
    (a₂ : G₂ ⟶ H₂) {e₂ : G₂ ⟶ M₂} {i₂ : M₂ ⟶ N₂} {m₂ : N₂ ⟶ H₂} (ha : a₂ = e₂ ≫ i₂ ≫ m₂)
    (b₂ : G₂ ⟶ I₂)
    (χ₂ : (modulePullback B₂ S₂ hS₂ p₂).obj H₂ ⟶ (modulePullback B₂ S₂ hS₂ p₂).obj I₂)
    {J₂ : (modulePullback B₂ S₂ hS₂ p₂).obj H₂ ⟶ E₂} {Θ₂ : E₂ ⟶ F₂}
    {T₂ : F₂ ⟶ (modulePullback B₂ S₂ hS₂ p₂).obj I₂} (hχ : χ₂ = J₂ ≫ Θ₂ ≫ T₂)
    {K₂ : (modulePullback B₂ S₂ hS₂ p₂).obj G₂ ⟶ C₂} {Φ₂ : C₂ ⟶ E₂} {Ψ₂ : C₂ ⟶ F₂}
    (hsch : Φ₂ ≫ Θ₂ = Ψ₂) (htgt : K₂ ≫ Ψ₂ ≫ T₂ = (modulePullback B₂ S₂ hS₂ p₂).map b₂)
    (hY : HEq Y₁ Y₂) (hX : HEq X₁ X₂) (hp : HEq p₁ p₂) (hG : HEq G₁ G₂) (hM : HEq M₁ M₂)
    (hN : HEq N₁ N₂) (hH : HEq H₁ H₂) (hE : HEq E₁ E₂) (hC : HEq C₁ C₂) (he : HEq e₁ e₂)
    (hi : HEq i₁ i₂) (hm : HEq m₁ m₂) (hJ : HEq J₁ J₂) (hK : HEq K₁ K₂) (hΦ : HEq Φ₁ Φ₂) :
    (modulePullback B₂ S₂ hS₂ p₂).map a₂ ≫ χ₂ = (modulePullback B₂ S₂ hS₂ p₂).map b₂ := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hY hX
  subst hp hG hM hN hH hE hC
  subst he hi hm hJ hK hΦ
  subst ha hχ
  rw [← Category.assoc, hsrc, Category.assoc, reassoc_of% hsch, htgt]

/-- **A transport of modules, read over a second spelling of the site**: `eqToHom` of an equality
of modules over `B₁` is heterogeneously equal to `eqToHom` of the corresponding equality over
`B₂ = B₁`, for heterogeneously equal space, source and target. -/
theorem eqToHom_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {Y₁ : AlgebraicSpaces B₁ S₁ hS₁} {X₁ Z₁ : Modules.{u, u} B₁ S₁ hS₁ Y₁.1 Y₁.2} (h₁ : X₁ = Z₁)
    {Y₂ : AlgebraicSpaces B₂ S₂ hS₂} {X₂ Z₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2} (h₂ : X₂ = Z₂)
    (hY : HEq Y₁ Y₂) (hX : HEq X₁ X₂) (hZ : HEq Z₁ Z₂) :
    HEq (eqToHom h₁) (eqToHom h₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hY hX hZ
  rfl

/-- **The module attached to a map of quasi-coherent modules, read over a second spelling of the
site** (Stacks 03DX (2)): `(θ^a).hom` over `B₁` is heterogeneously equal to `(θ^a).hom` over
`B₂ = B₁`, for heterogeneously equal `T`, source, target and `θ`. -/
theorem representedQuasicoherentSchemeEquivalence_functor_map_hom_heq {B₁ B₂ : BigFppfSite.{u}}
    (hB : B₁ = B₂) {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁}
    {hS₂ : B₂.Contains S₂} {T₁ : BigFppfOver B₁ S₁ hS₁} {T₂ : BigFppfOver B₂ S₂ hS₂}
    {M₁ N₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj T₁).ringCatSheaf).FullSubcategory}
    {M₂ N₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj T₂).ringCatSheaf).FullSubcategory}
    {θ₁ : M₁ ⟶ N₁} {θ₂ : M₂ ⟶ N₂}
    (hT : HEq T₁ T₂) (hM : HEq M₁ M₂) (hN : HEq N₁ N₂) (hθ : HEq θ₁ θ₂) :
    HEq ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ T₁).functor.map θ₁).hom
      ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ T₂).functor.map θ₂).hom := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hT hM hN hθ
  rfl

/-- **The target square of clause (1), read over a second spelling of the site**: an equation
`K ≫ Ψ ≫ T = p^*b` over `B₁` gives the same equation over `B₂ = B₁` for heterogeneously equal
leaves. -/
theorem comp_comp_eq_modulePullback_map_of_heq {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {Y₁ X₁ : AlgebraicSpaces B₁ S₁ hS₁} {p₁ : Y₁ ⟶ X₁} {G₁ I₁ : Modules.{u, u} B₁ S₁ hS₁ X₁.1 X₁.2}
    {C₁ F₁ : Modules.{u, u} B₁ S₁ hS₁ Y₁.1 Y₁.2} {K₁ : (modulePullback B₁ S₁ hS₁ p₁).obj G₁ ⟶ C₁}
    {Ψ₁ : C₁ ⟶ F₁} {T₁ : F₁ ⟶ (modulePullback B₁ S₁ hS₁ p₁).obj I₁} {b₁ : G₁ ⟶ I₁}
    (H : K₁ ≫ Ψ₁ ≫ T₁ = (modulePullback B₁ S₁ hS₁ p₁).map b₁)
    {Y₂ X₂ : AlgebraicSpaces B₂ S₂ hS₂} {p₂ : Y₂ ⟶ X₂} {G₂ I₂ : Modules.{u, u} B₂ S₂ hS₂ X₂.1 X₂.2}
    {C₂ F₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2} {K₂ : (modulePullback B₂ S₂ hS₂ p₂).obj G₂ ⟶ C₂}
    {Ψ₂ : C₂ ⟶ F₂} {T₂ : F₂ ⟶ (modulePullback B₂ S₂ hS₂ p₂).obj I₂} {b₂ : G₂ ⟶ I₂}
    (hY : HEq Y₁ Y₂) (hX : HEq X₁ X₂) (hp : HEq p₁ p₂) (hG : HEq G₁ G₂) (hI : HEq I₁ I₂)
    (hC : HEq C₁ C₂) (hF : HEq F₁ F₂) (hK : HEq K₁ K₂) (hΨ : HEq Ψ₁ Ψ₂) (hT : HEq T₁ T₂)
    (hb : HEq b₁ b₂) :
    K₂ ≫ Ψ₂ ≫ T₂ = (modulePullback B₂ S₂ hS₂ p₂).map b₂ := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hY hX
  subst hp hG hI hC hF
  subst hK hΨ hT hb
  exact H

/-- **A composite of four morphisms, read over a second spelling of the site**: over `B₁` and
over `B₂ = B₁`, `κ ≫ τ ≫ μ ≫ ρ` are heterogeneously equal for heterogeneously equal leaves. -/
theorem comp_comp_comp_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {Y₁ : AlgebraicSpaces B₁ S₁ hS₁} {U₁ V₁ Q₁ R₁ Z₁ : Modules.{u, u} B₁ S₁ hS₁ Y₁.1 Y₁.2}
    {κ₁ : U₁ ⟶ V₁} {τ₁ : V₁ ⟶ Q₁} {μ₁ : Q₁ ⟶ R₁} {ρ₁ : R₁ ⟶ Z₁}
    {Y₂ : AlgebraicSpaces B₂ S₂ hS₂} {U₂ V₂ Q₂ R₂ Z₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2}
    {κ₂ : U₂ ⟶ V₂} {τ₂ : V₂ ⟶ Q₂} {μ₂ : Q₂ ⟶ R₂} {ρ₂ : R₂ ⟶ Z₂}
    (hY : HEq Y₁ Y₂) (hU : HEq U₁ U₂) (hV : HEq V₁ V₂) (hQ : HEq Q₁ Q₂) (hR : HEq R₁ R₂)
    (hZ : HEq Z₁ Z₂) (hκ : HEq κ₁ κ₂) (hτ : HEq τ₁ τ₂) (hμ : HEq μ₁ μ₂) (hρ : HEq ρ₁ ρ₂) :
    HEq (κ₁ ≫ τ₁ ≫ μ₁ ≫ ρ₁) (κ₂ ≫ τ₂ ≫ μ₂ ≫ ρ₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hY
  subst hU hV hQ hR hZ
  subst hκ hτ hμ hρ
  rfl

/-- **A composite of two morphisms, read over a second spelling of the site.** -/
theorem comp_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {Y₁ : AlgebraicSpaces B₁ S₁ hS₁} {U₁ V₁ Z₁ : Modules.{u, u} B₁ S₁ hS₁ Y₁.1 Y₁.2}
    {e₁ : U₁ ⟶ V₁} {i₁ : V₁ ⟶ Z₁}
    {Y₂ : AlgebraicSpaces B₂ S₂ hS₂} {U₂ V₂ Z₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2}
    {e₂ : U₂ ⟶ V₂} {i₂ : V₂ ⟶ Z₂}
    (hY : HEq Y₁ Y₂) (hU : HEq U₁ U₂) (hV : HEq V₁ V₂) (hZ : HEq Z₁ Z₂) (he : HEq e₁ e₂)
    (hi : HEq i₁ i₂) :
    HEq (e₁ ≫ i₁) (e₂ ≫ i₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hY
  subst hU hV hZ
  subst he hi
  rfl

/-- **The inverse image of a morphism of modules, read over a second spelling of the site.** -/
theorem modulePullback_map_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {Y₁ Z₁ : AlgebraicSpaces B₁ S₁ hS₁} {a₁ : Y₁ ⟶ Z₁}
    {M₁ T₁ : Modules.{u, u} B₁ S₁ hS₁ Z₁.1 Z₁.2} {g₁ : M₁ ⟶ T₁}
    {Y₂ Z₂ : AlgebraicSpaces B₂ S₂ hS₂} {a₂ : Y₂ ⟶ Z₂}
    {M₂ T₂ : Modules.{u, u} B₂ S₂ hS₂ Z₂.1 Z₂.2} {g₂ : M₂ ⟶ T₂}
    (hY : HEq Y₁ Y₂) (hZ : HEq Z₁ Z₂) (ha : HEq a₁ a₂) (hM : HEq M₁ M₂) (hT : HEq T₁ T₂)
    (hg : HEq g₁ g₂) :
    HEq ((modulePullback B₁ S₁ hS₁ a₁).map g₁) ((modulePullback B₂ S₂ hS₂ a₂).map g₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hY hZ
  subst ha hM hT
  subst hg
  rfl

/-- **The comparison of two factorisations, read over a second spelling of the site**: the
underlying morphisms of `…InvertibleTwistingRestriction.modulePullbackCompTransportIso` over `B₁`
and over `B₂ = B₁` are heterogeneously equal for heterogeneously equal leaves. -/
theorem modulePullbackCompTransportIso_hom_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {A₁ Y₁ Z₁ P₁ : AlgebraicSpaces B₁ S₁ hS₁} {a₁ : A₁ ⟶ Y₁} {b₁ : Y₁ ⟶ P₁} {a₁' : A₁ ⟶ Z₁}
    {b₁' : Z₁ ⟶ P₁} {h₁ : a₁ ≫ b₁ = a₁' ≫ b₁'} {M₁ : Modules.{u, u} B₁ S₁ hS₁ P₁.1 P₁.2}
    {A₂ Y₂ Z₂ P₂ : AlgebraicSpaces B₂ S₂ hS₂} {a₂ : A₂ ⟶ Y₂} {b₂ : Y₂ ⟶ P₂} {a₂' : A₂ ⟶ Z₂}
    {b₂' : Z₂ ⟶ P₂} {h₂ : a₂ ≫ b₂ = a₂' ≫ b₂'} {M₂ : Modules.{u, u} B₂ S₂ hS₂ P₂.1 P₂.2}
    (hA : HEq A₁ A₂) (hY : HEq Y₁ Y₂) (hZ : HEq Z₁ Z₂) (hP : HEq P₁ P₂) (ha : HEq a₁ a₂)
    (hb : HEq b₁ b₂) (ha' : HEq a₁' a₂') (hb' : HEq b₁' b₂') (hM : HEq M₁ M₂) :
    HEq (modulePullbackCompTransportIso a₁ b₁ a₁' b₁' h₁ M₁).hom
      (modulePullbackCompTransportIso a₂ b₂ a₂' b₂' h₂ M₂).hom := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hA hY hZ hP
  subst ha hb ha' hb' hM
  rfl

/-- The module functor of a functor into a full subcategory takes a commutative triangle to a
commutative triangle of underlying morphisms. -/
theorem functor_map_hom_comp_map_hom {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty D} (F : C ⥤ P.FullSubcategory) {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z}
    {c : X ⟶ Z} (h : a ≫ b = c) : (F.map a).hom ≫ (F.map b).hom = (F.map c).hom := by
  rw [← h, F.map_comp]
  rfl

end Generic

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- **The source square of clause (1) at a scheme point `w` of `U(ψ)`, over the site of `s`**:
`…InvertibleTwistingRestriction.clauseOneSourceShaped_square` at `B = s.site`, with the base
change square of `ψ` of Stacks 084D
(`…modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom`), the source
identification `…InvertibleTwistingRestriction.chartSourceIso` of the chart map read through its
definition, the `ψ_P` leg `π_{U(ψ)}^*𝒜_d ≅ r^*(π^*𝒜_d) ⟶ r^*𝒪(d)` written as its three factors,
and the source identification of the square written as the composite of its four factors (the
value of `…InvertibleTwistingRestriction.clauseOnePointSourceIso`), each factor in the spelling
of the square. -/
theorem clauseOneSource_square_site :
    type_of% (clauseOneSourceShaped_square (B := s.site) (S := s.base) (hS := s.containsBase)
      (modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom s Px W
        (locusPoint w ≫ f.hom) d)
      (hab := pointHom_comp_invertibleSpaceMorphism w)
      (chartSourceIso Px w (locusOpen_locusPoint w) (d : ℤ)) rfl
      (pre₁ := eqToHom (congrArg (fun k => (modulePullback s.site s.base s.containsBase k).obj
        (s.shrink.algebra.piece (d : ℤ)))
        (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm))
      (pre₂ := ((modulePullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) _ rfl
      (A' := pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w)
      (hab' := pointHom_comp_invertibleSpaceMorphism w) _ rfl HEq.rfl HEq.rfl rfl rfl rfl rfl) :=
  clauseOneSourceShaped_square (B := s.site) (S := s.base) (hS := s.containsBase)
      (modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso_hom s Px W
        (locusPoint w ≫ f.hom) d)
      (hab := pointHom_comp_invertibleSpaceMorphism w)
      (chartSourceIso Px w (locusOpen_locusPoint w) (d : ℤ)) rfl
      (pre₁ := eqToHom (congrArg (fun k => (modulePullback s.site s.base s.containsBase k).obj
        (s.shrink.algebra.piece (d : ℤ)))
        (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm))
      (pre₂ := ((modulePullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) _ rfl
      (A' := pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w)
      (hab' := pointHom_comp_invertibleSpaceMorphism w) _ rfl HEq.rfl HEq.rfl rfl rfl rfl rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
