module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OpenImmersionCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative diagonal of an unramified morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. [Stacks Project, Tag 05W1]
has two parts:

1. if `f` is unramified then its relative diagonal `X ⟶ X ×_Y X` is an open immersion;
2. if `f` is locally of finite type and its relative diagonal is an open immersion then `f` is
   unramified.

Both are proved here. Part (1) supplies the hypothesis `h05W1` of the two equivalences of
`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria`, which are conditions (1) ⟺ (2)
and (1) ⟺ (4) of [Stacks Project, Tag 05W6].

## Main definitions

There are no new definitions.

## Main results

* `CategoryTheory.Limits.isPullback_kernelPair_diagonal` is the categorical heart of both
  parts: for `p : A ⟶ X ×_Y V` with components `α` and `β`, the comparison from a kernel pair
  of `p` to a kernel pair of `β` is a base change of the relative diagonal of `f`.
* `AlgebraicGeometry.Space.monomorphisms_diagonal`,
  `AlgebraicGeometry.Space.locallyOfFiniteType_diagonal`,
  `AlgebraicGeometry.Space.isSeparated_diagonal` and
  `AlgebraicGeometry.Space.locallyQuasiFinite_diagonal` are the five conclusions of
  [Stacks Project, Tag 03HK]: the relative diagonal is representable, locally of finite type, a
  monomorphism, separated and locally quasi-finite.
* `AlgebraicGeometry.Space.presheaf_etale_diagonal_of_isUnramified`: every represented base
  change of the relative diagonal of an unramified morphism is an étale morphism of schemes.
* `AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified` is part (1) of
  [Stacks Project, Tag 05W1].
* `AlgebraicGeometry.Space.isUnramified_of_isOpenImmersion_diagonal` is part (2).
* `AlgebraicGeometry.Space.map_pullbackDiagonal_of_presheaf_pullbackDiagonal`: for a
  representable morphism of presheaves whose relative diagonal has a relatively representable
  property `P`, the morphism of schemes underlying each canonical represented base change has
  `P` on its own diagonal.

## Implementation notes

The source proves part (1) by exhibiting the relative diagonal as a representable étale
monomorphism and quoting [Stacks Project, Tag 025G]; its diagram is the one a reader has
questioned (comment #11750 on the tag), and the route taken here is a different, checkable
arrangement of the same three inputs.

*Representability and the monomorphism condition* are [Stacks Project, Tag 03HK] and come from
the absolute diagonal: the relative diagonal of `f` is a base change of `diag X` along
`X ×_Y X ⟶ X ⨯ X` (`AlgebraicGeometry.isPullback_pullbackDiagonal_diag`), and the absolute
diagonal of an algebraic space is representable by definition and a monomorphism after every
represented base change by part (2) of [Stacks Project, Tag 02X4]
(`AlgebraicGeometry.Space.monomorphisms_diag_of_representable`). The other three conclusions of
Tag 03HK transport from parts (1), (3) and (4) of the same tag in exactly the same way, so the
whole of Tag 03HK is recorded here and needs no new argument.

*Étaleness of every represented base change* is where unramifiedness enters. Étaleness is fppf
local on the base, so by `AlgebraicGeometry.Space.presheaf_of_etale_cover` it is enough to
refine each represented base change along a surjective étale cover. Choose a surjective étale
chart `ψ : h_V ⟶ Y`, a surjective étale atlas `q₀ : h_{U₀} ⟶ X`, and let
`U = U₀ ×_Y V`; then `q : h_U ⟶ X` and `m : U ⟶ V` form a commuting square of étale charts, so
`m` is an unramified morphism of schemes, and `p : h_U ⟶ X ×_Y h_V` is a base change of `q₀`
and hence surjective and étale after every represented base change. Given
`g : h_a ⟶ X ×_Y X`, pulling `ψ` back along the common image in `Y` and then `p` back along
each of the two components in turn produces a surjective étale `c : a₂ ⟶ a` together with two
lifts `a₂ ⟶ U` whose images in `V` *agree*, that is a morphism `a₂ ⟶ U ×_V U`. By
`CategoryTheory.Limits.isPullback_kernelPair_diagonal` the comparison `k` from the kernel pair
of `p` to `U ×_V U` is a base change of the relative diagonal, so the refined base change is a
base change of `k`; and `k` is étale because `k` followed by the first projection of `U ×_V U`
is the étale projection of the kernel pair of `p`, while that first projection is a base change
of the unramified `m`, so `AlgebraicGeometry.Etale.of_comp` applies. This last cancellation —
`g ≫ h` étale and `g` unramified force `h` étale — is what the chart diagram of the source
replaces.

*Conclusion.* A morphism of schemes which is étale and universally injective is an open
immersion, [Stacks Project, Tag 025G], available as
`AlgebraicGeometry.tfae_isOpenImmersion`; a monomorphism of schemes is universally injective.

Part (2) uses the same kernel-pair square in the opposite direction; see the docstring of
`AlgebraicGeometry.Space.isUnramified_of_isOpenImmersion_diagonal`. It needs no algebraicity
hypothesis at all, because the representability it uses is that of the étale charts and of the
cancellation property of [Stacks Project, Tag 05L9].

Neither part uses [Stacks Project, Tag 03MJ], the equivalence of the represented-base-change
form of a property with its étale-chart form, which this development does not have: part (1)
produces the represented-base-change form directly from the chart condition, and part (2)
consumes it directly.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 05L9](https://stacks.math.columbia.edu/tag/05L9)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

/-- **The kernel pair of a relative chart is a base change of the relative diagonal.**

Let `f : X ⟶ Y` and `ψ : V ⟶ Y`, and let `p : A ⟶ X ×_Y V` be a morphism with components
`α : A ⟶ X` and `β : A ⟶ V`. Let `r₁, r₂ : R ⟶ A` be a kernel pair of `p` and let
`w₁, w₂ : W ⟶ A` be a kernel pair of `β`, so that the pair `r₁, r₂` factors through `w₁, w₂`
by a morphism `j : R ⟶ W`. Then `j` is the base change of the relative diagonal of `f` along
the morphism `θ : W ⟶ X ×_Y X` with components `w₁ ≫ α` and `w₂ ≫ α`.

In words: inside `W = A ×_V A` the locus where the two `X`-components agree is exactly
`R = A ×_{X ×_Y V} A`, because agreeing in `X ×_Y V` is agreeing in `X` and in `V` at once,
and the `V`-components already agree on `W`. -/
theorem isPullback_kernelPair_diagonal {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y V A R W : C} {f : X ⟶ Y} {ψ : V ⟶ Y} {p : A ⟶ pullback f ψ} {α : A ⟶ X} {β : A ⟶ V}
    (hα : p ≫ pullback.fst f ψ = α) (hβ : p ≫ pullback.snd f ψ = β)
    {r₁ r₂ : R ⟶ A} (hR : IsPullback r₁ r₂ p p)
    {w₁ w₂ : W ⟶ A} (hW : IsPullback w₁ w₂ β β)
    {j : R ⟶ W} (hj₁ : j ≫ w₁ = r₁) (hj₂ : j ≫ w₂ = r₂) {θ : W ⟶ pullback f f}
    (hθ₁ : θ ≫ pullback.fst f f = w₁ ≫ α) (hθ₂ : θ ≫ pullback.snd f f = w₂ ≫ α) :
    IsPullback (r₁ ≫ α) j (pullback.diagonal f) θ := by
  have hα' : ∀ {Z : C} (k l : Z ⟶ A), k ≫ p = l ≫ p → k ≫ α = l ≫ α := fun k l h => by
    rw [← hα, ← Category.assoc, h, Category.assoc]
  have hr : r₁ ≫ α = r₂ ≫ α := hα' r₁ r₂ hR.w
  have hcomm : CommSq (r₁ ≫ α) j (pullback.diagonal f) θ := by
    refine ⟨pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, hθ₁,
        ← Category.assoc, hj₁]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, hθ₂,
        ← Category.assoc, hj₂]
      exact hr
  have key : ∀ (c : PullbackCone (pullback.diagonal f) θ),
      c.fst = c.snd ≫ w₁ ≫ α ∧ c.fst = c.snd ≫ w₂ ≫ α := by
    intro c
    have h₁ := c.condition =≫ pullback.fst f f
    have h₂ := c.condition =≫ pullback.snd f f
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, hθ₁] at h₁
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, hθ₂] at h₂
    exact ⟨h₁, h₂⟩
  have hcond : ∀ (c : PullbackCone (pullback.diagonal f) θ),
      (c.snd ≫ w₁) ≫ p = (c.snd ≫ w₂) ≫ p := by
    intro c
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, hα]
      rw [← (key c).1, ← (key c).2]
    · simp only [Category.assoc, hβ]
      rw [hW.w]
  refine IsPullback.of_isLimit' hcomm
    (PullbackCone.IsLimit.mk hcomm.w (fun c => hR.lift _ _ (hcond c)) (fun c => ?_)
      (fun c => ?_) (fun c m _ hm => ?_))
  · rw [← Category.assoc, hR.lift_fst, Category.assoc, ← (key c).1]
  · refine hW.hom_ext ?_ ?_
    · rw [Category.assoc, hj₁, hR.lift_fst]
    · rw [Category.assoc, hj₂, hR.lift_snd]
  · refine hR.hom_ext ?_ ?_
    · rw [hR.lift_fst, ← hj₁, ← Category.assoc, hm]
    · rw [hR.lift_snd, ← hj₂, ← Category.assoc, hm]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Stacks 03HK: the relative diagonal is a representable monomorphism -/

/-- **Stacks 03HK, representability and the monomorphism condition.** The relative diagonal of
a morphism of algebraic spaces over `S` is representable and a monomorphism after every
represented base change.

It is the base change of the absolute diagonal of the source along `X ×_Y X ⟶ X ⨯ X`
(`AlgebraicGeometry.isPullback_pullbackDiagonal_diag`), and for the absolute diagonal this is
part (2) of [Stacks Project, Tag 02X4]. Algebraicity of the target is not needed. -/
@[stacks 03HK "representable and a monomorphism"]
theorem monomorphisms_diagonal (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f) :=
  presheaf_of_isPullback B S hS (isPullback_pullbackDiagonal_diag B S hS f)
    (monomorphisms_diag_of_representable B S hS hX.diagonal_representable)

/-- **Stacks 03HK, local finite type.** Every represented base change of the relative diagonal
of a morphism of algebraic spaces over `S` is a morphism of schemes which is locally of finite
type. This is part (1) of [Stacks Project, Tag 02X4] transported along
`AlgebraicGeometry.isPullback_pullbackDiagonal_diag`. -/
@[stacks 03HK "locally of finite type"]
theorem locallyOfFiniteType_diagonal (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f) :=
  presheaf_of_isPullback B S hS (isPullback_pullbackDiagonal_diag B S hS f)
    (presheaf_locallyOfFiniteType_diag B S hS X hX)

/-- **Stacks 03HK, separatedness.** Every represented base change of the relative diagonal of a
morphism of algebraic spaces over `S` is a separated morphism of schemes. This is part (3) of
[Stacks Project, Tag 02X4] transported along
`AlgebraicGeometry.isPullback_pullbackDiagonal_diag`. -/
@[stacks 03HK "separated"]
theorem isSeparated_diagonal (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f) :=
  presheaf_of_isPullback B S hS (isPullback_pullbackDiagonal_diag B S hS f)
    (isSeparated_diag_of_representable B S hS hX.diagonal_representable)

/-- **Stacks 03HK, local quasi-finiteness.** Every represented base change of the relative
diagonal of a morphism of algebraic spaces over `S` is a morphism of schemes which is locally
of finite type and locally quasi-finite. This is part (4) of [Stacks Project, Tag 02X4]
transported along `AlgebraicGeometry.isPullback_pullbackDiagonal_diag`. -/
@[stacks 03HK "locally quasi-finite"]
theorem locallyQuasiFinite_diagonal (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f) :=
  presheaf_of_isPullback B S hS (isPullback_pullbackDiagonal_diag B S hS f)
    (presheaf_locallyQuasiFinite_diag B S hS X hX)

/-! ### Étaleness of the base changes of the diagonal of an unramified morphism -/

/-- **An étale chart of `X` over an étale chart of `Y`.** There are a surjective étale chart
`ψ : h_V ⟶ Y`, an object `U` of the site, a morphism `m : U ⟶ V` and a morphism
`p : h_U ⟶ X ×_Y h_V` such that `p` is surjective and étale after every represented base
change, its first component `p ≫ pullback.fst f ψ` is an étale chart of `X`, and its second
component is `yoneda.map m`.

Take a surjective étale atlas `ψ` of `Y` and a surjective étale atlas `q₀ : h_{U₀} ⟶ X`, and
let `U` be the object representing the base change of `ψ` along `q₀ ≫ f`. Then `p` is the base
change of `q₀` along the base change `X ×_Y h_V ⟶ X` of `ψ`, which is where its surjectivity
and étaleness come from. -/
private theorem exists_etale_chart_over_target
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    ∃ (V U : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ Y) (m : U ⟶ V)
      (p : yoneda.obj U ⟶ pullback f ψ),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ψ ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ψ ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (p ≫ pullback.fst f ψ) ∧
      p ≫ pullback.snd f ψ = yoneda.map m ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  obtain ⟨V, ψ, hψs, hψe⟩ := hY.exists_atlas
  obtain ⟨U₀, q₀, hq₀s, hq₀e⟩ := hX.exists_atlas
  have hrep : yoneda.relativelyRepresentable ψ := hψe.rep
  have sqU : IsPullback (yoneda.map (hrep.fst' (q₀ ≫ f)))
      (yoneda.map (hrep.snd (q₀ ≫ f))) ψ (q₀ ≫ f) := hrep.isPullback' (q₀ ≫ f)
  have hc : (yoneda.map (hrep.snd (q₀ ≫ f)) ≫ q₀) ≫ f
      = yoneda.map (hrep.fst' (q₀ ≫ f)) ≫ ψ := by
    rw [Category.assoc]; exact sqU.w.symm
  have hfst : pullback.lift _ _ hc ≫ pullback.fst f ψ
      = yoneda.map (hrep.snd (q₀ ≫ f)) ≫ q₀ := pullback.lift_fst _ _ hc
  have sqP : IsPullback (pullback.lift _ _ hc) (yoneda.map (hrep.snd (q₀ ≫ f)))
      (pullback.fst f ψ) q₀ := by
    refine IsPullback.of_right ?_ hfst (IsPullback.of_hasPullback f ψ).flip
    rw [pullback.lift_snd _ _ hc]
    exact sqU
  refine ⟨V, hrep.pullback (q₀ ≫ f), ψ, hrep.fst' (q₀ ≫ f), pullback.lift _ _ hc,
    hψs, hψe, ?_, pullback.lift_snd _ _ hc,
    presheaf_of_isPullback B S hS sqP.flip hq₀s, presheaf_of_isPullback B S hS sqP.flip hq₀e⟩
  rw [hfst]
  exact etale_comp_of_scheme B S hS _ q₀ (hψe.property (q₀ ≫ f) _ _ sqU) hq₀e

/-- A morphism of schemes which is a monomorphism and étale is an open immersion. -/
private theorem isOpenImmersion_of_mono_of_etale {M N : Scheme.{u}} (g : M ⟶ N) [Mono g]
    [AlgebraicGeometry.Etale g] : AlgebraicGeometry.IsOpenImmersion g := by
  have : AlgebraicGeometry.UniversallyInjective g ∧ AlgebraicGeometry.Etale g :=
    ⟨inferInstance, inferInstance⟩
  exact ((AlgebraicGeometry.tfae_isOpenImmersion g).out 2 1).mp this

/-- A functor carries the diagonal of `g` to the diagonal of `F.map g`, up to the comparison
isomorphism of the fibre product. -/
private theorem map_diagonal_comp_isoPullback_hom {C D : Type*} [Category C] [Category D]
    [HasPullbacks C] [HasPullbacks D] (F : C ⥤ D) {M N : C} (g : M ⟶ N)
    (hs : IsPullback (F.map (pullback.fst g g)) (F.map (pullback.snd g g)) (F.map g) (F.map g)) :
    F.map (pullback.diagonal g) ≫ hs.isoPullback.hom = pullback.diagonal (F.map g) := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [Category.assoc, hs.isoPullback_hom_fst, hs.isoPullback_hom_snd,
      ← Functor.map_comp, pullback.diagonal_fst, pullback.diagonal_snd,
      CategoryTheory.Functor.map_id]

/-- A kernel pair of `p : h_U ⟶ X ×_Y h_V` over `h_V`-component `yoneda.map m` maps to `U ×_V U`
by a base change of the relative diagonal of `f`. -/
private theorem exists_isPullback_kernelPair_diagonal_yoneda
    {V U R : BigFppfOver B S hS} (f : X ⟶ Y) (ψ : yoneda.obj V ⟶ Y) (m : U ⟶ V)
    (p : yoneda.obj U ⟶ pullback f ψ) (hpsnd : p ≫ pullback.snd f ψ = yoneda.map m)
    {k₁ k₂ : R ⟶ U} (sqR : IsPullback (yoneda.map k₁) (yoneda.map k₂) p p) :
    ∃ (hkm : k₁ ≫ m = k₂ ≫ m)
      (hθ : (yoneda.map (pullback.fst m m) ≫ p ≫ pullback.fst f ψ) ≫ f
        = (yoneda.map (pullback.snd m m) ≫ p ≫ pullback.fst f ψ) ≫ f),
      IsPullback (yoneda.map k₁ ≫ p ≫ pullback.fst f ψ) (yoneda.map (pullback.lift k₁ k₂ hkm))
        (pullback.diagonal f) (pullback.lift _ _ hθ) := by
  have hkm : k₁ ≫ m = k₂ ≫ m := by
    apply yoneda.map_injective
    have h := sqR.w =≫ pullback.snd f ψ
    simpa only [Category.assoc, hpsnd, Functor.map_comp] using h
  have hside : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : Z ⟶ yoneda.obj U),
      (t ≫ p ≫ pullback.fst f ψ) ≫ f = (t ≫ p ≫ pullback.snd f ψ) ≫ ψ := by
    intro Z t
    simp only [Category.assoc]
    rw [pullback.condition]
  have hθ : (yoneda.map (pullback.fst m m) ≫ p ≫ pullback.fst f ψ) ≫ f
      = (yoneda.map (pullback.snd m m) ≫ p ≫ pullback.fst f ψ) ≫ f := by
    rw [hside, hside, hpsnd, ← Functor.map_comp, ← Functor.map_comp,
      pullback.condition (f := m) (g := m)]
  refine ⟨hkm, hθ, isPullback_kernelPair_diagonal (f := f) (ψ := ψ) (p := p) rfl hpsnd sqR
    (yoneda.map_isPullback (IsPullback.of_hasPullback m m)) ?_ ?_
    (pullback.lift_fst _ _ hθ) (pullback.lift_snd _ _ hθ)⟩
  · rw [← Functor.map_comp, pullback.lift_fst]
  · rw [← Functor.map_comp, pullback.lift_snd]

/-- A kernel pair of `p : h_U ⟶ P` has a diagonal section `U ⟶ R`. -/
private theorem exists_section_of_isPullback_yoneda {U R : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {r₁ r₂ : R ⟶ U} {p : yoneda.obj U ⟶ P}
    (sq : IsPullback (yoneda.map r₁) (yoneda.map r₂) p p) :
    ∃ s : U ⟶ R, s ≫ r₁ = 𝟙 U ∧ s ≫ r₂ = 𝟙 U := by
  obtain ⟨s, hs⟩ := yoneda.map_surjective (sq.lift (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj U)) rfl)
  refine ⟨s, ?_, ?_⟩ <;> apply yoneda.map_injective <;>
    simp only [Functor.map_comp, hs, sq.lift_fst, sq.lift_snd, CategoryTheory.Functor.map_id]

/-- Every represented base change of the relative diagonal of an unramified morphism of
algebraic spaces over `S` is an étale morphism of schemes. -/
theorem presheaf_etale_diagonal_of_isUnramified
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsUnramified B S hS f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f) := by
  obtain ⟨V, U, ψ, m, p, hψs, hψe, hqe, hpsnd, hps, hpe⟩ :=
    exists_etale_chart_over_target B S hS hX hY f
  have hrepΔ : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    MorphismProperty.of_isPullback (isPullback_pullbackDiagonal_diag B S hS f)
      hX.diagonal_representable
  -- The scheme morphism of the chart square is unramified, so the first projection of
  -- `U ×_V U` is unramified as a base change of it.
  have hmU : AlgebraicGeometry.Unramified ((BigFppfOver.toScheme B S hS).map m) := by
    refine hf U V (p ≫ pullback.fst f ψ) ψ m hqe hψe ?_
    rw [← hpsnd, Category.assoc, Category.assoc, pullback.condition]
  have hfstU : AlgebraicGeometry.Unramified
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m)) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Unramified.{u})
      ((BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback m m)).flip hmU
  -- The kernel pair of `p` maps étalely to `U ×_V U`.
  obtain ⟨R, k₂, k₁', sqR⟩ := hpe.rep p
  obtain ⟨k₁, rfl⟩ := yoneda.map_surjective k₁'
  have hk₁E : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₁) :=
    hpe.property p (yoneda.map k₂) k₁ sqR.flip
  obtain ⟨hkm, hθ, sqK⟩ := exists_isPullback_kernelPair_diagonal_yoneda B S hS f ψ m p hpsnd sqR
  have hkfst : Limits.pullback.lift k₁ k₂ hkm ≫ Limits.pullback.fst m m = k₁ :=
    Limits.pullback.lift_fst _ _ _
  have hkE : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.lift k₁ k₂ hkm)) := by
    have h₁ : AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map (Limits.pullback.lift k₁ k₂ hkm) ≫
          (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m)) := by
      rw [← Functor.map_comp, hkfst]; exact hk₁E
    have h₂ : AlgebraicGeometry.Unramified
        ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m)) := hfstU
    have h₃ : AlgebraicGeometry.FormallyUnramified
        ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m)) :=
      AlgebraicGeometry.formallyUnramified_of_unramified _
    exact AlgebraicGeometry.Etale.of_comp
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.lift k₁ k₂ hkm))
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst m m))
  -- Refine an arbitrary represented base change so that it factors through `U ×_V U`.
  refine presheaf_of_etale_cover B S hS _ hrepΔ fun a g => ?_
  obtain ⟨a₀, c₀, v', sq₀⟩ := hψe.rep ((g ≫ pullback.fst f f) ≫ f)
  obtain ⟨v, rfl⟩ := yoneda.map_surjective v'
  have hz₁ : (yoneda.map c₀ ≫ g ≫ pullback.fst f f) ≫ f = yoneda.map v ≫ ψ := by
    rw [sq₀.w]; simp only [Category.assoc]
  have hz₂ : (yoneda.map c₀ ≫ g ≫ pullback.snd f f) ≫ f = yoneda.map v ≫ ψ := by
    rw [sq₀.w]; simp only [Category.assoc]; rw [pullback.condition]
  obtain ⟨a₁, c₁, w₁', sq₁⟩ := hpe.rep (pullback.lift _ _ hz₁)
  obtain ⟨w₁, rfl⟩ := yoneda.map_surjective w₁'
  obtain ⟨a₂, c₂, w₂', sq₂⟩ := hpe.rep (yoneda.map c₁ ≫ pullback.lift _ _ hz₂)
  obtain ⟨w₂, rfl⟩ := yoneda.map_surjective w₂'
  have hw₁p : yoneda.map (c₂ ≫ w₁) ≫ p
      = yoneda.map (c₂ ≫ c₁) ≫ pullback.lift _ _ hz₁ := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, sq₁.w]
  have hw₂p : yoneda.map w₂ ≫ p = yoneda.map (c₂ ≫ c₁) ≫ pullback.lift _ _ hz₂ := by
    rw [Functor.map_comp, Category.assoc]; exact sq₂.w
  have e₁ : yoneda.map c₂ ≫ yoneda.map w₁ ≫ yoneda.map m
      = yoneda.map c₂ ≫ yoneda.map c₁ ≫ yoneda.map v := by
    have h := hw₁p =≫ pullback.snd f ψ
    simpa only [Category.assoc, hpsnd, pullback.lift_snd, Functor.map_comp] using h
  have e₂ : yoneda.map w₂ ≫ yoneda.map m
      = yoneda.map c₂ ≫ yoneda.map c₁ ≫ yoneda.map v := by
    have h := hw₂p =≫ pullback.snd f ψ
    simpa only [Category.assoc, hpsnd, pullback.lift_snd, Functor.map_comp] using h
  have hm12 : (c₂ ≫ w₁) ≫ m = w₂ ≫ m := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, Category.assoc]
    rw [e₁, e₂]
  have d₁ : yoneda.map c₂ ≫ yoneda.map w₁ ≫ p ≫ pullback.fst f ψ
      = yoneda.map c₂ ≫ yoneda.map c₁ ≫ yoneda.map c₀ ≫ g ≫ pullback.fst f f := by
    have h := hw₁p =≫ pullback.fst f ψ
    simpa only [Category.assoc, pullback.lift_fst, Functor.map_comp] using h
  have d₂ : yoneda.map w₂ ≫ p ≫ pullback.fst f ψ
      = yoneda.map c₂ ≫ yoneda.map c₁ ≫ yoneda.map c₀ ≫ g ≫ pullback.snd f f := by
    have h := hw₂p =≫ pullback.fst f ψ
    simpa only [Category.assoc, pullback.lift_fst, Functor.map_comp] using h
  have hll₁ : yoneda.map (Limits.pullback.lift (c₂ ≫ w₁) w₂ hm12)
      ≫ yoneda.map (Limits.pullback.fst m m) = yoneda.map c₂ ≫ yoneda.map w₁ := by
    rw [← Functor.map_comp, Limits.pullback.lift_fst, Functor.map_comp]
  have hll₂ : yoneda.map (Limits.pullback.lift (c₂ ≫ w₁) w₂ hm12)
      ≫ yoneda.map (Limits.pullback.snd m m) = yoneda.map w₂ := by
    rw [← Functor.map_comp, Limits.pullback.lift_snd]
  have hlθ : yoneda.map (Limits.pullback.lift (c₂ ≫ w₁) w₂ hm12)
      ≫ pullback.lift _ _ hθ = yoneda.map (c₂ ≫ c₁ ≫ c₀) ≫ g := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, Functor.map_comp]
      rw [← Category.assoc, hll₁]
      simp only [Category.assoc]
      exact d₁
    · simp only [Category.assoc, pullback.lift_snd, Functor.map_comp]
      rw [← Category.assoc, hll₂]
      exact d₂
  have sqL := (yoneda.map_isPullback (IsPullback.of_hasPullback
    (Limits.pullback.lift k₁ k₂ hkm) (Limits.pullback.lift (c₂ ≫ w₁) w₂ hm12))).paste_horiz sqK
  rw [hlθ] at sqL
  refine ⟨a₂, c₂ ≫ c₁ ≫ c₀, ?_, ?_, ?_⟩
  · have h₀ : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map c₀) :=
      hψs.property _ _ c₀ sq₀
    have h₁ : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map c₁) :=
      hps.property _ _ c₁ sq₁
    have h₂ : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map c₂) :=
      hps.property _ _ c₂ sq₂
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  · have h₀ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map c₀) :=
      hψe.property _ _ c₀ sq₀
    have h₁ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map c₁) :=
      hpe.property _ _ c₁ sq₁
    have h₂ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map c₂) :=
      hpe.property _ _ c₂ sq₂
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  · have hri : MorphismProperty.RespectsIso
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
        (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))
    refine property_of_isPullback_of_isPullback B S hS
      (hrepΔ.isPullback (yoneda.map (c₂ ≫ c₁ ≫ c₀) ≫ g)) sqL ?_
    exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale.{u})
      ((BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback _ _)) hkE

/-- **Stacks 05W1, part (1).** The relative diagonal of an unramified morphism of algebraic
spaces over `S` is an open immersion.

Each represented base change of the relative diagonal is a monomorphism of schemes, because
the relative diagonal is a base change of the absolute diagonal of the source
(`AlgebraicGeometry.isPullback_pullbackDiagonal_diag`) and the absolute diagonal of an algebraic
space is a monomorphism after every represented base change
(`AlgebraicGeometry.Space.monomorphisms_diag_of_representable`, part (2) of
[Stacks Project, Tag 02X4]). It is moreover étale, which is
`AlgebraicGeometry.Space.presheaf_etale_diagonal_of_isUnramified`. A morphism of schemes which
is étale and universally injective — in particular one which is étale and a monomorphism — is
an open immersion by [Stacks Project, Tag 025G]. -/
@[stacks 05W1 "part (1)",
  ega "IV 17.4.2" "a) ⇒ b)",
  sga "1 I 3.4" "diagonal case (g = id)",
  sga "3 XI 1.3" "more general"]
theorem isOpenImmersion_diagonal_of_isUnramified
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsUnramified B S hS f) :
    IsOpenImmersion B S hS (pullback.diagonal f) := by
  have hmono : (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f) :=
    monomorphisms_diagonal B S hS hX f
  have hetale := presheaf_etale_diagonal_of_isUnramified B S hS hX hY f hf
  refine ⟨hetale.rep, fun a b gg fst snd hsq => ?_⟩
  have hm : Mono ((BigFppfOver.toScheme B S hS).map snd) := hmono.property gg fst snd hsq
  have he : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd) :=
    hetale.property gg fst snd hsq
  exact isOpenImmersion_of_mono_of_etale ((BigFppfOver.toScheme B S hS).map snd)

/-- **Stacks 05W1, part (2).** A morphism of algebraic spaces over `S` which is locally of
finite type and whose relative diagonal is an open immersion is unramified.

Let `a : h_U ⟶ X`, `b : h_V ⟶ Y` be étale charts over `h : U ⟶ V`, and let
`p : h_U ⟶ X ×_Y h_V` be the induced morphism. The morphism `p` is representable, because
`p` composed with the base change `X ×_Y h_V ⟶ X` of `b` is the representable `a` and
representability cancels (`CategoryTheory.Functor.relativelyRepresentable.hasOfPostcompProperty`,
[Stacks Project, Tag 05L9]). Its kernel pair `R` is, by
`CategoryTheory.Limits.isPullback_kernelPair_diagonal`, a base change of the relative diagonal
of `f`, so `R ⟶ U ×_V U` is an open immersion by hypothesis.

The relative diagonal `U ⟶ U ×_V U` factors through `R` by a section `σ` of its first
projection, and it remains to see that `σ` is an open immersion. The relative diagonal
`d : U ⟶ R_a` of `p` over the kernel pair `R_a` of `a` *is* one: it is a section of the étale
first projection of `R_a`, hence étale by `AlgebraicGeometry.Etale.of_comp`, and a split
monomorphism, hence an open immersion by [Stacks Project, Tag 025G]. The comparison
`e : R ⟶ R_a` is a monomorphism because the two projections of `R` are jointly monic, and
`σ` is the base change of `d` along `e` — the square `𝟙, σ, d, e` is cartesian because `e` is a
monomorphism. Composing the two open immersions and transporting along the comparison of the
fibre product of `h` with itself in the site and in schemes gives that the diagonal of the
scheme morphism is an open immersion, and part (2) of [Stacks Project, Tag 02GE] concludes. -/
@[stacks 05W1 "part (2)", ega "IV 17.4.2" "b) ⇒ a)", sga "3 XI 1.3" "more general"]
theorem isUnramified_of_isOpenImmersion_diagonal (f : X ⟶ Y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hoi : IsOpenImmersion B S hS (pullback.diagonal f)) :
    IsUnramified B S hS f := by
  intro U V a b h ha hb hsq
  have hlft : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hft U V a b h ha hb hsq
  -- The chart of `X ×_Y h_V` determined by the square, and its kernel pair.
  set p : yoneda.obj U ⟶ pullback f b := pullback.lift a (yoneda.map h) hsq.symm with hpdef
  have hpfst : p ≫ pullback.fst f b = a := by rw [hpdef]; exact pullback.lift_fst _ _ _
  have hpsnd : p ≫ pullback.snd f b = yoneda.map h := by rw [hpdef]; exact pullback.lift_snd _ _ _
  have hprep : yoneda.relativelyRepresentable p := by
    refine MorphismProperty.of_postcomp _ p (pullback.fst f b)
      (presheaf_pullback_fst B S hS b f hb).rep ?_
    rw [hpfst]; exact ha.rep
  obtain ⟨R, ρ₂, ρ₁', sqR⟩ := hprep p
  obtain ⟨ρ₁, rfl⟩ := yoneda.map_surjective ρ₁'
  obtain ⟨hρh, hθ, sqK⟩ :=
    exists_isPullback_kernelPair_diagonal_yoneda B S hS f b h p hpsnd sqR
  have hkOI : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.lift ρ₁ ρ₂ hρh)) :=
    hoi.property _ _ _ sqK
  -- The relative diagonal of `p` over the kernel pair of `a` is an open immersion.
  obtain ⟨Ra, α₂, α₁', sqA⟩ := ha.rep a
  obtain ⟨α₁, rfl⟩ := yoneda.map_surjective α₁'
  have hα₁E : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map α₁) :=
    ha.property a (yoneda.map α₂) α₁ sqA.flip
  obtain ⟨d, hd₁, hd₂⟩ := exists_section_of_isPullback_yoneda B S hS sqA
  have hdE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map d) := by
    have h₁ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map d ≫
        (BigFppfOver.toScheme B S hS).map α₁) := by
      rw [← Functor.map_comp, hd₁, CategoryTheory.Functor.map_id]; infer_instance
    exact MorphismProperty.of_postcomp
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (W' := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))
      ((BigFppfOver.toScheme B S hS).map d) ((BigFppfOver.toScheme B S hS).map α₁) hα₁E h₁
  have hdOI : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map d) := by
    have : Mono ((BigFppfOver.toScheme B S hS).map d) :=
      have : IsSplitMono ((BigFppfOver.toScheme B S hS).map d) :=
        IsSplitMono.mk' ⟨(BigFppfOver.toScheme B S hS).map α₁, by
          rw [← Functor.map_comp, hd₁, CategoryTheory.Functor.map_id]⟩
      inferInstance
    exact isOpenImmersion_of_mono_of_etale _
  -- The comparison `R ⟶ R_a` is a monomorphism, and the diagonal section is its base change.
  have hρa : yoneda.map ρ₁ ≫ a = yoneda.map ρ₂ ≫ a := by
    have hw := sqR.w =≫ pullback.fst f b
    simpa only [Category.assoc, hpfst] using hw
  obtain ⟨e, he⟩ := yoneda.map_surjective (sqA.lift (yoneda.map ρ₁) (yoneda.map ρ₂) hρa)
  have he₁ : e ≫ α₁ = ρ₁ := by
    apply yoneda.map_injective; rw [Functor.map_comp, he, sqA.lift_fst]
  have he₂ : e ≫ α₂ = ρ₂ := by
    apply yoneda.map_injective; rw [Functor.map_comp, he, sqA.lift_snd]
  have heMono : Mono ((BigFppfOver.toScheme B S hS).map e) := by
    have hy : Mono (yoneda.map e) := by
      refine ⟨fun {Z} g₁ g₂ heq => sqR.hom_ext ?_ ?_⟩
      · have hx := heq =≫ yoneda.map α₁
        simpa only [Category.assoc, ← Functor.map_comp, he₁] using hx
      · have hx := heq =≫ yoneda.map α₂
        simpa only [Category.assoc, ← Functor.map_comp, he₂] using hx
    have : Mono e := yoneda.mono_of_mono_map hy
    exact preserves_mono_of_preservesLimit _ e
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_section_of_isPullback_yoneda B S hS sqR
  have hσe : σ ≫ e = d := by
    apply yoneda.map_injective
    refine sqA.hom_ext ?_ ?_
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, he₁, hσ₁, hd₁]
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, he₂, hσ₂, hd₂]
  have sqσ : IsPullback (𝟙 ((BigFppfOver.toScheme B S hS).obj U))
      ((BigFppfOver.toScheme B S hS).map σ) ((BigFppfOver.toScheme B S hS).map d)
      ((BigFppfOver.toScheme B S hS).map e) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, ← Functor.map_comp, hσe]⟩
  have hσOI : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map σ) :=
    MorphismProperty.of_isPullback
      (P := (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})) sqσ hdOI
  -- Assemble, and transport to the diagonal of the scheme morphism.
  have hσk : σ ≫ Limits.pullback.lift ρ₁ ρ₂ hρh = Limits.pullback.diagonal h := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, hσ₁, Limits.pullback.diagonal_fst]
    · rw [Category.assoc, Limits.pullback.lift_snd, hσ₂, Limits.pullback.diagonal_snd]
  have hdiagOI : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.diagonal h)) := by
    rw [← hσk, Functor.map_comp]
    have h₁ := hσOI
    have h₂ := hkOI
    infer_instance
  have hpbh := (BigFppfOver.toScheme B S hS).map_isPullback
    (IsPullback.of_hasPullback h h)
  have hOIdiag : AlgebraicGeometry.IsOpenImmersion
      (pullback.diagonal ((BigFppfOver.toScheme B S hS).map h)) := by
    rw [← map_diagonal_comp_isoPullback_hom _ h hpbh]
    have h₁ := hdiagOI
    infer_instance
  exact AlgebraicGeometry.Unramified.of_isOpenImmersion_diagonal
    ((BigFppfOver.toScheme B S hS).map h)

/-- **A property of the relative diagonal passes to the diagonals of the canonical represented
base changes.** Let `f : F ⟶ G` be a representable morphism of presheaves on the big fppf site
of `S` whose relative diagonal has the relatively representable property attached to a property
`P` of morphisms of schemes. Then, for each morphism `g` from a representable presheaf into `G`,
the morphism of schemes underlying the canonical represented base change of `f` along `g` has
`P` on its own diagonal.

This instantiates the universally quantified condition
`CategoryTheory.MorphismProperty.presheaf` at a single canonical pullback, for an arbitrary `P`,
so that the two comparisons between a diagonal and the image of a diagonal — under
`CategoryTheory.yoneda` and under `AlgebraicGeometry.BigFppfOver.toScheme` — are made once. -/
theorem map_pullbackDiagonal_of_presheaf_pullbackDiagonal
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : yoneda.relativelyRepresentable f)
    (hΔ : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.diagonal f))
    {a : BigFppfOver B S hS} (g : yoneda.obj a ⟶ G) :
    P (pullback.diagonal ((BigFppfOver.toScheme B S hS).map (hf.snd g))) := by
  have _ : MorphismProperty.IsStableUnderBaseChange
      ((MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have _ : MorphismProperty.RespectsIso
      ((MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf) :=
    MorphismProperty.relative_respectsIso _
  -- Descend the hypothesis from `f` to the canonical base change `yoneda.map (hf.snd g)`.
  have h₁ : ((MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).presheaf).diagonal (yoneda.map (hf.snd g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hf.isPullback g) hΔ
  -- Compare the presheaf-level diagonal with the Yoneda image of the diagonal in the site.
  have hy : IsPullback (yoneda.map (pullback.fst (hf.snd g) (hf.snd g)))
      (yoneda.map (pullback.snd (hf.snd g) (hf.snd g)))
      (yoneda.map (hf.snd g)) (yoneda.map (hf.snd g)) :=
    (IsPullback.of_hasPullback (hf.snd g) (hf.snd g)).map yoneda
  have hcy := map_diagonal_comp_isoPullback_hom yoneda (hf.snd g) hy
  have h₂ : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (pullback.diagonal (hf.snd g))) := by
    rw [MorphismProperty.diagonal_iff, ← hcy] at h₁
    exact (MorphismProperty.cancel_right_of_respectsIso
      (P := (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf) _
      hy.isoPullback.hom).mp h₁
  -- Read the statement in the site off, and compare with the diagonal of the scheme morphism.
  have h₃ : MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)
      (pullback.diagonal (hf.snd g)) := MorphismProperty.of_relative_map h₂
  have h₄ : P ((BigFppfOver.toScheme B S hS).map (pullback.diagonal (hf.snd g))) := h₃
  have hs : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst (hf.snd g) (hf.snd g)))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd (hf.snd g) (hf.snd g)))
      ((BigFppfOver.toScheme B S hS).map (hf.snd g))
      ((BigFppfOver.toScheme B S hS).map (hf.snd g)) :=
    (IsPullback.of_hasPullback (hf.snd g) (hf.snd g)).map (BigFppfOver.toScheme B S hS)
  have hcs := map_diagonal_comp_isoPullback_hom (BigFppfOver.toScheme B S hS) (hf.snd g) hs
  rw [← hcs]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := P) _ hs.isoPullback.hom).mpr h₄

end AlgebraicGeometry.Space

end
