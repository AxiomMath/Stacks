module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverFrobeniusTwistSituation
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCover

/-!
# The relative Frobenius of a smooth morphism of locally constant relative dimension

Let `S₀` be a scheme in characteristic `p` and let `X ⟶ S₀` be smooth, with no fixed relative
dimension.  The relative dimension is then only locally constant on `X`.  This module proves that
the relative Frobenius `F_{X/S₀} : X ⟶ X^{(1)}` is an iterated `α_p`-cover, and that around every
point of `X^{(1)}` it has constant degree `p ^ n` for the local relative dimension `n`; when `X` is
quasi-compact the exponents `n` are bounded.

The argument reduces to `AlgebraicGeometry.exists_affine_relativeFrobenius_restriction`, the local
statement for a morphism smooth of a fixed relative dimension.  Smoothness makes every point of
`X` lie in an open `V` with `V ⟶ S₀` smooth of some relative dimension `n`, and the relative
Frobenius commutes with restriction to `V`: the square

```
V          ⟶  V^{(1)}
↓              ↓
X          ⟶  X^{(1)}
```

is a fibre square whose right arrow is an open immersion, because Frobenius twisting is a base
change and the relative Frobenius of an open immersion is an isomorphism.  So the restriction of
`F_{X/S₀}` over an open of `V^{(1)}` is identified with the restriction of `F_{V/S₀}` there.

## Main results

* `AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_nbhd` — a smooth morphism is smooth
  of some relative dimension on a neighbourhood of every point of the source.
* `AlgebraicGeometry.Smooth.exists_bound_smoothOfRelativeDimension_nbhd` — over a quasi-compact
  source those relative dimensions may be taken bounded.
* `AlgebraicGeometry.exists_affine_relativeFrobenius_restriction_of_smooth` — locally on
  `X^{(1)}` the relative Frobenius of a smooth `X ⟶ S₀` is a composition of `α_p`-covers whose
  sections have a basis of `p ^ n` elements, `n` bounded when `X` is quasi-compact.
* `relativeFrobeniusToTwist_isIteratedAlphaPCover_localDegree`, in the namespace
  `Crystalline.GlobalCrystallineSituation` — in the global crystalline situation with `p ∈ I`
  and `X ⟶ S₀` smooth with `X` quasi-compact, `F_{X/S₀}` is an iterated `α_p`-cover, and
  locally on `X^{(1)}` it has constant degree `p ^ n` with `n ≤ D` for one `D`.

## References

* [Stacks Project, Lemma 60.26.5, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
* [Stacks Project, Proposition 60.27.1, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Locally constant relative dimension -/

/-- **A smooth morphism is smooth of some relative dimension near every point of the source**:
every point has an open neighbourhood `V` such that `V ⟶ Y` is smooth of relative dimension `n`
for some `n`. -/
theorem Smooth.exists_smoothOfRelativeDimension_nbhd {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp
      (HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension n)).respectsIso
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- **Over a quasi-compact source a smooth morphism has bounded local relative dimension**: there
is one `D` such that every point of the source has an open neighbourhood `V` with `V ⟶ Y` smooth
of some relative dimension `n ≤ D`. -/
theorem Smooth.exists_bound_smoothOfRelativeDimension_nbhd {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [CompactSpace X] :
    ∃ D : ℕ, ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      ∃ n ≤ D, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  choose V hV n hn using Smooth.exists_smoothOfRelativeDimension_nbhd f
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hV x⟩)
  refine ⟨t.sup n, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact ⟨V x, hy, n x, Finset.le_sup hx, hn x⟩

/-! ### The relative Frobenius and restriction to an open -/

/-- **Restriction over the image of an open immersion in a fibre square.**  If `b` is the base
change of `f` along an open immersion `k`, then the restriction of `f` over the image of `k` is
identified with `b` by isomorphisms of sources and targets. -/
theorem exists_iso_morphismRestrict_opensRange_of_isPullback
    {P Y' X Y : Scheme.{u}} {b : P ⟶ Y'} {c : P ⟶ X} {k : Y' ⟶ Y} {f : X ⟶ Y}
    [IsOpenImmersion k] (h : IsPullback b c k f) :
    ∃ eX : (f ⁻¹ᵁ k.opensRange).toScheme ≅ P,
      (f ∣_ k.opensRange) ≫ k.isoOpensRange.inv = eX.hom ≫ b := by
  have hsq : IsPullback (b ≫ k.isoOpensRange.hom) c k.opensRange.ι f := by
    apply h.of_iso (Iso.refl _) k.isoOpensRange (Iso.refl _) (Iso.refl _) <;>
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact k.isoOpensRange_hom_ι.symm
  let hr := isPullback_morphismRestrict f k.opensRange
  refine ⟨hr.isoIsPullback _ _ hsq, ?_⟩
  rw [← cancel_mono k.isoOpensRange.hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (hr.isoIsPullback_hom_fst _ _ hsq).symm

/-- **Locally on `X^{(1)}`, the relative Frobenius of a smooth morphism is a composition of
`α_p`-covers whose sections have a basis of `p ^ n` elements, `n` bounded by the bound of the
local relative dimension.**  If every point of `X` has an open neighbourhood smooth over `S₀` of
some relative dimension at most `D`, then every point of `X^{(1)}` has an affine open
neighbourhood `W` over which `F_{X/S₀}` is a composition of `α_p`-covers and `Γ(X, F⁻¹ W)` has
a basis of `p ^ n` elements over `Γ(X^{(1)}, W)`, for some `n ≤ D`. -/
theorem exists_affine_relativeFrobenius_restriction_of_bound
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) (D : ℕ)
    (hD : ∀ x : X.left, ∃ V : X.left.Opens, x ∈ V ∧
      ∃ n ≤ D, SmoothOfRelativeDimension n (V.ι ≫ X.hom))
    (x : ((frobeniusTwist S p hS).obj X).left) :
    ∃ W : ((frobeniusTwist S p hS).obj X).left.Opens,
      IsAffineOpen W ∧ x ∈ W ∧ ∃ n ≤ D,
      IsAlphaPCoverComposite p ((relativeFrobenius S p hS X).left ∣_ W) ∧
      HasFiniteBasis ((relativeFrobenius S p hS X).left ∣_ W).appTop.hom (p ^ n) := by
  obtain ⟨x', hx'⟩ := relativeFrobenius_surjective S p hS X x
  obtain ⟨V, hxV, n, hnD, hn⟩ := hD x'
  let X₁ : Over S := Over.mk (V.ι ≫ X.hom)
  have : SmoothOfRelativeDimension n X₁.hom := hn
  let i : X₁ ⟶ X := Over.homMk V.ι rfl
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  let j := ((frobeniusTwist S p hS).map i).left
  have : IsOpenImmersion j :=
    MorphismProperty.of_isPullback (isPullback_frobeniusTwist_map S p hS i).flip
      (inferInstanceAs (IsOpenImmersion i.left))
  have hi := isPullback_relativeFrobenius_of_etale S p hS i
  let F₁ := (relativeFrobenius S p hS X₁).left
  let y := F₁ ⟨x', hxV⟩
  obtain ⟨W', hW', hyW', hc, hb⟩ := exists_affine_relativeFrobenius_restriction S p hS X₁ n y
  have : IsAffine W'.toScheme := hW'
  let k := W'.ι ≫ j
  have hsq := (isPullback_morphismRestrict F₁ W').paste_vert hi
  obtain ⟨eX, hcompat⟩ := exists_iso_morphismRestrict_opensRange_of_isPullback hsq
  refine ⟨k.opensRange, isAffineOpen_opensRange k, ?_, n, hnD,
    isAlphaPCoverComposite_of_iso p _ _ eX k.isoOpensRange.symm hcompat hc,
    hasFiniteBasis_appTop_of_iso _ _ eX k.isoOpensRange.symm hcompat _ hb⟩
  exact ⟨⟨y, hyW'⟩, (congrArg (fun g : V.toScheme ⟶ ((frobeniusTwist S p hS).obj X).left =>
    g ⟨x', hxV⟩) hi.w).trans hx'⟩

/-- **Locally on `X^{(1)}`, the relative Frobenius of a smooth morphism with quasi-compact source
is a composition of `α_p`-covers with a basis of `p ^ n` elements, `n` bounded.** -/
theorem exists_affine_relativeFrobenius_restriction_of_smooth
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) [Smooth X.hom] [CompactSpace X.left] :
    ∃ D : ℕ, ∀ x : ((frobeniusTwist S p hS).obj X).left,
      ∃ W : ((frobeniusTwist S p hS).obj X).left.Opens,
        IsAffineOpen W ∧ x ∈ W ∧ ∃ n ≤ D,
        IsAlphaPCoverComposite p ((relativeFrobenius S p hS X).left ∣_ W) ∧
        HasFiniteBasis ((relativeFrobenius S p hS X).left ∣_ W).appTop.hom (p ^ n) := by
  obtain ⟨D, hD⟩ := Smooth.exists_bound_smoothOfRelativeDimension_nbhd X.hom
  exact ⟨D, exists_affine_relativeFrobenius_restriction_of_bound S p hS X D hD⟩

/-- A morphism `f` whose sections over the whole of its affine target have a basis of `q`
elements has constant degree `q`. -/
theorem hasConstantDegree_of_hasFiniteBasis_appTop {X' X : Scheme.{u}} [IsAffine X]
    (f : X' ⟶ X) (q : ℕ) (h : HasFiniteBasis f.appTop.hom q) : HasConstantDegree f q := by
  intro x
  refine ⟨⊤, isAffineOpen_top X, trivial, ?_⟩
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  let _ := (f.app ⊤).hom.toAlgebra
  obtain ⟨b⟩ : HasFiniteBasis (f.app ⊤).hom q := h
  exact ⟨Module.Free.of_basis b, by simpa using rank_eq_card_basis b⟩

/-- **The relative Frobenius of a smooth morphism with quasi-compact source is an iterated
`α_p`-cover of locally bounded degree.**  Let `S₀` be a scheme in characteristic `p` and let
`X ⟶ S₀` be smooth with `X` quasi-compact.  Then `F_{X/S₀} : X ⟶ X^{(1)}` is an iterated
`α_p`-cover, and there is `D` such that every point of `X^{(1)}` has an open neighbourhood `U`
over which `F_{X/S₀}` has constant degree `p ^ n` for some `n ≤ D`. -/
theorem isIteratedAlphaPCover_relativeFrobenius_localDegree
    (S₀ : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS₀ : IsInCharacteristic S₀ p)
    (X : Over S₀) [Smooth X.hom] [CompactSpace X.left] :
    IsIteratedAlphaPCover p (relativeFrobenius S₀ p hS₀ X).left ∧
      ∃ D : ℕ, ∀ x : ((frobeniusTwist S₀ p hS₀).obj X).left,
        ∃ U : ((frobeniusTwist S₀ p hS₀).obj X).left.Opens, x ∈ U ∧
          ∃ n ≤ D, HasConstantDegree ((relativeFrobenius S₀ p hS₀ X).left ∣_ U) (p ^ n) := by
  obtain ⟨D, hD⟩ := exists_affine_relativeFrobenius_restriction_of_smooth S₀ p hS₀ X
  refine ⟨⟨isInCharacteristic_of_hom ((frobeniusTwist S₀ p hS₀).obj X).hom p hS₀,
    fun x => ?_⟩, D, fun x => ?_⟩
  · obtain ⟨W, _, hx, _, _, hc, _⟩ := hD x
    exact ⟨W, hx, hc⟩
  · obtain ⟨W, hW, hx, n, hn, _, hb⟩ := hD x
    have : IsAffine W.toScheme := hW
    exact ⟨W, hx, n, hn, hasConstantDegree_of_hasFiniteBasis_appTop _ _ hb⟩

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation

open AlgebraicGeometry

variable (T : GlobalCrystallineSituation.{u})

/-- **`F_{X/S₀}` is an iterated `α_p`-cover of locally bounded degree, for `X ⟶ S₀` smooth with
`X` quasi-compact.**  In the global crystalline situation of [Stacks, Tag 07MF] with `p` in the
divided power ideal, let `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` and `F_{X/S₀} : X ⟶ X^{(1)}` the relative
Frobenius.  If `X ⟶ S₀` is smooth and `X` is quasi-compact, then `F_{X/S₀}` is an iterated
`α_p`-cover, and there is `D` such that every point of `X^{(1)}` has an open neighbourhood over
which `F_{X/S₀}` has constant degree `p ^ n` for some `n ≤ D`: the relative dimension of
`X ⟶ S₀` is only locally constant, and `D` bounds it. -/
theorem relativeFrobeniusToTwist_isIteratedAlphaPCover_localDegree
    (hp : (T.p : Γ(T.S.scheme, ⊤)) ∈ T.S.ideal.obj (op ⊤))
    [Smooth T.toClosedFiber] [CompactSpace T.X] :
    IsIteratedAlphaPCover T.p (T.relativeFrobeniusToTwist hp) ∧
      ∃ D : ℕ, ∀ x : (T.frobeniusTwistSituation hp).X,
        ∃ U : (T.frobeniusTwistSituation hp).X.Opens, x ∈ U ∧
          ∃ n ≤ D, HasConstantDegree ((T.relativeFrobeniusToTwist hp) ∣_ U) (T.p ^ n) := by
  have : Smooth T.overClosedFiber.hom := ‹_›
  have : CompactSpace T.overClosedFiber.left := ‹_›
  exact isIteratedAlphaPCover_relativeFrobenius_localDegree (DividedPowerScheme.closedFiber T.S)
    T.p (T.isInCharacteristic_closedFiber_of_prime_mem hp) T.overClosedFiber

end Crystalline.GlobalCrystallineSituation

end
