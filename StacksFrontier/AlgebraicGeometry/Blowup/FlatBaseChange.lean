module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# Blowing up commutes with flat base change

Let `g : X₁ ⟶ X₂` be a flat morphism of schemes, let `Z₂ ⊆ X₂` be the closed subscheme cut out
by a quasi-coherent ideal sheaf `I`, and let `Z₁ ⊆ X₁` be its inverse image, cut out by
`I.comap g`. Writing `Xᵢ'` for the blowup of `Xᵢ` in `Zᵢ`, Stacks tag 0805 says that the square

```
X₁' ⟶ X₂'
 ↓      ↓
X₁ ⟶  X₂
```

is cartesian.

## Main results

* `Stacks.Blowup.isPullback_of_isTerminal`: the purely formal half. If `b₁` is a terminal object
  of the category of tag 0806 for `I.comap g` over `X₁`, `b₂` is one for `I` over `X₂`, and the
  base change `X₁ ×_{X₂} X₂' ⟶ X₁` happens to lie in the former category, then the square built
  from `b₁`, `b₂` and `g` is cartesian.
* `Stacks.Blowup.IsAdmissibleBlowup.of_isPullback`: **admissible blowups are stable under flat
  base change**. A base change of a `U`-admissible blowup along a flat `g` is a
  `g ⁻¹ᵁ U`-admissible blowup, the centre of the base change being the inverse image of the
  centre. Stated for an arbitrary cartesian square, so that both spellings of a base change are
  instances of it.
* `Stacks.Blowup.IsAdmissibleBlowup.pullback_snd` and
  `Stacks.Blowup.IsAdmissibleBlowup.morphismRestrict`: those two spellings — the second
  projection of a fibre product, and the restriction of the base to an open subscheme. The
  latter is the one the locality of admissible blowups on the base needs: a `U`-admissible
  blowup of `S` restricts over an open `W ⊆ S` to a `(U ⊓ W)`-admissible blowup of `W`, with
  that open of `W` written either as `W.ι ⁻¹ᵁ U` or, through
  `AlgebraicGeometry.Scheme.Opens.ι_preimage_inf_right`, as `W.ι ⁻¹ᵁ (U ⊓ W)` — see
  `Stacks.Blowup.IsAdmissibleBlowup.morphismRestrict_inf`.

Tag 0805 itself, blowing up commutes with flat base change, is
`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap` of
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/FlatBaseChange.lean`. It lies in the
namespace of the constants the statement is about, `AlgebraicGeometry`, since the type mentions
`AlgebraicGeometry.blowUpToBase`, and it is not redeclared here.

## Implementation notes

The argument is the usual one: both `X₁'` and `X₁ ×_{X₂} X₂'` are shown to be terminal in the
category `C₁` of schemes over `X₁` whose inverse image of `Z₁` is an effective Cartier divisor,
so the canonical maps between them are mutually inverse.

* `X₁ ⟶ X₂` lies under `X₁' ⟶ X₁`, and the inverse image of `Z₂` along the composite is the
  inverse image of `Z₁` along `X₁' ⟶ X₁`, which is an effective Cartier divisor; so `X₁'` is an
  object of the category `C₂` of tag 0806 for `I` and the terminal object `X₂'` receives a
  canonical map `f : X₁' ⟶ X₂'` over `X₂`. Together with `X₁' ⟶ X₁` this gives
  `h : X₁' ⟶ X₁ ×_{X₂} X₂'`.
* Conversely `X₁ ×_{X₂} X₂' ⟶ X₂'` is a base change of the flat `g`, hence flat, so the inverse
  image of the exceptional divisor of `X₂'` along it is again an effective Cartier divisor
  (tag 02OO (6), `Stacks.Divisors.isPullbackDefined_of_flat`). That divisor is the inverse image
  of `Z₁` along `X₁ ×_{X₂} X₂' ⟶ X₁`, so the pullback is an object of `C₁` and the terminal `X₁'`
  receives a canonical map `k` back.
* `k ≫ h = 𝟙` and `h ≫ k = 𝟙` both follow from terminality, the first in `C₂` after checking the
  two projections and the second in `C₁` directly.

`Stacks.Blowup.isPullback_of_isTerminal` quantifies over *arbitrary* schemes `Y₁, Y₂` with
morphisms `b₁, b₂` assumed terminal, rather than over the blowups themselves. Only the final
instantiation mentions `AlgebraicGeometry.blowUp`, which is a relative `Proj`; keeping the
concrete object out of the formal argument is what stops the kernel from being asked to unfold
the relative `Proj` chart data while checking it.

Flatness is used exactly once, to produce the hypothesis `hP`.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

/-- The formal half of Stacks tag 0805. Let `g : X₁ ⟶ X₂` be a morphism of schemes and `I` a
quasi-coherent ideal sheaf on `X₂`. Suppose `b₂ : Y₂ ⟶ X₂` is a terminal object of the category
of tag 0806 for `I`, that `b₁ : Y₁ ⟶ X₁` is a terminal object of that category for `I.comap g`,
and that the first projection of `X₁ ×_{X₂} Y₂` is an object of the latter category. Then the
square with sides `b₁`, `b₂` and `g` is cartesian.

No flatness is needed: flatness of `g` serves only to supply `hP`. -/
theorem isPullback_of_isTerminal {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂) (I : X₂.IdealSheafData)
    {Y₁ Y₂ : Scheme.{u}} {b₁ : Y₁ ⟶ X₁} {b₂ : Y₂ ⟶ X₂}
    {h₁ : IsCartierOver (I.comap g) (Over.mk b₁)} {h₂ : IsCartierOver I (Over.mk b₂)}
    (t₁ : IsTerminal (⟨Over.mk b₁, h₁⟩ : CartierOver (I.comap g)))
    (t₂ : IsTerminal (⟨Over.mk b₂, h₂⟩ : CartierOver I))
    (hP : IsCartierOver (I.comap g) (Over.mk (pullback.fst g b₂))) :
    ∃ h : Y₁ ⟶ Y₂, IsPullback b₁ h g b₂ := by
  -- `Y₁` is an object of the category for `I` over `X₂`, via the composite `b₁ ≫ g`.
  have h₁₂ : IsCartierOver I (Over.mk (b₁ ≫ g)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (b₁ ≫ g))
    rw [Scheme.IdealSheafData.comap_comp]
    exact h₁
  -- the classifying morphism `f : Y₁ ⟶ Y₂` over `X₂`
  set φ := t₂.from (⟨Over.mk (b₁ ≫ g), h₁₂⟩ : CartierOver I)
  set f : Y₁ ⟶ Y₂ := φ.hom.left
  have hf : f ≫ b₂ = b₁ ≫ g := Over.w φ.hom
  -- the comparison morphism into the fibre product
  set h : Y₁ ⟶ pullback g b₂ := pullback.lift b₁ f hf.symm
  have hfst : h ≫ pullback.fst g b₂ = b₁ := pullback.lift_fst b₁ f hf.symm
  have hsnd : h ≫ pullback.snd g b₂ = f := pullback.lift_snd b₁ f hf.symm
  -- the classifying morphism back, from the fibre product
  set κ := t₁.from (⟨Over.mk (pullback.fst g b₂), hP⟩ : CartierOver (I.comap g))
  set k : pullback g b₂ ⟶ Y₁ := κ.hom.left
  have hk : k ≫ b₁ = pullback.fst g b₂ := Over.w κ.hom
  -- the fibre product is also an object of the category for `I` over `X₂`
  have hP₂ : IsCartierOver I (Over.mk (pullback.snd g b₂ ≫ b₂)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (pullback.snd g b₂ ≫ b₂))
    rw [← pullback.condition, Scheme.IdealSheafData.comap_comp]
    exact hP
  -- `k ≫ f` and `pullback.snd` are two morphisms in that category to the terminal object
  have hkf : k ≫ f = pullback.snd g b₂ := by
    have := t₂.hom_ext
      (ObjectProperty.homMk (X := (⟨Over.mk (pullback.snd g b₂ ≫ b₂), hP₂⟩ : CartierOver I))
        (Over.homMk (k ≫ f) (by
          change (k ≫ f) ≫ b₂ = pullback.snd g b₂ ≫ b₂
          rw [Category.assoc, hf, ← Category.assoc, hk, pullback.condition])))
      (ObjectProperty.homMk (Over.homMk (pullback.snd g b₂) rfl))
    exact congrArg (fun q => q.hom.left) this
  have hcompP : k ≫ h = 𝟙 (pullback g b₂) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, hk, Category.id_comp]
    · rw [Category.assoc, hsnd, hkf, Category.id_comp]
  have hcompY₁ : h ≫ k = 𝟙 Y₁ := by
    have := t₁.hom_ext
      (ObjectProperty.homMk (X := (⟨Over.mk b₁, h₁⟩ : CartierOver (I.comap g)))
        (Over.homMk (h ≫ k) (by
          change (h ≫ k) ≫ b₁ = b₁
          rw [Category.assoc, hk, hfst])))
      (𝟙 _)
    simpa using congrArg (fun q => q.hom.left) this
  refine ⟨f, ?_⟩
  exact IsPullback.iff_exists_over_iso.2 ⟨Over.isoMk ⟨h, k, hcompY₁, hcompP⟩ hfst, hsnd.symm⟩

/-! ### Admissible blowups are stable under flat base change

The two conditions `Stacks.Blowup.IsAdmissibleBlowup` puts on the centre are inherited by its
inverse image, and tag 0805 identifies the base change of the blowup with the blowup in that
inverse image. So a `U`-admissible blowup base changes to a `g ⁻¹ᵁ U`-admissible blowup along any
flat `g`, in particular along the inclusion of an open subscheme.
-/

/-- The open of `W` cut out by `U` is the one cut out by `U ⊓ W`: restricting to `W` already
intersects with `W`. This is what makes
`Stacks.Blowup.IsAdmissibleBlowup.morphismRestrict` the statement that a `U`-admissible blowup
restricts to a `(U ⊓ W)`-admissible blowup of `W`. -/
theorem _root_.AlgebraicGeometry.Scheme.Opens.ι_preimage_inf_right {X : Scheme.{u}}
    (U W : X.Opens) : W.ι ⁻¹ᵁ (U ⊓ W) = W.ι ⁻¹ᵁ U := by
  have h : W.ι ⁻¹ᵁ (U ⊓ W) = (W.ι ⁻¹ᵁ U) ⊓ (W.ι ⁻¹ᵁ W) := rfl
  rw [h, W.ι_preimage_self, inf_top_eq]

/-- **Admissible blowups are stable under flat base change.** If `f : X' ⟶ X` is a
`U`-admissible blowup and `p : P ⟶ X₁` is a base change of `f` along a flat `g : X₁ ⟶ X`, then
`p` is a `g ⁻¹ᵁ U`-admissible blowup of `X₁`.

The centre is the inverse image `I.comap g` of the centre `I` exhibiting `f`. Its closed
subscheme is of finite presentation because it is the base change of `I.subscheme`
(`AlgebraicGeometry.finitePresentation_comap_subschemeι`), and its support is the inverse image
of the support of `I` (`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`), hence disjoint
from the inverse image of `U`. That `P` is the blowup of `X₁` in `I.comap g` is
[Stacks, Tag 0805] (`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`): both `P` and that
blowup sit at the top left of a cartesian square over the cospan formed by `g` and the blowup
morphism of `I`, so they agree over `X₁`.

Tag 0805 is stated for `AlgebraicGeometry.blowUp` while
`Stacks.Blowup.IsAdmissibleBlowup` is phrased with `Stacks.Blowup.blowUp`; the two constructions
are compared by `Stacks.Blowup.isAdmissibleBlowup_iff`, which is what lets the square tag 0805
produces be used directly.

The hypothesis is given as a cartesian square rather than as a concrete fibre product so that
the two spellings a consumer may hold -- `CategoryTheory.Limits.pullback.snd` and
`AlgebraicGeometry.morphismRestrict` -- are both instances of it; see
`Stacks.Blowup.IsAdmissibleBlowup.pullback_snd` and
`Stacks.Blowup.IsAdmissibleBlowup.morphismRestrict`. -/
theorem IsAdmissibleBlowup.of_isPullback {X X' X₁ P : Scheme.{u}} {U : X.Opens} {f : X' ⟶ X}
    (h : IsAdmissibleBlowup U f) {g : X₁ ⟶ X} [Flat g] {p : P ⟶ X₁} {q : P ⟶ X'}
    (hP : IsPullback p q g f) : IsAdmissibleBlowup (g ⁻¹ᵁ U) p := by
  rw [isAdmissibleBlowup_iff] at h ⊢
  obtain ⟨I, hfp, hdisj, e, he⟩ := h
  refine ⟨I.comap g, finitePresentation_comap_subschemeι I g hfp, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.support_comap]
    exact hdisj.preimage g.base
  · obtain ⟨c, hB⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap g I
    have hA : IsPullback p (q ≫ e.hom) g (AlgebraicGeometry.blowUpToBase I) :=
      hP.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp)
        (by simpa using he.symm)
    exact ⟨hA.isoIsPullback _ _ hB, hA.isoIsPullback_hom_fst _ _ hB⟩

/-- **Admissible blowups are stable under flat base change**, for the fibre product
`CategoryTheory.Limits.pullback`: the second projection of `X' ×_X X₁` is a
`g ⁻¹ᵁ U`-admissible blowup of `X₁` whenever `f : X' ⟶ X` is a `U`-admissible blowup and
`g : X₁ ⟶ X` is flat. -/
theorem IsAdmissibleBlowup.pullback_snd {X X' X₁ : Scheme.{u}} {U : X.Opens} {f : X' ⟶ X}
    (h : IsAdmissibleBlowup U f) (g : X₁ ⟶ X) [Flat g] :
    IsAdmissibleBlowup (g ⁻¹ᵁ U) (pullback.snd f g) :=
  h.of_isPullback (IsPullback.of_hasPullback f g).flip

/-- **Admissible blowups are stable under restricting the base to an open subscheme.** If
`f : X' ⟶ X` is a `U`-admissible blowup and `W ⊆ X` is open, then the restriction
`f ∣_ W : f ⁻¹ᵁ W ⟶ W` is a `W.ι ⁻¹ᵁ U`-admissible blowup of `W`.

The open of `W` appearing here is the one `U ⊓ W` cuts out, by
`AlgebraicGeometry.Scheme.Opens.ι_preimage_inf_right`. -/
theorem IsAdmissibleBlowup.morphismRestrict {X X' : Scheme.{u}} {U : X.Opens} {f : X' ⟶ X}
    (h : IsAdmissibleBlowup U f) (W : X.Opens) :
    IsAdmissibleBlowup (W.ι ⁻¹ᵁ U) (f ∣_ W) :=
  h.of_isPullback (isPullback_morphismRestrict f W)

/-- **Admissible blowups are stable under restricting the base to an open subscheme**, with the
open of `W` spelled as the one `U ⊓ W` cuts out. This is
`Stacks.Blowup.IsAdmissibleBlowup.morphismRestrict` read through
`AlgebraicGeometry.Scheme.Opens.ι_preimage_inf_right`. -/
theorem IsAdmissibleBlowup.morphismRestrict_inf {X X' : Scheme.{u}} {U : X.Opens} {f : X' ⟶ X}
    (h : IsAdmissibleBlowup U f) (W : X.Opens) :
    IsAdmissibleBlowup (W.ι ⁻¹ᵁ (U ⊓ W)) (f ∣_ W) := by
  rw [Scheme.Opens.ι_preimage_inf_right]
  exact h.morphismRestrict W

end Stacks.Blowup

end
