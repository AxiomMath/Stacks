module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.StalkColonIdeal
public import StacksFrontier.AlgebraicGeometry.DenominatorColonIdeal.SectionMultiplication

/-!
# The stalk of multiplication by the section is the fractional product ideal of a local ratio

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a meromorphic section of `L`. The
ideal of denominators `I ⊆ 𝒪_X` of `s` has two projections, and
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.StalkColonIdeal` passes the affine-local
presentation of the first — the inclusion in the structure sheaf — to the stalk at a point: its
germs are `Ideal.denominatorIdeal` of the germs of a local ratio `a / b` of `s`. This file does
the same for the second projection, multiplication by `s`.

The values of multiplication by `s` are sections of `L`, not of `𝒪_X`, so their germs form a
subset of `L_x` rather than an ideal of the local ring. A trivializing basis of `L` at `x` turns
that subset into one: over an affine open `V` carrying a basis element `e` and the ratio `a / b`,
the values of multiplication by `s` on sections over a basic open of `V` are exactly the
multiples `y e` with `y b` a multiple of `a`, so the germs at `x` are exactly the multiples
`y · germ(e)` with `y` in `Ideal.fractionalProductIdeal` of the germs of `a` and of `b`. Read
through the coordinate of the stalk basis — `Stacks.Divisors.IsStalkBasis.coord` — that is the
statement

  `z ∈ mulGerms ↔ coord z ∈ Ideal.fractionalProductIdeal (germ a) (germ b)`.

That is the shape in which part (4) of [Stacks, Tag 02SW] consumes the second quotient: the
coefficient of the cycle `[Q₂]_k` at a point is the length of `(F ⊗ L)_x / s(I F)_x`, and the
length formula of [Stacks, Tag 02QH] —
`Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient` — compares exactly the
colengths of `Ideal.fractionalProductIdeal a b` and of `Ideal.denominatorIdeal a b`.

## Main definitions

* `Stacks.Chow.DenominatorStalk.mulGerms` — the germs at a point of the values of multiplication
  by `s` on the ideal of denominators, a subset of `L_x`.

## Main results

* `Stacks.Chow.DenominatorStalk.mulGerms_eq_smul_image` — those germs are the multiples of a
  trivializing germ by the fractional product ideal of the germs of the local ratio.
* `Stacks.Chow.DenominatorStalk.mem_mulGerms_iff_coord_mem` — the same statement read through the
  coordinate of a stalk basis, which is the form a length computation consumes.
* `Stacks.Chow.DenominatorStalk.exists_affineOpen_stalk_presentations` — around every point of a
  scheme there is an affine open carrying **one** ratio `a / b`, with `b` a nonzerodivisor, and a
  trivializing basis for which the germs of the first projection are `Ideal.denominatorIdeal` of
  its germs and the germs of the second are `Ideal.fractionalProductIdeal` of them. This is the
  entry point, and its only hypothesis is that `L` is invertible.

## Implementation notes

The proof is the one of `Stacks.Chow.DenominatorStalk.germs_eq_coe_denominatorIdeal`, run on the
second projection: no localization statement about colon ideals is used, because
`Stacks.DenominatorMul.range_denominatorIdealMul_app_basicOpen` is available on *every* basic open
of the trivializing affine and those form a neighbourhood basis of each of its points by
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`. Both inclusions therefore choose
representatives of germs on a basic open and read the presentation there.

The one new ingredient is that the trivializing section has to be the *same* on all those basic
opens, which it is: the presentation on a basic open is stated with the restriction of the basis
element of the affine open, and the germ of a restriction is the germ, so the right-hand side of
the germ statement mentions one element `germ(e)` of `L_x` and nothing smaller.

`Stacks.Chow.DenominatorStalk.mulGerms` is written with `AlgebraicGeometry.denominatorIdealMul`
while the hypothesis of
`Stacks.Chow.DenominatorStalk.exists_affineOpen_stalk_presentations` is supplied in the
`Stacks.DenominatorIdeal` spelling, exactly as for the first projection in
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.DenominatorActionStalk`: the two are two
names for one object, the crossing between them is a `rfl`, and
`open AlgebraicGeometry hiding denominatorIdeal denominatorIdealι denominatorIdealMul` is what
keeps the three names unambiguous. They are left alone here.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry hiding denominatorIdeal denominatorIdealι denominatorIdealMul
open CategoryTheory TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorColonIdeal Stacks.DenominatorLocalRatio

universe u

namespace Stacks.Chow.DenominatorStalk

variable (X : Scheme.{u}) (L : X.Modules)
  (s : AlgebraicGeometry.MeromorphicSection.{u, u} X.sheaf L)

/-- **The germs at `x` of the values of multiplication by `s`** on the ideal of denominators,
that is the image in `L_x` of the stalk of the second projection of that ideal. This is the
counterpart for the second projection of `Stacks.Chow.DenominatorStalk.germs`, and it is a subset
of `L_x` rather than of the local ring because multiplication by `s` lands in `L`. -/
def mulGerms (x : X) : Set (L.presheaf.stalk x) :=
  {z | ∃ (W : Opens X) (hxW : x ∈ W) (t : Γ(L, W)),
    t ∈ Set.range (ConcreteCategory.hom
        ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op W))) ∧
      L.presheaf.germ W x hxW t = z}

/-- The image of multiplication by `s` on sections is stable under restriction: a value over `W`
restricts to a value over any smaller open set. -/
lemma mem_range_denominatorIdealMul_app_res {W W' : Opens X} (h : W' ≤ W) {t : Γ(L, W)}
    (ht : t ∈ Set.range (ConcreteCategory.hom
      ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op W)))) :
    L.presheaf.map (homOfLE h).op t ∈
      Set.range (ConcreteCategory.hom
        ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op W'))) := by
  obtain ⟨d, rfl⟩ := ht
  exact ⟨(AlgebraicGeometry.denominatorIdeal X L s).val.map (homOfLE h).op d,
    PresheafOfModules.naturality_apply (AlgebraicGeometry.denominatorIdealMul X L s).val
      (homOfLE h).op d⟩

/-- **The germs of the values of multiplication by `s` are the multiples of a trivializing germ
by the fractional product ideal of the germs of the local ratio.** The hypothesis is the
presentation of `Stacks.DenominatorMul.range_denominatorIdealMul_app_basicOpen` on every basic
open of an affine open `V` carrying a basis element `e` and a ratio `a / b` of `s`.

Both inclusions shrink a neighbourhood of `x` to a basic open of `V`, where the presentation is
available: a value of multiplication restricts to one there, and conversely an equation between
germs holds on some neighbourhood, hence on a basic open inside it. -/
theorem mulGerms_eq_smul_image {V : Opens X} (hV : IsAffineOpen V) {a b : Γ(X, V)} {e : Γ(L, V)}
    (hbas : ∀ f : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op (X.basicOpen f)))) =
        (fun y : Γ(X, X.basicOpen f) =>
            y • L.presheaf.map (homOfLE (X.basicOpen_le f)).op e) ''
          {y : Γ(X, X.basicOpen f) | ∃ u : Γ(X, X.basicOpen f),
            y * algebraMap Γ(X, V) Γ(X, X.basicOpen f) b =
              algebraMap Γ(X, V) Γ(X, X.basicOpen f) a * u})
    {x : X} (hx : x ∈ V) :
    mulGerms X L s x =
      (fun y : X.presheaf.stalk x => y • L.presheaf.germ V x hx e) ''
        (Ideal.fractionalProductIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) :
          Set (X.presheaf.stalk x)) := by
  ext z
  constructor
  · rintro ⟨W, hxW, t, ht, rfl⟩
    obtain ⟨f, hfle, hxf⟩ :=
      hV.exists_basicOpen_le (⟨x, ⟨hxW, hx⟩⟩ : (W ⊓ V : Opens X)) hx
    have hleW : X.basicOpen f ≤ W := hfle.trans inf_le_left
    obtain ⟨y, ⟨u, hu⟩, hy⟩ := (Set.ext_iff.mp (hbas f) _).mp
      (mem_range_denominatorIdealMul_app_res X L s hleW ht)
    refine ⟨X.presheaf.germ (X.basicOpen f) x hxf y, ?_, ?_⟩
    · refine SetLike.mem_coe.mpr (Ideal.mem_fractionalProductIdeal_iff.mpr
        ⟨X.presheaf.germ (X.basicOpen f) x hxf u, ?_⟩)
      have hgerm := congrArg (ConcreteCategory.hom (X.presheaf.germ (X.basicOpen f) x hxf)) hu
      rw [map_mul, map_mul, germ_algebraMap_basicOpen X f hx hxf a,
        germ_algebraMap_basicOpen X f hx hxf b] at hgerm
      exact hgerm.trans (mul_comm _ _)
    · rw [← L.presheaf.germ_res_apply (homOfLE hleW) x hxf t, ← hy,
        Scheme.Modules.germ_smul L hxf,
        L.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxf e]
  · rintro ⟨z₀, hz₀, rfl⟩
    obtain ⟨w, hw'⟩ :=
      Ideal.mem_fractionalProductIdeal_iff.mp (SetLike.mem_coe.mp hz₀)
    have hw : z₀ * X.presheaf.germ V x hx b = X.presheaf.germ V x hx a * w :=
      hw'.trans (mul_comm _ _)
    obtain ⟨W₁, hW₁V, hxW₁, z₁, hz₁⟩ := X.presheaf.exists_le_germ_eq z₀ hx
    obtain ⟨W₂, hW₂V, hxW₂, w₂, hw₂⟩ := X.presheaf.exists_le_germ_eq w hx
    have hxW₃ : x ∈ W₁ ⊓ W₂ := ⟨hxW₁, hxW₂⟩
    have hW₃V : W₁ ⊓ W₂ ≤ V := inf_le_left.trans hW₁V
    set z₃ := X.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op z₁
    set w₃ := X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op w₂
    set a₃ := X.presheaf.map (homOfLE hW₃V).op a
    set b₃ := X.presheaf.map (homOfLE hW₃V).op b
    have hgz : X.presheaf.germ (W₁ ⊓ W₂) x hxW₃ z₃ = z₀ :=
      (X.presheaf.germ_res_apply _ x hxW₃ z₁).trans hz₁
    have heq : X.presheaf.germ (W₁ ⊓ W₂) x hxW₃ (z₃ * b₃) =
        X.presheaf.germ (W₁ ⊓ W₂) x hxW₃ (a₃ * w₃) := by
      simp only [z₃, w₃, a₃, b₃, map_mul, X.presheaf.germ_res_apply, hz₁, hw₂]
      exact hw
    obtain ⟨W₄, hxW₄, i₁, i₂, hmap⟩ :=
      X.presheaf.germ_eq x hxW₃ hxW₃ (z₃ * b₃) (a₃ * w₃) heq
    obtain ⟨f, hfle, hxf⟩ := hV.exists_basicOpen_le (⟨x, hxW₄⟩ : W₄) hx
    have hD : X.basicOpen f ≤ W₁ ⊓ W₂ := hfle.trans i₁.le
    have hcollapse : ∀ (i : W₄ ⟶ W₁ ⊓ W₂) (t : Γ(X, W₁ ⊓ W₂)),
        X.presheaf.map (homOfLE hfle).op (X.presheaf.map i.op t) =
          X.presheaf.map (homOfLE hD).op t := by
      intro i t
      rw [← X.presheaf.map_comp_apply]
      rfl
    have hmapD : X.presheaf.map (homOfLE hD).op (z₃ * b₃) =
        X.presheaf.map (homOfLE hD).op (a₃ * w₃) :=
      (hcollapse i₁ _).symm.trans
        ((congrArg (ConcreteCategory.hom (X.presheaf.map (homOfLE hfle).op)) hmap).trans
          (hcollapse i₂ _))
    rw [map_mul, map_mul, res_res X hW₃V hD (X.basicOpen_le f) a,
      res_res X hW₃V hD (X.basicOpen_le f) b] at hmapD
    refine ⟨X.basicOpen f, hxf,
      X.presheaf.map (homOfLE hD).op z₃ •
        L.presheaf.map (homOfLE (X.basicOpen_le f)).op e,
      (Set.ext_iff.mp (hbas f) _).mpr
        ⟨X.presheaf.map (homOfLE hD).op z₃, ⟨X.presheaf.map (homOfLE hD).op w₃, hmapD⟩, rfl⟩,
      ?_⟩
    rw [Scheme.Modules.germ_smul L hxf,
      L.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxf e,
      X.presheaf.germ_res_apply (homOfLE hD) x hxf z₃, hgz]

/-- **The germs of the values of multiplication by `s`, read through the coordinate of a stalk
basis of `L` at the point: they are the fractional product ideal of the germs of the local
ratio.** This is `Stacks.Chow.DenominatorStalk.mulGerms_eq_smul_image` composed with
`Stacks.Divisors.IsStalkBasis.coord`, which identifies `L_x` with the local ring; the ideal is
meaningful only on the local ring, and this is the form a length computation consumes. -/
theorem mem_mulGerms_iff_coord_mem {V : Opens X} (hV : IsAffineOpen V) {a b : Γ(X, V)}
    {e : Γ(L, V)}
    (hbas : ∀ f : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op (X.basicOpen f)))) =
        (fun y : Γ(X, X.basicOpen f) =>
            y • L.presheaf.map (homOfLE (X.basicOpen_le f)).op e) ''
          {y : Γ(X, X.basicOpen f) | ∃ u : Γ(X, X.basicOpen f),
            y * algebraMap Γ(X, V) Γ(X, X.basicOpen f) b =
              algebraMap Γ(X, V) Γ(X, X.basicOpen f) a * u})
    {x : X} (hx : x ∈ V)
    (hm : Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hx e))
    (z : L.presheaf.stalk x) :
    z ∈ mulGerms X L s x ↔
      hm.coord z ∈
        Ideal.fractionalProductIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) := by
  rw [mulGerms_eq_smul_image X L s hV hbas hx]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [hm.coord_smul]
  · exact fun hz => ⟨hm.coord z, hz, hm.smul_coord z⟩

/-- **Around every point of a scheme there is an affine open on which the meromorphic section is
a ratio `a / b` and `L` has a trivializing basis, such that the germs of the two projections of
the ideal of denominators are `Ideal.denominatorIdeal` and `Ideal.fractionalProductIdeal` of the
germs of that ratio.** The two presentations hold for one and the same `a / b`, which is what a
statement comparing the two quotients of [Stacks, Tag 02SW] needs: the length formula of
[Stacks, Tag 02QH] is about the two colon ideals of a single ratio.

The affine open, the ratio and the basis come from
`Stacks.DenominatorMul.exists_affineOpen_denominator_presentations`; the only hypothesis is that
`L` is invertible. -/
theorem exists_affineOpen_stalk_presentations
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧
      ∃ (a b : Γ(X, V)) (e : Γ(L, V))
        (hm : Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hxV e)),
        b ∈ nonZeroDivisors Γ(X, V) ∧
        Ideal.span (germs X L s x) =
            Ideal.denominatorIdeal (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) ∧
          ∀ z : L.presheaf.stalk x, z ∈ mulGerms X L s x ↔
            hm.coord z ∈ Ideal.fractionalProductIdeal
              (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) := by
  obtain ⟨V, hxV, hVaff, a, b, e, hb, hm, hι, hmul⟩ :=
    Stacks.DenominatorMul.exists_affineOpen_denominator_presentations X L s hL x
  exact ⟨V, hxV, hVaff, a, b, e, hm, hb,
    span_germs_eq_denominatorIdeal X L s hVaff hι hxV,
    fun z => mem_mulGerms_iff_coord_mem X L s hVaff hmul hxV hm z⟩

end Stacks.Chow.DenominatorStalk

end
