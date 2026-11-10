module

public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Basic

/-!
# Rigidity of the graded twists relative to a graded ring homomorphism

`Stacks.AlgebraicGeometry.TwistRigidity.eq_id` forces a multiplicative family of endomorphisms
of the twists on `Proj 𝒜` to be the identity once it fixes the global section
`degreeSection 𝒜 k c` attached to **every** homogeneous `c`. This file weakens that hypothesis
to the homogeneous elements in the image of a graded ring homomorphism `ψ : ℬ →+*ᵍ 𝒜`, at the
price of one extra input: the image of `ψ` must *generate* `𝒜` pointwise, in the sense that
every homogeneous `a` becomes an image of `ψ` after multiplication by a degree-zero image of `ψ`
which does not vanish at a prescribed point of `Proj 𝒜`. The multiplier may be chosen anew at
each point, and `ψ` need not be surjective in any degree.

That is exactly the shape in which the geometric input is available: for a nested pair of affine
opens `U ⊆ V` of the base of a quasi-coherent graded algebra, `Γ(V, A_k) → Γ(U, A_k)` is **not**
surjective, but it becomes surjective after inverting any function cutting out a basic open of
`V` inside `U`, and such functions generate the unit ideal of `Γ(U, 𝒪)`. The consequence for a
nested affine pair is
`StacksFrontier/AlgebraicGeometry/RelativeTwistRigidity/Basic.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.FixesResDegreeSections`: the relative fixing
  hypothesis — the family fixes the homogeneous global sections attached to the images of `ψ`.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.Generates`: pointwise degreewise generation.

## Main results

* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id`: **relative rigidity.** A
  multiplicative family satisfying the relative fixing hypothesis for a generating `ψ` is the
  identity in every integer degree.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.fixesDegreeSections`: generation upgrades the
  relative fixing hypothesis to the absolute one, which is what the absolute statement consumes.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.fixesDegreeSections_of_forall_point`: the
  criterion with the generating data spelled out, free of any ring homomorphism.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.app_degreeSection_apply`: the cancellation
  step, which is the whole content.

## The route

**No covering argument on `Proj 𝒜` is needed, and that is the design.** The absolute hypothesis
`FixesDegreeSections` asserts an equality of two *global* sections of `𝒪(k)`, and a section of a
twist is a dependent function on the points subject to a local condition; so the equality is
checked at each point separately, by `fixesDegreeSections_of_apply`. The multiplier `g` may
therefore depend on the point, which is what makes the hypothesis reachable — a single `g`
working for all points would amount to surjectivity of `ψ` up to one denominator, which is false.

At a fixed point `x` and for a fixed homogeneous `a` of degree `k`, pick `g` of degree `0` with
`g ∉ x` such that both `g` and `a * g` have fixed homogeneous sections. The canonical product of
`degreeSection 𝒜 k a` with `degreeSection 𝒜 0 g` is a section of `𝒪(k + 0)` whose value at every
point is `(a * g) / 1`, so it is the restriction of `degreeSection 𝒜 k (a * g)` and is fixed.
Multiplicativity turns the family applied to that product into the product of the two images;
the second factor is fixed by hypothesis, and `g / 1` is a unit of the local ring at `x` because
`g ∉ x`. Cancelling it gives the value of the family at `degreeSection 𝒜 k a` back.

## Implementation notes

**The degree arithmetic is routed through the free integer index, not through a cast.** The
product above lives in `𝒪(↑k + ↑(0 : ℕ))` and the section it is compared to lives in `𝒪(↑k)`.
Rather than identify the two indices — which means rewriting the index of a dependent type —
`app_eq_self_of_values_mkOne'` keeps the integer index a free variable `m` with `(N : ℤ) = m` as
a hypothesis and substitutes into it, exactly as
`Stacks.AlgebraicGeometry.TwistRigidity.app_eq_self_of_values_mkOne` does. The natural-number
side uses `a * g` rather than `g * a` so that the degree is `k + 0`, which is definitional,
instead of `0 + k`, which is not.

That lemma is a copy of the absolute one with its hypothesis specialized from
`FixesDegreeSections` to the single global section it actually uses. The specialization is the
point: the absolute version cannot be invoked here, since the absolute hypothesis is what is
being proved.

**`rw` is unusable on the sheaf-morphism equalities.** Rewriting with
`hfixg : (α 0).val.app (op ⊤) (degreeSection 𝒜 0 ⟨g, hg⟩) = degreeSection 𝒜 0 ⟨g, hg⟩` inside a
goal whose displayed subterm is character-for-character that left-hand side fails to find the
pattern: the two spellings of the base ring sheaf are `rfl`-equal but are different terms in the
`Category` instance argument. The same holds for `absoluteTwistProduct_apply`, whose point
argument is typed by `(AlgebraicGeometry.Proj 𝒜).Opens` while the goal's is typed by
`Opens (ProjectiveSpectrum.top 𝒜)`. Both are therefore applied in term mode, by `Eq.trans`,
where the conversion is free; only equalities between *values* — elements of one local ring —
are rewritten.

**The sheaf-side reasoning is kept in this file on purpose.** The
criterion is stated for a variable graded ring. Instantiated at the section ring of a
quasi-coherent graded algebra over an affine open, the existential goal of
`fixesDegreeSections_of_forall_point` costs more than the whole heartbeat budget for *any*
tactic that touches it: after `refine fixesDegreeSections_of_forall_point hmul fun k a x => ?_`
even `obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 0 := ⟨0, rfl⟩` times out at `isDefEq`, while `have hq := …`
on the same proof term costs nothing. So the destructuring lives here, where the graded ring is
a variable, and the only thing crossing into the concrete instance is `Generates ψ` — a
statement about ring elements and a prime ideal, with no sheaf in it. Stating the criterion with
the generating data as a bare existential and destructuring it at the concrete instance does
not elaborate.

## What is not done here

Nothing is said about *existence* of a generating `ψ`, nor about families that satisfy the
relative fixing hypothesis for a `ψ` that does not generate — for those the conclusion is false
in general, since the absolute statement's own proof consumes an arbitrary homogeneous numerator
and denominator. Unitality of the family is not assumed and not used.

Nothing here is about a relative `Proj`: the statement is for one graded ring together with one
homomorphism into it.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.TwistRigidity

namespace Stacks.AlgebraicGeometry.RelativeTwistRigidity

universe u u' w w'

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible]
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The product of two fractions with denominator `1`. -/
public theorem mkOne_mul_mkOne (P : Submonoid R) (a b : R) :
    LocalizedModule.mk a (1 : P) * LocalizedModule.mk b (1 : P)
      = LocalizedModule.mk (a * b) (1 : P) := by
  change Localization.mk a (1 : P) * Localization.mk b (1 : P) = Localization.mk (a * b) (1 : P)
  rw [Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- Cancellation on the right against a fraction with denominator `1`. -/
public theorem eq_of_mul_mkOne_eq (P : Submonoid R) {c : R} (hc : c ∈ P)
    {u v : LocalizedModule P R}
    (h : u * LocalizedModule.mk c (1 : P) = v * LocalizedModule.mk c (1 : P)) : u = v :=
  (isUnit_mkOne P hc).mul_right_cancel h

variable {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n}

/-- A section whose value at every point is `a / 1` is fixed, provided only that the one global
section `degreeSection 𝒜 N a` is. -/
public theorem app_eq_self_of_values_mkOne' {m : ℤ} {N : ℕ} (hm : (N : ℤ) = m) {a : R}
    (ha : a ∈ 𝒜 N)
    (hfix : (α (N : ℤ)).val.app (op ⊤) (degreeSection 𝒜 N ⟨a, ha⟩) = degreeSection 𝒜 N ⟨a, ha⟩)
    (W : Opens (ProjectiveSpectrum.top 𝒜)) (s : (twistingSheaf 𝒜 m).val.obj (op W))
    (hs : ∀ y : W,
      s.1 y = LocalizedModule.mk a (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl)) :
    (α m).val.app (op W) s = s := by
  subst hm
  have hres : (twistingSheaf 𝒜 (N : ℤ)).val.map (homOfLE (le_top : W ≤ ⊤)).op
      (degreeSection 𝒜 N ⟨a, ha⟩) = s :=
    Subtype.ext (funext fun y =>
      (degreeSection_apply 𝒜 N ⟨a, ha⟩ ⟨y.1, trivial⟩).trans (hs y).symm)
  rw [← hres, PresheafOfModules.naturality_apply, hfix]

/-- **The cancellation step of relative rigidity.** -/
public theorem app_degreeSection_apply (hmul : IsMultiplicative α) (k : ℕ) (a : 𝒜 k)
    {g : R} (hg : g ∈ 𝒜 0)
    (hfixg : (α ((0 : ℕ) : ℤ)).val.app (op ⊤) (degreeSection 𝒜 0 ⟨g, hg⟩)
      = degreeSection 𝒜 0 ⟨g, hg⟩)
    (hag : (a : R) * g ∈ 𝒜 k)
    (hfixag : (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k ⟨(a : R) * g, hag⟩)
      = degreeSection 𝒜 k ⟨(a : R) * g, hag⟩)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)))
    (hx : g ∉ x.1.asHomogeneousIdeal) :
    ((α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k a)).1 x = (degreeSection 𝒜 k a).1 x := by
  have hs : ∀ y : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)),
      (absoluteTwistProduct 𝒜 (k : ℤ) ((0 : ℕ) : ℤ) ⊤ (degreeSection 𝒜 k a)
        (degreeSection 𝒜 0 ⟨g, hg⟩)).1 y =
      LocalizedModule.mk ((a : R) * g)
        (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
    intro y
    refine Eq.trans (absoluteTwistProduct_apply 𝒜 (k : ℤ) ((0 : ℕ) : ℤ) ⊤ _ _ y) ?_
    rw [degreeSection_apply 𝒜 k a ⟨y.1, trivial⟩,
      degreeSection_apply 𝒜 0 ⟨g, hg⟩ ⟨y.1, trivial⟩]
    exact mkOne_mul_mkOne _ _ _
  have h1 := app_eq_self_of_values_mkOne' (α := α)
    (m := (k : ℤ) + ((0 : ℕ) : ℤ)) (N := k) (by simp) hag hfixag ⊤ _ hs
  have h2 := hmul (k : ℤ) ((0 : ℕ) : ℤ) ⊤ (degreeSection 𝒜 k a) (degreeSection 𝒜 0 ⟨g, hg⟩)
  have h4 : ((α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k a)).1 x *
        ((α ((0 : ℕ) : ℤ)).val.app (op ⊤) (degreeSection 𝒜 0 ⟨g, hg⟩)).1 x =
      (degreeSection 𝒜 k a).1 x * (degreeSection 𝒜 0 ⟨g, hg⟩).1 x :=
    (absoluteTwistProduct_apply 𝒜 (k : ℤ) ((0 : ℕ) : ℤ) ⊤ _ _ x).symm.trans
      ((twist_val_congr 𝒜 (h2.symm.trans h1) x).trans
        (absoluteTwistProduct_apply 𝒜 (k : ℤ) ((0 : ℕ) : ℤ) ⊤ _ _ x))
  have hax : (degreeSection 𝒜 0 ⟨g, hg⟩).1 x =
      LocalizedModule.mk g (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    degreeSection_apply 𝒜 0 ⟨g, hg⟩ ⟨x.1, trivial⟩
  refine eq_of_mul_mkOne_eq _ hx ?_
  exact (congrArg (HMul.hMul _) ((twist_val_congr 𝒜 hfixg x).trans hax)).symm.trans
    (h4.trans (congrArg (HMul.hMul _) hax))

/-- Fixing the homogeneous global sections is a pointwise condition. -/
public theorem fixesDegreeSections_of_apply
    (hpt : ∀ (k : ℕ) (a : 𝒜 k) (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒜))),
      ((α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k a)).1 x = (degreeSection 𝒜 k a).1 x) :
    FixesDegreeSections α :=
  fun k c => Subtype.ext (funext fun x => hpt k c x)

/-- **The rigidity criterion.** A multiplicative family is the identity as soon as, at every
point and for every homogeneous element `a`, there is a degree-zero element `g` nonvanishing at
that point such that the family fixes both the homogeneous section of `g` and that of `a * g`.

Nothing is assumed about the homogeneous section of `a` itself, which is the whole point: the
elements whose sections are known to be fixed need only generate the others up to a
nonvanishing degree-zero factor, chosen anew at each point. -/
public theorem fixesDegreeSections_of_forall_point (hmul : IsMultiplicative α)
    (hgen : ∀ (k : ℕ) (a : 𝒜 k) (x : ProjectiveSpectrum 𝒜),
      ∃ (g : R) (hg : g ∈ 𝒜 0) (hag : (a : R) * g ∈ 𝒜 k), g ∉ x.asHomogeneousIdeal ∧
        (α ((0 : ℕ) : ℤ)).val.app (op ⊤) (degreeSection 𝒜 0 ⟨g, hg⟩) =
          degreeSection 𝒜 0 ⟨g, hg⟩ ∧
        (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k ⟨(a : R) * g, hag⟩) =
          degreeSection 𝒜 k ⟨(a : R) * g, hag⟩) :
    FixesDegreeSections α := by
  refine fixesDegreeSections_of_apply fun k a x => ?_
  obtain ⟨g, hg, hag, hnv, hfixg, hfixag⟩ := hgen k a x.1
  exact app_degreeSection_apply hmul k a hg hfixg hag hfixag x hnv

/-! ### Rigidity relative to a graded ring homomorphism -/

variable {R' : Type u'} {σ' : Type w'} [CommRing R'] [SetLike σ' R'] [AddSubgroupClass σ' R']
  {ℬ : ℕ → σ'} [GradedRing ℬ]

/-- **The relative fixing hypothesis.** The family fixes the global section of `𝒪(k)` on
`Proj 𝒜` attached to the image under `ψ` of every homogeneous element of degree `k` of `ℬ`. -/
public def FixesResDegreeSections (ψ : ℬ →+*ᵍ 𝒜)
    (α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n) : Prop :=
  ∀ (k : ℕ) (c : ℬ k),
    (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k ⟨ψ c, ψ.map_mem c.2⟩) =
      degreeSection 𝒜 k ⟨ψ c, ψ.map_mem c.2⟩

/-- **Pointwise degreewise generation.** Every homogeneous element of `𝒜` becomes an image of
`ψ` after multiplication by a degree-zero image of `ψ` which, at a prescribed point of
`Proj 𝒜`, does not vanish. The multiplier may be chosen anew at each point; `ψ` itself need not
be surjective in any degree. -/
public def Generates (ψ : ℬ →+*ᵍ 𝒜) : Prop :=
  ∀ (k : ℕ) (a : 𝒜 k) (x : ProjectiveSpectrum 𝒜),
    ∃ (d : ℬ 0) (c : ℬ k), (ψ (d : R') : R) ∉ x.asHomogeneousIdeal ∧
      (a : R) * ψ (d : R') = ψ (c : R')

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
/-- The relative fixing hypothesis, read at an element presented as an image of `ψ`. -/
public theorem fixes_of_eq_res {ψ : ℬ →+*ᵍ 𝒜} (hfix : FixesResDegreeSections ψ α) (k : ℕ)
    (c : ℬ k) (w : 𝒜 k) (hwc : (w : R) = ψ (c : R')) :
    (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k w) = degreeSection 𝒜 k w := by
  obtain rfl : w = ⟨ψ c, ψ.map_mem c.2⟩ := Subtype.ext hwc
  exact hfix k c

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
/-- **Relative rigidity on the homogeneous sections.** Generation plus the relative fixing
hypothesis force the absolute one. -/
public theorem fixesDegreeSections {ψ : ℬ →+*ᵍ 𝒜} (hmul : IsMultiplicative α)
    (hgen : Generates ψ) (hfix : FixesResDegreeSections ψ α) : FixesDegreeSections α := by
  refine fixesDegreeSections_of_forall_point hmul fun k a x => ?_
  obtain ⟨d, c, hnv, heq⟩ := hgen k a x
  have hag : (a : R) * ψ (d : R') ∈ 𝒜 k := heq ▸ ψ.map_mem c.2
  exact ⟨ψ (d : R'), ψ.map_mem d.2, hag, hnv, hfix 0 d,
    fixes_of_eq_res hfix k c ⟨(a : R) * ψ (d : R'), hag⟩ heq⟩

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
/-- **Relative rigidity.** A multiplicative family of endomorphisms of the twists on `Proj 𝒜`
which fixes the homogeneous global sections attached to the images of a graded ring
homomorphism `ψ : ℬ →+*ᵍ 𝒜` is the identity in every integer degree, provided only that `ψ`
generates `𝒜` pointwise in the sense of
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.Generates`. -/
public theorem eq_id {ψ : ℬ →+*ᵍ 𝒜} (hmul : IsMultiplicative α) (hgen : Generates ψ)
    (hfix : FixesResDegreeSections ψ α) (n : ℤ) : α n = 𝟙 (twistingSheaf 𝒜 n) :=
  _root_.Stacks.AlgebraicGeometry.TwistRigidity.eq_id hmul
    (fixesDegreeSections hmul hgen hfix) n

end Stacks.AlgebraicGeometry.RelativeTwistRigidity

end
