module

public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise

/-!
# Rigidity of the graded twists on an absolute `Proj`

Let `S` be a nonnegatively graded ring and `X = Proj(S)`. This file proves that the graded
algebra `⨁_{n : ℤ} 𝒪_X(n)` has no nontrivial multiplicative self-maps that fix the sections
coming from homogeneous elements: a family of endomorphisms `α n : 𝒪(n) ⟶ 𝒪(n)` which carries
the canonical product of local sections to the product of their images, and which fixes the
global section `degreeSection 𝒮 k c` attached to every homogeneous element `c` of every
nonnegative degree `k`, consists of identity morphisms.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative`: the family respects the canonical
  product of local sections of the twists, on every open and in all integer degrees.
* `Stacks.AlgebraicGeometry.TwistRigidity.FixesDegreeSections`: the family fixes the global
  section attached to each homogeneous element.

## Main results

* `Stacks.AlgebraicGeometry.TwistRigidity.eq_id`: **the rigidity statement.** A multiplicative
  family fixing the homogeneous sections is the identity in every degree.
* `Stacks.AlgebraicGeometry.TwistRigidity.app_eq_self`: the same on sections, which is what the
  proof produces.
* `Stacks.AlgebraicGeometry.TwistRigidity.app_eq_self_of_values_mkOne`: the step that promotes
  the hypothesis from `degreeSection` to an arbitrary section whose local values are all `a / 1`
  for one homogeneous `a`. This is where the degree bookkeeping is absorbed.

## The route

The argument is generation-and-cancellation, and it has to be: the twist `𝒪(n)` is **not** free
on a standard open `D₊(f)` for general `n` — only `𝒪(n · deg f)` is, which is exactly the
hypothesis shape of `Stacks.AlgebraicGeometry.ProjTrivialization`. So no trivialization is
available to read `α n` through.

Instead, fix a section `t` of `𝒪(n)` over `V` and a point `x` of `V`. By the defining local
condition on sections, `t` is on some `V' ∋ x` the single fraction `β / c` with `c ∈ 𝒮 K` and
`β` in the degree-`K` piece of `S(n)`, i.e. `β ∈ integerGrading 𝒮 (K + n)`. There are two cases
and both are needed.

If `K + n < 0` that piece is the zero submodule, so `β = 0` and `t` restricted to `V'` is the
zero section; `α n` is additive, so it fixes it.

In the remaining case `β` is homogeneous of the nonnegative degree `N = K + n`, and the product of
`degreeSection 𝒮 K c` with `t` is the section of `𝒪(K + n)` over `V'` whose value at every point
is `β / 1` — the computation `mkOne_mul_mk`. That section is fixed by `α (K + n)`, because a
section with those values is the restriction of `degreeSection 𝒮 N β`, which is fixed by
hypothesis. Multiplicativity turns the left-hand side into `degreeSection 𝒮 K c` times
`α n t`, and cancelling the unit `c / 1` pointwise gives `α n t = t` on `V'`, hence at `x`.

No sheaf-gluing step is needed at the end. A section of a twist *is* a dependent function on the
points of the open, subject to a local condition, and restriction of sections is restriction of
functions; so the equality of two sections over `V` is checked at each point of `V` separately,
and each point is handled on its own `V'`.

## Implementation notes

The degree of the numerator is `K + n` as an integer, while `degreeSection` is indexed by a
natural number, and the two indices appear in the *type* of a section. The identification is
therefore made once, in `app_eq_self_of_values_mkOne`, whose integer index is a free variable
that the natural-number index is substituted into; every later step works with the integer index
`K + n` untouched. Attempting the substitution later means rewriting the index of a dependent
type and fails its motive check.

Destructing the local-fraction witness of a section produces an equation whose left-hand side is
the unreduced application of a lambda, on which `rw` does not fire; it is re-ascribed with a
`have` at the reduced form, exactly as in `Stacks.AlgebraicGeometry.ProjTwistEpi`.

## What is not done here

Nothing is said about *existence* of such a family, nor about families that are multiplicative
without fixing the homogeneous sections — for those the conclusion is false in general. Unitality
of the family is **not** assumed and not used: multiplicativity together with the fixed
homogeneous sections already forces the identity, and the unit is itself one of the fixed
sections. Nothing here is about a relative `Proj`; the statement is for one graded ring.

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
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistRigidity

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {𝒜}

/-- The family respects the canonical product of local sections of the twists, on every open
and in all integer degrees. -/
public def IsMultiplicative (α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n) : Prop :=
  ∀ (i j : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj (op V)) (b : (twistingSheaf 𝒜 j).val.obj (op V)),
    (α (i + j)).val.app (op V) (absoluteTwistProduct 𝒜 i j V a b) =
      absoluteTwistProduct 𝒜 i j V ((α i).val.app (op V) a) ((α j).val.app (op V) b)

/-- The family fixes the global section of `𝒪(k)` attached to each homogeneous element of
degree `k`. -/
public def FixesDegreeSections (α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n) : Prop :=
  ∀ (k : ℕ) (c : 𝒜 k),
    (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k c) = degreeSection 𝒜 k c

variable {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n}

/-! ### From `degreeSection` to an arbitrary constant fraction -/

/-- A section of `𝒪(m)` whose value at every point is `a / 1`, for one homogeneous `a` of
degree `N` with `N = m`, is fixed by a family that fixes the homogeneous sections: it is the
restriction of `degreeSection 𝒮 N a`.

This is where the natural-number degree of `a` and the integer index of the twist are
identified, and the identification is made by substituting into the free integer index `m`. -/
public theorem app_eq_self_of_values_mkOne (hfix : FixesDegreeSections α)
    {m : ℤ} {N : ℕ} (hm : (N : ℤ) = m) {a : S} (ha : a ∈ 𝒜 N)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) (s : (twistingSheaf 𝒜 m).val.obj (op V))
    (hs : ∀ y : V,
      s.1 y = LocalizedModule.mk a (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl)) :
    (α m).val.app (op V) s = s := by
  subst hm
  have hres : (twistingSheaf 𝒜 (N : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op
      (degreeSection 𝒜 N ⟨a, ha⟩) = s :=
    Subtype.ext (funext fun y =>
      (degreeSection_apply 𝒜 N ⟨a, ha⟩ ⟨y.1, trivial⟩).trans (hs y).symm)
  rw [← hres, PresheafOfModules.naturality_apply, hfix]

/-! ### One local fraction -/

/-- A family that fixes the homogeneous sections fixes their restrictions. -/
public theorem app_degreeSectionOn (hfix : FixesDegreeSections α) (k : ℕ) {c : S}
    (hc : c ∈ 𝒜 k) (V : Opens (ProjectiveSpectrum.top 𝒜)) :
    (α (k : ℤ)).val.app (op V) (degreeSectionOn 𝒜 k hc V) = degreeSectionOn 𝒜 k hc V := by
  refine Eq.trans (PresheafOfModules.naturality_apply (α (k : ℤ)).val
    (homOfLE (le_top : V ≤ ⊤)).op (degreeSection 𝒜 k ⟨c, hc⟩)) ?_
  rw [hfix]
  rfl

/-- **The generation-and-cancellation step, nonnegative case.** A section of `𝒪(n)` given on
the whole of its open by a single homogeneous fraction `β / c` whose numerator has nonnegative
degree is fixed: multiplying by the homogeneous section of `c` clears the denominator, the
result is fixed because its values are all `β / 1`, and the unit `c / 1` cancels. -/
public theorem app_eq_self_of_isFraction_nonneg (hmul : IsMultiplicative α)
    (hfix : FixesDegreeSections α) (n : ℤ) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf 𝒜 n).val.obj (op V)) {K N : ℕ} {β c : S}
    (hN : (N : ℤ) = (K : ℤ) + n) (hβ : β ∈ 𝒜 N) (hc : c ∈ 𝒜 K)
    (hnv : ∀ y : V, c ∉ y.1.asHomogeneousIdeal)
    (hval : ∀ y : V, t.1 y = LocalizedModule.mk β ⟨c, hnv y⟩) :
    (α n).val.app (op V) t = t := by
  have hfixed : (α ((K : ℤ) + n)).val.app (op V)
      (absoluteTwistProduct 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) t) =
      absoluteTwistProduct 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) t :=
    app_eq_self_of_values_mkOne hfix hN hβ V
      (absoluteTwistProduct 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) t)
      (degreeSectionOn_mul_apply 𝒜 K hc n V t hnv hval)
  have hmul' := hmul (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) t
  rw [app_degreeSectionOn hfix K hc V] at hmul'
  refine Subtype.ext (funext fun y => ?_)
  have hprod : ∀ u : (twistingSheaf 𝒜 n).val.obj (op V),
      (absoluteTwistProduct 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) u).1 y =
        LocalizedModule.mk c (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl) * u.1 y := fun u =>
    (absoluteTwistProduct_apply 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) u y).trans
      (by rw [degreeSectionOn_apply 𝒜 K hc V y])
  refine eq_of_mkOne_mul_eq _ (hnv y) ?_
  calc LocalizedModule.mk c (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl) *
          ((α n).val.app (op V) t).1 y
      = (absoluteTwistProduct 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V)
          ((α n).val.app (op V) t)).1 y := (hprod _).symm
    _ = ((α ((K : ℤ) + n)).val.app (op V)
          (absoluteTwistProduct 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) t)).1 y :=
          (twist_val_congr 𝒜 hmul' y).symm
    _ = (absoluteTwistProduct 𝒜 (K : ℤ) n V (degreeSectionOn 𝒜 K hc V) t).1 y :=
          twist_val_congr 𝒜 hfixed y
    _ = _ := hprod t

/-- **The generation-and-cancellation step.** A section of `𝒪(n)` which is given on the whole
of its open by a single homogeneous fraction `β / c` is fixed. If the numerator's degree
`K + n` is negative the numerator lies in the zero submodule and the section vanishes;
in the remaining case this is `app_eq_self_of_isFraction_nonneg`. -/
public theorem app_eq_self_of_isFraction (hmul : IsMultiplicative α)
    (hfix : FixesDegreeSections α) (n : ℤ) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf 𝒜 n).val.obj (op V)) {K : ℕ} {β c : S}
    (hβ : β ∈ twistGrading (S := S) 𝒜 n (K : ℤ)) (hc : c ∈ 𝒜 K)
    (hnv : ∀ y : V, c ∉ y.1.asHomogeneousIdeal)
    (hval : ∀ y : V, t.1 y = LocalizedModule.mk β ⟨c, hnv y⟩) :
    (α n).val.app (op V) t = t := by
  have hmem : β ∈ integerGrading (S := S) 𝒜 ((K : ℤ) + n) := hβ
  rcases le_or_gt 0 ((K : ℤ) + n) with hKn | hKn
  · have hβ' : β ∈ 𝒜 ((K : ℤ) + n).toNat := by simpa [integerGrading, hKn] using hmem
    exact app_eq_self_of_isFraction_nonneg hmul hfix n V t
      (Int.toNat_of_nonneg hKn) hβ' hc hnv hval
  · have hβ0 : β = 0 := by simpa [integerGrading, not_le.mpr hKn] using hmem
    have ht0 : t = 0 := by
      refine Subtype.ext (funext fun y => ?_)
      exact show t.1 y = 0 by rw [hval y, hβ0]; simp
    rw [ht0, map_zero]

/-! ### The rigidity statement -/

/-- **Rigidity on sections.** A multiplicative family of endomorphisms of the twists that fixes
the homogeneous sections fixes every local section. -/
public theorem app_eq_self (hmul : IsMultiplicative α)
    (hfix : FixesDegreeSections α) (n : ℤ) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf 𝒜 n).val.obj (op V)) :
    (α n).val.app (op V) t = t := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨V', hxV', i, K, β, c, hβ, hc, hnv, heq⟩ := t.2 x
  have hval : ∀ y : V',
      ((twistingSheaf 𝒜 n).val.map i.op t).1 y = LocalizedModule.mk β ⟨c, hnv y⟩ :=
    heq
  have hnat : (α n).val.app (op V') ((twistingSheaf 𝒜 n).val.map i.op t) =
      (twistingSheaf 𝒜 n).val.map i.op ((α n).val.app (op V) t) :=
    PresheafOfModules.naturality_apply (α n).val i.op t
  calc ((α n).val.app (op V) t).1 x
      = ((twistingSheaf 𝒜 n).val.map i.op
          ((α n).val.app (op V) t)).1 ⟨x.1, hxV'⟩ := rfl
    _ = ((α n).val.app (op V') ((twistingSheaf 𝒜 n).val.map i.op t)).1
          ⟨x.1, hxV'⟩ := twist_val_congr 𝒜 hnat.symm _
    _ = ((twistingSheaf 𝒜 n).val.map i.op t).1 ⟨x.1, hxV'⟩ :=
          twist_val_congr 𝒜 (app_eq_self_of_isFraction hmul hfix n V' _ hβ hc hnv hval) _
    _ = t.1 x := rfl

/-- **Rigidity.** A multiplicative family of endomorphisms of the twists on `Proj S` which
fixes the global section attached to every homogeneous element is the identity in every integer
degree. -/
public theorem eq_id (hmul : IsMultiplicative α)
    (hfix : FixesDegreeSections α) (n : ℤ) : α n = 𝟙 (twistingSheaf 𝒜 n) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun t => app_eq_self hmul hfix n V.unop t))

end Stacks.AlgebraicGeometry.TwistRigidity

end
