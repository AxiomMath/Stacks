module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Irreducible
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsLength
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower

/-!
# The measure of [Stacks, Tag 0C1L] is additive along an intermediate factorization

The measure the splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` needs is the length of
`f_*𝒪_{X'}/𝒪_X`, and the first of its three parts is additivity along

`0 ⟶ 𝒜/𝒪_X ⟶ f_*𝒪_{X'}/𝒪_X ⟶ f_*𝒪_{X'}/𝒜 ⟶ 0`

for an intermediate `𝒪_X ⊂ 𝒜 ⊂ f_*𝒪_{X'}`. **This file proves that additivity**, point by
point, in the `ℕ`-valued form the induction reads the measure in, and reduces the *strictness*
of the drop at either end to the single question of whether the corresponding cokernel has a
nonvanishing stalk — which at the upper end is properness of `𝒜 ⊂ f_*𝒪_{X'}`.

Nothing here is specific to the structure sheaf: the statements are about an arbitrary
composable pair of monomorphisms of `𝒪_X`-modules, and the geometric corollaries below are the
case `𝒪_X ⟶ 𝒜 ⟶ f_*𝒪_{X'}` with the finiteness of the length discharged from
`Stacks.GlueSquishFactor.isFiniteLength_stalk_cokernel_structureUnitHom`.

## Main results

* `Stacks.GlueSquishFactor.length_stalk_cokernel_comp_add` — **the additivity of the stalk
  length**: for composable monomorphisms `a : F ⟶ G`, `b : G ⟶ H` of `𝒪_X`-modules, the length of
  the stalk of `H/F` is the sum of those of `G/F` and `H/G`.
* `Stacks.GlueSquishFactor.isFiniteLength_stalk_cokernel_of_comp_left` and
  `...isFiniteLength_stalk_cokernel_of_comp_right` — finiteness of the length of `H/F` at a point
  gives it for both halves. So the finiteness proved for `f_*𝒪_{X'}/𝒪_X` covers *every*
  intermediate factorization at once, and neither half needs its own argument.
* `Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_comp_add` — the same additivity for
  `Stacks.Chow.sheafMultiplicity`, the `ℕ`-valued reading of the length, whose only hypothesis is
  finiteness of the length of `H/F`.
* `Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_lt_of_mem_supp_right` and
  `...sheafMultiplicity_cokernel_lt_of_mem_supp_left` — **the strict drops**: the multiplicity of
  `G/F` is strictly below that of `H/F` at any point of the support of `H/G`, and symmetrically.
* `Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_add` and
  `...sheafMultiplicity_cokernel_structureUnitHom_lt_of_mem_supp_right` — the two preceding
  statements for `𝒪_X ⟶ 𝒜 ⟶ f_*𝒪_{X'}` under the hypotheses of [Stacks, Tag 0C1L], with the
  finiteness hypothesis discharged.

## Implementation notes

**Both halves are reused, neither is rebuilt.** The short exact sequence of cokernels is
`Stacks.Abelian.cokernelCompShortComplex_shortExact`, the third isomorphism theorem in an
abelian category, already in the tree for the adic quotient tower of sheaves of modules; and
additivity of the stalk length along a short exact sequence of modules on a scheme is
`AlgebraicGeometry.length_stalk_add_of_shortExact`, proved for [Stacks, Tag 0AYW]. `X.Modules`
is abelian, so the first applies to it with no further work, and the whole of the additivity is
their composition. The monomorphy hypothesis `Mono a` of the third isomorphism theorem is not an
extra demand here: `CategoryTheory.mono_of_mono` derives it from `Mono (a ≫ b)`, which is the
form in which [Stacks, Tag 0C1L] carries `𝒪_X ⊂ f_*𝒪_{X'}`.

**What the strict drops still need, and it is not here.** The induction of
`Stacks.GlueSquishFactor.isElementaryChain_of_split` needs the measure of *each* half to be
strictly below that of `f`, where the measure is a sum over the points of the respective scheme.
Two things separate the statements below from that:

* the measure of the upper half `X' ⟶ Spec_X(𝒜)` is a sum of lengths over the local rings of
  `Spec_X(𝒜)`, not over those of `X`; carrying it across is the fibre sum, for which
  `Stacks.Length.length_eq_sum_length_localizedModule` is the ring-theoretic statement. The
  cokernel `f_*𝒪_{X'}/𝒜` whose stalk lengths appear below is the push-down to `X` of that
  quotient, so no fibre sum enters *these* statements; it enters the comparison with the measure
  of `X' ⟶ Spec_X(𝒜)` computed on `Spec_X(𝒜)`.
* the hypothesis `x ∈ SheafOfModules.supp (cokernel b)` of the strict drop at the upper end is
  exactly properness of `𝒜 ⊂ f_*𝒪_{X'}` localized at `x`. **A producer now supplies it**:
  `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel` in
  `StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsSupport`, which spreads out the
  proper stalk subalgebra of
  `StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SpreadOutSubalgebra` and then converts
  the resulting section-level inequality `C.obj U ≠ ⊤` into a point of the support. The older
  producers `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem` and
  `Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_section` do not: they give a subalgebra
  large enough to contain a prescribed section, never one that is proper.

## No stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** These statements are inputs to the
splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`, which is still unproved; on their own
they assert no part of the lemma.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-! ### Additivity of the stalk length -/

/-- **The stalk length is additive along a composable pair of monomorphisms of modules.** For
`a : F ⟶ G` and `b : G ⟶ H` monomorphisms of `𝒪_X`-modules, the length of the stalk of `H/F` at a
point is the sum of the lengths of the stalks of `G/F` and `H/G` there.

The short exact sequence `0 ⟶ G/F ⟶ H/F ⟶ H/G ⟶ 0` is the third isomorphism theorem
`Stacks.Abelian.cokernelCompShortComplex_shortExact`, applied in the abelian category
`X.Modules`, and the additivity of the length of a stalk along a short exact sequence is
`AlgebraicGeometry.length_stalk_add_of_shortExact`. -/
theorem length_stalk_cokernel_comp_add {X : Scheme.{u}} {F G H : X.Modules} (a : F ⟶ G)
    (b : G ⟶ H) [Mono a] [Mono b] (x : X) :
    Module.length (X.presheaf.stalk x) ((cokernel (a ≫ b)).presheaf.stalk x) =
      Module.length (X.presheaf.stalk x) ((cokernel a).presheaf.stalk x) +
        Module.length (X.presheaf.stalk x) ((cokernel b).presheaf.stalk x) :=
  AlgebraicGeometry.length_stalk_add_of_shortExact
    (Stacks.Abelian.cokernelCompShortComplex_shortExact a b) x

/-- Finiteness of the length of the whole quotient gives it for both halves: a summand of a sum
which is not `⊤` is not `⊤`. -/
private theorem isFiniteLength_stalk_cokernel_comp {X : Scheme.{u}} {F G H : X.Modules}
    (a : F ⟶ G) (b : G ⟶ H) [Mono a] [Mono b] {x : X}
    (h : IsFiniteLength (X.presheaf.stalk x) ((cokernel (a ≫ b)).presheaf.stalk x)) :
    IsFiniteLength (X.presheaf.stalk x) ((cokernel a).presheaf.stalk x) ∧
      IsFiniteLength (X.presheaf.stalk x) ((cokernel b).presheaf.stalk x) := by
  have := Module.length_ne_top_iff.mpr h
  rw [length_stalk_cokernel_comp_add a b x, ne_eq, ENat.add_eq_top, not_or] at this
  exact ⟨Module.length_ne_top_iff.mp this.1, Module.length_ne_top_iff.mp this.2⟩

/-- **Finiteness of the length of the whole quotient gives it for the lower half.** A summand of
a sum which is not `⊤` is not `⊤`. -/
theorem isFiniteLength_stalk_cokernel_of_comp_left {X : Scheme.{u}} {F G H : X.Modules}
    (a : F ⟶ G) (b : G ⟶ H) [Mono a] [Mono b] {x : X}
    (h : IsFiniteLength (X.presheaf.stalk x) ((cokernel (a ≫ b)).presheaf.stalk x)) :
    IsFiniteLength (X.presheaf.stalk x) ((cokernel a).presheaf.stalk x) :=
  (isFiniteLength_stalk_cokernel_comp a b h).1

/-- **Finiteness of the length of the whole quotient gives it for the upper half.** -/
theorem isFiniteLength_stalk_cokernel_of_comp_right {X : Scheme.{u}} {F G H : X.Modules}
    (a : F ⟶ G) (b : G ⟶ H) [Mono a] [Mono b] {x : X}
    (h : IsFiniteLength (X.presheaf.stalk x) ((cokernel (a ≫ b)).presheaf.stalk x)) :
    IsFiniteLength (X.presheaf.stalk x) ((cokernel b).presheaf.stalk x) :=
  (isFiniteLength_stalk_cokernel_comp a b h).2

/-! ### Additivity of the multiplicity -/

/-- **The multiplicity is additive along a composable pair of monomorphisms of modules.** This is
`Stacks.GlueSquishFactor.length_stalk_cokernel_comp_add` read through `ENat.toNat`, which is
faithful on sums of finite lengths; finiteness of the length of `H/F` is the only hypothesis,
because it carries over to both halves. -/
theorem sheafMultiplicity_cokernel_comp_add {X : Scheme.{u}} {F G H : X.Modules} (a : F ⟶ G)
    (b : G ⟶ H) [Mono a] [Mono b] {x : X}
    (h : IsFiniteLength (X.presheaf.stalk x) ((cokernel (a ≫ b)).presheaf.stalk x)) :
    Stacks.Chow.sheafMultiplicity (cokernel (a ≫ b)) x =
      Stacks.Chow.sheafMultiplicity (cokernel a) x +
        Stacks.Chow.sheafMultiplicity (cokernel b) x := by
  have hleft := Module.length_ne_top_iff.mpr (isFiniteLength_stalk_cokernel_of_comp_left a b h)
  have hright := Module.length_ne_top_iff.mpr (isFiniteLength_stalk_cokernel_of_comp_right a b h)
  simp only [Stacks.Chow.sheafMultiplicity, length_stalk_cokernel_comp_add a b x]
  rw [ENat.toNat_add hleft hright]
  push_cast
  ring

/-- **The strict drop at the upper end.** At a point where `H/G` does not vanish, the
multiplicity of `G/F` is strictly below that of `H/F`.

For `𝒪_X ⟶ 𝒜 ⟶ f_*𝒪_{X'}` the hypothesis is that `𝒜 ⊂ f_*𝒪_{X'}` is proper at `x`; this is the
clause of the splitting hypothesis of [Stacks, Tag 0C1L] that no producer in the tree supplies,
see the implementation notes of this file. -/
theorem sheafMultiplicity_cokernel_lt_of_mem_supp_right {X : Scheme.{u}} {F G H : X.Modules}
    (a : F ⟶ G) (b : G ⟶ H) [Mono a] [Mono b] {x : X}
    (h : IsFiniteLength (X.presheaf.stalk x) ((cokernel (a ≫ b)).presheaf.stalk x))
    (hb : x ∈ SheafOfModules.supp (cokernel b)) :
    Stacks.Chow.sheafMultiplicity (cokernel a) x <
      Stacks.Chow.sheafMultiplicity (cokernel (a ≫ b)) x := by
  have hpos := Stacks.Chow.sheafMultiplicity_pos_of_mem_supp (cokernel b)
    (isFiniteLength_stalk_cokernel_of_comp_right a b h) hb
  rw [sheafMultiplicity_cokernel_comp_add a b h]
  omega

/-- **The strict drop at the lower end.** At a point where `G/F` does not vanish, the
multiplicity of `H/G` is strictly below that of `H/F`. For `𝒪_X ⟶ 𝒜 ⟶ f_*𝒪_{X'}` the hypothesis
is that `𝒪_X ⊂ 𝒜` is proper at `x`, which is what the capture clause of
`Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_section` is for. -/
theorem sheafMultiplicity_cokernel_lt_of_mem_supp_left {X : Scheme.{u}} {F G H : X.Modules}
    (a : F ⟶ G) (b : G ⟶ H) [Mono a] [Mono b] {x : X}
    (h : IsFiniteLength (X.presheaf.stalk x) ((cokernel (a ≫ b)).presheaf.stalk x))
    (ha : x ∈ SheafOfModules.supp (cokernel a)) :
    Stacks.Chow.sheafMultiplicity (cokernel b) x <
      Stacks.Chow.sheafMultiplicity (cokernel (a ≫ b)) x := by
  have hpos := Stacks.Chow.sheafMultiplicity_pos_of_mem_supp (cokernel a)
    (isFiniteLength_stalk_cokernel_of_comp_left a b h) ha
  rw [sheafMultiplicity_cokernel_comp_add a b h]
  omega

/-! ### The two statements for `𝒪_X ⊂ 𝒜 ⊂ f_*𝒪_{X'}` -/

/-- **Additivity of the measure of [Stacks, Tag 0C1L] along an intermediate factorization.** Let
`f : X' ⟶ X` be a morphism of `k`-schemes with `X` locally of finite type over `k`, an
isomorphism over an open `U` with finite complement, and with `f_*𝒪_{X'}/𝒪_X` coherent — the
hypotheses of `Stacks.GlueSquishFactor.isFiniteLength_stalk_cokernel_structureUnitHom`. Then for
any factorization of `𝒪_X ⟶ f_*𝒪_{X'}` through an `𝒪_X`-module `𝒜` by monomorphisms, the
multiplicity of `f_*𝒪_{X'}/𝒪_X` at every point is the sum of those of `𝒜/𝒪_X` and
`f_*𝒪_{X'}/𝒜`.

No finiteness hypothesis is left: finiteness of the length of `f_*𝒪_{X'}/𝒪_X` at every point is
`Stacks.GlueSquishFactor.isFiniteLength_stalk_cokernel_structureUnitHom`, and it passes to both
halves. -/
theorem sheafMultiplicity_cokernel_structureUnitHom_add {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hcoh : (cokernel (structureUnitHom f)).IsCoherent) (U : X.Opens) [IsIso (f ∣_ U)]
    (hUfin : Set.Finite ((U : Set X)ᶜ)) {A : X.Modules} (a : unitModule X ⟶ A)
    (b : A ⟶ (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules)) [Mono a]
    [Mono b] (hab : a ≫ b = structureUnitHom f) (x : X) :
    Stacks.Chow.sheafMultiplicity (cokernel (structureUnitHom f)) x =
      Stacks.Chow.sheafMultiplicity (cokernel a) x +
        Stacks.Chow.sheafMultiplicity (cokernel b) x := by
  have hfin := isFiniteLength_stalk_cokernel_structureUnitHom f p hcoh U hUfin x
  rw [← hab] at hfin ⊢
  exact sheafMultiplicity_cokernel_comp_add a b hfin

/-- **The strict drop at the upper end for [Stacks, Tag 0C1L].** With the hypotheses of
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_add`, the multiplicity of
`𝒜/𝒪_X` is strictly below that of `f_*𝒪_{X'}/𝒪_X` at every point of the support of
`f_*𝒪_{X'}/𝒜`.

This is the shape in which properness of `𝒜 ⊂ f_*𝒪_{X'}` is used: a *single* point at which the
quotient `f_*𝒪_{X'}/𝒜` is nonzero. -/
theorem sheafMultiplicity_cokernel_structureUnitHom_lt_of_mem_supp_right {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hcoh : (cokernel (structureUnitHom f)).IsCoherent) (U : X.Opens) [IsIso (f ∣_ U)]
    (hUfin : Set.Finite ((U : Set X)ᶜ)) {A : X.Modules} (a : unitModule X ⟶ A)
    (b : A ⟶ (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules)) [Mono a]
    [Mono b] (hab : a ≫ b = structureUnitHom f) {x : X}
    (hb : x ∈ SheafOfModules.supp (cokernel b)) :
    Stacks.Chow.sheafMultiplicity (cokernel a) x <
      Stacks.Chow.sheafMultiplicity (cokernel (structureUnitHom f)) x := by
  have hfin := isFiniteLength_stalk_cokernel_structureUnitHom f p hcoh U hUfin x
  rw [← hab] at hfin ⊢
  exact sheafMultiplicity_cokernel_lt_of_mem_supp_right a b hfin hb

end Stacks.GlueSquishFactor

end
