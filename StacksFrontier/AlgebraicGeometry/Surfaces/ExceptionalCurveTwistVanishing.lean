module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ClosedImmersionSections
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistInjectivity

/-!
# Twisting by an exceptional curve of nonnegative degree keeps `H¹` zero

Let `E ⊆ X` be an exceptional curve of the first kind on a scheme `X`, let `ℒ` be an invertible
`𝒪_X`-module, and let `n` be the degree of `ℒ|_E` on `𝐏¹`. If `H¹(X, ℒ) = 0` and `n ≥ 0` then

`H¹(X, ℒ(iE)) = 0` for `0 ≤ i ≤ n + 1`.

This is assertion (1) of [Stacks, Tag 0C2J]; assertion (2) is
`Stacks.Surfaces.mono_rightDerived_one_map_tensorCanonicalSection` in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistInjectivity.lean`, and the two
together are the whole tag.

## Main results

* `Stacks.Surfaces.isZero_rightDerived_one_tensorInvertibleSheafPow`: **assertion (1) of Tag
  0C2J.**
* `Stacks.Surfaces.isZero_rightDerived_one_tensorInvertibleSheaf`: the induction step — one
  twist by `E` preserves the vanishing as long as the degree has not yet dropped below zero.
* `Stacks.Surfaces.isZero_rightDerived_one_tensorPushforwardUnit`: the cohomological input,
  that `H¹(X, 𝓜 ⊗ i_*𝒪_E)` vanishes as soon as `𝓜` restricts to `𝒪(d)` on `𝐏¹` with `d ≥ -1`.
* `Stacks.Surfaces.isZero_rightDerived_one_X₂`: the long-exact-sequence step, that the middle
  term of a short exact sequence has vanishing `H¹` when the two outer terms do.

## The argument

The twist `ℒ(iE)` is `ℒ ⊗ 𝒪_X(iE)`, and `iE` is the `i`-fold sum `E ^ i` of effective Cartier
divisors — the *product* of ideal sheaves, as everywhere in
`StacksFrontier/AlgebraicGeometry/DivisorSum/Basic.lean`. The induction on `i` runs on the ideal
sequence `0 ⟶ ℐ_E ⟶ 𝒪_X ⟶ i_*𝒪_E ⟶ 0` of a closed immersion
(`Stacks.Cohomology.AmpleH1.shortExact_idealSheaf`, formal from the kernel and carrying no tag
of its own; [Stacks, Tag 01WX] supplies only the identification `ℐ_E = 𝒪_X(-E)` of its first
term and the inclusion into `𝒪_X`), tensored by `𝓜 = ℒ(iE) ⊗ 𝒪_X(E)`,
exactly the sequence assertion (2) uses: its first term is `ℒ(iE)` by the evaluation pairing
(`Stacks.Surfaces.twistedIdealIso`), its middle term is `ℒ((i+1)E)`, and its third term is
`𝓜 ⊗ i_*𝒪_E`. Where assertion (2) reads off the connecting map out of the third term's *global
sections*, assertion (1) reads off the exactness of

`H¹(X, ℒ(iE)) ⟶ H¹(X, ℒ((i+1)E)) ⟶ H¹(X, 𝓜 ⊗ i_*𝒪_E)`

and concludes that the middle group vanishes when both ends do. The left end is the induction
hypothesis; the right end is the vanishing `H¹(𝐏¹, 𝒪(d)) = 0` for `d ≥ -1` of
`Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le`, reached in three
moves: the projection formula identifies `𝓜 ⊗ i_*𝒪_E` with `i_*(i^*𝓜)`, the comparison along a
closed immersion turns `H¹(X, i_*N)` into `H¹(E, N)`, and `e : 𝐏¹ ≅ E` — itself a closed
immersion — turns that into `H¹(𝐏¹, e^*i^*𝓜)`. Since `e^*i^*ℒ ≅ 𝒪(n)` and
`e^*i^*𝒪_X(E) ≅ 𝒪(-1)`, the module `e^*i^*𝓜` is `𝒪(n - i - 1)`, whose `H¹` vanishes exactly
when `i ≤ n`; that is why the conclusion stops at `i = n + 1`.

## Implementation notes

**The closed-immersion comparison is unconditional, and that is what makes this possible.**
`Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_sectionsFunctor_pushforward_iff` holds
for an arbitrary closed immersion of schemes, in every degree, for every sheaf of modules — no
affine base, no quasi-coherence, no Noetherian hypothesis. It is used twice here, once at
`E ⊆ X` and once at the isomorphism `e : 𝐏¹ ≅ E`, an isomorphism being a closed immersion.
Transporting across `e` also needs `N ≅ e_*e^*N`, which is
`Stacks.ClosedImmersion.unitIsoOfIsIso`.

**The degree hypothesis.** As in assertion (2), "`n` is the degree of `ℒ|_E` as an invertible
module on `𝐏¹`" is recorded as an isomorphism `e^*i^*ℒ ≅ 𝒪(n)`, which is what having degree `n`
means for an invertible module on the projective line and the form in which the source's proof
uses it — its first line replaces the degree hypothesis by exactly this isomorphism.

**Noetherianness is not assumed.** The source states the lemma for `X` Noetherian, but nothing
in the argument above uses it: an exact sequence, the projection formula, the comparison along a
closed immersion and a vanishing statement on `𝐏¹`. The statement below is therefore a
generalization of the tag, not a weakening.

**Why the multiples of `E` arrive through `Stacks.Divisors.invertibleSheafSumIso`.** `𝒪_X(iE)`
is `Stacks.Divisors.invertibleSheaf' (E ^ i)`, the invertible sheaf of the divisor `iE`, and the
induction needs it one twist at a time. [Stacks, Tag 02OP] supplies
`𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')`, which at `D = iE`, `D' = E` is the step; the `eqToIso` in
`Stacks.Surfaces.invertibleSheafPowSuccIso` is only `pow_succ`, the equality
`E ^ (i + 1) = E ^ i * E` of ideal sheaves, and the base case `𝒪_X(0 · E) ≅ 𝒪_X` is
`Stacks.Divisors.invertibleSheafTopIsoUnit`.

**Which spelling of the category.** As in assertion (2), everything is stated for
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)` with the monoidal structure the
ideal
sequence and the twisting functor are stated at; the local instances are the very ones
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistInjectivity.lean` installs, re-made
local here rather than restated, so that the isomorphisms imported from there are about the same
terms.

## References

* [Stacks Project, Tag 0C2J](https://stacks.math.columbia.edu/tag/0C2J)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 02OP](https://stacks.math.columbia.edu/tag/02OP)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Divisors
open RingedSpaceModuleAdjunction (modulePullback modulePushforward)

universe u

namespace Stacks.Surfaces

attribute [local instance] HasDerivedCategory.standard MvPolynomial.gradedAlgebra
attribute [local instance] schemeModulesMonoidal schemeModulesSymmetric

variable {X : Scheme.{u}}

/-! ### The cohomological input -/

/-- `H¹(X, -)` vanishes on an object isomorphic to one on which it vanishes. -/
private theorem isZero_rightDerived_one_of_iso {M N : _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)} (f : M ≅ N)
    (h : IsZero (((moduleGlobalSections X).rightDerived 1).obj N)) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj M) :=
  h.of_iso (((moduleGlobalSections X).rightDerived 1).mapIso f)

/-- **`H¹(X, 𝓜 ⊗ i_*𝒪_E)` vanishes when `𝓜` pulls back to a twist of degree `≥ -1` on the
projective line.** The module is `i_*(i^*𝓜)` by the projection formula; the cohomology of a
direct image along a closed immersion is the cohomology upstairs, so this is `H¹(E, i^*𝓜)`; and
the isomorphism `e : 𝐏¹ ≅ E` is itself a closed immersion, so that in turn is
`H¹(𝐏¹, e^*i^*𝓜) = H¹(𝐏¹, 𝒪(d))`, which vanishes for `d ≥ -1`.

This is the degree-one companion of
`Stacks.Surfaces.isZero_sections_tensorPushforwardUnit`, which does the same for global
sections and a *negative* twist. -/
theorem isZero_rightDerived_one_tensorPushforwardUnit (E : X.IdealSheafData) (k : Type u)
    [Field k] (e : projectiveLineProj k ≅ E.subscheme)
    (M : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) {d : ℤ} (hd : -1 ≤ d)
    (hiso : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj M) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) d) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj M).obj
        ((modulePushforward E.subschemeι.toLRSHom.toShHom).obj
          (𝟙_ (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf E.subscheme.sheaf)))))) := by
  show IsZero (((moduleGlobalSections X).rightDerived 1).obj
    (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) M
      ((modulePushforward E.subschemeι.toLRSHom.toShHom).obj
      (𝟙_ (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf E.subscheme.sheaf))))))
  refine isZero_rightDerived_one_of_iso (tensorPushforwardUnitIso E.subschemeι M) ?_
  refine (Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_sectionsFunctor_pushforward_iff
    E.subschemeι _ 1).2 ?_
  refine IsZero.of_iso ?_
    (((Stacks.Cohomology.sectionsFunctor E.subscheme ⊤).rightDerived 1).mapIso
      (Stacks.ClosedImmersion.unitIsoOfIsIso e.hom
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj M)))
  refine (Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_sectionsFunctor_pushforward_iff
    e.hom _ 1).2 ?_
  refine IsZero.of_iso ?_
    (((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).rightDerived 1).mapIso hiso)
  exact Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le k hd

/-- **The middle term of a short exact sequence has vanishing `H¹` when the two outer terms
do.** This is exactness of `H¹(X, X₁) ⟶ H¹(X, X₂) ⟶ H¹(X, X₃)`, the `exact_map` row of the
long exact cohomology sequence of
`Stacks.AmpleCohomologicalCriterion.sectionsDeltaFunctor`, with both outer groups zero. -/
theorem isZero_rightDerived_one_X₂
    {S : ShortComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))} (hS : S.ShortExact)
    (h₁ : IsZero (((moduleGlobalSections X).rightDerived 1).obj S.X₁))
    (h₃ : IsZero (((moduleGlobalSections X).rightDerived 1).obj S.X₃)) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj S.X₂) :=
  ((Stacks.AmpleCohomologicalCriterion.sectionsDeltaFunctor X ⊤).exact_map hS 1).isZero_X₂
    (h₁.eq_of_src _ 0) (h₃.eq_of_tgt _ 0)

/-- `𝓜 ⊗ 𝒪_X(E)` is invertible when `𝓜` is: the tensor product of two invertible modules is
invertible ([Stacks, Tag 01CT]), and `𝒪_X(E)` is invertible because `E` is an effective Cartier
divisor ([Stacks, Tag 01WX]). -/
theorem isInvertible_tensorObj_invertibleSheaf (E : X.IdealSheafData)
    [IsEffectiveCartierDivisor E] (M : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        M (invertibleSheaf' E)) :=
  have _hM : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  have _hP : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf' E) :=
    isTensorInvertible_invertibleSheaf E
  (Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf
    (structureSheafRing X.toRingedSpace).property M (invertibleSheaf' E)).toAlgebraicGeometry

/-! ### The induction step -/

/-- **One twist by `E` preserves the vanishing of `H¹`, as long as the degree is still
nonnegative.** Let `E ⊆ X` be an exceptional curve of the first kind, `𝓜` an invertible
`𝒪_X`-module with `e^*i^*𝓜 ≅ 𝒪(m)` and `m ≥ 0`. If `H¹(X, 𝓜) = 0` then `H¹(X, 𝓜(E)) = 0`.

Tensor the ideal sequence `0 ⟶ ℐ_E ⟶ 𝒪_X ⟶ i_*𝒪_E ⟶ 0` by `𝓜 ⊗ 𝒪_X(E)`. Its first term is
`𝓜` by `Stacks.Surfaces.twistedIdealIso`, its middle term is `𝓜 ⊗ 𝒪_X(E)` up to the right unit
constraint, and the `H¹` of its third term vanishes by
`Stacks.Surfaces.isZero_rightDerived_one_tensorPushforwardUnit`, since `𝓜 ⊗ 𝒪_X(E)` pulls back
to `𝒪(m - 1)` and `m - 1 ≥ -1`. -/
theorem isZero_rightDerived_one_tensorInvertibleSheaf (E : X.IdealSheafData) (k : Type u)
    [Field k] {e : projectiveLineProj k ≅ E.subscheme}
    (hE : E.IsExceptionalCurveOfFirstKind k e)
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    {m : ℤ} (hm : 0 ≤ m)
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj M) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)
    (h : IsZero (((moduleGlobalSections X).rightDerived 1).obj M)) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj
      (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        M (invertibleSheaf' E))) := by
  have _hcartier := hE.isEffectiveCartierDivisor
  have hNinv := isInvertible_tensorObj_invertibleSheaf E M
  set N := MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    M (invertibleSheaf' E) with hN
  have hse := Stacks.Cohomology.AmpleH1.shortExact_map_tensorLeft X N
    (idealShortComplex_shortExact E)
  refine isZero_rightDerived_one_of_iso (ρ_ N).symm (isZero_rightDerived_one_X₂ hse ?_ ?_)
  · exact isZero_rightDerived_one_of_iso (twistedIdealIso E M) h
  · exact isZero_rightDerived_one_tensorPushforwardUnit E k e N (d := m + -1) (by omega)
      (pullbackTwistIso E k hE M hdeg)

/-! ### The multiples of the divisor -/

/-- **`𝒪_X(0 · E) ≅ 𝒪_X`**: the zero divisor is the empty closed subscheme, whose invertible
sheaf is the structure sheaf (`Stacks.Divisors.invertibleSheafTopIsoUnit`). -/
def invertibleSheafPowZeroIso (E : X.IdealSheafData) :
    invertibleSheaf' (E ^ 0) ≅ 𝟙_ (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  eqToIso (congrArg invertibleSheaf'
      ((pow_zero E).trans AlgebraicGeometry.Scheme.IdealSheafData.one_eq_top)) ≪≫
    invertibleSheafTopIsoUnit

/-- **`𝒪_X((i+1)E) ≅ 𝒪_X(iE) ⊗ 𝒪_X(E)`**: [Stacks, Tag 02OP] at the divisors `iE` and `E`,
whose sum `iE + E = (i+1)E` is the equality `E ^ (i + 1) = E ^ i * E` of ideal sheaves. -/
def invertibleSheafPowSuccIso (E : X.IdealSheafData) [IsEffectiveCartierDivisor E] (i : ℕ) :
    invertibleSheaf' (E ^ (i + 1)) ≅
      MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (invertibleSheaf' (E ^ i)) (invertibleSheaf' E) :=
  eqToIso (congrArg invertibleSheaf' (pow_succ E i)) ≪≫ (invertibleSheafSumIso (E ^ i) E).symm

/-- **`ℒ(0 · E) ≅ ℒ`**, the base case of the induction. -/
def divisorTwistZeroIso (E : X.IdealSheafData)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
      L (invertibleSheaf' (E ^ 0)) ≅ L :=
  whiskerLeftIso L (invertibleSheafPowZeroIso E) ≪≫ ρ_ L

/-- **`ℒ((i+1)E) ≅ ℒ(iE) ⊗ 𝒪_X(E)`**, the step of the induction: one more multiple of `E` is
one more twist by `𝒪_X(E)`. -/
def divisorTwistSuccIso (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (i : ℕ) :
    MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        L (invertibleSheaf' (E ^ (i + 1))) ≅
      MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
          L (invertibleSheaf' (E ^ i))) (invertibleSheaf' E) :=
  whiskerLeftIso L (invertibleSheafPowSuccIso E i) ≪≫
    (α_ L (invertibleSheaf' (E ^ i)) (invertibleSheaf' E)).symm

/-- **`e^*i^*(ℒ(iE)) ≅ 𝒪(n - i)` when `ℒ|_E` has degree `n`.** Each multiple of `E` drops the
degree by one, since `e^*i^*𝒪_X(E) ≅ 𝒪(-1)` for an exceptional curve of the first kind
(`Stacks.Surfaces.pullbackTwistIso`). Stated as a `Nonempty`, which is all the vanishing
statement below consumes. -/
theorem nonempty_pullbackTwistPowIso (E : X.IdealSheafData) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ E.subscheme} (hE : E.IsExceptionalCurveOfFirstKind k e)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) {n : ℤ}
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj L) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) (i : ℕ) :
    Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj
          (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
            L (invertibleSheaf' (E ^ i)))) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n - i)) := by
  have _hcartier := hE.isEffectiveCartierDivisor
  induction i with
  | zero =>
      refine ⟨((modulePullback e.hom.toLRSHom.toShHom).mapIso
        ((modulePullback E.subschemeι.toLRSHom.toShHom).mapIso (divisorTwistZeroIso E L))) ≪≫
        hdeg ≪≫ eqToIso ?_⟩
      exact congrArg _ (by push_cast; ring)
  | succ i ih =>
      obtain ⟨f⟩ := ih
      refine ⟨((modulePullback e.hom.toLRSHom.toShHom).mapIso
          ((modulePullback E.subschemeι.toLRSHom.toShHom).mapIso (divisorTwistSuccIso E L i))) ≪≫
        pullbackTwistIso E k hE
          (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
            L (invertibleSheaf' (E ^ i))) f ≪≫ eqToIso ?_⟩
      exact congrArg _ (by push_cast; ring)

/-! ### Assertion (1) of Tag 0C2J -/

/-- **[Stacks, Tag 0C2J], assertion (1).** Let `E ⊆ X` be an exceptional curve of the first kind
on a scheme `X`, let `ℒ` be an invertible `𝒪_X`-module, and let `n` be the degree of `ℒ|_E` as an
invertible module on `𝐏¹`, recorded as an isomorphism `e^*i^*ℒ ≅ 𝒪(n)`. If `H¹(X, ℒ) = 0` and
`n ≥ 0` then `H¹(X, ℒ(iE)) = 0` for every `0 ≤ i ≤ n + 1`.

Here `ℒ(iE)` is `ℒ ⊗ 𝒪_X(iE)` with `iE = E ^ i` the `i`-fold sum of `E` with itself in the monoid
of effective Cartier divisors. -/
@[stacks 0C2J "assertion (1): vanishing through the twists of nonnegative degree"]
theorem isZero_rightDerived_one_tensorInvertibleSheafPow (E : X.IdealSheafData) (k : Type u)
    [Field k] {e : projectiveLineProj k ≅ E.subscheme}
    (hE : E.IsExceptionalCurveOfFirstKind k e)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {n : ℤ} (_hn : 0 ≤ n)
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj L) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) n)
    (h0 : IsZero (((moduleGlobalSections X).rightDerived 1).obj L))
    (i : ℕ) (hi : (i : ℤ) ≤ n + 1) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj
      (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        L (invertibleSheaf' (E ^ i)))) := by
  have _hcartier := hE.isEffectiveCartierDivisor
  induction i with
  | zero =>
      exact isZero_rightDerived_one_of_iso (divisorTwistZeroIso E L) h0
  | succ i ih =>
      have hi' : (i : ℤ) ≤ n + 1 := by push_cast at hi ⊢; omega
      have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          (structureSheafRing X.toRingedSpace).property
          (MonoidalCategory.tensorObj (C := _root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
            L (invertibleSheaf' (E ^ i))) :=
        isInvertible_tensorObj_invertibleSheaf (E ^ i) L
      obtain ⟨f⟩ := nonempty_pullbackTwistPowIso E k hE L hdeg i
      exact isZero_rightDerived_one_of_iso (divisorTwistSuccIso E L i)
        (isZero_rightDerived_one_tensorInvertibleSheaf E k hE _
          (m := n - i) (by push_cast at hi; omega) f (ih hi'))

end Stacks.Surfaces

end
