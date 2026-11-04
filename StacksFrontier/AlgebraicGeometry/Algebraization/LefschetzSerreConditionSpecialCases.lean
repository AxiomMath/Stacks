module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.GlobalProperOverCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerAlgebraization
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.RingCatStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Algebraization of formal modules on a threefold satisfying `(S₃)`

Let `k` be a field, `X` a proper variety over `k` and `Y ⊂ X` an effective Cartier divisor with
`𝒪_X(Y)` ample, with sheaf of ideals `𝓘`. Let `(𝓔ₙ)` be an object of `Coh(X, 𝓘)` whose terms are
finite locally free over the infinitesimal neighbourhoods `Yₙ`. The algebraization criterion of
Stacks 0EL5 asks that

`depth(𝒪_{X,x}) + dim({x}‾) > 2`

off `Y`, and this file records when that inequality is automatic: it holds at every point as soon
as `dim(X) ≥ 3` and `X` satisfies Serre's condition `(S₃)`, in particular when `X` is a
Cohen–Macaulay threefold. The conclusion in both cases is that `(𝓔ₙ)` is the completion of a
coherent `𝒪_X`-module `𝓔`, and such an `𝓔` is finite locally free near `Y`.

The arithmetic is uniform. Write `d = dim(𝒪_{X,x})` and `c = dim({x}‾)`, so that `d + c = dim(X)`
on a variety. Serre's condition gives `min(3, d) ≤ depth(𝒪_{X,x})`, and

`min(3, d) + c = min(3 + c, d + c) ≥ min(3, dim(X)) = 3`,

because `c ≥ 0` and `dim(X) ≥ 3`. So `depth(𝒪_{X,x}) + c ≥ 3 > 2` whether or not `d` exceeds `3`.
A Cohen–Macaulay scheme satisfies `(Sₖ)` for every `k`, so the threefold case is the case
`dim(X) = 3` of the general one.

In dimension at most two the criterion is empty rather than false: `depth(𝒪_{X,x}) ≤ dim(𝒪_{X,x})`
and `dim(𝒪_{X,x}) + dim({x}‾) ≤ dim(X) ≤ 2`, so its hypothesis has no instances. That is a remark
about how far the criterion reaches, not a mathematical assertion, and nothing below formalizes
it; the first clause of Stacks 0EL6, which records it, states nothing and carries no attribute
here.

## Main definitions

* `Stacks.Algebraization.localDepthAddDimClosure` — the quantity
  `depth(𝒪_{X,x}) + dim({x}‾)` the criterion of Stacks 0EL5 bounds below.
* `Stacks.Algebraization.IsFiniteLocallyFreeAdic` — the hypothesis of Stacks 0EL6 that the terms
  of the system be finite locally free, read over the infinitesimal neighbourhoods.

## Main results

* `Stacks.Algebraization.two_lt_depth_add_dimClosure_of_hasPropertySk_three` — the arithmetic:
  `dim(X) ≥ 3` together with `(S₃)` and the dimension formula give `depth + dim({x}‾) > 2`.
* `Stacks.Algebraization.isCompletionOfCoherent_of_hasPropertySk_three` — Stacks 0EL6, clause (3).
* `Stacks.Algebraization.isCompletionOfCoherent_of_isCohenMacaulay_threefold` — Stacks 0EL6,
  clause (2).
* `Stacks.Algebraization.exists_isOpen_isFiniteLocallyFree_of_forall_mem` — a module free near
  every point of a set is finite locally free on an open neighbourhood of that set.
* `Stacks.Algebraization.exists_isFiniteLocallyFree_neighbourhood_of_isCompletionOfCoherent` —
  Stacks 0EL6, the closing remark.

## Implementation notes

The freeness hypothesis is read over the infinitesimal neighbourhoods, not over `X`. Asking that
`𝓔ₙ` be finite locally free as an `𝒪_X`-module — which is what
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (𝓔ₙ)` says — would make the hypothesis
satisfiable only by the zero system, so the statements below would carry no content. A term of a
coherent adic system is annihilated by `𝓘 ^ (n + 1)` (the second clause of
`Stacks.Coherent.IsCoherentAdicSystem`), and the annihilator of a free module of nonzero rank on
an affine open `U` is the zero ideal, so finite local freeness over `𝒪_X` forces
`𝓘(U) ^ (n + 1) = 0`; on a variety `Γ(X, U)` is a domain, so this forces `𝓘(U) = 0`, which an
effective Cartier divisor forbids on a nonempty `U`. Only the empty index set survives, i.e.
`𝓔ₙ = 0`. `Stacks.Algebraization.IsFiniteLocallyFreeAdic` is the source's condition instead: each
`𝓔ₙ` is the direct image along `Yₙ ↪ X` of a finite locally free module on `Yₙ`, the subscheme
cut out by `𝓘 ^ (n + 1)`.

Three inputs of the source are hypotheses rather than invocations, each for a reason:

* The conclusion of Stacks 0EL5 is not available. That tag's carrier in this library is
  `Stacks.Algebraization.satisfiesDepthInequalities_one_two_iff`, in
  `StacksFrontier/AlgebraicGeometry/Algebraization/DepthInequalitiesCohomologicalDimensionOne.lean`,
  and its own attribute records that it proves only the opening step — the identification of the
  depth hypothesis with the `(1, 2)`-inequalities, in the affine situation of Stacks 0EHC. That
  the system is a completion is not proved there, so it is the hypothesis `halgebraize` here, in
  the shape Stacks 0EL7 applies it: the depth inequality off `Y` implies algebraizability.
* The dimension formula `dim(𝒪_{X,x}) + dim({x}‾) = dim(X)` for a variety is the hypothesis
  `hform`. What this library has of Stacks 0A21 is the transcendence-degree form
  `AlgebraicGeometry.topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk` in
  `StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/Formula.lean`, line 95; the bridge
  `dim({x}‾) = trdeg κ(x)` that turns it into the form used here is
  `AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_trdeg` of
  `StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/Trdeg.lean`, line 167.
Local freeness of `𝓔` at the points of `Y`, the closing remark, is proved rather than assumed,
and not through the completed stalk: there is no freeness statement about
`Stacks.Algebraization.completedStalk` in this library, and the descent of freeness along a
faithfully flat base change is a `private` lemma of
`StacksFrontier/RingTheory/Smooth/LocusBaseChange.lean`. The route taken instead stays with the
finite level `n`. The stalk of `𝓔 / 𝓘 ^ (n + 1) 𝓔` at `y` is `𝓔_y / 𝓘_y ^ (n + 1) 𝓔_y` and the
hypothesis identifies it with the stalk of a finite locally free module on `Yₙ`, which is free
over `𝒪_{Yₙ, y} = 𝒪_{X,y} / 𝓘_y ^ (n + 1)`; a finite module over a Noetherian local ring whose
every adic quotient is free is free, by Krull's intersection theorem. Those two steps are
`Stacks.Algebraization.free_quotient_stalk_of_pushforward_iso` in
`StacksFrontier/AlgebraicGeometry/Algebraization/LefschetzSerreFreeStalk.lean` and
`Stacks.FreeOfAdicQuotients.free_of_forall_free_quotient_pow_smul_top` in
`StacksFrontier/RingTheory/Module/Free/OfAdicQuotients.lean`. Stacks 0B8J then turns the free stalk
into a free neighbourhood, and the passage from those neighbourhoods to a single one is the force
of the source's "of course".

Spelling out "finite locally free in an open neighbourhood `V` of `Y`" as local freeness at every
point of `V`, with the witnessing opens inside `V`, is the unfolding of
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree` for the restriction of `𝓔` to `V`: that
predicate is itself the existence of a free neighbourhood of each point, so no comparison between
the opens of `V` and those of `X` is involved.

Local Noetherianity of `X` is implied by `LocallyOfFiniteType f`, which `IsProperVariety` extends,
but is taken as an instance binder so that one instance is in play in the statements that need it.
Serre's condition is `AlgebraicGeometry.HasPropertySk`, which compares `min(k, dim(𝒪_{X,x}))`
with the depth of the local ring in `WithBot ℕ∞`; the depth and dimension quantities below are
read in that same ordered monoid, where `dim({x}‾)` is `Stacks.Algebraization.dimClosureAt`.

## References

* [Stacks Project, Tag 0EL6](https://stacks.math.columbia.edu/tag/0EL6)
* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5), the criterion.
* [Stacks Project, Tag 033Q](https://stacks.math.columbia.edu/tag/033Q), Serre's conditions.
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), the dimension formula.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### The depth–dimension quantity -/

/-- The quantity `depth(𝒪_{X,x}) + dim({x}‾)` compared with `2` by the algebraization criterion of
Stacks 0EL5, read in `WithBot ℕ∞`, where Serre's conditions and the Krull dimension live. -/
public def localDepthAddDimClosure (X : Scheme.{u}) (x : X) : WithBot ℕ∞ :=
  (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x) : WithBot ℕ∞) + dimClosureAt X x

/-! ### The arithmetic of Serre's condition `(S₃)` -/

/-- In `ℕ∞`, if `3 ≤ d + c` then `3 ≤ min(3, d) + c`: the truncation at `3` costs nothing,
because `c ≥ 0` covers the case `d ≥ 3` and the hypothesis covers the case `d ≤ 3`. -/
private lemma three_le_min_three_add {d c : ℕ∞} (h : (3 : ℕ∞) ≤ d + c) :
    (3 : ℕ∞) ≤ min 3 d + c := by
  rcases le_total (3 : ℕ∞) d with hd | hd
  · rw [min_eq_left hd]; exact le_self_add
  · rw [min_eq_right hd]; exact h

/-- The arithmetic step: from `d + c = D` with `3 ≤ D` and `min(3, d) ≤ e` one gets `2 < e + c`.
Both `d` and `c` are finite below because `⊥` is absorbing for the sum, which `3 ≤ D` forbids. -/
private lemma two_lt_add_of_min_three_le {d c D e : WithBot ℕ∞} (hsum : d + c = D)
    (hD : ((3 : ℕ) : WithBot ℕ∞) ≤ D) (he : min ((3 : ℕ) : WithBot ℕ∞) d ≤ e) :
    ((2 : ℕ) : WithBot ℕ∞) < e + c := by
  subst hsum
  obtain ⟨hd, hc⟩ := WithBot.add_ne_bot.mp (ne_bot_of_le_ne_bot (by simp) hD)
  lift d to ℕ∞ using hd
  lift c to ℕ∞ using hc
  lift e to ℕ∞ using ne_bot_of_le_ne_bot (by simp) he
  have h3 : ((3 : ℕ) : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := by simp
  rw [h3, ← WithBot.coe_add, WithBot.coe_le_coe] at hD
  rw [h3, ← WithBot.coe_min, WithBot.coe_le_coe] at he
  have hgoal : (3 : ℕ∞) ≤ e + c :=
    (three_le_min_three_add hD).trans (add_le_add he le_rfl)
  have h2 : ((2 : ℕ) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by simp
  rw [h2, ← WithBot.coe_add, WithBot.coe_lt_coe]
  exact lt_of_lt_of_le (by norm_num) hgoal

/-- **The depth criterion of Stacks 0EL5 holds on an `(S₃)` scheme of dimension at least three.**
Serre's condition gives `min(3, dim(𝒪_{X,x})) ≤ depth(𝒪_{X,x})`, and adding `dim({x}‾)` turns the
truncation at `3` into the dimension of `X`, which is at least `3`. -/
public theorem two_lt_depth_add_dimClosure_of_hasPropertySk_three (X : Scheme.{u})
    [IsLocallyNoetherian X] (hS₃ : HasPropertySk X 3)
    (hdim : ((3 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X)
    (hform : ∀ x : X,
      ringKrullDim (X.presheaf.stalk x) + dimClosureAt X x = topologicalKrullDim X) (x : X) :
    ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x :=
  two_lt_add_of_min_three_le (hform x) hdim (hS₃ x)

/-! ### Finite local freeness of an adic system over the infinitesimal neighbourhoods -/

/-- **The terms of an adic system are finite locally free over the infinitesimal
neighbourhoods.** Stacks 0EL6 asks that `𝓔ₙ` be finite locally free *read over* `Yₙ`, the closed
subscheme cut out by `𝓘 ^ (n + 1)`, not over `𝒪_X`: a term of a coherent adic system is
annihilated by `𝓘 ^ (n + 1)`, so over `𝒪_X` the only finite locally free such term is the zero
module. The condition is therefore that `𝓔ₙ` be the direct image of a finite locally free module
on `Yₙ`, which is the scheme-theoretic reading of "locally free over `𝒪_X / 𝓘 ^ (n + 1)`". -/
public def IsFiniteLocallyFreeAdic {X : Scheme.{u}} (I : X.IdealSheafData)
    (E : Stacks.Coherent.CoherentAdicSystems I) : Prop :=
  ∀ n : ℕ, ∃ M : (I ^ (n + 1)).subscheme.Modules,
    AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree M ∧
      Nonempty ((Scheme.Modules.pushforward (I ^ (n + 1)).subschemeι).obj M ≅
        E.obj.obj (op n))

/-! ### The special cases of Stacks 0EL5 -/

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Stacks Project, Tag 0EL6, clause (3).** Let `X` be a proper variety over a field with an
effective Cartier divisor `Y` whose sheaf `𝒪_X(Y)` is ample, and let `(𝓔ₙ)` be an object of
`Coh(X, 𝓘)` whose terms are finite locally free over the infinitesimal neighbourhoods. If
`dim(X) ≥ 3` and `X` satisfies `(S₃)`, then `(𝓔ₙ)` is the completion of a coherent
`𝒪_X`-module. -/
@[stacks 0EL6 "clause (3): dim X >= 3 and (S_3); the freeness of E_n is corrected to be read \
 over Y_n, since over O_X it would force E_n = 0; 0EL5's conclusion and 0A21 hypothesised"]
public theorem isCompletionOfCoherent_of_hasPropertySk_three (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor Y]
    (_hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (Stacks.Divisors.divisorSheaf Y))
    (E : Stacks.Coherent.CoherentAdicSystems Y)
    (_hfree : IsFiniteLocallyFreeAdic Y E)
    (hdim : ((3 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) (hS₃ : HasPropertySk X 3)
    (hform : ∀ x : X,
      ringKrullDim (X.presheaf.stalk x) + dimClosureAt X x = topologicalKrullDim X)
    (halgebraize : (∀ x : X, x ∉ Y.support →
        ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x) → IsCompletionOfCoherent Y E) :
    IsCompletionOfCoherent Y E :=
  halgebraize fun x _ => two_lt_depth_add_dimClosure_of_hasPropertySk_three X hS₃ hdim hform x

/-- **Stacks Project, Tag 0EL6, clause (2).** In the situation of clause (3), a Cohen–Macaulay
threefold satisfies `(S₃)` and has dimension `3`, so `(𝓔ₙ)` is again the completion of a coherent
`𝒪_X`-module. -/
@[stacks 0EL6 "clause (2): a Cohen-Macaulay threefold; the freeness of E_n is corrected to be \
 read over Y_n, since over O_X it would force E_n = 0; 0EL5 and 0A21 hypothesised"]
public theorem isCompletionOfCoherent_of_isCohenMacaulay_threefold (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor Y]
    (_hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (Stacks.Divisors.divisorSheaf Y))
    (E : Stacks.Coherent.CoherentAdicSystems Y)
    (_hfree : IsFiniteLocallyFreeAdic Y E)
    (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hdim : topologicalKrullDim X = ((3 : ℕ) : WithBot ℕ∞))
    (hform : ∀ x : X,
      ringKrullDim (X.presheaf.stalk x) + dimClosureAt X x = topologicalKrullDim X)
    (halgebraize : (∀ x : X, x ∉ Y.support →
        ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x) → IsCompletionOfCoherent Y E) :
    IsCompletionOfCoherent Y E :=
  isCompletionOfCoherent_of_hasPropertySk_three f Y _hample E _hfree hdim.ge
    ((AlgebraicGeometry.isCohenMacaulay_iff_forall_hasPropertySk X).mp hCM 3) hform halgebraize

/-! ### Local freeness near the divisor -/

/-- **Local freeness along a set spreads to a neighbourhood of it.** If a module on a scheme is
finite free on some open around every point of a set `S`, the union of those opens is an open
neighbourhood of `S` on which the module is finite locally free. -/
public theorem exists_isOpen_isFiniteLocallyFree_of_forall_mem {Z : Scheme.{u}} (G : Z.Modules)
    (S : Set Z)
    (hfree : ∀ y ∈ S, ∃ (U : Z.Opens) (_ : y ∈ U) (ρ : Type u) (_ : Finite ρ),
      Nonempty (Scheme.Modules.restrict G U.ι ≅ SheafOfModules.free.{u} ρ)) :
    ∃ V : Z.Opens, S ⊆ (V : Set Z) ∧ ∀ x : Z, x ∈ V →
      ∃ (U : Z.Opens) (_ : x ∈ U) (_ : U ≤ V) (ρ : Type u) (_ : Finite ρ),
        Nonempty (Scheme.Modules.restrict G U.ι ≅ SheafOfModules.free.{u} ρ) := by
  classical
  refine ⟨⨆ y : S, (hfree y.1 y.2).choose, fun y hy => ?_, fun x hx => ?_⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨y, hy⟩, (hfree y hy).choose_spec.choose⟩
  · obtain ⟨y, hyx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨_, ρ, hρ, e⟩ := (hfree y.1 y.2).choose_spec
    exact ⟨(hfree y.1 y.2).choose, hyx, le_iSup (fun z : S => (hfree z.1 z.2).choose) y, ρ, hρ, e⟩

/-- **Stacks Project, Tag 0EL6, the closing remark.** If the object `(𝓔ₙ)` is the completion of a
coherent `𝒪_X`-module `𝓔`, then `𝓔` is finite locally free on an open neighbourhood of `Y`.

At a point `y` of `Y` the terms of the system identify the adic quotients
`𝓔_y / 𝓘_y ^ (n + 1) 𝓔_y` with the stalks of finite locally free modules on the infinitesimal
neighbourhoods, hence make them free over `𝒪_{X,y} / 𝓘_y ^ (n + 1)`
(`Stacks.Algebraization.free_quotient_stalk_of_pushforward_iso`); a module with a free tower of
adic quotients over a Noetherian local ring is free
(`Stacks.FreeOfAdicQuotients.free_of_forall_free_quotient_pow_smul_top`), so `𝓔_y` is a finite
free `𝒪_{X,y}`-module. Stacks 0B8J spreads a free stalk to a free neighbourhood, and those
neighbourhoods cover a neighbourhood of `Y`. -/
@[stacks 0EL6 "closing remark: such an E is finite locally free near Y"]
public theorem exists_isFiniteLocallyFree_neighbourhood_of_isCompletionOfCoherent
    (f : X ⟶ Spec (.of k)) [IsProperVariety k f] [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor Y]
    (_hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (Stacks.Divisors.divisorSheaf Y))
    (E : Stacks.Coherent.CoherentAdicSystems Y)
    (hfree : IsFiniteLocallyFreeAdic Y E)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hcompletion : Nonempty (((completionFunctor X Y).obj G).obj ≅ E.obj)) :
    ∃ V : X.Opens, (Y.support : Set X) ⊆ (V : Set X) ∧ ∀ x : X, x ∈ V →
      ∃ (U : X.Opens) (_ : x ∈ U) (_ : U ≤ V) (ρ : Type u) (_ : Finite ρ),
        Nonempty (Scheme.Modules.restrict G.obj U.ι ≅ SheafOfModules.free.{u} ρ) := by
  classical
  have hfp := _root_.isFinitePresentation_of_isCoherent G.obj
  have hqc := _root_.isQuasicoherent_of_isFinitePresentation G.obj
  refine exists_isOpen_isFiniteLocallyFree_of_forall_mem G.obj _ fun y hy => ?_
  have hstalkFree :=
    free_stalk_of_forall_pushforward_iso Y (show X.Modules from G.obj) hy fun n => by
      obtain ⟨N, hN, ⟨eN⟩⟩ := hfree n
      exact ⟨N, hN, ⟨(eqToIso (completionFunctor_obj X Y G n).symm ≪≫
        hcompletion.some.app (op n)) ≪≫ eN.symm⟩⟩
  have hfpStalk :=
    Stacks.StalkFiniteType.finitePresentation_stalk (show X.Modules from G.obj) y
  obtain ⟨U, hU, ⟨e⟩⟩ := Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis
    (show X.Modules from G.obj) y (Module.Free.chooseBasis _ _)
  exact ⟨U, hU, _, inferInstance, ⟨Stacks.Modules.restrictIsoFree U G.obj _ e.symm⟩⟩

end Stacks.Algebraization

end
