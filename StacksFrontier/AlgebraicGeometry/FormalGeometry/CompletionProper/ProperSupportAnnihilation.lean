module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Devissage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticSupport.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The ideal sheaf annihilating a coherent adic system

Let `X` be a locally Noetherian scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent ideal sheaf and `(F_n)` an
object of `Coh(X, ℐ)`. The quasi-coherent ideal sheaves `𝒦` with `𝒦 F_n = 0` for every `n` — the
condition `Stacks.Algebraization.IsSystemAnnihilatedBy` — have a largest member, namely

  `⨅ n, annihilatorIdeal (F_n)`,

because annihilation by `𝒦` at a single level is exactly `𝒦 ≤ annihilatorIdeal (F_n)`
(`AlgebraicGeometry.annihilatorIdeal` is the honest sectionwise annihilator, by
`AlgebraicGeometry.ideal_annihilatorIdeal`). This file records that ideal sheaf and the one
consequence it has for [Stacks, Tag 088E]: the hypothesis `hSupp` of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver` — that a coherent `ℐ`-adic
system whose first term has support proper over the base is annihilated by the ideal sheaf of
*some* closed subscheme proper over the base — is **equivalent** to properness of the closed
subscheme cut out by this one canonical ideal sheaf. The existential quantifier in `hSupp`
carries no content: the candidate is forced.

## Main definitions

* `Stacks.Algebraization.systemAnnihilatorIdeal` — the largest quasi-coherent ideal sheaf
  annihilating every term of a coherent adic system.

## Main results

* `Stacks.Algebraization.le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot` — annihilation of
  a coherent module by an ideal sheaf is containment in its annihilator ideal sheaf.
* `Stacks.Algebraization.le_systemAnnihilatorIdeal_iff` — the universal property: an ideal sheaf
  kills the system exactly when it is below `systemAnnihilatorIdeal`.
* `Stacks.Algebraization.isSystemAnnihilatedBy_systemAnnihilatorIdeal` — it does kill the system.
* `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_iff` — **the reduction**: a closed
  subscheme proper over the base annihilating the system exists if and only if the subscheme of
  `systemAnnihilatorIdeal` is proper over the base.
* `Stacks.Algebraization.hSupp_of_isProper_systemAnnihilatorIdeal` and
  `Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_hSupp` — the same equivalence in the
  shape the hypothesis `hSupp` of Stacks 088E is stated in.
* `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_pow` — the sufficient condition
  a uniform power gives: if one fixed power of an ideal sheaf proper over the base kills every
  term, `hSupp` holds for that system.

## Where the content of `hSupp` sits

Write `Z = Supp(F_0)`, assumed proper over `A`, and `J = systemAnnihilatorIdeal`.

**`⊥` is not the answer and neither is `annihilatorIdeal (F_0)`.** The zero ideal sheaf kills
every system (`Stacks.Algebraization.isSystemAnnihilatedBy_bot`) but its subscheme is `X` itself,
so the properness clause would become properness of `f`, which Stacks 088E does not assume. At
the other end `annihilatorIdeal (F_0)` cuts out exactly `Z`, which *is* proper, but it does not
kill `F_n` for `n > 0`. The two clauses pull in opposite directions — annihilation wants `J`
small, properness of its subscheme wants `J` large — and `systemAnnihilatorIdeal` is the exact
optimum: it is below `annihilatorIdeal (F_n)` for every `n`
(`Stacks.Algebraization.supp_subset_support_systemAnnihilatorIdeal` records the resulting
inclusion `Z ⊆ V(J)`) and above every competitor.

**The levelwise annihilators genuinely shrink, so [Stacks, Tag 01Y9] does not close the gap.**
Each `F_n` is supported on `Z`, so
`AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset` gives an exponent `m(n)`
with `𝒦 ^ m(n) F_n = 0` for `𝒦` the vanishing ideal sheaf of `Z`, and any
*uniform* exponent would finish by `exists_isProper_isSystemAnnihilatedBy_of_pow`. There is none
in general: over `A = ℤ_p`, `I = (p)`, `X = 𝔸¹ = Spec ℤ_p[x]` the system `F_n = ℤ_p[x]/(p ⁿ⁺¹, x)`
has `Z = V(p, x)` a single closed point, `𝒦 = (p, x)` and `𝒦 ᵐ F_n = 0` exactly for `m ≥ n + 1`;
moreover `⨅ ₘ 𝒦 ᵐ = 0`, whose subscheme is all of `𝔸¹`. The ideal sheaf that works there is
`J = ⨅ ₙ (p ⁿ⁺¹, x) = (x)`, with `V(J) = Spec ℤ_p` proper over `ℤ_p` — not a power of `𝒦`, and not
`⊥`. So `J` is the scheme-theoretic support of the *algebraization* of the system, and the content
of `hSupp` is that this algebraization does not escape to infinity.

**Why this is not an affine-local statement.** Properness is not local on the source, and the two
affine-local routes both fail. First, `U ↦ ⋂ ₙ ann(F_n(U))` is not an ideal sheaf: in the example
above its value on `X` is `(x)` while on `D(p)` it is the unit ideal, and `(x)` does not localize
to the unit ideal — which is why `systemAnnihilatorIdeal` must be taken in the lattice
`AlgebraicGeometry.Scheme.IdealSheafData`, where `⨅` over an infinite family is *not* computed
sectionwise (`AlgebraicGeometry.Scheme.IdealSheafData.ideal_iInf` asks for a finite index type).
Second, the sections of `J` over an affine open `U` need not cut out anything finite over `A`:
`Γ(U)/J(U)` embeds in the `I`-adic completion `Γ(U) ^∧ / ann(lim F_n(U))` only after the
sectionwise intersection is identified with `J(U)`, and `Z ∩ U` — an *open* piece of the proper
`Z` — is not proper over `A` once `Z` has positive dimension. The elementary argument therefore
settles only the case where the support is finite over `A`, i.e. where `f` is affine.

**What the source does instead.** The proof of [Stacks, Tag 088E] obtains `J` by Noetherian
induction on the ideal sheaves, and at each step applies Chow's lemma ([Stacks, Tag 0200]) to
get a proper surjection from an H-quasi-projective `Y`, an open immersion of `Y` into a
projective `Y'`, the projective case of Grothendieck existence ([Stacks, Tag 0885]) on `Y'` and
the comparison of [Stacks, Tag 088B] back on `X`. Completeness of `A` enters that proof in
exactly one place, and it is a global step, not a support computation: `I` lies in the Jacobson
radical of `A`, so a nonempty closed subset of `Spec A` meets `V(I)`, whence a coherent sheaf on
the *proper* `Y'` whose support meets the closed fibre inside `Y` has its whole support inside
`Y`. That step needs the proper ambient `Y'`, i.e. a compactification, so the attribution in the
module docstring of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceSeparated`
stands: `hSupp` is not reachable from support and annihilator bookkeeping alone. What this file
contributes is that the whole of it is one properness statement about one canonical ideal sheaf.

## References

* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
* [Stacks Project, Tag 0CYN](https://stacks.math.columbia.edu/tag/0CYN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-! ### Annihilation of a single coherent module -/

/-- **Annihilation by an ideal sheaf is containment in the annihilator ideal sheaf.** For a
coherent module on a locally Noetherian scheme the subsheaf `𝒦 F` vanishes exactly when `𝒦` is
contained in `AlgebraicGeometry.annihilatorIdeal F`, since the ideal of the latter on an affine
open is the annihilator of the sections there with nothing lost. -/
public theorem le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent.{u} F] (K : X.IdealSheafData) :
    K ≤ annihilatorIdeal F ↔ idealPowerMultiple K 1 F = ⊥ := by
  rw [idealPowerMultiple_eq_bot_iff_affine_smul_top, Scheme.IdealSheafData.le_def]
  refine forall_congr' fun U => ?_
  rw [pow_one, ideal_annihilatorIdeal, ← Submodule.annihilator_top,
    Submodule.le_annihilator_iff]

/-! ### The annihilator ideal sheaf of a coherent adic system -/

/-- **The largest quasi-coherent ideal sheaf annihilating every term of a coherent adic
system.** It is the infimum, in the lattice of quasi-coherent ideal sheaves, of the annihilator
ideal sheaves of the terms.

The infimum is taken in `AlgebraicGeometry.Scheme.IdealSheafData` and over an infinite family it
is *not* the sectionwise intersection of the annihilators, which is not an ideal sheaf; see the
module docstring. -/
public def systemAnnihilatorIdeal {I : X.IdealSheafData}
    (𝓖 : Stacks.Coherent.CoherentAdicSystems I) : X.IdealSheafData :=
  ⨅ n : ℕ, haveI : _root_.SheafOfModules.IsCoherent.{u} (𝓖.obj.obj (op n)) := 𝓖.property.1 n
    annihilatorIdeal (𝓖.obj.obj (op n))

/-- `systemAnnihilatorIdeal` is below the annihilator ideal sheaf of every term. -/
public theorem systemAnnihilatorIdeal_le_annihilatorIdeal {I : X.IdealSheafData}
    (𝓖 : Stacks.Coherent.CoherentAdicSystems I) (n : ℕ) :
    systemAnnihilatorIdeal 𝓖 ≤
      haveI : _root_.SheafOfModules.IsCoherent.{u} (𝓖.obj.obj (op n)) := 𝓖.property.1 n
      annihilatorIdeal (𝓖.obj.obj (op n)) :=
  iInf_le _ n

/-- **The universal property of `systemAnnihilatorIdeal`.** A quasi-coherent ideal sheaf kills
every term of a coherent adic system exactly when it is contained in
`systemAnnihilatorIdeal`. -/
public theorem le_systemAnnihilatorIdeal_iff {I : X.IdealSheafData}
    (𝓖 : Stacks.Coherent.CoherentAdicSystems I) (K : X.IdealSheafData) :
    K ≤ systemAnnihilatorIdeal 𝓖 ↔ IsSystemAnnihilatedBy K 𝓖.obj := by
  have key : ∀ n : ℕ,
      have : _root_.SheafOfModules.IsCoherent.{u} (𝓖.obj.obj (op n)) := 𝓖.property.1 n
      (K ≤ annihilatorIdeal (𝓖.obj.obj (op n)) ↔
        idealPowerMultiple K 1 (𝓖.obj.obj (op n)) = ⊥) := by
    intro n
    have : _root_.SheafOfModules.IsCoherent.{u} (𝓖.obj.obj (op n)) := 𝓖.property.1 n
    exact le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot _ K
  rw [systemAnnihilatorIdeal, le_iInf_iff]
  exact forall_congr' key

/-- **`systemAnnihilatorIdeal` kills the system.** -/
public theorem isSystemAnnihilatedBy_systemAnnihilatorIdeal {I : X.IdealSheafData}
    (𝓖 : Stacks.Coherent.CoherentAdicSystems I) :
    IsSystemAnnihilatedBy (systemAnnihilatorIdeal 𝓖) 𝓖.obj :=
  (le_systemAnnihilatorIdeal_iff 𝓖 _).1 le_rfl

/-- The support of every term of the system is contained in the closed subset cut out by
`systemAnnihilatorIdeal`: the closed subscheme carrying the system is at least as large as the
support of each of its terms. -/
public theorem supp_subset_support_systemAnnihilatorIdeal {I : X.IdealSheafData}
    (𝓖 : Stacks.Coherent.CoherentAdicSystems I) (n : ℕ) :
    _root_.SheafOfModules.supp (𝓖.obj.obj (op n)) ⊆
      ((systemAnnihilatorIdeal 𝓖).support : Set X) := by
  have : _root_.SheafOfModules.IsCoherent.{u} (𝓖.obj.obj (op n)) := 𝓖.property.1 n
  rw [supp_eq_support_annihilatorIdeal (𝓖.obj.obj (op n))]
  exact Scheme.IdealSheafData.support_antitone
    (systemAnnihilatorIdeal_le_annihilatorIdeal 𝓖 n)

/-! ### The hypothesis `hSupp` of Stacks 088E, as one properness statement -/

/-- If the closed subset cut out by an ideal sheaf is proper over the base, so is its closed
subscheme. -/
private theorem isProper_subschemeι_comp_of_isProperOver {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] {K : Y.IdealSheafData} (hp : IsProperOver f K.support) :
    IsProper (K.subschemeι ≫ f) :=
  (exists_isProper_iff_forall_isProper f _).1 ((isProperOver_iff_exists_isProper f _).1 hp) _ rfl

omit [IsLocallyNoetherian X] in
/-- **A uniform power suffices.** If one fixed positive power of an ideal sheaf whose closed
subscheme is proper over the base annihilates every term of the system, then the system is
annihilated by the ideal sheaf of a closed subscheme proper over the base: a positive power has
the same support, and properness of a closed subset does not depend on the closed subscheme
structure put on it ([Stacks, Tag 0CYL]).

This is as far as [Stacks, Tag 01Y9] alone goes; the exponent it produces for the vanishing ideal
sheaf of the support is not uniform in the level, see the module docstring. -/
public theorem exists_isProper_isSystemAnnihilatedBy_of_pow {S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {I : X.IdealSheafData}
    (𝓖 : Stacks.Coherent.CoherentAdicSystems I) (K : X.IdealSheafData)
    (hK : IsProper (K.subschemeι ≫ f)) (m : ℕ)
    (hm : IsSystemAnnihilatedBy (K ^ (m + 1)) 𝓖.obj) :
    ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧ IsSystemAnnihilatedBy J 𝓖.obj := by
  refine ⟨K ^ (m + 1), ?_, hm⟩
  have hp : IsProperOver f (K ^ (m + 1)).support := by
    rw [Scheme.IdealSheafData.support_pow_succ]
    exact (isProperOver_iff_exists_isProper f _).2 ⟨K, rfl, hK⟩
  exact isProper_subschemeι_comp_of_isProperOver f hp

/-- **The reduction of `hSupp` to one canonical ideal sheaf.** A closed subscheme of `X` proper
over the base whose ideal sheaf annihilates every term of a coherent adic system exists if and
only if the closed subscheme cut out by `systemAnnihilatorIdeal` is proper over the base.

One direction is that `systemAnnihilatorIdeal` is itself a candidate. The other is its
maximality: a competitor `J` lies below it, so the closed subset it cuts out contains the one
cut out by `systemAnnihilatorIdeal`, and a closed subset of a closed subset proper over the base
is proper over the base ([Stacks, Tag 0CYN]). So the existential of `hSupp` carries no content
and the whole of it is properness of this one subscheme. -/
public theorem exists_isProper_isSystemAnnihilatedBy_iff {S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {I : X.IdealSheafData}
    (𝓖 : Stacks.Coherent.CoherentAdicSystems I) :
    (∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧ IsSystemAnnihilatedBy J 𝓖.obj) ↔
      IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f) := by
  refine ⟨?_, fun h => ⟨_, h, isSystemAnnihilatedBy_systemAnnihilatorIdeal 𝓖⟩⟩
  rintro ⟨J, hJ, hann⟩
  have hp : IsProperOver f (systemAnnihilatorIdeal 𝓖).support :=
    isProperOver_of_le f
      (Scheme.IdealSheafData.support_antitone ((le_systemAnnihilatorIdeal_iff 𝓖 J).2 hann))
      ((isProperOver_iff_exists_isProper f J.support).2 ⟨J, rfl, hJ⟩)
  exact isProper_subschemeι_comp_of_isProperOver f hp

end Stacks.Algebraization

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-- **The hypothesis `hSupp` of Stacks 088E, from properness of `systemAnnihilatorIdeal`.** This
is the statement of the binder `hSupp` of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver`, proved from the single
properness statement the previous theorem reduces it to. -/
public theorem hSupp_of_isProper_systemAnnihilatorIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hJ : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        HasProperSupport f (𝓖.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
          IsSystemAnnihilatedBy J 𝓖.obj := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact fun 𝓖 h => (exists_isProper_isSystemAnnihilatedBy_iff f 𝓖).2 (hJ 𝓖 h)

/-- **The converse**: the hypothesis `hSupp` of Stacks 088E gives properness of the closed
subscheme cut out by `systemAnnihilatorIdeal`. Together with
`Stacks.Algebraization.hSupp_of_isProper_systemAnnihilatorIdeal` this says that the two are the
same hypothesis, so nothing is lost by working with the canonical ideal sheaf. -/
public theorem isProper_systemAnnihilatorIdeal_of_hSupp
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hSupp : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        HasProperSupport f (𝓖.obj.obj (op 0)) →
          ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
            IsSystemAnnihilatedBy J 𝓖.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact fun 𝓖 h => (exists_isProper_isSystemAnnihilatedBy_iff f 𝓖).1 (hSupp 𝓖 h)

end Stacks.Algebraization

end
