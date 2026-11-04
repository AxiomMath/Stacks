module

public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Sections
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connectedness of a scheme from its ring of global functions

A scheme `Z` is connected as soon as it is nonempty and `Γ(Z, 𝒪_Z)` has no idempotent other
than `0` and `1`: a clopen subset produces an idempotent whose basic open it is
(`AlgebraicGeometry.exists_isIdempotentElem_basicOpen_eq`), and that idempotent is trivial only
for the two trivial clopens. Conversely a preconnected scheme has only the two trivial
idempotents (`Stacks.AlgebraicGeometry.ProperGeomConnected.isIdempotentElem_eq_zero_or_one`).

Putting the two together: if `i : Z ⟶ X` induces a *bijection* `Γ(X, 𝒪_X) → Γ(Z, 𝒪_Z)` and `X`
is connected, then `Z` is connected. This is the step of the Enriques–Severi–Zariski
connectedness theorem [Stacks, Tag 0FD9] that converts the cohomological input — the inclusion
of the zero scheme is an isomorphism on global functions — into the topological conclusion. The
source phrases it as "`R_n` is either zero, or contains a nontrivial idempotent, so
`Γ(X, 𝒪_X) → R_n` cannot be an isomorphism".

## Main results

* `Stacks.AmpleSectionConnected.exists_isIdempotentElem_ne_zero_ne_one`: a scheme that is not
  preconnected has a nontrivial idempotent global function.
* `Stacks.AmpleSectionConnected.connectedSpace_of_bijective_appTop`: a scheme whose ring of
  global functions is identified, by a morphism to a connected scheme, with that scheme's ring
  of global functions is connected.

## Implementation notes

Nonemptiness of `Z` is not assumed in the second result: it is *derived*, because a bijection
onto `Γ(Z, 𝒪_Z)` from the nontrivial ring `Γ(X, 𝒪_X)`
(`AlgebraicGeometry.Scheme.component_nontrivial`, `X` being nonempty) forces `Γ(Z, 𝒪_Z)` to be
nontrivial, and the sections over the empty space form the terminal — hence trivial — ring. This
is the "either `R_n` is zero" half of the source's dichotomy.

## References

* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AmpleSectionConnected

/-- **A scheme that is not preconnected carries a nontrivial idempotent global function.** The
clopen set witnessing the failure of preconnectedness is the basic open of an idempotent, and
that idempotent is neither `0` nor `1` because the clopen set is neither empty nor everything. -/
@[ega "III 7.8.6.1" "special case"]
theorem exists_isIdempotentElem_ne_zero_ne_one (Z : Scheme.{u})
    (hZ : ¬ PreconnectedSpace Z) :
    ∃ e : Γ(Z, ⊤), IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  rw [preconnectedSpace_iff_clopen] at hZ
  push Not at hZ
  obtain ⟨s, hs, hsempty, hsuniv⟩ := hZ
  obtain ⟨e, he, hbasic⟩ :=
    AlgebraicGeometry.exists_isIdempotentElem_basicOpen_eq Z ⟨s, hs.isOpen⟩ hs.isClosed
  have hset : ((Z.basicOpen e : Z.Opens) : Set Z) = s :=
    congrArg (fun U : Z.Opens => (U : Set Z)) hbasic
  refine ⟨e, he, ?_, ?_⟩
  · rintro rfl
    exact hsempty.ne_empty (by simpa using hset.symm)
  · rintro rfl
    exact hsuniv (by simpa using hset.symm)

/-- **A morphism to a connected scheme which is bijective on global functions has connected
source.** Nonemptiness comes from injectivity, and preconnectedness from surjectivity together
with injectivity: a nontrivial idempotent of `Γ(Z, 𝒪_Z)` lifts to an element of `Γ(X, 𝒪_X)`
which injectivity forces to be idempotent, hence `0` or `1` by connectedness of `X`, hence the
original idempotent was trivial after all. -/
theorem connectedSpace_of_bijective_appTop {X Z : Scheme.{u}} [ConnectedSpace X] (i : Z ⟶ X)
    (hbij : Function.Bijective (i.appTop).hom) : ConnectedSpace Z := by
  have : Nonempty Z := by
    -- If `Z` were empty, `Γ(Z, 𝒪_Z)` would be the trivial ring, and injectivity on global
    -- functions would force `0 = 1` in `Γ(X, 𝒪_X)`, which is nontrivial because `X` is
    -- connected and hence nonempty.
    by_contra hne
    let : IsEmpty Z := ⟨fun z => hne ⟨z⟩⟩
    have htop : (⊤ : Z.Opens) = ⊥ := by
      ext z
      exact isEmptyElim z
    have hΓ : Subsingleton Γ(Z, ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty htop)
    have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
    have : Nontrivial Γ(X, ⊤) := Scheme.component_nontrivial X ⊤
    exact zero_ne_one (hbij.1 (Subsingleton.elim _ _) : (0 : Γ(X, ⊤)) = 1)
  have hpreconn : PreconnectedSpace Z := by
    by_contra hpre
    obtain ⟨e, he, he0, he1⟩ := exists_isIdempotentElem_ne_zero_ne_one Z hpre
    obtain ⟨a, ha⟩ := hbij.2 e
    have haidem : IsIdempotentElem a :=
      hbij.1 (by rw [map_mul, ha, he.eq])
    have hXpre : _root_.IsPreconnected ((⊤ : X.Opens) : Set X) := by
      rw [TopologicalSpace.Opens.coe_top]
      exact isPreconnected_univ
    rcases Stacks.AlgebraicGeometry.ProperGeomConnected.isIdempotentElem_eq_zero_or_one
        hXpre haidem with rfl | rfl
    · exact he0 (by rw [← ha, map_zero])
    · exact he1 (by rw [← ha, map_one])
  exact { toPreconnectedSpace := hpreconn, toNonempty := ‹Nonempty Z› }

end Stacks.AmpleSectionConnected

end
