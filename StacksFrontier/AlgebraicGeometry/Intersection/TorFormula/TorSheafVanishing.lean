module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.StalkRingComparison
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.RingTheory.Tor.ProjectiveDimension
import StacksCore.Tactic.StacksAttribute

/-!
# The Tor sheaves of a regular scheme vanish above its dimension

Let `X` be a regular scheme of dimension at most `d`. For `𝒪_X`-modules `ℱ` and `𝒢` the Tor
sheaf `Tor_p^{𝒪_X}(ℱ, 𝒢)` vanishes for every `p > d`. On a nonsingular variety, where `d` may be
taken to be `dim X`, this is the vanishing clause of Lemma 43.14.2.

The argument is the source's. A sheaf of modules is zero exactly when all of its stalks are, and
the stalk of the Tor sheaf is the Tor module of the stalks. The local ring at a point of a
regular scheme is a regular local ring, and its Krull dimension is at most the dimension of the
scheme; over a regular local ring of dimension `d₀` the global dimension is `d₀`, so every module
has projective dimension at most `d₀ ≤ d`, and `Tor_p` against a module of projective dimension
at most `d` vanishes for `p > d`.

## Main results

* `AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing` — the algebraic step: over a
  regular local ring of dimension at most `d`, `Tor_p` vanishes for `p > d`.
* `AlgebraicGeometry.TorFormula.isZero_torSheaf_of_lt` — **Tag 0AZT, the vanishing clause.**

## Implementation notes

The dimension bound on the local rings comes from the dimension of the scheme through
`topologicalKrullDim_eq_iSup_krullDimOfRing_stalk` (Tag 04MU), which expresses the dimension of a
scheme as the supremum of the Krull dimensions of its local rings, so the bound is uniform in the
point — which is what a statement about the sheaf, rather than about one stalk, requires.

The two stalk rings of
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.StalkRingComparison` both appear:
regularity and the dimension bound are natural over the `CommRingCat`-valued stalk, while the
Tor module produced by the stalk comparison lives over the `RingCat`-valued one. They are
transported across `stalkRingEquiv` by `IsRegularLocalRing.of_ringEquiv` and
`ringKrullDim_eq_of_ringEquiv`.

## References

* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
* [Stacks Project, Tag 00OE](https://stacks.math.columbia.edu/tag/00OE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.TorFormula

/-- **Over a regular local ring of dimension at most `d`, `Tor_p` vanishes for `p > d`.** The
global dimension of a regular local ring is its Krull dimension, so every module has projective
dimension at most `d`, and `Tor` above the projective dimension of its first argument is
zero. -/
@[sga "6 IX 1.5" "Direction"]
theorem isZero_Tor_of_isRegularLocalRing {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (M N : ModuleCat.{u} A) (d p : ℕ)
    (hdim : ringKrullDim A ≤ (d : WithBot ℕ∞)) (hdp : d < p) :
    IsZero (((Tor (ModuleCat.{u} A) p).obj M).obj N) := by
  obtain ⟨d₀, hd₀⟩ : ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) := by
    have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
    cases hx : ringKrullDim A with
    | bot => exact (ringKrullDim_ne_bot hx).elim
    | coe y =>
      cases y with
      | top => exact (htop (by simpa using hx)).elim
      | coe n => exact ⟨n, by simp⟩
  have hsup : (⨆ K : ModuleCat.{u} A, projectiveDimension K) = (d₀ : WithBot ℕ∞) :=
    ((Stacks.RegularRing.GlobalDimension.solution d₀).out 1 2).mpr
      (⟨((Stacks.RegularRing.FiniteGlobalDimension.solution (R := A)).out 1 3).mp
        ‹IsRegularLocalRing A›, hd₀⟩ : IsRegularRing A ∧ _)
  have hd₀d : d₀ ≤ d := by
    rw [hd₀] at hdim
    exact_mod_cast hdim
  have hpd : HasProjectiveDimensionLE M d := by
    rw [← projectiveDimension_le_iff]
    exact ((le_iSup (fun K : ModuleCat.{u} A ↦ projectiveDimension K) M).trans hsup.le).trans
      (by exact_mod_cast hd₀d)
  exact StacksDraft.ProjectiveDimension.isZero_Tor_of_hasProjectiveDimensionLE M N d p hpd hdp

/-- The Krull dimension of the local ring at a point of a scheme is at most the dimension of the
scheme: the latter is the supremum of the former over all points. -/
@[ega "IV 5.1.4" "partial"]
alias ringKrullDim_stalk_le :=
  Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim

/-- **Stacks 0AZT: the Tor sheaves of a regular scheme vanish above its dimension.** If every
local ring of `X` is regular and `dim X ≤ d`, then `Tor_p^{𝒪_X}(ℱ, 𝒢) = 0` for every `p > d` and
all `𝒪_X`-modules `ℱ`, `𝒢`. -/
@[stacks 0AZT "the vanishing clause: on a scheme all of whose local rings are regular and whose \
dimension is at most `d`, the Tor sheaf `Tor_p^{𝒪_X}(ℱ, 𝒢)` vanishes for `p > d`. The source \
states it for a nonsingular variety with the bound `dim X`, which is the case `d = dim X` of \
this; the bound is a parameter here because the dimension of a general scheme need not be \
finite. No hypothesis on the two modules is needed, where the source assumes them coherent. The \
coherence, support and stalk clauses are `isCoherent_torSheaf_of_isRegular`, \
`supp_torSheaf_subset_inter` and `torSheafStalkIso`."]
theorem isZero_torSheaf_of_lt (X : Scheme.{u})
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (F G : X.Modules) (d p : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hdp : d < p) :
    IsZero (torSheaf X F G p) := by
  refine (AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
    X.ringCatSheaf (torSheaf X F G p)).mpr fun x ↦ ?_
  let _ : CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) :=
      StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x
  have := hreg x
  have hregStalk : IsRegularLocalRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) :=
    IsRegularLocalRing.of_ringEquiv (stalkRingEquiv X x).symm
  have hdimStalk : ringKrullDim (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) ≤ (d : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv (stalkRingEquiv X x)]
    exact (ringKrullDim_stalk_le X x).trans hd
  exact IsZero.of_iso
    (isZero_Tor_of_isRegularLocalRing _ _ d p hdimStalk hdp)
    (torSheafStalkIso X F G p x)

end AlgebraicGeometry.TorFormula

end
