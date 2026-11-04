module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Topology.Connected.ComponentSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.StrictlyHenselianFromRetractions
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ExtremallyDisconnectedComponents
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ProfiniteComponentRealization
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Flatness
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings
public import StacksFrontier.Topology.ExtremallyDisconnected.Characterization
public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.Profinite.Defs
public import StacksFrontier.Topology.Spectral.ComponentSpace

/-!
# Necessary conditions for w-contractibility

A ring `A` is w-contractible when every faithfully flat weakly étale `A`-algebra admits a
retraction. Weakly étale is a weaker condition than ind-étale, so w-contractibility implies that
every faithfully flat ind-étale `A`-algebra admits a retraction. In turn, that retraction property
forces the local-global conditions `Spec A` is w-local, `π₀(Spec A)` is extremally disconnected,
and the localization of `A` at each maximal ideal is strictly henselian.

## Main results

* `indEtale_of_isIndZariski`: an ind-Zariski algebra is ind-étale.
* `indEtale_faithfullyFlat_retracts_of_isWContractible`: faithfully flat ind-étale algebras over
  a w-contractible ring admit retractions.
* `wLocal_extremallyDisconnected_strictlyHenselian_of_indEtale_faithfullyFlat_retracts`: the
  retraction property for faithfully flat ind-étale algebras makes `Spec A` w-local, `π₀(Spec A)`
  extremally disconnected, and the local rings of `A` at its maximal ideals strictly henselian.
* `wLocal_extremallyDisconnected_strictlyHenselian_of_isWContractible`: the same three
  conditions for a w-contractible ring.

## Implementation notes

Ind-étaleness is `StacksDraft.IndEtale` and ind-Zariskiness is
`AlgebraicGeometry.ProEtale.IsIndZariski`. A retraction of the structure map of an algebra is an
algebra homomorphism back to the base ring.

## References

* [Stacks Project, Tag 0981](https://stacks.math.columbia.edu/tag/0981)
* [Stacks Project, Tag 0982](https://stacks.math.columbia.edu/tag/0982)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

/-- An ind-Zariski algebra is ind-étale. -/
theorem indEtale_of_isIndZariski (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : IsIndZariski.{u, u, u} A B) : StacksDraft.IndEtale A B := by
  obtain ⟨J, hJ, hfilt, pres, hp⟩ := h
  refine ⟨J, hJ, hfilt, pres, fun j => ?_⟩
  have : Algebra.IsLocalIso A (pres.diag.obj j) := hp j
  infer_instance

/-- Over a w-contractible ring every faithfully flat ind-étale algebra admits a retraction. -/
theorem indEtale_faithfullyFlat_retracts_of_isWContractible (A : Type u) [CommRing A]
    (h : ProetaleWContractible.IsWContractible.{u, u} A) (B : Type u) [CommRing B]
    [Algebra A B] (hff : Module.FaithfullyFlat A B) (hie : StacksDraft.IndEtale A B) :
    Nonempty (B →ₐ[A] A) :=
  h B ((Algebra.weaklyEtale_iff A B).mp (Algebra.weaklyEtale_of_ind_etale hie)) hff

/-- If every faithfully flat ind-étale algebra over `A` admits a retraction, then `Spec A` is
w-local. -/
theorem wLocalSpace_of_indEtale_faithfullyFlat_retracts (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      StacksDraft.IndEtale A B → Nonempty (B →ₐ[A] A)) :
    WLocalSpace (PrimeSpectrum A) :=
  wLocalSpace_of_indZariski_faithfullyFlat_retracts.{u, u} A
    fun B _ _ hff hind => h B hff (indEtale_of_isIndZariski A B hind)

/-- If every faithfully flat ind-étale algebra over `A` admits a retraction, then the
localization of `A` at each maximal ideal is strictly henselian. -/
theorem localizationAtPrime_strictlyHenselian_of_indEtale_faithfullyFlat_retracts
    (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      StacksDraft.IndEtale A B → Nonempty (B →ₐ[A] A))
    (m : Ideal A) [m.IsMaximal] :
    StrictlyHenselianLocalRing (Localization.AtPrime m) :=
  localizationAtPrime_strictlyHenselian_of_etale_faithfullyFlat_retracts A
    (fun B _ _ _ _ => h B inferInstance
      (StacksDraft.indEtale_iff.mpr ((CommAlgCat.etale A).le_ind _ inferInstance))) m

/-- If every faithfully flat ind-étale algebra over `A` admits a retraction, then `π₀(Spec A)` is
extremally disconnected. -/
theorem extremallyDisconnected_connectedComponents_of_indEtale_faithfullyFlat_retracts
    (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      StacksDraft.IndEtale A B → Nonempty (B →ₐ[A] A)) :
    ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) :=
  extremallyDisconnected_of_indZariski_faithfullyFlat_retracts.{u, u} A
    fun B _ _ hff hind => h B hff (indEtale_of_isIndZariski A B hind)

/-- The spectrum of a w-contractible ring is w-local. -/
theorem wLocalSpace_of_isWContractible (A : Type u) [CommRing A]
    (h : ProetaleWContractible.IsWContractible.{u, u} A) : WLocalSpace (PrimeSpectrum A) :=
  wLocalSpace_of_indEtale_faithfullyFlat_retracts A
    (indEtale_faithfullyFlat_retracts_of_isWContractible A h)

/-- The localization of a w-contractible ring at a maximal ideal is strictly henselian. -/
@[stacks 0982 "(1) ⇒ (3)(c)"]
theorem localizationAtPrime_strictlyHenselian_of_isWContractible (A : Type u) [CommRing A]
    (h : ProetaleWContractible.IsWContractible.{u, u} A) (m : Ideal A) [m.IsMaximal] :
    StrictlyHenselianLocalRing (Localization.AtPrime m) :=
  localizationAtPrime_strictlyHenselian_of_indEtale_faithfullyFlat_retracts A
    (indEtale_faithfullyFlat_retracts_of_isWContractible A h) m

/-- The space of connected components of the spectrum of a w-contractible ring is extremally
disconnected. -/
theorem extremallyDisconnected_connectedComponents_of_isWContractible (A : Type u) [CommRing A]
    (h : ProetaleWContractible.IsWContractible.{u, u} A) :
    ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) :=
  extremallyDisconnected_connectedComponents_of_indEtale_faithfullyFlat_retracts A
    (indEtale_faithfullyFlat_retracts_of_isWContractible A h)

/-- If every faithfully flat ind-étale algebra over `A` admits a retraction, then `Spec A` is
w-local, `π₀(Spec A)` is extremally disconnected, and the localization of `A` at each maximal
ideal is strictly henselian. -/
theorem wLocal_extremallyDisconnected_strictlyHenselian_of_indEtale_faithfullyFlat_retracts
    (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      StacksDraft.IndEtale A B → Nonempty (B →ₐ[A] A)) :
    WLocalSpace (PrimeSpectrum A) ∧
      ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
      ∀ (m : Ideal A) [m.IsMaximal],
        StrictlyHenselianLocalRing (Localization.AtPrime m) :=
  ⟨wLocalSpace_of_indEtale_faithfullyFlat_retracts A h,
    extremallyDisconnected_connectedComponents_of_indEtale_faithfullyFlat_retracts A h,
    fun m _ => localizationAtPrime_strictlyHenselian_of_indEtale_faithfullyFlat_retracts A h m⟩

/-- The spectrum of a w-contractible ring is w-local, its space of connected components is
extremally disconnected, and its localizations at maximal ideals are strictly henselian. -/
theorem wLocal_extremallyDisconnected_strictlyHenselian_of_isWContractible (A : Type u)
    [CommRing A] (h : ProetaleWContractible.IsWContractible.{u, u} A) :
    WLocalSpace (PrimeSpectrum A) ∧
      ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
      ∀ (m : Ideal A) [m.IsMaximal],
        StrictlyHenselianLocalRing (Localization.AtPrime m) :=
  wLocal_extremallyDisconnected_strictlyHenselian_of_indEtale_faithfullyFlat_retracts A
    (indEtale_faithfullyFlat_retracts_of_isWContractible A h)

end AlgebraicGeometry.ProEtale

end
