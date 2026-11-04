module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Divisors.AmpleFamilyRegular
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TriangleAdditivityQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.SectionImageIdeal
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealCoveringResolutionNoetherian
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.StacksAttribute

/-!
# The resolution property of a Noetherian regular scheme

[Stacks, Tag 0F8A] — a quasi-compact regular scheme with affine diagonal has the resolution
property — is proved in this development as
`AlgebraicGeometry.hasResolutionProperty_of_isRegular`, carrying **two** hypotheses: the
substantial direction of [Stacks, Tag 0F89] quantified over all schemes
(`AlgebraicGeometry.IdealCoveringImpliesResolutionProperty`), and the sheaf of ideals cut out by
a global section of an invertible module (`AlgebraicGeometry.ExistsSectionImageIdeal`).

This file removes both, for a **Noetherian** scheme.

The second is now a theorem: `AlgebraicGeometry.existsSectionImageIdeal` of
`StacksFrontier/AlgebraicGeometry/Perfect/SectionImageIdeal.lean`.  The first is a theorem for a
Noetherian scheme, `AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian`;
what kept it from discharging the carried hypothesis is only that the hypothesis quantifies over
*all* schemes, while [Stacks, Tag 0GMM] and [Stacks, Tag 0F8A] apply it to the one scheme in
their own statement.  Repackaging the Noetherian theorem at
`AlgebraicGeometry.IsIdealAffineCovering` and rerunning the two proofs with it in place of the
hypothesis therefore costs nothing, and both tags become unconditional over a Noetherian scheme.

## Main results

* `AlgebraicGeometry.idealCoveringImpliesResolutionProperty_of_isNoetherian`: the substantial
  direction of [Stacks, Tag 0F89] for a Noetherian scheme, in the shape [Stacks, Tag 0GMM]
  consumes it — over the data `AlgebraicGeometry.IsIdealAffineCovering` rather than over its
  four fields.
* `AlgebraicGeometry.hasResolutionProperty_of_isRegular_of_isNoetherian`:
  **[Stacks, Tag 0F8A] for a Noetherian scheme, unconditionally.**
* `AlgebraicGeometry.hasResolutionProperty_of_smooth_isProper_over_field`: the form in which the
  proof of [Stacks, Tag 0G0E] needs it — **a scheme smooth and proper over a field has the
  resolution property**, with no hypothesis beyond smoothness and properness.  Every instance the
  route asks for is derived here: Noetherianness and quasi-compactness from properness over a
  field, the affine diagonal from separatedness, and regularity from smoothness by
  [Stacks, Tag 056S].

## Implementation notes

*The one place the two shapes differ.*
`hasResolutionProperty_of_epi_idealPow_of_isNoetherian` asks for
`((I j).support.compl : X.Opens) = U j`, an equality of opens, while
`AlgebraicGeometry.IsIdealAffineCovering.support_eq` supplies
`((I j).support : Set X) = ((U j : Set X))ᶜ`, an equality of sets in the other direction.  The
crossing is `TopologicalSpace.Opens.ext` followed by `compl_compl`; the finite-type field of
`IsIdealAffineCovering` is not consumed at all, the Noetherian theorem deriving the finite
generation it needs from `IsNoetherian X`.

*Why this does not discharge `IdealCoveringImpliesResolutionProperty` itself.*  That abbreviation
quantifies over every scheme, with no Noetherian hypothesis, and the Noetherian theorem does not
prove it — the general case of [Stacks, Tag 0F89] is still not in this development.  What is
shown here is that the *consumers* of the hypothesis never need it in its quantified generality:
each applies it to the scheme in its own statement, so a Noetherian hypothesis on that scheme
replaces it.

*The chain of instances for a smooth proper scheme over a field.*  `IsProper f` unfolds to
`IsSeparated f`, `UniversallyClosed f` and `LocallyOfFiniteType f`, and `UniversallyClosed f`
gives `QuasiCompact f`, so `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType` applies over
the Noetherian `Spec k` and `IsNoetherian X` carries `CompactSpace X` with it.  For the affine
diagonal, `terminal.from X` factors as `f ≫ terminal.from (Spec k)`, whose second leg is a
morphism of affine schemes, hence affine, hence separated; a composite of separated morphisms is
separated, the diagonal of a separated morphism is a closed immersion, and a closed immersion is
affine.

## References

* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 0F8A](https://stacks.math.columbia.edu/tag/0F8A)
* [Stacks Project, Tag 0GML](https://stacks.math.columbia.edu/tag/0GML)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.IdealPowerColimit

/-- **The substantial direction of [Stacks, Tag 0F89] for a Noetherian scheme**, in the shape
`AlgebraicGeometry.IdealCoveringImpliesResolutionProperty` is stated in: a Noetherian scheme
carrying a finite affine open covering cut out by sheaves of ideals, each of which is a quotient
of a finite locally free module, has the resolution property.

This is `AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian` repackaged over
the bundled data `AlgebraicGeometry.IsIdealAffineCovering`; the finite-type field of that
structure is not used, the Noetherian hypothesis supplying it. -/
-- No `@[stacks 0F89]`: Tag 0F89 is not restricted to Noetherian schemes, so this proves a
-- special case of its substantial direction, and a tag goes only on a declaration stating the
-- whole tag.  The base registration of the immediate direction is untouched.
theorem idealCoveringImpliesResolutionProperty_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    {m : ℕ} (U : Fin m → X.Opens) (I : Fin m → X.IdealSheafData)
    (hcov : IsIdealAffineCovering X U I)
    (hq : ∀ j, ∃ (E : X.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (q : E ⟶ idealPow (I j) 1), Epi q) :
    HasResolutionProperty X := by
  choose E hE q hq using hq
  refine hasResolutionProperty_of_epi_idealPow_of_isNoetherian U I hcov.isAffineOpen
    hcov.iSup_eq_top (fun j => ?_) E hE q hq
  refine TopologicalSpace.Opens.ext ?_
  show ((I j).support : Set X)ᶜ = (U j : Set X)
  rw [hcov.support_eq j, compl_compl]

/-- **[Stacks, Tag 0F8A] for a Noetherian scheme, unconditionally.** A Noetherian regular scheme
with affine diagonal has the resolution property.

A quasi-compact regular scheme with affine diagonal carries an ample family of invertible modules
by [Stacks, Tag 0GML] (`AlgebraicGeometry.exists_isAmpleFamily_of_isRegular`), and
`Stacks.Chow.hasResolutionProperty_of_isAmpleFamily_of_isNoetherian` applies to it.
Quasi-compactness is not a separate hypothesis here: `IsNoetherian X` carries `CompactSpace X`. -/
-- No `@[stacks 0F8A]`: the tag assumes a quasi-compact regular scheme with affine diagonal and
-- NOT Noetherianness (checked against the source), so this is a special case of it.
@[sga "3 VIB 13.3" "more general"]
theorem hasResolutionProperty_of_isRegular_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X) :
    HasResolutionProperty X := by
  obtain ⟨_, _, hL⟩ := exists_isAmpleFamily_of_isRegular X hX
  exact Stacks.Chow.hasResolutionProperty_of_isAmpleFamily_of_isNoetherian hL

/-- **A scheme smooth and proper over a field has the resolution property.**

This is the form the proof of [Stacks, Tag 0G0E] asks for: [Stacks, Tag 0FZ0] is stated with
`AlgebraicGeometry.HasResolutionProperty` on the two factors of the product, and the hypotheses
available there are smoothness and properness over a field.  Each instance the route needs is
derived here — `IsNoetherian X` from properness over the Noetherian `Spec k`, the affine diagonal
from separatedness, and `AlgebraicGeometry.IsRegular X` from smoothness by [Stacks, Tag 056S] —
so nothing is assumed beyond `Smooth f` and `IsProper f`. -/
@[sga "3 VIB 13.3" "special case"]
theorem hasResolutionProperty_of_smooth_isProper_over_field {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f] :
    HasResolutionProperty X := by
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]; infer_instance
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  exact hasResolutionProperty_of_isRegular_of_isNoetherian X (isRegular_of_smooth_over_field f)

end AlgebraicGeometry

end
