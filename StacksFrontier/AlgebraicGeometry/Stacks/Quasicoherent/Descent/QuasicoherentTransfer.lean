module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Colimits of quasi-coherent modules, transferred along an equivalence

Let `R` be a sheaf of rings on a site.  Quasi-coherence of a sheaf of `R`-modules is a local
condition — on a covering of each object the module has a global presentation — and it is *not*
preserved by colimits on an arbitrary site: an infinite diagram of quasi-coherent modules
supplies one covering per index, and a general site has no common refinement of infinitely many
coverings.  What makes the clause true in the situations the source states it in is that the
quasi-coherent modules are the essential image of a colimit-preserving fully faithful functor
from a category in which the colimits are already known to exist.

That is exactly how Stacks 0GNC is proved: "the proof will be to use Lemma 06VE to transfer
these truths to `(Sch/S)_τ`", the functor being `𝓕 ↦ 𝓕^a` and the identification of its
essential image being Descent, Proposition 03DX.  This file isolates that transfer, so that the
remaining content of the clause is the identification of the essential image and nothing else.

## Main results

* `SheafOfModules.essImage_eq_isQuasicoherentOnSite`: a fully faithful functor landing in
  quasi-coherent modules and hitting all of them has the quasi-coherent modules as its
  essential image.
* `SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`: **Stacks 0GNC (1), (2),
  (3)** — such a functor, if it preserves colimits of shape `K` out of a category having them,
  makes quasi-coherence closed under colimits of shape `K`.
* `SheafOfModules.hasColimitsOfSize_quasicoherentOnSite`: **Stacks 0GNE (1), the existence
  half** — the category of quasi-coherent modules then has colimits.
* `SheafOfModules.preservesColimitsOfSize_quasicoherentOnSite_ι` and
  `SheafOfModules.preservesFiniteColimits_quasicoherentOnSite_ι`: **Stacks 06WV (4) and (3)**
  for the site — those colimits agree with the colimits of all module sheaves, and in
  particular the inclusion of the quasi-coherent modules is right exact.

## Implementation notes

The transfer step itself is
`CategoryTheory.Limits.instIsClosedUnderColimitsOfShapeEssImage`, the Mathlib instance saying
that the essential image of a fully faithful functor is closed under the colimits that functor
preserves.  The work here is only to recognise quasi-coherence as such an essential image; the
hypotheses `hF` and `hsurj` below are Stacks 03DV ("`𝓕^a` is quasi-coherent") and Stacks 03DX
(1) ("every quasi-coherent module on the big site is a `𝓕^a`"), and `[F.Full]`, `[F.Faithful]`
are Stacks 0GN7.  No hypothesis of this file is about colimits of quasi-coherent modules, which
is what distinguishes it from a restatement of the clause being proved.

The index shapes are `K : Type uK` with `Category.{uK} K`, and the size statements are
`HasColimitsOfSize.{uK, uK}` and `PreservesColimitsOfSize.{uK, uK}`.  A bare
`CategoryTheory.Limits.HasColimits` would instead bind the index universe to the *hom* universe
of the category of module sheaves, which is unrelated to the universe of the site; the source's
"has colimits" means small colimits indexed at the size of the site, and that is what the
equal-universe spelling says.  This follows the convention already written into this library
for the analogous clause of Stacks 09JJ.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uA vA uK u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}} {A : Type uA} [Category.{vA} A]
  (F : A ⥤ SheafOfModules.{m} R)

/-- A functor whose values are quasi-coherent and which hits every quasi-coherent module up to
isomorphism has the quasi-coherent modules as its essential image.  For `𝓕 ↦ 𝓕^a` on the big
site of a scheme the two hypotheses are Stacks 03DV and Stacks 03DX (1). -/
public theorem essImage_eq_isQuasicoherentOnSite
    (hF : ∀ a, (F.obj a).IsQuasicoherentOnSite)
    (hsurj : isQuasicoherentOnSite.{u, v, r, m} R ≤ F.essImage) :
    F.essImage = isQuasicoherentOnSite.{u, v, r, m} R :=
  le_antisymm
    (by
      rintro M ⟨a, ⟨e⟩⟩
      exact (isQuasicoherentOnSite.{u, v, r, m} R).prop_of_iso e (hF a))
    hsurj

/-- **Stacks 0GNC (1), (2), (3).**  Quasi-coherence of sheaves of modules on a site is closed
under colimits of shape `K`, provided the quasi-coherent modules are the essential image of a
fully faithful functor that preserves colimits of shape `K` out of a category having them.

This is the transfer Stacks performs with Lemma 06VE: parts (1), (2) and (3) of 0GNC are the
cases of `K` a discrete category, an arbitrary small category and
`CategoryTheory.Limits.WalkingParallelPair`.  On the big `τ`-site of a scheme the functor is
`𝓕 ↦ 𝓕^a`, which preserves colimits because it is a left adjoint (Stacks 06VE (2), (3)); the
colimits upstairs are those of quasi-coherent modules on the scheme itself. -/
public theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite [F.Full] [F.Faithful]
    (K : Type uK) [Category.{uK} K] [HasColimitsOfShape K A] [PreservesColimitsOfShape K F]
    (hF : ∀ a, (F.obj a).IsQuasicoherentOnSite)
    (hsurj : isQuasicoherentOnSite.{u, v, r, m} R ≤ F.essImage) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape K := by
  rw [ObjectProperty.isClosedUnderColimitsOfShape_iff,
    ← essImage_eq_isQuasicoherentOnSite F hF hsurj]
  exact ObjectProperty.IsClosedUnderColimitsOfShape.colimitsOfShape_le _ K

section Size

variable [HasColimitsOfSize.{uK, uK} (SheafOfModules.{m} R)]

/-- Closure of quasi-coherence under colimits of every shape `K : Type uK`, the hypothesis the
three results below share.  It is the conclusion of
`SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`, taken over all shapes. -/
public abbrev ClosedUnderColimitsOfSize (R : Sheaf J RingCat.{r}) : Prop :=
  ∀ (K : Type uK) [Category.{uK} K],
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape K

/-- **Stacks 0GNE (1), the existence half.**  Once quasi-coherence is closed under colimits of
every shape `K : Type uK`, the category of quasi-coherent modules has those colimits. -/
public theorem hasColimitsOfSize_quasicoherentOnSite
    (hclosed : ClosedUnderColimitsOfSize.{uK, u, v, r, m} R) :
    HasColimitsOfSize.{uK, uK} (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory := by
  constructor
  intro K _
  have := hclosed K
  infer_instance

/-- **Stacks 06WV (4), the comparison half.**  Colimits of quasi-coherent modules agree with
the colimits of the same diagram taken in all sheaves of modules: the inclusion of the
quasi-coherent modules preserves them. -/
public theorem preservesColimitsOfSize_quasicoherentOnSite_ι
    (hclosed : ClosedUnderColimitsOfSize.{uK, u, v, r, m} R) :
    PreservesColimitsOfSize.{uK, uK} (isQuasicoherentOnSite.{u, v, r, m} R).ι := by
  constructor
  intro K _
  have := hclosed K
  infer_instance

/-- **Stacks 06WV (3), right exactness.**  The inclusion of the quasi-coherent modules into all
sheaves of modules preserves finite colimits.  Stacks obtains this from part (4), and so does
this proof: right exactness is the finite-shape case of the comparison. -/
public theorem preservesFiniteColimits_quasicoherentOnSite_ι
    (hclosed : ClosedUnderColimitsOfSize.{uK, u, v, r, m} R) :
    PreservesFiniteColimits (isQuasicoherentOnSite.{u, v, r, m} R).ι :=
  have : PreservesColimitsOfSize.{uK, uK} (isQuasicoherentOnSite.{u, v, r, m} R).ι :=
    preservesColimitsOfSize_quasicoherentOnSite_ι.{uK} hclosed
  PreservesColimitsOfSize.preservesFiniteColimits _

end Size

end SheafOfModules

end
