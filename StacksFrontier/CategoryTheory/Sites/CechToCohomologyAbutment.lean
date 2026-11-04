module

public import StacksFrontier.CategoryTheory.Sites.CechToCohomologyFunctorial
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cech
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceAbutmentIsCohomology
public import StacksFrontier.CategoryTheory.Sites.IntegralCechComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The abutment of the functorial Čech-to-cohomology spectral sequence

Let `C` be a small site given by a pretopology `J`, let `U` be an object of `C` and let
`𝒰 = {U_i → U}` be a covering family of `U`. [Stacks, Tag 03AZ] asserts the spectral sequence

```
E₂^{p,q} = Ȟ^p(𝒰, H^q(F))  ⟹  H^{p+q}(U, F),
```

functorially in the abelian sheaf `F`.
`StacksFrontier/CategoryTheory/Sites/CechToCohomologyFunctorial.lean` supplies the functor, the
natural second-page identification and a functorial finite filtered abutment, the abutment being
the cohomology of the total complex of the double complex `A^{i,j}(F) = Č^j(𝒰, I^i(F))`. This file
supplies the remaining clause: that abutment **is** the sheaf cohomology `H^n(U, F)`, naturally in
`F`.

## The route

The Čech simplicial semi-representable object `K(𝒰) = Stacks.CechSite.cechSimplicialObject` of a
*covering* family is a hypercovering of `U`, so the abutment identification of clause (3) of
[Stacks, Tag 01GY] applies to it verbatim: nothing about the Čech situation has to be redone.
Concretely, `Stacks.CechSite.cechSimplicialObject E` is the Čech object
`Mathlib.CategoryTheory.Limits.FormalCoproduct.cech` of
`Stacks.IntegralCech.famFormalCoproduct E` on the nose — the two definitions differ only in which
`CategoryTheory.Limits.HasProduct` instance they name, and `HasProduct` is a proposition — so
`Stacks.CategoryTheory.Hypercovering.isHypercovering_cech_of_isCoveringOver`, Tag 01G6 for an
arbitrary covering family, gives the hypercovering property, and
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso` together with its
naturality in the sheaf gives the identification.

## Main definitions

* `Stacks.CechSite.cechToCohomologyAbutmentIso`: `H^n(Tot(Č^•(𝒰, I^•(F)))) ≅ H^n(U, F)`, as an
  isomorphism of functors of the sheaf.
* `Stacks.CechSite.cechToCohomologySheafCohomologyAbutment`: **the functorial finite filtered
  abutment of the functorial Čech-to-cohomology spectral sequence, abutting to `H^{p+q}(U, F)`.**
* `Stacks.CechSite.cechToCohomologySheafCohomologyAbutmentAt`: the same read at one sheaf.

## Main results

* `Stacks.CechSite.isHypercovering_cechSimplicialObject`: the Čech simplicial semi-representable
  object of a covering family is a hypercovering of the covered object. This is Tag 01G6 at the
  spelling `Stacks.CechSite.cechSimplicialObject`, which is the one the Čech complex of
  [Stacks, Tag 03AM] is built on.

## Implementation notes

The site is taken small and the family indexed in the same universe, as in
`StacksFrontier/CategoryTheory/Sites/CechToCohomologyFunctorial.lean`; the topology is given by a
pretopology because that is what a hypercovering is defined against, and the Grothendieck
topology the sheaves live on is `CategoryTheory.Pretopology.toGrothendieck` of it.

The products indexing the Čech object are the selected ones asked for by
`Stacks.CechSite.cechSimplicialObject` -- only the finite nonempty fibre products of the family,
not all finite products of `Over U`. The comparison with `FormalCoproduct.cech`, which does ask
for all of them, is nonetheless an equality rather than an isomorphism: `HasPullbacks C` supplies
`HasFiniteProducts (Over U)`, and since `CategoryTheory.Limits.HasProduct` is a proposition the
two product objects are the same term up to proof irrelevance. This is what keeps the hypercovering
property transportable with no comparison morphism, and with it the abutment identification: a
covering family of a pretopology need *not* stay covering under an arbitrary isomorphism of
`SR(C, U)`, as the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/Cech.lean` record.

## References

* [Stacks Project, Tag 03AZ](https://stacks.math.columbia.edu/tag/03AZ)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01G6](https://stacks.math.columbia.edu/tag/01G6)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v

namespace Stacks.CechSite

open Stacks.CategoryTheory.Hypercovering Stacks.CategoryTheory.Hypercovering.Functorial
open Stacks.Cohomology.Leray Stacks.IntegralCech

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (J : Pretopology C) {U : C}
  (E : PreZeroHypercover.{v} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]

/-! ### The Čech object of a covering family is a hypercovering -/

/-- **The Čech simplicial semi-representable object of a covering family is a hypercovering of
the covered object.** This is [Stacks, Tag 01G6] at the spelling
`Stacks.CechSite.cechSimplicialObject`, on which the Čech complex of [Stacks, Tag 03AM] is built:
that object is the Čech object `FormalCoproduct.cech` of
`Stacks.IntegralCech.famFormalCoproduct` on the nose, and the covering hypothesis of
`Stacks.CategoryTheory.Hypercovering.isHypercovering_cech_of_isCoveringOver` is the presieve of
the family by
`Stacks.CategoryTheory.Hypercovering.isCoveringOver_terminal_from_of_mem`. -/
theorem isHypercovering_cechSimplicialObject (hE : E.presieve₀ ∈ J U) :
    IsHypercovering J (cechSimplicialObject E) := by
  let : HasTerminal (Over U) := Over.over_hasTerminal U
  let : HasBinaryProducts (Over U) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let : HasFiniteProducts (Over U) := hasFiniteProducts_of_has_binary_and_terminal
  exact isHypercovering_cech_of_isCoveringOver J (famFormalCoproduct E)
    (isCoveringOver_terminal_from_of_mem J (famFormalCoproduct E) hE)

/-! ### The abutment identification -/

/-- **`H^n(Tot(Č^•(𝒰, I^•(F)))) ≅ H^n(U, F)`, naturally in the abelian sheaf `F`.** The
cohomology of the total complex of the double complex `A^{i,j}(F) = Č^j(𝒰, I^i(F))`, which the
functorial filtered abutment `Stacks.CechSite.cechToCohomologyFunctorialAbutment` abuts to, is
the sheaf cohomology of `F` on the covered object, which is what [Stacks, Tag 03AZ] asserts it
abuts to.

Its components are
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso` at the hypercovering
`Stacks.CechSite.isHypercovering_cechSimplicialObject` and its naturality is
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso_naturality_sheaf`; the
morphism of cohomology the filtration functor moves along is `H^n` of
`hypercoverFilteredMap` at `(𝟙 K(𝒰), f)`, which is exactly the shape that lemma is stated in. -/
noncomputable def cechToCohomologyAbutmentIso (hE : E.presieve₀ ∈ J U) (n : ℕ) :
    sheafToCechPair J.toGrothendieck E ⋙
        hypercoverFiltrationFunctor U J.toGrothendieck (n : ℤ) ⋙ FilteredObject.forget ≅
      Sheaf.cohomologyPresheafFunctor J.toGrothendieck n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op U) :=
  NatIso.ofComponents
    (fun F ↦ hypercoverAbutmentIso U J (isHypercovering_cechSimplicialObject J E hE) F n)
    (fun {_ _} f ↦ hypercoverAbutmentIso_naturality_sheaf U J
      (isHypercovering_cechSimplicialObject J E hE) f n)

/-- **The abutment clause of [Stacks, Tag 03AZ]**: the functorial Čech-to-cohomology spectral
sequence of a covering family `𝒰 = {U_i → U}` abuts, through a finite decreasing filtration whose
graded pieces are its infinity terms, to the sheaf cohomology `H^{p+q}(U, F)` — all of it
naturally in the abelian sheaf `F`.

Together with `Stacks.CechSite.cechToCohomologySpectralSequenceFunctor` and
`Stacks.CechSite.cechToCohomologyPageTwoIso` this is the whole of [Stacks, Tag 03AZ] in functorial
form: a functor from abelian sheaves to first-quadrant `E₂` cohomological spectral sequences, a
natural identification of its second page with `Ȟ^p(𝒰, H^q(F))` and a functorial filtered
abutment to `H^{p+q}(U, F)`.

It is `Stacks.CechSite.cechToCohomologyFunctorialAbutment` with its abutment transported along
`Stacks.CechSite.cechToCohomologyAbutmentIso`;
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofIsoAbutment` touches no other field --
the asserted abutment is mentioned in `abutmentIso` alone, so the filtration, its finiteness, its
top and bottom steps and the graded identification are the ones already proved. -/
@[stacks 03AZ "the abutment of the functorial spectral sequence is `H^{p+q}(U, F)`",
  sga "4 V 3.2" "abutment (covering)", sga "4 V 3.3" "partial"]
noncomputable def cechToCohomologySheafCohomologyAbutment (hE : E.presieve₀ ∈ J U) :
    FunctorialFirstQuadrantAbutsTo
      (cechToCohomologySpectralSequenceFunctor J.toGrothendieck E)
      (fun n ↦ Sheaf.cohomologyPresheafFunctor J.toGrothendieck n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op U)) :=
  (cechToCohomologyFunctorialAbutment J.toGrothendieck E).ofIsoAbutment
    (cechToCohomologyAbutmentIso J E hE)

/-- **The abutment clause of [Stacks, Tag 03AZ] read at one sheaf.** For each abelian sheaf `F`
the Čech-to-cohomology spectral sequence of `F` abuts, through a finite decreasing filtration
whose graded pieces are its infinity terms, to `H^n(U, F)`. This is the convergence structure
`Stacks.Cohomology.Leray.FirstQuadrantAbutment` records, and the objectwise reading of
`Stacks.CechSite.cechToCohomologySheafCohomologyAbutment`. -/
noncomputable def cechToCohomologySheafCohomologyAbutmentAt (hE : E.presieve₀ ∈ J U)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    FirstQuadrantAbutment ((cechToCohomologySpectralSequenceFunctor J.toGrothendieck E).obj F)
      (fun n ↦ ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).obj F).obj (op U)) :=
  (cechToCohomologySheafCohomologyAbutment J E hE).toFirstQuadrantAbutment F

end Stacks.CechSite

end
