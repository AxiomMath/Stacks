module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceAbutment
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSecondPage
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech-to-cohomology spectral sequence, functorially in the sheaf

Let `C` be a (small) site, `U` an object of `C` and `𝒰 = {U_i → U}` a family of morphisms with
target `U` whose finite nonempty fibre products exist. [Stacks, Tag 03AZ] produces, for an
abelian sheaf `F` on `C`, a cohomological spectral sequence

```
E₂^{p,q} = Ȟ^p(𝒰, H^q(F))  ⟹  H^{p+q}(U, F),
```

and asserts in its last sentence that **this spectral sequence is functorial in `F`**. The
spectral sequence itself, its second page and its convergence are carried by
`StacksFrontier/CategoryTheory/Sites/CechToCohomology.lean`, in the existential form that the
Grothendieck spectral sequence of [Stacks, Tag 015N] delivers; being existential, that form
carries no datum to be natural in. This file supplies the functoriality: a *functor* from
abelian sheaves to first-quadrant `E₂` cohomological spectral sequences, a *natural* isomorphism
identifying its second page with `Ȟ^p(𝒰, H^q(F))`, and a *functorial* finite filtered abutment.

## The construction

The Čech complex of `𝒰` is, by definition
(`Stacks.CechSite.cechComplexFunctor`), the complex of sections of the simplicial
semi-representable object `K(𝒰) = Stacks.CechSite.cechSimplicialObject`, the simplicial formal
coproduct of all finite nonempty fibre products of the family. So the Čech-to-cohomology spectral
sequence of `𝒰` is the spectral sequence of clause (3) of [Stacks, Tag 01GY] at `K(𝒰)`, and
nothing has to be built here: the two-variable functorial spectral sequence of a small site
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverSpectralSequenceFunctor`, its natural
second page `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverPageTwoIso` and its
functorial filtered abutment
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverFunctorialAbutment` are all stated for
an *arbitrary* simplicial semi-representable object over `U` and an arbitrary Grothendieck
topology, and this file restricts them along `F ↦ (K(𝒰), F)`.

That construction is the one the implementation notes of
`StacksFrontier/CategoryTheory/Sites/CechToCohomology.lean` name: the double complex
`A^{i,j}(F) = Č^j(𝒰, I^i(F))` of the Čech complexes of a *functorial* injective resolution
`I^•(F)` of `F`, with the resolution degree outer and the Čech degree inner, whose second
spectral sequence is presented from its second page because an injective resolution is
functorial in the sheaf only up to homotopy.

## Main definitions

* `Stacks.CechSite.cechCohomologyFunctor`: `Ȟ^p(𝒰, -)` on abelian presheaves on `C`.
* `Stacks.CechSite.sheafToCechPair`: the functor `F ↦ (K(𝒰), F)` along which the hypercovering
  spectral sequence is restricted.
* `Stacks.CechSite.cechToCohomologySpectralSequenceFunctor`: **the Čech-to-cohomology spectral
  sequence as a functor of the abelian sheaf**.
* `Stacks.CechSite.cechPageTwoFunctor`: the asserted second page `F ↦ Ȟ^p(𝒰, H^q(F))`, as a
  functor of the sheaf.
* `Stacks.CechSite.cechToCohomologyPageTwoIso`: its natural identification with the second page
  of the spectral sequence.
* `Stacks.CechSite.cechToCohomologyFunctorialAbutment`: the functorial finite filtered abutment
  of that spectral sequence.
* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.restrict`: a functorial filtered
  abutment restricts along any functor into its parameter category.

## Main results

* `Stacks.CechSite.cechCohomologyOverBifunctor_obj_cechSimplicialObject`: Čech cohomology of the
  family is Čech cohomology of its simplicial semi-representable object, on the nose — the
  identification the whole file rests on.
* `Stacks.CechSite.cechPageTwoFunctor_obj` and `Stacks.CechSite.cechPageTwoFunctor_map`: the
  second-page functor is `Ȟ^p(𝒰, H^q(-))` on objects and on morphisms.
* `Stacks.CechSite.cechToCohomologyPageTwoIso`: **the second page of the functorial spectral
  sequence is `Ȟ^p(𝒰, H^q(F))`, naturally in `F`.**

## What is proved and what is not

What is proved is the functoriality of the spectral sequence and of its second-page
identification, together with a functorial finite filtered abutment. The abutment is the
cohomology of the total complex of the double complex above; **this file does not identify that
abutment with the sheaf cohomology `H^n(U, F)`**, and no declaration below claims it. Convergence
to `H^{p+q}(U, F)` for one sheaf at a time is
`Stacks.CechSite.exists_cechToCohomology_spectralSequence_sheafCohomologyAbutment`, which is a
statement about the existential spectral sequence of [Stacks, Tag 03OW] and not about the functor
below; the two spectral sequences are not compared here.

That identification is supplied, for a *covering* family of a pretopology whose Grothendieck
topology is the one used here, by
`StacksFrontier/CategoryTheory/Sites/CechToCohomologyAbutment.lean`:
`Stacks.CechSite.cechToCohomologyAbutmentIso` is the natural isomorphism and
`Stacks.CechSite.cechToCohomologySheafCohomologyAbutment` the functorial filtered abutment to
`H^{p+q}(U, F)`. It needs no covering hypothesis *here*, which is why the two files are separate:
the spectral sequence, its second page and their functoriality hold for an arbitrary family with
the stated fibre products, and only the abutment clause asks the family to cover `U`.

The route taken there is the hypercovering development's own abutment identification,
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAbutmentIso`, which consumes
`Stacks.CategoryTheory.Hypercovering.IsHypercovering` for a pretopology: `K(𝒰)` is a
hypercovering of `U` exactly when `𝒰` is a covering family, by
`Stacks.CategoryTheory.Hypercovering.isHypercovering_cech_of_isCoveringOver`, Tag 01G6 for an
arbitrary covering family, so nothing Čech-specific has to be redone — in particular
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverResolutionAbutmentIso` is not rebuilt
on the Čech acyclicity of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/ToSheafCohomology.lean`.

## Implementation notes

The site is taken *small*, `C : Type v` with `SmallCategory C`, and the family indexed in the
same universe, which is the hypothesis of the source ([Stacks, Tag 0005] and
[Stacks, Tag 00VI]). This is what the hypercovering development's small-site branch assumes and
what makes the coefficient universe of the Čech complex of a `v`-indexed family coincide with the
universe in which sheaf cohomology is taken; see the module documentation of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequenceSmallSite.lean`. The library's
existential form of [Stacks, Tag 03AZ] is stated for a `Category.{u} C` on `Type u`, so neither
form implies the other by instantiation.

`Stacks.CechSite.cechPageTwoFunctor` is *spelled* as the restriction of the hypercovering
development's second-page functor rather than as
`Sheaf.cohomologyPresheafFunctor J q ⋙ Stacks.CechSite.cechCohomologyFunctor E p`, even though
`cechPageTwoFunctor_obj` and `cechPageTwoFunctor_map` say that the two agree on objects and on
morphisms. The reason is one of elaboration cost, not of mathematics: identifying the two as
functors means building a `CategoryTheory.NatIso.ofComponents` whose components are identities,
and for those identities to be *seen* as type-correct at `implicit` transparency the limit data
behind the products of the Čech complex has to be unfolded, which does not finish inside the
heartbeat budget. With the restriction as the definition, the second-page isomorphism is a
whiskering and the Čech description is carried by the two `rfl`-lemmas instead.

## References

* [Stacks Project, Tag 03AZ](https://stacks.math.columbia.edu/tag/03AZ)
* [Stacks Project, Tag 03OW](https://stacks.math.columbia.edu/tag/03OW)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe v

namespace Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo

variable {A : Type*} [Category* A] [Abelian A] {D : Type*} [Category* D]
  {D' : Type*} [Category* D'] {E : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}

/-- **A functorial filtered abutment restricts along any functor into its parameter category.**
Every field of `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` is a statement about the
spectral sequence and the filtration at an object or at a morphism, so composing the parameter
with a functor `G` transports all seven of them; the filtration becomes `G ⋙ filtration n` and
the abutment `G ⋙ H n`.

This is the operation `Stacks.CategoryTheory.Hypercovering.Functorial`
performs by hand when it restricts
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverFunctorialAbutment` to the full
subcategory of hypercoverings. -/
def restrict (h : FunctorialFirstQuadrantAbutsTo E H) (G : D' ⥤ D) :
    FunctorialFirstQuadrantAbutsTo (G ⋙ E) (fun n ↦ G ⋙ H n) where
  filtration n := G ⋙ h.filtration n
  abutmentIso n := Functor.isoWhiskerLeft G (h.abutmentIso n)
  isFinite K n := h.isFinite (G.obj K) n
  isTop K n := h.isTop (G.obj K) n
  isBot K n := h.isBot (G.obj K) n
  gradedIso K p q := h.gradedIso (G.obj K) p q
  gradedIso_naturality φ p q := h.gradedIso_naturality (G.map φ) p q

end Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo

namespace Stacks.CechSite

open Stacks.CategoryTheory.Hypercovering Stacks.CategoryTheory.Hypercovering.Functorial
open Stacks.Cohomology.Leray

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{v} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]

/-! ### Čech cohomology of the family as a functor -/

/-- **Čech cohomology of the family `𝒰 = E` in degree `p`, as a functor of the abelian
presheaf**: the degree-`p` homology of the Čech complex of [Stacks, Tag 03AM]. -/
noncomputable def cechCohomologyFunctor (p : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v} :=
  cechComplexFunctor E ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p

/-- The value of `Stacks.CechSite.cechCohomologyFunctor` is the Čech cohomology group
`Ȟ^p(𝒰, P)` of [Stacks, Tag 03AM]. -/
lemma cechCohomologyFunctor_obj (p : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (cechCohomologyFunctor E p).obj P = cechCohomology E P p :=
  rfl

/-- **The Čech cohomology functor of the family is the Čech cohomology functor of its simplicial
semi-representable object**, on the nose: the Čech complex of a family is by definition the
complex of sections of `Stacks.CechSite.cechSimplicialObject`. This is what lets the
hypercovering spectral sequence of a small site be read as the Čech-to-cohomology spectral
sequence of the family. -/
lemma cechCohomologyOverBifunctor_obj_cechSimplicialObject (p : ℕ) :
    (cechCohomologyOverBifunctor.{v, v, v} U p).obj (op (cechSimplicialObject E)) =
      cechCohomologyFunctor E p :=
  cechCohomologyOverBifunctor_obj.{v, v, v} U (cechSimplicialObject E) p

/-! ### The spectral sequence as a functor of the sheaf -/

/-- The functor `F ↦ (K(𝒰), F)` into the parameter category of the hypercovering spectral
sequence of a small site, `K(𝒰)` being the simplicial semi-representable object
`Stacks.CechSite.cechSimplicialObject` of the family. Restriction along it is what turns the
two-variable spectral sequence of clause (3) of [Stacks, Tag 01GY] into the Čech-to-cohomology
spectral sequence of the family. -/
noncomputable def sheafToCechPair : Sheaf J AddCommGrpCat.{v} ⥤
    (SimplicialObject (FormalCoproduct.{v} (Over U)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} :=
  Functor.prod' ((Functor.const _).obj (op (cechSimplicialObject E))) (𝟭 _)

/-- **The Čech-to-cohomology spectral sequence of a family of morphisms, as a functor of the
abelian sheaf.** This is the last sentence of [Stacks, Tag 03AZ]: the spectral sequence whose
second page is `Ȟ^p(𝒰, H^q(F))` is functorial in `F`.

It is the first-quadrant `E₂` cohomological spectral sequence of the double complex
`A^{i,j}(F) = Č^j(𝒰, I^i(F))` of the Čech complexes of a functorial injective resolution of `F`,
obtained by restricting the two-variable spectral sequence of clause (3) of [Stacks, Tag 01GY]
along `Stacks.CechSite.sheafToCechPair`. Its second page is
`Stacks.CechSite.cechToCohomologyPageTwoIso` and its functorial filtered abutment is
`Stacks.CechSite.cechToCohomologyFunctorialAbutment`; that abutment is the cohomology of the
total complex and is *not* identified with `H^n(U, F)` here. -/
@[stacks 03AZ "functoriality of the spectral sequence in the sheaf"]
noncomputable def cechToCohomologySpectralSequenceFunctor : Sheaf J AddCommGrpCat.{v} ⥤
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v} :=
  sheafToCechPair J E ⋙ hypercoverSpectralSequenceFunctor U J

/-! ### The second page -/

/-- **The asserted second page of [Stacks, Tag 03AZ], as a functor of the sheaf**:
`F ↦ Ȟ^p(𝒰, H^q(F))`, the Čech cohomology of the family with coefficients in the degree-`q`
cohomology presheaf of `F`.

It is spelled as the restriction along `Stacks.CechSite.sheafToCechPair` of the second-page
functor of clause (3) of [Stacks, Tag 01GY]; `cechPageTwoFunctor_obj` and
`cechPageTwoFunctor_map` say that this is `Ȟ^p(𝒰, H^q(-))` on objects and on morphisms. -/
noncomputable def cechPageTwoFunctor (p q : ℕ) :
    Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  sheafToCechPair J E ⋙ pageTwoSmallSite J U p q

/-- **The value of `Stacks.CechSite.cechPageTwoFunctor` is `Ȟ^p(𝒰, H^q(F))`**, on the nose. -/
lemma cechPageTwoFunctor_obj (p q : ℕ) (F : Sheaf J AddCommGrpCat.{v}) :
    (cechPageTwoFunctor J E p q).obj F =
      cechCohomology E ((Sheaf.cohomologyPresheafFunctor J q).obj F) p :=
  rfl

/-- **On a morphism of sheaves `Stacks.CechSite.cechPageTwoFunctor` is Čech cohomology of the
induced morphism of cohomology presheaves.** With `cechPageTwoFunctor_obj` this says that the
functor is `Ȟ^p(𝒰, H^q(-))` and nothing else; it is
`Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor_map_sheaf` at the simplicial
semi-representable object of the family, the action of
`Stacks.CechSite.sheafToCechPair` on a morphism being `(𝟙 K(𝒰), f)`. -/
lemma cechPageTwoFunctor_map (p q : ℕ) {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    (cechPageTwoFunctor J E p q).map f =
      (cechCohomologyFunctor E p).map ((Sheaf.cohomologyPresheafFunctor J q).map f) :=
  pageTwoBifunctor_map_sheaf.{v, v, v} U J (cechSimplicialObject E) f p q

/-- **The second page of the functorial Čech-to-cohomology spectral sequence is
`Ȟ^p(𝒰, H^q(F))`, naturally in the sheaf `F`.** Together with
`Stacks.CechSite.cechToCohomologySpectralSequenceFunctor` this is the functoriality asserted by
the last sentence of [Stacks, Tag 03AZ]: not merely that each sheaf has such a spectral sequence,
but that the assignment is a functor and that the second-page identification is a natural
isomorphism.

It is `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverPageTwoIso` restricted along
`Stacks.CechSite.sheafToCechPair`. -/
@[stacks 03AZ "functoriality of the second page in the sheaf", sga "4 V 3.2" "E₂-page (covering)"]
noncomputable def cechToCohomologyPageTwoIso (p q : ℕ) :
    cechToCohomologySpectralSequenceFunctor J E ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ (p, q) ≅
      cechPageTwoFunctor J E p q :=
  Functor.isoWhiskerLeft (sheafToCechPair J E) (hypercoverPageTwoIso.{v} U J p q)

/-! ### The functorial abutment -/

/-- **The functorial finite filtered abutment of the functorial Čech-to-cohomology spectral
sequence.** The spectral sequence has an infinity page at every bidegree, the abutment carries a
finite decreasing filtration which is everything in step `0` and zero in step `n + 1`, and the
infinity terms `E_∞^{p,q}` are its graded pieces — all of it naturally in the sheaf.

The abutment here is the cohomology of the total complex of the double complex
`A^{i,j}(F) = Č^j(𝒰, I^i(F))`. It is **not** identified with the sheaf cohomology `H^n(U, F)`;
see the section "What is proved and what is not" of this file's module documentation.

It is `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverFunctorialAbutment` restricted
along `Stacks.CechSite.sheafToCechPair`. -/
noncomputable def cechToCohomologyFunctorialAbutment :
    FunctorialFirstQuadrantAbutsTo (cechToCohomologySpectralSequenceFunctor J E)
      (fun n ↦ sheafToCechPair J E ⋙
        hypercoverFiltrationFunctor.{v} U J (n : ℤ) ⋙ FilteredObject.forget) :=
  (hypercoverFunctorialAbutment.{v} U J).restrict (sheafToCechPair J E)

/-- **The functorial abutment read at one sheaf.** For each abelian sheaf `F` the Čech-to-
cohomology spectral sequence of `F` abuts, through a finite decreasing filtration whose graded
pieces are its infinity terms, to the cohomology of the total complex of
`A^{i,j}(F) = Č^j(𝒰, I^i(F))`; this is the convergence structure that
`Stacks.Cohomology.Leray.FirstQuadrantAbutment` records, and it is the objectwise reading of
`Stacks.CechSite.cechToCohomologyFunctorialAbutment`. -/
noncomputable def cechToCohomologyAbutment (F : Sheaf J AddCommGrpCat.{v}) :
    FirstQuadrantAbutment ((cechToCohomologySpectralSequenceFunctor J E).obj F)
      (fun n ↦ ((hypercoverFiltrationFunctor.{v} U J (n : ℤ) ⋙
        FilteredObject.forget).obj (op (cechSimplicialObject E), F))) :=
  (cechToCohomologyFunctorialAbutment J E).toFirstQuadrantAbutment F

end Stacks.CechSite

end
