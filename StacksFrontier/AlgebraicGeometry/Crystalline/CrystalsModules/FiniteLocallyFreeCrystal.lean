module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Crystals in quasi-coherent and in finite locally free modules

[Stacks, Tag 07IU] names two conditions on a sheaf of `𝒪_{X/S}`-modules `F` on either crystalline
site, `CRIS(X/S)` or `Cris(X/S)`: `F` is a *crystal in quasi-coherent modules* when it satisfies
the equivalent conditions of [Stacks, Tag 07IT], and a *crystal in finite locally free modules*
when it is in addition finite locally free.

The two conditions [Stacks, Tag 07IT] declares equivalent are (1) that `F` be quasi-coherent in
the sense of [Stacks, Tag 03DL], and (2) that `F` be locally quasi-coherent and a crystal in
`𝒪_{X/S}`-modules.  The notion is taken here in form (1), as
`SheafOfModules.IsQuasicoherentOnSite`: it is one of the two forms the source itself declares
interchangeable, it is the same predicate on both crystalline sites, and it needs nothing from the
equivalence — which this library does not have (see *What is and is not proved* below).  Finite
local freeness is `SheafOfModules.IsFiniteLocallyFreeOnSite`, the predicate of
[Stacks, Tag 03DL].

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.IsFiniteLocallyFreeQuasicoherentCrystal` — a
  crystal in finite locally free modules on the small crystalline site `Cris(X/S)`.

The big-site clause,
`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal`, is stated in
`StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal`, which this file imports.  It lives there
because [Stacks, Tag 07N3] builds its F-crystal on it and that file is upstream of this one — it
is reached from here through
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal`,
`...CrystalsModules.QuasicoherentCriterion` and `...CrystalsModules.SheafCrystal` — while the
clause itself needs nothing but `SheafOfModules.IsQuasicoherentOnSite` and
`SheafOfModules.IsFiniteLocallyFreeOnSite`.  It carries the `07IU` attribute there.

## Main results

* `Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal`
  `.isLocallyQuasiCoherent` and
  `Crystalline.GlobalCrystallineSituation.SmallSite.IsFiniteLocallyFreeQuasicoherentCrystal`
  `.isLocallyQuasiCoherent` — on either crystalline site a crystal in finite locally free modules
  is locally quasi-coherent, by the implication (1) ⇒ (2)(a) of [Stacks, Tag 07IT].

## What is and is not proved

Both clauses of [Stacks, Tag 07IU] are stated, for both crystalline sites, and the tag attribute
is placed on them — the big-site one in `StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal`, the
small-site one below; they are the whole covering set of the tag.  Being a definition, the tag has
nothing to prove beyond the well-formedness of what it names; the one judgement it rests on is
which of the two forms of [Stacks, Tag 07IT] to take as the definition, discussed above.

What is *not* available is the full equivalence of [Stacks, Tag 07IT].  Its implication (1) ⟹ (2)
is proved, both halves and for both sites the tag is stated for: that a quasi-coherent module is
locally quasi-coherent is
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` on
`CRIS(X/S)` and
`Crystalline.GlobalCrystallineSituation.SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`
on `Cris(X/S)`, and that it is a crystal in `𝒪_{X/S}`-modules is
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite` and
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite`.  So a
crystal in quasi-coherent modules as defined here is locally quasi-coherent on either site — that
is `IsFiniteLocallyFreeQuasicoherentCrystal.isLocallyQuasiCoherent` and its small-site namesake.
The converse (2) ⟹ (1) is a separate statement, proved on neither site.

The first of those two is what consumers of a crystal in finite locally free modules need when
they want the crystal property itself, and it is the reason
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_toSmallFCrystal` takes
(1) ⟹ (2) as an explicit input: see the docstring there.

`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeCrystal` of
`StacksFrontier/AlgebraicGeometry/Crystalline/FCrystal.lean` is a **different** predicate, which
carries no `07IU` attribute.  It conjoins finite local freeness with
`Crystalline.GlobalCrystallineSituation.IsCrystal`, the crystal condition read on the *presheaf*
level, and omits quasi-coherence; so it is the crystal half of form (2) alone, read at the wrong
level, not form (2) and not form (1).  It is strictly stronger than the two clauses of the tag:
finite local freeness already implies quasi-coherence
(`SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite` followed by the instance
`SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`), so it is the conjunction of
the big-site clause with the presheaf-level crystal condition, which the source does not impose.
The converse implication fails, needing the passage from the sheaf-level crystal condition
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal` to the presheaf-level one, which is false
in general — see the discussion in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsModules/QuasicoherentCriterion.lean`.  Neither
implication is assembled in Lean here: the first of the two lemmas above lives in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent`, and importing the
algebraic-space development into the crystalline chapter for a remark is not worth the layering.
Nothing in the library is stated about `IsFiniteLocallyFreeCrystal`; the two clauses of
[Stacks, Tag 07IU] are the predicates faithful to the tag, and
`Crystalline.FCrystal` of [Stacks, Tag 07N3] is built on the big-site one.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Crystalline.GlobalCrystallineSituation

add_to_stacks 07IU "a crystal in quasi-coherent modules on either crystalline site is a
  quasi-coherent sheaf of modules, condition (1) of Stacks 07IT"
  SheafOfModules.IsQuasicoherentOnSite

/-- **A crystal in finite locally free modules on the big crystalline site is locally
quasi-coherent.**  This is the half of [Stacks, Tag 07IT] the library proves,
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`, applied
to the quasi-coherence of the crystal. -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.isLocallyQuasiCoherent
    {S : GlobalCrystallineSituation.{u}} {M : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) : IsLocallyQuasiCoherent M :=
  isLocallyQuasiCoherent_of_isQuasicoherentOnSite M hM.isQuasicoherentOnSite

namespace SmallSite

/-- **Stacks Project, Tag 07IU.**  A *crystal in finite locally free modules* on the small
crystalline site: a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` which is a crystal in quasi-coherent
modules — that is, quasi-coherent, condition (1) of [Stacks, Tag 07IT] — and is finite locally
free.  [Stacks, Tag 07IS] states the conditions for `CRIS(X/S)` and for `Cris(X/S)` alike, and
both predicates used here are the general ones for a sheaf of modules on a site, so this differs
from the condition on the big site only in the site it is read on. -/
@[stacks 07IU "crystals in finite locally free modules on the small site Cris(X/S), with the
  crystal in quasi-coherent modules taken as condition (1) of Stacks 07IT"]
structure IsFiniteLocallyFreeQuasicoherentCrystal {S : GlobalCrystallineSituation.{u}}
    (M : SheafOfModules.{u} (structureSheaf S)) : Prop where
  /-- The module is quasi-coherent, which is what it is for it to be a crystal in quasi-coherent
  modules. -/
  isQuasicoherentOnSite : M.IsQuasicoherentOnSite
  /-- The module is finite locally free. -/
  isFiniteLocallyFree : SheafOfModules.IsFiniteLocallyFreeOnSite M

/-- **A crystal in finite locally free modules on the small crystalline site is locally
quasi-coherent.**  This is the half of [Stacks, Tag 07IT] the library proves for `Cris(X/S)`,
`Crystalline.GlobalCrystallineSituation.SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`,
applied to the quasi-coherence of the crystal. -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.isLocallyQuasiCoherent
    {S : GlobalCrystallineSituation.{u}} {M : SheafOfModules.{u} (structureSheaf S)}
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) : IsLocallyQuasiCoherent M :=
  isLocallyQuasiCoherent_of_isQuasicoherentOnSite M hM.isQuasicoherentOnSite

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
