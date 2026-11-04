module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic

/-!
# Coherence of a higher direct image is local on the base, in the `ℕ`-indexed spelling

For `f : X ⟶ S` and a family of opens covering `S`, if the `p`-th higher direct image along each
`f ∣_ V i` of the corresponding restriction of `ℱ` is coherent, then `R^p f_* ℱ` is coherent.
There is no hypothesis on `f`, on `ℱ` or on the base.

This is [Stacks, Tag 01E5] plus the locality of coherence, and it is the same argument as
`AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_cover` — but stated
for `CategoryTheory.Functor.rightDerived`, the `ℕ`-indexed derived functor, rather than for
`CategoryTheory.Functor.rightDerivedPlus`.

**Why the indexing matters here and is not a presentational choice.** `Functor.rightDerivedPlus`
takes a `CategoryTheory.HasDerivedCategory` instance, and the library has two incompatible ones
for `X.Modules`: the `CategoryTheory.HasDerivedCategory.standard` that the cohomology files
activate as a local instance, and the global
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is at a lower universe and wins
wherever it is in scope. A `rightDerivedPlus` statement therefore means different things in
different import closures, and the existing locality lemmas — compiled where only `standard` is
visible — cannot be applied inside a closure that reaches `LocallySmall`. `Functor.rightDerived`
takes no such instance, so the statements below are the same statements in every closure, and
they compose with results proved on either side.

Nothing here is a weakening: `AlgebraicGeometry.ProjectiveCoherentImage`
`.higherDirectImageRestrictIsoScheme`, the `ℕ`-indexed form of [Stacks, Tag 01E5], is what the
`ℤ`-indexed one is *built from*, by whiskering with `Stacks.DerivedIndexing.rightDerivedIso` on
both sides. The derived-category structure enters only in that last step, which is the step
omitted here.

## Main results

* `AlgebraicGeometry.CoherentImageLocalBase.isCoherent_restrict_rightDerived`: coherence of
  `R^p (f ∣_ V)_*` of a restriction gives coherence of the restriction to `V` of `R^p f_* ℱ`.
* `AlgebraicGeometry.CoherentImageLocalBase.isCoherent_rightDerived_of_cover`: **coherence of a
  higher direct image is local on the base**, with no hypothesis owed.

## Implementation notes

**No tag attribute is attached.** [Stacks, Tag 01E5] is the restriction isomorphism, which is
`higherDirectImageRestrictIsoScheme` and already carries its attribution; what is added here is
its combination with the locality of coherence, which asserts neither tag on its own.

**The gluing hypothesis is discharged rather than carried.** The existing cover lemma takes the
locality of coherence as an explicit `hglue` argument; `AlgebraicGeometry.Modules`
`.isCoherent_of_restrict` proves it, so it is supplied here and the statement owes nothing.

**The namespace deliberately avoids a `Stacks.` prefix.** Inside one, `SheafOfModules.IsCoherent`
resolves to the distinct class `Stacks.SheafOfModules.IsCoherent` rather than to the root one of
[Stacks, Tag 01BW], and the statements below would silently become statements about it. This is
the same precaution `AlgebraicGeometry.ProperCoherentImage` records.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.CoherentImageLocalBase

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (p : ℕ)

/-- **Coherence of a higher direct image over an open of the base, `ℕ`-indexed.** If the `p`-th
higher direct image along `f ∣_ V` of the restriction of `ℱ` to `f⁻¹(V)` is coherent, then so is
the restriction to `V` of `R^p f_* ℱ`.

This is the `ℕ`-indexed [Stacks, Tag 01E5] isomorphism
`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme` together with the
closure of coherence under isomorphism. No hypothesis on `f`, on `ℱ` or on the base is used. -/
theorem isCoherent_restrict_rightDerived (V : S.Opens)
    (h : (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).IsCoherent) :
    ((Scheme.Modules.restrictFunctor V.ι).obj
      (((Scheme.Modules.pushforward f).rightDerived p).obj F)).IsCoherent :=
  ObjectProperty.prop_of_iso
    (P := fun M : SheafOfModules.{u} V.toScheme.ringCatSheaf => M.IsCoherent)
    ((ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme f V p).app F) h

/-- **Coherence of a higher direct image is local on the base, `ℕ`-indexed.** Let `V` be a family
of opens covering `S`. If for every member the `p`-th higher direct image along `f ∣_ V i` of the
corresponding restriction of `ℱ` is coherent, then `R^p f_* ℱ` is coherent.

Nothing is owed: the locality of coherence is `AlgebraicGeometry.Modules.isCoherent_of_restrict`,
and there is no hypothesis on `f`, on `ℱ` or on the base. -/
theorem isCoherent_rightDerived_of_cover {I : Type u} (V : I → S.Opens) (hV : iSup V = ⊤)
    (h : ∀ i, (((Scheme.Modules.pushforward (f ∣_ V i)).rightDerived p).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V i).ι).obj F)).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerived p).obj F).IsCoherent :=
  AlgebraicGeometry.Modules.isCoherent_of_restrict _ V hV
    fun i => isCoherent_restrict_rightDerived f F p (V i) (h i)

end AlgebraicGeometry.CoherentImageLocalBase

end
