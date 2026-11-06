module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentCoprod
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras

/-!
# Quasi-coherence of a coproduct indexed by a small type, and of a graded algebra sheaf

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentCoprod` builds a
`SheafOfModules.QuasicoherentData` for a coproduct `∐ P` out of presentations of the summands
over one common covering family, with the index type of the summands required to lie in the
module universe `u`.  That requirement is too strong for the family this is meant to be applied
to.  A graded algebra sheaf is a coproduct indexed by `ℕ`, and `ℕ : Type 0`; instantiating a
`Type u`-indexed statement at `ℕ` forces `u = 0`, which collapses the module universe.

This file removes that restriction.  The index type is only asked to be `Small.{u}`, which `ℕ`
is, and the construction is reduced to the `Type u`-indexed one by reindexing along
`equivShrink`.  The three sheaves of modules underlying the tensor, exterior and symmetric
algebras of a sheaf of modules are then covered, since each is *by definition* a coproduct of
its homogeneous pieces indexed by `ℕ`.

## Main definitions

* `SheafOfModules.overSigmaIso` : restriction to a slice site preserves coproducts, when the
  site has binary products.  This names the isomorphism that
  `SheafOfModules.isQuasicoherent_coprod` derives inline.
* `SheafOfModules.sigmaShrinkIso` : the reindexing `∐ (P ∘ (equivShrink ι).symm) ≅ ∐ P` of a
  coproduct along a shrinking of its index type.
* `SheafOfModules.QuasicoherentData.coprodOfSmall` : **the shared-cover builder.**
  Quasi-coherent data for `∐ P`, for an index type that is merely `Small.{u}`, out of
  presentations of `(P n).over (X i)` for one common covering family `X`.  The index type `I` of
  the covering family, the family `X` itself and its `CoversTop` witness are shared across the
  summands; only the generators and the relations are summed.

## Main results

* `SheafOfModules.isQuasicoherent_coprod_of_small` : a coproduct of sheaves of modules presented
  over one common covering family is quasi-coherent, for a `Small.{u}` index type.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isQuasicoherent_tensorAlgebraSheaf`,
  `isQuasicoherent_exteriorAlgebraSheaf` and `isQuasicoherent_symmetricAlgebraSheaf` : the three
  conclusions of Stacks Tag 01CL, reduced to the hypothesis that one covering family presents
  every homogeneous piece.

## Implementation notes

**Why `Small.{u}` and not a free universe.** A presentation indexes its generators by a type in
the module universe `u`, and the generators of a presentation of `∐ P` are those of the summands
taken together, so `Σ n, (p n).generators.I` must land in `Type u`.  For `ι : Type w` that sigma
type is an object of `Type (max w u)`, and `max w u = u` is not a statement Lean can be asked to
assume.  `Small.{u} ι` is exactly that assumption in the form Lean does accept, and it is
discharged by `instance` for every index type a graded object uses: `ℕ`, `ℤ`, `Fin n`.  The
reindexing is therefore done once here rather than inside each consumer's comparison
isomorphism.

**The products hypothesis is not a narrowing here.** `HasBinaryProducts C` enters through
`SheafOfModules.isLeftAdjoint_pushforward_of_isIso`, which is the only route in Mathlib to the
fact that restriction to a slice site preserves coproducts — the right adjoint of
`Over.forget X` is `Over.star X`.  Stacks assumes no products of a site, so a statement about a
general site should not acquire it; but the consumers below are the algebra sheaves of
Section 17.21, and quasi-coherence there is read on a ringed space, where the site is
`TopologicalSpace.Opens` and `HasBinaryProducts` is intersection of opens and holds by
`inferInstance`.  `SheafOfModules.isQuasicoherent_coprod_of_coversTop`, which takes the
comparison isomorphisms as an argument and assumes no products, remains available for a general
site.

**No `@[stacks 01CL]` attribute, deliberately.** Tag 01CL asserts that the tensor, exterior and
symmetric algebras of a *quasi-coherent* sheaf of modules are quasi-coherent, and its proof opens
by warning that an infinite direct sum of quasi-coherent modules need not be quasi-coherent: what
rescues the lemma is that a single open neighbourhood presents every power simultaneously.  That
uniformity is the content of the tag and is *not* proved here — it is the hypothesis
`p` of the three results below.  Per-power quasi-coherence would not do, which is why the
covering family is shared.  Tagging any of these would claim the tag for the formal step while
the mathematical step is open.

**Where the hypothesis `p` is discharged.** It is no longer owed. For the symmetric and the
exterior algebra the uniform presentation is
`Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over` and
`nonempty_presentation_exteriorPower_over` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras`, and for the tensor algebra
it is `nonempty_presentation_tensorPower_over` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPresentation`; the three conclusions of
the tag that consume them, and which carry `@[stacks 01CL]`, are
`Stacks.SheafOfModules.isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent`,
`isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent` and
`isQuasicoherent_tensorAlgebraSheaf_of_isQuasicoherent`. The locally free half of the tag,
clause (2), is `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeAlgebras`, whose
`Stacks.SheafOfModules.isLocallyFree_coprod_of_small` is the locally-free analogue of
`isQuasicoherent_coprod_of_small` below and uses `SheafOfModules.overSigmaIso` and
`sigmaShrinkIso` from this file.

## References

* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

universe w' w u v₁ u₁

open CategoryTheory Limits CategoryTheory.Sheaf

/-- Coproducts of presheaves of modules indexed by a `Small.{u}` type, named outright: since
Lean v4.35.0 instance search for them exceeds its budget in this import closure. -/
instance (priority := high) presheafOfModules_hasColimitsOfShape_discrete
    {D : Type u₁} [Category.{v₁} D] {S : Dᵒᵖ ⥤ RingCat.{u}} (ι : Type w') [Small.{u} ι] :
    HasColimitsOfShape (Discrete ι) (PresheafOfModules.{u} S) :=
  haveI : HasColimitsOfShape (Discrete ι) AddCommGrpCat.{u} := inferInstance
  PresheafOfModules.hasColimitsOfShape S (Discrete ι)

/-- Coproducts of sheaves of modules indexed by a `Small.{u}` type, from the presheaf case;
instance search alone exceeds its budget here since Lean v4.35.0. -/
instance (priority := high) sheafOfModules_hasColimitsOfShape_discrete
    {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (ι : Type w') [Small.{u} ι] :
    HasColimitsOfShape (Discrete ι) (SheafOfModules.{u} S) :=
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    S (Discrete ι)

/-- A coproduct of sheaves of modules indexed by a `Small.{u}` type exists; see
`sheafOfModules_hasColimitsOfShape_discrete`. -/
instance (priority := high) sheafOfModules_hasColimit_discrete
    {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type w'} [Small.{u} ι] (F : Discrete ι ⥤ SheafOfModules.{u} S) : HasColimit F :=
  (sheafOfModules_hasColimitsOfShape_discrete ι).has_colimit F

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Restriction to a slice site preserves coproducts -/

section Slice

variable [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction to a slice site preserves coproducts.** The right adjoint of `Over.forget Y` is
`Over.star Y`, so this is where binary products of the site are used; see the module docstring.
`SheafOfModules.isQuasicoherent_coprod` derives the same isomorphism inline. -/
noncomputable def overSigmaIso [HasBinaryProducts C] {κ : Type u} (Q : κ → SheafOfModules.{u} R)
    (Y : C) : (∐ fun n => (Q n).over Y) ≅ (∐ Q).over Y := by
  haveI : (overFunctor.{u} R Y).IsLeftAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward.{u} (𝟙 (R.over Y))).IsLeftAdjoint
  haveI : PreservesColimitsOfSize.{u, u} (overFunctor.{u} R Y) :=
    (Adjunction.ofIsLeftAdjoint (overFunctor.{u} R Y)).leftAdjoint_preservesColimits
  exact (PreservesCoproduct.iso (overFunctor.{u} R Y) Q).symm

end Slice

/-! ### Coproducts indexed by a small type -/

section Small

variable {ι : Type w'} [Small.{u} ι] {P : ι → SheafOfModules.{u} R} [HasCoproduct P]

/-- The reindexing of a coproduct along a shrinking of its index type to the module universe. -/
noncomputable def sigmaShrinkIso :
    (∐ fun j : Shrink.{u} ι => P ((equivShrink ι).symm j)) ≅ ∐ P :=
  Sigma.whiskerEquiv (equivShrink ι).symm fun _ => Iso.refl _

variable [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The shared-cover builder.** Quasi-coherent data for a coproduct of sheaves of modules all
of which are presented over one and the same covering family `X`, with the index type of the
summands only required to be `Small.{u}` rather than to lie in the module universe.

The covering family `X`, its index type `I` and its `CoversTop` witness are shared across the
summands; the generators and the relations of the presentation over `X i` are the sigma types of
those of the summands. -/
noncomputable def QuasicoherentData.coprodOfSmall [HasBinaryProducts C] {I : Type w}
    (X : I → C) (hX : J.CoversTop X)
    (p : ∀ (i : I) (n : ι), ((P n).over (X i)).Presentation) :
    QuasicoherentData.{w} (∐ P) :=
  (QuasicoherentData.coprod (R := R)
      (P := fun j : Shrink.{u} ι => P ((equivShrink ι).symm j)) X hX
      (fun i j => p i ((equivShrink ι).symm j))
      (fun i => overSigmaIso (fun j : Shrink.{u} ι => P ((equivShrink ι).symm j))
        (X i))).ofIsIso sigmaShrinkIso.hom

/-- **A coproduct of sheaves of modules presented over one common covering family is
quasi-coherent**, for an index type that is only `Small.{u}`. This is
`SheafOfModules.isQuasicoherent_coprod` with its index universe freed, which is what makes it
applicable to an `ℕ`-graded coproduct at a nonzero module universe. -/
theorem isQuasicoherent_coprod_of_small [HasBinaryProducts C] {I : Type w}
    (X : I → C) (hX : J.CoversTop X)
    (p : ∀ (i : I) (n : ι), ((P n).over (X i)).Presentation) :
    (∐ P).IsQuasicoherent :=
  (QuasicoherentData.coprodOfSmall X hX p).isQuasicoherent

end Small

/-! ### The three algebra sheaves of Section 17.21 -/

namespace TensorExteriorSymmetricAlgebras

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C] {F : SheafOfModules.{u} (toRingCat J Osharp)}
  (A : TensorExteriorSymmetricAlgebras J F)

/-- **The sheaf of modules underlying the tensor algebra is quasi-coherent, once one covering
family presents every tensor power.** The sharing of the covering family across the degrees is
the whole content of Stacks Tag 01CL and is the hypothesis here; see the module docstring. -/
theorem isQuasicoherent_tensorAlgebraSheaf {I : Type w} (X : I → C) (hX : J.CoversTop X)
    (p : ∀ (i : I) (n : ℕ), ((A.tensor.piece (n : ℤ)).over (X i)).Presentation) :
    A.tensorAlgebraSheaf.IsQuasicoherent :=
  isQuasicoherent_coprod_of_small X hX p

/-- **The sheaf of modules underlying the exterior algebra is quasi-coherent, once one covering
family presents every exterior power.** -/
theorem isQuasicoherent_exteriorAlgebraSheaf {I : Type w} (X : I → C) (hX : J.CoversTop X)
    (p : ∀ (i : I) (n : ℕ), ((A.exteriorPower n).over (X i)).Presentation) :
    A.exteriorAlgebraSheaf.IsQuasicoherent :=
  isQuasicoherent_coprod_of_small X hX p

/-- **The sheaf of modules underlying the symmetric algebra is quasi-coherent, once one covering
family presents every symmetric power.** -/
theorem isQuasicoherent_symmetricAlgebraSheaf {I : Type w} (X : I → C) (hX : J.CoversTop X)
    (p : ∀ (i : I) (n : ℕ), ((A.symmetricPower n).over (X i)).Presentation) :
    A.symmetricAlgebraSheaf.IsQuasicoherent :=
  isQuasicoherent_coprod_of_small X hX p

end TensorExteriorSymmetricAlgebras

end SheafOfModules

end
