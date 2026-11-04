module

public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.RingBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.AffineBase

/-!
# Over an affine base the finite-type clause of Tag 0EX4 is finiteness of a module

[Stacks, Tag 0EX4] asserts, for `f : X ⟶ Y` proper all of whose fibres have dimension at most
`d` and `F` quasi-coherent of finite type, that `R ᵈ f_* F` is quasi-coherent of finite type.
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/AffineBase.lean` reduces that clause to
its own affine-base case, and the source's proof continues from there with the sentence

> Say `Y = Spec(R)`. Then it suffices to prove that `Hᵈ(X, F)` is a finite `R`-module.

This file proves that sentence — in both directions, and with **no Noetherian hypothesis on the
base**, which is the whole point: over a locally Noetherian base the corresponding bridge is
already available through coherence
(`…ProperCohomologyFinite.moduleFinite_cohomology_iff_isCoherent`), and it is exactly the
Noetherian hypothesis that [Stacks, Tag 0EX4] does not carry.

The ingredients are [Stacks, Tag 01XK] — the identification of `Hⁿ(X, F)`, with scalars
restricted along `f.appTop`, with the global sections of `Rⁿ f_* F` — and the two directions of
condition (4) of [Stacks, Tag 01XZ]: the sections of a quasi-coherent module of finite type over
an affine open are a finite module, and a quasi-coherent module whose sections over an affine
cover are finite modules is of finite type. Neither needs Noetherianness; it is only the step
from finite type to *coherence* that does, and that step is what the existing statements take and
this file does not.

The consequence for Tag 0EX4 is
`forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology_affineBase`: the finite-type
clause of [Stacks, Tag 0EX4], quantified over all of its data, is **equivalent** to the single
module-finiteness family

> for every proper `f : X ⟶ Y` with `Y` affine whose fibres all have dimension at most `d`, and
> every quasi-coherent `F` of finite type, `Hᵈ(X, F)` is a finite `Γ(Y, ⊤)`-module.

That family is the residue of the clause at declaration granularity, and it is stated in the same
vocabulary as [Stacks, Tag 02O6] — the two differ exactly by dropping `IsLocallyNoetherian Y`,
weakening `IsCoherent F` to quasi-coherent of finite type, and adding the fibre-dimension bound.
So what the tag asks beyond [Stacks, Tag 02O6] is visible as a difference of binders rather than
as a difference of shape.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType`'s
  `moduleFinite_cohomology_of_isFiniteType_rightDerived`: over an **arbitrary** affine base,
  finiteness of type of `Rⁿ f_* F` makes `Hⁿ(X, F)` a finite `Γ(S, ⊤)`-module.
* `…isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine`: the converse, also with no
  Noetherian hypothesis.
* `…moduleFinite_cohomology_iff_isFiniteType_rightDerived`: the two together.
* `…moduleFinite_cohomology_ringBase_of_isFiniteType_rightDerived`,
  `…isFiniteType_rightDerived_of_moduleFinite_cohomology_ringBase` and
  `…moduleFinite_cohomology_ringBase_iff_isFiniteType_rightDerived`: the same over a base
  `Spec A` for an **arbitrary** commutative ring `A`, which is the spelling the source's sentence
  uses and the one the limit presentation `A = colim Aᵢ` by Noetherian subrings acts on.
* `…forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology_affineBase`: **the
  finite-type clause of [Stacks, Tag 0EX4] is equivalent to a module-finiteness family over
  affine bases.**

## Implementation notes

**No `@[stacks 0EX4]` attribute is attached to anything here.** Nothing below asserts the tag:
the pointwise statements carry finiteness of type of `Rⁿ f_* F` (which for a general proper
morphism is the clause itself) or the module finiteness as a *hypothesis*, and the family
statement is an equivalence between two families, neither of which is proved. The quasi-coherence
clause of the tag is tagged in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/Qcqs.lean`; the finite-type clause
carries one over a locally Noetherian base in
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianBaseUnconditional.lean`.

**Three declarations of the library are subsumed by the ones below.** `…ProperCohomologyFinite.moduleFinite_cohomology_of_isCoherent` is
`moduleFinite_cohomology_of_isFiniteType_rightDerived` after
`…CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent`;
`…ProperCohomologyFinite.isCoherent_of_moduleFinite_cohomology` is
`isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine` followed by
`…CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`; and
`…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isFiniteType` is
`moduleFinite_cohomology_ringBase_of_isFiniteType_rightDerived` with `[IsNoetherianRing A]` and
`[IsProper f]` deleted. Those three are not generalised in place, because
that would invert the import direction: they live in `ProperCohomologyFinite/`, which this file
imports. Each is a one-term corollary of its generalisation here.

**Properness is used nowhere in the pointwise statements**, only quasi-compactness and
quasi-separatedness, which is what [Stacks, Tag 01XK] needs. It enters only in the family
statement, through the tag's own hypotheses and through
`…TopDegreeFiniteType.forall_isFiniteType_rightDerived_iff_forall_isAffineBase`.

**The `Γ(S, ⊤)` and the ring spellings are interchangeable with no hypothesis.**
`…ProperCohomologyFinite.moduleFinite_compHom_of_surjective` moves finiteness from
`Γ(Spec A, ⊤)` to `A` along the ring isomorphism `AlgebraicGeometry.Scheme.ΓSpecIso`, and
`…ProperCohomologyFinite.moduleFinite_of_compHom` moves it back; neither needs surjectivity in
the second case nor Noetherianness in either.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance] HasDerivedCategory.standard

/-! ### Over an affine base, finite type is finiteness of the cohomology module -/

section AffineBase

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.IsAffine S]

/-- **Over an arbitrary affine base, finiteness of type of `Rⁿ f_* F` makes `Hⁿ(X, F)` a finite
`Γ(S, ⊤)`-module.** No Noetherian hypothesis on `S`.

`Rⁿ f_* F` is quasi-coherent by [Stacks, Tag 01XJ], found by instance search from the
quasi-compactness and quasi-separatedness of `f`, so its sections over the affine open `⊤` are a
finite module by condition (4) of [Stacks, Tag 01XZ]
(`AlgebraicGeometry.moduleFinite_sections_on_affine`); [Stacks, Tag 01XK] identifies those
sections with `Hⁿ(X, F)`.

This generalises `…ProperCohomologyFinite.moduleFinite_cohomology_of_isCoherent`, whose
hypothesis is coherence of `Rⁿ f_* F`: coherence is quasi-coherence together with finiteness of
type, and only the latter is used. -/
theorem moduleFinite_cohomology_of_isFiniteType_rightDerived (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F)) := by
  have := h
  have hfin : Module.Finite Γ(S, ⊤)
      ((moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :=
    AlgebraicGeometry.moduleFinite_sections_on_affine
      (((Scheme.Modules.pushforward f).rightDerived n).obj F) ⊤ (isAffineOpen_top S)
  exact Module.Finite.equiv (cohomologyIsoSectionsRightDerived f F n).toLinearEquiv.symm

/-- **The converse, over an arbitrary affine base**: finiteness of `Hⁿ(X, F)` as a
`Γ(S, ⊤)`-module makes `Rⁿ f_* F` of finite type. No Noetherian hypothesis on `S`.

[Stacks, Tag 01XK] turns the hypothesis into finiteness of the sections of `Rⁿ f_* F` over `⊤`,
which covers `S` by itself, and condition (5) ⇒ (2) of [Stacks, Tag 01XZ] concludes.

This is the finite-type half of `…ProperCohomologyFinite.isCoherent_of_moduleFinite_cohomology`,
which goes on to deduce coherence and therefore has to assume `IsLocallyNoetherian S`. Dropping
that hypothesis is the point: [Stacks, Tag 0EX4] does not carry it. -/
theorem isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (h : Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F))) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType := by
  have hsec : Module.Finite Γ(S, ⊤)
      ((moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :=
    Module.Finite.equiv (cohomologyIsoSectionsRightDerived f F n).toLinearEquiv
  exact isFiniteType_of_cover_isFiniteTildeOn
    (((Scheme.Modules.pushforward f).rightDerived n).obj F)
    (fun _ : PUnit.{u + 1} => (⊤ : S.Opens)) (IsOpenCover.mk iSup_const)
    (fun _ => isAffineOpen_top S)
    (fun _ => isFiniteTildeOn_of_moduleFinite_sections _ ⟨⊤, isAffineOpen_top S⟩ hsec)

/-- **Over an arbitrary affine base, finiteness of type of `Rⁿ f_* F` and finiteness of the
`Γ(S, ⊤)`-module `Hⁿ(X, F)` are the same condition.** -/
theorem moduleFinite_cohomology_iff_isFiniteType_rightDerived (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) ↔
      (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType :=
  ⟨isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine f F n,
    moduleFinite_cohomology_of_isFiniteType_rightDerived f F n⟩

end AffineBase

/-! ### The same over an arbitrary ring base -/

section RingBase

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]

/-- **`Hⁿ(X, F)` is a finite `A`-module as soon as `Rⁿ f_* F` is of finite type**, for
`f : X ⟶ Spec A` quasi-compact and quasi-separated, `F` quasi-coherent and `A` an arbitrary
commutative ring. This is the source's own spelling of the obligation — *"it suffices to prove
that `Hᵈ(X, F)` is a finite `R`-module"* — the `A`-structure being the restriction of scalars
along `A ≅ Γ(Spec A, ⊤) → Γ(X, ⊤)`.

Finiteness over `Γ(Spec A, ⊤)` is `moduleFinite_cohomology_of_isFiniteType_rightDerived`, and it
is moved to `A` along `AlgebraicGeometry.Scheme.ΓSpecIso` by
`…ProperCohomologyFinite.moduleFinite_compHom_of_surjective`.

This generalises `…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isFiniteType`,
which assumes `IsNoetherianRing A` and `IsProper f` and routes through coherence; neither is
used. -/
theorem moduleFinite_cohomology_ringBase_of_isFiniteType_rightDerived (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) := by
  have hA := moduleFinite_cohomology_of_isFiniteType_rightDerived f F n h
  exact moduleFinite_compHom_of_surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F))

/-- **The converse over an arbitrary ring base.** `A`-finiteness is pushed to
`Γ(Spec A, ⊤)`-finiteness by `…ProperCohomologyFinite.moduleFinite_of_compHom`, which needs no
surjectivity, and `isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine` concludes.
No Noetherian hypothesis on `A`. -/
theorem isFiniteType_rightDerived_of_moduleFinite_cohomology_ringBase (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (h : Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F))) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine f F n
    (moduleFinite_of_compHom (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      ((ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) h)

/-- **Over an arbitrary ring base, the finite-type conclusion of [Stacks, Tag 0EX4] in degree `n`
and finiteness of the `A`-module `Hⁿ(X, F)` are the same condition.** -/
theorem moduleFinite_cohomology_ringBase_iff_isFiniteType_rightDerived (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) :
    Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj F)) ↔
      (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType :=
  ⟨isFiniteType_rightDerived_of_moduleFinite_cohomology_ringBase A f F n,
    moduleFinite_cohomology_ringBase_of_isFiniteType_rightDerived A f F n⟩

end RingBase

/-! ### The finite-type clause of Tag 0EX4 as a module-finiteness family -/

/-- **The finite-type clause of [Stacks, Tag 0EX4] is equivalent to a module-finiteness family
over affine bases.** Each side is quantified over all of its own data. On the right the base is
affine and the conclusion is that `Hᵈ(X, F)` is a finite `Γ(Y, ⊤)`-module; on the left the base
is arbitrary and the conclusion is the tag's.

The reduction to an affine base is
`…TopDegreeFiniteType.forall_isFiniteType_rightDerived_iff_forall_isAffineBase`, itself an
equivalence, and over an affine base the two conclusions are interchangeable by
`moduleFinite_cohomology_iff_isFiniteType_rightDerived`. So nothing is weakened in either step,
and the right-hand family is the residue of the clause rather than a convenient shadow of it.

The right-hand side is [Stacks, Tag 02O6]'s own vocabulary. The two families differ by exactly
three binders: this one has no `IsLocallyNoetherian Y`, asks only that `F` be quasi-coherent of
finite type rather than coherent, and adds the bound on the dimensions of the fibres of `f`.
Over a locally Noetherian base the first two differences vanish and the third is provably inert
(`…TopDegreeFiniteType.forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology`), so
the whole of what the tag asks beyond [Stacks, Tag 02O6] is the removal of the Noetherian
hypothesis — which in the source is the limit presentation of `Γ(Y, ⊤)` by its Noetherian
subrings. -/
theorem forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology_affineBase :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → ∀ d : ℕ,
        (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) →
          ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
            (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType) ↔
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → IsAffine Y → ∀ d : ℕ,
        (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) →
          ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
            Module.Finite Γ(Y, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
              (((moduleGlobalSections X).rightDerived d).obj F))) := by
  rw [forall_isFiniteType_rightDerived_iff_forall_isAffineBase]
  constructor <;> intro h X Y f hf hY d hdim F hqc hft <;> have := hf <;> have := hY <;>
    have := hqc
  · exact moduleFinite_cohomology_of_isFiniteType_rightDerived f F d
      (h X Y f hf hY d hdim F hqc hft)
  · exact isFiniteType_rightDerived_of_moduleFinite_cohomology_of_isAffine f F d
      (h X Y f hf hY d hdim F hqc hft)

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
