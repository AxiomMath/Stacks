module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic

/-!
# [Stacks, Tag 02O6] over an arbitrary ring base

[Stacks, Tag 02O6] is stated over a Noetherian **ring**: for `A` Noetherian,
`f : X ⟶ Spec A` proper and `F` coherent, each `Hⁱ(X, F)` is a finite `A`-module, the
`A`-action being the one obtained by restricting scalars along `A ≅ Γ(Spec A, ⊤) → Γ(X, ⊤)`.

`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/Basic.lean` proves the mathematical
content of the tag — finiteness of `Hⁿ(X, F)` is coherence of `Rⁿ f_* F` — but states it over
`Γ(S, ⊤)` for an affine base scheme `S`, which is the spelling [Stacks, Tag 01XK] lands in and
needs no transport. The move to a ring base was made there only for a **field**, inside
`AlgebraicGeometry.cohomologyOverField`. This file makes it for an arbitrary commutative ring,
so that the tag's own statement is available as a term.

The transport is in both directions and neither needs Noetherianness, properness or coherence:

* `A`-finiteness **from** `Γ(Spec A, ⊤)`-finiteness, because `A ≅ Γ(Spec A, ⊤)` is in particular
  a surjective ring map (`moduleFinite_compHom_of_surjective`, already in `Basic.lean`);
* `Γ(Spec A, ⊤)`-finiteness **from** `A`-finiteness, because a module finite over a ring acting
  through another is finite over that other ring — `moduleFinite_of_compHom` below, which needs
  no surjectivity at all and is the sharper of the two.

## Main results

* `Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_of_compHom`: a module finite
  over `R` for the action obtained from `ψ : R →+* A` is finite over `A`.
* `…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isCoherent`: **[Stacks, Tag 02O6]
  over a ring base, from coherence of `Rⁿ f_* F`** — the tag's conclusion verbatim, for a
  quasi-compact quasi-separated `f` and a quasi-coherent `F`, with no Noetherian hypothesis.
* `…ProperCohomologyFinite.isCoherent_rightDerived_of_moduleFinite_cohomology_ringBase` and
  `…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_iff_isCoherent`: the converse and the
  equivalence, over a Noetherian ring. **So [Stacks, Tag 02O6] at a ring base and the affine case
  of [Stacks, Tag 02O5] at that base are the same statement**, which together with
  `…ProperCohomologyFinite.forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology`
  says that nothing is gained by attacking the tag in this spelling rather than that one.
* `…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isFiniteType`: the same from the
  single property `IsFiniteType` of `Rⁿ f_* F`, under properness.
* `…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isFinite` and
  `…ProperCohomologyFinite.moduleFinitePlus_cohomology_ringBase_of_isFinite`: **[Stacks,
  Tag 02O6] over a ring base for a *finite* morphism, unconditionally**, in both indexings of the
  right derived functor.
* `…ProperCohomologyFinite.moduleFinitePlus_cohomology_ringBase_of_isCoherent`: the conditional
  result in the `Functor.rightDerivedPlus` indexing.

## Implementation notes

**No `@[stacks 02O6]` attribute is attached to anything here.** The conditional statements carry
coherence (or finiteness of type) of `Rⁿ f_* F` as a hypothesis, which is [Stacks, Tag 02O5] and
is not in the library for a general proper morphism; the unconditional ones replace the tag's
`IsProper f` by the strictly stronger `IsFinite f`. Withholding the attribute is the point: the
equivalence below shows that this spelling of the tag is exactly as hard as the other, so an
attribute here would assert something no declaration in the library proves.

Two indexings of the right derived functor are in use. [Stacks, Tag 02O6]'s `Hⁱ` and
`ProperCohomologyFinite/Basic.lean` use `CategoryTheory.Functor.rightDerived` (indexed by `ℕ`);
the tagged statements and the dévissage development use `CategoryTheory.Functor.rightDerivedPlus`
(indexed by `ℤ`). `Stacks.DerivedIndexing.rightDerivedIso` compares them, and the `…Plus…`
variants below are the `ℕ`-indexed ones transported along it.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.ProperCohomologyFinite

attribute [local instance] HasDerivedCategory.standard

/-! ### Transport of finiteness along an arbitrary ring map -/

/-- **A module finite over `R` for an action factored through `ψ : R →+* A` is finite over `A`.**
No surjectivity is needed: `R` acts through `A`, so an `R`-spanning set spans over `A`.

This is the mirror of `moduleFinite_compHom_of_surjective`, which goes the other way and does
need surjectivity. -/
theorem moduleFinite_of_compHom {R A : Type u} [CommRing R] [CommRing A] (ψ : R →+* A)
    (M : Type u) [AddCommGroup M] [Module A M]
    (h : @Module.Finite R M _ _ (Module.compHom M ψ)) : Module.Finite A M := by
  let _ : Module R M := Module.compHom M ψ
  let _ : Algebra R A := ψ.toAlgebra
  have : IsScalarTower R A M := ⟨fun x a m => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact mul_smul (ψ x) a m⟩
  have := h
  exact Module.Finite.of_restrictScalars_finite R A M

/-! ### [Stacks, Tag 02O6] over a ring base -/

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]

/-- **[Stacks, Tag 02O6] over a ring base, from [Stacks, Tag 02O5].** For `f : X ⟶ Spec A`
quasi-compact and quasi-separated and `F` quasi-coherent, coherence of `Rⁿ f_* F` makes
`Hⁿ(X, F)` a finite `A`-module, the `A`-structure being the restriction of scalars along
`A ≅ Γ(Spec A, ⊤) → Γ(X, ⊤)`.

This is the tag's conclusion verbatim. Finiteness over `Γ(Spec A, ⊤)` is
`moduleFinite_cohomology_of_isCoherent`, and it is moved to `A` across the ring isomorphism
`Scheme.ΓSpecIso` by `moduleFinite_compHom_of_surjective`. Properness, coherence of `F` and
Noetherianness of `A` are all unused. -/
theorem moduleFinite_cohomology_ringBase_of_isCoherent (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) := by
  have := moduleFinite_cohomology_of_isCoherent f F n h
  exact moduleFinite_compHom_of_surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F))

/-- **The converse**, over a Noetherian ring: finiteness of `Hⁿ(X, F)` as an `A`-module makes
`Rⁿ f_* F` coherent.

`A`-finiteness is pushed to `Γ(Spec A, ⊤)`-finiteness by `moduleFinite_of_compHom` and
`isCoherent_of_moduleFinite_cohomology` concludes; `Spec A` is locally Noetherian because `A`
is. -/
theorem isCoherent_rightDerived_of_moduleFinite_cohomology_ringBase [IsNoetherianRing A]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (h : Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F))) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent :=
  isCoherent_of_moduleFinite_cohomology f F n
    (moduleFinite_of_compHom (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      ((ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) h)

/-- **[Stacks, Tag 02O6] over a ring base is the affine case of [Stacks, Tag 02O5].** Over a
Noetherian ring `A`, `Hⁿ(X, F)` is a finite `A`-module exactly when `Rⁿ f_* F` is coherent.

Together with
`forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology` — which says
[Stacks, Tag 02O5] and [Stacks, Tag 02O6] over an affine base scheme are equivalent — this says
that stating the tag over a ring rather than over `Γ(S, ⊤)` changes nothing about its
difficulty. -/
theorem moduleFinite_cohomology_ringBase_iff_isCoherent [IsNoetherianRing A] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) :
    Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj F)) ↔
      (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent :=
  ⟨isCoherent_rightDerived_of_moduleFinite_cohomology_ringBase A f F n,
    moduleFinite_cohomology_ringBase_of_isCoherent A f F n⟩

/-- **[Stacks, Tag 02O6] over a ring base from the single property `IsFiniteType`.** For `f`
proper and `A` Noetherian, finiteness of type of `Rⁿ f_* F` suffices: quasi-coherence is
[Stacks, Tag 01XJ] by instance search and quasi-coherent of finite type over a locally Noetherian
scheme is coherent ([Stacks, Tag 01XZ]). -/
theorem moduleFinite_cohomology_ringBase_of_isFiniteType [IsNoetherianRing A]
    [AlgebraicGeometry.IsProper f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) :=
  moduleFinite_cohomology_ringBase_of_isCoherent A f F n
    (isCoherent_rightDerived_of_isFiniteType f F n h)

/-- **[Stacks, Tag 02O6] over a ring base for a finite morphism**, unconditionally. A finite
morphism is proper, so this is the tag's conclusion under the strictly stronger hypothesis
`IsFinite f`; the coherence input is [Stacks, Tag 01Y6]. -/
theorem moduleFinite_cohomology_ringBase_of_isFinite (A : Type u) [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (g : X ⟶ Spec (.of A))
    [AlgebraicGeometry.IsFinite g] (F : X.Modules) [F.IsCoherent] (n : ℕ) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) := by
  have := (isQuasicoherent_isFiniteType_of_isCoherent F).1
  exact moduleFinite_cohomology_ringBase_of_isCoherent A g F n
    (isCoherent_rightDerived_of_isFinite g F n)

/-! ### The same in the `rightDerivedPlus` indexing -/

/-- Finiteness of `Hⁿ(X, F)` over `A` transfers along `rightDerivedIso` to the
`Functor.rightDerivedPlus` indexing. -/
private theorem moduleFinitePlus_of_moduleFinite {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A))
    (F : Y.Modules) (n : ℕ)
    (h : Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
        (((moduleGlobalSections Y).rightDerived n).obj F))) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
        (((moduleGlobalSections Y).rightDerivedPlus (n : ℤ)).obj F)) :=
  Module.Finite.equiv
    ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections Y) n).app F)).toLinearEquiv

/-- `moduleFinite_cohomology_ringBase_of_isCoherent` in the `Functor.rightDerivedPlus` indexing,
which is the one the tagged statements and the dévissage development use. The two indexings are
compared by `Stacks.DerivedIndexing.rightDerivedIso`. -/
theorem moduleFinitePlus_cohomology_ringBase_of_isCoherent (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj F)) :=
  moduleFinitePlus_of_moduleFinite A f F n
    (moduleFinite_cohomology_ringBase_of_isCoherent A f F n h)

/-- **[Stacks, Tag 02O6] over a ring base for a finite morphism, in the `rightDerivedPlus`
indexing**, unconditionally. -/
theorem moduleFinitePlus_cohomology_ringBase_of_isFinite (A : Type u) [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (g : X ⟶ Spec (.of A))
    [AlgebraicGeometry.IsFinite g] (F : X.Modules) [F.IsCoherent] (n : ℕ) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
        (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj F)) :=
  moduleFinitePlus_of_moduleFinite A g F n
    (moduleFinite_cohomology_ringBase_of_isFinite A g F n)

/-! ### The ring spelling of the tag is the same obligation as the coherence -/

/-- **[Stacks, Tag 02O6] in its own ring spelling, quantified over all its data, is equivalent to
[Stacks, Tag 02O5] over the bases `Spec A`.** Each direction is the pointwise equivalence
`moduleFinite_cohomology_ringBase_iff_isCoherent`.

This statement rules out a proof strategy. The natural route derives the tag from
coherence of `Rⁿ f_* F`, which is [Stacks, Tag 02O5]; the derivation itself is already in the
library, more generally, as `moduleFinite_cohomology_of_isCoherent`. The equivalence here says
that the derivation cannot be the whole of a proof of the tag under any spelling: its hypothesis
is exactly as strong as its conclusion. Together with
`forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology`, which lifts the affine
case to a general locally Noetherian base, the two tags are one obligation and the obligation is
the finiteness theorem itself — in the source, a dévissage ([Stacks, Tag 01YI]) over Chow's lemma
([Stacks, Tag 0200]). -/
theorem forall_moduleFinite_cohomology_ringBase_iff_forall_isCoherent_rightDerived :
    (∀ (A : Type u) [CommRing A], IsNoetherianRing A →
        ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), AlgebraicGeometry.IsProper f →
          ∀ F : X.Modules, F.IsQuasicoherent → ∀ n : ℕ,
            Module.Finite A
              ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
                (((moduleGlobalSections X).rightDerived n).obj F))) ↔
      (∀ (A : Type u) [CommRing A], IsNoetherianRing A →
        ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), AlgebraicGeometry.IsProper f →
          ∀ F : X.Modules, F.IsQuasicoherent → ∀ n : ℕ,
            (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent) := by
  constructor
  · intro h A _ hA X f hf F hF n
    exact isCoherent_rightDerived_of_moduleFinite_cohomology_ringBase A f F n
      (h A hA X f hf F hF n)
  · intro h A _ hA X f hf F hF n
    exact moduleFinite_cohomology_ringBase_of_isCoherent A f F n (h A hA X f hf F hF n)

end Stacks.AlgebraicGeometry.ProperCohomologyFinite

end
