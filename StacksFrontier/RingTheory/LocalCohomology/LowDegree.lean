module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections on the complement of a zero locus in an affine scheme

Let `A` be a commutative ring and `I ⊆ A` an ideal, and let `U = Spec A \ V(I)` be the open
complement of the zero locus of `I`. The low-degree exact sequence of local cohomology
(Stacks 0DWR) compares an `A`-module `M` with the sections on `U` of the quasi-coherent
module it generates. This file builds the geometric half of that comparison: the locally
fractional sections of a module whose universe is unrelated to the universe of the ring,
restriction of sheaves of modules along an open immersion with an independent section universe,
and the `A`-module of global sections on `U`.

Mathlib's `AlgebraicGeometry.tilde`, and the structure sheaf it is built from, force the module
to live in the same universe as the ring. Local cohomology is applied to modules whose universe
is independent of the ring's, so the locally-fractional construction is repeated here with that
restriction removed: `moduleSections` is the `A`-module of locally fractional sections on an
open of `Spec A` — Mathlib's `StructureSheaf.sectionsSubmodule` with the universes separated —
and `associatedAbPresheaf` assembles them into a sheaf of abelian groups, functorially in the
module. `associatedAbPresheaf_eq_tilde` and `restrictFunctor_eq` record that in a common
universe these are definitionally Mathlib's constructions, so nothing is duplicated
mathematically.

## Main definitions

* `Stacks.LocalCohomology.complementZeroLocus` — the open `Spec A \ V(I)`.
* `Stacks.LocalCohomology.moduleSections` — locally fractional sections of a module on an
  open of `Spec A`, as an `A`-submodule of the product of the localizations.
* `Stacks.LocalCohomology.associatedAbPresheaf`, `associatedAbPresheafMap` — those sections as
  a presheaf of abelian groups, functorially in the module.
* `Stacks.LocalCohomology.restrictFunctor` — restriction of sheaves of modules along an open
  immersion, with the section universe independent of the scheme universe.
* `Stacks.LocalCohomology.complementGlobalSections`,
  `Stacks.LocalCohomology.complementGlobalSectionsFunctor` — global sections on
  `Spec A \ V(I)`, regarded as an `A`-module by restriction of scalars.

## Main results

* `Stacks.LocalCohomology.associatedAbPresheaf_isSheaf` — the locally fractional presheaf is a
  sheaf.
* `Stacks.LocalCohomology.associatedAbPresheaf_eq_tilde`,
  `Stacks.LocalCohomology.restrictFunctor_eq` — agreement with Mathlib's constructions when the
  ring and the module share a universe.

The structure-sheaf action on `moduleSections`, and hence the sheaf *of modules* associated to a
module of independent universe, is in
`StacksFrontier/RingTheory/LocalCohomology/LowDegree/ExactSequence.lean`, where it is assembled
into `Stacks.LocalCohomology.associatedSheaf`.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The open complement of the zero locus of an ideal in an affine spectrum. -/
def complementZeroLocus (R : Type u) [CommRing R] (I : Ideal R) :
    (Spec (CommRingCat.of R)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).isOpen_compl⟩

/-- A family of elements of the localizations is a fraction if a single numerator and
denominator represent it at every prime. This is the predicate used in Mathlib's `tilde`
construction, with the ring and module universes allowed to differ. -/
def moduleIsFractionPrelocal (M : ModuleCat.{v} A) :
    TopCat.PrelocalPredicate
      (fun x : PrimeSpectrum.Top A ↦ LocalizedModule x.asIdeal.primeCompl M) where
  pred {_} s := ∃ m a, ∀ x, ∃ ha : a ∉ x.1.asIdeal,
    s x = LocalizedModule.mk m ⟨a, ha⟩
  res := by rintro V U i s ⟨m, a, h⟩; exact ⟨m, a, fun x ↦ h (i x)⟩

/-- The `A`-module of locally fractional sections of `M` on an open of `Spec A`. -/
def moduleSections (M : ModuleCat.{v} A) (U : Opens (PrimeSpectrum.Top A)) :
    Submodule A (∀ x : U, LocalizedModule x.1.asIdeal.primeCompl M) where
  carrier := {s | (moduleIsFractionPrelocal M).sheafify.pred s}
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia,
      sb • ra + sa • rb, sa * sb, fun x ↦ ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa + $hsb).trans (LocalizedModule.mk_add_mk ..)⟩
  zero_mem' x := ⟨U, x.2, 𝟙 _, 0, 1, fun y ↦ by simp [Ideal.IsPrime.one_notMem]⟩
  smul_mem' r {a} ha x := by
    obtain ⟨V, m, i, ra, sa, wa⟩ := ha x
    exact ⟨V, m, i, r • ra, sa, fun x ↦ ⟨(wa x).1,
      congr(r • $((wa x).2)).trans (LocalizedModule.smul'_mk ..)⟩⟩

/-- The presheaf of abelian groups underlying the associated sheaf of `M`, constructed as
locally fractional sections exactly as in Mathlib's `tilde`, for an arbitrary module
universe. -/
def associatedAbPresheaf (M : ModuleCat.{v} A) :
    TopCat.Presheaf AddCommGrpCat.{max u v} (PrimeSpectrum.Top A) where
  obj U := AddCommGrpCat.of (moduleSections M U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨fun x ↦ s.1 (i.unop x),
        (moduleIsFractionPrelocal M).sheafify.res i.unop s.1 s.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- The locally fractional presheaf satisfies the sheaf condition. -/
theorem associatedAbPresheaf_isSheaf (M : ModuleCat.{v} A) :
    (associatedAbPresheaf M).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat)
    (associatedAbPresheaf M)).2
    (TopCat.subsheafToTypes (moduleIsFractionPrelocal M).sheafify).2

/-- When the ring and the module share a universe, this is precisely the presheaf underlying
Mathlib's `tilde`. -/
theorem associatedAbPresheaf_eq_tilde (M : ModuleCat.{u} A) :
    associatedAbPresheaf M =
      (Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).obj (tilde M) := rfl

/-- A module map acts on locally fractional sections by applying it to numerators. -/
def associatedAbPresheafMap {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    associatedAbPresheaf M ⟶ associatedAbPresheaf N where
  app U := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨fun x ↦ IsLocalizedModule.map x.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) g.hom (s.1 x), by
        intro x
        obtain ⟨V, hx, i, m, a, h⟩ := s.2 x
        refine ⟨V, hx, i, g m, a, fun y ↦ ⟨(h y).1, ?_⟩⟩
        exact (congrArg (IsLocalizedModule.map y.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) g.hom)
          (h y).2).trans (IsLocalizedModule.map_LocalizedModules _ _ _ _)⟩
      map_zero' := by apply Subtype.ext; funext x; exact map_zero _
      map_add' s t := by apply Subtype.ext; funext x; exact map_add _ _ _ }
  naturality {U V} i := by ext s; rfl

/-- Restriction of sheaves of modules along an open immersion, with the section universe
independent of the scheme universe. -/
def restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.{v} Y.ringCatSheaf ⥤ SheafOfModules.{v} X.ringCatSheaf :=
  letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  SheafOfModules.pushforward (F := f.opensFunctor)
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- In a common universe this is Mathlib's restriction functor. -/
theorem restrictFunctor_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    restrictFunctor.{u, u} f = Scheme.Modules.restrictFunctor f := rfl

variable (A) in
/-- Global sections on `Spec A \ V(I)`, regarded as an `A`-module through the canonical map
from `A` to the global sections of the structure sheaf. -/
abbrev complementGlobalSections (I : Ideal A)
    (F : SheafOfModules.{v} (complementZeroLocus A I : Scheme).ringCatSheaf) :
    ModuleCat.{v} A :=
  letI : Module Γ((complementZeroLocus A I : Scheme), ⊤) (F.val.obj (op ⊤)) :=
    (F.val.obj (op ⊤)).isModule
  letI : Module A (F.val.obj (op ⊤)) := Module.compHom _
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (complementZeroLocus A I).ι.appTop).hom
  ModuleCat.of A (F.val.obj (op ⊤))

variable (A) in
/-- Global sections on `Spec A \ V(I)` as a functor to `A`-modules, with scalars restricted
along the canonical map from `A`. -/
def complementGlobalSectionsFunctor (I : Ideal A) :
    SheafOfModules.{v} (complementZeroLocus A I : Scheme).ringCatSheaf ⥤ ModuleCat.{v} A :=
  SheafOfModules.evaluation _ (op ⊤) ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (complementZeroLocus A I).ι.appTop).hom

end Stacks.LocalCohomology
