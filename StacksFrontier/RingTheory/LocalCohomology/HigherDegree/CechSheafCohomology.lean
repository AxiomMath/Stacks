module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverCofinality
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Cover
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence

/-!
# The standard open covering computes cohomology on the complement of a zero locus

Let `A` be a commutative ring, let `I = (f₁, …, f_r)` be a finitely generated ideal and let
`U = Spec A \ V(I)`. The opens `D(f_i)` cover `U`, every intersection
`D(f_{i₀}) ∩ ⋯ ∩ D(f_{i_p}) = D(f_{i₀} ⋯ f_{i_p})` is an affine open of `Spec A`, and the sheaf
`M̃` associated to an `A`-module is quasi-coherent. Serre vanishing therefore makes this covering
acyclic for `M̃`, and the Čech-to-cohomology comparison of Stacks 01ET is an isomorphism: the Čech
complex of the covering computes `RΓ(U, M̃)`, in the derived category and in every degree.

This file also connects that classical cohomology to the derived sections functor
`Stacks.LocalCohomology.derivedSectionsOnAffineComplement` of
`StacksFrontier/RingTheory/LocalCohomology/AffineLocalizationTriangle.lean`, which is the right-hand
term of the affine localization triangle of Stacks 0DWR. That functor is a *total* right derived
functor on the unbounded derived category of sheaves of modules on `Spec A`, and nothing used it
before: the comparison below is its first consumer. Its degree-`p` cohomology at a sheaf placed in
degree zero is the classical `p`-th right derived functor of sections on `U`, and hence the Čech
cohomology of the standard covering.

## Main definitions

* `Stacks.LocalCohomology.cechStandardOpen` — the standard covering `D(f_i)` of
  `U = Spec A \ V(I)`, indexed in the universe of the ring as the Čech machinery requires.
* `Stacks.LocalCohomology.complementOpenScalars` — the structure map `A ⟶ Γ(Spec A, U)`, at the
  `RingCat`-valued spelling of the structure sheaf used by
  `Stacks.LocalCohomology.sectionsOnAffineComplement`.
* `Stacks.LocalCohomology.cechDerivedGlobalSectionsIso` — **the Čech complex of the standard
  covering is `RΓ(U, M̃)`** in the bounded-below derived category.
* `Stacks.LocalCohomology.cechCohomologyIsoCohomology` — the same comparison on cohomology:
  `Ȟ^p(𝒰, M̃) ≅ H^p(U, M̃)` in every degree.
* `Stacks.LocalCohomology.homologyDerivedSectionsIsoRightDerived` — the degree-`p` cohomology of
  the total right derived functor `RΓ(U, -)` at a sheaf in degree zero is the classical `p`-th
  right derived functor of sections on `U`.
* `Stacks.LocalCohomology.rightDerivedSectionsOnAffineComplementIso` — restriction of scalars to
  `A` comes out of the right derived functors of sections on `U`.
* `Stacks.LocalCohomology.derivedGlobalSectionsIsoRightDerived` — the bounded-below derived
  sections functor of Stacks 01EQ computes those same right derived functors.
* `Stacks.LocalCohomology.homologyDerivedSectionsIsoCechCohomology` — **the cohomology of the
  derived sections functor of Stacks 0DWR is Čech cohomology of the standard covering.**

## Main results

* `Stacks.LocalCohomology.isZero_rightDerived_evaluation_of_isAffineOpen` — Serre vanishing
  (Stacks 01XB) for the `ModuleCat`-valued right derived functors of `SheafOfModules.evaluation`.
* `Stacks.LocalCohomology.isAffineOpen_iInf_cechStandardOpen` — the intersections occurring in the
  Čech complex of the standard covering are affine opens.
* `Stacks.LocalCohomology.complementZeroLocus_eq_iSup_cechStandardOpen` — the basic opens of a
  family of generators cover `U`.
* `Stacks.LocalCohomology.isZero_rightDerived_evaluation_iInf_associatedSheaf` — the standard
  covering is acyclic for `M̃`, which is the hypothesis of Stacks 01ET.
* `Stacks.LocalCohomology.isIso_cechToDerivedGlobalSections_associatedSheaf` — the canonical
  comparison of Stacks 01EQ is invertible there.

## Implementation notes

The module universe is the ring universe `u` throughout, and that is forced rather than chosen:
Stacks 01ET is stated for `SheafOfModules.{u} O` with `O` a sheaf of `RingCat.{u}`-valued rings on
a space in `Type u`, and `Stacks.LocalCohomology.sectionsOnAffineComplement` lands in
`ModuleCat.{u} A`. The module-universe-independent `Stacks.LocalCohomology.associatedSheaf` is
therefore used at the universe where it agrees with Mathlib's `tilde`, which is also the only
universe at which its quasi-coherence is available.

Two spellings of the structure map `A ⟶ Γ(Spec A, U)` have to coexist.
`Stacks.LocalCohomology.complementScalars` is the same composite of maps, but its ascribed type
takes the `Ring` structure of the target through `CommRingCat`, whereas
`Stacks.LocalCohomology.sectionsOnAffineComplement` restricts scalars along the composite as
elaborated against `RingCat`. The two `Ring` instances are definitionally equal and the two
`ModuleCat.restrictScalars` functors are not *syntactically* equal, so instance search for
`Additive`, `PreservesHomology` and `PreservesFiniteLimits` succeeds for one and fails for the
other. `complementOpenScalars` is the second spelling; everything below is stated at it.

`Stacks.Cohomology.rightDerivedSingleIso` is a private declaration of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence`, reached by
`import all` rather than re-ported. It may be named in proofs but not in an exposed definition
body, so the definition whose body uses it carries `@[no_expose]`; its statement is the public one
and consumers still get the isomorphism.

`HasDerivedCategory.standard` is pinned as a local instance, as in every file of this
development. That is forced: it is already baked into the type of
`Stacks.LocalCohomology.derivedSectionsOnAffineComplement` and into the one of Stacks 01ET, and
nothing below mentions a coproduct or a product of a derived category, which is where the standard
model would make a statement vacuous.

No Stacks tag attribute is placed here. Stacks 01ET and Stacks 01XB already carry theirs, on
`Stacks.Cohomology.CechAcyclic.isIso_cechCohomologyToCohomology_app` and on
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`; what is below is their
instance at the standard covering of `Spec A \ V(I)` together with the comparison of two spellings
of derived sections, and it is not the covering set of a tag of its own.

## References

* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### Serre vanishing for the module-valued cohomology of an affine open -/

/-- **Stacks 01XB for `SheafOfModules.evaluation`.** The positive-degree right derived functors of
sections over an affine open, with their module structure over the ring of functions on that open,
vanish on a quasi-coherent sheaf of modules.

This is the abelian-group-valued Serre vanishing
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, transported along the
comparison `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`: forgetting the
module structure is exact, so it commutes with right derived functors, and a module whose
underlying abelian group is zero is zero. -/
theorem isZero_rightDerived_evaluation_of_isAffineOpen (F : (Spec (CommRingCat.of A)).Modules)
    [F.IsQuasicoherent] (V : (Spec (CommRingCat.of A)).Opens) (hV : IsAffineOpen V)
    (q : ℕ) (hq : 0 < q) :
    IsZero (((SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
      (op V)).rightDerived q).obj F) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero
      (show IsZero (((SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
            (op V)).rightDerived q ⋙
          forget₂ (ModuleCat.{u} ((Spec (CommRingCat.of A)).ringCatSheaf.obj.obj (op V)))
            AddCommGrpCat.{u}).obj F) from
        (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen _ F V hV q hq).of_iso
          ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
            (Spec (CommRingCat.of A)).ringCatSheaf V q).app F)))

/-! ### The standard covering of the complement of a zero locus -/

/-- An element of the ring, as a global function on `Spec A`. -/
abbrev specGlobalSection (a : A) : Γ(Spec (CommRingCat.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv a

/-- **The standard covering of `U = Spec A \ V(I)`** attached to a finite family of generators of
`I`: the basic open `D(f_i)`, indexed by a copy of `Fin r` in the universe of the ring, as the
Čech machinery of Stacks 01EP requires. It is written as the basic open of a global function on the
scheme `Spec A` rather than as a basic open of the prime spectrum, because that is the spelling in
which the affineness of the intersections is available. -/
def cechStandardOpen {r : ℕ} (f : Fin r → A) (i : ULift.{u} (Fin r)) :
    (Spec (CommRingCat.of A)).Opens :=
  (Spec (CommRingCat.of A)).basicOpen (specGlobalSection (f i.down))

/-- A member of the standard covering is the basic open of the prime spectrum. -/
theorem cechStandardOpen_eq_basicOpen {r : ℕ} (f : Fin r → A) (i : ULift.{u} (Fin r)) :
    cechStandardOpen f i = PrimeSpectrum.basicOpen (f i.down) :=
  basicOpen_eq_of_affine _

/-- **The intersections occurring in the Čech complex of the standard covering are affine
opens**: a finite intersection of basic opens of an affine open is the basic open of the product of
the corresponding functions. -/
theorem isAffineOpen_iInf_cechStandardOpen {r : ℕ} (f : Fin r → A) {m : ℕ}
    (s : Fin (m + 1) → ULift.{u} (Fin r)) :
    IsAffineOpen (⨅ k, cechStandardOpen f (s k)) :=
  Stacks.Cohomology.Cech.isAffineOpen_iInf_basicOpen
    (isAffineOpen_top (Spec (CommRingCat.of A))) (fun i => specGlobalSection (f i))
    (fun k => (s k).down)

/-- **The standard covering covers `U = Spec A \ V(I)`.** A prime avoids `V(I)` exactly when it
avoids one of the generators. -/
theorem complementZeroLocus_eq_iSup_cechStandardOpen {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hIf : Ideal.span (Set.range f) = I) :
    complementZeroLocus A I = ⨆ i, cechStandardOpen f i := by
  refine Eq.trans (complementZeroLocus_eq_iSup_basicOpen f I hIf)
    (le_antisymm (iSup_le fun i => ?_) (iSup_le fun i => ?_))
  · exact (cechStandardOpen_eq_basicOpen f ⟨i⟩).ge.trans
      (le_iSup (fun j => cechStandardOpen f j) ⟨i⟩)
  · exact (cechStandardOpen_eq_basicOpen f i).le.trans
      (le_iSup (fun j : Fin r => PrimeSpectrum.basicOpen (f j)) i.down)

/-- The sheaf on `Spec A` associated to an `A`-module in the ring's own universe is
quasi-coherent: it is Mathlib's `tilde`. -/
instance isQuasicoherent_associatedSheaf (M : ModuleCat.{u} A) :
    (associatedSheaf A M).IsQuasicoherent :=
  inferInstanceAs ((tilde.functor (CommRingCat.of A)).obj M).IsQuasicoherent

/-- **The standard covering is acyclic for `M̃`**, which is the hypothesis of Stacks 01ET: the
intersections are affine opens and `M̃` is quasi-coherent, so Serre vanishing applies. -/
theorem isZero_rightDerived_evaluation_iInf_associatedSheaf {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{u} A) {m : ℕ} (s : Fin (m + 1) → ULift.{u} (Fin r)) (q : ℕ) (hq : 0 < q) :
    IsZero (((SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
      (op (⨅ k, cechStandardOpen f (s k)))).rightDerived q).obj (associatedSheaf A M)) :=
  isZero_rightDerived_evaluation_of_isAffineOpen _ _ (isAffineOpen_iInf_cechStandardOpen f s) q hq

/-! ### The Čech complex of the standard covering computes `RΓ(U, M̃)` -/

variable {r : ℕ} (f : Fin r → A) (I : Ideal A) (hIf : Ideal.span (Set.range f) = I)
  (M : ModuleCat.{u} A)

/-- **The Čech-to-derived-sections transformation of Stacks 01EQ is invertible at `M̃` for the
standard covering of `U = Spec A \ V(I)`.** This is Stacks 01ET together with the acyclicity
supplied by Serre vanishing. -/
theorem isIso_cechToDerivedGlobalSections_associatedSheaf :
    IsIso ((Stacks.Cohomology.CechDerived.cechToDerivedGlobalSections
      (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) (cechStandardOpen f)
      (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf)).app (associatedSheaf A M)) :=
  Stacks.Cohomology.CechAcyclic.isIso_cechToDerivedGlobalSections_app
    (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) (cechStandardOpen f)
    (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) (associatedSheaf A M)
    fun _ s _ hq => isZero_rightDerived_evaluation_iInf_associatedSheaf f M s _ hq

/-- **The Čech complex of the standard covering is `RΓ(U, M̃)`.** For `U = Spec A \ V(I)` covered
by the basic opens of a finite family of generators of `I`, the Čech complex of `M̃`, viewed in the
bounded-below derived category of `Γ(Spec A, U)`-modules, is isomorphic to derived sections of `M̃`
on `U`, by the canonical comparison of Stacks 01EQ. -/
def cechDerivedGlobalSectionsIso :
    (Stacks.Cohomology.CechDerived.cechComplexPlusFunctor
          (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) (cechStandardOpen f)
          (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) ⋙
        DerivedCategory.Plus.Q).obj (associatedSheaf A M) ≅
      (Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor
        (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I)).obj
          (associatedSheaf A M) :=
  @asIso _ _ _ _ _ (isIso_cechToDerivedGlobalSections_associatedSheaf f I hIf M)

/-- **`Ȟ^p(𝒰, M̃) ≅ H^p(U, M̃)` for the standard covering.** The canonical maps of Stacks 01EQ from
the Čech cohomology of the standard covering of `U = Spec A \ V(I)` to the cohomology of `M̃` on
`U` are isomorphisms in every degree. -/
def cechCohomologyIsoCohomology (p : ℕ) :
    (Stacks.Cohomology.CechDerived.cechComplexPlusFunctor
          (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) (cechStandardOpen f)
          (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (associatedSheaf A M) ≅
    (Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor
        (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) ⋙
      DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj (associatedSheaf A M) :=
  @asIso _ _ _ _
    ((Stacks.Cohomology.CechDerived.cechCohomologyToCohomology
      (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) (cechStandardOpen f)
      (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) (p : ℤ)).app (associatedSheaf A M))
    (Stacks.Cohomology.CechAcyclic.isIso_cechCohomologyToCohomology_app
      (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) (cechStandardOpen f)
      (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) (associatedSheaf A M)
      (fun _ s _ hq => isZero_rightDerived_evaluation_iInf_associatedSheaf f M s _ hq) p)

/-! ### The derived sections functor of Stacks 0DWR -/

section DerivedSections

variable (J : Ideal A)

/-- **The structure map `A ⟶ Γ(Spec A, U)` for `U = Spec A \ V(J)`**, at the `RingCat`-valued
spelling of the structure sheaf along which
`Stacks.LocalCohomology.sectionsOnAffineComplement` restricts scalars.

It is the same composite of maps as `Stacks.LocalCohomology.complementScalars`, whose ascribed
type instead takes the ring structure of the target through `CommRingCat`. The two ring
structures are definitionally equal; the two `ModuleCat.restrictScalars` functors are not
syntactically equal, which is what makes two spellings necessary. -/
abbrev complementOpenScalars : A →+*
    (Spec (CommRingCat.of A)).ringCatSheaf.obj.obj (op (complementZeroLocus A J)) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
      (homOfLE (le_top (a := complementZeroLocus A J))).op).hom.comp
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv)

/-- Sections over `U = Spec A \ V(J)` of the underlying presheaf of a sheaf of modules on
`Spec A` is an additive functor. -/
instance additive_evaluation_complementZeroLocus :
    (SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
      (op (complementZeroLocus A J))).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- **The cohomology of the derived sections functor of Stacks 0DWR is classical sheaf
cohomology.** The degree-`p` cohomology of the total right derived functor `RΓ(U, -)` on the
unbounded derived category, evaluated at a sheaf of modules placed in degree zero, is the
classical `p`-th right derived functor of sections over `U = Spec A \ V(J)`.

This is `Stacks.Cohomology.rightDerivedSingleIso` — the general comparison, for a right
derived functor in the sense of Kan extensions along `Qh`, between its cohomology at an object in
degree zero and the right derived functors computed from an injective resolution — applied with
the K-injective resolutions of
`Stacks.LocalCohomology.exists_quasiIso_isKInjective_specModules`. It is the first consumer of
`Stacks.LocalCohomology.derivedSectionsOnAffineComplement`. -/
@[no_expose] public def homologyDerivedSectionsIsoRightDerived
    (P : (Spec (CommRingCat.of A)).Modules) (p : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p : ℤ)).obj
        ((derivedSectionsOnAffineComplement A J).obj
          ((DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules 0).obj P)) ≅
      ((sectionsOnAffineComplement A J).rightDerived p).obj P :=
  Stacks.Cohomology.rightDerivedSingleIso (sectionsOnAffineComplement A J)
    (derivedSectionsOnAffineComplement A J) (derivedSectionsOnAffineComplementUnit A J)
    (exists_quasiIso_isKInjective_specModules A) P p

/-- **`A`-linear derived sections on `U` are derived sections over `Γ(Spec A, U)`, with scalars
restricted.** Restriction of scalars is exact, so it may be pulled out of a right derived
functor; `Stacks.LocalCohomology.sectionsOnAffineComplement` is by definition sections over `U`
followed by restriction of scalars along
`Stacks.LocalCohomology.complementOpenScalars`. -/
def rightDerivedSectionsOnAffineComplementIso (p : ℕ) :
    (sectionsOnAffineComplement A J).rightDerived p ≅
      (SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
          (op (complementZeroLocus A J))).rightDerived p ⋙
        ModuleCat.restrictScalars.{u, u, u} (complementOpenScalars J) :=
  letI : (ModuleCat.restrictScalars.{u, u, u} (complementOpenScalars J)).PreservesHomology :=
    restrictScalars_preservesHomology (complementOpenScalars J)
  CategoryTheory.Functor.rightDerivedCompIso
    (SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
      (op (complementZeroLocus A J)))
    (ModuleCat.restrictScalars.{u, u, u} (complementOpenScalars J)) p

/-- The bounded-below derived sections functor of Stacks 01EQ computes, in degree `p`, the
classical `p`-th right derived functor of sections over `U = Spec A \ V(J)`. -/
def derivedGlobalSectionsIsoRightDerived (P : (Spec (CommRingCat.of A)).Modules) (p : ℕ) :
    (Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor
          (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A J) ⋙
        DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj P ≅
      ((SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
        (op (complementZeroLocus A J))).rightDerived p).obj P :=
  Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObj
    (SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
      (op (complementZeroLocus A J))) P p

end DerivedSections

/-- **The cohomology of the derived sections functor of Stacks 0DWR is the Čech cohomology of the
standard covering.** For `I = (f₁, …, f_r)` and `U = Spec A \ V(I)`, the degree-`p` cohomology of
`RΓ(U, M̃)` is, after restricting scalars from `Γ(Spec A, U)` to `A`, the degree-`p` Čech
cohomology of `M̃` for the covering of `U` by the basic opens `D(f_i)`.

The three steps are `Stacks.LocalCohomology.homologyDerivedSectionsIsoRightDerived` (the total
right derived functor computes the classical one),
`Stacks.LocalCohomology.rightDerivedSectionsOnAffineComplementIso` (restriction of scalars comes
out of the derived functor) and
`Stacks.LocalCohomology.cechCohomologyIsoCohomology` (Stacks 01ET for the standard covering). -/
def homologyDerivedSectionsIsoCechCohomology (p : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p : ℤ)).obj
        ((derivedSectionsOnAffineComplement A I).obj
          ((DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules 0).obj
            (associatedSheaf A M))) ≅
      (ModuleCat.restrictScalars.{u, u, u} (complementOpenScalars I)).obj
        ((Stacks.Cohomology.CechDerived.cechComplexPlusFunctor
            (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) (cechStandardOpen f)
            (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) ⋙
          DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
            (associatedSheaf A M)) :=
  homologyDerivedSectionsIsoRightDerived I (associatedSheaf A M) p ≪≫
    (rightDerivedSectionsOnAffineComplementIso I p).app (associatedSheaf A M) ≪≫
    (ModuleCat.restrictScalars.{u, u, u} (complementOpenScalars I)).mapIso
      ((derivedGlobalSectionsIsoRightDerived I (associatedSheaf A M) p).symm ≪≫
        (cechCohomologyIsoCohomology f I hIf M p).symm)

end Stacks.LocalCohomology

end
