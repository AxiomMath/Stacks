module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamLocalInjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DeRhamSectionwise
import StacksCore.Tactic.StacksAttribute

/-!
# The relative de Rham complex of sheaves of rings exists and is unique

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B` the
structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative differentials and
let `B` also denote a package of the three algebras of Stacks Section 17.21 for `Ω`, so that
`⋀ᵖ Ω` is available. `StacksFrontier.Topology.Sheaves.Modules.DeRham` defines a *de Rham
differential* on `⋀ᵖ Ω` — a square-zero family of morphisms of sheaves of `A`-modules obeying

`d (b₀ · d b₁ ∧ ⋯ ∧ d bₚ) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d bₚ`

on every local section of that shape — and `DeRhamUniqueness` proves there is at most one.
**This file constructs one**, which finishes Tag 0FKM.

The construction is the Stacks proof. `⋀ᵖ Ω` is the sheafification of the presheaf
`U ↦ ⋀ᵖ_{B(U)}(Ω_{B(U)/A(U)})`, with `AlgebraicGeometry.SheafOfModules.exactWedgeComparison` as
the sheafification map (`DeRhamLocalInjectivity`), and the ring-level de Rham differentials
assemble into a morphism `PresheafOfModules.sectionwiseDeRhamDifferential` of presheaves of
`A`-modules between those presheaves (`DeRhamSectionwise`). Sheafifying that morphism and
transporting it along the comparison gives the differential.

The one step not already available is that the comparison stays a sheafification map after
**restriction of scalars from `B` to `A`**:
`isIso_sheafificationHomEquiv_symm_exactWedgeComparison` is a statement about sheaves of
`B`-modules, while the sectionwise differential is a morphism of presheaves of `A`-modules. That
is `isIso_restrictedComparison` below, and it is cheap for a structural reason: restriction of
scalars does not change the underlying presheaf of abelian groups, so the local injectivity and
local surjectivity that exhibit a morphism as a sheafification map are literally the same two
statements before and after it.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.restrictedComparison`: the exact-wedge comparison, read as a
  morphism of presheaves of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.deRhamTermIso`: `⋀ᵖ Ω` **is** the sheafification, as a sheaf
  of `A`-modules, of the presheaf of sectionwise exterior powers of the sectionwise Kähler
  differentials.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferentialHom`: the degree-`p` de Rham differential,
  obtained by sheafifying `PresheafOfModules.sectionwiseDeRhamDifferential` and conjugating by
  that isomorphism.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferential`: **the de Rham differential**, as a term
  of `AlgebraicGeometry.SheafOfModules.DeRhamDifferential`.
* `AlgebraicGeometry.SheafOfModules.relativeDeRhamComplex`: **the relative de Rham complex**
  `⋀⁰ Ω → ⋀¹ Ω → ⋀² Ω → ⋯` of sheaves of `A`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.isIso_restrictedComparison`: **sheafification commutes with
  restriction of scalars for the exact-wedge comparison** — the comparison, read as a morphism of
  presheaves of `A`-modules, still exhibits `⋀ᵖ Ω` as the sheafification of its source, now in
  sheaves of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferentialHom_app_exactWedgeComparison`: the
  descended differential computes the sectionwise one through the comparison. This is the identity
  that transports every property of the sectionwise differential to the sheaf level.
* `AlgebraicGeometry.SheafOfModules.exactWedgeComparison_app_ιMulti_d`: the comparison carries the
  wedge of the exact sectionwise differentials of `c₀, …, c_{p-1}` to the ordered product of the
  degree-one generators.
* `AlgebraicGeometry.SheafOfModules.exists_eq_homogeneousProdLeft`: **an exact wedge is an ordered
  product of exact differentials**, the converse of
  `AlgebraicGeometry.SheafOfModules.isExactWedge_homogeneousProdLeft`. It is what makes the de
  Rham rule checkable on an arbitrary exact wedge: an exact wedge is, on the nose, the comparison
  of a wedge of exact sectionwise differentials.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferentialHom_comp_self` and
  `AlgebraicGeometry.SheafOfModules.deRhamDifferentialHom_generator`: the two axioms of a de Rham
  differential.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferential_unique`: there is no other de Rham
  differential; this is `AlgebraicGeometry.SheafOfModules.DeRhamDifferential.eq` read at the
  constructed one.

## Implementation notes

What is forced and what is chosen.

* The package of algebras is a **hypothesis**, as everywhere in this group of files, so the
  differential is constructed for an arbitrary exterior algebra of `Ω` and specializes to the
  chosen one. The single universe `u` is the one `SheafOfModules.TensorExteriorSymmetricAlgebras`
  is stated at; nothing is narrowed. `PresheafOfModules.extPow`'s module universe is pinned by
  hand as `.{u, u, u, u}`, since the unifier cannot solve `max u ?a =?= u`.
* `restrictedComparison` is `(PresheafOfModules.restrictScalars _).map (exactWedgeComparison B p)`
  at an **ascribed** type whose target is spelled with the `restrictScalars (𝟙 _)` wrapper that
  `PresheafOfModules.sheafificationHomEquiv` demands.
  `PresheafOfModules.restrictScalarsCompToPresheaf` is `Iso.refl`, so the two
  local-bijectivity hypotheses of
  `Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm` are discharged by the `B`-module
  statements of `DeRhamLocalInjectivity` with no transport at all.
* **No lemma here is stated elementwise at a type mentioning a sheafification.** Writing
  `(deRhamTermIso B p).hom.val.app U (sheafifyUnit … z)` exhausts the heartbeat budget: the
  unifier must reconcile `restrictScalars (𝟙 _)` applied to a concrete `sheafification` object
  with that object itself, and the individual layers are cheap while the composite is fatal. The
  cure is that every such step is taken through a lemma whose presheaf and sheaf are
  **variables** — `AlgebraicGeometry.SheafOfModules.lift_unit_apply` and
  `PresheafOfModules.unit_naturality_apply` — instantiated inside a proof, where the type is
  computed rather than unified against an ascription.
* For the same reason the proofs below are `Eq.trans`/`congrArg` chains rather than `rw` chains.
  `rw` calls `kabstract`, which type-checks its motive at `implicit` transparency; here that
  fails on `TopCat.Sheaf CommRingCat ↑X` versus `Sheaf (Opens.grothendieckTopology ↑X) CommRingCat`
  and is reported as "did not find an occurrence of the pattern". `exact` tolerates the same
  difference, so the gluing between the two spellings is left to defeq at the application site.
* `deRhamDifferentialHom_comp_self` needs `(PresheafOfModules.sheafification _).map 0 = 0`. The
  additivity of a sheafification functor is **not** an instance, but it is one line from the
  adjunction: `CategoryTheory.Adjunction.left_adjoint_additive`, since
  `SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars _` is additive.
* `Fin.cons b c` needs its motive pinned by an ascription wherever it appears in a statement of
  this file, and the ascription must use the **same** spelling of the ring of sections as the
  lemma it will be matched against, since the motive is part of the term.

## References

* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FKG](https://stacks.math.columbia.edu/tag/0FKG)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 08TD](https://stacks.math.columbia.edu/tag/08TD)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace PresheafOfModules

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### The comparison after restriction of scalars -/

/-- The exact-wedge comparison, read as a morphism of presheaves of `A`-modules: the restriction
of scalars along `φ` of `AlgebraicGeometry.SheafOfModules.exactWedgeComparison`.

The result type is ascribed with the `PresheafOfModules.restrictScalars (𝟙 _)` wrapper that
`PresheafOfModules.sheafificationHomEquiv` puts on its target, so that no later statement has to
cross that spelling. -/
noncomputable def restrictedComparison (p : ℕ) :
    PresheafOfModules.sectionwiseForms φ.hom p ⟶
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj
          (deRhamTerm B p) :=
  (PresheafOfModules.restrictScalars (CategoryTheory.Sheaf.toRingCatMap
    (Opens.grothendieckTopology X.carrier) φ.hom)).map (exactWedgeComparison B p)

/-- Restriction of scalars does not change what the comparison does to a local section. -/
theorem restrictedComparison_app (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (z : (PresheafOfModules.extPow.{u, u, u, u} p
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)).obj U) :
    PresheafOfModules.Hom.app (restrictedComparison B p) U z =
      (exactWedgeComparison B p).app U z :=
  rfl

/-- **Sheafification commutes with restriction of scalars for the exact-wedge comparison.**
`AlgebraicGeometry.SheafOfModules.isIso_sheafificationHomEquiv_symm_exactWedgeComparison` says
that `⋀ᵖ Ω` is the sheafification of the presheaf of sectionwise exterior powers of the
sectionwise Kähler differentials *in sheaves of `B`-modules*; this says the same in sheaves of
`A`-modules.

It needs no transport: `PresheafOfModules.toPresheaf` of a restriction of scalars is the same
presheaf of abelian groups, so the local injectivity and local surjectivity of
`DeRhamLocalInjectivity` are already statements about the restricted comparison. -/
theorem isIso_restrictedComparison (p : ℕ) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).symm
        (restrictedComparison B p)) :=
  Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm _ _
    (isLocallyInjective_exactWedgeComparison B p)
    (isLocallySurjective_exactWedgeComparison B p)

/-- **`⋀ᵖ Ω`, as a sheaf of `A`-modules, is the sheafification of the presheaf of sectionwise
exterior powers of the sectionwise Kähler differentials.** -/
noncomputable def deRhamTermIso (p : ℕ) :
    (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj
        (PresheafOfModules.sectionwiseForms φ.hom p) ≅ deRhamTerm B p :=
  haveI := isIso_restrictedComparison B p
  asIso ((PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).symm (restrictedComparison B p))

/-! ### The differential -/

/-- **The degree-`p` de Rham differential**: the sheafification of the sectionwise de Rham
differential, read on `⋀ᵖ Ω` through `AlgebraicGeometry.SheafOfModules.deRhamTermIso`. -/
noncomputable def deRhamDifferentialHom (p : ℕ) : deRhamTerm B p ⟶ deRhamTerm B (p + 1) :=
  (deRhamTermIso B p).inv ≫
    (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).map
      (PresheafOfModules.sectionwiseDeRhamDifferential φ.hom p) ≫ (deRhamTermIso B (p + 1)).hom

/-- The differential is conjugate to the sheafified sectionwise differential. -/
theorem deRhamTermIso_hom_comp_deRhamDifferentialHom (p : ℕ) :
    (deRhamTermIso B p).hom ≫ deRhamDifferentialHom B p =
      (PresheafOfModules.sheafification
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).map
        (PresheafOfModules.sectionwiseDeRhamDifferential φ.hom p) ≫
          (deRhamTermIso B (p + 1)).hom :=
  (deRhamTermIso B p).hom_inv_id_assoc _

/-- **The de Rham differential computes the sectionwise one through the comparison.** On a local
section of `⋀ᵖ Ω` that comes from a local section of the sectionwise exterior powers, the
differential is the comparison of the sectionwise differential of that section.

This is the identity every property of the sectionwise differential travels along. -/
theorem deRhamDifferentialHom_app_exactWedgeComparison (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (z : (PresheafOfModules.extPow.{u, u, u, u} p
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)).obj U) :
    (deRhamDifferentialHom B p).val.app U ((exactWedgeComparison B p).app U z) =
      (exactWedgeComparison B (p + 1)).app U
        (PresheafOfModules.sectionwiseDeRhamDifferentialApp φ.hom p U z) := by
  have h1 := lift_unit_apply (Opens.grothendieckTopology X.carrier)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)
    (PresheafOfModules.sectionwiseForms φ.hom p)
    (deRhamTerm B p) (restrictedComparison B p) U z
  have h2 := lift_unit_apply (Opens.grothendieckTopology X.carrier)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)
    (PresheafOfModules.sectionwiseForms φ.hom (p + 1))
    (deRhamTerm B (p + 1)) (restrictedComparison B (p + 1)) U
    (PresheafOfModules.sectionwiseDeRhamDifferentialApp φ.hom p U z)
  have h3 := PresheafOfModules.unit_naturality_apply
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)
    (PresheafOfModules.sectionwiseDeRhamDifferential φ.hom p) U z
  have h4 := _root_.SheafOfModules.hom_congr_app_apply
    (deRhamTermIso_hom_comp_deRhamDifferentialHom B p) U
    (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).unit.app
        (PresheafOfModules.sectionwiseForms φ.hom p)) U z)
  exact ((congrArg (fun w => (deRhamDifferentialHom B p).val.app U w) h1.symm).trans h4).trans
    ((congrArg (fun w => (deRhamTermIso B (p + 1)).hom.val.app U w) h3).trans h2)

/-- **The de Rham differential squares to zero.** The sectionwise differential does, the
sheafification functor is additive, and an isomorphism cancels. -/
theorem deRhamDifferentialHom_comp_self (p : ℕ) :
    deRhamDifferentialHom B p ≫ deRhamDifferentialHom B (p + 1) = 0 := by
  let _ : (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).left_adjoint_additive
  have hzero := (congrArg (fun g => (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).map g)
    (PresheafOfModules.sectionwiseDeRhamDifferential_comp_self φ.hom p)).trans
      (Functor.map_zero _ _ _)
  refine (cancel_epi (deRhamTermIso B p).hom).1 (Eq.trans ?_ Limits.comp_zero.symm)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun h => h ≫ deRhamDifferentialHom B (p + 1))
    (deRhamTermIso_hom_comp_deRhamDifferentialHom B p)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun h => (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).map
        (PresheafOfModules.sectionwiseDeRhamDifferential φ.hom p) ≫ h)
    (deRhamTermIso_hom_comp_deRhamDifferentialHom B (p + 1))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact Eq.trans (congrArg (fun h => h ≫ (deRhamTermIso B (p + 1 + 1)).hom)
    ((Functor.map_comp _ _ _).symm.trans hzero)) Limits.zero_comp

/-! ### Exact wedges are comparisons of wedges of exact sectionwise differentials -/

/-- **The comparison carries the wedge of the exact sectionwise differentials of `c₀, …, c_{p-1}`
to the ordered product of the degree-one generators.** This is the computation inside
`AlgebraicGeometry.SheafOfModules.isExactWedge_exactWedgeComparison`, recorded as an equation:
the first factor of the comparison carries the wedge to the wedge of the universal differentials
and the second carries that to the ordered product, by the defining equation of the comparison
morphism of Tag 01CG. -/
theorem exactWedgeComparison_app_ιMulti_d (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (c : Fin p → X.sheaf.obj.obj U) :
    (exactWedgeComparison B p).app U
        ((PresheafOfModules.extPowSections.{u, u, u, u} p
            (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)
              U).symm
          (exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
            fun i =>
              (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ.hom).d (c i))) =
      B.exterior.toPresheafGradedAlgebra.homogeneousProd U p fun i => exactOne B U (c i) := by
  have h1 : PresheafOfModules.extPowSections.{u, u, u, u} p
      (moduleOfDifferentials.{u, u, u} φ).val U
      ((PresheafOfModules.extPowMap.{u, u, u, u} p (toModuleOfDifferentials φ)).app U
        ((PresheafOfModules.extPowSections.{u, u, u, u} p
            (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)
              U).symm
          (exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
            fun i =>
              (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ.hom).d (c i)))) =
      exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
        fun i => (universalDerivation.{u, u, u} φ).d (c i) := by
    refine Subtype.ext ?_
    refine Eq.trans (PresheafOfModules.extPowMap_app_ιMulti.{u, u, u, u} p
      (toModuleOfDifferentials φ) U
      (fun i => (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ.hom).d (c i))
        _ ?_) ?_
    · exact exteriorPower.ιMulti_apply_coe _ p _
    · refine Eq.trans ?_ (exteriorPower.ιMulti_apply_coe _ p _).symm
      exact congrArg (ExteriorAlgebra.ιMulti _ p)
        (funext fun i => toModuleOfDifferentials_d U (c i))
  have h2 := Stacks.GradedAlgebra.extCmpSections_ιMulti B.exterior.toPresheafGradedAlgebra
    B.exteriorGenerator.val (fun Y x => B.squareZero_exteriorGenerator Y x) p U
    (fun i => (universalDerivation.{u, u, u} φ).d (c i))
  exact (congrArg (fun z => B.exterior.toPresheafGradedAlgebra.extCmpSections
    B.exteriorGenerator.val (fun Y x => B.squareZero_exteriorGenerator Y x) p U z) h1).trans h2

/-- **An exact wedge is an ordered product of exact differentials**: the converse of
`AlgebraicGeometry.SheafOfModules.isExactWedge_homogeneousProdLeft`.

`AlgebraicGeometry.SheafOfModules.IsExactWedge` is a recursion whose step carries a degree
transport, so the induction is the same `Stacks.heq_degCast` step read backwards. -/
theorem exists_eq_homogeneousProdLeft (U : (Opens X.carrier)ᵒᵖ) (p : ℕ) :
    ∀ ω : (B.exteriorPower p).val.obj U, IsExactWedge B U p ω →
      ∃ c : Fin p → X.sheaf.obj.obj U, ω =
        B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p
          fun i => exactOne B U (c i) := by
  induction p with
  | zero => exact fun ω hω => ⟨Fin.elim0, hω⟩
  | succ p ih =>
      rintro ω ⟨b, η, hη, hheq⟩
      obtain ⟨c, rfl⟩ := ih η hη
      exact ⟨Fin.cons b c, eq_of_heq (HEq.symm ((Stacks.heq_degCast _ _).trans hheq.symm))⟩

/-- **The de Rham rule.** On a multiple of an exact wedge the differential is the wedge of the
exact differentials of all the factors.

The exact wedge is an ordered product of exact differentials, hence — on the nose, not merely
locally — the comparison of a wedge of exact sectionwise differentials; the differential computes
the sectionwise one there, and the sectionwise de Rham rule
`PresheafOfModules.sectionwiseDeRhamDifferentialApp_smul_ιMulti_d` finishes it. -/
theorem deRhamDifferentialHom_generator (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (hω : IsExactWedge B U p ω) :
    HEq ((deRhamDifferentialHom B p).val.app U (b • ω))
      ((B.exterior.mul 1 (p : ℤ)).app U (exactOne B U b) ω) := by
  obtain ⟨c, rfl⟩ := exists_eq_homogeneousProdLeft B U p ω hω
  have hD := PresheafOfModules.sectionwiseDeRhamDifferentialApp_smul_ιMulti_d φ.hom p U
    (Fin.cons b c)
  have hz := exactWedgeComparison_app_ιMulti_d B p U c
  have hz1 := exactWedgeComparison_app_ιMulti_d B (p + 1) U (Fin.cons b c)
  have hpl := B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft_eq_homogeneousProd U p
    fun i => exactOne B U (c i)
  have hpl1 := B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft_eq_homogeneousProd U (p + 1)
    fun i => exactOne B U ((Fin.cons b c : Fin (p + 1) → X.sheaf.obj.obj U) i)
  have hkey := deRhamDifferentialHom_app_exactWedgeComparison B p U
    ((PresheafOfModules.extPowSections.{u, u, u, u} p
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom) U).symm
        (b • exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
          fun i =>
            (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ.hom).d (c i)))
  have hA := (congrArg (fun y => b • y) (hpl.trans hz.symm)).trans
    ((PresheafOfModules.app_smul (exactWedgeComparison B p) b _).symm.trans
      (congrArg (fun y => (exactWedgeComparison B p).app U y) (LinearEquiv.map_smul _ b _).symm))
  have hC := (LinearEquiv.symm_apply_apply _ _).symm.trans (congrArg (LinearEquiv.symm _) hD)
  have key := (congrArg (fun y => (deRhamDifferentialHom B p).val.app U y) hA).trans
    (hkey.trans ((congrArg (fun y => (exactWedgeComparison B (p + 1)).app U y) hC).trans
      (hz1.trans hpl1.symm)))
  exact (heq_of_eq key).trans (Stacks.heq_degCast _ _)

/-! ### Tag 0FKM -/

/-- **The relative de Rham differential of `φ` exists.** The differential in each degree is the
sheafification of the ring-level de Rham differential, read on `⋀ᵖ Ω` through the exact-wedge
comparison; it squares to zero and obeys the de Rham rule because the sectionwise differential
does. -/
@[stacks 0FKM "existence: the de Rham differential exists. The tag defines the complex by a \
uniqueness property, so the covering set is this construction, `relativeDeRhamComplex` and \
`deRhamDifferential_unique`.", ega "IV 16.6.2" "existence"]
noncomputable def deRhamDifferential : DeRhamDifferential B :=
  { differential := deRhamDifferentialHom B
    squared := deRhamDifferentialHom_comp_self B
    generator := deRhamDifferentialHom_generator B }

/-- **The relative de Rham complex** `⋀⁰ Ω → ⋀¹ Ω → ⋀² Ω → ⋯` of sheaves of `A`-modules. -/
@[stacks 0FKM "the canonical complex: the de Rham complex of `B` over `A`, assembled from the \
differential of `deRhamDifferential`. Its terms and arrows are `deRhamComplex_X` and \
`deRhamComplex_d`.", stacks 0FKQ "the morphism-of-ringed-spaces case, at `A := f⁻¹𝒪_Y`"]
noncomputable abbrev relativeDeRhamComplex :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ :=
  deRhamComplex B (deRhamDifferential B)

/-- **The relative de Rham differential is unique.** This is
`AlgebraicGeometry.SheafOfModules.DeRhamDifferential.eq` read at the constructed differential. -/
@[stacks 0FKM "uniqueness: a de Rham differential is the one constructed here, so the complex of \
Tag 0FKM is well defined. The general two-differential form is `DeRhamDifferential.eq` of \
`StacksFrontier.Topology.Sheaves.Modules.DeRhamUniqueness`.", ega "IV 16.6.2" "uniqueness"]
theorem deRhamDifferential_unique (D : DeRhamDifferential B) : D = deRhamDifferential B :=
  DeRhamDifferential.eq B D (deRhamDifferential B)

/-- Every de Rham differential assembles into the relative de Rham complex. -/
theorem deRhamComplex_eq_relativeDeRhamComplex (D : DeRhamDifferential B) :
    deRhamComplex B D = relativeDeRhamComplex B :=
  deRhamComplex_eq B D (deRhamDifferential B)

end AlgebraicGeometry.SheafOfModules

end
