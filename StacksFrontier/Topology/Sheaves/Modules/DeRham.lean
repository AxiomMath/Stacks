module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.HomogeneousProdLeft
public import StacksFrontier.Topology.Sheaves.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# The relative de Rham complex of sheaves of rings

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B`
the structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative
differentials of `φ` and let `⋀ᵖ Ω` be its exterior powers, supplied by a package of the three
algebras of Stacks Section 17.21. A *de Rham differential* is a family of morphisms of sheaves of
`A`-modules `d : ⋀ᵖ Ω ⟶ ⋀ᵖ⁺¹ Ω` which squares to zero and obeys

`d (b · d b₁ ∧ ⋯ ∧ d bₚ) = d b ∧ d b₁ ∧ ⋯ ∧ d bₚ`

on every local section of that shape. This file records that notion, the complex of sheaves of
`A`-modules a de Rham differential produces, and the identities that complex satisfies.

Everything here is stated for an **arbitrary** package `B` of the three algebras, taken as a
hypothesis, and for the sheaf of relative differentials of an arbitrary `φ`. No particular
construction of the exterior algebra is presupposed; `SheafOfModules.ringedSpaceAlgebras` is one
such package, so nothing below is vacuous.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.differentialAlgebras` and
  `AlgebraicGeometry.SheafOfModules.differentialForms`: the chosen package of the three algebras
  of the sheaf of relative differentials, and its exterior powers `Ωᵖ_{B/A}`.
* `AlgebraicGeometry.SheafOfModules.exactOne`: the degree-one differential form `d b` attached to
  a local section `b` of the target ring, read in the exterior algebra of the package.
* `AlgebraicGeometry.SheafOfModules.IsExactWedge`: a local section of `⋀ᵖ Ω` is an *exact wedge*
  if it is an ordered product `d b₁ ∧ ⋯ ∧ d bₚ` of exact differentials, the empty product being
  the unit of the exterior algebra.
* `AlgebraicGeometry.SheafOfModules.deRhamTerm`: the degree-`p` term `⋀ᵖ Ω` of the de Rham
  complex, as a sheaf of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.DeRhamDifferential`: a square-zero differential on those
  terms obeying the de Rham rule on exact wedges.
* `AlgebraicGeometry.SheafOfModules.deRhamComplex`: the cochain complex of sheaves of
  `A`-modules a de Rham differential assembles into.

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_eq_smul_one`: in degree zero every local section is a
  multiple of the unit, that is, of the unique exact wedge of degree zero.
* `AlgebraicGeometry.SheafOfModules.isExactWedge_homogeneousProdLeft`: the ordered product of
  exact differentials is an exact wedge, which is what makes `IsExactWedge` nonvacuous in every
  degree.
* `AlgebraicGeometry.SheafOfModules.DeRhamDifferential.differential_zero_eq`: **the degree-zero
  differential is uniquely determined by the de Rham rule.**
* `AlgebraicGeometry.SheafOfModules.DeRhamDifferential.eq_of_locallyGeneratedByExactWedges`:
  **a de Rham differential is uniquely determined by the rule in every degree in which the exact
  wedges generate `⋀ᵖ Ω` locally.**
* `AlgebraicGeometry.SheafOfModules.deRhamComplex_X`,
  `AlgebraicGeometry.SheafOfModules.deRhamComplex_d`: the terms and the arrows.
* `AlgebraicGeometry.SheafOfModules.deRhamComplex_exactWedge`,
  `AlgebraicGeometry.SheafOfModules.deRhamComplex_degreeZero` and
  `AlgebraicGeometry.SheafOfModules.deRhamComplex_degreeZero_apply`: the de Rham rule read on the
  arrows of the complex, and its degree-zero form, which identifies the first arrow with the
  universal relative derivation.
* `AlgebraicGeometry.SheafOfModules.deRhamComplex_eq_of_locallyGeneratedByExactWedges`: under the
  same local generation hypothesis, the complex does not depend on the differential chosen.

## Implementation notes

What is forced and what is chosen.

* The single universe `u` carrying the space, the sections of the two rings and the sections of
  every module is the one `SheafOfModules.TensorExteriorSymmetricAlgebras` is stated at, and that
  in turn is the universe of `RingedSpace.{u, u}`. `moduleOfDifferentials` does allow a larger
  coefficient universe, but the exterior powers of its value are only available at the equal
  universes, so nothing is narrowed by instantiating it there.
* The package of algebras is a **hypothesis**, not `SheafOfModules.ringedSpaceAlgebras`. Every
  statement below is therefore about an arbitrary exterior algebra of `Ω` and specializes to the
  chosen one; this is also what keeps the file independent of which construction of the exterior
  algebra is in use.
* The terms are sheaves of `A`-modules and not of `B`-modules, because a de Rham differential is
  only `A`-linear: already in degree zero the Leibniz rule gives `d (b b') = b d b' + b' d b`.
  The restriction of scalars is along `underlyingRingHom`, the ring-sheaf morphism underlying
  `φ`.
* `IsExactWedge` and `DeRhamDifferential.generator` are stated with `HEq` because the product of
  a degree-one and a degree-`p` section lands in degree `1 + (p : ℤ)`, which is only
  propositionally `((p + 1 : ℕ) : ℤ)`. The same transport is packaged as
  `Stacks.GradedAlgebra.homogeneousProdLeft`, and `isExactWedge_homogeneousProdLeft` is the
  bridge between the two presentations.
* `exists_eq_smul_one` is the degree-zero case of the local generation of `⋀ᵖ Ω` by exact wedges,
  and it is unconditional: the degree-zero piece of an exterior algebra is free of rank one on
  the unit. In higher degrees local generation is a genuine statement about the sheafification of
  the sectionwise exterior powers, which is why
  `DeRhamDifferential.eq_of_locallyGeneratedByExactWedges` takes it as a hypothesis in the shape
  `LocallyGeneratedByExactWedges`.
* No `@[stacks 0FKM]` attribute. Tag 0FKM asserts that the de Rham differential *exists* and is
  *unique*; neither is proved here. What is proved is the complex a differential gives rise to,
  the identities it satisfies, and uniqueness in degree zero and, conditionally on
  `LocallyGeneratedByExactWedges`, in every degree. Both of the inputs this file once listed as
  owed have since been supplied elsewhere: `LocallyGeneratedByExactWedges` is unconditional in
  every degree by `AlgebraicGeometry.SheafOfModules.locallyGeneratedByExactWedges`
  (`DeRhamUniqueness.lean`), and existence and uniqueness of the de Rham differential are proved
  and carry `@[stacks 0FKM]` in `DeRhamExistence.lean`. This file is the unconditional core they
  are built on, and it keeps no 0FKM attribute of its own.

## References

* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FKG](https://stacks.math.columbia.edu/tag/0FKG)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}

/-- The **chosen** package of the tensor, exterior and symmetric algebras of the sheaf of
relative differentials of `φ`. Every statement below is proved for an arbitrary package and so
holds for this one; it is recorded because it is what makes the de Rham complex of a *given*
`φ` an object rather than a family depending on a choice of exterior algebra. -/
noncomputable def differentialAlgebras (φ : A ⟶ X.sheaf) :
    _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ) :=
  _root_.SheafOfModules.ringedSpaceAlgebras X (moduleOfDifferentials.{u, u, u} φ)

/-- The sheaf `Ωᵖ_{B/A} = ⋀ᵖ Ω` of relative differential forms of degree `p`, for the chosen
package of algebras. -/
noncomputable abbrev differentialForms (φ : A ⟶ X.sheaf) (p : ℕ) :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) :=
  (differentialAlgebras φ).exteriorPower p

variable (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- The degree-one exterior-algebra section `d b` attached to a local section `b` of the target
ring: the image under the degree-one generator of the package of the universal relative
differential of `b`. -/
noncomputable def exactOne (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    (B.exteriorPower 1).val.obj U :=
  B.exteriorGenerator.val.app U (((universalDerivation.{u, u, u} φ).app U).d b)

/-- A local section of `⋀ᵖ Ω` is an **exact wedge** if it is an ordered product
`d b₁ ∧ ⋯ ∧ d bₚ` of exact differentials. The empty product is the unit of the exterior algebra,
and the product recurses on the left, so a degree transport is part of the statement. -/
def IsExactWedge (U : (Opens X.carrier)ᵒᵖ) :
    (p : ℕ) → (B.exteriorPower p).val.obj U → Prop
  | 0, ω => ω = B.exterior.one.eval U
  | p + 1, ω =>
      ∃ (b : X.sheaf.obj.obj U) (η : (B.exteriorPower p).val.obj U),
        IsExactWedge U p η ∧
          HEq ω ((B.exterior.mul 1 (p : ℤ)).app U (exactOne B U b) η)

/-- The morphism of sheaves of rings underlying `φ`, used to regard a sheaf of `B`-modules as a
sheaf of `A`-modules. -/
noncomputable abbrev underlyingRingHom :
    Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf :=
  { hom := Functor.whiskerRight φ.hom (forget₂ CommRingCat.{u} RingCat.{u}) }

/-- The degree-`p` term `⋀ᵖ Ω` of the relative de Rham complex, as a sheaf of `A`-modules. -/
noncomputable abbrev deRhamTerm (p : ℕ) :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A) :=
  (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj (B.exteriorPower p)

/-- A **de Rham differential** on the exterior powers of the sheaf of relative differentials: a
square-zero family of morphisms of sheaves of `A`-modules obeying
`d (b · d b₁ ∧ ⋯ ∧ d bₚ) = d b ∧ d b₁ ∧ ⋯ ∧ d bₚ` on every local section of that shape. -/
@[ext]
structure DeRhamDifferential where
  /-- The differential in each degree, `A`-linear but in general not `B`-linear. -/
  differential (p : ℕ) : deRhamTerm B p ⟶ deRhamTerm B (p + 1)
  /-- Consecutive differentials compose to zero. -/
  squared (p : ℕ) : differential p ≫ differential (p + 1) = 0
  /-- The de Rham rule on a multiple of an exact wedge. -/
  generator (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
      (b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
      (hω : IsExactWedge B U p ω) :
    HEq ((differential p).val.app U (b • ω))
      ((B.exterior.mul 1 (p : ℤ)).app U (exactOne B U b) ω)

/-! ### Exact wedges -/

/-- The ordered product on the left of the exact differentials of `c₀, …, c_{p-1}` is an exact
wedge. This is what makes `IsExactWedge` nonvacuous in every degree, and it is the bridge
between the `HEq` presentation of `IsExactWedge` and the degree transport packaged as
`Stacks.GradedAlgebra.homogeneousProdLeft`. -/
theorem isExactWedge_homogeneousProdLeft (U : (Opens X.carrier)ᵒᵖ) (p : ℕ)
    (c : Fin p → X.sheaf.obj.obj U) :
    IsExactWedge B U p
      (B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p fun i => exactOne B U (c i)) := by
  induction p with
  | zero => rfl
  | succ p ih =>
      exact ⟨c 0, _, ih fun i => c i.succ, Stacks.heq_degCast _ _⟩

/-- In degree zero every local section of the exterior algebra is a multiple of the unit, that
is, of the unique exact wedge of degree zero. This is the degree-zero case of the local
generation of `⋀ᵖ Ω` by exact wedges, and it holds on the nose rather than locally. -/
theorem exists_eq_smul_one (U : (Opens X.carrier)ᵒᵖ) (ξ : (B.exteriorPower 0).val.obj U) :
    ∃ b : X.sheaf.obj.obj U, b • B.exterior.one.eval U = ξ :=
  B.exists_exterior_eq_smul_one U ξ

/-! ### Uniqueness -/

/-- The additive subgroup of local sections of `⋀ᵖ Ω` over `U` generated by the multiples of the
exact wedges. It is stable under the `A`-action, because an `A`-multiple of a `B`-multiple of an
exact wedge is again a `B`-multiple of it. -/
noncomputable def exactWedgeSubgroup (U : (Opens X.carrier)ᵒᵖ) (p : ℕ) :
    AddSubgroup ((B.exteriorPower p).val.obj U) :=
  AddSubgroup.closure {η | ∃ (b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U),
    IsExactWedge B U p ω ∧ η = b • ω}

/-- The exact wedges **generate `⋀ᵖ Ω` locally** in degree `p`: every local section restricts
into `exactWedgeSubgroup` along the members of some covering sieve.

This is the one input the de Rham rule needs in order to determine the differential, and it is
exactly the assertion that `⋀ᵖ Ω` is the sheafification of the presheaf of sectionwise exterior
powers of the sectionwise Kähler differentials. It holds unconditionally for `p = 0`
(`locallyGeneratedByExactWedges_zero`). -/
def LocallyGeneratedByExactWedges (p : ℕ) : Prop :=
  ∀ (U : (Opens X.carrier)ᵒᵖ) (ξ : (B.exteriorPower p).val.obj U),
    ∃ S : Sieve (unop U), S ∈ Opens.grothendieckTopology X.carrier (unop U) ∧
      ∀ ⦃V : Opens X.carrier⦄ (f : V ⟶ unop U), S f →
        (B.exteriorPower p).val.map f.op ξ ∈ exactWedgeSubgroup B (op V) p

/-- In degree zero the exact wedges generate on the nose, hence locally. -/
theorem locallyGeneratedByExactWedges_zero : LocallyGeneratedByExactWedges B 0 := by
  intro U ξ
  refine ⟨⊤, Opens.grothendieckTopology X.carrier |>.top_mem _, fun V f _ => ?_⟩
  obtain ⟨b, rfl⟩ := exists_eq_smul_one B U ξ
  refine AddSubgroup.subset_closure ⟨X.sheaf.obj.map f.op b, B.exterior.one.eval (op V), rfl, ?_⟩
  exact ((B.exteriorPower 0).val.map_smul f.op b _).trans
    (congrArg _ (B.exterior.one.property f.op))

/-- **The de Rham rule determines the differential in every degree in which the exact wedges
generate `⋀ᵖ Ω` locally.** Two de Rham differentials agree in such a degree: their difference is
additive and kills every multiple of an exact wedge, hence kills the subgroup those generate,
hence vanishes on a covering family, hence vanishes because the target is a sheaf. -/
theorem DeRhamDifferential.differential_eq_of_locallyGenerated {p : ℕ}
    (hp : LocallyGeneratedByExactWedges B p) (D D' : DeRhamDifferential B) :
    D.differential p = D'.differential p := by
  have key : ∀ (U : (Opens X.carrier)ᵒᵖ) (η : (B.exteriorPower p).val.obj U),
      η ∈ exactWedgeSubgroup B U p →
        (D.differential p).val.app U η = (D'.differential p).val.app U η := by
    intro U
    have hsub : exactWedgeSubgroup B U p ≤
        AddMonoidHom.eqLocus ((D.differential p).val.app U).hom.toAddMonoidHom
          ((D'.differential p).val.app U).hom.toAddMonoidHom := by
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro η ⟨b, ω, hω, rfl⟩
      exact eq_of_heq ((D.generator p U b ω hω).trans (D'.generator p U b ω hω).symm)
    exact fun η hη => hsub hη
  refine (_root_.SheafOfModules.forget _).map_injective
    (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun ξ => ?_))
  obtain ⟨S, hS, hcov⟩ := hp U ξ
  refine (B.exteriorPower (p + 1)).isSheaf.isSeparated (unop U) S hS _ _ fun V f hf => ?_
  exact (PresheafOfModules.naturality_apply (D.differential p).val f.op ξ).symm.trans
    ((key (op V) _ (hcov f hf)).trans
      (PresheafOfModules.naturality_apply (D'.differential p).val f.op ξ))

/-- **The degree-zero de Rham differential is uniquely determined by the de Rham rule.** In
degree zero every local section is a multiple of the unit, so the rule already prescribes the
differential on every section. -/
theorem DeRhamDifferential.differential_zero_eq (D D' : DeRhamDifferential B) :
    D.differential 0 = D'.differential 0 :=
  DeRhamDifferential.differential_eq_of_locallyGenerated B
    (locallyGeneratedByExactWedges_zero B) D D'

/-- **Two de Rham differentials agree** as soon as the exact wedges generate `⋀ᵖ Ω` locally in
every degree. -/
theorem DeRhamDifferential.eq_of_locallyGeneratedByExactWedges
    (h : ∀ p : ℕ, LocallyGeneratedByExactWedges B p) (D D' : DeRhamDifferential B) : D = D' :=
  DeRhamDifferential.ext
    (funext fun p => DeRhamDifferential.differential_eq_of_locallyGenerated B (h p) D D')

/-! ### The complex -/

/-- The relative de Rham complex `⋀⁰ Ω → ⋀¹ Ω → ⋀² Ω → ⋯` of sheaves of `A`-modules attached to
a de Rham differential. -/
noncomputable def deRhamComplex (D : DeRhamDifferential B) :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ :=
  CochainComplex.of (deRhamTerm B) D.differential D.squared

/-- The terms of the relative de Rham complex are the exterior-power sheaves, viewed as sheaves
of `A`-modules. -/
@[simp] theorem deRhamComplex_X (D : DeRhamDifferential B) (p : ℕ) :
    (deRhamComplex B D).X p = deRhamTerm B p := rfl

/-- The arrow of the relative de Rham complex out of degree `p` is the given differential. -/
@[simp] theorem deRhamComplex_d (D : DeRhamDifferential B) (p : ℕ) :
    (deRhamComplex B D).d p (p + 1) = D.differential p := by
  apply CochainComplex.of_d

/-- The de Rham rule on a multiple of an exact wedge, read on the arrows of the complex. -/
theorem deRhamComplex_exactWedge (D : DeRhamDifferential B) (p : ℕ)
    (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (hω : IsExactWedge B U p ω) :
    HEq (((deRhamComplex B D).d p (p + 1)).val.app U (b • ω))
      ((B.exterior.mul 1 (p : ℤ)).app U (exactOne B U b) ω) := by
  rw [deRhamComplex_d]
  exact D.generator p U b ω hω

/-- In degree zero the differential is the universal relative derivation, using multiplication
by the exterior-algebra unit to view a local section of the target ring as a degree-zero form. -/
theorem deRhamComplex_degreeZero (D : DeRhamDifferential B) (U : (Opens X.carrier)ᵒᵖ)
    (b : X.sheaf.obj.obj U) :
    HEq (((deRhamComplex B D).d 0 1).val.app U (b • B.exterior.one.eval U))
      (exactOne B U b) :=
  (deRhamComplex_exactWedge B D 0 U b (B.exterior.one.eval U) rfl).trans
    (B.exterior.mul_one 1 U (exactOne B U b))

/-- On every degree-zero form, the differential is the universal derivation of the corresponding
local section of the target ring. -/
theorem deRhamComplex_degreeZero_apply (D : DeRhamDifferential B) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower 0).val.obj U) :
    HEq (((deRhamComplex B D).d 0 1).val.app U ω)
      (exactOne B U (B.exteriorPieceZeroIsoUnit.hom.val.app U ω)) := by
  have h := deRhamComplex_degreeZero B D U (B.exteriorPieceZeroIsoUnit.hom.val.app U ω)
  rwa [B.exteriorPieceZeroIsoUnit_smul_one U ω _ rfl] at h

/-- **Any two de Rham differentials give the same complex**, as soon as the exact wedges generate
`⋀ᵖ Ω` locally in every degree. -/
theorem deRhamComplex_eq_of_locallyGeneratedByExactWedges
    (h : ∀ p : ℕ, LocallyGeneratedByExactWedges B p) (D D' : DeRhamDifferential B) :
    deRhamComplex B D = deRhamComplex B D' := by
  rw [DeRhamDifferential.eq_of_locallyGeneratedByExactWedges B h D D']

end AlgebraicGeometry.SheafOfModules

end
