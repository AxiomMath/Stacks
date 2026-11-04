module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtPowLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection
public import StacksFrontier.Topology.Sheaves.Modules.DeRham
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Stalk
import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the relative de Rham differential

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B` the
structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative differentials
and let `B` also denote a package of the three algebras of Stacks Section 17.21 for `Ω`, so that
`⋀ᵖ Ω` is available. `StacksFrontier.Topology.Sheaves.Modules.DeRham` defines a *de Rham
differential* on the exterior powers of `Ω` and proves that two of them agree in every degree in
which the **exact wedges** `d b₁ ∧ ⋯ ∧ d bₚ` generate `⋀ᵖ Ω` locally, a hypothesis it names
`LocallyGeneratedByExactWedges` and discharges only in degree zero.

This file discharges it **in every degree**, and so proves that the de Rham differential is
unique. The argument is a chain of three local surjections, all of them of presheaves of
`B`-modules on the open-cover site:

`⋀ᵖ(Ω_{B(U)/A(U)}) ⟶ ⋀ᵖ(Ω(U)) ⟶ (⋀ᵖ Ω)(U)`,

where the first map is `PresheafOfModules.extPowMap` applied to the canonical morphism from the
presheaf of sectionwise Kähler differentials to its associated sheaf, and the second is the
comparison morphism of Tag 01CG. The composite is locally surjective, and on the source the
elements `b₀ · (D b₁ ∧ ⋯ ∧ D bₚ)` span over `B(U)` because the exact differentials span the
sectionwise Kähler differentials — so every local section of `⋀ᵖ Ω` is, locally, a `B`-linear
combination of multiples of exact wedges, which is exactly `LocallyGeneratedByExactWedges`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.toModuleOfDifferentials`: the canonical morphism from the
  presheaf of sectionwise Kähler differentials of `φ` to the sheaf of relative differentials,
  namely the unit of sheafification followed by
  `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise`.
* `AlgebraicGeometry.SheafOfModules.extPowComparison`: the comparison morphism of Tag 01CG at the
  exterior algebra of the chosen package, `⋀ᵖ(Ω(U)) ⟶ (⋀ᵖ Ω)(U)`.
* `AlgebraicGeometry.SheafOfModules.exactWedgeComparison`: the composite of the two, from the
  presheaf of sectionwise exterior powers of the sectionwise Kähler differentials.

## Main results

* `CommRingCat.KaehlerDifferential.span_range_d`: the exact differentials span the module of
  Kähler differentials of a morphism of commutative rings.
* `AlgebraicGeometry.SheafOfModules.toModuleOfDifferentials_d`: the comparison carries the
  sectionwise differential of a local section to its universal differential. This is what makes
  the chain land on *exact* wedges rather than on arbitrary ones.
* `AlgebraicGeometry.SheafOfModules.mem_imageSieve_toModuleOfDifferentials`,
  `mem_imageSieve_extPowComparison`, `mem_imageSieve_exactWedgeComparison`: the three local
  surjectivity statements.
* `AlgebraicGeometry.SheafOfModules.isExactWedge_exactWedgeComparison`: the composite carries a
  wedge of exact sectionwise differentials to an exact wedge.
* `AlgebraicGeometry.SheafOfModules.locallyGeneratedByExactWedges`: **the exact wedges generate
  `⋀ᵖ Ω` locally in every degree.**
* `AlgebraicGeometry.SheafOfModules.DeRhamDifferential.eq` and the `Subsingleton` instance:
  **any two de Rham differentials are equal**, unconditionally.
* `AlgebraicGeometry.SheafOfModules.deRhamComplex_eq`: **the relative de Rham complex does not
  depend on the differential it is built from.**

## Implementation notes

What is forced and what is chosen.

* The single universe `u` is the one `SheafOfModules.TensorExteriorSymmetricAlgebras` and
  `AlgebraicGeometry.SheafOfModules.DeRham` are stated at; nothing is narrowed here.
  `PresheafOfModules.extPow` and its relatives are stated at a module universe `max w a`, and the
  unifier cannot solve `max u ?a =?= u`, so every use below carries explicit universe arguments.
  This is the recorded diagnosis that a universe appearing only as a parameter the statements
  carry is harmless, whereas one *computed* into a `max` must be pinned by hand.
* The package of algebras is a **hypothesis**, as in `DeRham`, so uniqueness is proved for an
  arbitrary exterior algebra of `Ω` and specializes to the chosen one.
* `AlgebraicGeometry.SheafOfModules.toModuleOfDifferentials` is a `def` with an **ascribed**
  result type, landing in `(moduleOfDifferentials φ).val`, not in the `sheafifyRestrict` spelling
  the sheafification unit natively has. That ascription is load-bearing: the two differ by
  `PresheafOfModules.restrictScalars (𝟙 _)`, and a type ascription on a term does not retype it.
  For the same reason `Stacks.liftSieve_mem` is applied with its scalar morphism `α` named
  explicitly — left to unification it poses `max`-constrained metavariables under a structure
  projection and exhausts the `whnf` budget.
* Local surjectivity is taken and produced in the `CategoryTheory.Presheaf.imageSieve` form with
  explicit hypotheses rather than as `Presheaf.IsLocallySurjective` instances, for the reason
  recorded in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtPowLocallySurjective`.
* `AlgebraicGeometry.SheafOfModules.span_range_derivation_sectionwise` restates
  `CommRingCat.KaehlerDifferential.span_range_d` with the ring spelled
  `(B.obj ⋙ forget₂ CommRingCat RingCat).obj U` instead of `B.obj.obj U`. The two are the same
  type, but `Submodule.span` records the ring syntactically and the spanning lemma of the
  exterior power is applied at the former, so the two statements are not interchangeable by
  `rw`.

**No `@[stacks 0FKM]` attribute.** Tag 0FKM asserts that the de Rham differential *exists* and is
*unique*. Uniqueness is proved here, unconditionally; existence is not, and the tag is not placed
on half of its content. What existence still needs, beyond this file: the ring-level
`KaehlerDifferential.deRhamDifferential` assembled into a morphism of presheaves of `A`-modules
`⋀ᵖ(Ω_{B(U)/A(U)}) ⟶ ⋀ᵖ⁺¹(Ω_{B(U)/A(U)})` — its compatibility with the restriction maps follows
from the generator rule and `KaehlerDifferential.deRhamDifferential_unique`, but is nowhere in
the tree — and then a descent of that morphism along `exactWedgeComparison`, which needs that
comparison to be locally *injective* as well. Local injectivity does not follow from the spanning
argument used here; the route to it is to observe that
`SheafOfModules.sectionwiseExteriorAlgebra J (𝟙 B.obj) (relativeDifferentials' φ.hom)` is an
exterior algebra of the sheafification of `relativeDifferentials' φ.hom`, hence of `Ω`, so that
`exactWedgeComparison` is a sheafification unit followed by a degreewise isomorphism — the
statement `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp` proves for the sections of a sheaf of
modules and which is needed here for a presheaf that is not of that form.

## References

* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FKG](https://stacks.math.columbia.edu/tag/0FKG)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace PresheafOfModules

universe u

namespace CommRingCat.KaehlerDifferential

/-- **The exact differentials span the module of Kähler differentials** of a morphism of
commutative rings. This is `KaehlerDifferential.span_range_derivation` read through the algebra
structure that `CommRingCat.KaehlerDifferential` installs on its target. -/
theorem span_range_d {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Submodule.span S (Set.range (fun b : S => KaehlerDifferential.d (f := f) b)) = ⊤ := by
  let := f.hom.toAlgebra
  exact _root_.KaehlerDifferential.span_range_derivation R S

end CommRingCat.KaehlerDifferential

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}

/-! ### From the sectionwise Kähler differentials to the sheaf of relative differentials -/

/-- The canonical morphism from the presheaf of sectionwise Kähler differentials to the sheaf of
relative differentials: the unit of sheafification, followed by the identification of the
sheafified sectionwise differentials with the representing object. -/
noncomputable def toModuleOfDifferentials (φ : A ⟶ X.sheaf) :
    DifferentialsConstruction.relativeDifferentials' φ.hom ⟶
      (moduleOfDifferentials.{u, u, u} φ).val :=
  toSectionwiseDifferentialsSheaf.{u, u} φ ≫
    (moduleOfDifferentialsIsoSectionwise.{u, u} φ).inv.val

/-- The comparison carries the sectionwise differential of a local section of the target ring to
its universal differential. -/
theorem toModuleOfDifferentials_d (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    (toModuleOfDifferentials φ).app U
        ((DifferentialsConstruction.derivation' φ.hom).d b) =
      (universalDerivation.{u, u, u} φ).d b := by
  have h := moduleOfDifferentialsIsoSectionwise_hom_app_d.{u, u} φ U b
  have h2 := _root_.SheafOfModules.iso_inv_hom_app_apply
    (moduleOfDifferentialsIsoSectionwise.{u, u} φ) U ((universalDerivation.{u, u, u} φ).d b)
  show (moduleOfDifferentialsIsoSectionwise.{u, u} φ).inv.val.app U
    ((toSectionwiseDifferentialsSheaf.{u, u} φ).app U
      ((DifferentialsConstruction.derivation' φ.hom).d b)) = _
  rw [← h]
  exact h2

/-- An isomorphism of sheaves of modules is surjective on sections. -/
private theorem exists_hom_app_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : _root_.SheafOfModules R} (e : M ≅ N) (V : Cᵒᵖ) (y : N.val.obj V) :
    ∃ z, e.hom.val.app V z = y :=
  ⟨e.inv.val.app V y, _root_.SheafOfModules.hom_congr_app_apply e.inv_hom_id V y⟩

/-- The comparison is locally surjective: it is a sheafification unit followed by an
isomorphism. -/
theorem mem_imageSieve_toModuleOfDifferentials (U : (Opens X.carrier)ᵒᵖ)
    (y : (moduleOfDifferentials.{u, u, u} φ).val.obj U) :
    Presheaf.imageSieve ((toPresheaf _).map (toModuleOfDifferentials φ)) y ∈
      Opens.grothendieckTopology X.carrier U.unop := by
  refine mem_imageSieve_comp _ _ _ ?_ ?_ U y
  · exact fun V z => Stacks.liftSieve_mem
      (α := 𝟙 (underlyingRingSheaf.{u, u} X.sheaf).obj)
      (DifferentialsConstruction.relativeDifferentials' φ.hom) z
  · exact mem_imageSieve_of_surjective _ _ fun V z =>
      exists_hom_app_eq (moduleOfDifferentialsIsoSectionwise.{u, u} φ).symm V z

/-- The exact sectionwise differentials span the sectionwise Kähler differentials, with the ring
spelled as the underlying presheaf of rings of the target. -/
theorem span_range_derivation_sectionwise (U : (Opens X.carrier)ᵒᵖ) :
    Submodule.span ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
      (Set.range (fun b : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U =>
        (DifferentialsConstruction.derivation' φ.hom).d b)) = ⊤ :=
  CommRingCat.KaehlerDifferential.span_range_d (φ.hom.app U)

/-! ### The comparison with the exterior powers -/

variable (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- The comparison morphism of Tag 01CG at the exterior algebra of the chosen package: the
presheaf of sectionwise exterior powers of the sections of `Ω` maps to `⋀ᵖ Ω` by wedging
together the degree-one generators. -/
noncomputable def extPowComparison (p : ℕ) :
    PresheafOfModules.extPow.{u, u, u, u} p (moduleOfDifferentials.{u, u, u} φ).val ⟶
      (B.exteriorPower p).val :=
  B.exterior.extPowCmp
    (hO := (CategoryTheory.Sheaf.toRingCat
      (Opens.grothendieckTopology X.carrier) X.sheaf).property)
    B.exteriorGenerator B.squareZero_exteriorGenerator p

/-- The comparison morphism factors as the sheafification unit followed by a degreewise
isomorphism. -/
theorem extPowComparison_eq (p : ℕ) :
    extPowComparison B p =
      PresheafOfModules.sheafifyUnit
          (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology X.carrier)
            (𝟙 X.sheaf.obj))
          (PresheafOfModules.extPow.{u, u, u, u} p (moduleOfDifferentials.{u, u, u} φ).val) ≫
        (_root_.SheafOfModules.forget
            (CategoryTheory.Sheaf.toRingCat
              (Opens.grothendieckTopology X.carrier) X.sheaf)).map
          (_root_.SheafOfModules.exteriorPieceIso (moduleOfDifferentials.{u, u, u} φ) B.exterior
            B.exteriorGenerator B.exterior_isExteriorAlgebra (p : ℤ)).hom :=
  _root_.SheafOfModules.extPowCmp_eq_sheafifyUnit_comp _ _ _ B.squareZero_exteriorGenerator
    B.exterior_isExteriorAlgebra p

/-- The comparison morphism of Tag 01CG is locally surjective. -/
theorem mem_imageSieve_extPowComparison (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ξ : (B.exteriorPower p).val.obj U) :
    Presheaf.imageSieve ((toPresheaf _).map (extPowComparison B p)) ξ ∈
      Opens.grothendieckTopology X.carrier U.unop := by
  rw [extPowComparison_eq]
  refine mem_imageSieve_comp _ _ _ ?_ ?_ U ξ
  · exact fun V z => Stacks.liftSieve_mem
      (α := CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology X.carrier)
        (𝟙 X.sheaf.obj))
      (PresheafOfModules.extPow.{u, u, u, u} p (moduleOfDifferentials.{u, u, u} φ).val) z
  · exact mem_imageSieve_of_surjective _ _ fun V z =>
      exists_hom_app_eq (_root_.SheafOfModules.exteriorPieceIso
        (moduleOfDifferentials.{u, u, u} φ) B.exterior B.exteriorGenerator
        B.exterior_isExteriorAlgebra (p : ℤ)) V z

/-- The comparison morphism from the presheaf of sectionwise exterior powers of the **sectionwise
Kähler differentials** to the exterior powers of the sheaf of relative differentials. On this
source the wedges of exact differentials span. -/
noncomputable def exactWedgeComparison (p : ℕ) :
    PresheafOfModules.extPow.{u, u, u, u} p
        (DifferentialsConstruction.relativeDifferentials' φ.hom) ⟶ (B.exteriorPower p).val :=
  PresheafOfModules.extPowMap.{u, u, u, u} p (toModuleOfDifferentials φ) ≫ extPowComparison B p

/-- The comparison morphism `exactWedgeComparison B p` is locally surjective: the image sieve of
every local section of `⋀ᵖ Ω` is a covering sieve. -/
theorem mem_imageSieve_exactWedgeComparison (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ξ : (B.exteriorPower p).val.obj U) :
    Presheaf.imageSieve ((toPresheaf _).map (exactWedgeComparison B p)) ξ ∈
      Opens.grothendieckTopology X.carrier U.unop :=
  mem_imageSieve_comp _ _ _
    (imageSieve_extPowMap_mem _ (toModuleOfDifferentials φ) p
      mem_imageSieve_toModuleOfDifferentials)
    (mem_imageSieve_extPowComparison B p) U ξ

/-- **The comparison morphism carries a wedge of exact sectionwise differentials to an exact
wedge.** The first factor carries it to the wedge of the universal differentials, by
`toModuleOfDifferentials_d`; the second carries that to the ordered product of the degree-one
generators, by the defining equation of the comparison of Tag 01CG; and that ordered product is
an exact wedge. -/
theorem isExactWedge_exactWedgeComparison (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (c : Fin p → X.sheaf.obj.obj U) :
    IsExactWedge B U p ((exactWedgeComparison B p).app U
      ((PresheafOfModules.extPowSections.{u, u, u, u} p
          (DifferentialsConstruction.relativeDifferentials' φ.hom) U).symm
        (exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
          fun i => (DifferentialsConstruction.derivation' φ.hom).d (c i)))) := by
  have h1 : PresheafOfModules.extPowSections.{u, u, u, u} p
      (moduleOfDifferentials.{u, u, u} φ).val U
      ((PresheafOfModules.extPowMap.{u, u, u, u} p (toModuleOfDifferentials φ)).app U
        ((PresheafOfModules.extPowSections.{u, u, u, u} p
            (DifferentialsConstruction.relativeDifferentials' φ.hom) U).symm
          (exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
            fun i => (DifferentialsConstruction.derivation' φ.hom).d (c i)))) =
      exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
        fun i => (universalDerivation.{u, u, u} φ).d (c i) := by
    refine Subtype.ext ?_
    refine Eq.trans (PresheafOfModules.extPowMap_app_ιMulti.{u, u, u, u} p
      (toModuleOfDifferentials φ) U
      (fun i => (DifferentialsConstruction.derivation' φ.hom).d (c i)) _ ?_) ?_
    · exact exteriorPower.ιMulti_apply_coe _ p _
    · refine Eq.trans ?_ (exteriorPower.ιMulti_apply_coe _ p _).symm
      exact congrArg (ExteriorAlgebra.ιMulti _ p)
        (funext fun i => toModuleOfDifferentials_d U (c i))
  have h2 := Stacks.GradedAlgebra.extCmpSections_ιMulti B.exterior.toPresheafGradedAlgebra
    B.exteriorGenerator.val (fun Y x => B.squareZero_exteriorGenerator Y x) p U
    (fun i => (universalDerivation.{u, u, u} φ).d (c i))
  have h3 := isExactWedge_homogeneousProdLeft B U p c
  rw [B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft_eq_homogeneousProd U p] at h3
  rw [show (exactWedgeComparison B p).app U
        ((PresheafOfModules.extPowSections.{u, u, u, u} p
            (DifferentialsConstruction.relativeDifferentials' φ.hom) U).symm
          (exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) p
            fun i => (DifferentialsConstruction.derivation' φ.hom).d (c i))) =
      B.exterior.toPresheafGradedAlgebra.homogeneousProd U p fun i => exactOne B U (c i) from
    (congrArg (fun z => B.exterior.toPresheafGradedAlgebra.extCmpSections
      B.exteriorGenerator.val (fun Y x => B.squareZero_exteriorGenerator Y x) p U z) h1).trans h2]
  exact h3

/-! ### Local generation by exact wedges, and uniqueness -/

/-- The subgroup generated by the multiples of the exact wedges is stable under the action of the
target ring: a multiple of a multiple of an exact wedge is again one. -/
theorem smul_mem_exactWedgeSubgroup {p : ℕ} {U : (Opens X.carrier)ᵒᵖ} (r : X.sheaf.obj.obj U)
    {η : (B.exteriorPower p).val.obj U} (hη : η ∈ exactWedgeSubgroup B U p) :
    r • η ∈ exactWedgeSubgroup B U p := by
  refine (AddSubgroup.closure_le ((exactWedgeSubgroup B U p).comap
    (AddMonoidHom.mk' (fun x => r • x) (smul_add r)))).2 ?_ hη
  rintro ζ ⟨b, ω, hω, rfl⟩
  exact AddSubgroup.subset_closure ⟨r * b, ω, hω, (mul_smul r b ω).symm⟩

/-- **The exact wedges generate `⋀ᵖ Ω` locally, in every degree.** Every local section of `⋀ᵖ Ω`
lifts, on a covering sieve, to a section of the presheaf of sectionwise exterior powers of the
sectionwise Kähler differentials; there the wedges of exact differentials span over the target
ring, and the comparison carries those to exact wedges. -/
theorem locallyGeneratedByExactWedges (p : ℕ) : LocallyGeneratedByExactWedges B p := by
  intro U ξ
  refine ⟨Presheaf.imageSieve ((toPresheaf _).map (exactWedgeComparison B p)) ξ,
    mem_imageSieve_exactWedgeComparison B p U ξ, fun V f hf => ?_⟩
  obtain ⟨z, hz⟩ := exists_app_eq_of_mem_imageSieve (exactWedgeComparison B p) ξ f hf
  rw [← hz]
  have hspan : ∀ t ∈ Submodule.span ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      (Set.range fun c : Fin p → (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V) =>
        exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) p
          fun i => (DifferentialsConstruction.derivation' φ.hom).d (c i)),
      (exactWedgeComparison B p).app (op V)
          ((PresheafOfModules.extPowSections.{u, u, u, u} p
            (DifferentialsConstruction.relativeDifferentials' φ.hom) (op V)).symm t) ∈
        exactWedgeSubgroup B (op V) p := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨c, rfl⟩ := hw
        exact AddSubgroup.subset_closure
          ⟨1, _, isExactWedge_exactWedgeComparison B p (op V) c, (one_smul _ _).symm⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | smul r a _ ha =>
        rw [LinearEquiv.map_smul, app_smul]
        exact smul_mem_exactWedgeSubgroup B r ha
  have htop := Crystalline.span_range_ιMulti_eq_top
    (fun b : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V) =>
      (DifferentialsConstruction.derivation' φ.hom).d b)
    (span_range_derivation_sectionwise (op V)) p
  have h := hspan (PresheafOfModules.extPowSections.{u, u, u, u} p
    (DifferentialsConstruction.relativeDifferentials' φ.hom) (op V) z)
    (htop.ge Submodule.mem_top)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- **The relative de Rham differential is unique.** Two square-zero differentials on the
exterior powers of `Ω` obeying the de Rham rule on exact wedges are equal, with no hypothesis:
the rule prescribes them on a family of local sections that generates every `⋀ᵖ Ω` locally, and
the targets are sheaves. -/
theorem DeRhamDifferential.eq (D D' : DeRhamDifferential B) : D = D' :=
  DeRhamDifferential.eq_of_locallyGeneratedByExactWedges B (locallyGeneratedByExactWedges B) D D'

/-- There is at most one relative de Rham differential. -/
instance : Subsingleton (DeRhamDifferential B) :=
  ⟨DeRhamDifferential.eq B⟩

/-- **The relative de Rham complex does not depend on the differential** it is assembled from. -/
theorem deRhamComplex_eq (D D' : DeRhamDifferential B) : deRhamComplex B D = deRhamComplex B D' :=
  deRhamComplex_eq_of_locallyGeneratedByExactWedges B (locallyGeneratedByExactWedges B) D D'

end AlgebraicGeometry.SheafOfModules

end
