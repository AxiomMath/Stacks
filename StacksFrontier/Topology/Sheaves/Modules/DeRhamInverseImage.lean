module

public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.Topology.Sheaves.Modules.DeRham
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamExistence
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamUniqueness
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.InverseImage
public import StacksFrontier.Topology.Sheaves.Modules.InverseImageRestrictScalars
import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image of the relative de Rham complex

Let `f : Y ⟶ X` be a continuous map of topological spaces and let `φ : 𝒜 ⟶ ℬ` be a homomorphism
of sheaves of commutative rings on `X`. Writing `Ωᵖ_{ℬ/𝒜} = ⋀ᵖ Ω_{ℬ/𝒜}` for the terms of the
relative de Rham complex, this file identifies

`f⁻¹ Ωᵖ_{ℬ/𝒜} = Ωᵖ_{f⁻¹ℬ/f⁻¹𝒜}`

in every degree, compatibly with the exterior products, the units and the degree-one generators,
and then assembles those identifications into the identification of **complexes**

`f⁻¹Ω•_{ℬ/𝒜} = Ω•_{f⁻¹ℬ/f⁻¹𝒜}`

of Tag 0FKP, together with its canonicality and its uniqueness.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.inverseImageRing` and `inverseImageRingMap`: the inverse
  images `f⁻¹𝒜` and `f⁻¹φ`, typed over the inverse-image ringed space.
* `AlgebraicGeometry.SheafOfModules.inverseImageDifferentials`: the degree-one identification
  `f⁻¹Ω_{ℬ/𝒜} = Ω_{f⁻¹ℬ/f⁻¹𝒜}` of Tag 08RR, read at the inverse-image ringed space.
* `AlgebraicGeometry.SheafOfModules.inverseImageExteriorAlgebraIso`: the canonical comparison of
  the two exterior algebras, carrying its compatibilities with the products, the units and the
  degree-one generators.
* `AlgebraicGeometry.SheafOfModules.inverseImageDifferentialForms`: **the degree-`p`
  identification `f⁻¹ Ωᵖ_{ℬ/𝒜} ≅ Ωᵖ_{f⁻¹ℬ/f⁻¹𝒜}`** of sheaves of `f⁻¹ℬ`-modules, and
  `inverseImageForm`, its value on the inverse image of a local differential form.
* `AlgebraicGeometry.SheafOfModules.inverseImageDeRhamTerm`: the same identification read in
  sheaves of `f⁻¹𝒜`-modules, that is, **of the terms of the de Rham complex**.
* `AlgebraicGeometry.SheafOfModules.inverseImageDeRhamComplex`: the termwise inverse image of
  the relative de Rham complex.
* `AlgebraicGeometry.SheafOfModules.IsCanonicalInverseImageDeRhamIso`: canonicality of an
  identification of the two complexes, namely that in every degree it carries
  `b · d b₁ ∧ ⋯ ∧ d bₚ` to `f⁻¹b · d(f⁻¹b₁) ∧ ⋯ ∧ d(f⁻¹bₚ)` on the inverse-image sections.
* `AlgebraicGeometry.SheafOfModules.inverseImageDeRhamComplexIso`: **the identification
  `f⁻¹Ω•_{ℬ/𝒜} = Ω•_{f⁻¹ℬ/f⁻¹𝒜}` of de Rham complexes.**

## Main results

* `AlgebraicGeometry.SheafOfModules.isExteriorAlgebra_inverseImageExteriorGenerator`: the exterior
  algebra of `Ω_{f⁻¹ℬ/f⁻¹𝒜}` is an exterior algebra of `f⁻¹Ω_{ℬ/𝒜}`, through the degree-one
  identification of Tag 08RR. This is what makes the comparison of Tag 01CI available, and so is
  the step that turns the degree-one statement into the statement in every degree.
* `AlgebraicGeometry.SheafOfModules.inverseImageDifferentialForms_eq`: the degreewise
  identification is the corresponding component of `inverseImageExteriorAlgebraIso`, whose
  `map_mul`, `map_one` and `map_generator` fields are the compatibilities with the exterior
  products, the degree-zero unit and the degree-one generators.
* `AlgebraicGeometry.SheafOfModules.deRhamTerm_hom_ext`: two morphisms out of `⋀ᵖ Ω` agreeing on
  the multiples of the ordered products of exact differentials are equal.
* `AlgebraicGeometry.SheafOfModules.inverseImageForm_one`,
  `inverseImageForm_smul`, `inverseImageForm_exactOne`, `inverseImageForm_mul` and
  `inverseImageForm_homogeneousProdLeft`: the identification of the terms respects the unit, the
  scalars, the exact differentials, the exterior products, and hence the ordered products
  `d b₁ ∧ ⋯ ∧ d bₚ`.
* `AlgebraicGeometry.SheafOfModules.inverseImageDeRhamTerm_comm_d`: **the identification of the
  terms commutes with the de Rham differentials.**
* `AlgebraicGeometry.SheafOfModules.inverseImageDeRhamComplexIso_canonical` and
  `inverseImageDeRhamComplexIso_unique`: **the identification of the complexes is canonical, and
  canonicality determines it.**

## Implementation notes

An arbitrary sheaf of commutative rings on a space is the structure sheaf of a ringed space, so
the target `ℬ` of `φ` is presented as `X.sheaf` for a ringed space `X`; this is what makes the
exterior powers of `Ω_{ℬ/𝒜}` available, since the package of three algebras of Stacks Section
17.21 is supplied for a sheaf of modules on a ringed space. The inverse image `f⁻¹ℬ` is the
structure sheaf of `AlgebraicGeometry.RingedSpace.inverseImage X f`, and inverse image of sheaves
of `ℬ`-modules is pullback along `AlgebraicGeometry.RingedSpace.inverseImageProjection X f`: that
morphism of ringed spaces has the unit `ℬ ⟶ f_*f⁻¹ℬ` as its structure map, so
`RingedSpaceModuleAdjunction.structureSheafHom` of it is `inverseImageRingHom` and the two
spellings of `f⁻¹` on sheaves of modules agree definitionally. This is what lets Tag 01CI, which
is stated for a morphism of ringed spaces, be applied to a bare continuous map.

**Where the two spellings are crossed.** `Y` and the carrier of the inverse-image ringed space are
definitionally equal but not syntactically so, and the sheaf of rings `f⁻¹𝒜` has to be presented
over the latter before the module-of-differentials API will accept it: otherwise the sheaf of rings
is a metavariable whose *type* mentions the unreduced carrier, and the implicit arguments of
`differentialAlgebras` cannot be solved. `inverseImageRing` is that one presentation, and
`inverseImageDifferentials` is the one crossing of the two spellings of `f⁻¹` on modules;
everything downstream speaks the ringed-space spelling and needs no further crossing.

The identification is **not** asserted to exist: it is the comparison of Tag 01CI at the two
exterior algebras. That comparison applies because `Ω_{f⁻¹ℬ/f⁻¹𝒜}` is, by the degree-one
identification of Tag 08RR, the same sheaf of modules as `f⁻¹Ω_{ℬ/𝒜}`; transporting the universal
property along that identification is `SheafOfModules.GradedAlgebra.isExteriorAlgebra_ofIso`. The
generated module, not the algebra, changes, which is why the transport is a precomposition on the
generator. Canonicality is carried by `inverseImageExteriorAlgebraIso` in the shape Tag 01CI
supplies it: compatibility with the products, the units and the degree-one generators on the
inverse-image sections, which determine the comparison because those sections generate the
inverse image locally.

**From the terms to the complexes.** The terms of the de Rham complex are sheaves of
`𝒜`-modules, obtained from `Ωᵖ_{ℬ/𝒜}` by restriction of scalars along `φ`, while the comparison
of Tag 01CI is of the exterior powers themselves, as sheaves of `f⁻¹ℬ`-modules. Two steps bridge
the gap.

* `AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsIso` moves the identification
  across the restriction of scalars; `inverseImageDeRhamTerm` is the composite.
* Compatibility with the differentials is checked on the inverse-image sections of the local
  sections `b · d b₁ ∧ ⋯ ∧ d bₚ`, which is enough: both composites are morphisms out of an
  inverse image, so they agree as soon as their transposes along `f⁻¹ ⊣ f_*` do, and those are
  morphisms out of `⋀ᵖ Ω`, which the multiples of the ordered products of exact differentials
  generate locally (`AlgebraicGeometry.SheafOfModules.locallyGeneratedByExactWedges`). On such a
  section the de Rham rule produces one more exact differential on each side, and the
  identification matches the two by its `map_one`, `map_mul` and `map_generator` fields together
  with Tag 08RR's compatibility with universal derivations
  (`inverseImageDifferentials_hom_d`).

**No degree transports.** The de Rham rule is stated on an `IsExactWedge`, whose recursion
multiplies on the left and so carries a transport along `1 + (p : ℤ) = ((p + 1 : ℕ) : ℤ)`. Every
statement here is instead phrased with `Stacks.GradedAlgebra.homogeneousProdLeft`, which keeps
that transport inside its own definition, and the induction identifying it with the
inverse-image product runs on the right-handed `Stacks.GradedAlgebra.homogeneousProd`, whose
degree `(p : ℤ) + 1` is definitionally `((p + 1 : ℕ) : ℤ)`. The bridge is
`Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`.

**Two spellings of the inverse image of an open.** `Opens.map f` lands in `Opens Y`, while the
module structures on `Ωᵖ_{f⁻¹ℬ/f⁻¹𝒜}` are registered over
`Opens (AlgebraicGeometry.RingedSpace.inverseImage X f).carrier`. The two are definitionally
equal, but instance search is syntactic and fails at the first spelling, so every statement
below uses `inverseImageOpensMap`, the second one.

**Proofs are `Eq.trans`/`congrArg` chains rather than `rw` chains**, for the reason recorded in
`StacksFrontier.Topology.Sheaves.Modules.DeRhamExistence`: `rw` type-checks its motive at
`implicit` transparency, which here fails on `TopCat.Sheaf CommRingCat ↑X` versus
`Sheaf (Opens.grothendieckTopology ↑X) CommRingCat` and is reported as a missing pattern.

## References

* [Stacks Project, Tag 0FKP](https://stacks.math.columbia.edu/tag/0FKP)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.RingedSpace Stacks.PullbackExteriorAlgebra
open SheafOfModules.GradedAlgebra

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- The inverse image `f⁻¹𝒜` of a sheaf of commutative rings along a continuous map, presented as
a sheaf of rings on the carrier of the inverse-image ringed space. -/
abbrev inverseImageRing {X : RingedSpace.{u, u}} (A : TopCat.Sheaf CommRingCat.{u} X.carrier)
    {Y : TopCat.{u}} (f : Y ⟶ X.carrier) :
    TopCat.Sheaf CommRingCat.{u} (RingedSpace.inverseImage X f).carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f).obj A

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} (φ : A ⟶ X.sheaf)
  {Y : TopCat.{u}} (f : Y ⟶ X.carrier)

/-- The inverse image `f⁻¹φ : f⁻¹𝒜 ⟶ f⁻¹ℬ` of a homomorphism of sheaves of commutative rings,
with target the structure sheaf of the inverse-image ringed space. -/
abbrev inverseImageRingMap : inverseImageRing A f ⟶ (RingedSpace.inverseImage X f).sheaf :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f).map φ

/-- **The identification `f⁻¹Ω_{ℬ/𝒜} = Ω_{f⁻¹ℬ/f⁻¹𝒜}` of Tag 08RR**, with the inverse image read
as pullback along the projection from the inverse-image ringed space. -/
def inverseImageDifferentials :
    (pullbackFunctor (RingedSpace.inverseImageProjection X f)).obj
        (moduleOfDifferentials.{u, u, u} φ) ≅
      moduleOfDifferentials.{u, u, u} (inverseImageRingMap φ f) :=
  pullbackDifferentialsIso f φ

/-- The degree-one generator of the exterior algebra of `Ω_{f⁻¹ℬ/f⁻¹𝒜}`, read on `f⁻¹Ω_{ℬ/𝒜}`
through the identification of Tag 08RR. -/
def inverseImageExteriorGenerator :
    (pullbackFunctor (RingedSpace.inverseImageProjection X f)).obj
        (moduleOfDifferentials.{u, u, u} φ) ⟶
      (differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior.piece 1 :=
  (inverseImageDifferentials φ f).hom ≫
    (differentialAlgebras.{u} (inverseImageRingMap φ f)).exteriorGenerator

/-- **The exterior algebra of `Ω_{f⁻¹ℬ/f⁻¹𝒜}` is an exterior algebra of `f⁻¹Ω_{ℬ/𝒜}`.** The two
sheaves of modules are identified by Tag 08RR, and the universal property transports along that
identification. -/
theorem isExteriorAlgebra_inverseImageExteriorGenerator :
    IsExteriorAlgebra (differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior
      (inverseImageExteriorGenerator φ f) :=
  _root_.SheafOfModules.GradedAlgebra.isExteriorAlgebra_ofIso (inverseImageDifferentials φ f)
    (differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior_isExteriorAlgebra

/-- **Stacks Project, Tag 0FKP, canonicality.** The canonical comparison between the inverse image
of the exterior algebra of `Ω_{ℬ/𝒜}` and the exterior algebra of `Ω_{f⁻¹ℬ/f⁻¹𝒜}`, in every degree
and on the underlying direct-sum sheaf, together with its compatibility with the exterior products,
the degree-zero units and the degree-one generators. Those compatibilities determine the
comparison, by `Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso_unique`. -/
@[stacks 0FKP "canonicality of the identification of the terms, as sheaves of `f⁻¹ℬ`-modules: \
the comparison is the one compatible with the exterior products, the units and the exact \
differentials, and that determines it. The complex-level statement of the tag is \
`inverseImageDeRhamComplexIso` below."]
def inverseImageExteriorAlgebraIso :
    ExteriorAlgebraPullbackIso (RingedSpace.inverseImageProjection X f)
      (differentialAlgebras.{u} φ).exterior (differentialAlgebras.{u} φ).exteriorGenerator
      (differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior
      (inverseImageExteriorGenerator φ f) :=
  exteriorAlgebraPullbackIso _ _ _ _ _ (differentialAlgebras.{u} φ).exterior_isExteriorAlgebra
    (isExteriorAlgebra_inverseImageExteriorGenerator φ f)

/-- **Stacks Project, Tag 0FKP, on the terms.** The canonical identification
`f⁻¹ Ωᵖ_{ℬ/𝒜} = Ωᵖ_{f⁻¹ℬ/f⁻¹𝒜}` of the inverse image of the sheaf of relative differential
`p`-forms with the sheaf of relative differential `p`-forms of the inverse-image rings. -/
@[stacks 0FKP "the identification of the terms: in each degree `p` the inverse image of \
`Ωᵖ_{ℬ/𝒜}` is `Ωᵖ_{f⁻¹ℬ/f⁻¹𝒜}`, as sheaves of `f⁻¹ℬ`-modules. The identification of the \
complexes of `f⁻¹𝒜`-modules is `inverseImageDeRhamComplexIso` below, which is built from this \
one by `inverseImageRestrictScalarsIso`."]
def inverseImageDifferentialForms (p : ℕ) :
    (pullbackFunctor (RingedSpace.inverseImageProjection X f)).obj (differentialForms.{u} φ p) ≅
      differentialForms.{u} (inverseImageRingMap φ f) p :=
  (inverseImageExteriorAlgebraIso φ f).app (p : ℤ)

/-- The degreewise identification is the degree-`p` component of the comparison of exterior
algebras. -/
theorem inverseImageDifferentialForms_eq (p : ℕ) :
    inverseImageDifferentialForms φ f p = (inverseImageExteriorAlgebraIso φ f).app (p : ℤ) :=
  rfl

/-! ### The de Rham rule on ordered products of exact differentials

The de Rham rule is stated on a multiple of an `IsExactWedge`, with a degree transport. These
two lemmas restate it on the ordered product `Stacks.GradedAlgebra.homogeneousProdLeft`, which
carries the transport inside its own definition, and record the extensionality principle the
rule supplies. Everything below is transport-free.
-/

section Rule

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- **The de Rham rule, transport-free.** On a multiple of an ordered product of exact
differentials the differential is the ordered product of one more exact differential. -/
private theorem DeRhamDifferential.differential_smul_homogeneousProdLeft
    (D : DeRhamDifferential B)
    (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U)
    (c : Fin p → X.sheaf.obj.obj U) :
    (D.differential p).val.app U
        (b • B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p
          fun i => exactOne B U (c i)) =
      B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U (p + 1)
        fun i => exactOne B U ((Fin.cons b c : Fin (p + 1) → X.sheaf.obj.obj U) i) :=
  eq_of_heq
    ((D.generator p U b _ (isExactWedge_homogeneousProdLeft B U p c)).trans
      (Stacks.heq_degCast
        (F := fun k : ℤ => ((B.exterior.piece k).val.obj U : Type u))
        (show (1 : ℤ) + (p : ℤ) = ((p + 1 : ℕ) : ℤ) by omega) _).symm)

/-- **Two morphisms out of `⋀ᵖ Ω` agreeing on the multiples of the ordered products of exact
differentials are equal.** Those products are exactly the exact wedges
(`AlgebraicGeometry.SheafOfModules.exists_eq_homogeneousProdLeft`), they generate `⋀ᵖ Ω`
locally, and the target is a sheaf. -/
theorem deRhamTerm_hom_ext {p : ℕ} {N : _root_.SheafOfModules.{u} (underlyingRingSheaf A)}
    {g h : deRhamTerm B p ⟶ N}
    (H : ∀ (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) (c : Fin p → X.sheaf.obj.obj U),
      g.val.app U (b • B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p
          fun i => exactOne B U (c i)) =
        h.val.app U (b • B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p
          fun i => exactOne B U (c i))) :
    g = h := by
  have key : ∀ (U : (Opens X.carrier)ᵒᵖ) (η : (B.exteriorPower p).val.obj U),
      η ∈ exactWedgeSubgroup B U p → g.val.app U η = h.val.app U η := by
    intro U
    have hsub : exactWedgeSubgroup B U p ≤
        AddMonoidHom.eqLocus (g.val.app U).hom.toAddMonoidHom
          (h.val.app U).hom.toAddMonoidHom := by
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro η ⟨b, ω, hω, rfl⟩
      obtain ⟨c, rfl⟩ := exists_eq_homogeneousProdLeft B U p ω hω
      exact H U b c
    exact fun η hη => hsub hη
  refine (_root_.SheafOfModules.forget _).map_injective
    (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun ξ => ?_))
  obtain ⟨S, hS, hcov⟩ := locallyGeneratedByExactWedges B p U ξ
  refine N.isSheaf.isSeparated (unop U) S hS _ _ fun V i hi => ?_
  exact (PresheafOfModules.naturality_apply g.val i.op ξ).symm.trans
    ((key (op V) _ (hcov i hi)).trans (PresheafOfModules.naturality_apply h.val i.op ξ))

end Rule

/-! ### Inverse image of the terms as sheaves of `f⁻¹𝒜`-modules -/

/-- The functor on opens underlying the inverse image, presented over the carrier of the
inverse-image ringed space. It is `Opens.map f`, but the module-of-differentials API on the
inverse-image ringed space finds its scalar actions only at this spelling. -/
noncomputable abbrev inverseImageOpensMap :
    CategoryTheory.Functor (Opens X.carrier) (Opens (RingedSpace.inverseImage X f).carrier) :=
  RingedSpaceModuleAdjunction.opensMap (RingedSpace.inverseImageProjection X f)


/-- The inverse image of a local section of the target ring. -/
noncomputable abbrev inverseImageRingSection (U : (Opens X.carrier)ᵒᵖ)
    (b : X.sheaf.obj.obj U) :
    (RingedSpace.inverseImage X f).sheaf.obj.obj ((inverseImageOpensMap f).op.obj U) :=
  inverseImageRingUnitApp f X.sheaf U b

/-- The inverse image of a local differential `p`-form, read in `Ωᵖ_{f⁻¹ℬ/f⁻¹𝒜}` through the
degreewise identification. -/
noncomputable def inverseImageForm (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (differentialForms.{u} φ p).val.obj U) :
    (differentialForms.{u} (inverseImageRingMap φ f) p).val.obj
      ((inverseImageOpensMap f).op.obj U) :=
  (inverseImageDifferentialForms φ f p).hom.val.app ((inverseImageOpensMap f).op.obj U)
    (pullbackUnit (RingedSpace.inverseImageProjection X f) (differentialForms.{u} φ p) U ω)

/-- **The identification is semilinear** for the inverse-image ring map: the inverse image of a
multiple of a form is the corresponding multiple of the inverse image of the form. -/
theorem inverseImageForm_smul (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U)
    (ω : (differentialForms.{u} φ p).val.obj U) :
    inverseImageForm φ f p U
        (SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj.obj U)
          b ω) =
      SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
          (RingedSpace.inverseImage X f).sheaf).obj.obj ((inverseImageOpensMap f).op.obj U))
        (inverseImageRingSection f U b) (inverseImageForm φ f p U ω) :=
  (congrArg ((inverseImageDifferentialForms φ f p).hom.val.app
      ((inverseImageOpensMap f).op.obj U))
    (pullbackUnit_smul (RingedSpace.inverseImageProjection X f)
      (differentialForms.{u} φ p) U b ω)).trans (map_smul _ _ _)

/-- **The identification respects the degree-zero unit.** -/
theorem inverseImageForm_one (U : (Opens X.carrier)ᵒᵖ) :
    inverseImageForm φ f 0 U ((differentialAlgebras.{u} φ).exterior.one.eval U) =
      (differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior.one.eval
        ((inverseImageOpensMap f).op.obj U) :=
  (inverseImageExteriorAlgebraIso φ f).map_one U

/-- **The degree-one identification of Tag 08RR carries `f⁻¹(d b)` to `d (f⁻¹b)`.** This is the
compatibility of that identification with the universal derivations, read on the inverse-image
sections. -/
theorem inverseImageDifferentials_hom_d (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    (inverseImageDifferentials φ f).hom.val.app ((inverseImageOpensMap f).op.obj U)
        (pullbackUnit (RingedSpace.inverseImageProjection X f)
          (moduleOfDifferentials.{u, u, u} φ) U ((universalDerivation.{u, u, u} φ).d b)) =
      (universalDerivation.{u, u, u} (inverseImageRingMap φ f)).d
        (inverseImageRingSection f U b) := by
  have h := congrArg (fun d => d.d (inverseImageRingSection f U b))
    (pullbackDifferentialsIso_compatible f φ)
  exact (congrArg ((inverseImageDifferentials φ f).hom.val.app ((inverseImageOpensMap f).op.obj U))
    ((inverseImageDerivation f (universalDerivation.{u, u, u} φ)).property U b)).symm.trans h

/-- **The identification carries an exact differential to an exact differential.** -/
theorem inverseImageForm_exactOne (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    inverseImageForm φ f 1 U (exactOne (differentialAlgebras.{u} φ) U b) =
      exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
        ((inverseImageOpensMap f).op.obj U)
        (inverseImageRingSection f U b) :=
  ((inverseImageExteriorAlgebraIso φ f).map_generator U
      ((universalDerivation.{u, u, u} φ).d b)).trans
    (congrArg ((differentialAlgebras.{u} (inverseImageRingMap φ f)).exteriorGenerator.val.app
      ((inverseImageOpensMap f).op.obj U)) (inverseImageDifferentials_hom_d φ f U b))

/-- **The identification respects the exterior product** of a degree-`p` and a degree-one form.
The right-handed product has degree `(p : ℤ) + 1`, which is definitionally `((p + 1 : ℕ) : ℤ)`,
so no degree transport appears. -/
theorem inverseImageForm_mul (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (differentialForms.{u} φ p).val.obj U)
    (η : (differentialForms.{u} φ 1).val.obj U) :
    inverseImageForm φ f (p + 1) U
        (((differentialAlgebras.{u} φ).exterior.mul (p : ℤ) 1).app U ω η) =
      ((differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior.mul (p : ℤ) 1).app
        ((inverseImageOpensMap f).op.obj U) (inverseImageForm φ f p U ω)
        (inverseImageForm φ f 1 U η) :=
  (inverseImageExteriorAlgebraIso φ f).map_mul (p : ℤ) 1 U ω η

/-- **The identification carries an ordered product of exact differentials to the ordered
product of the exact differentials of the inverse images.** The right-handed product needs no
degree transport, so this is a bare induction on the exterior-product compatibility. -/
theorem inverseImageForm_homogeneousProd (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (c : Fin p → X.sheaf.obj.obj U) :
    inverseImageForm φ f p U
        ((differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProd U p
          fun i => exactOne (differentialAlgebras.{u} φ) U (c i)) =
      (differentialAlgebras.{u}
          (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProd
        ((inverseImageOpensMap f).op.obj U) p
        fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
          ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i)) := by
  induction p with
  | zero => exact inverseImageForm_one φ f U
  | succ p ih =>
      have hA : (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProd
            U (p + 1) (fun i => exactOne (differentialAlgebras.{u} φ) U (c i)) =
          ((differentialAlgebras.{u} φ).exterior.mul (p : ℤ) 1).app U
            ((differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProd U p
              fun i => exactOne (differentialAlgebras.{u} φ) U (c i.castSucc))
            (exactOne (differentialAlgebras.{u} φ) U (c (Fin.last p))) := rfl
      have hB : (differentialAlgebras.{u}
            (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProd
            ((inverseImageOpensMap f).op.obj U) (p + 1)
            (fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
              ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i))) =
          ((differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior.mul (p : ℤ) 1).app
            ((inverseImageOpensMap f).op.obj U)
            ((differentialAlgebras.{u}
              (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProd
              ((inverseImageOpensMap f).op.obj U) p
              fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
                ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i.castSucc)))
            (exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
              ((inverseImageOpensMap f).op.obj U)
              (inverseImageRingSection f U (c (Fin.last p)))) := rfl
      refine Eq.trans (congrArg (inverseImageForm φ f (p + 1) U) hA)
        ((inverseImageForm_mul φ f p U _ _).trans (Eq.trans ?_ hB.symm))
      refine Eq.trans (congrArg (fun x =>
        ((differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior.mul (p : ℤ) 1).app
          ((inverseImageOpensMap f).op.obj U) x
          (inverseImageForm φ f 1 U (exactOne (differentialAlgebras.{u} φ) U (c (Fin.last p)))))
        (ih fun i => c i.castSucc)) ?_
      exact congrArg (fun y =>
        ((differentialAlgebras.{u} (inverseImageRingMap φ f)).exterior.mul (p : ℤ) 1).app
          ((inverseImageOpensMap f).op.obj U)
          ((differentialAlgebras.{u}
            (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProd
            ((inverseImageOpensMap f).op.obj U) p
            fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
              ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i.castSucc))) y)
        (inverseImageForm_exactOne φ f U (c (Fin.last p)))

/-- The left-handed form of `inverseImageForm_homogeneousProd`, which is the shape the de Rham
rule and `AlgebraicGeometry.SheafOfModules.exists_eq_homogeneousProdLeft` speak in. -/
theorem inverseImageForm_homogeneousProdLeft (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (c : Fin p → X.sheaf.obj.obj U) :
    inverseImageForm φ f p U
        ((differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p
          fun i => exactOne (differentialAlgebras.{u} φ) U (c i)) =
      (differentialAlgebras.{u}
          (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        ((inverseImageOpensMap f).op.obj U) p
        fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
          ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i)) := by
  refine Eq.trans (congrArg (inverseImageForm φ f p U)
    (Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd _ U p _)) ?_
  exact (inverseImageForm_homogeneousProd φ f p U c).trans
    (Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd _ _ p _).symm

/-- **The identification of the terms, as sheaves of `f⁻¹𝒜`-modules.** The terms of the de Rham
complex are the exterior powers read along `φ`; the degreewise identification of Tag 0FKP is of
the exterior powers themselves, and
`AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsIso` moves it across the
restriction of scalars. -/
noncomputable def inverseImageDeRhamTerm (p : ℕ) :
    inverseImageModule f A (deRhamTerm (differentialAlgebras.{u} φ) p) ≅
      deRhamTerm (differentialAlgebras.{u} (inverseImageRingMap φ f)) p :=
  inverseImageRestrictScalarsIso f φ (differentialForms.{u} φ p) ≪≫
    (_root_.SheafOfModules.restrictScalars
      (underlyingRingHom (φ := inverseImageRingMap φ f))).mapIso
        (inverseImageDifferentialForms φ f p)

/-- On an inverse-image section the identification of the terms is the degreewise
identification. -/
theorem inverseImageDeRhamTerm_unit (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (differentialForms.{u} φ p).val.obj U) :
    (inverseImageDeRhamTerm φ f p).hom.val.app ((inverseImageOpensMap f).op.obj U)
        ((inverseImageModuleUnit f A (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U ω) =
      inverseImageForm φ f p U ω :=
  congrArg ((inverseImageDifferentialForms φ f p).hom.val.app ((inverseImageOpensMap f).op.obj U))
    (inverseImageRestrictScalarsIso_unit_apply f φ (differentialForms.{u} φ p) U ω)

/-- The inverse-image section of a multiple of a form is the corresponding multiple of the
inverse-image section. -/
theorem inverseImageDeRhamTerm_unit_smul (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (b : X.sheaf.obj.obj U) (ω : (differentialForms.{u} φ p).val.obj U) :
    (inverseImageDeRhamTerm φ f p).hom.val.app ((inverseImageOpensMap f).op.obj U)
        ((inverseImageModuleUnit f A
          (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
            (SMul.smul
              (M := (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj.obj U)
              (α := ((differentialForms.{u} φ p).val.obj U : Type u)) b ω)) =
      SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
          (RingedSpace.inverseImage X f).sheaf).obj.obj ((inverseImageOpensMap f).op.obj U))
        (inverseImageRingSection f U b) (inverseImageForm φ f p U ω) :=
  (inverseImageDeRhamTerm_unit φ f p U
    (SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj.obj U)
      (α := ((differentialForms.{u} φ p).val.obj U : Type u)) b ω)).trans
    (inverseImageForm_smul φ f p U b ω)

/-- The inverse-image section of a multiple of an ordered product of exact differentials is the
corresponding multiple of the ordered product of the exact differentials of the inverse images. -/
private theorem inverseImageDeRhamTerm_unit_smul_homogeneousProdLeft (p : ℕ)
    (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) (c : Fin p → X.sheaf.obj.obj U) :
    (inverseImageDeRhamTerm φ f p).hom.val.app ((inverseImageOpensMap f).op.obj U)
        ((inverseImageModuleUnit f A
          (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
          (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i))) =
      inverseImageRingSection f U b •
        (differentialAlgebras.{u}
          (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
          ((inverseImageOpensMap f).op.obj U) p
          fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
            ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i)) :=
  (inverseImageDeRhamTerm_unit_smul φ f p U b _).trans
    (congrArg (fun z : ((differentialForms.{u} (inverseImageRingMap φ f) p).val.obj
        ((inverseImageOpensMap f).op.obj U) : Type u) =>
      SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
          (RingedSpace.inverseImage X f).sheaf).obj.obj ((inverseImageOpensMap f).op.obj U))
        (inverseImageRingSection f U b) z)
      (inverseImageForm_homogeneousProdLeft φ f p U c))

/-! ### The identification of the complexes -/

/-- Pullback of sheaves of modules along `inverseImageRingHom g O` is a left adjoint. -/
instance isLeftAdjoint_inverseImagePullback {Z W : TopCat.{u}} (g : W ⟶ Z)
    (O : TopCat.Sheaf CommRingCat.{u} Z) :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom g O)).IsLeftAdjoint :=
  (inverseImageAdjunction g O).isLeftAdjoint

/-- Pullback of sheaves of modules along `inverseImageRingHom g O` preserves zero morphisms. -/
instance preservesZeroMorphisms_inverseImagePullback {Z W : TopCat.{u}} (g : W ⟶ Z)
    (O : TopCat.Sheaf CommRingCat.{u} Z) :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom g O)).PreservesZeroMorphisms :=
  CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- **The inverse image of the relative de Rham complex**, taken termwise: a complex of sheaves
of `f⁻¹𝒜`-modules on `Y`. -/
noncomputable abbrev inverseImageDeRhamComplex :
    CochainComplex
      (_root_.SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing A f))) ℕ :=
  ((_root_.SheafOfModules.pullback (inverseImageRingHom f A)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (relativeDeRhamComplex (differentialAlgebras.{u} φ))

/-- Transposing a morphism out of the inverse image of a term, on sections: the transpose at a
local section is the morphism evaluated at the inverse-image section. -/
private theorem homEquiv_val_app {M : _root_.SheafOfModules.{u} (underlyingRingSheaf A)}
    {Z : _root_.SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing A f))}
    (g : inverseImageModule f A M ⟶ Z) (U : (Opens X.carrier)ᵒᵖ) (z : M.val.obj U) :
    (((inverseImageAdjunction f A).homEquiv M Z) g).val.app U z =
      g.val.app ((inverseImageOpensMap f).op.obj U)
        ((inverseImageModuleUnit f A M).val.app U z) :=
  congrArg (fun k => k.val.app U z)
    (Adjunction.homEquiv_unit (adj := inverseImageAdjunction f A) (f := g))

/-- **Two morphisms out of the inverse image of a term agree** as soon as they agree on the
inverse-image sections of the multiples of the ordered products of exact differentials. Both
morphisms are determined by their transposes, and a transpose is determined on those sections by
`AlgebraicGeometry.SheafOfModules.deRhamTerm_hom_ext`. -/
theorem inverseImageDeRhamTerm_hom_ext (p : ℕ)
    {N : _root_.SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing A f))}
    {g h : inverseImageModule f A (deRhamTerm (differentialAlgebras.{u} φ) p) ⟶ N}
    (H : ∀ (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) (c : Fin p → X.sheaf.obj.obj U),
      g.val.app ((inverseImageOpensMap f).op.obj U)
          ((inverseImageModuleUnit f A (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
            (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
              U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i))) =
        h.val.app ((inverseImageOpensMap f).op.obj U)
          ((inverseImageModuleUnit f A (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
            (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
              U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i)))) :
    g = h :=
  ((inverseImageAdjunction f A).homEquiv _ N).injective
    (deRhamTerm_hom_ext (differentialAlgebras.{u} φ) fun U b c =>
      (homEquiv_val_app f g U _).trans ((H U b c).trans (homEquiv_val_app f h U _).symm))

/-- **The identification of the terms is a morphism of complexes, on the inverse-image sections
that determine it.** On the source the de Rham differential produces the ordered product of one
more exact differential and the identification carries that product over; on the target the
identification carries the product over and the de Rham differential of the inverse-image rings
produces one more exact differential. -/
theorem inverseImageDeRhamTerm_comm_d_apply (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (b : X.sheaf.obj.obj U) (c : Fin p → X.sheaf.obj.obj U) :
    (inverseImageDeRhamTerm φ f (p + 1)).hom.val.app ((inverseImageOpensMap f).op.obj U)
        (((inverseImageDeRhamComplex φ f).d p (p + 1)).val.app
          ((inverseImageOpensMap f).op.obj U)
          ((inverseImageModuleUnit f A (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
            (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
              U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i)))) =
      ((relativeDeRhamComplex (differentialAlgebras.{u} (inverseImageRingMap φ f))).d
            p (p + 1)).val.app ((inverseImageOpensMap f).op.obj U)
        ((inverseImageDeRhamTerm φ f p).hom.val.app ((inverseImageOpensMap f).op.obj U)
          ((inverseImageModuleUnit f A (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
            (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
              U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i)))) := by
  have hcons : (fun i => inverseImageRingSection f U
        ((Fin.cons b c : Fin (p + 1) → X.sheaf.obj.obj U) i)) =
      (Fin.cons (inverseImageRingSection f U b)
        (fun i => inverseImageRingSection f U (c i)) :
          Fin (p + 1) → (RingedSpace.inverseImage X f).sheaf.obj.obj
            ((inverseImageOpensMap f).op.obj U)) := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have hnat : (inverseImageModuleUnit f A
          (deRhamTerm (differentialAlgebras.{u} φ) (p + 1))).val.app U
        (((relativeDeRhamComplex (differentialAlgebras.{u} φ)).d p (p + 1)).val.app U
          (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i))) =
      ((inverseImageDeRhamComplex φ f).d p (p + 1)).val.app
          ((inverseImageOpensMap f).op.obj U)
        ((inverseImageModuleUnit f A (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
          (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i))) :=
    ConcreteCategory.congr_hom (congrArg (fun k => k.val.app U)
        ((inverseImageAdjunction f A).unit.naturality
          ((relativeDeRhamComplex (differentialAlgebras.{u} φ)).d p (p + 1))))
      (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p
        fun i => exactOne (differentialAlgebras.{u} φ) U (c i))
  have hsrc : ((relativeDeRhamComplex (differentialAlgebras.{u} φ)).d p (p + 1)).val.app U
        (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
          U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i)) =
      (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        U (p + 1) fun i => exactOne (differentialAlgebras.{u} φ) U
          ((Fin.cons b c : Fin (p + 1) → X.sheaf.obj.obj U) i) :=
    (_root_.SheafOfModules.hom_congr_app_apply
        (deRhamComplex_d (differentialAlgebras.{u} φ)
          (deRhamDifferential (differentialAlgebras.{u} φ)) p) U _).trans
      (DeRhamDifferential.differential_smul_homogeneousProdLeft (differentialAlgebras.{u} φ)
        (deRhamDifferential (differentialAlgebras.{u} φ)) p U b c)
  have htgt : ((relativeDeRhamComplex
            (differentialAlgebras.{u} (inverseImageRingMap φ f))).d p (p + 1)).val.app
          ((inverseImageOpensMap f).op.obj U)
        (inverseImageRingSection f U b •
          (differentialAlgebras.{u}
            (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            ((inverseImageOpensMap f).op.obj U) p
            fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
              ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i))) =
      (differentialAlgebras.{u}
          (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
          ((inverseImageOpensMap f).op.obj U) (p + 1)
          fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
            ((inverseImageOpensMap f).op.obj U)
            ((Fin.cons (inverseImageRingSection f U b)
              (fun i => inverseImageRingSection f U (c i)) :
                Fin (p + 1) → (RingedSpace.inverseImage X f).sheaf.obj.obj
                  ((inverseImageOpensMap f).op.obj U)) i) :=
    (_root_.SheafOfModules.hom_congr_app_apply
        (deRhamComplex_d (differentialAlgebras.{u} (inverseImageRingMap φ f))
          (deRhamDifferential (differentialAlgebras.{u} (inverseImageRingMap φ f))) p)
        ((inverseImageOpensMap f).op.obj U) _).trans
      (DeRhamDifferential.differential_smul_homogeneousProdLeft
        (differentialAlgebras.{u} (inverseImageRingMap φ f))
        (deRhamDifferential (differentialAlgebras.{u} (inverseImageRingMap φ f))) p
        ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U b)
        fun i => inverseImageRingSection f U (c i))
  refine Eq.trans (congrArg ((inverseImageDeRhamTerm φ f (p + 1)).hom.val.app
      ((inverseImageOpensMap f).op.obj U)) hnat.symm) ?_
  refine Eq.trans (inverseImageDeRhamTerm_unit φ f (p + 1) U _) ?_
  refine Eq.trans (congrArg (inverseImageForm φ f (p + 1) U) hsrc) ?_
  refine Eq.trans (inverseImageForm_homogeneousProdLeft φ f (p + 1) U
    (Fin.cons b c : Fin (p + 1) → X.sheaf.obj.obj U)) ?_
  refine Eq.trans (congrArg (fun z : Fin (p + 1) →
      (RingedSpace.inverseImage X f).sheaf.obj.obj ((inverseImageOpensMap f).op.obj U) =>
    (differentialAlgebras.{u}
        (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        ((inverseImageOpensMap f).op.obj U) (p + 1)
        fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
          ((inverseImageOpensMap f).op.obj U) (z i)) hcons) ?_
  refine Eq.trans htgt.symm ?_
  refine congrArg (((relativeDeRhamComplex
      (differentialAlgebras.{u} (inverseImageRingMap φ f))).d p (p + 1)).val.app
        ((inverseImageOpensMap f).op.obj U)) ?_
  exact (inverseImageDeRhamTerm_unit_smul_homogeneousProdLeft φ f p U b c).symm

/-- **The identification of the terms is a morphism of complexes.** Both composites are
morphisms out of an inverse image, so they agree as soon as they agree on the inverse-image
sections of the multiples of the ordered products of exact differentials. -/
theorem inverseImageDeRhamTerm_comm_d (p : ℕ) :
    (inverseImageDeRhamComplex φ f).d p (p + 1) ≫ (inverseImageDeRhamTerm φ f (p + 1)).hom =
      (inverseImageDeRhamTerm φ f p).hom ≫
        (relativeDeRhamComplex
          (differentialAlgebras.{u} (inverseImageRingMap φ f))).d p (p + 1) :=
  inverseImageDeRhamTerm_hom_ext φ f p fun U b c =>
    inverseImageDeRhamTerm_comm_d_apply φ f p U b c

/-- An identification of the inverse image of the de Rham complex with the de Rham complex of
the inverse-image rings is **canonical** if in every degree it carries the inverse-image section
of a multiple of an ordered product of exact differentials to the same expression formed from
the inverse images of the local sections involved.

In degree zero this says the identification is the inverse-image ring map, and in degree one
that it is the identification of Tag 08RR; the condition in higher degrees is the compatibility
with the exterior products. These sections generate the terms locally, so the condition
determines the identification. -/
def IsCanonicalInverseImageDeRhamIso
    (e : inverseImageDeRhamComplex φ f ≅
      relativeDeRhamComplex (differentialAlgebras.{u} (inverseImageRingMap φ f))) : Prop :=
  ∀ (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U)
    (c : Fin p → X.sheaf.obj.obj U),
      (e.hom.f p).val.app ((inverseImageOpensMap f).op.obj U)
          ((inverseImageModuleUnit f A
            (deRhamTerm (differentialAlgebras.{u} φ) p)).val.app U
            (b • (differentialAlgebras.{u} φ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
              U p fun i => exactOne (differentialAlgebras.{u} φ) U (c i))) =
        inverseImageRingSection f U b •
          (differentialAlgebras.{u}
            (inverseImageRingMap φ f)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            ((inverseImageOpensMap f).op.obj U) p
            fun i => exactOne (differentialAlgebras.{u} (inverseImageRingMap φ f))
              ((inverseImageOpensMap f).op.obj U) (inverseImageRingSection f U (c i))

/-- **Stacks Project, Tag 0FKP.** The canonical identification
`f⁻¹Ω•_{ℬ/𝒜} = Ω•_{f⁻¹ℬ/f⁻¹𝒜}` of de Rham complexes: the degreewise identification of the
differential forms, moved into sheaves of `f⁻¹𝒜`-modules and assembled into an isomorphism of
complexes. -/
@[stacks 0FKP "the identification of the de Rham COMPLEXES: `f⁻¹Ω•_{ℬ/𝒜} = Ω•_{f⁻¹ℬ/f⁻¹𝒜}` as \
complexes of sheaves of `f⁻¹𝒜`-modules"]
noncomputable def inverseImageDeRhamComplexIso :
    inverseImageDeRhamComplex φ f ≅
      relativeDeRhamComplex (differentialAlgebras.{u} (inverseImageRingMap φ f)) :=
  HomologicalComplex.Hom.isoOfComponents (inverseImageDeRhamTerm φ f) (by
    rintro i j hij
    have hj : i + 1 = j := hij
    subst hj
    exact (inverseImageDeRhamTerm_comm_d φ f i).symm)

/-- **Stacks Project, Tag 0FKP, canonicality.** The identification of the complexes is the one
that carries each local multiple of an ordered product of exact differentials to the same
expression in the inverse-image rings. -/
@[stacks 0FKP "canonicality of the identification of the complexes: it is the map determined by \
`b · d b₁ ∧ ⋯ ∧ d bₚ ↦ f⁻¹b · d(f⁻¹b₁) ∧ ⋯ ∧ d(f⁻¹bₚ)` on the inverse-image sections"]
theorem inverseImageDeRhamComplexIso_canonical :
    IsCanonicalInverseImageDeRhamIso φ f (inverseImageDeRhamComplexIso φ f) :=
  fun p U b c => inverseImageDeRhamTerm_unit_smul_homogeneousProdLeft φ f p U b c

/-- **Stacks Project, Tag 0FKP, uniqueness.** Canonicality determines the identification of the
complexes: the local multiples of the ordered products of exact differentials generate the terms
locally, so an isomorphism of complexes prescribed on them is prescribed. -/
@[stacks 0FKP "uniqueness: a canonical identification of the de Rham complexes is the one \
constructed here"]
theorem inverseImageDeRhamComplexIso_unique
    (e : inverseImageDeRhamComplex φ f ≅
      relativeDeRhamComplex (differentialAlgebras.{u} (inverseImageRingMap φ f)))
    (he : IsCanonicalInverseImageDeRhamIso φ f e) :
    e = inverseImageDeRhamComplexIso φ f :=
  Iso.ext (HomologicalComplex.Hom.ext (funext fun p =>
    inverseImageDeRhamTerm_hom_ext φ f p fun U b c =>
      (he p U b c).trans (inverseImageDeRhamComplexIso_canonical φ f p U b c).symm))

end AlgebraicGeometry.SheafOfModules

end
