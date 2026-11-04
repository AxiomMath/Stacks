module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The presentation attached to a square-zero extension of ringed topoi (Stacks 0GQ6)

Let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` be a morphism of ringed topoi, let `𝒢` be an `𝒪`-module
and let `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` be an extension of `f⁻¹𝒪_ℬ`-algebras with `𝒢` an ideal of square
zero, that is a solution of the square-zero extension problem of **Stacks 08UF** whose base
reduction is invertible — the situation of **Stacks 0GQ5**. Taking for `ℰ` the sheaf of sets
underlying `𝒪'` and for `α' : ℰ ⟶ 𝒪'` the identity gives a commutative diagram over
`𝒪' ⟶ 𝒪` in which `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` is surjective; writing `𝒥` for its kernel,

`NL(α) = (𝒥/𝒥² ⟶ Ω_{f⁻¹𝒪_ℬ[ℰ]/f⁻¹𝒪_ℬ} ⊗_{f⁻¹𝒪_ℬ[ℰ]} 𝒪)`

is `NL_{𝒪/𝒪_ℬ}` in `D(𝒪)`, and `α'` induces a map `𝒥/𝒥² ⟶ 𝒢`, hence a first Ext class of
`NL(α)`.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.inverseImageBaseRing`: the sheaf of
  rings `f⁻¹𝒪_ℬ` on the site of the source, over which the free algebra below is taken.
* `CompatibleFirstOrderThickening.kernelPreimage` and
  `CompatibleFirstOrderThickening.kernelIdentification`: the inverse on sections of the kernel
  identification of a solution, and that inverse as a
  `Stacks.Sites.Conormal.IdealRestriction` for the reduction `𝒪' ⟶ 𝒪`.
* `CompatibleFirstOrderThickening.generators`, `.generatorsMap` and `.lift`: the sheaf of sets
  `ℰ`, the map `α : ℰ ⟶ 𝒪`, and the map `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪'` determined by `α'`.
* `CompatibleFirstOrderThickening.presentation`: the presentation `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪`.
* `CompatibleFirstOrderThickening.conormalToIdeal`: the induced map `𝒥/𝒥² ⟶ 𝒢`.
* `CompatibleFirstOrderThickening.extClass`: the resulting class in `Ext¹_𝒪(NL(α), 𝒢)`.
* `CompatibleFirstOrderThickening.naiveCotangentIso`: the isomorphism `NL(α) ≅ NL_{𝒪/𝒪_ℬ}` in
  `D(𝒪)` that a quasi-isomorphic comparison map gives, that quasi-isomorphy being a hypothesis;
  see the implementation notes.

## Main results

* `CompatibleFirstOrderThickening.exists_base`: an invertible base reduction makes the thickened
  structure sheaf of a solution an `f⁻¹𝒪_ℬ`-algebra over `𝒪`, which is what makes the free
  algebra `f⁻¹𝒪_ℬ[ℰ]` map to `𝒪'`.
* `CompatibleFirstOrderThickening.lift_comp_reduction`: the commutative diagram of the source,
  that is, `α'` followed by the reduction `𝒪' ⟶ 𝒪` is the presentation attached to `α`.
* `CompatibleFirstOrderThickening.presentation_isLocallySurjective`: the presentation
  `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` is surjective, which is what makes `NL(α)` defined.
* `CompatibleFirstOrderThickening.exists_generators`: the choice the source makes is possible —
  there are `ℰ`, `α'` and `α` forming a commutative triangle over `𝒪' ⟶ 𝒪` with
  `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` surjective.
* `CompatibleFirstOrderThickening.mul_incl_presentationScalar`: scalars act on the identified
  kernel through the reduction, with the scalar in the `presentationScalar` spelling.
* `CompatibleFirstOrderThickening.idealRestriction_app`: on a local relation `h` of the
  presentation the map `𝒥/𝒥² ⟶ 𝒢` is `h ↦ α'(h)`, read in the square-zero ideal and carried to
  `𝒢`; the induced map on `𝒥/𝒥²` is then determined by
  `Stacks.Sites.Conormal.conormalDesc_toAssociatedModule`.

## Implementation notes

**The identification `NL(α) ≅ NL_{𝒪/𝒪_ℬ}`.**
`CompatibleFirstOrderThickening.naiveCotangentIso` takes the quasi-isomorphy of the canonical
comparison map `Stacks.SheafOfModules.naiveCotangentComplexComparison` as an explicit
hypothesis. Everything else below is unconditional: the presentation, its surjectivity, the
map `𝒥/𝒥² ⟶ 𝒢` and the Ext class are all constructed outright. The hypothesis is
**Stacks 08TY**, which holds on every site by
`Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison_site`; over
`TopologicalSpace.Opens.grothendieckTopology` it is also the stalkwise
`Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison`.

The algebra structure `f⁻¹𝒪_ℬ ⟶ 𝒪'` is carried as a pair of arguments rather than rebuilt at
every use: `CompatibleFirstOrderThickening.exists_base` produces it from the invertibility of
the base reduction, which is exactly the shape of the problem of **Stacks 0GQ5**, and the
declarations that need the map take it together with its compatibility with the reduction.

The identification of the square-zero ideal `Ker(𝒪' ⟶ 𝒪)` with `𝒢` is a field of a solution,
in the form of an inclusion of `𝒢` into `𝒪'` which is bijective onto the kernel section by
section. The map `𝒥/𝒥² ⟶ 𝒢` needs its *inverse*, which is
`CompatibleFirstOrderThickening.kernelPreimage`; it is additive, linear over `𝒪'` acting
through the reduction, and natural, because the inclusion is, and therefore assembles into a
`Stacks.Sites.Conormal.IdealRestriction`. Such a family annihilates the square of the ideal
automatically, which is the source's square-zero hypothesis.

Both the presentation and its lift are morphisms of sheaves of rings on the one site, the
underlying topoi of a first order thickening being identified; accordingly `𝒪'` is a sheaf of
commutative rings on the site of the source and not the structure sheaf of a second ringed
topos.

**Universes.** The source ringed topos is `AlgebraicGeometry.RingedTopos.{u, u, u}`, so that the
conormal sheaf of a presentation, whose sections live in the universe `max w u v` generated by
the site and the ring universe, is a sheaf of modules in the universe of the prescribed module
`𝒢`. The base ringed topos is unconstrained.

## References

* [Stacks Project, Tag 0GQ6](https://stacks.math.columbia.edu/tag/0GQ6)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.Conormal (IdealRestriction conormalDesc conormalSheaf kernelIdeal
  kernelIdeal_le_comap hom_of_comp_eq presentationScalar)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf
  freeAlgebraSheafCoefficientMap freeAlgebraSheafVariable canonicalPresentation
  freeAlgebraSheaf_hom_ext canonicalPresentation_comp_coefficientMap
  freeAlgebraSheafCoefficientMap_comp_desc freeAlgebraSheafVariable_comp_desc)

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- `f⁻¹𝒪_ℬ`, the inverse image of the structure sheaf of the base, as a sheaf of commutative
rings on the site of the source, which is the category the constructions below compose in. -/
abbrev inverseImageBaseRing (S : RingedToposExtensionProblem X B) :
    Sheaf X.J CommRingCat.{u} :=
  (inverseImageCommRingFunctor S.f.toToposHom).obj B.O

namespace CompatibleFirstOrderThickening

variable {S : RingedToposExtensionProblem X B} (P : S.CompatibleFirstOrderThickening)

/-! ### The inverse of the kernel identification -/

/-- `CompatibleFirstOrderThickening.mul_incl`, with the scalar in the `presentationScalar`
spelling that the conormal presentation uses.

The scalar is read in `(sheafCompose X.J (forget₂ CommRingCat RingCat)).obj X.O`, the sheaf of
rings over which `𝒢` is a module; `Stacks.Sites.Conormal.presentationScalar` is stated with
values in `Stacks.SheafOfModules.Tensor.ringSheaf X.O`, which is the same sheaf of rings but a
spelling that instance search cannot reduce to the one carried by `𝒢`. -/
theorem mul_incl_presentationScalar {U : X.Cᵒᵖ} (a : P.extension.obj.obj U)
    (g : S.G.val.obj U) :
    a * P.incl g =
      P.incl ((S.G.val.obj U).isModule.toSMul.smul
        (presentationScalar P.reduction U a) g) :=
  P.mul_incl a g

/-- A local section of the kernel ideal of the reduction is killed by the reduction. -/
theorem reduction_coe_eq_zero {U : X.Cᵒᵖ} (a : kernelIdeal P.reduction.hom U) :
    P.reduction.hom.app U (a : P.extension.obj.obj U) = 0 := a.2

/-- The local section of `𝒢` corresponding to a local section of the kernel of the reduction:
the inverse on sections of the kernel identification of a solution. -/
def kernelPreimage {U : X.Cᵒᵖ} (a : kernelIdeal P.reduction.hom U) : S.G.val.obj U :=
  (P.exists_incl (a : P.extension.obj.obj U) (P.reduction_coe_eq_zero a)).choose

/-- The inverse of the kernel identification is a section of it. -/
theorem incl_kernelPreimage {U : X.Cᵒᵖ} (a : kernelIdeal P.reduction.hom U) :
    P.incl (P.kernelPreimage a) = (a : P.extension.obj.obj U) :=
  (P.exists_incl (a : P.extension.obj.obj U) (P.reduction_coe_eq_zero a)).choose_spec

/-- The inverse of the kernel identification on the sections over one object of the site, as a
homomorphism of additive groups. -/
def kernelPreimageHom (U : X.Cᵒᵖ) :
    ↥(kernelIdeal P.reduction.hom U) →+ ↥(S.G.val.obj U) where
  toFun a := P.kernelPreimage a
  map_zero' := P.incl_injective (U := U) (by
    rw [P.incl_kernelPreimage, P.incl_zero]
    rfl)
  map_add' a b := P.incl_injective (U := U) (by
    rw [P.incl_kernelPreimage, P.incl_add, P.incl_kernelPreimage, P.incl_kernelPreimage]
    rfl)

/-- `kernelPreimageHom` is `kernelPreimage` on sections. -/
@[simp] theorem kernelPreimageHom_apply (U : X.Cᵒᵖ) (a : kernelIdeal P.reduction.hom U) :
    P.kernelPreimageHom U a = P.kernelPreimage a :=
  rfl

/-- The inverse of the kernel identification is linear over `𝒪'` acting on `𝒢` through the
reduction. -/
theorem kernelPreimage_smul {U : X.Cᵒᵖ} (r : P.extension.obj.obj U)
    (a : kernelIdeal P.reduction.hom U) :
    P.kernelPreimage (r • a) =
      (S.G.val.obj U).isModule.toSMul.smul
        (presentationScalar P.reduction U r) (P.kernelPreimage a) :=
  P.incl_injective (U := U) (by
    rw [P.incl_kernelPreimage, ← P.mul_incl_presentationScalar, P.incl_kernelPreimage]
    rfl)

/-- The inverse of the kernel identification commutes with the restriction maps of the site. -/
theorem kernelPreimage_naturality {U V : X.Cᵒᵖ} (i : U ⟶ V)
    (a : kernelIdeal P.reduction.hom U) :
    P.kernelPreimage ⟨(P.extension.obj.map i).hom (a : P.extension.obj.obj U),
        Stacks.Sites.Conormal.map_kernel P.reduction.hom i a.2⟩ =
      S.G.val.map i (P.kernelPreimage a) :=
  P.incl_injective (U := V) (by
    rw [P.incl_kernelPreimage, P.incl_naturality, P.incl_kernelPreimage])

/-- The identification of the square-zero ideal `Ker(𝒪' ⟶ 𝒪)` of a solution with the prescribed
module `𝒢`, as a restriction datum for the reduction `𝒪' ⟶ 𝒪`. -/
def kernelIdentification : IdealRestriction.{u, u, u, u} P.reduction S.G where
  app U := P.kernelPreimageHom U
  app_smul := fun _ r a ↦ P.kernelPreimage_smul r a
  app_map i a := P.kernelPreimage_naturality i a

/-- On a local section of the kernel of the reduction the restriction datum of a solution is
the inverse of the kernel identification. -/
theorem kernelIdentification_app (U : X.Cᵒᵖ) (a : kernelIdeal P.reduction.hom U) :
    P.kernelIdentification.app U a = P.kernelPreimage a :=
  rfl

/-! ### The algebra structure on the thickened structure sheaf -/

/-- **The thickened structure sheaf of a solution is an `f⁻¹𝒪_ℬ`-algebra over `𝒪`.** This is
where the shape of the problem of [Stacks 0GQ5] enters: its base thickening is
`0 ⟶ 0 ⟶ f⁻¹𝒪_ℬ ⟶ f⁻¹𝒪_ℬ ⟶ 0`, that is, its base reduction is invertible, and then the map
from the inverse image of the thickened base ring is a map out of `f⁻¹𝒪_ℬ` itself. -/
theorem exists_base [IsIso S.baseReduction] :
    ∃ base : inverseImageBaseRing S ⟶ P.extension,
      base ≫ P.reduction = S.f.fSharpInverseImage := by
  refine ⟨(inverseImageCommRingFunctor S.f.toToposHom).map (inv S.baseReduction) ≫ P.baseMap, ?_⟩
  rw [Category.assoc, P.baseMap_reduction, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-! ### The presentation of `𝒪` by the sheaf of sets underlying `𝒪'` -/

variable [HasWeakSheafify X.J CommRingCat.{u}]

/-- The sheaf of sets `ℰ` of the source: the one underlying `𝒪'`. -/
abbrev generators : Functor X.Cᵒᵖ (Type u) := underlyingPresheaf X.J P.extension

/-- The map `α : ℰ ⟶ 𝒪` of the source: the reduction, read on underlying sets. -/
abbrev generatorsMap : P.generators ⟶ underlyingPresheaf X.J X.O :=
  Functor.whiskerRight P.reduction.hom (forget CommRingCat.{u})

/-- The map `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪'` determined by `α' : ℰ ⟶ 𝒪'`, which is the identity. -/
abbrev lift (base : inverseImageBaseRing S ⟶ P.extension) :
    freeAlgebraSheaf X.J (inverseImageBaseRing S) P.generators ⟶ P.extension :=
  canonicalPresentation X.J (inverseImageBaseRing S) P.extension base

/-- The presentation `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` attached to `α`. -/
abbrev presentation :
    freeAlgebraSheaf X.J (inverseImageBaseRing S) P.generators ⟶ X.O :=
  Stacks.SheafOfModules.presentation X.J (inverseImageBaseRing S) X.O
    S.f.fSharpInverseImage P.generators P.generatorsMap

/-- **Stacks Project, Tag 0GQ6**, the commutative diagram: `α'` followed by the reduction
`𝒪' ⟶ 𝒪` is the presentation attached to `α`. -/
@[stacks 0GQ6 "the commutative diagram over 𝒪' ⟶ 𝒪 for ℰ underlying 𝒪' with α' the identity"]
theorem lift_comp_reduction (base : inverseImageBaseRing S ⟶ P.extension)
    (hbase : base ≫ P.reduction = S.f.fSharpInverseImage) :
    P.lift base ≫ P.reduction = P.presentation := by
  have hc : freeAlgebraSheafCoefficientMap X.J (inverseImageBaseRing S) P.generators ≫
      P.lift base = base :=
    canonicalPresentation_comp_coefficientMap X.J (inverseImageBaseRing S) P.extension base
  have hv : freeAlgebraSheafVariable X.J (inverseImageBaseRing S) P.generators ≫
      Functor.whiskerRight ((sheafToPresheaf X.J CommRingCat.{u}).map (P.lift base))
        (forget CommRingCat.{u}) = 𝟙 _ :=
    freeAlgebraSheafVariable_comp_desc X.J (inverseImageBaseRing S) P.extension P.generators
      base (𝟙 _)
  refine freeAlgebraSheaf_hom_ext X.J (inverseImageBaseRing S) X.O P.generators ?_ ?_
  · rw [← Category.assoc, hc, hbase,
      freeAlgebraSheafCoefficientMap_comp_desc X.J (inverseImageBaseRing S) X.O P.generators
        S.f.fSharpInverseImage P.generatorsMap]
  · rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc, hv,
      Category.id_comp,
      freeAlgebraSheafVariable_comp_desc X.J (inverseImageBaseRing S) X.O P.generators
        S.f.fSharpInverseImage P.generatorsMap]
    rfl

/-- **Stacks Project, Tag 0GQ6**, surjectivity of `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪`: the variables of the free
algebra are all the local sections of `𝒪'`, and they already cover `𝒪` because the reduction
does. -/
@[stacks 0GQ6 "surjectivity of f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪, which is what makes NL(α) defined"]
instance presentation_isLocallySurjective :
    Presheaf.IsLocallySurjective X.J P.presentation.hom := by
  have : Presheaf.IsLocallySurjective X.J P.generatorsMap :=
    (Presheaf.isLocallySurjective_iff_whisker_forget X.J P.reduction.hom).mp
      P.locallySurjective
  have := Presheaf.isLocallySurjective_of_isLocallySurjective_fac X.J
    (freeAlgebraSheafVariable_comp_desc X.J (inverseImageBaseRing S) X.O P.generators
      S.f.fSharpInverseImage P.generatorsMap)
  exact (Presheaf.isLocallySurjective_iff_whisker_forget X.J P.presentation.hom).mpr
    (by assumption)

/-- **Stacks Project, Tag 0GQ6**, the choice the source makes is possible: there are a sheaf of
sets `ℰ` and maps `α' : ℰ ⟶ 𝒪'`, `α : ℰ ⟶ 𝒪` forming a commutative triangle over the reduction
`𝒪' ⟶ 𝒪` for which `f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪` is surjective. The witness is the source's own: `ℰ` is the
sheaf of sets underlying `𝒪'` and `α'` is the identity. -/
@[stacks 0GQ6 "the choice of ℰ with α' : ℰ ⟶ 𝒪' and α : ℰ ⟶ 𝒪 making f⁻¹𝒪_ℬ[ℰ] ⟶ 𝒪 surjective"]
theorem exists_generators :
    ∃ (E : Functor X.Cᵒᵖ (Type u)) (α' : E ⟶ underlyingPresheaf X.J P.extension)
      (α : E ⟶ underlyingPresheaf X.J X.O),
      α' ≫ Functor.whiskerRight P.reduction.hom (forget CommRingCat.{u}) = α ∧
        Presheaf.IsLocallySurjective X.J
          (Stacks.SheafOfModules.presentation X.J (inverseImageBaseRing S) X.O
            S.f.fSharpInverseImage E α).hom :=
  ⟨P.generators, 𝟙 _, P.generatorsMap, Category.id_comp _, P.presentation_isLocallySurjective⟩

/-! ### The map out of the conormal sheaf of the presentation -/

/-- A local relation of the presentation is carried by `α'` into the square-zero ideal. -/
theorem lift_mem_kernelIdeal (base : inverseImageBaseRing S ⟶ P.extension)
    (hbase : base ≫ P.reduction = S.f.fSharpInverseImage) (U : X.Cᵒᵖ)
    (h : kernelIdeal P.presentation.hom U) :
    ((P.lift base).hom.app U).hom h.1 ∈ kernelIdeal P.reduction.hom U :=
  kernelIdeal_le_comap P.presentation.hom P.reduction.hom (P.lift base).hom
    (hom_of_comp_eq (P.lift_comp_reduction base hbase)) U h.2

/-- The map `𝒥(U) ⟶ 𝒢(U)` on sections determined by `α'`: apply `α'`, then read the result in
the square-zero ideal. -/
def idealRestriction (base : inverseImageBaseRing S ⟶ P.extension)
    (hbase : base ≫ P.reduction = S.f.fSharpInverseImage) :
    IdealRestriction.{u, u, u, u} P.presentation S.G where
  app U :=
    { toFun := fun h ↦ P.kernelIdentification.app U
        ⟨((P.lift base).hom.app U).hom h.1, P.lift_mem_kernelIdeal base hbase U h⟩
      map_zero' :=
        Eq.trans
          (congrArg (P.kernelIdentification.app U)
            (Subtype.ext (map_zero ((P.lift base).hom.app U).hom)))
          (map_zero (P.kernelIdentification.app U))
      map_add' := fun h h' ↦
        Eq.trans
          (congrArg (P.kernelIdentification.app U)
            (Subtype.ext (map_add ((P.lift base).hom.app U).hom _ _)))
          (map_add (P.kernelIdentification.app U) _ _) }
  app_smul U r h :=
    Eq.trans
      (congrArg (P.kernelIdentification.app U)
        (Subtype.ext (map_mul ((P.lift base).hom.app U).hom r h.1)))
      (Eq.trans (P.kernelIdentification.app_smul U (((P.lift base).hom.app U).hom r) _)
        (congrArg
          (· • P.kernelIdentification.app U
            ⟨((P.lift base).hom.app U).hom h.1, P.lift_mem_kernelIdeal base hbase U h⟩)
          (congrArg (fun t : _ ⟶ X.O ↦ (t.hom.app U).hom r)
            (P.lift_comp_reduction base hbase))))
  app_map {U V} i h := by
    refine Eq.trans ?_
      (P.kernelIdentification.app_map i
        ⟨((P.lift base).hom.app U).hom h.1, P.lift_mem_kernelIdeal base hbase U h⟩)
    refine congrArg (P.kernelIdentification.app V) (Subtype.ext ?_)
    exact NatTrans.naturality_apply (P.lift base).hom i h.1

/-- On a local relation `h` of the presentation the restriction datum is `α'(h)`, read in the
square-zero ideal and carried to `𝒢`. -/
theorem idealRestriction_app (base : inverseImageBaseRing S ⟶ P.extension)
    (hbase : base ≫ P.reduction = S.f.fSharpInverseImage) (U : X.Cᵒᵖ)
    (h : kernelIdeal P.presentation.hom U) :
    (P.idealRestriction base hbase).app U h =
      P.kernelIdentification.app U
        ⟨((P.lift base).hom.app U).hom h.1, P.lift_mem_kernelIdeal base hbase U h⟩ :=
  rfl

/-- **Stacks Project, Tag 0GQ6**, the map `𝒥/𝒥² ⟶ 𝒢` determined by `α'`. -/
@[stacks 0GQ6 "the map 𝒥/𝒥² ⟶ 𝒢 determined by α'"]
abbrev conormalToIdeal (base : inverseImageBaseRing S ⟶ P.extension)
    (hbase : base ≫ P.reduction = S.f.fSharpInverseImage) :
    conormalSheaf.{u, u, u, u} X.J
        (freeAlgebraSheaf X.J (inverseImageBaseRing S) P.generators) X.O P.presentation ⟶
      S.G :=
  conormalDesc.{u, u, u, u} P.presentation S.G (P.idealRestriction base hbase)

/-! ### The identification with the naive cotangent complex, and the Ext class -/

section Derived

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- `NL(α)`, the naive cotangent complex of the presentation attached to the extension. -/
abbrev naiveCotangentComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex.{u, u, u, u} X.J
    (inverseImageBaseRing S) X.O S.f.fSharpInverseImage P.generators P.generatorsMap

/-- The identification `NL(α) ≅ NL_{𝒪/𝒪_ℬ}` in `D(𝒪)` that a quasi-isomorphic canonical
comparison map of the presentation gives.

The quasi-isomorphy `hq` is a hypothesis here. It is **Stacks 08TY**, which supplies it on every
site as `Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison_site`. -/
def naiveCotangentIso
    (hq : QuasiIso (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u} X.J
      (inverseImageBaseRing S) X.O S.f.fSharpInverseImage P.generators P.generatorsMap)) :
    DerivedCategory.Q.obj P.naiveCotangentComplex ≅
      DerivedCategory.Q.obj (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
        (inverseImageBaseRing S) X.O S.f.fSharpInverseImage) :=
  haveI : IsIso (DerivedCategory.Q.map
      (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u} X.J
        (inverseImageBaseRing S) X.O S.f.fSharpInverseImage P.generators P.generatorsMap)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  asIso (DerivedCategory.Q.map
    (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u} X.J
      (inverseImageBaseRing S) X.O S.f.fSharpInverseImage P.generators P.generatorsMap))

/-- **Stacks Project, Tag 0GQ6**, the class in `Ext¹_𝒪(NL(α), 𝒢)` that `α'` determines: the
first Ext class of the map `𝒥/𝒥² ⟶ 𝒢`. -/
@[stacks 0GQ6 "the class in Ext¹_𝒪(NL(α), 𝒢) that α' determines through the map 𝒥/𝒥² ⟶ 𝒢"]
def extClass (base : inverseImageBaseRing S ⟶ P.extension)
    (hbase : base ≫ P.reduction = S.f.fSharpInverseImage) :
    DerivedCategory.Ext (DerivedCategory.Q.obj P.naiveCotangentComplex)
      ((DerivedCategory.singleFunctor _ 0).obj S.G) 1 :=
  Stacks.SheafOfModules.presentationConormalExtClass.{u, u, u, t} X.J (inverseImageBaseRing S)
    X.O S.f.fSharpInverseImage P.generators P.generatorsMap S.G
    (P.conormalToIdeal base hbase)

end Derived

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
