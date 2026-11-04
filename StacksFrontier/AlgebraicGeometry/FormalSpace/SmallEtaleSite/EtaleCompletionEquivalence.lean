module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleRigidityOverColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.McQuillanAffineEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumEtaleCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjectiveSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductFibreProductSupplement

/-!
# Stacks 0AN8: the equivalence of categories

Let `S` be a scheme contained in a big fppf site `B` and let `Y = Spf R` be a McQuillan affine
formal algebraic space over `S`, so `R` is a weakly admissible topological ring presented over
`S` by a quotient system `D` whose atlas lies in the site. **Stacks 0AN8** asserts an
equivalence between

1. the category of morphisms `X ⟶ Spf R` of affine formal algebraic spaces which are
   representable by algebraic spaces and étale, and
2. the category of topological `R`-algebras `A^∧ = lim A/JA`, for `A` an étale `R`-algebra and
   `J` running over the weak ideals of definition of `R`,

given by sending `A^∧` to `X = Spf (A^∧)`; in particular every `X` as in (1) is McQuillan.

This file constructs that functor and proves it is an equivalence.

## Main definitions

* `AlgebraicGeometry.FormalSpace.EtaleCompletion.quotientSystem` and
  `AlgebraicGeometry.FormalSpace.EtaleCompletion.structureHom`: the quotient system over `S` of
  the completion `A^∧` of an object of category (2), and the canonical map `R → A^∧` as a
  continuous homomorphism over `S` into it. Both are
  `AlgebraicGeometry.FormalSpace.completionOverQuotientSystem` and
  `AlgebraicGeometry.FormalSpace.completionOverContinuousHomWithCanonicalMap` of Stacks 0ANM,
  specialized to the étale ring map naming the object.
* `AlgebraicGeometry.FormalSpace.EtaleCompletion.chart`: the object `Spf (A^∧) ⟶ Spf R` of
  category (1) attached to an object of category (2).
* `AlgebraicGeometry.FormalSpace.etaleCompletionCharts`: **Stacks 0AN8**, the functor from the
  opposite of category (2) to category (1).

## Main results

* `AlgebraicGeometry.FormalSpace.QuotientSystem.eq_of_continuousHom`: a quotient system over `S`
  receiving a continuous homomorphism from a fixed one is determined by the underlying ring map
  of that homomorphism. This is what makes
  `AlgebraicGeometry.FormalSpace.EtaleCompletion.quotientSystem` *the* quotient system of
  `A^∧` rather than one of many, and it is what matches the quotient system produced by the
  essential-surjectivity clause against it.
* `AlgebraicGeometry.FormalSpace.faithful_etaleCompletionCharts`,
  `AlgebraicGeometry.FormalSpace.full_etaleCompletionCharts` and
  `AlgebraicGeometry.FormalSpace.essSurj_etaleCompletionCharts`: the three clauses.
* `AlgebraicGeometry.FormalSpace.isEquivalence_etaleCompletionCharts`: **Stacks 0AN8**, the
  functor is an equivalence of categories, and every object of category (1) is McQuillan.

## Implementation notes

The equivalence is realized on the *opposite* of category (2). A morphism of category (2) is a
continuous `R`-algebra homomorphism `A₁^∧ → A₂^∧`, and `Spf` is contravariant, so the functor
`A^∧ ↦ Spf (A^∧)` reverses arrows; Stacks 0DEF writes the same identification with the opposite
on the geometric side, as `(X_{affine,étale})^{opp}`. Taking the opposite on the algebra side
instead keeps the object map of the tag — `A^∧ ↦ Spf (A^∧)` — on the nose.

The hypotheses carried are the source's. The quotient system `D` is how this library makes `R` a
topological ring over `S` at all: the structure morphisms of the quotients `Spec (R ⧸ J) ⟶ S`
are data here, where the source has them from `R` being a topological `S`-algebra, and without
them `Spf R` is not defined. Its large-site condition `QuotientSystem.HasLargeSite` — that the
chosen big fppf site contain the atlas `∐_J Spec (R ⧸ J)` — is the content of "`Spf R` is an
affine formal algebraic space": it is exactly what Stacks 0AIF consumes
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`), and the source
has it from the same place, its sites being indexed by a cutoff it is free to enlarge. It is a
condition on the *site*, not on `R`; through Stacks 0ANM it passes to every `A^∧`, so it is the
only size hypothesis carried. In particular no bound on the cardinality of `R` is assumed: a
bound `#R < B.cutoff` implies it,
`AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff`, but is strictly stronger and is
a restriction on the ring rather than on the site.

The three clauses are proved as follows:

* the object map lands in category (1) because `Spf (A^∧)` is an affine formal algebraic space
  (Stacks 0AIF) and `Spf (A^∧) ⟶ Spf R` is representable by algebraic spaces (Stacks 0ANM) and
  étale after every represented base change
  (`AlgebraicGeometry.FormalSpace.relative_etale_formalSpectrumMap_completionOver`, which is
  Stacks 0AN8 proved first, out of the ring-theoretic first step
  `TopologicalRing.etale_quotientMap_weakIdealOfDefinition`). The last is stated as a relative
  morphism property, and
  `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_relative_etale'` reads it back as
  condition (2) of Definition 0AIM.
* full faithfulness is Stacks 0AN0,
  `AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`: a morphism
  `Spf (A₂^∧) ⟶ Spf (A₁^∧)` is `Spf` of a unique continuous homomorphism over `S`, and the
  uniqueness clause applied over `Spf R` turns the compatibility with the morphisms to `Spf R`
  into `R`-linearity of that homomorphism, which is precisely what a morphism of category (2)
  is.
* essential surjectivity is
  `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf'`, whose output is an étale
  `R`-algebra `A` together with *some* quotient system on `A^∧` receiving the canonical map;
  `QuotientSystem.eq_of_continuousHom` identifies it with
  `EtaleCompletion.quotientSystem`, and `continuousHom_ext` identifies the two continuous
  homomorphisms, so the isomorphism produced there is an isomorphism onto the value of the
  functor.

The McQuillan conclusion is read off essential surjectivity: the source of an object of
category (1) is isomorphic to `Spf (A^∧)` for an étale `R`-algebra `A`, and `A^∧` is weakly
admissible by `TopologicalRing.completionOver_isWeaklyAdmissible`.

Composing this equivalence with Stacks 0DEE,
`AlgebraicGeometry.FormalSpace.affineEtaleEquivalence`, gives Stacks 0DEF, the identification of
category (2) with the opposite of the affine étale site of the reduction of `Spf R`; that is
`AlgebraicGeometry.FormalSpace.mcQuillanAffineEtaleEquivalence`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0DEF](https://stacks.math.columbia.edu/tag/0DEF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### A quotient system is determined by a continuous homomorphism into it -/

section Uniqueness

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]

/-- Two quotient systems over `S` on the same topological ring with the same structure
morphisms are equal: the remaining two fields are propositions. -/
theorem QuotientSystem.ext_overS {E E' : QuotientSystem B S hS C}
    (h : E.overS = E'.overS) : E = E' := by
  cases E
  cases E'
  cases h
  rfl

/-- **A quotient system over `S` is determined by a continuous homomorphism into it.** If two
quotient systems on `C` receive continuous homomorphisms over `S` from one and the same quotient
system on a weakly admissible `A`, and the two homomorphisms have the same underlying ring map,
then the two quotient systems are equal.

Each weak ideal of definition `K` of `C` has a weak ideal of definition `J` of `A` inside its
preimage, and the compatibility condition on a continuous homomorphism over `S` then *computes*
the structure morphism at `K` as `Spec (A ⧸ J → C ⧸ K)` followed by the structure morphism of
`A` at `J`. So the structure morphisms of the target are not a choice at all. -/
theorem QuotientSystem.eq_of_continuousHom [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E E' : QuotientSystem B S hS C} (f : ContinuousHom D E) (f' : ContinuousHom D E')
    (h : f.toRingHom = f'.toRingHom) : E = E' := by
  refine QuotientSystem.ext_overS (funext fun K ↦ ?_)
  obtain ⟨J, hJ⟩ :=
    exists_isWeakIdealOfDefinition_le_comap hA.1 f.toRingHom f.continuous K
  have hJ' : J.1 ≤ Ideal.comap f'.toRingHom K.1 := by
    rw [← h]; exact hJ
  have hq : Ideal.quotientMap K.1 f.toRingHom hJ =
      Ideal.quotientMap K.1 f'.toRingHom hJ' := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    show Ideal.Quotient.mk K.1 (f.toRingHom a) = Ideal.Quotient.mk K.1 (f'.toRingHom a)
    rw [h]
  rw [← f.overS J K hJ, ← f'.overS J K hJ', hq]

end Uniqueness

/-! ### The object of category (1) attached to an object of category (2) -/

namespace EtaleCompletion

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R] (hR : TopologicalRing.IsWeaklyAdmissible R)
  (D : QuotientSystem B S hS R) (hD : D.HasLargeSite)

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] in
/-- The underlying étale ring map of an object of category (2) is of finite type, so the
statements of Stacks 0ANM apply to its relative completion. -/
theorem finiteType_str (Y : EtaleCompletion R) : Y.str.FiniteType :=
  finiteType_of_etale Y.str Y.etale

/-- The quotient system over `S` of the completion `A^∧` of an object of category (2): the one
Stacks 0ANM attaches to the étale ring map naming the object, which is determined by the
quotient system `D` of the base and the canonical map `R → A^∧`, by
`AlgebraicGeometry.FormalSpace.QuotientSystem.eq_of_continuousHom`. -/
def quotientSystem (Y : EtaleCompletion R) : QuotientSystem B S hS Y.completion :=
  completionOverQuotientSystem' B S hS Y.str Y.finiteType_str hR D
    hD

/-- The canonical map `R → A^∧` of an object of category (2), as a continuous homomorphism of
topological rings over `S`. This is the `R`-algebra structure the object carries. -/
def structureHom (Y : EtaleCompletion R) :
    ContinuousHom D (Y.quotientSystem hR D hD) :=
  (completionOverContinuousHomWithCanonicalMap B S hS Y.str Y.finiteType_str hR D
    hD).1

/-- The underlying ring map of `AlgebraicGeometry.FormalSpace.EtaleCompletion.structureHom` is
the canonical map `R → A^∧`, which is the structure map of the object. -/
theorem structureHom_toRingHom (Y : EtaleCompletion R) :
    (Y.structureHom hR D hD).toRingHom = Y.structureMap :=
  (completionOverContinuousHomWithCanonicalMap B S hS Y.str Y.finiteType_str hR D
    hD).2

/-- The large-site condition passes from the base to the completion of an object of
category (2), by Stacks 0ANM. -/
theorem hasLargeSite_quotientSystem (Y : EtaleCompletion R) :
    (Y.quotientSystem hR D hD).HasLargeSite :=
  hasLargeSite_completionOver_of_finiteType B S hS Y.str Y.finiteType_str
    hD _

/-- **Stacks 0AIF** for the completion of an étale algebra: `Spf (A^∧)` is an affine formal
algebraic space over `S`. -/
theorem isAffineFormalAlgebraicSpace_formalSpectrum_quotientSystem (Y : EtaleCompletion R) :
    IsAffineFormalAlgebraicSpace B S hS (formalSpectrum (Y.quotientSystem hR D hD)) :=
  isAffineFormalAlgebraicSpace_formalSpectrum (Y.isWeaklyAdmissible_completion hR) _
    (Y.hasLargeSite_quotientSystem hR D hD)

/-- **The morphism `Spf (A^∧) ⟶ Spf R` of an object of category (2) is representable by
algebraic spaces and étale**, that is, it satisfies condition (2) of Definition 0AIM.
Representability is Stacks 0ANM and étaleness after every represented base change is the half of
Stacks 0AN8 the source proves first. -/
theorem isRepresentableEtale_formalSpectrumMap_structureHom (Y : EtaleCompletion R) :
    IsRepresentableEtale B S hS (formalSpectrumMap hR (Y.structureHom hR D hD)) :=
  isRepresentableEtale_of_relative_etale' B S hS _
    (relative_etale_formalSpectrumMap_completionOver hR Y.str Y.etale D
      hD (Y.quotientSystem hR D hD)
      (Y.structureHom hR D hD) (Y.structureHom_toRingHom hR D hD))

/-- The object `Spf (A^∧) ⟶ Spf R` of category (1) of Stacks 0AN8 attached to an object `A^∧`
of category (2). -/
def chart (Y : EtaleCompletion R) : AffineEtaleFormalCharts B S hS (formalSpectrum D) :=
  ⟨Over.mk (formalSpectrumMap hR (Y.structureHom hR D hD)),
    Y.isAffineFormalAlgebraicSpace_formalSpectrum_quotientSystem hR D hD,
    Y.isRepresentableEtale_formalSpectrumMap_structureHom hR D hD⟩

/-- A morphism `A₁^∧ → A₂^∧` of category (2), read as a continuous homomorphism of the quotient
systems over `S` of the two completions. Being a homomorphism of `R`-algebras is exactly the
compatibility `AlgebraicGeometry.FormalSpace.ContinuousHom.ofComp'` consumes. -/
def chartHom {Y Z : EtaleCompletion R} (φ : Y ⟶ Z) :
    ContinuousHom (Y.quotientSystem hR D hD) (Z.quotientSystem hR D hD) :=
  ContinuousHom.ofComp' hR (Y.structureHom hR D hD) (Z.structureHom hR D hD)
    φ.toRingHom φ.continuous_toRingHom (by
      rw [Z.structureHom_toRingHom hR D hD, Y.structureHom_toRingHom hR D hD]
      exact φ.comp_structureMap.symm)

/-- The underlying ring map of `chartHom φ` is that of `φ`. -/
@[simp]
theorem chartHom_toRingHom {Y Z : EtaleCompletion R} (φ : Y ⟶ Z) :
    (chartHom hR D hD φ).toRingHom = φ.toRingHom :=
  rfl

/-- The morphism of category (1) induced by a morphism of category (2): on formal spectra the
latter goes the other way, and the triangle over `Spf R` is the composition law for `Spf`. -/
def chartMap {Y Z : EtaleCompletion R} (φ : Y ⟶ Z) :
    Z.chart hR D hD ⟶ Y.chart hR D hD :=
  ObjectProperty.homMk (Over.homMk
    (formalSpectrumMap (Y.isWeaklyAdmissible_completion hR) (chartHom hR D hD φ))
    (formalSpectrumMap_comp hR (Y.isWeaklyAdmissible_completion hR)
      (Y.structureHom hR D hD) (chartHom hR D hD φ) (Z.structureHom hR D hD) (by
        rw [Z.structureHom_toRingHom hR D hD, chartHom_toRingHom,
          Y.structureHom_toRingHom hR D hD]
        exact φ.comp_structureMap.symm)))

end EtaleCompletion

/-! ### Stacks 0AN8: the functor and the equivalence -/

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R] (hR : TopologicalRing.IsWeaklyAdmissible R)
  (D : QuotientSystem B S hS R) (hD : D.HasLargeSite)

/-- **Stacks 0AN8**, the functor. From the opposite of the category of the topological
`R`-algebras `A^∧ = lim A/JA`, for `A` an étale `R`-algebra, to the category of the morphisms
`X ⟶ Spf R` of affine formal algebraic spaces which are representable by algebraic spaces and
étale. On objects it is `A^∧ ↦ Spf (A^∧)` with its canonical morphism to `Spf R`; on morphisms
it is `Spf` of a continuous `R`-algebra homomorphism of completions, which is why the source is
the opposite category. -/
def etaleCompletionCharts :
    (EtaleCompletion R)ᵒᵖ ⥤ AffineEtaleFormalCharts B S hS (formalSpectrum D) where
  obj Y := Y.unop.chart hR D hD
  map {_Y _Z} φ := EtaleCompletion.chartMap hR D hD φ.unop
  map_id Y := ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (formalSpectrumMap_id (Y.unop.isWeaklyAdmissible_completion hR) _ rfl))
  map_comp {_Y Z W} φ ψ := ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (formalSpectrumMap_comp (W.unop.isWeaklyAdmissible_completion hR)
      (Z.unop.isWeaklyAdmissible_completion hR) (EtaleCompletion.chartHom hR D hD ψ.unop)
      (EtaleCompletion.chartHom hR D hD φ.unop)
      (EtaleCompletion.chartHom hR D hD (ψ.unop ≫ φ.unop)) rfl).symm)

/-- On the underlying formal spaces, `etaleCompletionCharts` sends a morphism to `Spf` of the
continuous homomorphism `chartHom` it induces. -/
@[simp]
theorem etaleCompletionCharts_map_hom_left {Y Z : (EtaleCompletion R)ᵒᵖ} (φ : Y ⟶ Z) :
    ((etaleCompletionCharts hR D hD).map φ).hom.left =
      formalSpectrumMap (Z.unop.isWeaklyAdmissible_completion hR)
        (EtaleCompletion.chartHom hR D hD φ.unop) :=
  rfl

/-- **Stacks 0AN8** is faithful. Two morphisms of category (2) with the same `Spf` are equal,
by the uniqueness clause of Stacks 0AN0. -/
theorem faithful_etaleCompletionCharts : (etaleCompletionCharts hR D hD).Faithful where
  map_injective {Y Z} {φ ψ} h := by
    refine Quiver.Hom.unop_inj (EtaleCompletion.Hom.ext ?_)
    have h' : formalSpectrumMap (Z.unop.isWeaklyAdmissible_completion hR)
          (EtaleCompletion.chartHom hR D hD φ.unop) =
        formalSpectrumMap (Z.unop.isWeaklyAdmissible_completion hR)
          (EtaleCompletion.chartHom hR D hD ψ.unop) :=
      congrArg (fun m ↦ m.hom.left) h
    have huniq := existsUnique_continuousHom_formalSpectrumMap_eq
      (Z.unop.isWeaklyAdmissible_completion hR) (Y.unop.isWeaklyAdmissible_completion hR)
      (formalSpectrumMap (Z.unop.isWeaklyAdmissible_completion hR)
        (EtaleCompletion.chartHom hR D hD φ.unop))
    exact congrArg ContinuousHom.toRingHom
      ((huniq.unique rfl h'.symm : EtaleCompletion.chartHom hR D hD φ.unop = _))

/-- **Stacks 0AN8** is full. A morphism `Spf (A₂^∧) ⟶ Spf (A₁^∧)` over `Spf R` is `Spf` of a
unique continuous homomorphism over `S` by Stacks 0AN0, and the uniqueness clause over `Spf R`
forces that homomorphism to be a homomorphism of `R`-algebras, hence a morphism of
category (2). -/
theorem full_etaleCompletionCharts : (etaleCompletionCharts hR D hD).Full where
  map_surjective {Y Z} m := by
    obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq
      (Z.unop.isWeaklyAdmissible_completion hR) (Y.unop.isWeaklyAdmissible_completion hR)
      m.hom.left
    -- `g` is a homomorphism of `R`-algebras, by the uniqueness clause over `Spf R`
    have hcomp : (ContinuousHom.comp (Z.unop.isWeaklyAdmissible_completion hR) hR g
        (Z.unop.structureHom hR D hD)) = Y.unop.structureHom hR D hD := by
      refine ((existsUnique_continuousHom_formalSpectrumMap_eq hR
        (Y.unop.isWeaklyAdmissible_completion hR)
        (formalSpectrumMap hR (Y.unop.structureHom hR D hD))).unique ?_ rfl)
      rw [← formalSpectrumMap_comp hR (Z.unop.isWeaklyAdmissible_completion hR)
        (Z.unop.structureHom hR D hD) g _ rfl, hg]
      exact m.hom.w
    have hR' : g.toRingHom.comp Z.unop.structureMap = Y.unop.structureMap := by
      rw [← Y.unop.structureHom_toRingHom hR D hD, ← hcomp,
        ← Z.unop.structureHom_toRingHom hR D hD]
      rfl
    set φ : Z.unop ⟶ Y.unop := ⟨g.toRingHom, g.continuous, hR'⟩
    have hchart : EtaleCompletion.chartHom hR D hD φ = g := continuousHom_ext' rfl
    refine ⟨Opposite.op φ, ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)⟩
    show formalSpectrumMap (Z.unop.isWeaklyAdmissible_completion hR)
      (EtaleCompletion.chartHom hR D hD φ) = m.hom.left
    rwa [hchart]

/-- **Stacks 0AN8** is essentially surjective: every morphism `X ⟶ Spf R` of affine formal
algebraic spaces which is representable by algebraic spaces and étale is `Spf` of the completion
of an étale `R`-algebra, compatibly with the morphisms to `Spf R`. -/
theorem essSurj_etaleCompletionCharts : (etaleCompletionCharts hR D hD).EssSurj where
  mem_essImage W := by
    obtain ⟨A, instA, instAlg, instEt, E, c, ε, hc, hε⟩ :=
      isEssentiallySurjectiveSpf' B S hS R hR D hD W.obj.left W.obj.hom W.property.1
        W.property.2
    let := instA
    let := instAlg
    let := instEt
    let Y : EtaleCompletion R :=
      { carrier := A
        str := algebraMap R A
        etale := RingHom.etale_algebraMap.mpr instEt }
    have hc' := hc.trans (Y.structureHom_toRingHom hR D hD).symm
    have hEq : E = Y.quotientSystem hR D hD :=
      QuotientSystem.eq_of_continuousHom hR c (Y.structureHom hR D hD) hc'
    subst hEq
    have hcEq : c = Y.structureHom hR D hD := continuousHom_ext' hc'
    refine ⟨Opposite.op Y, ⟨(IsAffineEtaleFormalChart B S hS
      (formalSpectrum D)).fullyFaithfulι.preimageIso (Over.isoMk ε.symm ?_)⟩⟩
    rw [Iso.symm_hom]
    show ε.inv ≫ W.obj.hom = formalSpectrumMap hR (Y.structureHom hR D hD)
    rw [← hε, ← hcEq, Iso.inv_hom_id_assoc]

/-- **Stacks 0AN8.** Let `S` be a scheme contained in a big fppf site `B` and let `R` be a
weakly admissible topological ring presented over `S` by a quotient system `D` whose atlas
`∐_J Spec (R ⧸ J)` lies in the site, so that `Y = Spf R` is a McQuillan affine formal algebraic
space over `S`. Then the functor sending an étale `R`-algebra `A` to the morphism
`Spf (A^∧) ⟶ Spf R` is an equivalence between the opposite of the category of the topological
`R`-algebras `A^∧ = lim A/JA` and the category of the morphisms `X ⟶ Spf R` of affine formal
algebraic spaces which are representable by algebraic spaces and étale; in particular every
such `X` is McQuillan, being `Spf` of the weakly admissible topological ring `A^∧`.

The hypotheses are the source's. The quotient system `D` is how this library says that `R` is a
topological `S`-algebra — the structure morphisms `Spec (R ⧸ J) ⟶ S` are data here, where the
source has them from `R` being a topological `S`-algebra — and without it `Spf R` is not
defined. Its large-site condition `D.HasLargeSite` says that the chosen big fppf site contains
the atlas of `Spf R`, which is what Stacks 0AIF needs to make `Spf R` an affine formal algebraic
space at all; so it is part of the hypothesis that `Y` is one, and it is a condition on the site
rather than on `R`. Through Stacks 0ANM it passes to every `A^∧` with nothing further
assumed. -/
@[stacks 0AN8 "the equivalence of categories, with the functor `A^∧ ↦ Spf (A^∧)` and the \
McQuillan conclusion. The equivalence is realized on the opposite of the category of the \
algebras `A^∧`, a morphism of that category being a continuous `R`-algebra homomorphism and \
`Spf` being contravariant; Stacks 0DEF writes the same identification with the opposite taken \
on the geometric side, and `mcQuillanAffineEtaleEquivalence` moves it there. The quotient \
system `D` is how this library says that `R` is a topological `S`-algebra, the structure \
morphisms of the quotient spectra being data here, and without it `Spf R` is not defined; its \
large-site condition `QuotientSystem.HasLargeSite` says that the chosen big fppf site contains \
the atlas of `Spf R`, which is what Stacks 0AIF consumes to make `Spf R` an affine formal \
algebraic space, so it is part of the source's hypothesis that `Y` is one, and is a condition \
on the site rather than on `R`. It passes to every `A^∧` through Stacks 0ANM. No bound on the \
cardinality of `R` is assumed"]
theorem isEquivalence_etaleCompletionCharts :
    (etaleCompletionCharts hR D hD).IsEquivalence ∧
      ∀ W : AffineEtaleFormalCharts B S hS (formalSpectrum D),
        ∃ Y : EtaleCompletion R,
          TopologicalRing.IsWeaklyAdmissible Y.completion ∧
            Nonempty (W.obj.left ≅ formalSpectrum (Y.quotientSystem hR D hD)) := by
  let := faithful_etaleCompletionCharts hR D hD
  let := full_etaleCompletionCharts hR D hD
  let := essSurj_etaleCompletionCharts hR D hD
  refine ⟨{ faithful := inferInstance, full := inferInstance, essSurj := inferInstance }, ?_⟩
  intro W
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := etaleCompletionCharts hR D hD) W
  exact ⟨Y.unop, Y.unop.isWeaklyAdmissible_completion hR,
    ⟨(Over.forget (formalSpectrum D)).mapIso
      ((IsAffineEtaleFormalChart B S hS (formalSpectrum D)).ι.mapIso e.symm)⟩⟩

end AlgebraicGeometry.FormalSpace

end
