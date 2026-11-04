module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximationComplete
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.TangentSpace.Functor
public import StacksFrontier.RingTheory.GRing.EssFiniteType

/-!
# The reduction of Stacks 0DLN to the results it uses

Stacks 0DLN asserts that for a proper, flat, finitely presented morphism `f : X ⟶ B` of algebraic
spaces over a scheme `S`, the category `Complexes_{X/B}` of Stacks 0DLE is an algebraic stack over
`S`.  Its proof

1. reduces to `B` a scheme (Remark 0DLI and Section 03YJ), then to `S = B` (Section 04X4), then to
   `S = B` affine, and then, writing `S = Spec Λ` with `Λ` a filtered colimit of finite type
   `ℤ`-algebras and descending `X` (Stacks 07SK, 08K0, 08K1), to `S = B = Spec Λ` with `Λ` of
   finite type over `ℤ` (Remark 0DLI and Section 04X4 again);
2. in that case applies Artin's criterion, Stacks 07Y4, whose hypotheses are Lemmas 0DLG (the
   diagonal), 0DLH (the stack condition), 0DLJ (limit preservation), 0DLK (the condition (RS*),
   hence (RS)), 0DLL (finite dimensional tangent spaces), 0DLM together with Stacks 0CXU
   (effectiveness of formal objects and openness of versality), and Stacks 07PX (the local rings
   of `S` are G-rings).

None of the results named is yet available unconditionally, except Stacks 07PX.  This file states
the two steps with the missing results as explicit hypotheses, each stated at the content of the
tag it waits for, so that Stacks 0DLN follows by supplying them.  Nothing here is registered.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.complexesBasedCategory`: `Complexes_{X/B}` as a
  category over the big fppf site of `S`, with the projection `p` of Stacks 0DLE.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`: step 2.  The
  G-ring hypothesis (5) of Stacks 07Y4 is discharged here, from Stacks 07PX; the others are
  hypotheses named by the tag that supplies each.
* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_reduction`: steps 1 and 2
  together.

## Implementation notes

The hypothesis `h07Y4` is Stacks 07Y4 at the base `Spec Λ`, in the form in which the criterion is
stated: the diagonal representable by algebraic spaces, the set
theoretic bound on isomorphism classes of axiom [-1], the étale stack condition of axiom [0],
limit preservation (Stacks 07XL), (RS) (Stacks 07WP), finite dimensionality of tangent spaces
(axiom [3]), effectiveness of formal objects (Stacks 07X7), openness of versality (Stacks 07XQ)
and the G-ring condition.  Each is written out rather than named, because the predicates naming
two of them are not yet in the library.

The hypothesis `hsize` is axiom [-1] for `Complexes_{X/B}`, which the source's proof says it
omits.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory

/-- **`Complexes_{X/B}` as a category over `(Sch/S)_fppf`**: the objects
`AlgebraicGeometry.Space.ComplexesObject` of Stacks 0DLE, with the category structure
`AlgebraicGeometry.Space.ComplexesSituation.complexesCategory` and the projection
`p : (T, g, E) ↦ T` of `AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor`. -/
@[reducible]
def complexesBasedCategory (D : ComplexesSituation B S hS) :
    BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) where
  obj := ComplexesObject D
  category := complexesCategory D
  p := complexesFunctor D

/-- The local rings of the spectrum of a finite type `ℤ`-algebra are G-rings, by Stacks 07PX:
`ℤ` is a G-ring, a finite type algebra over a G-ring is a G-ring, and so is each of its
localizations at a prime. -/
theorem isGRing_stalk_of_finiteType_int (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
    (s : Spec (CommRingCat.of Λ)) :
    IsGRing ((Spec (CommRingCat.of Λ)).presheaf.stalk s) :=
  StacksDraft.ArtinApproximation.isGRing_stalk_spec Λ
    (isGRing_basic_examples.{0, u}.2.2.2.2 ℤ Λ isGRing_basic_examples.{0, 0}.2.2.1) s

/-- **Stacks 0DLN, the case `S = Spec Λ` with `Λ` of finite type over `ℤ`, reduced to the results
its proof uses.**  The last paragraph of the source's proof: `Complexes_{X/B}` is an algebraic
stack by Artin's criterion, Stacks 07Y4 (`h07Y4`), whose hypotheses are

* fibred in groupoids: Stacks 0DLF (`h0DLF`);
* (1) the diagonal is representable by algebraic spaces: Stacks 0DLG (`h0DLG`);
* axiom [-1]: `hsize`, omitted by the source;
* axiom [0]: Stacks 0DLH (`h0DLH`), the stack condition, read for the étale topology;
* axiom [1]: Stacks 0DLJ (`h0DLJ`);
* axiom [2]: Stacks 0DLK (`h0DLK`), (RS*) and hence (RS);
* axiom [3]: Stacks 0DLL (`h0DLL`);
* (3) effectiveness of formal objects: Stacks 0DLM (`h0DLM`);
* (4) openness of versality: Stacks 0CXU applied with 0DLG, 0DLK, 0DLJ and 0DLM (`h0CXU`);
* (5) the local rings of `S` at finite type points are G-rings: discharged here, by Stacks 07PX
  (`AlgebraicGeometry.Space.ComplexesSituation.isGRing_stalk_of_finiteType_int`). -/
theorem isAlgebraicStack_of_artinCriterion (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
    {hΛ : B.Contains (Spec (CommRingCat.of Λ))} (D : ComplexesSituation B _ hΛ)
    (h07Y4 : ∀ (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
        (BigFppfOver B (Spec (CommRingCat.of Λ)) hΛ)),
      Stack.HasRepresentableDiagonal B _ hΛ 𝒳 →
      (∃ T : BigFppfOver B _ hΛ,
        ∀ (U : BigFppfOver B _ hΛ) (k : Type u) [Field k],
          U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B _ hΛ U →
          Cardinal.lift.{u, u + 1}
              (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U)))) ≤
            Cardinal.lift.{u + 1, u} T.left.1.size) →
      𝒳.val.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hΛ)) →
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B _ hΛ 𝒳 →
      Deformation.Artin.SatisfiesRS B _ hΛ 𝒳.val.p 𝒳.property →
      (∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ Spec (CommRingCat.of Λ))
          (x₀ : 𝒳.val.obj)
          (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
          LocallyOfFiniteType i₀ → QuasiCompact i₀ →
          ∀ (s : Spec (CommRingCat.of Λ)), i₀ (IsLocalRing.closedPoint k) = s →
          ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
            (_hΛstalk : Λ' = (Spec (CommRingCat.of Λ)).presheaf.stalk s)
            (iΛ : Spec (.of Λ') ⟶ Spec (CommRingCat.of Λ))
            (_hiΛ : HEq iΛ ((Spec (CommRingCat.of Λ)).fromSpecStalk s))
            (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
            let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
              hx₀.trans (congrArg Over.mk hbase.symm)
            let D := Deformation.Artin.predeformationCategory iΛ
              (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
            letI : Category D.carrier := D.category
            ∀ hD : Deformation.IsDeformationCategory D.projection,
              let 𝓕 := BasedCategory.ofFunctor D.projection
              let hS2 :=
              Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                𝓕 hD
              letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
              letI : Fact (Deformation.SchlessingerConditionS2
                (CategoryOfElements.π
                  (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
              let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
              let T := Deformation.artinianTangentSpace Λ' k F
              letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
              letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
              FiniteDimensional k T) →
      (∀ ξ : Deformation.Artin.FormalObject B _ hΛ 𝒳.val.p,
        Deformation.Artin.FormalObject.IsEffective B _ hΛ 𝒳.val.p 𝒳.property ξ) →
      (∀ U : Over (Spec (CommRingCat.of Λ)), LocallyOfFiniteType U.hom →
        ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
          IsFiniteTypePoint u →
          Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
          ∃ V : U.left.Opens, u ∈ V.1 ∧
            ∀ u' : U.left, u' ∈ V.1 → IsFiniteTypePoint u' →
              Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy) →
      (∀ s : Spec (CommRingCat.of Λ), IsFiniteTypePoint s →
        IsGRing ((Spec (CommRingCat.of Λ)).presheaf.stalk s)) →
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ 𝒳.val)
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : Stack.HasRepresentableDiagonal B _ hΛ
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) h0DLF))
    (hsize : ∃ T : BigFppfOver B _ hΛ,
        ∀ (U : BigFppfOver B _ hΛ) (k : Type u) [Field k],
          U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B _ hΛ U →
          Cardinal.lift.{u, u + 1}
              (Cardinal.mk (Quotient (isIsomorphicSetoid ((complexesFunctor D).Fiber U)))) ≤
            Cardinal.lift.{u + 1, u} T.left.1.size)
    (h0DLH : (complexesFunctor D).IsStackInGroupoids.{u + 1}
      ((etaleTopology B).over (B.obj hΛ)))
    (h0DLJ : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B _ hΛ
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) h0DLF))
    (h0DLK : Deformation.Artin.SatisfiesRS B _ hΛ (complexesFunctor D) h0DLF)
    (h0DLL : ∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ Spec (CommRingCat.of Λ))
          (x₀ : ComplexesObject D)
          (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
          LocallyOfFiniteType i₀ → QuasiCompact i₀ →
          ∀ (s : Spec (CommRingCat.of Λ)), i₀ (IsLocalRing.closedPoint k) = s →
          ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
            (_hΛstalk : Λ' = (Spec (CommRingCat.of Λ)).presheaf.stalk s)
            (iΛ : Spec (.of Λ') ⟶ Spec (CommRingCat.of Λ))
            (_hiΛ : HEq iΛ ((Spec (CommRingCat.of Λ)).fromSpecStalk s))
            (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
            let hx : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
              hx₀.trans (congrArg Over.mk hbase.symm)
            let P := Deformation.Artin.predeformationCategory iΛ
              (complexesFunctor D ⋙ Over.post B.inclusion) x₀ hx
            letI : Category P.carrier := P.category
            ∀ hD : Deformation.IsDeformationCategory P.projection,
              let 𝓕 := BasedCategory.ofFunctor P.projection
              let hS2 :=
              Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                𝓕 hD
              letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
              letI : Fact (Deformation.SchlessingerConditionS2
                (CategoryOfElements.π
                  (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
              let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
              let T := Deformation.artinianTangentSpace Λ' k F
              letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
              letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
              FiniteDimensional k T)
    (h0DLM : ∀ ξ : Deformation.Artin.FormalObject B _ hΛ (complexesFunctor D),
      Deformation.Artin.FormalObject.IsEffective B _ hΛ (complexesFunctor D) h0DLF ξ)
    (h0CXU : ∀ U : Over (Spec (CommRingCat.of Λ)), LocallyOfFiniteType U.hom →
      ∀ (y : ComplexesObject D) (hy : (complexesFunctor D ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left), IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u' y
              hy) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D) :=
  h07Y4 (CatFiberedInGroupoids.mk (complexesBasedCategory D) h0DLF) h0DLG hsize h0DLH h0DLJ
    h0DLK h0DLL h0DLM h0CXU (fun s _ => isGRing_stalk_of_finiteType_int Λ s)

/-- **Stacks 0DLN, reduced to the case `S = B = Spec Λ` with `Λ` of finite type over `ℤ`.**  The
first four paragraphs of the source's proof show that `Complexes_{X/B}` is an algebraic stack for
every proper, flat, finitely presented `f : X ⟶ B` over every scheme `S` of the site as soon as it
is for those with `S = Spec Λ`, `Λ` of finite type over `ℤ`, and `B = S`, that is, `B` the final
algebraic space over `S`.  That implication is `hred`.  It waits for

* Remark 0DLI: base change of `Complexes_{X/B}` along `B' ⟶ B` is the 2-fibre product with
  `(Sch/B') ⟶ (Sch/B)`;
* Section 03YJ: for `B' ⟶ B` surjective étale from a scheme, `Complexes_{X'/B'} ⟶ Complexes_{X/B}`
  is surjective and étale, so algebraicity descends;
* Section 04X4: replacing `S` by a scheme `B` over it;
* the covering of `S` by affine opens; and
* Stacks 07SK, 08K0 and 08K1: descending `X ⟶ Spec Λ` to a proper, flat, finitely presented
  morphism over a finite type `ℤ`-algebra, followed by Remark 0DLI and Section 04X4 once more.

The case `hcase` is `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`
for the situations whose base is the final algebraic space. -/
theorem isAlgebraicStack_of_reduction
    (hred : (∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D')) →
      ∀ (S' : Scheme.{u}) (hS' : B.Contains S') (D : ComplexesSituation B S' hS'),
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S' hS' (complexesBasedCategory D))
    (hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D'))
    (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  hred hcase S hS D

end AlgebraicGeometry.Space.ComplexesSituation

end
