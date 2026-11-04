module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PushforwardSections
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictTensorator
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTwisting

/-!
# A pair of Tag 01O4 is a quadruple of Section 01NS

Let `𝒜` be a graded `𝒪_S`-algebra as in Situation 01NN, `f : T ⟶ S` a morphism of schemes, and
`P` a pair of Tag 01O4: an invertible `𝒪_T`-module `L`, a degreewise family
`ψ_n : 𝒜_n ⟶ f_*T(L)_n` into the direct image of the tensor algebra of `L` which is
multiplicative and unital on local sections, and surjectivity of the adjoint transpose in degree
one. `StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleBridge` built from `P` the family
`F1Pair.laurentApp`, which has exactly the shape of the field `app` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting` at `d = 1`, and proved the
surjectivity clause. This file proves the other two clauses and assembles the quadruple.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.laurentHom`: **the homomorphism of sheaves
  of graded algebras `f^*𝒜 ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` a pair determines**, as the adjoint transpose of
  the homomorphism `𝒜 ⟶ f_*(⨁_{n ∈ ℤ} L^{⊗ n})` its data give.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.twisting` and `F1Pair.quadruple`: **the
  twisting and the quadruple of Section 01NS a pair of Tag 01O4 determines**, at `d = 1`.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.laurentApp_app_mul` and
  `laurentApp_app_one`: **the multiplicativity and unit clauses of `Twisting` for the family a
  pair determines.**
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.mulSheaf_pullbackGradedAlgebra`: the morphism-level
  multiplication of `f^*𝒜` is the multiplication of `𝒜` conjugated by the comparison of
  Tag 01CD, which is the shape `Twisting.app_mul` is stated at.

## Implementation notes

**Where the two clauses come from.** The data of a pair are stated on local sections and over
`f ⁻¹ᵁ U`; the clauses of `Twisting` are equations of morphisms over `T`. The passage between
them is in three steps, and each is a lemma that already exists.

First, the multiplication of `f_*(⨁ L^{⊗ n})` on sections over `U` is the multiplication of
`⨁ L^{⊗ n}` over `f ⁻¹ᵁ U`, and likewise for the unit: that is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pushforwardGradedAlgebra_mul_app` and
`pushforwardGradedAlgebra_one_eval`. With those, `F1Pair.map_mul` and the multiplicativity of
`tensorToLaurent` make `psiLaurentHom` a homomorphism of sheaves of graded algebras
`𝒜 ⟶ f_*(⨁ L^{⊗ n})`.

Second, `SheafOfModules.GradedAlgebra.transportHomBackward` transposes that into a homomorphism
out of `f^*𝒜`, degreewise by the hom-set bijection of `f^* ⊣ f_*`; its components are
`F1Pair.pullbackMap` followed by `tensorToLaurent`, which is `F1Pair.laurentApp` up to the
degree identification `n * 1 = n`.

Third, `Twisting.app_mul` is written with `inv (pullbackTensorComparison ..)`, the tensorator of
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, while the transport is for
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`. Those are the same, by
`Stacks.PullbackStrictTensorator.mu_pullbackStrictMonoidal_eq`.

**The degree identification is isolated in two statements with free degrees.**
`laurentApp_app_mul_of_eq` and `laurentApp_app_one_of_eq` take the source degrees as variables
together with the equalities identifying them, so that `subst` turns every `eqToHom` into an
identity and the aligned statements `laurentHom_mulSheaf` and `laurentHom_one` apply directly.
Rewriting `n * 1` to `n` inside the dependent types is not available: `n * 1 = n` is not `rfl`
for an integer.

**No `@[stacks]` attribute.** Tag 01O4 asserts that relative Proj represents the functor of
pairs; a quadruple built from a pair is one direction of the comparison of the two data, not
that representability, and the tag's clauses are carried elsewhere. The quadruple's uniqueness
and the inverse construction are not here.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf AlgebraicGeometry Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackMonoidalSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBridge
open SheafOfModules.GradedAlgebra Stacks.PullbackTensorCoherence

universe u

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal
attribute [local instance] Stacks.PushforwardGradedAlgebra.pushforwardFunctorLaxMonoidal

variable {S T : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (f : T ⟶ S)

/-! ### The morphism-level multiplication of a pulled-back graded algebra -/

/-- **The morphism-level multiplication of `f^*𝒜` is the multiplication of `𝒜` conjugated by the
comparison of Tag 01CD.** `f^*𝒜` is the transport of `𝒜` along the monoidal pullback, so its
multiplication is the lax tensorator of that functor followed by the pullback of the
multiplication of `𝒜`; the tensorator is the inverse comparison by
`Stacks.PullbackStrictTensorator.mu_pullbackStrictMonoidal_eq`. This is the shape
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.app_mul` is stated at. -/
theorem mulSheaf_pullbackGradedAlgebra
    (B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (i j : ℤ) :
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f) B
        (isSheafStruct S)).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (B.piece i) (B.piece j)) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (B.mulSheaf i j) := by
  refine Eq.trans (mulSheaf_transport (pullbackFunctor (ringedSpaceHom f)) B
    (isSheafStruct S) (isSheafStruct T) i j) ?_
  exact congrArg (fun z => z ≫ (pullbackFunctor (ringedSpaceHom f)).map (B.mulSheaf i j))
    (Stacks.PullbackStrictTensorator.mu_pullbackStrictMonoidal_eq (ringedSpaceHom f)
      (B.piece i) (B.piece j))

namespace F1Pair

/-! ### The homomorphism into the direct image of the Laurent algebra -/

/-- **The degreewise map `𝒜_n ⟶ f_*(⨁_{m ∈ ℤ} L^{⊗ m})_n` a pair determines**: its map `ψ` into
the direct image of the tensor algebra, followed by the direct image of the comparison of the
tensor algebra with the Laurent algebra. -/
def psiLaurent (P : F1Pair A TA f) (n : ℤ) :
    letI := P.invertible
    (situationAlgebra A).piece n ⟶
      (Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra (ringedSpaceHom f)
        (laurent P.L)).piece n :=
  letI := P.invertible
  P.ψ n ≫ (Scheme.Modules.pushforward f).map ((tensorToLaurent P.L (TA T P.L)).app n)

/-- **The degreewise maps of a pair preserve products of homogeneous local sections**, as maps
into the direct image of the Laurent algebra. The multiplication of the direct image on sections
over `U` is the multiplication of the Laurent algebra over `f ⁻¹ᵁ U`, which is where
`F1Pair.map_mul` and the multiplicativity of `tensorToLaurent` are stated. -/
theorem psiLaurent_map_mul (P : F1Pair A TA f) (i j : ℤ) (U : (Opens S.carrier)ᵒᵖ)
    (a : ((situationAlgebra A).piece i).val.obj U)
    (b : ((situationAlgebra A).piece j).val.obj U) :
    letI := P.invertible
    (psiLaurent A TA f P (i + j)).val.app U (((situationAlgebra A).mul i j).app U a b) =
      ((Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra (ringedSpaceHom f)
          (laurent P.L)).mul i j).app U
        ((psiLaurent A TA f P i).val.app U a) ((psiLaurent A TA f P j).val.app U b) := by
  let := P.invertible
  obtain ⟨U⟩ := U
  refine Eq.trans (congrArg
    (((Scheme.Modules.pushforward f).map ((tensorToLaurent P.L (TA T P.L)).app (i + j))).val.app
      (op U)) (P.map_mul i j U a b)) ?_
  refine Eq.trans ((tensorToLaurent P.L (TA T P.L)).map_mul i j (op (f ⁻¹ᵁ U))
    ((P.ψ i).val.app (op U) a) ((P.ψ j).val.app (op U) b)) ?_
  exact (pushforwardGradedAlgebra_mul_app f (laurent P.L) i j U _ _).symm

/-- **The homomorphism of sheaves of graded algebras `𝒜 ⟶ f_*(⨁_{n ∈ ℤ} L^{⊗ n})` a pair
determines.** -/
def psiLaurentHom (P : F1Pair A TA f) :
    letI := P.invertible
    situationAlgebra A ⟶
      Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra (ringedSpaceHom f)
        (laurent P.L) :=
  letI := P.invertible
  { app := psiLaurent A TA f P, map_mul := psiLaurent_map_mul A TA f P }

/-- **The homomorphism of sheaves of graded algebras `f^*𝒜 ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` a pair
determines**: the adjoint transpose of `psiLaurentHom` across the correspondence of Tag 0FQX
between homomorphisms out of a pullback and homomorphisms into a pushforward. -/
def laurentHom (P : F1Pair A TA f) :
    letI := P.invertible
    Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f)
        (situationAlgebra A) (isSheafStruct S) ⟶ laurent P.L :=
  letI := P.invertible
  transportHomBackward (pullbackAdjunction (ringedSpaceHom f))
    (isSheafStruct T) (isSheafStruct S) (psiLaurentHom A TA f P)

/-- The components of `laurentHom` are the adjoint transposes `F1Pair.pullbackMap` of the maps
of the pair, followed by the comparison with the Laurent algebra. -/
theorem laurentHom_app (P : F1Pair A TA f) (n : ℤ) :
    letI := P.invertible
    (laurentHom A TA f P).app n =
      P.pullbackMap A TA n ≫ (tensorToLaurent P.L (TA T P.L)).app n := by
  let := P.invertible
  exact Adjunction.homEquiv_naturality_right_symm (pullbackAdjunction (ringedSpaceHom f))
    (P.ψ n) ((tensorToLaurent P.L (TA T P.L)).app n)

/-- **The family `F1Pair.laurentApp` is `laurentHom` read through the degree identification
`n * 1 = n`.** -/
theorem laurentApp_eq (P : F1Pair A TA f) (n : ℤ) :
    letI := P.invertible
    P.laurentApp A TA f n =
      eqToHom (congrArg
        (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k))
        (mul_one n)) ≫ (laurentHom A TA f P).app n := by
  let := P.invertible
  exact congrArg (fun z => eqToHom (congrArg
    (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k))
    (mul_one n)) ≫ z) (laurentHom_app A TA f P n).symm

/-! ### The two clauses, at aligned degrees -/

/-- **`laurentHom` is multiplicative**, in the shape `Twisting.app_mul` has but with the degrees
not shifted by `n * 1`. -/
theorem laurentHom_mulSheaf (P : F1Pair A TA f) (i j : ℤ) :
    letI := P.invertible
    MonoidalCategoryStruct.tensorHom ((laurentHom A TA f P).app i)
          ((laurentHom A TA f P).app j) ≫ (laurent P.L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) ((situationAlgebra A).piece i)
          ((situationAlgebra A).piece j)) ≫
        (pullbackFunctor (ringedSpaceHom f)).map ((situationAlgebra A).mulSheaf i j) ≫
          (laurentHom A TA f P).app (i + j) := by
  let := P.invertible
  refine ((mulSheaf_comp_eq_iff (isSheafStruct T)
      (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f)
        (situationAlgebra A) (isSheafStruct S))
      (laurent P.L) (laurentHom A TA f P).app i j).mpr
    ((laurentHom A TA f P).map_mul i j)).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ (laurentHom A TA f P).app (i + j))
    (mulSheaf_pullbackGradedAlgebra f (situationAlgebra A) i j)) ?_
  exact Category.assoc _ _ _

/-- **`laurentHom` preserves the degree-zero unit**, in the shape `Twisting.app_one` has but
with the degree not shifted by `0 * 1`. A global section is determined by its value over `⊤`,
and there the unit of `f^*𝒜` is the pullback-unit image of the unit of `𝒜`, on which the
transposed map is the map of the pair. -/
theorem laurentHom_one (P : F1Pair A TA f) :
    letI := P.invertible
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) (situationAlgebra A) ≫
        (laurentHom A TA f P).app 0 = oneHom (laurent P.L) := by
  let := P.invertible
  refine (SheafOfModules.unitHomEquiv ((laurent P.L).piece 0)).injective
    (Stacks.AlgebraicGeometry.AffineTwisting.sections_eq_of_eval_top
      ((laurent P.L).piece 0) _ _ ?_)
  rw [Stacks.PullbackTensorCoherence.unitHomEquiv_eval,
    Stacks.PullbackTensorCoherence.unitHomEquiv_eval]
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) (situationAlgebra A))
    ((laurentHom A TA f P).app 0) (op ⊤) _) ?_
  refine Eq.trans (congrArg (fun z => ((laurentHom A TA f P).app 0).val.app (op ⊤) z)
    (Stacks.AlgebraicGeometry.AffineTwisting.pullbackOne_val_app_oneSec f
      (situationAlgebra A))) ?_
  refine Eq.trans (SheafOfModules.hom_congr_app_apply (laurentHom_app A TA f P 0) _ _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply (P.pullbackMap A TA 0)
    ((tensorToLaurent P.L (TA T P.L)).app 0) _ _) ?_
  refine Eq.trans (congrArg (fun z => ((tensorToLaurent P.L (TA T P.L)).app 0).val.app _ z)
    (((Stacks.RingedSpace.homEquiv_val_app (ringedSpaceHom f)
      ((situationAlgebra A).piece 0) ((TA T P.L).tensor.piece 0) (P.pullbackMap A TA 0)
      (op ⊤) ((situationAlgebra A).one.eval (op ⊤))).symm).trans
      ((SheafOfModules.hom_congr_app_apply
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
          ((situationAlgebra A).piece 0) ((TA T P.L).tensor.piece 0)
          |>.apply_symm_apply (P.ψ 0)) (op ⊤)
        ((situationAlgebra A).one.eval (op ⊤))).trans (P.map_one ⊤)))) ?_
  refine Eq.trans ((tensorToLaurent P.L (TA T P.L)).map_one _) ?_
  exact (Stacks.PullbackTensorCoherence.oneMorphism_val_app_oneSec (laurent P.L) (op ⊤)).symm

/-! ### The two clauses of a twisting -/

/-- **The multiplicativity clause of `Twisting`, with the three source degrees taken as
variables.** Substituting the equalities turns every `eqToHom` into an identity and leaves
`laurentHom_mulSheaf`; the degree identification `n * 1 = n` cannot be rewritten inside the
dependent types, since it is not `rfl` for an integer. -/
theorem laurentApp_app_mul_of_eq (P : F1Pair A TA f) (i j i' j' k' : ℤ)
    (hi : i' = i) (hj : j' = j) (hk : k' = i + j) (h : i' + j' = k') :
    letI := P.invertible
    MonoidalCategoryStruct.tensorHom
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj
              ((situationAlgebra A).piece n)) hi) ≫ (laurentHom A TA f P).app i)
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj
              ((situationAlgebra A).piece n)) hj) ≫ (laurentHom A TA f P).app j) ≫
        (laurent P.L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) ((situationAlgebra A).piece i')
          ((situationAlgebra A).piece j')) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          ((situationAlgebra A).mulSheaf i' j' ≫
            eqToHom (congrArg (situationAlgebra A).piece h)) ≫
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj
              ((situationAlgebra A).piece n)) hk) ≫ (laurentHom A TA f P).app (i + j)) := by
  let := P.invertible
  have := Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison
    (ringedSpaceHom f) ((situationAlgebra A).piece i') ((situationAlgebra A).piece j')
  subst hi
  subst hj
  subst hk
  simp only [eqToHom_refl]
  exact laurentHom_mulSheaf A TA f P i' j'

/-- **The unit clause of `Twisting`, with the source degree taken as a variable.** -/
theorem laurentApp_app_one_of_eq (P : F1Pair A TA f) (k' : ℤ) (hk : k' = 0)
    (h : (0 : ℤ) = k') :
    letI := P.invertible
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) (situationAlgebra A) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg (situationAlgebra A).piece h)) ≫
          (eqToHom (congrArg
            (fun n : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj
              ((situationAlgebra A).piece n)) hk) ≫ (laurentHom A TA f P).app 0) =
      oneHom (laurent P.L) := by
  let := P.invertible
  subst hk
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact laurentHom_one A TA f P

/-- **The multiplicativity clause of `Twisting` for the family a pair of Tag 01O4
determines.** -/
theorem laurentApp_app_mul (P : F1Pair A TA f) (i j : ℤ) :
    letI := P.invertible
    MonoidalCategoryStruct.tensorHom (P.laurentApp A TA f i) (P.laurentApp A TA f j) ≫
        (laurent P.L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) ((situationAlgebra A).piece (i * 1))
          ((situationAlgebra A).piece (j * 1))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          ((situationAlgebra A).mulSheaf (i * 1) (j * 1) ≫
            eqToHom (congrArg (situationAlgebra A).piece
              (by ring : i * 1 + j * 1 = (i + j) * 1))) ≫
          P.laurentApp A TA f (i + j) := by
  let := P.invertible
  rw [laurentApp_eq A TA f P i, laurentApp_eq A TA f P j, laurentApp_eq A TA f P (i + j)]
  exact laurentApp_app_mul_of_eq A TA f P i j (i * 1) (j * 1) ((i + j) * 1) (mul_one i)
    (mul_one j) (mul_one (i + j)) (by ring)

/-- **The unit clause of `Twisting` for the family a pair of Tag 01O4 determines.** -/
theorem laurentApp_app_one (P : F1Pair A TA f) :
    letI := P.invertible
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) (situationAlgebra A) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg (situationAlgebra A).piece (by ring : (0 : ℤ) = 0 * 1))) ≫
        P.laurentApp A TA f 0 =
      oneHom (laurent P.L) := by
  let := P.invertible
  rw [laurentApp_eq A TA f P 0]
  exact laurentApp_app_one_of_eq A TA f P (0 * 1) (mul_one 0) (by ring)

/-! ### The twisting and the quadruple -/

/-- **The map `ψ` of Section 01NS a pair of Tag 01O4 determines**, at `d = 1`: the family
`F1Pair.laurentApp`, with its multiplicativity and its unit clause. -/
def twisting (P : F1Pair A TA f) :
    letI := P.invertible
    Twisting f (situationAlgebra A) 1 P.L :=
  letI := P.invertible
  { app := P.laurentApp A TA f
    app_mul := laurentApp_app_mul A TA f P
    app_one := laurentApp_app_one A TA f P }

/-- **The quadruple of Section 01NS a pair of Tag 01O4 determines**, at `d = 1`: the pair's
invertible module, the twisting it determines, and the degree-one surjectivity
`F1Pair.epi_laurentApp_one`. -/
def quadruple (P : F1Pair A TA f) : Quadruple f (situationAlgebra A) 1 where
  L := P.L
  isInvertible := P.invertible
  twisting := twisting A TA f P
  epi_app_one := P.epi_laurentApp_one A TA f

end F1Pair

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
