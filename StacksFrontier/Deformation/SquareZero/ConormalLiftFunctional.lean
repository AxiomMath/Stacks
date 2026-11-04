module

public import StacksFrontier.Deformation.SquareZero.AlgebraExtensions

/-!
# The conormal functional of a lift of the canonical presentation

Let `A → B` be a ring map and `N` a `B`-module. A solution `X` of the square-zero extension
problem `Stacks.Deformation.algebraExtensionProblem A B N` is a square-zero extension
`0 → N → B' → B → 0` of `A`-algebras. Lifting the canonical polynomial presentation
`A[B] → B` to `B'` produces a `B`-linear functional on the conormal module of that
presentation, and its class in the conormal cokernel
`Stacks.Deformation.conormalCokernel` does not depend on the lift.

## Main definitions

* `Stacks.Deformation.solutionExtension`: a solution of the algebra extension problem, read
  as an `Algebra.Extension`.
* `Stacks.Deformation.solutionCotangentEquiv`: its conormal module is `N`, because its kernel
  has square zero.
* `Stacks.Deformation.liftFunctional` and `Stacks.Deformation.liftClass`: the conormal
  functional of a lift of the canonical presentation into a solution, and its class in the
  conormal cokernel.

## Main results

* `Stacks.Deformation.liftClass_eq`: the class of the conormal functional in the conormal
  cokernel is independent of the lift.

## Implementation notes

The conormal module of a solution is identified with `N` by exhibiting the `B`-linear map
`N → I/I²` sending `n` to the class of the kernel element `n` names, and proving it
bijective: `I² = 0`, so the class map `I → I/I²` is injective. The `B`-action on `I/I²` is
the one Mathlib installs through a set-theoretic section of `B' → B`, and the `B`-action on
the kernel is the one the solution carries; they agree because both are multiplication by a
lift, which is the content of the solution's `toB_smul_kernel`.

The lifts of the canonical presentation are taken as morphisms of extensions, so that the
independence of the class is Mathlib's `Algebra.Extension.Cotangent.map_sub_map`: the
difference of the two induced maps on conormal modules is precomposition with the conormal
differential.

Everything is spelled through the fields of the problem — `(prob A B N).A`, `.B`, `.N` — and
not through `A`, `B`, `N` themselves, although the two agree by definition: the conormal
cokernel is spelled through the fields, and instance search does not unfold the problem, so
mixing the two spellings makes the module structures on conormal functionals unfindable.

## References

* [Stacks Project, Tag 0GPU](https://stacks.math.columbia.edu/tag/0GPU)
* [Stacks Project, Tag 08S5](https://stacks.math.columbia.edu/tag/08S5)
* [Stacks Project, Tag 08S7](https://stacks.math.columbia.edu/tag/08S7)
-/

@[expose] public noncomputable section

universe uA uB uN uE v

namespace Stacks.Deformation

variable {A : Type uA} {B : Type uB} {N : Type uN}
  [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N]

variable (A B N) in
/-- The square-zero extension problem of extending `B` by `N`, abbreviated. -/
abbrev prob := algebraExtensionProblem A B N

/-- The canonical polynomial presentation `A[B] → B`, read as an extension. -/
abbrev canonicalExtension (A : Type uA) (B : Type uB) (N : Type uN)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N] :
    Algebra.Extension (prob A B N).A (prob A B N).B :=
  (Algebra.Generators.self (prob A B N).A (prob A B N).B).toExtension

/-- Reducing the coefficients of a relation along `A → A` changes nothing: the lower row of
the algebra extension problem is the identity of `A`. -/
lemma reducedRelationOf_val (x : RingHom.ker (problemPresentationToB (prob A B N))) :
    (reducedRelationOf (prob A B N) x).1 = x.1 := by
  show MvPolynomial.map (RingHom.id A) x.1 = x.1
  exact MvPolynomial.map_id x.1

/-- A scalar of the base acts on the conormal module of an extension through any of its
lifts. -/
lemma smul_cotangent_of_algebraMap_eq {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {P : Algebra.Extension.{uE} R S} (c : P.Ring) (b : S)
    (hc : algebraMap P.Ring S c = b) (z : P.Cotangent) : c • z = b • z := by
  refine Algebra.Extension.Cotangent.ext ?_
  rw [Algebra.Extension.Cotangent.val_smul' c, Algebra.Extension.Cotangent.val_smul b]
  have hmem : c - P.σ b ∈ P.ker := by
    rw [Algebra.Extension.ker, RingHom.mem_ker, map_sub, hc, P.algebraMap_σ, sub_self]
  have hzero := Algebra.Extension.Cotangent.smul_eq_zero_of_mem (P := P) (c - P.σ b) hmem z.val
  rwa [sub_smul, sub_eq_zero] at hzero

/-- The canonical presentation maps to every extension of `B` over `A`, by evaluating the
variables at a set-theoretic section of that extension. -/
def canonicalHom (E : Algebra.Extension.{uE} (prob A B N).A (prob A B N).B) :
    (canonicalExtension A B N).Hom E where
  toRingHom := (MvPolynomial.aeval (fun b : (prob A B N).B ↦ E.σ b)).toRingHom
  toRingHom_algebraMap a :=
    (MvPolynomial.aeval (fun b : (prob A B N).B ↦ E.σ b)).commutes a
  algebraMap_toRingHom := by
    have key : (IsScalarTower.toAlgHom (prob A B N).A E.Ring (prob A B N).B).comp
        (MvPolynomial.aeval (fun b : (prob A B N).B ↦ E.σ b)) =
        MvPolynomial.aeval (fun b : (prob A B N).B ↦ b) := by
      refine MvPolynomial.algHom_ext fun b ↦ ?_
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        IsScalarTower.coe_toAlgHom']
      exact E.algebraMap_σ b
    exact AlgHom.congr_fun key

section Solution

/-- The middle ring of a solution of the algebra extension problem is an algebra over the
base of the problem: the lower-left ring of `Stacks.Deformation.algebraExtensionProblem A B N`
is `A` itself, so this is the solution's own algebra structure, restated because instance
search does not unfold the problem to see it. -/
instance algebraBaseSolutionRing {X : (prob A B N).CompatibleExtension.{v}} :
    Algebra (prob A B N).A X.B' :=
  X.algebraA'B'

variable (X : (prob A B N).CompatibleExtension.{v})

/-- A solution of the square-zero extension problem of `B` by `N`, read as an extension. -/
def solutionExtension : Algebra.Extension.{v} (prob A B N).A (prob A B N).B :=
  Algebra.Extension.ofSurjective X.toB X.surjective

/-- An element of the kernel of a solution, read in the kernel of its extension. -/
def solKer (y : RingHom.ker X.toB.toRingHom) : (solutionExtension X).ker := ⟨y.1, y.2⟩

/-- The class in the conormal module of a solution of the kernel element named by `n`. -/
def solutionCotangentHom :
    (prob A B N).N →ₗ[(prob A B N).B] (solutionExtension X).Cotangent where
  toFun n := Algebra.Extension.Cotangent.mk (P := solutionExtension X)
    (solKer X (X.kernelEquiv n))
  map_add' n m := by
    rw [map_add]
    exact map_add (Algebra.Extension.Cotangent.mk (P := solutionExtension X))
      (solKer X (X.kernelEquiv n)) (solKer X (X.kernelEquiv m))
  map_smul' b n := by
    obtain ⟨c, hc⟩ := X.surjective b
    let c' : (solutionExtension X).Ring := c
    have h1 : solKer X (X.kernelEquiv (b • n)) = c' • solKer X (X.kernelEquiv n) :=
      Subtype.ext (by rw [map_smul, ← hc, X.toB_smul_kernel]; rfl)
    rw [h1, map_smul]
    exact smul_cotangent_of_algebraMap_eq (P := solutionExtension X) c' b hc _

/-- `solutionCotangentHom X n` is the conormal class of the kernel element named by `n`. -/
lemma solutionCotangentHom_apply (n : (prob A B N).N) :
    solutionCotangentHom X n =
      Algebra.Extension.Cotangent.mk (P := solutionExtension X)
        (solKer X (X.kernelEquiv n)) :=
  rfl

/-- The class map sends the element of `N` identified with a kernel element `y` to the class
of `y`. -/
lemma solutionCotangentHom_kernelEquiv_symm (y : (solutionExtension X).ker) :
    solutionCotangentHom X (X.kernelEquiv.symm ⟨y.1, y.2⟩) =
      Algebra.Extension.Cotangent.mk y := by
  rw [solutionCotangentHom_apply]
  exact congrArg (Algebra.Extension.Cotangent.mk (P := solutionExtension X))
    (Subtype.ext (congrArg Subtype.val (X.kernelEquiv.apply_symm_apply ⟨y.1, y.2⟩)))

/-- The class map from `N` to the conormal module of a solution is bijective. -/
lemma solutionCotangentHom_bijective : Function.Bijective (solutionCotangentHom X) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun n hn ↦ ?_, fun z ↦ ?_⟩
  · have hsq : (solutionExtension X).ker ^ 2 = ⊥ := X.sq_zero
    rw [solutionCotangentHom_apply, Algebra.Extension.Cotangent.mk_eq_zero_iff, hsq,
      Ideal.mem_bot] at hn
    exact X.kernelEquiv.map_eq_zero_iff.mp (Subtype.ext hn)
  · obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    exact ⟨_, solutionCotangentHom_kernelEquiv_symm X y⟩

/-- The conormal module of a solution is `N`: its kernel has square zero, so the class map
from the kernel is bijective, and the kernel is `N` by the solution's own identification. -/
def solutionCotangentEquiv :
    (prob A B N).N ≃ₗ[(prob A B N).B] (solutionExtension X).Cotangent :=
  LinearEquiv.ofBijective (solutionCotangentHom X) (solutionCotangentHom_bijective X)

/-- The conormal functional of a lift of the canonical presentation into a solution: the
`B`-linear map `J/J² → N` induced by the lift. -/
def liftFunctional (a : (canonicalExtension A B N).Hom (solutionExtension X)) :
    (canonicalExtension A B N).Cotangent →ₗ[(prob A B N).B] (prob A B N).N :=
  (solutionCotangentEquiv X).symm.toLinearMap ∘ₗ Algebra.Extension.Cotangent.map a

/-- The conormal functional of a lift is the induced map of conormal modules followed by the
inverse of `solutionCotangentEquiv`. -/
lemma liftFunctional_apply (a : (canonicalExtension A B N).Hom (solutionExtension X))
    (z : (canonicalExtension A B N).Cotangent) :
    liftFunctional X a z = (solutionCotangentEquiv X).symm
      (Algebra.Extension.Cotangent.map a z) :=
  rfl

/-- `solutionCotangentEquiv X` agrees with `solutionCotangentHom X`. -/
@[simp] lemma solutionCotangentEquiv_apply (n : (prob A B N).N) :
    solutionCotangentEquiv X n = solutionCotangentHom X n := rfl

/-- The inverse of `solutionCotangentEquiv` sends the class of a kernel element `y` to the
element of `N` identified with `y`. -/
lemma solutionCotangentEquiv_symm_mk (y : (solutionExtension X).ker) :
    (solutionCotangentEquiv X).symm (Algebra.Extension.Cotangent.mk y) =
      X.kernelEquiv.symm ⟨y.1, y.2⟩ := by
  rw [LinearEquiv.symm_apply_eq, solutionCotangentEquiv_apply]
  exact (solutionCotangentHom_kernelEquiv_symm X y).symm

/-- The lift of the canonical presentation into a solution given by the chosen lifts of the
elements of `B`, which are the ones the obstruction functional of Stacks 08S5 is computed
with. -/
def canonicalLift : (canonicalExtension A B N).Hom (solutionExtension X) where
  toRingHom := (MvPolynomial.aeval
    (fun b : (prob A B N).B ↦ Classical.choose (X.surjective b))).toRingHom
  toRingHom_algebraMap a :=
    (MvPolynomial.aeval
      (fun b : (prob A B N).B ↦ Classical.choose (X.surjective b))).commutes a
  algebraMap_toRingHom := by
    have key : (IsScalarTower.toAlgHom (prob A B N).A (solutionExtension X).Ring
          (prob A B N).B).comp
        (MvPolynomial.aeval
          (fun b : (prob A B N).B ↦ Classical.choose (X.surjective b))) =
        MvPolynomial.aeval (fun b : (prob A B N).B ↦ b) := by
      refine MvPolynomial.algHom_ext fun b ↦ ?_
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        IsScalarTower.coe_toAlgHom']
      exact Classical.choose_spec (X.surjective b)
    exact AlgHom.congr_fun key

/-- The conormal functional of the canonical lift is the evaluation of relations at the
chosen lifts, which is the datum the obstruction functional of Stacks 08S5 is built from. -/
lemma liftFunctional_canonicalLift
    (x : RingHom.ker (problemPresentationToB (prob A B N))) :
    liftFunctional X (canonicalLift X)
        (Algebra.Extension.Cotangent.mk (reducedRelationOf (prob A B N) x)) =
      solutionRelationEval X x := by
  rw [liftFunctional_apply, Algebra.Extension.Cotangent.map_mk,
    solutionCotangentEquiv_symm_mk]
  have hspec : ((X.kernelEquiv (solutionRelationEval X x) :
        RingHom.ker X.toB.toRingHom) : X.B') =
      (presentationEval₁ (comparisonDiagram X X)) x.1 :=
    relationEval₁_spec (comparisonDiagram X X) x
  refine Eq.trans ?_ (X.kernelEquiv.symm_apply_apply (solutionRelationEval X x))
  refine congrArg X.kernelEquiv.symm (Subtype.ext ?_)
  show @Eq X.B' ((canonicalLift X).toAlgHom (reducedRelationOf (prob A B N) x).1)
    ((X.kernelEquiv (solutionRelationEval X x) : RingHom.ker X.toB.toRingHom) : X.B')
  rw [hspec]
  show (MvPolynomial.aeval (fun b : (prob A B N).B ↦ Classical.choose (X.surjective b)))
      (reducedRelationOf (prob A B N) x).1 =
    (presentationEval₁ (comparisonDiagram X X)) x.1
  rw [reducedRelationOf_val]
  rfl

/-- The class in the conormal cokernel of the conormal functional of a lift. -/
def liftClass (a : (canonicalExtension A B N).Hom (solutionExtension X)) :
    conormalCokernel (prob A B N) :=
  Submodule.Quotient.mk (liftFunctional X a)

/-- The class of the conormal functional of a lift does not depend on the lift. -/
lemma liftClass_eq (a a' : (canonicalExtension A B N).Hom (solutionExtension X)) :
    liftClass X a = liftClass X a' := by
  rw [liftClass, liftClass, Submodule.Quotient.eq]
  refine LinearMap.mem_range.mpr
    ⟨(solutionCotangentEquiv X).symm.toLinearMap ∘ₗ a.sub a', ?_⟩
  refine LinearMap.ext fun z ↦ ?_
  have h := LinearMap.congr_fun (Algebra.Extension.Cotangent.map_sub_map a a') z
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at h
  show (solutionCotangentEquiv X).symm
      ((a.sub a') ((canonicalExtension A B N).cotangentComplex z)) =
    liftFunctional X a z - liftFunctional X a' z
  rw [← h, map_sub]
  rfl

/-- The conormal functional of a lift which factors through an extension `E` is pulled back
along the induced map of conormal modules. -/
lemma liftFunctional_comp {E : Algebra.Extension.{uE} (prob A B N).A (prob A B N).B}
    (hmor : (canonicalExtension A B N).Hom E) (g : E.Hom (solutionExtension X)) :
    liftFunctional X (g.comp hmor) =
      ((solutionCotangentEquiv X).symm.toLinearMap ∘ₗ
        Algebra.Extension.Cotangent.map g) ∘ₗ Algebra.Extension.Cotangent.map hmor := by
  refine LinearMap.ext fun z ↦ ?_
  rw [liftFunctional_apply, Algebra.Extension.Cotangent.map_comp]
  rfl

end Solution

/-- Pulling back conormal functionals of an extension `E` along a map from the canonical
presentation, read in the conormal cokernel. -/
def pullbackClass (E : Algebra.Extension.{uE} (prob A B N).A (prob A B N).B)
    (hmor : (canonicalExtension A B N).Hom E) :
    (E.Cotangent →ₗ[(prob A B N).B] (prob A B N).N) →ₗ[(prob A B N).B]
      conormalCokernel (prob A B N) :=
  (Submodule.mkQ _).comp (LinearMap.lcomp (prob A B N).B (prob A B N).N
    (Algebra.Extension.Cotangent.map hmor))

/-- `pullbackClass E hmor δ` is the class of `δ` composed with the map of conormal modules
induced by `hmor`. -/
lemma pullbackClass_apply (E : Algebra.Extension.{uE} (prob A B N).A (prob A B N).B)
    (hmor : (canonicalExtension A B N).Hom E)
    (δ : E.Cotangent →ₗ[(prob A B N).B] (prob A B N).N) :
    pullbackClass E hmor δ =
      Submodule.Quotient.mk (δ ∘ₗ Algebra.Extension.Cotangent.map hmor) :=
  rfl

/-- The obstruction functional of Stacks 08S5 is the difference of the conormal functionals
of the canonical lifts into the two solutions. -/
lemma obstructionFunctional_eq_sub (X Y : (prob A B N).CompatibleExtension.{v}) :
    obstructionFunctional X Y =
      liftFunctional Y (canonicalLift Y) - liftFunctional X (canonicalLift X) := by
  refine conormalFunctional_ext fun x ↦ ?_
  rw [obstructionFunctional_mk, LinearMap.sub_apply, liftFunctional_canonicalLift,
    liftFunctional_canonicalLift]

/-- The class of a solution through which `E` lifts is pulled back from `E`. -/
lemma liftClass_mem_range_pullbackClass
    {E : Algebra.Extension.{uE} (prob A B N).A (prob A B N).B}
    (hmor : (canonicalExtension A B N).Hom E)
    (X : (prob A B N).CompatibleExtension.{v}) (g : E.Hom (solutionExtension X)) :
    liftClass X (canonicalLift X) ∈ LinearMap.range (pullbackClass E hmor) := by
  refine ⟨(solutionCotangentEquiv X).symm.toLinearMap ∘ₗ
    Algebra.Extension.Cotangent.map g, ?_⟩
  rw [pullbackClass_apply, ← liftFunctional_comp X hmor g]
  exact (liftClass_eq X (canonicalLift X) (g.comp hmor)).symm

/-- **Every class of the conormal cokernel is pulled back from `E`**, as soon as the problem
has a solution, `E` maps to the canonical presentation, and `E` lifts through every solution.

This is the form in which a presentation other than the canonical polynomial one computes the
first Ext module of the naive cotangent complex: every square-zero extension is obtained from
a conormal functional of `E`, because the presentation `E` lifts through it and two lifts of
the canonical presentation differ by the conormal differential. -/
theorem mem_range_pullbackClass
    {E : Algebra.Extension.{uE} (prob A B N).A (prob A B N).B}
    (hmor : (canonicalExtension A B N).Hom E)
    (hlift : ∀ Z : (prob A B N).CompatibleExtension.{v},
      Nonempty (E.Hom (solutionExtension Z)))
    (X₀ : (prob A B N).CompatibleExtension.{v}) (c : conormalCokernel (prob A B N)) :
    c ∈ LinearMap.range (pullbackClass E hmor) := by
  obtain ⟨Y, hY⟩ := exists_obstructionCokernelClass_eq X₀ c
  have hc : c = Submodule.Quotient.mk (obstructionFunctional X₀ Y) := hY.symm
  rw [hc, obstructionFunctional_eq_sub]
  exact sub_mem (liftClass_mem_range_pullbackClass hmor Y (hlift Y).some)
    (liftClass_mem_range_pullbackClass hmor X₀ (hlift X₀).some)

end Stacks.Deformation

end
