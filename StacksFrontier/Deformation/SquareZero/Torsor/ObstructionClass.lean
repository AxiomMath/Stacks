module

public import StacksFrontier.Deformation.SquareZero.Obstruction

/-!
# The obstruction class of two solutions (Stacks 08S7)

The Ext group `naiveCotangentExtOne`, the comparison diagram of two solutions, the
canonical presentation `A'[B] → B` and its reduction to `A[B] → B`, the obstruction
functional and the conormal cokernel, fitting maps, and the obstruction class
`obstructionCokernelClass`, which vanishes exactly when the two solutions are isomorphic
and adds up along triples.

Part of `StacksFrontier.Deformation.SquareZero.Torsor`; see that module for the overview of
Stacks 08S7.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u₃ u₄ v

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

variable {S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}}

/-- The first Ext group `Ext¹_B(NL_{B/A}, N)` from the naive cotangent complex. -/
public noncomputable abbrev naiveCotangentExtOne
    (A : Type u₂) (B : Type u₃) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type u₄) [AddCommGroup N] [Module B N] :=
  let K := ((ModuleCat.uliftFunctor.{u₄} B).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex A B)
  DerivedCategory.Ext
    (DerivedCategory.Q.obj
      (HomologicalComplex.double (K.d 1 0)
        (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)))
    ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ u₄} B) 0).obj
      ((ModuleCat.uliftFunctor.{max u₂ u₃} B).obj
        (ModuleCat.of B N))) 1

/-- The compatible diagram which compares two solutions of the same square-zero extension
problem. -/
public noncomputable def comparisonDiagram
    {S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}}
    (X Y : S.CompatibleExtension.{v}) :
    CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      u₁, u₂, u₃, u₄, v, v} where
  S₁ := S
  S₂ := S
  X₁ := X
  X₂ := Y
  algebraA'₁A'₂ := inferInstance
  algebraA₁A₂ := inferInstance
  algebraB₁B₂ := inferInstance
  toA_comm := by ext; simp
  toB_comm := by ext; simp
  moduleB₁N₂ := S.moduleBN
  isScalarTowerB₁B₂N₂ := inferInstance
  mapN := LinearMap.id
  map_I := fun i ↦ by simp
  map_c := fun i ↦ by simp

section Presentation

variable (S)

/-- The canonical polynomial presentation `A'[B] → B` of `B` over the thickening `A'`. -/
public noncomputable def problemPresentationToB : MvPolynomial S.B S.A' →+* S.B :=
  (MvPolynomial.aeval (fun b : S.B ↦ b)).toRingHom

/-- The presentation `A'[B] → B` sends the variable `X b` to `b`. -/
@[simp]
public lemma problemPresentationToB_X (b : S.B) :
    problemPresentationToB S (MvPolynomial.X b) = b := by
  simp [problemPresentationToB]

/-- The presentation `A'[B] → B` sends a constant `C a` to the image of `a` in `B`. -/
@[simp]
public lemma problemPresentationToB_C (a : S.A') :
    problemPresentationToB S (MvPolynomial.C a) = algebraMap S.A' S.B a := by
  simp [problemPresentationToB]

/-- The canonical polynomial presentation `A[B] → B` of `B` over `A`. -/
public noncomputable def problemReducedPresentationToB : MvPolynomial S.B S.A →+* S.B :=
  (MvPolynomial.aeval (fun b : S.B ↦ b)).toRingHom

/-- Reduction of coefficients along `A' → A`, from `A'[B]` to the ring `A[B]` of the
canonical presentation. -/
public noncomputable abbrev reduceCoefficients :
    MvPolynomial S.B S.A' →+* (Algebra.Generators.self S.A S.B).toExtension.Ring :=
  MvPolynomial.map (algebraMap S.A' S.A)

/-- The presentation `A'[B] → B` factors through the reduced presentation `A[B] → B`. -/
public lemma problemPresentationToB_factor :
    (problemReducedPresentationToB S).comp (reduceCoefficients S) =
      problemPresentationToB S := by
  apply MvPolynomial.ringHom_ext'
  · ext a
    simpa [problemReducedPresentationToB] using
      (IsScalarTower.algebraMap_apply S.A' S.A S.B a).symm
  · intro b
    simp [problemReducedPresentationToB]

/-- A relation of the presentation `A'[B] → B`, reduced to a relation of `A[B] → B`. -/
public noncomputable def reducedRelationOf
    (x : RingHom.ker (problemPresentationToB S)) :
    (Algebra.Generators.self S.A S.B).toExtension.ker :=
  ⟨reduceCoefficients S x.1, by
    apply RingHom.mem_ker.mpr
    have h := DFunLike.congr_fun (problemPresentationToB_factor S) x.1
    change problemReducedPresentationToB S (reduceCoefficients S x.1) =
      problemPresentationToB S x.1 at h
    change problemReducedPresentationToB S (reduceCoefficients S x.1) = 0
    rw [h]
    exact RingHom.mem_ker.mp x.2⟩

/-- Every relation of `A[B] → B` lifts to a relation of `A'[B] → B`. -/
public lemma exists_relationOf_lift
    (y : (Algebra.Generators.self S.A S.B).toExtension.ker) :
    ∃ x : RingHom.ker (problemPresentationToB S), reducedRelationOf S x = y := by
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (algebraMap S.A' S.A) S.surjective y.1
  refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
  apply RingHom.mem_ker.mpr
  have h := DFunLike.congr_fun (problemPresentationToB_factor S) p
  change problemReducedPresentationToB S (reduceCoefficients S p) =
    problemPresentationToB S p at h
  change problemPresentationToB S p = 0
  rw [← h, show reduceCoefficients S p = y.1 from hp]
  exact RingHom.mem_ker.mp y.2

end Presentation

/-- Evaluating a relation of the presentation `A'[B] → B` at the chosen lifts of the
variables in a solution `X`, read in the kernel `N` of `X`. -/
public noncomputable def solutionRelationEval (X : S.CompatibleExtension.{v}) :
    RingHom.ker (problemPresentationToB S) →+ S.N :=
  relationEval₁ (comparisonDiagram X X)

/-- The first relation evaluation of the comparison diagram of `X` and `Y` is the relation
evaluation in `X`. -/
@[simp]
public lemma relationEval₁_comparisonDiagram (X Y : S.CompatibleExtension.{v}) :
    relationEval₁ (comparisonDiagram X Y) = solutionRelationEval X := rfl

/-- The second relation evaluation of the comparison diagram of `X` and `Y` is the relation
evaluation in `Y`. -/
@[simp]
public lemma relationEval₂_comparisonDiagram (X Y : S.CompatibleExtension.{v}) :
    relationEval₂ (comparisonDiagram X Y) = solutionRelationEval Y := rfl

/-- The relation functional of the comparison diagram of `X` and `Y` is the difference of
the evaluations in `Y` and in `X`. -/
public lemma relationDifference_comparisonDiagram (X Y : S.CompatibleExtension.{v})
    (x : RingHom.ker (problemPresentationToB S)) :
    (relationDifference (comparisonDiagram X Y) x : S.N) =
      solutionRelationEval Y x - solutionRelationEval X x := rfl

/-- The conormal functional measuring the obstruction to a map from `X` to `Y`. -/
public noncomputable def obstructionFunctional (X Y : S.CompatibleExtension.{v}) :
    (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N :=
  conormalFunctional (comparisonDiagram X Y)

/-- The conormal cokernel `Hom_B(J/J², N) / Hom_B(Ω_{A[B]/A} ⊗ B, N)`, which presents
`Ext¹_B(NL_{B/A}, N)`. -/
public abbrev conormalCokernel (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}) :=
  ((Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N) ⧸
    LinearMap.range (LinearMap.lcomp S.B S.N
      (Algebra.Generators.self S.A S.B).toExtension.cotangentComplex)

/-- Two conormal functionals which agree on the classes of all reduced relations are
equal. -/
public lemma conormalFunctional_ext
    {f g : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N}
    (h : ∀ x : RingHom.ker (problemPresentationToB S),
      f (Algebra.Extension.Cotangent.mk (reducedRelationOf S x)) =
        g (Algebra.Extension.Cotangent.mk (reducedRelationOf S x))) : f = g := by
  ext t
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective
    (P := (Algebra.Generators.self S.A S.B).toExtension) t
  obtain ⟨x, hx⟩ := exists_relationOf_lift S y
  rw [← hx]
  exact h x

/-- The value of the obstruction functional on the class of a reduced relation. -/
public lemma obstructionFunctional_mk (X Y : S.CompatibleExtension.{v})
    (x : RingHom.ker (problemPresentationToB S)) :
    obstructionFunctional X Y (Algebra.Extension.Cotangent.mk (reducedRelationOf S x)) =
      solutionRelationEval Y x - solutionRelationEval X x :=
  conormalFunctional_reducedRelation (comparisonDiagram X Y) x

/-- The obstruction functionals of three solutions add up. -/
public lemma obstructionFunctional_add (X Y Z : S.CompatibleExtension.{v}) :
    obstructionFunctional X Y + obstructionFunctional Y Z = obstructionFunctional X Z := by
  apply conormalFunctional_ext
  intro x
  rw [LinearMap.add_apply, obstructionFunctional_mk, obstructionFunctional_mk,
    obstructionFunctional_mk]
  abel

section FittingMaps

variable {X Y : S.CompatibleExtension.{v}}

/-- The underlying ring map of a fitting map of a comparison diagram, with its type spelled
in terms of the two solutions. -/
public def fittingMapHom (F : (comparisonDiagram X Y).FittingMap) : X.B' →+* Y.B' :=
  F.toRingHom

/-- A fitting map of a comparison diagram induces the identity on the quotient `B`. -/
public lemma fittingMap_toB_apply (F : (comparisonDiagram X Y).FittingMap) (x : X.B') :
    Y.toB (fittingMapHom F x) = X.toB x :=
  DFunLike.congr_fun F.toB_comm x

/-- A fitting map of a comparison diagram induces the identity on the kernel `N`. -/
public lemma fittingMap_kernel_apply (F : (comparisonDiagram X Y).FittingMap) (n : S.N) :
    fittingMapHom F ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') =
      ((Y.kernelEquiv n : RingHom.ker Y.toB.toRingHom) : Y.B') := F.kernel_comm n

/-- An element of `B'` mapping to zero in `B` is the image of some element of `N`. -/
private theorem exists_kernelEquiv_eq (Z : S.CompatibleExtension.{v}) {x : Z.B'}
    (hx : Z.toB x = 0) :
    ∃ n, ((Z.kernelEquiv n : RingHom.ker Z.toB.toRingHom) : Z.B') = x := by
  obtain ⟨n, hn⟩ := Z.kernelEquiv.surjective ⟨x, RingHom.mem_ker.mpr hx⟩
  exact ⟨n, congrArg Subtype.val hn⟩

/-- A fitting map between two solutions of the same problem is injective. -/
public lemma fittingMap_injective (F : (comparisonDiagram X Y).FittingMap) :
    Function.Injective (fittingMapHom F) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hb : X.toB x = 0 := by
    rw [← fittingMap_toB_apply F x, hx, map_zero]
  obtain ⟨n, hxn⟩ := exists_kernelEquiv_eq X hb
  have hzero : ((Y.kernelEquiv n : RingHom.ker Y.toB.toRingHom) : Y.B') = 0 := by
    rw [← fittingMap_kernel_apply F n, hxn, hx]
  have hn0 : n = 0 := Y.kernelEquiv.map_eq_zero_iff.mp (Subtype.ext hzero)
  rw [← hxn, hn0, map_zero]
  rfl

/-- A fitting map between two solutions of the same problem is surjective. -/
public lemma fittingMap_surjective (F : (comparisonDiagram X Y).FittingMap) :
    Function.Surjective (fittingMapHom F) := by
  intro y
  obtain ⟨x, hx⟩ := X.surjective (Y.toB y)
  obtain ⟨n, hn⟩ := exists_kernelEquiv_eq Y (x := y - fittingMapHom F x) (by
    rw [map_sub, fittingMap_toB_apply F x, hx, sub_self])
  refine ⟨x + ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B'), ?_⟩
  rw [map_add, fittingMap_kernel_apply F n, hn]
  abel

/-- A fitting map of a comparison diagram, as a map of `A'`-algebras. -/
public def fittingMapAlgHom (F : (comparisonDiagram X Y).FittingMap) : X.B' →ₐ[S.A'] Y.B' where
  __ := fittingMapHom F
  commutes' := fun a ↦ DFunLike.congr_fun F.toA'_comm a

/-- A fitting map of the comparison diagram of two solutions of the same problem is
automatically an isomorphism of solutions. -/
public noncomputable def isoOfFittingMap (F : (comparisonDiagram X Y).FittingMap) :
    SquareZeroExtensionProblem.CompatibleExtension.Iso X Y where
  toAlgEquiv := AlgEquiv.ofBijective (fittingMapAlgHom F)
    ⟨fittingMap_injective F, fittingMap_surjective F⟩
  toB_comm := by
    ext x
    exact fittingMap_toB_apply F x
  kernelEquiv_comm := fun n ↦ fittingMap_kernel_apply F n

/-- An isomorphism of solutions is a fitting map of their comparison diagram. -/
public def fittingMapOfIso (e : SquareZeroExtensionProblem.CompatibleExtension.Iso X Y) :
    (comparisonDiagram X Y).FittingMap where
  toRingHom := e.toAlgEquiv.toRingEquiv.toRingHom
  toA'_comm := RingHom.ext fun a ↦ e.toAlgEquiv.commutes a
  toB_comm := RingHom.ext fun x ↦ DFunLike.congr_fun e.toB_comm x
  kernel_comm := fun n ↦ e.kernelEquiv_comm n

/-- The identity map is a fitting map of the comparison diagram of a solution with
itself. -/
public def identityFittingMap (X : S.CompatibleExtension.{v}) :
    (comparisonDiagram X X).FittingMap :=
  fittingMapOfIso (SquareZeroExtensionProblem.CompatibleExtension.Iso.refl X)

end FittingMaps

/-- The obstruction class of the pair `(X, Y)` in the conormal cokernel. -/
public noncomputable def obstructionCokernelClass (X Y : S.CompatibleExtension.{v}) :
    conormalCokernel S :=
  Submodule.Quotient.mk (obstructionFunctional X Y)

/-- The obstruction class of `(X, Y)` vanishes exactly when the comparison diagram of `X`
and `Y` has a fitting map. -/
public lemma obstructionCokernelClass_eq_zero_iff_nonempty_fittingMap
    (X Y : S.CompatibleExtension.{v}) :
    obstructionCokernelClass X Y = 0 ↔ Nonempty (comparisonDiagram X Y).FittingMap :=
  conormalClass_eq_zero_iff_fittingMap (comparisonDiagram X Y)

/-- The obstruction class vanishes exactly when the two solutions are isomorphic. -/
public lemma obstructionCokernelClass_eq_zero_iff (X Y : S.CompatibleExtension.{v}) :
    obstructionCokernelClass X Y = 0 ↔
      SquareZeroExtensionProblem.CompatibleExtension.Isomorphic X Y := by
  rw [obstructionCokernelClass_eq_zero_iff_nonempty_fittingMap]
  exact ⟨fun ⟨F⟩ ↦ ⟨isoOfFittingMap F⟩, fun ⟨e⟩ ↦ ⟨fittingMapOfIso e⟩⟩

/-- The obstruction classes of three solutions add up. -/
public lemma obstructionCokernelClass_add (X Y Z : S.CompatibleExtension.{v}) :
    obstructionCokernelClass X Y + obstructionCokernelClass Y Z =
      obstructionCokernelClass X Z := by
  have h := obstructionFunctional_add X Y Z
  change Submodule.Quotient.mk (obstructionFunctional X Y) +
      Submodule.Quotient.mk (obstructionFunctional Y Z) =
    Submodule.Quotient.mk (obstructionFunctional X Z)
  rw [← h]
  rfl

/-- The obstruction class of a solution with itself vanishes. -/
@[simp]
public lemma obstructionCokernelClass_self (X : S.CompatibleExtension.{v}) :
    obstructionCokernelClass X X = 0 :=
  (obstructionCokernelClass_eq_zero_iff_nonempty_fittingMap X X).mpr ⟨identityFittingMap X⟩

/-- Swapping the two solutions negates the obstruction class. -/
public lemma obstructionCokernelClass_comm (X Y : S.CompatibleExtension.{v}) :
    obstructionCokernelClass Y X = -obstructionCokernelClass X Y := by
  have h := obstructionCokernelClass_add X Y X
  rw [obstructionCokernelClass_self] at h
  rw [add_comm] at h
  exact add_eq_zero_iff_eq_neg.mp h

/-- The obstruction class only depends on the isomorphism class of the source. -/
public lemma obstructionCokernelClass_congr_left {X X' Y : S.CompatibleExtension.{v}}
    (e : SquareZeroExtensionProblem.CompatibleExtension.Iso X X') :
    obstructionCokernelClass X' Y = obstructionCokernelClass X Y := by
  have h0 : obstructionCokernelClass X' X = 0 :=
    (obstructionCokernelClass_eq_zero_iff X' X).mpr ⟨e.symm⟩
  have h := obstructionCokernelClass_add X' X Y
  rw [h0, zero_add] at h
  exact h.symm

/-- The obstruction class only depends on the isomorphism class of the target. -/
public lemma obstructionCokernelClass_congr_right {X Y Y' : S.CompatibleExtension.{v}}
    (e : SquareZeroExtensionProblem.CompatibleExtension.Iso Y Y') :
    obstructionCokernelClass X Y' = obstructionCokernelClass X Y := by
  have h0 : obstructionCokernelClass Y Y' = 0 :=
    (obstructionCokernelClass_eq_zero_iff Y Y').mpr ⟨e⟩
  have h := obstructionCokernelClass_add X Y Y'
  rw [h0, add_zero] at h
  exact h.symm

end Stacks.Deformation

end
