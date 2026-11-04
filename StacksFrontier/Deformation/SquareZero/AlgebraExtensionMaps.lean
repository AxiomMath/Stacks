module

public import StacksFrontier.Deformation.SquareZero.AlgebraExtensions

/-!
# Maps between square-zero extensions along a ring map (Stacks 0GPV)

Let `A → B → C` be ring maps, let `M` be a `B`-module, let `N` be a `C`-module and let
`c : M → N` be `B`-linear.  Given square-zero extensions `0 → M → B' → B → 0` and
`0 → N → C' → C → 0` of `A`-algebras, with classes `ξ ∈ Ext¹_B(NL_{B/A}, M)` and
`ζ ∈ Ext¹_C(NL_{C/A}, N)` under the classification of **Stacks 0GPT**, there is an
`A`-algebra map `B' → C'` compatible with `B → C` and with `c` exactly when `ξ` and `ζ` have
the same image in `Ext¹_B(NL_{B/A}, N)`.

## Main definitions

* `Stacks.Deformation.naiveCotangentExtOneMap` is the map
  `Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)` induced by `c`.
* `Stacks.Deformation.naiveCotangentExtOneTowerMap` is the map
  `Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N)` given by restriction along `B → C` followed
  by precomposition with the canonical map `NL_{B/A} → NL_{C/A}`.
* `Stacks.Deformation.towerDiagram` is the deformation diagram of the two extensions,
  whose lower rows are the identity extension of `A`.

## Main results

* `Stacks.Deformation.exists_compatible_algebraMap_iff`: **Stacks 0GPV**.

## Implementation notes

Both maps on first Ext are built from the presentation of `Ext¹_B(NL_{B/A}, N)` by conormal
functionals, `Stacks.Deformation.extCokernelIso`: on a functional `δ : J/J² → M` the first
map is `δ ↦ c ∘ δ`, and on a functional `e : J_C/J_C² → N` the second is
`e ↦ e|_B ∘ NL_{B/A} → NL_{C/A}`.  Carrying the coefficient modules in separate universes is
what forces this, since `Ext¹_B(NL_{B/A}, M)` and `Ext¹_B(NL_{B/A}, N)` are then constructed
in different universes of module categories.

The proof compares the diagram of `X` and `Y` with the diagram of the two split extensions,
whose canonical obstruction vanishes because `b + m ↦ b + c(m)` fits it; the difference of
the two conormal functionals is the difference of the images of the two classes, and
**Stacks 08S5** turns the vanishing of the resulting class into the existence of the map.

## References

* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public noncomputable section

universe uA uB uC uM uN

open CategoryTheory

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard
  SquareZeroExtensionProblem.CompatibleExtension.commRingB'
  SquareZeroExtensionProblem.CompatibleExtension.algebraA'B'

/-- The ring of a square-zero extension of the `A`-algebra `B` is itself an `A`-algebra. -/
public instance instAlgebraCompatibleExtensionB' {A : Type*} {B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] {M : Type*} [AddCommGroup M] [Module B M]
    (X : (algebraExtensionProblem A B M).CompatibleExtension) : Algebra A X.B' :=
  X.algebraA'B'

variable (A : Type uA) (B : Type uB) (C : Type uC)
  [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- The canonical morphism of presentations `A[B] → A[C]` over `A → B → C`. -/
public def towerPresentationHom :
    (Algebra.Generators.self A B).Hom (Algebra.Generators.self A C) :=
  (Algebra.Generators.self A B).defaultHom (Algebra.Generators.self A C)

/-- Degree `1` of the canonical map `NL_{B/A} → NL_{C/A}`. -/
public def towerConormal :
    (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B]
      (Algebra.Generators.self A C).toExtension.Cotangent :=
  Algebra.Extension.Cotangent.map (towerPresentationHom A B C).toExtensionHom

/-- Degree `0` of the canonical map `NL_{B/A} → NL_{C/A}`. -/
public def towerCotangentSpace :
    (Algebra.Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Algebra.Generators.self A C).toExtension.CotangentSpace :=
  Algebra.Extension.CotangentSpace.map (towerPresentationHom A B C).toExtensionHom

/-- The comparison `A[B] → A[C]` of canonical presentations along `B → C`. -/
public def towerPolyHom : MvPolynomial B A →ₐ[A] MvPolynomial C A :=
  (towerPresentationHom A B C).toAlgHom

omit [IsScalarTower A B C] in
public lemma towerPolyHom_X (b : B) :
    towerPolyHom A B C (MvPolynomial.X b) = MvPolynomial.X (algebraMap B C b) := by
  rw [towerPolyHom, Algebra.Generators.Hom.toAlgHom_X, towerPresentationHom,
    Algebra.Generators.defaultHom_val]
  simp only [Function.comp_apply, Algebra.Generators.self_val, Algebra.Generators.self_σ, id_eq]

omit [IsScalarTower A B C] in
public lemma towerPolyHom_C (a : A) :
    towerPolyHom A B C (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [show (MvPolynomial.C a : MvPolynomial B A) = algebraMap A (MvPolynomial B A) a from rfl,
    AlgHom.commutes]
  rfl

/-- The cokernel `Hom_B(J/J², N) / Hom_B(Ω_{A[B]/A} ⊗ B, N)` presenting
`Ext¹_B(NL_{B/A}, N)`. -/
public abbrev extOneCokernel (N : Type uN) [AddCommGroup N] [Module B N] :=
  ((Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) ⧸
    LinearMap.range (LinearMap.lcomp B N
      (Algebra.Generators.self A B).toExtension.cotangentComplex)

variable {M : Type uM} [AddCommGroup M] [Module B M]
  {N : Type uN} [AddCommGroup N] [Module B N] [Module C N] [IsScalarTower B C N]

/-- Restriction along `B → C` followed by precomposition with `NL_{B/A} → NL_{C/A}`. -/
public def towerConormalPullback :
    ((Algebra.Generators.self A C).toExtension.Cotangent →ₗ[C] N) →ₗ[B]
      ((Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) where
  toFun e := (e.restrictScalars B).comp (towerConormal A B C)
  map_add' e f := by ext x; simp
  map_smul' b e := by ext x; simp

/-- Postcomposition with `c : M → N` on conormal functionals. -/
public def towerConormalPush (c : M →ₗ[B] N) :
    ((Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] M) →ₗ[B]
      ((Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) where
  toFun δ := c.comp δ
  map_add' δ ε := by ext x; simp
  map_smul' b δ := by ext x; simp

/-- The map `Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)` induced by `c`, on cokernels. -/
public def conormalCokernelPush (c : M →ₗ[B] N) :
    extOneCokernel A B M →+ extOneCokernel A B N :=
  (Submodule.mapQ _ _ (towerConormalPush A B c) (by
    rintro δ ⟨t, rfl⟩
    exact ⟨c.comp t, rfl⟩)).toAddMonoidHom

/-- The map `Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N)` of the lemma, on cokernels. -/
public def conormalCokernelPullback :
    extOneCokernel A C N →+ extOneCokernel A B N :=
  (Submodule.mapQ ((LinearMap.lcomp C N
      (Algebra.Generators.self A C).toExtension.cotangentComplex).range.restrictScalars B)
    _ (towerConormalPullback A B C) (by
      rintro e ⟨t, rfl⟩
      refine ⟨(t.restrictScalars B).comp (towerCotangentSpace A B C), ?_⟩
      ext x
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, towerConormalPullback,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_restrictScalars, towerConormal,
        towerCotangentSpace]
      exact congrArg t (Algebra.Extension.CotangentSpace.map_cotangentComplex
        (towerPresentationHom A B C).toExtensionHom x))).toAddMonoidHom

/-- The deformation diagram of two square-zero extensions of `A`-algebras along `B → C`. -/
public def towerDiagram (c : M →ₗ[B] N)
    (X : (algebraExtensionProblem A B M).CompatibleExtension.{max uB uM})
    (Y : (algebraExtensionProblem A C N).CompatibleExtension.{max uC uN}) :
    CompatibleSquareZeroDeformationDiagram.{uA, uA, uB, uM, uA, uA, uC, uN,
      max uB uM, max uC uN} where
  S₁ := algebraExtensionProblem A B M
  S₂ := algebraExtensionProblem A C N
  X₁ := X
  X₂ := Y
  algebraA'₁A'₂ := inferInstanceAs (Algebra A A)
  algebraA₁A₂ := inferInstanceAs (Algebra A A)
  algebraB₁B₂ := inferInstanceAs (Algebra B C)
  toA_comm := rfl
  toB_comm := by
    change (algebraMap A C).comp (algebraMap A A) = (algebraMap B C).comp (algebraMap A B)
    ext a
    simpa using IsScalarTower.algebraMap_apply A B C a
  moduleB₁N₂ := inferInstanceAs (Module B N)
  isScalarTowerB₁B₂N₂ := inferInstanceAs (IsScalarTower B C N)
  mapN := c
  map_I := fun i ↦ by
    rw [Ideal.mem_bot.mp i.2, map_zero]
    exact Submodule.zero_mem _
  map_c := fun i ↦ by
    have h₁ : (algebraExtensionProblem A B M).c = 0 := rfl
    have h₂ : (algebraExtensionProblem A C N).c = 0 := rfl
    rw [h₁, h₂]
    exact map_zero c

/-- The map `B ⋉ M → C ⋉ N` of split square-zero extensions induced by `B → C` and `c`. -/
public def splitTowerMap (c : M →ₗ[B] N) :
    (splitAlgebraExtension A B M).B' →+* (splitAlgebraExtension A C N).B' where
  toFun x := (⟨algebraMap B C x.fst, c x.snd⟩ : TrivSqZeroExt C N)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap B C)) (map_zero c)
  map_mul' x y := by
    refine TrivSqZeroExt.ext (map_mul (algebraMap B C) x.fst y.fst) ?_
    change c (x.fst • y.snd + y.fst • x.snd)
      = algebraMap B C x.fst • c y.snd + algebraMap B C y.fst • c x.snd
    rw [map_add, c.map_smul, c.map_smul, IsScalarTower.algebraMap_smul C x.fst (c y.snd),
      IsScalarTower.algebraMap_smul C y.fst (c x.snd)]
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap B C)) (map_zero c)
  map_add' x y := TrivSqZeroExt.ext (map_add (algebraMap B C) x.fst y.fst)
    (map_add c x.snd y.snd)

/-- The split extensions of `B` by `M` and of `C` by `N` are compatible along `c`. -/
public def splitTowerFittingMap (c : M →ₗ[B] N) :
    (towerDiagram A B C c (splitAlgebraExtension A B M)
      (splitAlgebraExtension A C N)).FittingMap where
  toRingHom := splitTowerMap A B C c
  toA'_comm := by
    ext a
    refine TrivSqZeroExt.ext ?_ (map_zero c)
    change algebraMap B C (algebraMap A B a) = algebraMap A C a
    exact (IsScalarTower.algebraMap_apply A B C a).symm
  toB_comm := rfl
  kernel_comm := fun m ↦ TrivSqZeroExt.ext (map_zero (algebraMap B C)) rfl

section Comparison

variable (c : M →ₗ[B] N)
    (X : (algebraExtensionProblem A B M).CompatibleExtension.{max uB uM})
    (Y : (algebraExtensionProblem A C N).CompatibleExtension.{max uC uN})

/-- A relation of the canonical presentation `A[B] → B`, carried to a relation of
`A[C] → C`. -/
public def towerRelation
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N))) :
    RingHom.ker (problemPresentationToB (algebraExtensionProblem A C N)) :=
  ⟨towerPolyHom A B C x.1, by
    apply RingHom.mem_ker.mpr
    refine (Algebra.Generators.Hom.algebraMap_toAlgHom
      (towerPresentationHom A B C) x.1).trans ?_
    exact (congrArg (algebraMap B C) (RingHom.mem_ker.mp x.2)).trans (map_zero _)⟩

/-- The evaluation at the chosen lifts of a solution over `C`, on relations of `A[C] → C`. -/
public def towerRelationEval
    (Z : (algebraExtensionProblem A C N).CompatibleExtension.{max uC uN})
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A C N))) : N :=
  solutionRelationEval Z x

/-- The evaluation at the chosen lifts of a solution over `B`, on relations of `A[B] → B`. -/
public def baseRelationEval
    (Z : (algebraExtensionProblem A B M).CompatibleExtension.{max uB uM})
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N))) : M :=
  solutionRelationEval Z x

/-- The class of a solution over `C` relative to the split extension. -/
public def towerObstruction
    (Z : (algebraExtensionProblem A C N).CompatibleExtension.{max uC uN}) :
    (Algebra.Generators.self A C).toExtension.Cotangent →ₗ[C] N :=
  obstructionFunctional (splitAlgebraExtension A C N) Z

/-- The class of a solution over `B` relative to the split extension. -/
public def baseObstruction
    (Z : (algebraExtensionProblem A B M).CompatibleExtension.{max uB uM}) :
    (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] M :=
  obstructionFunctional (splitAlgebraExtension A B M) Z

public lemma towerObstruction_mk
    (Z : (algebraExtensionProblem A C N).CompatibleExtension.{max uC uN})
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A C N))) :
    towerObstruction A C Z
        (Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self A C).toExtension)
          (reducedRelationOf (algebraExtensionProblem A C N) x))
      = towerRelationEval A C Z x
        - towerRelationEval A C (splitAlgebraExtension A C N) x :=
  obstructionFunctional_mk (splitAlgebraExtension A C N) Z x

public lemma baseObstruction_mk
    (Z : (algebraExtensionProblem A B M).CompatibleExtension.{max uB uM})
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N))) :
    baseObstruction A B Z
        (Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self A B).toExtension)
          (reducedRelationOf (algebraExtensionProblem A B N) x))
      = baseRelationEval A B Z x
        - baseRelationEval A B (splitAlgebraExtension A B M) x :=
  obstructionFunctional_mk (splitAlgebraExtension A B M) Z x

/-- Evaluation of `A[B]` in the ring of `Y`, at the chosen lifts of the images in `C`. -/
public def towerEval₂ : MvPolynomial B A →+* Y.B' :=
  (presentationEval₂ (towerDiagram A B C c X Y)).comp (RingHom.id (MvPolynomial B A))

/-- Evaluation of `A[C]` in the ring of `Y`, at the chosen lifts of `Y`. -/
public def towerSolutionEval : MvPolynomial C A →+* Y.B' :=
  (solutionEval Y).toRingHom.comp (RingHom.id (MvPolynomial C A))

public lemma towerEval₂_X (b : B) :
    towerEval₂ A B C c X Y (MvPolynomial.X b)
      = lift₂ (towerDiagram A B C c X Y) b :=
  MvPolynomial.eval₂_X _ _ b

public lemma towerSolutionEval_X (z : C) :
    towerSolutionEval A C Y (MvPolynomial.X z) = lift₁ (comparisonDiagram Y Y) z :=
  MvPolynomial.eval₂_X _ _ z

public lemma towerEval₂_C (a : A) :
    towerEval₂ A B C c X Y (MvPolynomial.C a)
      = towerSolutionEval A C Y (MvPolynomial.C a) :=
  (MvPolynomial.eval₂_C _ _ a).trans (MvPolynomial.eval₂_C _ _ a).symm

public lemma towerEval₂_eq (p : MvPolynomial B A) :
    towerEval₂ A B C c X Y p = towerSolutionEval A C Y (towerPolyHom A B C p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [towerPolyHom_C, towerEval₂_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p b hp =>
      rw [map_mul, map_mul, map_mul, hp, towerPolyHom_X, towerEval₂_X,
        towerSolutionEval_X]
      rfl

/-- The conormal functional of the diagram of `X` and `Y`, at its canonical type. -/
public def towerFunctional :
    (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N :=
  conormalFunctional (towerDiagram A B C c X Y)

public lemma relationEval₂_towerDiagram
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N))) :
    towerRelationEval A C Y (towerRelation A B C x)
      = relationEval₂ (towerDiagram A B C c X Y) x := by
  have h₁ : kernelInclusion Y (relationEval₂ (towerDiagram A B C c X Y) x)
      = towerEval₂ A B C c X Y x.1 :=
    relationEval₂_spec (towerDiagram A B C c X Y) x
  have h₂ : kernelInclusion Y (solutionRelationEval Y (towerRelation A B C x))
      = towerSolutionEval A C Y (towerPolyHom A B C x.1) :=
    kernelInclusion_solutionRelationEval Y (towerRelation A B C x)
  exact kernelInclusion_injective Y
    (h₂.trans ((towerEval₂_eq A B C c X Y x.1).symm.trans h₁.symm))

public lemma towerFunctional_mk
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N))) :
    towerFunctional A B C c X Y
        (Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self A B).toExtension)
          (reducedRelationOf (algebraExtensionProblem A B N) x))
      = towerRelationEval A C Y (towerRelation A B C x)
        - c (baseRelationEval A B X x) :=
  (conormalFunctional_reducedRelation (towerDiagram A B C c X Y) x).trans <|
    congrArg (fun n : N ↦ n - c (baseRelationEval A B X x))
      (relationEval₂_towerDiagram A B C c X Y x).symm

omit [IsScalarTower B C N] in
public lemma towerConormal_mk_reducedRelationOf
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N))) :
    towerConormal A B C (Algebra.Extension.Cotangent.mk
        (P := (Algebra.Generators.self A B).toExtension)
        (reducedRelationOf (algebraExtensionProblem A B N) x))
      = Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self A C).toExtension)
          (reducedRelationOf (algebraExtensionProblem A C N) (towerRelation A B C x)) := by
  refine (Algebra.Extension.Cotangent.map_mk (towerPresentationHom A B C).toExtensionHom
    (reducedRelationOf (algebraExtensionProblem A B N) x)).trans ?_
  refine congrArg (Algebra.Extension.Cotangent.mk
    (P := (Algebra.Generators.self A C).toExtension)) (Subtype.ext ?_)
  change towerPolyHom A B C (reduceCoefficients (algebraExtensionProblem A B N) x.1)
    = reduceCoefficients (algebraExtensionProblem A C N) (towerPolyHom A B C x.1)
  exact congrArg (towerPolyHom A B C) (MvPolynomial.map_id _) |>.trans (MvPolynomial.map_id _).symm

@[simp]
public lemma towerConormalPullback_apply
    (e : (Algebra.Generators.self A C).toExtension.Cotangent →ₗ[C] N)
    (t : (Algebra.Generators.self A B).toExtension.Cotangent) :
    towerConormalPullback A B C e t = e (towerConormal A B C t) := rfl

@[simp]
public lemma towerConormalPush_apply
    (δ : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] M)
    (t : (Algebra.Generators.self A B).toExtension.Cotangent) :
    towerConormalPush A B c δ t = c (δ t) := rfl

/-- Two conormal functionals which agree on the classes of all reduced relations of
`A[B] → B` are equal. -/
public lemma conormalFunctional_ext'
    {f g : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N}
    (h : ∀ x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N)),
      f (Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self A B).toExtension)
          (reducedRelationOf (algebraExtensionProblem A B N) x))
        = g (Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self A B).toExtension)
            (reducedRelationOf (algebraExtensionProblem A B N) x))) : f = g :=
  conormalFunctional_ext (S := algebraExtensionProblem A B N) h

/-- The class of the diagram of `X` and `Y` differs from that of the split diagram by the
difference of the two images of the classes of `X` and of `Y`. -/
public lemma towerFunctional_eq :
    towerFunctional A B C c X Y
      = towerFunctional A B C c (splitAlgebraExtension A B M) (splitAlgebraExtension A C N)
        + (towerConormalPullback A B C (towerObstruction A C Y)
            - towerConormalPush A B c (baseObstruction A B X)) := by
  refine conormalFunctional_ext' A B fun x ↦ ?_
  rw [LinearMap.add_apply, LinearMap.sub_apply,
    towerFunctional_mk A B C c X Y x,
    towerFunctional_mk A B C c (splitAlgebraExtension A B M)
      (splitAlgebraExtension A C N) x,
    towerConormalPullback_apply, towerConormalPush_apply,
    towerConormal_mk_reducedRelationOf A B C x,
    towerObstruction_mk A C Y (towerRelation A B C x),
    baseObstruction_mk A B X x, map_sub]
  abel

/-- The split extensions are compatible, so their diagram has vanishing class. -/
public lemma towerFunctional_split_eq_zero :
    (Submodule.Quotient.mk (towerFunctional A B C c (splitAlgebraExtension A B M)
        (splitAlgebraExtension A C N)) : extOneCokernel A B N) = 0 :=
  (conormalClass_eq_zero_iff_fittingMap _).mpr ⟨splitTowerFittingMap A B C c⟩

/-- The map `Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)` induced by `c : M → N`. -/
public def naiveCotangentExtOneMap (c : M →ₗ[B] N) :
    naiveCotangentExtOne A B M →+ naiveCotangentExtOne A B N :=
  ((extCokernelIso A B N).symm.toAddMonoidHom.comp (conormalCokernelPush A B c)).comp
    (extCokernelIso A B M).toAddMonoidHom

/-- The map `Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N)` given by restriction along `B → C`
followed by precomposition with the canonical map `NL_{B/A} → NL_{C/A}`. -/
public def naiveCotangentExtOneTowerMap :
    naiveCotangentExtOne A C N →+ naiveCotangentExtOne A B N :=
  ((extCokernelIso A B N).symm.toAddMonoidHom.comp (conormalCokernelPullback A B C)).comp
    (extCokernelIso A C N).toAddMonoidHom

section Classes

variable (c : M →ₗ[B] N)
    (X : (algebraExtensionProblem A B M).CompatibleExtension.{max uB uM})
    (Y : (algebraExtensionProblem A C N).CompatibleExtension.{max uC uN})

public lemma extOneCokernel_mk_add
    (f g : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    (Submodule.Quotient.mk (f + g) : extOneCokernel A B N)
      = Submodule.Quotient.mk f + Submodule.Quotient.mk g := rfl

public lemma extOneCokernel_mk_sub
    (f g : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    (Submodule.Quotient.mk (f - g) : extOneCokernel A B N)
      = Submodule.Quotient.mk f - Submodule.Quotient.mk g := rfl

/-- Under the presentation of `Ext¹_B(NL_{B/A}, M)` by conormal functionals, the class of `X`
is the obstruction class comparing the split extension with `X`. -/
public lemma extCokernelIso_classEquiv_base :
    extCokernelIso A B M (squareZeroAlgebraExtensionClassesEquivExtOne A B M
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A B M)) X))
      = Submodule.Quotient.mk (baseObstruction A B X) := by
  have h : squareZeroAlgebraExtensionClassesEquivExtOne A B M
      (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
        (algebraExtensionProblem A B M)) X)
      = (obstructionClass (comparisonDiagram (splitAlgebraExtension A B M) X)).1 :=
    isomorphismClasses_vsub_eq_obstructionClass (algebraExtensionProblem A B M)
      ⟨splitAlgebraExtension A B M⟩ (splitAlgebraExtension A B M) X
  rw [h]
  exact (extCokernelIso A B M).apply_symm_apply _

/-- The same statement for the extension `Y` of `C` by `N`. -/
public lemma extCokernelIso_classEquiv_tower :
    extCokernelIso A C N (squareZeroAlgebraExtensionClassesEquivExtOne A C N
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A C N)) Y))
      = Submodule.Quotient.mk (towerObstruction A C Y) :=
  extCokernelIso_classEquiv_base A C Y

public lemma naiveCotangentExtOneMap_classEquiv :
    naiveCotangentExtOneMap A B c (squareZeroAlgebraExtensionClassesEquivExtOne A B M
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A B M)) X))
      = (extCokernelIso A B N).symm
        (Submodule.Quotient.mk (towerConormalPush A B c (baseObstruction A B X))) := by
  show (extCokernelIso A B N).symm (conormalCokernelPush A B c
    (extCokernelIso A B M (squareZeroAlgebraExtensionClassesEquivExtOne A B M
      (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
        (algebraExtensionProblem A B M)) X)))) = _
  rw [extCokernelIso_classEquiv_base]
  rfl

public lemma naiveCotangentExtOneTowerMap_classEquiv :
    naiveCotangentExtOneTowerMap A B C (squareZeroAlgebraExtensionClassesEquivExtOne A C N
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A C N)) Y))
      = (extCokernelIso A B N).symm
        (Submodule.Quotient.mk (towerConormalPullback A B C (towerObstruction A C Y))) := by
  show (extCokernelIso A B N).symm (conormalCokernelPullback A B C
    (extCokernelIso A C N (squareZeroAlgebraExtensionClassesEquivExtOne A C N
      (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
        (algebraExtensionProblem A C N)) Y)))) = _
  rw [extCokernelIso_classEquiv_tower]
  rfl

/-- A fitting map of the diagram is the same thing as an `A`-algebra map `B' → C'` compatible
with `B → C` and with `c`. -/
public lemma nonempty_fittingMap_towerDiagram_iff :
    Nonempty (towerDiagram A B C c X Y).FittingMap ↔
      ∃ h : X.B' →ₐ[A] Y.B',
        (∀ z : X.B', Y.toB (h z) = algebraMap B C (X.toB z)) ∧
          ∀ m : M, h (kernelInclusion X m) = kernelInclusion Y (c m) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨{ toRingHom := F.toRingHom
             commutes' := fun a ↦ DFunLike.congr_fun F.toA'_comm a },
      fun z ↦ DFunLike.congr_fun F.toB_comm z, F.kernel_comm⟩
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨{ toRingHom := h.toRingHom
             toA'_comm := RingHom.ext fun a ↦ h.commutes a
             toB_comm := RingHom.ext fun z ↦ h₁ z
             kernel_comm := h₂ }⟩

/-- **Stacks 0GPV.**  Given ring maps `A → B → C`, a `B`-module `M`, a `C`-module `N`, a
`B`-linear map `c : M → N`, a square-zero extension `0 → M → B' → B → 0` of `A`-algebras with
class `ξ ∈ Ext¹_B(NL_{B/A}, M)` and a square-zero extension `0 → N → C' → C → 0` of
`A`-algebras with class `ζ ∈ Ext¹_C(NL_{C/A}, N)`, there is an `A`-algebra map `B' → C'`
compatible with `B → C` and with `c` if and only if `ξ` and `ζ` have the same image in
`Ext¹_B(NL_{B/A}, N)`. -/
@[stacks 0GPV]
public theorem exists_compatible_algebraMap_iff :
    (∃ h : X.B' →ₐ[A] Y.B',
        (∀ z : X.B', Y.toB (h z) = algebraMap B C (X.toB z)) ∧
          ∀ m : M, h (kernelInclusion X m) = kernelInclusion Y (c m)) ↔
      naiveCotangentExtOneMap A B c (squareZeroAlgebraExtensionClassesEquivExtOne A B M
          (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
            (algebraExtensionProblem A B M)) X))
        = naiveCotangentExtOneTowerMap A B C
          (squareZeroAlgebraExtensionClassesEquivExtOne A C N
            (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
              (algebraExtensionProblem A C N)) Y)) := by
  have hfit : Nonempty (towerDiagram A B C c X Y).FittingMap ↔
      (Submodule.Quotient.mk (towerFunctional A B C c X Y) : extOneCokernel A B N) = 0 :=
    (conormalClass_eq_zero_iff_fittingMap (towerDiagram A B C c X Y)).symm
  have hcls : (Submodule.Quotient.mk (towerFunctional A B C c X Y) : extOneCokernel A B N)
      = Submodule.Quotient.mk (towerConormalPullback A B C (towerObstruction A C Y))
        - Submodule.Quotient.mk (towerConormalPush A B c (baseObstruction A B X)) := by
    rw [towerFunctional_eq, extOneCokernel_mk_add, extOneCokernel_mk_sub,
      towerFunctional_split_eq_zero, zero_add]
  rw [← nonempty_fittingMap_towerDiagram_iff, hfit, hcls, sub_eq_zero,
    naiveCotangentExtOneMap_classEquiv, naiveCotangentExtOneTowerMap_classEquiv,
    (extCokernelIso A B N).symm.injective.eq_iff]
  exact eq_comm

end Classes

end Comparison

end Stacks.Deformation

end
