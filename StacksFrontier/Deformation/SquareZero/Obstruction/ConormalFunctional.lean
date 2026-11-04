module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Deformation.SquareZero.Obstruction.RelationDifference

/-!
# The conormal functional of a square-zero deformation diagram

The relation difference on the reduced polynomial presentation, its descent to the conormal
module, the resulting conormal functional, and the comparison of the first Ext group from the
naive cotangent complex with the cokernel of the conormal differential.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- `Algebra.Generators.toExtension` is a semireducible `def`, so the two spellings of its
-- polynomial ring -- `P.toExtension.Ring` and `P.Ring` -- do not unify at the transparency
-- that `simp` and `rw` use. Making it implicit-reducible here lets both spellings match.
attribute [local implicit_reducible] Algebra.Generators.toExtension

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂

namespace Stacks.Deformation
attribute [local instance] HasDerivedCategory.standard

/-- The difference of evaluations on the relation ideal of the reduced presentation. -/
public noncomputable def reducedRelationDifference
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    RingHom.ker (reducedPresentationToB D) →+ D.S₂.N where
  toFun x := relationDifference D (Classical.choose (reducedRelation_has_lift D x))
  map_zero' :=
    (relationDifference_eq_of_reduction_eq D
      (Classical.choose (reducedRelation_has_lift D 0)) (0 : RingHom.ker (presentationToB D))
      ((Classical.choose_spec (reducedRelation_has_lift D
        (0 : RingHom.ker (reducedPresentationToB D)))).trans (by simp))).trans (map_zero _)
  map_add' x y := by
    let lx := Classical.choose (reducedRelation_has_lift D x)
    let ly := Classical.choose (reducedRelation_has_lift D y)
    have hx := Classical.choose_spec (reducedRelation_has_lift D x)
    have hy := Classical.choose_spec (reducedRelation_has_lift D y)
    refine (relationDifference_eq_of_reduction_eq D
      (Classical.choose (reducedRelation_has_lift D (x + y))) (lx + ly) ?_).trans
      (map_add _ lx ly)
    calc
      _ = (x + y).1 := Classical.choose_spec (reducedRelation_has_lift D (x + y))
      _ = x.1 + y.1 := rfl
      _ = coefficientReduction D lx.1 + coefficientReduction D ly.1 := by rw [hx, hy]
      _ = coefficientReduction D (lx + ly).1 := by
        rw [show (lx + ly).1 = lx.1 + ly.1 from rfl, map_add]

/-- The coefficient reduction of a relation is a relation of the reduced presentation. -/
private theorem coefficientReduction_mem_ker
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    coefficientReduction D x.1 ∈ RingHom.ker (reducedPresentationToB D) := by
  apply RingHom.mem_ker.mpr
  have h := DFunLike.congr_fun (presentationToB_factor D) x.1
  change reducedPresentationToB D (coefficientReduction D x.1) =
    presentationToB D x.1 at h
  rw [h]
  exact RingHom.mem_ker.mp x.2

/-- The reduced relation difference of the coefficient reduction of a relation is its relation
difference. -/
public theorem reducedRelationDifference_spec
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    reducedRelationDifference D
      ⟨coefficientReduction D x.1, by
        apply RingHom.mem_ker.mpr
        have h := DFunLike.congr_fun (presentationToB_factor D) x.1
        change reducedPresentationToB D (coefficientReduction D x.1) =
          presentationToB D x.1 at h
        rw [h]
        exact RingHom.mem_ker.mp x.2⟩ = relationDifference D x := by
  let y : RingHom.ker (reducedPresentationToB D) := ⟨_, coefficientReduction_mem_ker D x⟩
  unfold reducedRelationDifference
  change relationDifference D (Classical.choose (reducedRelation_has_lift D y)) =
    relationDifference D x
  exact relationDifference_eq_of_reduction_eq D _ x
    (Classical.choose_spec (reducedRelation_has_lift D y))

/-- The reduced relation difference of a relation whose underlying element is the coefficient
reduction of `y` is the relation difference of `y`. -/
private theorem reducedRelationDifference_eq_of_eq_coefficientReduction
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (reducedPresentationToB D)) (y : RingHom.ker (presentationToB D))
    (h : x.1 = coefficientReduction D y.1) :
    reducedRelationDifference D x = relationDifference D y := by
  rw [← reducedRelationDifference_spec D y]
  exact congrArg _ (Subtype.ext h)

/-- The reduced relation difference is linear over `A₁[B₁]`, which acts on `N₂` through
`B₁`. -/
public theorem reducedRelationDifference_mul
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (q : MvPolynomial D.S₁.B D.S₁.A)
    (x : RingHom.ker (reducedPresentationToB D)) :
    reducedRelationDifference D ⟨q * x.1, by
      apply RingHom.mem_ker.mpr
      rw [map_mul, RingHom.mem_ker.mp x.2, mul_zero]⟩ =
      (reducedPresentationToB D q) • reducedRelationDifference D x := by
  obtain ⟨p, hp⟩ := coefficientReduction_surjective D q
  obtain ⟨y, hy⟩ := reducedRelation_has_lift D x
  let z : RingHom.ker (presentationToB D) := ⟨p * y.1, by
    apply RingHom.mem_ker.mpr
    rw [map_mul, RingHom.mem_ker.mp y.2, mul_zero]⟩
  rw [reducedRelationDifference_eq_of_eq_coefficientReduction D _ z
    (by change q * x.1 = coefficientReduction D (p * y.1); rw [map_mul, hp, hy]),
    reducedRelationDifference_eq_of_eq_coefficientReduction D x y hy.symm]
  change relationDifference D ⟨p * y.1, _⟩ =
    (reducedPresentationToB D q) • relationDifference D y
  rw [relationDifference_mul D p y]
  have h := DFunLike.congr_fun (presentationToB_factor D) p
  change reducedPresentationToB D (coefficientReduction D p) = presentationToB D p at h
  rw [hp] at h
  rw [h]

/-- The reduced relation difference as an `A₁[B₁]`-linear map, with `A₁[B₁]` acting on `N₂`
through `B₁`. -/
public noncomputable def reducedRelationDifferenceLinear
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := MvPolynomial D.S₁.B D.S₁.A
    letI : Module P D.S₂.N := Module.compHom D.S₂.N (reducedPresentationToB D)
    RingHom.ker (reducedPresentationToB D) →ₗ[P] D.S₂.N := by
  let : Module (MvPolynomial D.S₁.B D.S₁.A) D.S₂.N :=
    Module.compHom D.S₂.N (reducedPresentationToB D)
  refine { __ := reducedRelationDifference D, map_smul' := ?_ }
  intro p x
  change reducedRelationDifference D ⟨p * x.1, _⟩ =
    (reducedPresentationToB D p) • reducedRelationDifference D x
  exact reducedRelationDifference_mul D p x

/-- The reduced relation difference vanishes on a product of two relations. -/
public theorem reducedRelationDifference_mul_eq_zero
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x y : RingHom.ker (reducedPresentationToB D)) :
    reducedRelationDifference D (x * y) = 0 := by
  obtain ⟨lx, hx⟩ := reducedRelation_has_lift D x
  obtain ⟨ly, hy⟩ := reducedRelation_has_lift D y
  rw [reducedRelationDifference_eq_of_eq_coefficientReduction D (x * y) (lx * ly)
    (by change x.1 * y.1 = coefficientReduction D (lx.1 * ly.1); rw [map_mul, hx, hy]),
    relationDifference_mul_eq_zero]

/-- The reduced relation difference descends to the conormal module `J/J²` of the reduced
presentation. -/
public noncomputable def reducedRelationCotangentLinear
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := MvPolynomial D.S₁.B D.S₁.A
    letI : Module P D.S₂.N := Module.compHom D.S₂.N (reducedPresentationToB D)
    (RingHom.ker (reducedPresentationToB D)).Cotangent →ₗ[P] D.S₂.N := by
  let : Module (MvPolynomial D.S₁.B D.S₁.A) D.S₂.N :=
    Module.compHom D.S₂.N (reducedPresentationToB D)
  exact Ideal.Cotangent.lift (reducedRelationDifferenceLinear D)
    (reducedRelationDifference_mul_eq_zero D)

/-- The conormal functional of the compatible square-zero deformation diagram. -/
public noncomputable def conormalFunctional
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.Cotangent →ₗ[D.S₁.B]
      D.S₂.N := by
  let P := Algebra.Generators.self D.S₁.A D.S₁.B
  let : Module (MvPolynomial D.S₁.B D.S₁.A) D.S₂.N :=
    Module.compHom D.S₂.N (reducedPresentationToB D)
  let : Module P.toExtension.Ring D.S₂.N :=
    Module.compHom D.S₂.N (algebraMap P.toExtension.Ring D.S₁.B)
  let f : P.toExtension.Cotangent →ₗ[P.toExtension.Ring] D.S₂.N := {
    toFun x := reducedRelationCotangentLinear D
      (P.toExtension.cotangentEquivCotangentKer x)
    map_add' x y := map_add (reducedRelationCotangentLinear D) x.val y.val
    map_smul' r x := by
      rw [map_smul P.toExtension.cotangentEquivCotangentKer r x]
      exact map_smul (reducedRelationCotangentLinear D)
        (show MvPolynomial D.S₁.B D.S₁.A from r) _ }
  let : IsScalarTower P.toExtension.Ring D.S₁.B P.toExtension.Cotangent :=
    ⟨fun r s x ↦ by
      change (algebraMap P.toExtension.Ring D.S₁.B r * s) • x =
        algebraMap P.toExtension.Ring D.S₁.B r • s • x
      rw [mul_smul]⟩
  let : IsScalarTower P.toExtension.Ring D.S₁.B D.S₂.N :=
    ⟨fun r s x ↦ by
      change (algebraMap P.toExtension.Ring D.S₁.B r * s) • x =
        algebraMap P.toExtension.Ring D.S₁.B r • s • x
      rw [mul_smul]⟩
  exact f.extendScalarsOfSurjective P.toExtension.algebraMap_surjective

/-- The conormal functional sends the class of a relation to its reduced relation difference. -/
public theorem conormalFunctional_mk
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.ker) :
    conormalFunctional D (Algebra.Extension.Cotangent.mk x) =
      reducedRelationDifference D x := by
  simp only [conormalFunctional, LinearMap.extendScalarsOfSurjective_apply]
  change reducedRelationCotangentLinear D (Ideal.toCotangent _ x) =
    reducedRelationDifference D x
  simp [reducedRelationCotangentLinear]
  rfl

/-- The first Ext group of the two-term naive cotangent complex of `A → B`, with the terms
and the coefficient module lifted into a common module category, is the cokernel of
precomposition with the conormal differential. -/
public noncomputable def extCokernelIso
    (A : Type u₂) (B : Type u₃) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type v₄) [AddCommGroup N] [Module B N] :
    let P := Algebra.Generators.self A B
    let K := ((ModuleCat.uliftFunctor.{v₄} B).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex A B)
    DerivedCategory.Ext
      (DerivedCategory.Q.obj
        (HomologicalComplex.double (K.d 1 0)
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v₄} B) 0).obj
        ((ModuleCat.uliftFunctor.{max u₂ u₃} B).obj
          (ModuleCat.of B N))) 1 ≃+
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range
        (LinearMap.lcomp B N P.toExtension.cotangentComplex)) := by
  let P := Algebra.Generators.self A B
  let K := ((ModuleCat.uliftFunctor.{v₄} B).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex A B)
  let g := ModuleCat.ofHom
    (ULift.moduleEquiv.{u₃, max (max u₂ u₃) u₃, max u₂ u₃ v₄}.symm.toLinearMap.comp
      ((NaiveCotangent.NL P).d.comp
        ULift.moduleEquiv.{u₃, max u₂ u₃, max u₂ u₃ v₄}.toLinearMap))
  let e := HomologicalComplex.singleConeDoubleIso g
  let eN : ULift.{max u₂ u₃} N ≃ₗ[B]
      ULift.{max u₂ u₃ v₄} N :=
    ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  let eY := (DerivedCategory.singleFunctor
    (ModuleCat.{max u₂ u₃ v₄} B) 0).mapIso eN.toModuleIso
  let cmp := (extOneSourceIso ((DerivedCategory.Q).mapIso e)).trans
    (NaiveCotangent.extOne_naiveCotangentComplex_addEquiv_cokernel
      (N := N) P)
  let U₁ : ULift.{v₄} P.toExtension.Cotangent ≃ₗ[B]
      ULift.{max u₂ u₃ v₄} P.toExtension.Cotangent :=
    ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  let U₀ : ULift.{v₄} P.toExtension.CotangentSpace ≃ₗ[B]
      ULift.{max u₂ u₃ v₄} P.toExtension.CotangentSpace :=
    ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  let e₁ : K.X 1 ≅ ModuleCat.of B
      (ULift.{max u₂ u₃ v₄} P.toExtension.Cotangent) :=
    ((ModuleCat.uliftFunctor.{v₄} B).mapIso
      (HomologicalComplex.doubleXIso₀
        (ModuleCat.ofHom P.toExtension.cotangentComplex) rfl)).trans
      U₁.toModuleIso
  let e₀ : K.X 0 ≅ ModuleCat.of B
      (ULift.{max u₂ u₃ v₄} P.toExtension.CotangentSpace) :=
    ((ModuleCat.uliftFunctor.{v₄} B).mapIso
      (HomologicalComplex.doubleXIso₁
        (ModuleCat.ofHom P.toExtension.cotangentComplex) rfl (by decide))).trans
      U₀.toModuleIso
  have hcomm : e₁.hom ≫ g = K.d 1 0 ≫ e₀.hom := by
    let f := ModuleCat.ofHom P.toExtension.cotangentComplex
    have hbase :
        (HomologicalComplex.doubleXIso₀ f rfl).hom ≫ f =
          (Algebra.naiveCotangentComplex A B).d 1 0 ≫
            (HomologicalComplex.doubleXIso₁ f rfl (by decide)).hom := by
      change (HomologicalComplex.doubleXIso₀ f rfl).hom ≫ f =
        (HomologicalComplex.double f rfl).d 1 0 ≫
          (HomologicalComplex.doubleXIso₁ f rfl (by decide)).hom
      rw [HomologicalComplex.double_d f rfl (by decide)]
      simp
    ext x
    simp only [e₁, e₀, g, K, U₁, U₀, NaiveCotangent.NL, ULift.moduleEquiv]
    exact congrArg (fun φ => (ModuleCat.Hom.hom φ) x.down) hbase
  let eK := doubleIsoOfSquare (K.d 1 0) g e₁ e₀ hcomm
  exact (extOneTargetIso eY).trans
    ((extOneSourceIso ((DerivedCategory.Q).mapIso eK)).trans cmp)

/-- **The Ext--cokernel comparison is `B`-linear.** This is `extCokernelIso` with its scalar
action recorded: the first Ext group of the two-term naive cotangent complex of `A → B` is the
cokernel of precomposition with the conormal differential as an equivalence of `B`-modules, not
merely of additive groups.

The categorical transports it is assembled from are `B`-linear because composition in a
`B`-linear category is `B`-bilinear, and the comparison they are composed with is
`NaiveCotangent.extOne_naiveCotangentComplex_linearEquiv_cokernel`. The scalar action on the
Ext group is the one induced by `CategoryTheory.Linear B (ModuleCat B)`.

A merely additive comparison can support no statement about scalars at all, and
finite-dimensionality over a field does not transport along one; the tangent-space clauses of
Stacks 0DY3, 0DY4 and 0ET4 need this linear form. -/
public noncomputable def extCokernelLinearIso
    (A : Type u₂) (B : Type u₃) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type v₄) [AddCommGroup N] [Module B N] :
    let P := Algebra.Generators.self A B
    let K := ((ModuleCat.uliftFunctor.{v₄} B).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex A B)
    DerivedCategory.Ext
      (DerivedCategory.Q.obj
        (HomologicalComplex.double (K.d 1 0)
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v₄} B) 0).obj
        ((ModuleCat.uliftFunctor.{max u₂ u₃} B).obj
          (ModuleCat.of B N))) 1 ≃ₗ[B]
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range
        (LinearMap.lcomp B N P.toExtension.cotangentComplex)) := by
  let P := Algebra.Generators.self A B
  let K := ((ModuleCat.uliftFunctor.{v₄} B).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex A B)
  let g := ModuleCat.ofHom
    (ULift.moduleEquiv.{u₃, max (max u₂ u₃) u₃, max u₂ u₃ v₄}.symm.toLinearMap.comp
      ((NaiveCotangent.NL P).d.comp
        ULift.moduleEquiv.{u₃, max u₂ u₃, max u₂ u₃ v₄}.toLinearMap))
  let e := HomologicalComplex.singleConeDoubleIso g
  let eN : ULift.{max u₂ u₃} N ≃ₗ[B]
      ULift.{max u₂ u₃ v₄} N :=
    ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  let eY := (DerivedCategory.singleFunctor
    (ModuleCat.{max u₂ u₃ v₄} B) 0).mapIso eN.toModuleIso
  let cmp := (extOneSourceLinearIso B ((DerivedCategory.Q).mapIso e)).trans
    (NaiveCotangent.extOne_naiveCotangentComplex_linearEquiv_cokernel
      (N := N) P)
  let U₁ : ULift.{v₄} P.toExtension.Cotangent ≃ₗ[B]
      ULift.{max u₂ u₃ v₄} P.toExtension.Cotangent :=
    ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  let U₀ : ULift.{v₄} P.toExtension.CotangentSpace ≃ₗ[B]
      ULift.{max u₂ u₃ v₄} P.toExtension.CotangentSpace :=
    ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  let e₁ : K.X 1 ≅ ModuleCat.of B
      (ULift.{max u₂ u₃ v₄} P.toExtension.Cotangent) :=
    ((ModuleCat.uliftFunctor.{v₄} B).mapIso
      (HomologicalComplex.doubleXIso₀
        (ModuleCat.ofHom P.toExtension.cotangentComplex) rfl)).trans
      U₁.toModuleIso
  let e₀ : K.X 0 ≅ ModuleCat.of B
      (ULift.{max u₂ u₃ v₄} P.toExtension.CotangentSpace) :=
    ((ModuleCat.uliftFunctor.{v₄} B).mapIso
      (HomologicalComplex.doubleXIso₁
        (ModuleCat.ofHom P.toExtension.cotangentComplex) rfl (by decide))).trans
      U₀.toModuleIso
  have hcomm : e₁.hom ≫ g = K.d 1 0 ≫ e₀.hom := by
    let f := ModuleCat.ofHom P.toExtension.cotangentComplex
    have hbase :
        (HomologicalComplex.doubleXIso₀ f rfl).hom ≫ f =
          (Algebra.naiveCotangentComplex A B).d 1 0 ≫
            (HomologicalComplex.doubleXIso₁ f rfl (by decide)).hom := by
      change (HomologicalComplex.doubleXIso₀ f rfl).hom ≫ f =
        (HomologicalComplex.double f rfl).d 1 0 ≫
          (HomologicalComplex.doubleXIso₁ f rfl (by decide)).hom
      rw [HomologicalComplex.double_d f rfl (by decide)]
      simp
    ext x
    simp only [e₁, e₀, g, K, U₁, U₀, NaiveCotangent.NL, ULift.moduleEquiv]
    exact congrArg (fun φ => (ModuleCat.Hom.hom φ) x.down) hbase
  let eK := doubleIsoOfSquare (K.d 1 0) g e₁ e₀ hcomm
  exact (extOneTargetLinearIso B eY).trans
    ((extOneSourceLinearIso B ((DerivedCategory.Q).mapIso eK)).trans cmp)

/-- The additive Ext--cokernel comparison is the underlying additive equivalence of the linear
one, so the two cannot drift apart. -/
public lemma extCokernelIso_eq
    (A : Type u₂) (B : Type u₃) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type v₄) [AddCommGroup N] [Module B N] :
    extCokernelIso A B N = (extCokernelLinearIso A B N).toAddEquiv := rfl

/-- The comparison of the first Ext group of the diagram with the conormal cokernel.
It depends only on `A₁`, `B₁` and `N₂`, not on the chosen solutions. -/
public noncomputable def obstructionExtCokernelIso
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := Algebra.Generators.self D.S₁.A D.S₁.B
    let K := ((ModuleCat.uliftFunctor.{v₄} D.S₁.B).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex D.S₁.A D.S₁.B)
    DerivedCategory.Ext
      (DerivedCategory.Q.obj
        (HomologicalComplex.double (K.d 1 0)
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v₄} D.S₁.B) 0).obj
        ((ModuleCat.uliftFunctor.{max u₂ u₃} D.S₁.B).obj
          (ModuleCat.of D.S₁.B D.S₂.N))) 1 ≃+
      ((P.toExtension.Cotangent →ₗ[D.S₁.B] D.S₂.N) ⧸ LinearMap.range
        (LinearMap.lcomp D.S₁.B D.S₂.N P.toExtension.cotangentComplex)) :=
  extCokernelIso D.S₁.A D.S₁.B D.S₂.N

end Stacks.Deformation
end
