module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Deformation.SquareZero.Diagram
public import StacksFrontier.Homology.DoubleMappingCone
public import StacksFrontier.RingTheory.NaiveCotangent.ExtCokernel
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# Relation differences of a square-zero deformation diagram

Transport of first Ext groups along isomorphisms, uniqueness of fitting maps, chosen lifts and
the two polynomial evaluation maps of a compatible square-zero deformation diagram, and the
difference of these evaluations on the relation ideal of the polynomial presentation.
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

/-- A commuting square of isomorphisms gives an isomorphism of two-term complexes. -/
public def doubleIsoOfSquare {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    (h : e₀.hom ≫ g = f ≫ e₁.hom) :
    HomologicalComplex.double f (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) ≅
      HomologicalComplex.double g (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) := by
  apply HomologicalComplex.doubleIsoOfIsZero f rfl (by decide)
    (HomologicalComplex.double g rfl)
    (e₀.trans (HomologicalComplex.doubleXIso₀ g rfl).symm)
    (e₁.trans (HomologicalComplex.doubleXIso₁ g rfl (by decide)).symm)
  · rw [HomologicalComplex.double_d g rfl (by decide)]
    simp [Category.assoc, h]
  · intro j hj
    have hj' : j = 1 := by
      change 0 + 1 = j at hj
      omega
    subst j
    exact (HomologicalComplex.isZero_double_X g rfl 1 (by decide)
      (by decide)).eq_of_tgt _ _
  · intro j hj₀ hj₁
    exact HomologicalComplex.isZero_double_X g rfl j hj₀ hj₁

/-- Transport first Ext across an isomorphism of its source complexes. -/
public noncomputable def extOneSourceIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y Z : DerivedCategory C} (e : X ≅ Y) :
    DerivedCategory.Ext X Z 1 ≃+ DerivedCategory.Ext Y Z 1 where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.comp_add]

/-- Transport first Ext across an isomorphism of its target. -/
public noncomputable def extOneTargetIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y Z : DerivedCategory C} (e : Y ≅ Z) :
    DerivedCategory.Ext X Y 1 ≃+ DerivedCategory.Ext X Z 1 where
  toFun f := f ≫ (shiftFunctor (DerivedCategory C) 1).map e.hom
  invFun f := f ≫ (shiftFunctor (DerivedCategory C) 1).map e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.add_comp]

/-- Transport first Ext across an isomorphism of its source complexes, `R`-linearly.  This is
`extOneSourceIso` with its scalar action recorded: composition in an `R`-linear category is
`R`-bilinear, so precomposition with a fixed morphism is `R`-linear and not merely additive. -/
public noncomputable def extOneSourceLinearIso (R : Type*) [Ring R]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [CategoryTheory.Linear R C]
    {X Y Z : DerivedCategory C} (e : X ≅ Y) :
    DerivedCategory.Ext X Z 1 ≃ₗ[R] DerivedCategory.Ext Y Z 1 where
  __ := extOneSourceIso e
  map_smul' r f := CategoryTheory.Linear.comp_smul _ _ _ e.inv r f

/-- Transport first Ext across an isomorphism of its target, `R`-linearly.  This is
`extOneTargetIso` with its scalar action recorded. -/
public noncomputable def extOneTargetLinearIso (R : Type*) [Ring R]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [CategoryTheory.Linear R C]
    {X Y Z : DerivedCategory C} (e : Y ≅ Z) :
    DerivedCategory.Ext X Y 1 ≃ₗ[R] DerivedCategory.Ext X Z 1 where
  __ := extOneTargetIso e
  map_smul' r f := CategoryTheory.Linear.smul_comp _ _ _ r f _

/-- The additive transport along an isomorphism of source complexes is the underlying additive
equivalence of the linear one. -/
public lemma extOneSourceIso_eq (R : Type*) [Ring R]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [CategoryTheory.Linear R C]
    {X Y Z : DerivedCategory C} (e : X ≅ Y) :
    extOneSourceIso (Z := Z) e = (extOneSourceLinearIso R (Z := Z) e).toAddEquiv := rfl

/-- The additive transport along an isomorphism of target complexes is the underlying additive
equivalence of the linear one. -/
public lemma extOneTargetIso_eq (R : Type*) [Ring R]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [CategoryTheory.Linear R C]
    {X Y Z : DerivedCategory C} (e : Y ≅ Z) :
    extOneTargetIso (X := X) e = (extOneTargetLinearIso R (X := X) e).toAddEquiv := rfl

/-- A conormal functional represents zero in the cokernel precisely when it is obtained
by precomposing a functional on degree zero with the differential.  This is the elementary
quotient criterion used when comparing the obstruction with a fitting map. -/
public theorem conormal_class_eq_zero_iff
    {B X₁ X₀ N : Type*} [CommRing B]
    [AddCommGroup X₁] [Module B X₁] [AddCommGroup X₀] [Module B X₀]
    [AddCommGroup N] [Module B N]
    (d : X₁ →ₗ[B] X₀) (f : X₁ →ₗ[B] N) :
    (Submodule.Quotient.mk f :
      (X₁ →ₗ[B] N) ⧸ LinearMap.range
        ((LinearMap.llcomp B X₁ X₀ N).flip d)) = 0 ↔
      ∃ t : X₀ →ₗ[B] N, t ∘ₗ d = f := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range

/-- Two elements of the kernel of a square-zero quotient multiply to zero.  This is what
allows an evaluation on a presentation's relation ideal to descend to its conormal module. -/
public theorem squareZero_kernel_mul
    {R S : Type*} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : RingHom.ker π ^ 2 = ⊥) (x y : RingHom.ker π) :
    (x : R) * (y : R) = 0 := by
  have hxy : (x : R) * (y : R) ∈ RingHom.ker π ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul x.property y.property
  rw [hπ, Ideal.mem_bot] at hxy
  exact hxy

/-- The difference of two maps which agree modulo a square-zero ideal obeys the
Leibniz identity, with multiplication evaluated using either map. -/
public theorem ringHom_sub_mul_of_squareZero
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (π : S →+* T) (hπ : RingHom.ker π ^ 2 = ⊥)
    (f g : R →+* S) (hfg : π.comp f = π.comp g) (x y : R) :
    f (x * y) - g (x * y) =
      g x * (f y - g y) + g y * (f x - g x) := by
  have hmem (z : R) : f z - g z ∈ RingHom.ker π :=
    (RingHom.sub_mem_ker_iff _).mpr (DFunLike.congr_fun hfg z)
  rw [map_mul, map_mul]
  calc
    f x * f y - g x * g y =
        g x * (f y - g y) + g y * (f x - g x) +
          (f x - g x) * (f y - g y) := by ring
    _ = g x * (f y - g y) + g y * (f x - g x) := by
      rw [squareZero_kernel_mul π hπ ⟨_, hmem x⟩ ⟨_, hmem y⟩, add_zero]

/-- Two fitting maps agree on the kernel specified by the deformation diagram. -/
private theorem fittingMap_eq_on_kernel_aux
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (F G : D.FittingMap) (x : RingHom.ker D.X₁.toB.toRingHom) :
    F.toRingHom (x : D.X₁.B') = G.toRingHom (x : D.X₁.B') := by
  obtain ⟨n, rfl⟩ := D.X₁.kernelEquiv.surjective x
  rw [F.kernel_comm, G.kernel_comm]

/-- A fitting map is determined by its values on one chosen lift of every element of `B₁`.
The values on the kernel are already prescribed by the diagram. -/
public theorem fittingMap_toRingHom_eq_of_lifts
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (F G : D.FittingMap) (s : D.S₁.B → D.X₁.B')
    (hs : ∀ b, D.X₁.toB (s b) = b)
    (heq : ∀ b, F.toRingHom (s b) = G.toRingHom (s b)) :
    F.toRingHom = G.toRingHom := by
  ext x
  have h := fittingMap_eq_on_kernel_aux D F G
    ⟨x - s (D.X₁.toB x), (RingHom.sub_mem_ker_iff _).mpr (hs _).symm⟩
  rw [map_sub, map_sub, heq] at h
  exact sub_left_injective h

/-- Uniqueness of the full fitting-map structure follows from equality of the ring maps. -/
public theorem fittingMap_ext
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (F G : D.FittingMap) (h : F.toRingHom = G.toRingHom) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Two fitting maps agree on the kernel specified by the deformation diagram. -/
public theorem fittingMap_eq_on_kernel
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (F G : D.FittingMap) (x : RingHom.ker D.X₁.toB.toRingHom) :
    F.toRingHom (x : D.X₁.B') = G.toRingHom (x : D.X₁.B') :=
  fittingMap_eq_on_kernel_aux D F G x

/-- The difference of two fitting maps depends only on the image in `B₁`. -/
public theorem fittingMap_difference_eq_of_toB_eq
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (F G : D.FittingMap) (x y : D.X₁.B')
    (hxy : D.X₁.toB x = D.X₁.toB y) :
    F.toRingHom x - G.toRingHom x = F.toRingHom y - G.toRingHom y := by
  have h := fittingMap_eq_on_kernel D F G ⟨x - y, (RingHom.sub_mem_ker_iff _).mpr hxy⟩
  change F.toRingHom (x - y) = G.toRingHom (x - y) at h
  rw [map_sub, map_sub] at h
  linear_combination h

/-- Chosen representatives of elements of `B₁` in the first extension. -/
public noncomputable def lift₁
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (b : D.S₁.B) : D.X₁.B' :=
  Classical.choose (D.X₁.surjective b)

/-- The chosen lift `lift₁ D b` reduces to `b` in `B₁`. -/
public theorem lift₁_spec
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (b : D.S₁.B) :
    D.X₁.toB (lift₁ D b) = b :=
  Classical.choose_spec (D.X₁.surjective b)

/-- Chosen representatives in the second extension of the images of elements of `B₁`. -/
public noncomputable def lift₂
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (b : D.S₁.B) : D.X₂.B' :=
  Classical.choose (D.X₂.surjective (algebraMap D.S₁.B D.S₂.B b))

/-- The chosen lift `lift₂ D b` reduces to the image of `b` in `B₂`. -/
public theorem lift₂_spec
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (b : D.S₁.B) :
    D.X₂.toB (lift₂ D b) = algebraMap D.S₁.B D.S₂.B b :=
  Classical.choose_spec (D.X₂.surjective (algebraMap D.S₁.B D.S₂.B b))

/-- Evaluation at the chosen lifts gives the first polynomial presentation map. -/
public noncomputable def presentationEval₁
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    MvPolynomial D.S₁.B D.S₁.A' →ₐ[D.S₁.A'] D.X₁.B' :=
  MvPolynomial.aeval (lift₁ D)

/-- Evaluation at the chosen lifts gives the second polynomial presentation map, using
the displayed map `A'₁ → A'₂` for coefficients. -/
public noncomputable def presentationEval₂
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    MvPolynomial D.S₁.B D.S₁.A' →+* D.X₂.B' := by
  let : Algebra D.S₁.A' D.X₂.B' :=
    ((algebraMap D.S₂.A' D.X₂.B').comp
      (algebraMap D.S₁.A' D.S₂.A')).toAlgebra
  exact (MvPolynomial.aeval (lift₂ D)).toRingHom

/-- The common reduction of the two polynomial evaluation maps to `B₁`. -/
public noncomputable def presentationToB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    MvPolynomial D.S₁.B D.S₁.A' →+* D.S₁.B :=
  (MvPolynomial.aeval (fun b : D.S₁.B ↦ b)).toRingHom

/-- Reduction of the polynomial presentation along `A'₁ → A₁`. -/
public noncomputable def coefficientReduction
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    MvPolynomial D.S₁.B D.S₁.A' →+* MvPolynomial D.S₁.B D.S₁.A :=
  MvPolynomial.map (algebraMap D.S₁.A' D.S₁.A)

/-- Evaluation of the reduced canonical polynomial presentation. -/
public noncomputable def reducedPresentationToB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    MvPolynomial D.S₁.B D.S₁.A →+* D.S₁.B :=
  (MvPolynomial.aeval (fun b : D.S₁.B ↦ b)).toRingHom

/-- The reduction of the polynomial presentation to `B₁` factors through the reduction of its
coefficients along `A'₁ → A₁`. -/
public theorem presentationToB_factor
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    (reducedPresentationToB D).comp (coefficientReduction D) =
      presentationToB D := by
  apply MvPolynomial.ringHom_ext'
  · ext a
    simpa [reducedPresentationToB, coefficientReduction, presentationToB] using
      (IsScalarTower.algebraMap_apply D.S₁.A' D.S₁.A D.S₁.B a).symm
  · intro b
    simp [reducedPresentationToB, coefficientReduction, presentationToB]

/-- Reducing coefficients along the surjection `A'₁ → A₁` is surjective on polynomials. -/
public theorem coefficientReduction_surjective
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    Function.Surjective (coefficientReduction D) :=
  MvPolynomial.map_surjective (algebraMap D.S₁.A' D.S₁.A) D.S₁.surjective

/-- The kernel of the coefficient reduction is generated by the constant polynomials with
coefficients in `I₁`. -/
public theorem coefficientReduction_ker
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    RingHom.ker (coefficientReduction D) =
      Ideal.map MvPolynomial.C D.S₁.I := by
  rw [coefficientReduction, MvPolynomial.ker_map, D.S₁.kernel_eq]

/-- A polynomial whose coefficients reduce to zero is a relation of the presentation of `B₁`. -/
public theorem coefficientReduction_ker_le_presentationToB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    RingHom.ker (coefficientReduction D) ≤ RingHom.ker (presentationToB D) := by
  intro p hp
  apply RingHom.mem_ker.mpr
  have h := DFunLike.congr_fun (presentationToB_factor D) p
  change (reducedPresentationToB D) (coefficientReduction D p) =
    presentationToB D p at h
  rw [← h, RingHom.mem_ker.mp hp, map_zero]

/-- Evaluating at the first chosen lifts and then reducing to `B₁` is the presentation map
`A'₁[B₁] → B₁`. -/
public theorem presentationEval₁_toB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    D.X₁.toB.toRingHom.comp (presentationEval₁ D).toRingHom = presentationToB D := by
  apply MvPolynomial.ringHom_ext'
  · ext a
    simp [presentationEval₁, presentationToB]
  · intro b
    simp [presentationEval₁, presentationToB, lift₁_spec]

/-- Evaluating at the second chosen lifts and then reducing to `B₂` is the presentation map
`A'₁[B₁] → B₁` followed by `B₁ → B₂`. -/
public theorem presentationEval₂_toB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    D.X₂.toB.toRingHom.comp (presentationEval₂ D) =
      (algebraMap D.S₁.B D.S₂.B).comp (presentationToB D) := by
  apply MvPolynomial.ringHom_ext'
  · ext a
    simp only [AlgHom.toRingHom_eq_coe, presentationEval₂, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, MvPolynomial.algHom_C, presentationToB]
    change D.X₂.toB ((algebraMap D.S₂.A' D.X₂.B')
      (algebraMap D.S₁.A' D.S₂.A' a)) =
        algebraMap D.S₁.B D.S₂.B (algebraMap D.S₁.A' D.S₁.B a)
    calc
      _ = algebraMap D.S₂.A' D.S₂.B (algebraMap D.S₁.A' D.S₂.A' a) :=
        D.X₂.toB.commutes _
      _ = algebraMap D.S₂.A D.S₂.B
          (algebraMap D.S₂.A' D.S₂.A (algebraMap D.S₁.A' D.S₂.A' a)) := by
            rw [IsScalarTower.algebraMap_apply D.S₂.A' D.S₂.A D.S₂.B]
      _ = algebraMap D.S₂.A D.S₂.B
          (algebraMap D.S₁.A D.S₂.A (algebraMap D.S₁.A' D.S₁.A a)) :=
            congrArg (algebraMap D.S₂.A D.S₂.B)
              (by simpa only [RingHom.coe_comp, Function.comp_apply] using
                DFunLike.congr_fun D.toA_comm a)
      _ = algebraMap D.S₁.B D.S₂.B
          (algebraMap D.S₁.A D.S₁.B (algebraMap D.S₁.A' D.S₁.A a)) := by
            simpa only [RingHom.coe_comp, Function.comp_apply] using
              DFunLike.congr_fun D.toB_comm (algebraMap D.S₁.A' D.S₁.A a)
      _ = _ := by rw [IsScalarTower.algebraMap_apply D.S₁.A' D.S₁.A D.S₁.B]
  · intro b
    simp [presentationEval₂, presentationToB, lift₂_spec]

/-- The first evaluation of a relation lies in the kernel of the first extension. -/
private theorem presentationEval₁_mem_ker
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    (presentationEval₁ D) x.1 ∈ RingHom.ker D.X₁.toB.toRingHom := by
  change D.X₁.toB.toRingHom ((presentationEval₁ D).toRingHom x.1) = 0
  rw [← RingHom.comp_apply, presentationEval₁_toB]
  exact x.2

/-- The second evaluation of a relation lies in the kernel of the second extension. -/
private theorem presentationEval₂_mem_ker
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    (presentationEval₂ D) x.1 ∈ RingHom.ker D.X₂.toB.toRingHom := by
  change D.X₂.toB.toRingHom ((presentationEval₂ D) x.1) = 0
  rw [← RingHom.comp_apply, presentationEval₂_toB]
  simp [RingHom.mem_ker.mp x.2]

/-- Evaluation of a relation in the first extension, viewed in its specified kernel. -/
public noncomputable def relationEval₁
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    RingHom.ker (presentationToB D) →+ D.S₁.N where
  toFun x := D.X₁.kernelEquiv.symm ⟨(presentationEval₁ D) x.1, by
    change D.X₁.toB.toRingHom ((presentationEval₁ D).toRingHom x.1) = 0
    rw [← RingHom.comp_apply, presentationEval₁_toB]
    exact x.2⟩
  map_zero' := by
    apply D.X₁.kernelEquiv.injective
    rw [D.X₁.kernelEquiv.apply_symm_apply, map_zero D.X₁.kernelEquiv]
    exact Subtype.ext (map_zero (presentationEval₁ D))
  map_add' x y := by
    apply D.X₁.kernelEquiv.injective
    rw [D.X₁.kernelEquiv.apply_symm_apply,
      map_add D.X₁.kernelEquiv, D.X₁.kernelEquiv.apply_symm_apply,
      D.X₁.kernelEquiv.apply_symm_apply]
    exact Subtype.ext (map_add (presentationEval₁ D) (x : MvPolynomial D.S₁.B D.S₁.A') y)

/-- Evaluation of a relation in the second extension, viewed in its specified kernel. -/
public noncomputable def relationEval₂
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    RingHom.ker (presentationToB D) →+ D.S₂.N where
  toFun x := D.X₂.kernelEquiv.symm ⟨(presentationEval₂ D) x.1, by
    change D.X₂.toB.toRingHom ((presentationEval₂ D) x.1) = 0
    rw [← RingHom.comp_apply, presentationEval₂_toB]
    simp [RingHom.mem_ker.mp x.2]⟩
  map_zero' := by
    apply D.X₂.kernelEquiv.injective
    rw [D.X₂.kernelEquiv.apply_symm_apply, map_zero D.X₂.kernelEquiv]
    exact Subtype.ext (map_zero (presentationEval₂ D))
  map_add' x y := by
    apply D.X₂.kernelEquiv.injective
    rw [D.X₂.kernelEquiv.apply_symm_apply,
      map_add D.X₂.kernelEquiv, D.X₂.kernelEquiv.apply_symm_apply,
      D.X₂.kernelEquiv.apply_symm_apply]
    exact Subtype.ext (map_add (presentationEval₂ D) (x : MvPolynomial D.S₁.B D.S₁.A') y)

/-- The relation functional before descending from `A'₁[B₁]` to `A₁[B₁]`. -/
public noncomputable def relationDifference
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    RingHom.ker (presentationToB D) →+ D.S₂.N :=
  relationEval₂ D - D.mapN.toAddMonoidHom.comp (relationEval₁ D)

/-- Viewed in the first extension, `relationEval₁ D x` is the evaluation of the relation `x`. -/
public theorem relationEval₁_spec
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    ((D.X₁.kernelEquiv (relationEval₁ D x) : RingHom.ker D.X₁.toB.toRingHom) :
      D.X₁.B') = (presentationEval₁ D) x.1 :=
  congrArg Subtype.val (D.X₁.kernelEquiv.apply_symm_apply ⟨_, presentationEval₁_mem_ker D x⟩)

/-- Viewed in the second extension, `relationEval₂ D x` is the evaluation of the relation `x`. -/
public theorem relationEval₂_spec
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    ((D.X₂.kernelEquiv (relationEval₂ D x) : RingHom.ker D.X₂.toB.toRingHom) :
      D.X₂.B') = (presentationEval₂ D) x.1 :=
  congrArg Subtype.val (D.X₂.kernelEquiv.apply_symm_apply ⟨_, presentationEval₂_mem_ker D x⟩)

/-- The identified kernel of a square-zero solution has trivial products. -/
private theorem kernelEquiv_mul_eq_zero {S : SquareZeroExtensionProblem}
    (X : S.CompatibleExtension) (m n : S.N) :
    (X.kernelEquiv m : X.B') * (X.kernelEquiv n : X.B') = 0 :=
  squareZero_kernel_mul X.toB.toRingHom X.sq_zero (X.kernelEquiv m) (X.kernelEquiv n)

/-- Scalar multiplication on the identified kernel is multiplication by any lift. -/
private theorem kernelEquiv_toB_smul {S : SquareZeroExtensionProblem}
    (X : S.CompatibleExtension) (b' : X.B') (n : S.N) :
    (X.kernelEquiv (X.toB b' • n) : X.B') = b' * (X.kernelEquiv n : X.B') := by
  rw [map_smul]
  exact congrArg Subtype.val (X.toB_smul_kernel b' (X.kernelEquiv n))

/-- Evaluation of two relations vanishes because the target kernel is square zero. -/
public theorem relationEval₁_mul_eq_zero
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x y : RingHom.ker (presentationToB D)) :
    relationEval₁ D (x * y) = 0 := by
  apply D.X₁.kernelEquiv.injective
  apply Subtype.ext
  rw [relationEval₁_spec, map_zero]
  change (presentationEval₁ D) (x.1 * y.1) = 0
  rw [map_mul, ← relationEval₁_spec D x, ← relationEval₁_spec D y]
  exact kernelEquiv_mul_eq_zero D.X₁ _ _

/-- Evaluation of a product of two relations in the second extension vanishes, because the
kernel there is square zero. -/
public theorem relationEval₂_mul_eq_zero
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x y : RingHom.ker (presentationToB D)) :
    relationEval₂ D (x * y) = 0 := by
  apply D.X₂.kernelEquiv.injective
  apply Subtype.ext
  rw [relationEval₂_spec, map_zero]
  change (presentationEval₂ D) (x.1 * y.1) = 0
  rw [map_mul, ← relationEval₂_spec D x, ← relationEval₂_spec D y]
  exact kernelEquiv_mul_eq_zero D.X₂ _ _

/-- The relation difference vanishes on a product of two relations. -/
public theorem relationDifference_mul_eq_zero
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x y : RingHom.ker (presentationToB D)) :
    relationDifference D (x * y) = 0 := by
  simp [relationDifference, relationEval₁_mul_eq_zero,
    relationEval₂_mul_eq_zero]

/-- Evaluation of relations in the first extension is linear over the polynomial ring, which
acts on `N₁` through `B₁`. -/
public theorem relationEval₁_mul
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A')
    (x : RingHom.ker (presentationToB D)) :
    relationEval₁ D ⟨p * x.1, by
      apply RingHom.mem_ker.mpr
      rw [map_mul, RingHom.mem_ker.mp x.2, mul_zero]⟩ =
      (presentationToB D p) • relationEval₁ D x := by
  apply D.X₁.kernelEquiv.injective
  apply Subtype.ext
  have hp : D.X₁.toB (presentationEval₁ D p) = presentationToB D p :=
    DFunLike.congr_fun (presentationEval₁_toB D) p
  rw [relationEval₁_spec, ← hp, kernelEquiv_toB_smul, relationEval₁_spec, map_mul]

/-- Evaluation of relations in the second extension is linear over the polynomial ring, which
acts on `N₂` through `B₁`. -/
public theorem relationEval₂_mul
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A')
    (x : RingHom.ker (presentationToB D)) :
    relationEval₂ D ⟨p * x.1, by
      apply RingHom.mem_ker.mpr
      rw [map_mul, RingHom.mem_ker.mp x.2, mul_zero]⟩ =
      (presentationToB D p) • relationEval₂ D x := by
  apply D.X₂.kernelEquiv.injective
  apply Subtype.ext
  have hp : D.X₂.toB (presentationEval₂ D p) = algebraMap D.S₁.B D.S₂.B (presentationToB D p) :=
    DFunLike.congr_fun (presentationEval₂_toB D) p
  rw [relationEval₂_spec, ← IsScalarTower.algebraMap_smul D.S₂.B (presentationToB D p),
    ← hp, kernelEquiv_toB_smul, relationEval₂_spec, map_mul]

/-- The relation difference is linear over the polynomial ring, which acts on `N₂` through
`B₁`. -/
public theorem relationDifference_mul
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A')
    (x : RingHom.ker (presentationToB D)) :
    relationDifference D ⟨p * x.1, by
      apply RingHom.mem_ker.mpr
      rw [map_mul, RingHom.mem_ker.mp x.2, mul_zero]⟩ =
      (presentationToB D p) • relationDifference D x := by
  simp [relationDifference, relationEval₁_mul, relationEval₂_mul,
    map_smul, smul_sub]

/-- The relation difference is linear over the presentation ring, acting on the target
through its quotient map to `B₁`. -/
public noncomputable def relationDifferenceLinear
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := MvPolynomial D.S₁.B D.S₁.A'
    letI : Module P D.S₂.N := Module.compHom D.S₂.N (presentationToB D)
    RingHom.ker (presentationToB D) →ₗ[P] D.S₂.N := by
  let : Module (MvPolynomial D.S₁.B D.S₁.A') D.S₂.N :=
    Module.compHom D.S₂.N (presentationToB D)
  exact { __ := relationDifference D, map_smul' := fun p x ↦ relationDifference_mul D p x }

/-- The relation difference factors through the square of the relation ideal. -/
public noncomputable def relationCotangentLinear
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := MvPolynomial D.S₁.B D.S₁.A'
    letI : Module P D.S₂.N := Module.compHom D.S₂.N (presentationToB D)
    (RingHom.ker (presentationToB D)).Cotangent →ₗ[P] D.S₂.N := by
  let : Module (MvPolynomial D.S₁.B D.S₁.A') D.S₂.N :=
    Module.compHom D.S₂.N (presentationToB D)
  exact Ideal.Cotangent.lift (relationDifferenceLinear D)
    (relationDifference_mul_eq_zero D)

/-- A coefficient in `I₁` is a relation in `A'₁[B₁]`. -/
public def coefficientRelation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (i : D.S₁.I) :
    RingHom.ker (presentationToB D) := ⟨MvPolynomial.C i, by
  have hi : (i : D.S₁.A') ∈ RingHom.ker (algebraMap D.S₁.A' D.S₁.A) := by
    rw [D.S₁.kernel_eq]
    exact i.2
  change (MvPolynomial.aeval (fun b : D.S₁.B ↦ b))
    (MvPolynomial.C (i : D.S₁.A')) = 0
  rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply D.S₁.A' D.S₁.A D.S₁.B,
    RingHom.mem_ker.mp hi, map_zero]⟩

/-- A coefficient `i ∈ I₁` evaluates in the first extension to its image `c₁ i` in `N₁`. -/
public theorem relationEval₁_coefficient
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (i : D.S₁.I) :
    relationEval₁ D (coefficientRelation D i) = D.S₁.c i := by
  apply D.X₁.kernelEquiv.injective
  apply Subtype.ext
  rw [relationEval₁_spec]
  simpa only [coefficientRelation, presentationEval₁, MvPolynomial.aeval_C] using
    (D.X₁.map_I i).symm

/-- A coefficient `i ∈ I₁` evaluates in the second extension to the image in `N₂` of its
image in `I₂`. -/
public theorem relationEval₂_coefficient
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (i : D.S₁.I) :
    relationEval₂ D (coefficientRelation D i) =
      D.S₂.c ⟨algebraMap D.S₁.A' D.S₂.A' i, D.map_I i⟩ := by
  apply D.X₂.kernelEquiv.injective
  apply Subtype.ext
  rw [relationEval₂_spec]
  have heval : (presentationEval₂ D) (MvPolynomial.C (i : D.S₁.A')) =
      (algebraMap D.S₂.A' D.X₂.B')
        (algebraMap D.S₁.A' D.S₂.A' i) := by
    simp only [presentationEval₂, MvPolynomial.aeval_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rfl
  rw [coefficientRelation, heval]
  exact (D.X₂.map_I ⟨algebraMap D.S₁.A' D.S₂.A' i, D.map_I i⟩).symm

/-- The relation difference vanishes on coefficients in `I₁`, since the diagram is compatible
with the maps `I → N`. -/
public theorem relationDifference_coefficient_eq_zero
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (i : D.S₁.I) :
    relationDifference D (coefficientRelation D i) = 0 := by
  simp [relationDifference, relationEval₁_coefficient, relationEval₂_coefficient,
    D.map_c]

/-- The relation difference vanishes on every relation whose coefficients reduce to zero in
`A₁`. -/
public theorem relationDifference_eq_zero_of_coefficientReduction
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A')
    (hp : p ∈ RingHom.ker (coefficientReduction D))
    (hJ : p ∈ RingHom.ker (presentationToB D)) :
    relationDifference D ⟨p, hJ⟩ = 0 := by
  have hmemJ (q : MvPolynomial D.S₁.B D.S₁.A')
      (hq : q ∈ Ideal.map MvPolynomial.C D.S₁.I) :
      q ∈ RingHom.ker (presentationToB D) :=
    coefficientReduction_ker_le_presentationToB D (by rwa [coefficientReduction_ker D])
  rw [coefficientReduction_ker D] at hp
  refine Submodule.span_induction (p := fun q _ ↦ ∀ hq : q ∈ RingHom.ker (presentationToB D),
    relationDifference D ⟨q, hq⟩ = 0) ?_ ?_ ?_ ?_ hp hJ
  · intro q hq hqJ
    obtain ⟨i, hi, rfl⟩ := hq
    exact relationDifference_coefficient_eq_zero D ⟨i, hi⟩
  · exact fun _ ↦ map_zero (relationDifference D)
  · intro x y hx hy ihx ihy hxyJ
    have hxJ := hmemJ x hx
    have hyJ := hmemJ y hy
    have heq : (⟨x + y, hxyJ⟩ : RingHom.ker (presentationToB D)) =
        ⟨x, hxJ⟩ + ⟨y, hyJ⟩ := rfl
    rw [heq, map_add, ihx hxJ, ihy hyJ, add_zero]
  · intro a x hx ihx haxJ
    have hxJ := hmemJ x hx
    have heq : (⟨a • x, haxJ⟩ : RingHom.ker (presentationToB D)) =
        ⟨a * x, (RingHom.ker (presentationToB D)).mul_mem_left a hxJ⟩ := rfl
    rw [heq, relationDifference_mul D a ⟨x, hxJ⟩, ihx hxJ, smul_zero]

/-- Every relation in the reduced canonical presentation lifts to a relation in the
presentation over the square-zero thickening. -/
public theorem reducedRelation_has_lift
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (reducedPresentationToB D)) :
    ∃ y : RingHom.ker (presentationToB D), coefficientReduction D y.1 = x.1 := by
  obtain ⟨p, hp⟩ := coefficientReduction_surjective D x.1
  refine ⟨⟨p, ?_⟩, hp⟩
  rw [RingHom.mem_ker, ← presentationToB_factor D, RingHom.comp_apply, hp]
  exact RingHom.mem_ker.mp x.2

/-- The relation difference depends only on the reduced relation. -/
public theorem relationDifference_eq_of_reduction_eq
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x y : RingHom.ker (presentationToB D))
    (hxy : coefficientReduction D x.1 = coefficientReduction D y.1) :
    relationDifference D x = relationDifference D y := by
  have hz := relationDifference_eq_zero_of_coefficientReduction D (x.1 - y.1)
    ((RingHom.sub_mem_ker_iff _).mpr hxy) (sub_mem x.2 y.2)
  change relationDifference D (x - y) = 0 at hz
  simpa only [map_sub, sub_eq_zero] using hz

end Stacks.Deformation
end
