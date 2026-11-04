module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtensionAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionReflectsIso

/-!
# Quasi-isomorphisms and the extension from a subcategory of a chaotic site

Let `F : C' ⥤ C` be a functor of chaotic sites such that every category `U/F` is cofiltered and
let `(A, d)` be a sheaf of differential graded algebras on `C`. A presheaf of section modules `Z`
along `F` is *good* when every `Z(U')` is orthogonal on the left to the acyclic modules, and
*quasi-coherent* when every comparison map `Z(V') ⊗_{A(F V')} A(F U') ⟶ Z(U')` is a
quasi-isomorphism. For a good and quasi-coherent `Z` the transition maps of the diagrams defining
the extension `E(Z)` are quasi-isomorphisms, so `E(Z)(U)` is computed by any single term
`Z(U') ⊗_{A(F U')} A(U)`: this is the filtered-colimit step of the proof of Tag 0GZE. Dually,
for a presheaf of section modules `Y` on `C` whose comparison maps along the arrows into the image
of `F` are quasi-isomorphisms, the counit `E(Y|_{C'}) ⟶ Y` is a quasi-isomorphism.

## Main results

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.quasiIso_transition`: the transition
  maps of the diagram of a good quasi-coherent presheaf along `F` are quasi-isomorphisms.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.quasiIso_ι`: hence so are the
  coprojections into the extension.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.quasiIso_counitApp`: the counit is a
  quasi-isomorphism over every object, given the quasi-coherence of `Y` at the arrows into the
  image of `F`.

## References

* [Stacks Project, Lemma 24.34.1 (Tag 0GZE)](https://stacks.math.columbia.edu/tag/0GZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits
open DifferentialGradedModule (restrictScalarsFunctor restrictScalarsIdHom restrictScalarsIdInv
  forgetToCochainComplex acyclic' toHomotopyCategory)
open DifferentialGraded.Bimodule (tensorCompFunctor regular tensorPure plainTranspose
  tensorSquareMap unitHom)

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {B D : DifferentialGradedAlgebra.{u, u} R}

/-- **Extension of scalars carries a quasi-isomorphism between modules orthogonal on the left to
the acyclic modules to a quasi-isomorphism.** -/
theorem quasiIso_tensorCompFunctor_map_of_leftOrthogonal (ψ : B.Hom D)
    {X Y : DifferentialGradedModule.{u, u, u} B} (f : X ⟶ Y)
    (hf : QuasiIso ((forgetToCochainComplex B).map f))
    (hX : (acyclic' B).leftOrthogonal ((toHomotopyCategory B).obj X))
    (hY : (acyclic' B).leftOrthogonal ((toHomotopyCategory B).obj Y)) :
    QuasiIso ((forgetToCochainComplex D).map ((tensorCompFunctor (regular ψ)).map f)) := by
  have h3 := isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal (regular ψ)
    ((toHomotopyCategory B).map f) ((quasiIsomorphisms_map_iff' _ _).2 hf) hX hY
  have h4 : IsIso (((tensorCompFunctor (regular ψ) ⋙ toHomotopyCategory D) ⋙
      (quasiIsomorphisms' D).Q).map f) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (tensorCompFunctor_quotient (regular ψ))
      (quasiIsomorphisms' D).Q) _).2 h3
  exact (quasiIsomorphisms_map_iff' _ _).1 (quasiIsomorphisms'_of_isIso_Q_map _ _ h4)

/-- **The transition of a diagram of extensions of scalars, factored**: base change along a
square whose bottom edge is the identity is the identification
`X ⊗_B D ≅ (X ⊗_B B') ⊗_{B'} D` followed by the transpose of `r`, tensored with `D`. -/
theorem tensorSquareMap_eq_compIso {B' : DifferentialGradedAlgebra.{u, u} R} (θ : B.Hom B')
    (ψ : B.Hom D) (ψ' : B'.Hom D)
    (h : ∀ b, (DifferentialGradedAlgebra.Hom.id D).toAlgebraHom (ψ.toAlgebraHom b) =
      ψ'.toAlgebraHom (θ.toAlgebraHom b))
    {X : DifferentialGradedModule.{u, u, u} B} {X' : DifferentialGradedModule.{u, u, u} B'}
    (r : X ⟶ (restrictScalarsFunctor θ).obj X') :
    tensorSquareMap θ ψ ψ' (DifferentialGradedAlgebra.Hom.id D) h r ≫ restrictScalarsIdHom _ =
      (compIso θ ψ' ψ (fun b => (h b).symm) X).hom ≫
        (tensorCompFunctor (regular ψ')).map (plainTranspose θ r) := by
  refine DifferentialGradedModule.Hom.ext
    (tensorObj_linearMap_ext_homogeneous (regular ψ) X _ _ fun p x c => ?_)
  show (tensorSquareMap θ ψ ψ' _ h r).toFun ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c) =
    ((tensorCompFunctor (regular ψ')).map (plainTranspose θ r)).toFun
      ((compForward θ ψ' ψ (fun b => (h b).symm) X).toFun
        ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c))
  refine (tensorSquareMap_pure θ ψ ψ' _ h r p x c).trans ?_
  refine Eq.trans ?_ (congrArg ((tensorCompFunctor (regular ψ')).map (plainTranspose θ r)).toFun
    (compForward_pure θ ψ' ψ (fun b => (h b).symm) X p x c)).symm
  refine Eq.trans ?_ (tensorCompFunctor_map_pure' (regular ψ') (plainTranspose θ r) _ c).symm
  refine congrArg (fun w => (tensorPure (regular ψ') X').toLinearMap w c) ?_
  refine Eq.trans ?_ (plainTranspose_pure θ r p x 1).symm
  rw [MulOpposite.op_one]
  exact (one_smul _ (show X'.M from r.toFun (x : X.M))).symm

/-- **The transition of a diagram of extensions of scalars is a quasi-isomorphism** as soon as
the transpose of `r` is a quasi-isomorphism between modules orthogonal on the left to the acyclic
modules. -/
theorem quasiIso_tensorSquareMap {B' : DifferentialGradedAlgebra.{u, u} R} (θ : B.Hom B')
    (ψ : B.Hom D) (ψ' : B'.Hom D)
    (h : ∀ b, (DifferentialGradedAlgebra.Hom.id D).toAlgebraHom (ψ.toAlgebraHom b) =
      ψ'.toAlgebraHom (θ.toAlgebraHom b))
    {X : DifferentialGradedModule.{u, u, u} B} {X' : DifferentialGradedModule.{u, u, u} B'}
    (r : X ⟶ (restrictScalarsFunctor θ).obj X')
    (hr : QuasiIso ((forgetToCochainComplex B').map (plainTranspose θ r)))
    (hX : (acyclic' B).leftOrthogonal ((toHomotopyCategory B).obj X))
    (hX' : (acyclic' B').leftOrthogonal ((toHomotopyCategory B').obj X')) :
    QuasiIso ((forgetToCochainComplex D).map
      (tensorSquareMap θ ψ ψ' (DifferentialGradedAlgebra.Hom.id D) h r ≫
        restrictScalarsIdHom _)) := by
  rw [tensorSquareMap_eq_compIso, Functor.map_comp]
  have : QuasiIso ((forgetToCochainComplex D).map
      ((tensorCompFunctor (regular ψ')).map (plainTranspose θ r))) :=
    quasiIso_tensorCompFunctor_map_of_leftOrthogonal ψ' _ hr
      (leftOrthogonal_tensorCompFunctor_obj θ hX) hX'
  infer_instance

section Square

variable {B₁ B₂ C₁ C₂ : DifferentialGradedAlgebra.{u, u} R} (θ : B₁.Hom B₂) (ψ₁ : B₁.Hom C₁)
  (ψ₂ : B₂.Hom C₂) (χ : C₁.Hom C₂)
  (h : ∀ b, χ.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₂.toAlgebraHom (θ.toAlgebraHom b))
  {X₁ : DifferentialGradedModule.{u, u, u} B₁} {X₂ : DifferentialGradedModule.{u, u, u} B₂}
  {Y₁ : DifferentialGradedModule.{u, u, u} C₁} {Y₂ : DifferentialGradedModule.{u, u, u} C₂}
  (g : X₁ ⟶ (restrictScalarsFunctor θ).obj X₂) (k : Y₁ ⟶ (restrictScalarsFunctor χ).obj Y₂)
  (r₁ : X₁ ⟶ (restrictScalarsFunctor ψ₁).obj Y₁) (r₂ : X₂ ⟶ (restrictScalarsFunctor ψ₂).obj Y₂)

/-- The plain transposes of two maps compatible along a commutative square of differential
graded algebras are compatible. -/
theorem plainTranspose_comp_eq_tensorSquareMap
    (hr : ∀ x, k.toFun (r₁.toFun x) = r₂.toFun (g.toFun x)) :
    plainTranspose ψ₁ r₁ ≫ k =
      tensorSquareMap θ ψ₁ ψ₂ χ h g ≫ (restrictScalarsFunctor χ).map (plainTranspose ψ₂ r₂) := by
  refine DifferentialGradedModule.Hom.ext
    (tensorObj_linearMap_ext_homogeneous (regular ψ₁) X₁ _ _ fun p x c => ?_)
  show k.toFun ((plainTranspose ψ₁ r₁).toFun
      ((tensorPure (regular ψ₁) X₁).toLinearMap (x : X₁.M) c)) =
    (plainTranspose ψ₂ r₂).toFun ((tensorSquareMap θ ψ₁ ψ₂ χ h g).toFun
      ((tensorPure (regular ψ₁) X₁).toLinearMap (x : X₁.M) c))
  refine (congrArg k.toFun (plainTranspose_pure ψ₁ r₁ p x c)).trans ((k.map_smul _ c).trans ?_)
  refine Eq.trans ?_ (congrArg (plainTranspose ψ₂ r₂).toFun
    (tensorSquareMap_pure θ ψ₁ ψ₂ χ h g p x c)).symm
  refine Eq.trans ?_ (plainTranspose_pure ψ₂ r₂ p ⟨g.toFun x, g.map_grading p x x.2⟩
    (χ.toAlgebraHom c)).symm
  exact congrArg (fun z => @HSMul.hSMul C₂.Aᵐᵒᵖ Y₂.M Y₂.M _ (MulOpposite.op (χ.toAlgebraHom c)) z)
    (hr x)

include h in
/-- **Quasi-isomorphy of plain transposes is invariant along a commutative square of
isomorphisms of differential graded algebras**: for compatible maps `r₁` and `r₂` related by
bijections `g` and `k`, the transpose of `r₁` is a quasi-isomorphism exactly when the transpose
of `r₂` is. -/
theorem quasiIso_plainTranspose_iff_of_square (θ' : B₂.Hom B₁) (χ' : C₂.Hom C₁)
    (h' : ∀ b, χ'.toAlgebraHom (ψ₂.toAlgebraHom b) = ψ₁.toAlgebraHom (θ'.toAlgebraHom b))
    (g' : X₂ ⟶ (restrictScalarsFunctor θ').obj X₁) (hgg : ∀ x, g'.toFun (g.toFun x) = x)
    (hgg' : ∀ y, g.toFun (g'.toFun y) = y) (hχχ : ∀ c, χ'.toAlgebraHom (χ.toAlgebraHom c) = c)
    (hχχ' : ∀ c, χ.toAlgebraHom (χ'.toAlgebraHom c) = c) (hk : Function.Bijective k.toFun)
    (hr : ∀ x, k.toFun (r₁.toFun x) = r₂.toFun (g.toFun x)) :
    QuasiIso ((forgetToCochainComplex C₁).map (plainTranspose ψ₁ r₁)) ↔
      QuasiIso ((forgetToCochainComplex C₂).map (plainTranspose ψ₂ r₂)) := by
  have : IsIso k := isIso_of_bijective k hk
  have : IsIso (tensorSquareMap θ ψ₁ ψ₂ χ h g) := isIso_of_bijective _
    (bijective_tensorSquareMap θ ψ₁ ψ₂ χ h g θ' χ' h' g' hgg hgg' hχχ hχχ')
  have e := congrArg (forgetToCochainComplex C₁).map
    (plainTranspose_comp_eq_tensorSquareMap θ ψ₁ ψ₂ χ h g k r₁ r₂ hr)
  rw [Functor.map_comp, Functor.map_comp] at e
  rw [← quasiIso_iff_comp_right _ ((forgetToCochainComplex C₁).map k), e,
    quasiIso_iff_comp_left]
  rfl

end Square

end DifferentialGraded.Bimodule

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

namespace DifferentialGradedModule.ChaoticExtension

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] {F : C' ⥤ C}
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  [∀ U : C, IsCofiltered (StructuredArrow U F)]

namespace AlongSystem

/-- A presheaf of section modules along `F` is **good** when its modules are orthogonal on the
left to the acyclic modules. -/
def IsGood (Z : AlongSystem F A) : Prop :=
  ∀ U' : C'ᵒᵖ, (acyclic' (A.sectionAlgebra (F.op.obj U'))).leftOrthogonal
    ((toHomotopyCategory (A.sectionAlgebra (F.op.obj U'))).obj (Z.obj U'))

/-- A presheaf of section modules along `F` is **quasi-coherent** when its plain comparison maps
`Z(V') ⊗_{A(F V')} A(F U') ⟶ Z(U')` are quasi-isomorphisms. -/
def IsQC (Z : AlongSystem F A) : Prop :=
  ∀ ⦃U' V' : C'ᵒᵖ⦄ (a : V' ⟶ U'),
    QuasiIso ((forgetToCochainComplex (A.sectionAlgebra (F.op.obj U'))).map
      (plainTranspose (A.sectionRestriction (F.op.map a)) (Z.restr a)))

end AlongSystem

variable {Z : AlongSystem F A}

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- **The transition maps of the diagram of a good quasi-coherent presheaf along `F` are
quasi-isomorphisms.** -/
theorem quasiIso_transition (hgood : Z.IsGood) (hqc : Z.IsQC) {U : Cᵒᵖ}
    {b b' : StructuredArrow U.unop F} (g : b' ⟶ b) :
    QuasiIso ((forgetToCochainComplex (A.sectionAlgebra U)).map (transition Z g)) :=
  DifferentialGraded.Bimodule.quasiIso_tensorSquareMap _ _ _ _ _ (hqc g.right.op) (hgood _)
    (hgood _)

/-- **The coprojections into the extension of a good quasi-coherent presheaf along `F` are
quasi-isomorphisms**: the filtered colimit is attained at every term. -/
theorem quasiIso_ι (hgood : Z.IsGood) (hqc : Z.IsQC) {U : Cᵒᵖ}
    (b : StructuredArrow U.unop F) :
    QuasiIso ((forgetToCochainComplex (A.sectionAlgebra U)).map
      (_root_.DifferentialGradedModule.FilteredColimit.ι (diagram Z U) (Opposite.op b))) :=
  _root_.DifferentialGradedModule.FilteredColimit.quasiIso_ι _
    (fun _ _ g => quasiIso_transition hgood hqc g.unop) _

/-- **The counit is a quasi-isomorphism over every object**, when the plain comparison maps of `Y`
along the arrows into the image of `F` are quasi-isomorphisms. -/
theorem quasiIso_counitApp (Y : SectionSystem A)
    (hY : ∀ {U : Cᵒᵖ} (b : StructuredArrow U.unop F),
      QuasiIso ((forgetToCochainComplex (A.sectionAlgebra U)).map (counitLeg F Y b)))
    (U : Cᵒᵖ) :
    QuasiIso ((forgetToCochainComplex (A.sectionAlgebra U)).map (counitApp F Y U)) := by
  obtain ⟨b⟩ : Nonempty (StructuredArrow U.unop F) := IsCofiltered.nonempty
  let G := forgetToCochainComplex (A.sectionAlgebra U)
  have htr : ∀ ⦃i j : (StructuredArrow U.unop F)ᵒᵖ⦄ (g : i ⟶ j),
      QuasiIso (G.map ((diagram (restrictSystem F Y) U).map g)) := fun i j g => by
    show QuasiIso (G.map (transition (restrictSystem F Y) g.unop))
    have := hY j.unop
    refine (quasiIso_iff_comp_right _ (G.map (counitLeg F Y j.unop))).1 ?_
    rw [← G.map_comp, transition_counitLeg F Y g.unop]
    exact hY i.unop
  have hι := _root_.DifferentialGradedModule.FilteredColimit.quasiIso_ι _ htr (Opposite.op b)
  have hc : _root_.DifferentialGradedModule.FilteredColimit.ι (diagram (restrictSystem F Y) U)
      (Opposite.op b) ≫ counitApp F Y U = counitLeg F Y b :=
    _root_.DifferentialGradedModule.Hom.ext (DFunLike.ext _ _ fun z => counitApp_germ F Y b z)
  have e : G.map (_root_.DifferentialGradedModule.FilteredColimit.ι
      (diagram (restrictSystem F Y) U) (Opposite.op b)) ≫ G.map (counitApp F Y U) =
        G.map (counitLeg F Y b) := by
    rw [← hc]
    exact (G.map_comp _ _).symm
  have h3 : QuasiIso (G.map (_root_.DifferentialGradedModule.FilteredColimit.ι
      (diagram (restrictSystem F Y) U) (Opposite.op b)) ≫ G.map (counitApp F Y U)) := by
    rw [e]
    exact hY b
  exact (quasiIso_iff_comp_left (hφ := hι) _ (G.map (counitApp F Y U))).1 h3

end DifferentialGradedModule.ChaoticExtension

end SheafOfModules

end
