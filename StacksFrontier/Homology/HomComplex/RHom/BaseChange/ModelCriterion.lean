module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.DerivedInternalHom
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexAdjunction
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexChangeOfRings
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.BaseChangeMap
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexAdjunction

/-!
# A model criterion for the derived-Hom base-change map

Localized tensor--Hom identities, the compatibility of the change-of-rings comparison with
uncurrying (`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry`), and the
reduction of the invertibility of the derived-Hom base-change map to a unit comparison and to the
model rings.
-/

open StacksDraft.DerivedHom.Construction (KInjectiveObjects Q_map_surjective_of_isKInjective
    postcomp_bijective postcomp_quasiIso_of_homotopyEquivalence precomp_bijective
    precomp_quasiIso_of_homotopyEquivalence)

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex CochainComplex.HomComplex StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChangeIso

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open scoped TensorProduct ChangeOfRings

open DiagonalModel

noncomputable section

open CategoryTheory.MonoidalCategory CochainComplex CochainComplex.HomComplex
universe u
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
open DiagonalModel
open _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model
variable {R : Type u} [CommRing R]
/-- Uncurrying detects localized equality when the Hom source is K-flat. -/
private lemma Q_map_eq_of_uncurry
    {P K I : CochainComplex (ModuleCat.{u} R) ℤ} (hK : K.KFlat) [I.IsKInjective]
    (a b : P ⟶ HomComplexR R K I)
    (h : DerivedCategory.Q.map (uncurry a) = DerivedCategory.Q.map (uncurry b)) :
    DerivedCategory.Q.map a = DerivedCategory.Q.map b := by
  apply (cancel_mono ((_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homIso K
    I).inv).1
  apply (_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv _ _ _).injective
  rw [homEquiv_map_uncurry P K I hK a, homEquiv_map_uncurry P K I hK b, h]

/-- Uncurrying the diagonal gives associativity followed by evaluation. -/
private lemma uncurry_tensor_theta
    {P Z I K J : CochainComplex (ModuleCat.{u} R) ℤ}
    (t : Z ⟶ HomComplexR R K I) (q : P ⊗ I ⟶ J) :
    uncurry ((P ◁ t) ≫ Stacks.HomComplex.TensorHomComparison.theta P I K ≫
      Stacks.HomComplex.TensorHomMap.postcomp R K (P ⊗ I) J q) =
      (α_ P Z K).hom ≫ (P ◁ uncurry t) ≫ q := by
  show Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv _ _ _ _ = _
  rw [chainTensorHomEquiv_naturality_left, chainTensorHomEquiv_naturality_right,
    transpose_theta]
  simp only [Category.assoc]
  rw [associator_naturality_middle_assoc]
  have ht := chainTensorHomEquiv_naturality_left t (𝟙 (HomComplexR R K I))
  simp only [Category.comp_id] at ht
  change uncurry t = t ▷ K ≫ Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv _ _ _ (𝟙 _) at ht
  rw [← whiskerLeft_comp_assoc, ← ht]

/-- A linear Hom comparison remains linear after a K-injective replacement of its target. -/
private lemma tensor_hom_action_localized
    {P B Z L I K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : K.KFlat) [I.IsKInjective]
    (s : Z ⟶ HomComplexR R K L) (aL : B ⊗ L ⟶ L) (aZ : B ⊗ Z ⟶ Z)
    (hs : (B ◁ s) ≫ Stacks.HomComplex.TensorHomComparison.theta B L K ≫
      Stacks.HomComplex.TensorHomMap.postcomp R K (B ⊗ L) L aL =
      aZ ≫ s)
    (p : P ⟶ B) (q : L ⟶ I) (q' : P ⊗ I ⟶ I)
    (hq : DerivedCategory.Q.map ((P ◁ q) ≫ q') =
      DerivedCategory.Q.map ((p ▷ L) ≫ aL ≫ q)) :
    DerivedCategory.Q.map ((P ◁ (s ≫ Stacks.HomComplex.TensorHomMap.postcomp R K L I q)) ≫
      Stacks.HomComplex.TensorHomComparison.theta P I K ≫ Stacks.HomComplex.TensorHomMap.postcomp R
        K (P ⊗ I) I q') =
    DerivedCategory.Q.map ((p ▷ Z) ≫ aZ ≫ s ≫ Stacks.HomComplex.TensorHomMap.postcomp R K L I q) :=
      by
  apply Q_map_eq_of_uncurry hK
  rw [uncurry_tensor_theta]
  have hs' := congrArg (fun t => uncurry t) hs
  rw [uncurry_tensor_theta] at hs'
  change _ = Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv _ _ _ (aZ ≫ s) at hs'
  rw [chainTensorHomEquiv_naturality_left] at hs'
  change (α_ B Z K).hom ≫ B ◁ uncurry s ≫ aL = (aZ ▷ K) ≫ uncurry s at hs'
  show DerivedCategory.Q.map ((α_ P Z K).hom ≫
      P ◁ Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv _ _ _
        (s ≫ Stacks.HomComplex.TensorHomMap.postcomp R K L I q) ≫ q') =
    DerivedCategory.Q.map (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv _ _ _
      ((p ▷ Z) ≫ aZ ≫ s ≫ Stacks.HomComplex.TensorHomMap.postcomp R K L I q))
  rw [chainTensorHomEquiv_naturality_right,
    chainTensorHomEquiv_naturality_left,
    chainTensorHomEquiv_naturality_left,
    chainTensorHomEquiv_naturality_right]
  show DerivedCategory.Q.map ((α_ P Z K).hom ≫ P ◁ (uncurry s ≫ q) ≫ q') =
    DerivedCategory.Q.map (((p ▷ Z) ▷ K) ≫ (aZ ▷ K) ≫ uncurry s ≫ q)
  calc
    _ = DerivedCategory.Q.map ((α_ P Z K).hom ≫ P ◁ uncurry s) ≫
        DerivedCategory.Q.map ((P ◁ q) ≫ q') := by
      simp only [whiskerLeft_comp, Category.assoc, CategoryTheory.Functor.map_comp]
    _ = DerivedCategory.Q.map ((α_ P Z K).hom ≫ P ◁ uncurry s) ≫
        DerivedCategory.Q.map ((p ▷ L) ≫ aL ≫ q) := by rw [hq]
    _ = _ := by
      rw [← DerivedCategory.Q.map_comp]
      apply congrArg DerivedCategory.Q.map
      simp only [Category.assoc]
      rw [whisker_exchange_assoc, ← associator_naturality_left_assoc, reassoc_of% hs']
end

noncomputable section

open CategoryTheory.MonoidalCategory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct ChangeOfRings
universe u
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
/-- Extending the scalar-adjunction comparison and evaluating gives the scalar counit. -/
private lemma homComplexScalarAdjunction_counit
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    let E := CochainComplex.extendScalarsLarge f
    let U := CochainComplex.restrictScalarsLarge f
    let adj := (ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)
    E.map (homComplexScalarAdjunction f K J) ≫
      homComplexBaseChange f K (U.obj J) ≫
        Stacks.HomComplex.TensorHomMap.postcomp A (E.obj K) (E.obj (U.obj J)) J (adj.counit.app J) =
      adj.counit.app (HomComplexR A (E.obj K) J) := by
  dsimp only
  ext n : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  show (((Stacks.HomComplex.TensorHomMap.postcomp A _ _ J
      (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)).counit.app J)).f n
        ((homComplexBaseChange f K ((CochainComplex.restrictScalarsLarge f).obj J)).f n
          ((ModuleCat.extendScalars f).map ((homComplexScalarAdjunction f K J).f n)
            ((1 : A) ⊗ₜ[R,f] z)))).v p q hpq) ((1 : A) ⊗ₜ[R,f] x) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  show ((((homComplexBaseChange f K ((CochainComplex.restrictScalarsLarge f).obj J)).f n
      ((1 : A) ⊗ₜ[R,f] ((homComplexScalarAdjunction f K J).f n z))).comp
        (Cochain.ofHom (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up
          ℤ)).counit.app J))
          (add_zero n)).v p q hpq) ((1 : A) ⊗ₜ[R,f] x) = _
  rw [Cochain.comp_zero_cochain_v, ModuleCat.comp_apply, homComplexBaseChange_f_tmul_v,
    homComplexScalarAdjunction_f_apply]
  simp only [Cochain.ofHom_v, mul_one]
  show (ModuleCat.extendRestrictScalarsAdj f).counit.app (J.X q)
      ((1 : A) ⊗ₜ[R,f] (z.v p q hpq) ((1 : A) ⊗ₜ[R,f] x)) =
    (((ModuleCat.extendRestrictScalarsAdj f).counit.app
      ((HomComplexR A ((CochainComplex.extendScalarsLarge f).obj K) J).X n)
      ((1 : A) ⊗ₜ[R,f] z)).v p q hpq) ((1 : A) ⊗ₜ[R,f] x)
  erw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul (f := f) (J.X q)]

/-- The Hom-complex scalar adjunction intertwines the two scalar actions. -/
private lemma homComplexScalarAdjunction_linear
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    let E := CochainComplex.extendScalarsLarge f
    let U := CochainComplex.restrictScalarsLarge f
    let adj := (ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)
    let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
    let Z := HomComplexR A (E.obj K) J
    let c := homComplexScalarAdjunction f K J
    (B ◁ c) ≫ Stacks.HomComplex.TensorHomComparison.theta B (U.obj J) K ≫
      Stacks.HomComplex.TensorHomMap.postcomp R K (B ⊗ U.obj J) (U.obj J)
        ((extensionRestrictionComplexIso f).inv.app (U.obj J) ≫ U.map (adj.counit.app J)) =
    (extensionRestrictionComplexIso f).inv.app (U.obj Z) ≫ U.map (adj.counit.app Z) ≫ c := by
  dsimp only
  let E := CochainComplex.extendScalarsLarge f
  let U := CochainComplex.restrictScalarsLarge f
  let adj := (ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)
  let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  let Z := HomComplexR A (E.obj K) J
  let c := homComplexScalarAdjunction f K J
  have h := homComplexBaseChange_projection f K (U.obj J) (U.obj J) J
    (adj.counit.app J) (𝟙 _)
  have h' := congrArg (fun z => U.map (E.map c) ≫ z) h
  have hc := homComplexScalarAdjunction_counit f K J
  have hn := (extensionRestrictionComplexIso f).hom.naturality c
  dsimp only [Functor.comp_map] at hn
  simp only [Category.comp_id] at h'
  change U.map (E.map c) ≫ U.map
      (homComplexBaseChange f K (U.obj J) ≫
        Stacks.HomComplex.TensorHomMap.postcomp A (E.obj K) (E.obj (U.obj J)) J (adj.counit.app J))
          ≫ c = _ at h'
  rw [← U.map_comp_assoc, hc, reassoc_of% hn] at h'
  apply (cancel_epi ((extensionRestrictionComplexIso f).hom.app (U.obj Z))).1
  rw [Iso.hom_inv_id_app_assoc]
  exact h'.symm

private lemma homComplexChangeOfRingsMap_postcomp
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I)
      :
    Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q =
      homComplexScalarAdjunction f K J ≫
        Stacks.HomComplex.TensorHomMap.postcomp R K ((CochainComplex.restrictScalarsLarge f).obj J)
          I q := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p r hpr
  show ((Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q).f n z).v p r hpr =
    ((((homComplexScalarAdjunction f K J).f n z).comp (Cochain.ofHom q) (add_zero n)).v p r hpr)
  rw [Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap_f_apply, Cochain.comp_zero_cochain_v,
    homComplexScalarAdjunction_f_apply]
  rfl

/-- **The Hom-side change-of-rings map is the transpose of the tensor-side comparison.**

Let `f : R → A` be a homomorphism of commutative rings, `P` and `K` complexes of `R`-modules, `J`
a complex of `A`-modules and `q : J|_R ⟶ I` a map of complexes of `R`-modules.  Transposing a map
`s : P ⊗_R A ⟶ Hom^•_A(K ⊗_R A, J)` under the degreewise extension--restriction adjunction and
following it by the Hom-side change-of-rings map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` gives, after untransposing over `R`, the
same map of complexes as transposing the uncurrying of `s` after the tensor-side comparison
`Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso` and following that by `q`.

This is the chain-level comparison of the Hom-side change-of-rings map with the tensor side: the
whole content of the change-of-rings isomorphism of [stacks 0E1W] on representatives, with no
K-flatness or K-injectivity assumed of any of `P`, `K`, `J` or `I`.  The equation is an equality of
maps `P ⊗_R K ⟶ I`; both sides are transposes, so it determines each of the two comparisons from
the other. -/
theorem homComplexChangeOfRingsMap_uncurry
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I)
    (s : (CochainComplex.extendScalarsLarge f).obj P ⟶
      HomComplexR A ((CochainComplex.extendScalarsLarge f).obj K) J) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv (P ⊗ K) J
          ((tensorExtendScalarsIso f K).hom.app P ≫
            StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry s) ≫ q =
      StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).homEquiv P
            (HomComplexR A ((CochainComplex.extendScalarsLarge f).obj K) J) s ≫
          Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) := by
  have hg := tensorExtendScalarsIso_homEquiv f P K J
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry s)
  simp only [chainTranspose] at hg
  rw [StacksDraft.DerivedHom.DerivedInternalHom.Model.Phi_postcomp_uncurry] at hg
  apply chainTranspose_injective
  simp only [chainTranspose]
  rw [Stacks.HomComplex.TensorHomMap.postcomp_comp,
    StacksDraft.DerivedHom.DerivedInternalHom.Model.Phi_postcomp_uncurry, ← Category.assoc, hg,
    homComplexChangeOfRingsMap_postcomp, Category.assoc]
  rfl

end

section ScalarAdjunctionComparison

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- Extension of scalars along `f` is a left adjoint, with right adjoint restriction of scalars. -/
local instance : (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isLeftAdjoint
/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u} f).isLeftAdjoint

/-- The extension--restriction adjunction may be chosen with its original unit formula. -/
private def scalarAdjunctionWithUnitComparison
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))] :
    {a : F ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory //
      ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
        a.unit.app (DerivedCategory.Q.obj K) ≫
            (ModuleCat.restrictScalars f).mapDerivedCategory.map (α.app K) =
          DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
            (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app
              ((CochainComplex.extendScalarsLarge f).obj K)} := by
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} f F α
  letI := a.isLeftAdjoint
  letI := a.isRightAdjoint
  exact Stacks.DerivedHom.BaseChange.derivedAdjunctionWithUnitComparison
    ((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
    α (ModuleCat.restrictScalars f).mapDerivedCategoryFactors

/-- Restricting a natural isomorphism of bifunctors to the slice over an object `c`. -/
private def sliceIso {C₁ C₂ D₀ D₁ D₂ X Y Z : Type*} [Category* C₁] [Category* C₂] [Category* D₀]
    [Category* D₁] [Category* D₂] [Category* X] [Category* Y] [Category* Z]
    (G : C₁ ⥤ C₂) (L : D₀ ⥤ D₁) (V : D₀ ⥤ D₂) (H₁ : C₁ × D₁ ⥤ X) (H₂ : C₂ × D₂ ⥤ Y)
    (W₁ : X ⥤ Z) (W₂ : Y ⥤ Z)
    (ε : Functor.prod (𝟭 C₁) L ⋙ H₁ ⋙ W₁ ≅ Functor.prod G V ⋙ H₂ ⋙ W₂) (c : C₁) :
    L ⋙ (Functor.curry.obj H₁).obj c ⋙ W₁ ≅ V ⋙ (Functor.curry.obj H₂).obj (G.obj c) ⋙ W₂ :=
  NatIso.ofComponents (fun d => ε.app (c, d)) fun g => by
    simpa using ε.hom.naturality (X := (c, _)) (Y := (c, _)) (𝟙 c, g)

/-- The base-change isomorphism criterion is unchanged by normalizing the scalar adjunction. -/
private lemma isIso_derivedHomBaseChange_iff_unitComparison
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (a : F ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory)
    (K M : DerivedCategory (ModuleCat.{u} R)) :
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u} f F α K M) ↔
      IsIso ((a.homEquiv _ _).symm
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} R).map
          (show (Opposite.op K, M) ⟶ (Opposite.op K, _) from
            (𝟙 (Opposite.op K), a.unit.app M)) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{u, u, u} f F α).hom.app
            (Opposite.op K, F.obj M))) := by
  let U := (ModuleCat.restrictScalars f).mapDerivedCategory
  let H := (Functor.curry.obj (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} R)).obj
    (Opposite.op K)
  let J := (Functor.curry.obj (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A)).obj
    (Opposite.op (F.obj K))
  let e : U ⋙ H ⟶ J ⋙ U :=
    (sliceIso F.op U (𝟭 _) (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} R)
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A) (𝟭 _) U
      (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{u, u, u} f F α)
      (Opposite.op K)).hom
  exact isIso_unitComparison_iff
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} f F α) a H J
      e M

end ScalarAdjunctionComparison

noncomputable section

open CategoryTheory.MonoidalCategory CochainComplex
universe u
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
/-- Extension of scalars along `f` is a left adjoint, with right adjoint restriction of scalars. -/
local instance : (ModuleCat.extendScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isLeftAdjoint
/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u} f).isLeftAdjoint
variable (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
/-- The restricted derived counit is the ordinary scalar action on a K-flat resolution. -/
private lemma extensionRestrictionResolutionIso_action
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (p : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) [QuasiIso p]
    (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    let U := (ModuleCat.restrictScalars f).mapDerivedCategory
    let Uc := CochainComplex.restrictScalarsLarge f
    let β := (ModuleCat.restrictScalars f).mapDerivedCategoryFactors
    let a := (scalarAdjunctionWithUnitComparison f F α).1
    let adj := (ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)
    (extensionRestrictionResolutionIso f F α P hP p (Uc.obj J)).inv ≫
      U.map (F.map (β.inv.app J)) ≫ U.map (a.counit.app (DerivedCategory.Q.obj J)) ≫
        β.hom.app J =
      DerivedCategory.Q.map ((p ⊗ₘ 𝟙 (Uc.obj J)) ≫
        (extensionRestrictionComplexIso f).inv.app (Uc.obj J) ≫ Uc.map (adj.counit.app J)) := by
  dsimp only
  let U := (ModuleCat.restrictScalars f).mapDerivedCategory
  let Uc := CochainComplex.restrictScalarsLarge f
  let β := (ModuleCat.restrictScalars f).mapDerivedCategoryFactors
  let a := scalarAdjunctionWithUnitComparison f F α
  let adj := (ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)
  have hc := counit_fac_of_unit_fac adj α β a.1 a.2 J
  show (extensionRestrictionResolutionIso f F α P hP p (Uc.obj J)).inv ≫
      U.map (F.map (β.inv.app J)) ≫ U.map (a.1.counit.app (DerivedCategory.Q.obj J)) ≫
        β.hom.app J = _
  rw [← hc, Functor.map_comp, Functor.map_comp]
  simp only [← Category.assoc, ← U.map_comp, ← F.map_comp,
    Iso.inv_hom_id_app]
  have hb := β.hom.naturality (adj.counit.app J)
  dsimp only [Functor.comp_map] at hb
  simp only [Category.assoc, Functor.map_comp]
  erw [F.map_id, U.map_id, Category.id_comp, hb]
  have hp := extensionRestrictionResolutionIso_counit f F α P hP p (Uc.obj J)
  have hp' : (extensionRestrictionResolutionIso f F α P hP p (Uc.obj J)).inv ≫
      U.map (α.app (Uc.obj J)) ≫ β.hom.app ((CochainComplex.extendScalarsLarge f).obj (Uc.obj J)) =
    DerivedCategory.Q.map (p ⊗ₘ 𝟙 (Uc.obj J)) ≫
      DerivedCategory.Q.map ((extensionRestrictionComplexIso f).inv.app (Uc.obj J)) := by
    apply (cancel_epi (extensionRestrictionResolutionIso f F α P hP p (Uc.obj J)).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [reassoc_of% hp]
    simp only [← DerivedCategory.Q.map_comp,
      Iso.hom_inv_id_app]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
  erw [reassoc_of% hp']
  rfl
end


noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
variable
  [(ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint]
  [(ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint]
  [(ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint]
variable (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (α : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R))
/-- Scalar equivalences transport the canonical base-change criterion to the model rings. -/
private lemma isIso_derivedHomBaseChange_iff_model :
    let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM} f
      F α
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA uM} R
    let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{max uR uA
      uM,max uR uA uM,max uR uA uM} f' T.B T.alphaB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR,
      uA, uM} f
    let _τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let _eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let _HA := _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR,uA,uM} f F α K M) ↔
      IsIso ((a'.homEquiv _ _).symm
        (HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K))) (a'.unit.app
          (E.functor.obj M))) ≫
          (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso f' T.B T.alphaB).hom.app
            (Opposite.op (E.functor.obj K), T.B.obj (E.functor.obj M)))) := by
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
    α
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA uM} R
  let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA uM} A
  let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
  let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
    (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
      (ULift.{max uR uA uM} A)) ℤ)
  let a' := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{max uR uA
    uM,max uR uA uM,max uR uA uM} f' T.B T.alphaB
  let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR,
    uA, uM} f
  let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
    Iso.compInverseIso (H := E.symm)
      ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
        (Functor.associator _ _ _).symm)
  let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
    (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
  let HR := _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
  let HA := _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
  let H := (Functor.curry.obj (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,max uR uA uM}
    R)).obj (Opposite.op K)
  let J := (Functor.curry.obj (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA,max uR uA uM}
    A)).obj (Opposite.op (F.obj K))
  let H' := (Functor.curry.obj HR).obj (Opposite.op (E.functor.obj K))
  let J' := (Functor.curry.obj HA).obj (Opposite.op (T.B.obj (E.functor.obj K)))
  let e : U ⋙ H ⟶ J ⋙ U :=
    (sliceIso F.op U (𝟭 _) (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,
      max uR uA uM} R) (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A)
      (𝟭 _) U (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR,uA,uM} f F α)
      (Opposite.op K)).hom
  let e' : V ⋙ H' ⟶ J' ⋙ V :=
    (sliceIso T.B.op V (𝟭 _) HR HA (𝟭 _) V
      (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso f' T.B T.alphaB)
      (Opposite.op (E.functor.obj K))).hom
  let lH : H ⋙ E.functor ≅ E.functor ⋙ H' :=
    sliceIso E.functor.op (𝟭 _) E.functor (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,
      max uR uA uM} R) HR E.functor (𝟭 _) (homLiftIso.{uR,max uR uA uM} (R := R)) (Opposite.op K)
  let lJ₀ : J ⋙ S.functor ≅ S.functor ⋙
      (Functor.curry.obj HA).obj (Opposite.op (S.functor.obj (F.obj K))) :=
    sliceIso S.functor.op (𝟭 _) S.functor (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA,
      max uR uA uM} A) HA S.functor (𝟭 _) (homLiftIso.{uA,max uR uA uM} (R := A))
      (Opposite.op (F.obj K))
  let lJ : J ⋙ S.functor ≅ S.functor ⋙ J' :=
    lJ₀ ≪≫ Functor.isoWhiskerLeft S.functor ((Functor.curry.obj HA).mapIso (eF.app K).op)
  have hφ := unitComparison_scalar_unit E S a a' δ
  have he : ∀ Y, E.functor.map (e.app Y) ≫ τ.hom.app (J.obj Y) ≫ V.map (lJ.hom.app Y) =
      lH.hom.app (U.obj Y) ≫ H'.map (τ.hom.app Y) ≫ e'.app (S.functor.obj Y) := by
    intro Y
    let i := HA.mapIso ((eF.app K).op.prod (Iso.refl (S.functor.obj Y)))
    let g := H'.map (τ.hom.app Y) ≫ e'.app (S.functor.obj Y) ≫ V.map i.inv
    calc
      _ = E.functor.map (E.inverse.map g ≫ δ.inv.app _) ≫
          τ.hom.app (S.inverse.obj _) ≫ V.map (S.counitIso.hom.app _) ≫ V.map i.hom := by
        dsimp only [e, sliceIso, NatIso.ofComponents_hom_app, Iso.app_hom]
        rw [Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app.{uR,uA,uM}]
        simp only [g, lJ, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
        rfl
      _ = E.counitIso.hom.app _ ≫ g ≫ V.map i.hom := by
        erw [reassoc_of% (scalarRestriction_map E S U V δ g)]
        rfl
      _ = _ := by
        dsimp only [g]
        simp only [Category.assoc, ← V.map_comp, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id]
        erw [Category.comp_id]
        rfl
  have h := unitComparison_transport a a' E.functor S.functor H J H' J' e e'
    τ.hom lH.hom lJ.hom eF.inv M hφ he
  let src := (a.homEquiv _ _).symm (H.map (a.unit.app M) ≫ e.app (F.obj M))
  let tgt := (a'.homEquiv _ _).symm
    (H'.map (a'.unit.app (E.functor.obj M)) ≫ e'.app (T.B.obj (E.functor.obj M)))
  show IsIso src ↔ IsIso tgt
  have hi := Iff.of_eq (congrArg (fun z => IsIso z) h)
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at hi
  exact (isIso_iff_of_reflects_iso src S.functor).symm.trans hi.symm
end

noncomputable section
universe u
open CategoryTheory.MonoidalCategory CochainComplex
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
open _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
/-- Extension of scalars along `f` is a left adjoint, with right adjoint restriction of scalars. -/
local instance : (ModuleCat.extendScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isLeftAdjoint
/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u} f).isLeftAdjoint
variable (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
private lemma projectionAction_resolution
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (p : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) [QuasiIso p]
    (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    let _U := (ModuleCat.restrictScalars f).mapDerivedCategory
    let Uc := CochainComplex.restrictScalarsLarge f
    let β := (ModuleCat.restrictScalars f).mapDerivedCategoryFactors
    let a := (scalarAdjunctionWithUnitComparison f F α).1
    let proj := derivedExtensionRestrictionIso f F α
    let G := (Functor.curry.obj (tensor R)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A)))
    let adj := (ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)
    (tensorLeftIso P (Uc.obj J) hP).inv ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj
        (Uc.obj J)))) ≫
      G.map (β.inv.app J) ≫ (projectionAction a proj).app (DerivedCategory.Q.obj J) ≫
        β.hom.app J =
      DerivedCategory.Q.map ((p ▷ Uc.obj J) ≫
        (extensionRestrictionComplexIso f).inv.app (Uc.obj J) ≫ Uc.map (adj.counit.app J)) := by
  dsimp only
  let proj := derivedExtensionRestrictionIso f F α
  let β := (ModuleCat.restrictScalars f).mapDerivedCategoryFactors
  have hn := proj.inv.naturality (β.inv.app J)
  dsimp only [Functor.comp_map] at hn
  let U := (ModuleCat.restrictScalars f).mapDerivedCategory
  let Uc := CochainComplex.restrictScalarsLarge f
  let a := (scalarAdjunctionWithUnitComparison f F α).1
  let pre := (tensorLeftIso P (Uc.obj J) hP).inv ≫
    (tensor R).map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj
      (Uc.obj J))))
  calc
    _ = pre ≫ proj.inv.app (DerivedCategory.Q.obj (Uc.obj J)) ≫
        U.map (F.map (β.inv.app J)) ≫ U.map (a.counit.app (DerivedCategory.Q.obj J)) ≫
          β.hom.app J := by
      have h := congrArg (fun z => pre ≫ z ≫ U.map (a.counit.app (DerivedCategory.Q.obj J)) ≫
        β.hom.app J) hn
      simp only [pre, U, Uc, β, a, proj, Category.assoc, projectionAction_app] at h ⊢
      exact h
    _ = _ := by
      have h := extensionRestrictionResolutionIso_action f F α P hP p J
      simpa only [pre, U, Uc, β, a, proj, extensionRestrictionResolutionIso, Iso.trans_inv,
        Functor.mapIso_inv,
        Iso.prod_inv, Iso.symm_inv, asIso_hom, Iso.refl_inv, Iso.app_inv, Category.assoc,
        MonoidalCategory.tensorHom_def, whiskerLeft_id, Category.comp_id] using h
end

end Stacks.DerivedHom.BaseChangeIso

end
