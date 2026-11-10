module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionComparisonPlain
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiCoherentQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionQuasiCoherent
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeLeftOrthogonal
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ConstantBaseRing

/-!
# Derived pullback along a functor of chaotic sites preserves quasi-coherence

Let `u : C' ⥤ C` be a functor between categories viewed as sites with the chaotic topology, let
`g : (Sh(C'), O') → (Sh(C), O)` be the induced morphism of ringed topoi and `φ : g^*A → A'` a map
of sheaves of differential graded algebras. Tag 0GZC says that the derived pullback
`Lg^* : D(A, d) ⥤ D(A', d)` maps `QC(A, d)` into `QC(A', d)`.

The argument is the source's, carried out on a module `P` computing the object whose sections
are orthogonal on the left to the acyclic modules (a K-projective module). For such a `P` the
derived pullback is `g^*P` (`chaoticDerivedPullbackObjIso`), its sections over `U'` are
`P(u U') ⊗_{A(u U')} A'(U')` and again K-projective, and every derived tensor product in sight is
computed by the plain one. For a morphism `a' : V' → U'` of `C'ᵒᵖ` with image `a` under `u`, the
comparison map of `g^*P` along `a'` is then, up to the identification
`(P(uV') ⊗ A'(V')) ⊗_{A'(V')} A'(U') ≅ P(uV') ⊗_{A(uV')} A'(U') ≅
(P(uV') ⊗_{A(uV')} A(uU')) ⊗_{A(uU')} A'(U')`, the comparison map of `P` along `a` tensored with
`A'(U')`. That is the chain of equalities in the proof of Tag 0GZC; the quasi-isomorphism of the
comparison map of `P` is a homotopy equivalence between K-projective modules, so it survives the
tensor product.

## Implementation notes

The sites, their morphisms and the sheaves of rings live in one universe, the setting of the
derived pullback `SheafOfModules.DifferentialGradedModule.chaoticDerivedPullback`; the
`HasSheafCompose` instance arguments hold for the chaotic topology, on which every presheaf is a
sheaf, and are spelled out because instance search does not determine their universe. The
quasi-coherence of Definition 0GZ9 is `SheafOfModules.DifferentialGradedModule.Chaotic.QC`; the
proof passes through the equivalent condition `IsQC (sectionDatum A)` on the comparison maps of the
derived sections, which is invariant under isomorphism in `D(A, d)`.

## Main results

* `DifferentialGraded.Bimodule.quasiIso_plainTranspose_of_square`: the plain-module form of the
  computation, for a commutative square of differential graded algebras.
* `SheafOfModules.DifferentialGradedModule.isQCModule_pullbackFunctor`: the pullback of a
  K-projective module satisfying the quasi-coherence condition satisfies it.
* `SheafOfModules.DifferentialGradedModule.qc_iff_isQC_sectionDatum`: the full subcategory
  `QC(A, d)` of Definition 0GZ9 is cut out by the comparison maps of the section datum.
* `SheafOfModules.DifferentialGradedModule.qc_chaoticDerivedPullback`: **Tag 0GZC**, and
  `isQC_chaoticDerivedPullback` the same statement through the section datum.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.qcChaoticDerivedPullback`: the induced functor
  `QC(A, d) ⥤ QC(A', d)`.

## References

* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe m u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-! ### Base change of a plain transpose along a commutative square -/

section Square

variable {A₀ B₀ B₁ C : DifferentialGradedAlgebra.{u, u} R} (ψ : A₀.Hom B₀) (χ : B₀.Hom C)
  (ψ' : A₀.Hom B₁) (χ' : B₁.Hom C) (κ : A₀.Hom C)
  (h₁ : ∀ a, χ.toAlgebraHom (ψ.toAlgebraHom a) = κ.toAlgebraHom a)
  (h₂ : ∀ a, χ'.toAlgebraHom (ψ'.toAlgebraHom a) = κ.toAlgebraHom a)
  {X : DifferentialGradedModule.{u, u, u} A₀} {Y : DifferentialGradedModule.{u, u, u} B₀}
  (r : X ⟶ (restrictScalarsFunctor ψ).obj Y)
  (r' : (tensorCompFunctor (regular ψ')).obj X ⟶
    (restrictScalarsFunctor χ').obj ((tensorCompFunctor (regular χ)).obj Y))

include h₁ h₂ in
/-- The base change along `χ` of the transpose of `r` and the transpose of a map `r'` sending
`x ⊗ b` to `r(x) ⊗ χ'(b)` agree after the identifications of `X ⊗_{A₀} C` with
`(X ⊗_{A₀} B₀) ⊗_{B₀} C` and with `(X ⊗_{A₀} B₁) ⊗_{B₁} C`. -/
theorem compIso_hom_plainTranspose
    (hr' : ∀ (p : ℤ) (x : X.grading p) (b : B₁.A),
      r'.toFun ((tensorPure (regular ψ') X).toLinearMap (x : X.M) b) =
        (tensorPure (regular χ) Y).toLinearMap (r.toFun (x : X.M)) (χ'.toAlgebraHom b)) :
    (compIso ψ' χ' κ h₂ X).hom ≫ plainTranspose χ' r' =
      (compIso ψ χ κ h₁ X).hom ≫ (tensorCompFunctor (regular χ)).map (plainTranspose ψ r) := by
  refine tensorObj_hom_ext' (regular κ) X _ _ fun x c => ?_
  induction x using DirectSum.Decomposition.inductionOn X.grading with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | @homogeneous p x =>
    have hz := ((tensorDGFunctor (regular ψ')).pure X).map_grading p 0 x
      ⟨(1 : B₁.A), SetLike.one_mem_graded B₁.grading⟩
    have hl : (plainTranspose χ' r').toFun ((compIso ψ' χ' κ h₂ X).hom.toFun
        ((tensorPure (regular κ) X).toLinearMap (x : X.M) c)) =
        (tensorPure (regular χ) Y).toLinearMap (r.toFun (x : X.M)) c := by
      refine (congrArg (plainTranspose χ' r').toFun (compForward_pure ψ' χ' κ h₂ X p x c)).trans
        ((plainTranspose_pure χ' r' (p + 0) ⟨_, hz⟩ c).trans ?_)
      refine (congrArg (fun w => @HSMul.hSMul C.Aᵐᵒᵖ
        ((tensorCompFunctor (regular χ)).obj Y).M ((tensorCompFunctor (regular χ)).obj Y).M _
          (MulOpposite.op (show C.A from c)) w) (hr' p x 1)).trans ?_
      rw [map_one]
      exact (((tensorDGFunctor (regular χ)).pure Y).map_right _ _ _).symm.trans
        (congrArg _ (one_mul (show C.A from c)))
    have hr : ((tensorCompFunctor (regular χ)).map (plainTranspose ψ r)).toFun
        ((compIso ψ χ κ h₁ X).hom.toFun ((tensorPure (regular κ) X).toLinearMap (x : X.M) c)) =
        (tensorPure (regular χ) Y).toLinearMap (r.toFun (x : X.M)) c := by
      refine (congrArg _ (compForward_pure ψ χ κ h₁ X p x c)).trans
        ((tensorCompFunctor_map_pure' (regular χ) (plainTranspose ψ r)
          ((tensorPure (regular ψ) X).toLinearMap (x : X.M) (1 : B₀.A)) c).trans ?_)
      refine congrArg (fun w => (tensorPure (regular χ) Y).toLinearMap w c)
        ((plainTranspose_pure ψ r p x 1).trans ?_)
      rw [MulOpposite.op_one]
      exact one_smul _ (show Y.M from r.toFun (x : X.M))
    exact hl.trans hr.symm

include h₁ h₂ in
/-- **A commutative square of differential graded algebras carries a quasi-isomorphism of plain
transposes to a quasi-isomorphism**: if the transpose `X ⊗_{A₀} B₀ ⟶ Y` of `r` is a
quasi-isomorphism between modules orthogonal on the left to the acyclic modules, then the
transpose `(X ⊗_{A₀} B₁) ⊗_{B₁} C ⟶ Y ⊗_{B₀} C` of a map `x ⊗ b ↦ r(x) ⊗ χ'(b)` is a
quasi-isomorphism. -/
theorem quasiIso_plainTranspose_of_square
    (hr' : ∀ (p : ℤ) (x : X.grading p) (b : B₁.A),
      r'.toFun ((tensorPure (regular ψ') X).toLinearMap (x : X.M) b) =
        (tensorPure (regular χ) Y).toLinearMap (r.toFun (x : X.M)) (χ'.toAlgebraHom b))
    (hm : QuasiIso ((forgetToCochainComplex B₀).map (plainTranspose ψ r)))
    (hX : (acyclic' B₀).leftOrthogonal
      ((toHomotopyCategory B₀).obj ((tensorCompFunctor (regular ψ)).obj X)))
    (hY : (acyclic' B₀).leftOrthogonal ((toHomotopyCategory B₀).obj Y)) :
    QuasiIso ((forgetToCochainComplex C).map (plainTranspose χ' r')) := by
  have h3 := isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal (regular χ)
    ((toHomotopyCategory B₀).map (plainTranspose ψ r))
    ((quasiIsomorphisms_map_iff' _ _).2 hm) hX hY
  have h4 : IsIso (((tensorCompFunctor (regular χ) ⋙ toHomotopyCategory C) ⋙
      (quasiIsomorphisms' C).Q).map (plainTranspose ψ r)) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (tensorCompFunctor_quotient (regular χ))
      (quasiIsomorphisms' C).Q) _).2 h3
  have heq : plainTranspose χ' r' = (compIso ψ' χ' κ h₂ X).inv ≫ (compIso ψ χ κ h₁ X).hom ≫
      (tensorCompFunctor (regular χ)).map (plainTranspose ψ r) := by
    rw [← compIso_hom_plainTranspose ψ χ ψ' χ' κ h₁ h₂ r r' hr', Iso.inv_hom_id_assoc]
  have h5 : IsIso ((quasiIsomorphisms' C).Q.map ((toHomotopyCategory C).map
      (plainTranspose χ' r'))) := by
    rw [heq, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    have : IsIso ((quasiIsomorphisms' C).Q.map ((toHomotopyCategory C).map
        ((tensorCompFunctor (regular χ)).map (plainTranspose ψ r)))) := h4
    infer_instance
  exact (quasiIsomorphisms_map_iff' _ _).1 (quasiIsomorphisms'_of_isIso_Q_map _ _ h5)

end Square

end DifferentialGraded.Bimodule

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}}
  {F : C' ⥤ C}
  {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A')

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The plain comparison map of the pullback is the plain transpose of the restriction
homomorphism of its presheaf of section modules, read through the identification of the
sections. -/
theorem plainSectionComparison_pullbackFunctor (P : DifferentialGradedModule.{u, m, m} A)
    {U' V' : C'ᵒᵖ} (a : V' ⟶ U') :
    Chaotic.plainSectionComparison ((pullbackFunctor φ).obj P) a ≫
        ((pullbackSystem φ P).sectionsIso U').hom =
      (DifferentialGraded.Bimodule.tensorCompFunctor
          (DifferentialGraded.Bimodule.regular (A'.sectionRestriction a))).map
        ((pullbackSystem φ P).sectionsIso V').hom ≫
        DifferentialGraded.Bimodule.plainTranspose (A'.sectionRestriction a)
          (pullbackRestr φ P a) := by
  have h := (pullbackSystem φ P).sectionModuleRestriction_sectionsIso a
  let adj := DifferentialGraded.Bimodule.tensorRegularAdjRestrictScalars (A'.sectionRestriction a)
  change (adj.homEquiv _ _).symm (((pullbackFunctor φ).obj P).sectionModuleRestriction a) ≫ _ =
    _ ≫ (adj.homEquiv _ _).symm (pullbackRestr φ P a)
  exact (adj.homEquiv_naturality_right_symm _ _).symm.trans
    ((congrArg (adj.homEquiv _ _).symm h).trans (adj.homEquiv_naturality_left_symm _ _))

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The sections of the pullback of a K-projective module are K-projective**: they are
`P(u U') ⊗_{A(u U')} A'(U')`, and extension of scalars preserves K-projectivity. -/
theorem leftOrthogonal_sectionModule_pullbackFunctor (P : DifferentialGradedModule.{u, m, m} A)
    (U' : C'ᵒᵖ)
    (hP : (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra (F.op.obj U'))).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory _).obj
        (P.sectionModule (F.op.obj U')))) :
    (_root_.DifferentialGradedModule.acyclic' (A'.sectionAlgebra U')).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory _).obj
        (((pullbackFunctor φ).obj P).sectionModule U')) :=
  (_root_.DifferentialGradedModule.acyclic' (A'.sectionAlgebra U')).leftOrthogonal.prop_of_iso
    ((_root_.DifferentialGradedModule.toHomotopyCategory _).mapIso
      ((pullbackSystem φ P).sectionsIso U')).symm
    (DifferentialGraded.Bimodule.leftOrthogonal_tensorCompFunctor_obj (φ.sectionHom U') hP)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The pullback of a K-projective module satisfying the quasi-coherence condition satisfies
it.** Over a morphism `a' : V' ⟶ U'` of `C'ᵒᵖ` the comparison map of `g^*P` is, up to the
identifications of its source, the comparison map of `P` along `u a'` tensored with `A'(U')`. -/
theorem isQCModule_pullbackFunctor (P : DifferentialGradedModule.{u, m, m} A)
    (hP : ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory _).obj (P.sectionModule U)))
    (hQC : Chaotic.IsQCModule P) : Chaotic.IsQCModule ((pullbackFunctor φ).obj P) := by
  intro U' V' a
  rw [Chaotic.isIso_sectionComparison_iff_quasiIso _ a
    (leftOrthogonal_sectionModule_pullbackFunctor φ P V' (hP _))]
  have hm := (Chaotic.isIso_sectionComparison_iff_quasiIso P (F.op.map a) (hP _)).1
    (hQC (F.op.map a))
  have hsq := DifferentialGraded.Bimodule.quasiIso_plainTranspose_of_square
    (A.sectionRestriction (F.op.map a)) (φ.sectionHom U') (φ.sectionHom V')
    (A'.sectionRestriction a) ((φ.sectionHom U').comp (A.sectionRestriction (F.op.map a)))
    (fun _ => rfl) (fun b => (φ.sectionHom_sectionRestriction a b).symm)
    (P.sectionModuleRestriction (F.op.map a)) (pullbackRestr φ P a)
    (fun p x b => pullbackRestr_pure φ P a (x : (P.sectionModule (F.op.obj V')).M) b) hm
    (DifferentialGraded.Bimodule.leftOrthogonal_tensorCompFunctor_obj _ (hP _)) (hP _)
  have e : Arrow.mk (Chaotic.plainSectionComparison ((pullbackFunctor φ).obj P) a) ≅
      Arrow.mk (DifferentialGraded.Bimodule.plainTranspose (A'.sectionRestriction a)
        (pullbackRestr φ P a)) :=
    Arrow.isoMk ((DifferentialGraded.Bimodule.tensorCompFunctor
        (DifferentialGraded.Bimodule.regular (A'.sectionRestriction a))).mapIso
          ((pullbackSystem φ P).sectionsIso V'))
      ((pullbackSystem φ P).sectionsIso U')
      (plainSectionComparison_pullbackFunctor φ P a).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    ((_root_.DifferentialGradedModule.forgetToCochainComplex (A'.sectionAlgebra U')).mapArrow.mapIso
      e)).2 hsq

/-- The derived pullback maps the quasi-coherent objects for the section datum to quasi-coherent
objects; this is the form of Tag 0GZC through the derived sections functors of the section datum,
from which `qc_chaoticDerivedPullback` follows. -/
theorem isQC_chaoticDerivedPullback (K : derivedCategory.{u, m, m} A)
    (hK : IsQC (sectionDatum A) K) :
    IsQC (sectionDatum A') ((chaoticDerivedPullback φ).obj K) := by
  obtain ⟨M, rfl⟩ := exists_toDerivedCategory_obj_eq A K
  obtain ⟨P, f, hf, -, -, hs⟩ := exists_flat_quasiIso_sectionwise (A := A) M
  have : IsIso ((toDerivedCategory.{u, m, m} A).map ((HomotopyCategory.quotient A).map f)) :=
    (quasiIsomorphisms.{u, m, m} A).Q_inverts _ ((quasiIsomorphisms_quotient_map_iff f).2 hf)
  let e := asIso ((toDerivedCategory.{u, m, m} A).map ((HomotopyCategory.quotient A).map f))
  have hG : IsQC (sectionDatum A') ((toDerivedCategory.{u, m, m} A').obj
      ((HomotopyCategory.quotient A').obj ((pullbackFunctor φ).obj P))) :=
    (isQC_sectionDatum_iff _).2
      (isQCModule_pullbackFunctor φ P hs ((isQC_sectionDatum_iff P).1 (isQC_of_iso _ e.symm hK)))
  have hfin : IsQC (sectionDatum A') ((chaoticDerivedPullback φ).obj
      ((toDerivedCategory.{u, m, m} A).obj ((HomotopyCategory.quotient A).obj M))) :=
    isQC_of_iso _ ((chaoticDerivedPullbackObjIso φ hs).symm ≪≫
      (chaoticDerivedPullback φ).mapIso e) hG
  intro U V a
  exact hfin a

variable (A) in
/-- On a chaotic site the full subcategory `QC(A, d)` of Definition 0GZ9 is the one cut out by
the comparison maps of the section datum: a module computing an object satisfies the
quasi-coherence condition exactly when the object does. -/
theorem qc_iff_isQC_sectionDatum (X : derivedCategory.{u, m, m} A) :
    Chaotic.QC A X ↔ IsQC (sectionDatum A) X := by
  obtain ⟨M, rfl⟩ := exists_toDerivedCategory_obj_eq A X
  refine ⟨fun h => (isQC_sectionDatum_iff M).2 (h M rfl),
    fun h N hN => (isQC_sectionDatum_iff N).1 ?_⟩
  rwa [show (toDerivedCategory.{u, m, m} A).obj ((HomotopyCategory.quotient A).obj N) =
    (toDerivedCategory.{u, m, m} A).obj ((HomotopyCategory.quotient A).obj M) from hN]

/-- The derived pullback along a functor of chaotic sites preserves quasi-coherence, under the
instance that the forgetful functor from commutative rings to rings is compatible with sheaves
on the two chaotic sites. Tag 0GZC, with that instance discharged, is
`SheafOfModules.DifferentialGradedModule.qc_chaoticDerivedPullback_chaotic`. -/
theorem qc_chaoticDerivedPullback (K : derivedCategory.{u, m, m} A) :
    Chaotic.QC A K → Chaotic.QC A' ((chaoticDerivedPullback φ).obj K) := fun qc =>
  (qc_iff_isQC_sectionDatum A' _).2
    (isQC_chaoticDerivedPullback φ K ((qc_iff_isQC_sectionDatum A K).1 qc))

/-- The functor `QC(A, d) ⥤ QC(A', d)` induced by the derived pullback. -/
def qcChaoticDerivedPullback : QC (sectionDatum A) ⥤ QC (sectionDatum A') :=
  ObjectProperty.lift _ (QCι (sectionDatum A) ⋙ chaoticDerivedPullback φ)
    fun K => isQC_chaoticDerivedPullback φ K.obj K.property

/-! ### Tag 0GZC -/

section Tag

/-- On the chaotic site every presheaf is a sheaf, so the forgetful functor from commutative
rings to rings is compatible with sheaves. -/
theorem botHasSheafCompose_forget₂ (C : Type u) [Category.{u} C] :
    (⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  Stacks.PresheafOfModules.botHasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})

attribute [local instance] botHasSheafCompose_forget₂

/-- **Stacks 0GZC.** Let `u : C' ⥤ C` be a functor of categories with the chaotic topology,
`g : (Sh(C'), O') → (Sh(C), O)` the induced morphism of ringed topoi together with
`σ : g⁻¹O ⟶ O'`, and `φ : g^*A → A'` a map of sheaves of differential graded `O'`-algebras. Then
the derived pullback `Lg^* : D(A, d) ⥤ D(A', d)` maps `QC(A, d)` into `QC(A', d)`. -/
@[stacks 0GZC]
theorem qc_chaoticDerivedPullback_chaotic {C : Type u} [Category.{u} C] {C' : Type u}
    [Category.{u} C'] {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}} {F : C' ⥤ C}
    {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
    {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
    (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A') (K : derivedCategory.{u, m, m} A) :
    Chaotic.QC A K → Chaotic.QC A' ((chaoticDerivedPullback φ).obj K) :=
  qc_chaoticDerivedPullback φ K

end Tag

end SheafOfModules.DifferentialGradedModule

end
