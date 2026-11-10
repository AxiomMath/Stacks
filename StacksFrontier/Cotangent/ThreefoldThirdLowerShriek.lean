module

public import StacksFrontier.Cotangent.ThreefoldTowerFibreAcyclic
public import StacksFrontier.Cotangent.ThreefoldFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfCellularInverseImage

/-!
# Tag 08QW, the case `i = 3`: `Lg_{3,!} ∘ g₃⁻¹ = id`

Let `A → B → C` be ring maps, `u₃ : C_{C/B/A} ⥤ C_{C/B}` the functor
`(P → B, Q → C) ↦ (Q ⊗_P B → C)` of Tag 08QT and `g₃` the induced morphism of topoi. This file
proves that inverse image along `g₃` followed by derived lower shriek is the identity of
`D(Ab(C_{C/B}))`, for every left derived functor of lower shriek and every derived functor of
inverse image, on the unbounded derived categories.

## Main results

* `Stacks.ChaoticSite.lanCompEvaluationIsoColim`: the evaluation of a left Kan extension is the
  colimit over the costructured arrows, naturally, with no smallness hypothesis.
* `Stacks.ChaoticSite.acyclic_of_forall_evaluation`: a complex of sheaves for the chaotic topology
  is acyclic when its evaluations are.
* `CommAlgCat.lowerShriekThirdEvaluationIso`: lower shriek along `u₃`, evaluated at `(Q̄ → C)`, is
  the colimit over the fibre of `u₃`.
* `CommAlgCat.acyclic_lowerShriekThird`: lower shriek along `u₃` carries a bounded above acyclic
  complex of sheaves acyclic on the fibres to an acyclic complex.
* `CommAlgCat.fullyFaithfulThirdInverseImage`: `g₃⁻¹` is fully faithful on abelian sheaves.
* `CommAlgCat.derivedLowerShriekThirdInverseImageIso`: **Tag 08QW for `i = 3`.**

## Implementation notes

The source computes `L_n g_{3,!}` fibre by fibre by Cohomology on Sites, Lemma 08PK, and then
appeals to Tag 08QV on each fibre. Lemma 08PK is not used here: the fibrewise computation enters
only through the class `CommAlgCat.IsFibreAcyclicSheaf` of abelian sheaves acyclic on the fibres,
which satisfies the hypotheses of Stacks 0794 for `g_{3,!}`, so that every left derived functor of
`g_{3,!}` is computed by it, and which contains the image of `g₃⁻¹`. The argument is then the
formal one of `Stacks.ChaoticSite.derivedCompositeOfCellularImage`.

## References

* [Stacks Project, Tag 08QW](https://stacks.math.columbia.edu/tag/08QW)
* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08PK](https://stacks.math.columbia.edu/tag/08PK)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChaoticSite

universe v₁ v₂ v₃ u₁ u₂ u₃

section LanEvaluation

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] (L : 𝒞 ⥤ 𝒟)
  (H : Type u₃) [Category.{v₃} H] [∀ X : 𝒟, HasColimitsOfShape (CostructuredArrow L X) H]

/-- A morphism of left Kan extensions compatible with the units is the morphism of colimits over
the costructured arrows. -/
lemma app_comp_leftKanExtensionObjIsoColimit {G₁ G₂ : 𝒞 ⥤ H} (φ : G₁ ⟶ G₂)
    (m : L.leftKanExtension G₁ ⟶ L.leftKanExtension G₂)
    (hm : ∀ Y, (L.leftKanExtensionUnit G₁).app Y ≫ m.app (L.obj Y) =
      φ.app Y ≫ (L.leftKanExtensionUnit G₂).app Y) (X : 𝒟) :
    m.app X ≫ (L.leftKanExtensionObjIsoColimit G₂ X).hom =
      (L.leftKanExtensionObjIsoColimit G₁ X).hom ≫
        colimMap (Functor.whiskerLeft (CostructuredArrow.proj L X) φ) := by
  rw [← Iso.inv_comp_eq]
  refine colimit.hom_ext fun T => ?_
  calc colimit.ι (CostructuredArrow.proj L X ⋙ G₁) T ≫
        (L.leftKanExtensionObjIsoColimit G₁ X).inv ≫ m.app X ≫
          (L.leftKanExtensionObjIsoColimit G₂ X).hom
      = (L.leftKanExtensionUnit G₁).app T.left ≫
          ((L.leftKanExtension G₁).map T.hom ≫ m.app X) ≫
            (L.leftKanExtensionObjIsoColimit G₂ X).hom := by
        rw [← Category.assoc, Functor.ι_leftKanExtensionObjIsoColimit_inv]
        simp only [Category.assoc]
    _ = ((L.leftKanExtensionUnit G₁).app T.left ≫ m.app (L.obj T.left)) ≫
          (L.leftKanExtension G₂).map T.hom ≫ (L.leftKanExtensionObjIsoColimit G₂ X).hom := by
        rw [m.naturality T.hom]
        simp only [Category.assoc]
    _ = φ.app T.left ≫ colimit.ι (CostructuredArrow.proj L X ⋙ G₂) T := by
        rw [hm, Category.assoc, Functor.ι_leftKanExtensionObjIsoColimit_hom]
    _ = _ := (ι_colimMap (Functor.whiskerLeft (CostructuredArrow.proj L X) φ) T).symm

/-- **The evaluation of a left Kan extension is the colimit over the costructured arrows**,
naturally in the functor extended. This is `CategoryTheory.Functor.lanEvaluationIsoColim` without
its smallness hypotheses. -/
def lanCompEvaluationIsoColim (X : 𝒟) :
    L.lan ⋙ (evaluation 𝒟 H).obj X ≅
      (Functor.whiskeringLeft _ _ H).obj (CostructuredArrow.proj L X) ⋙ colim :=
  NatIso.ofComponents (fun G => L.leftKanExtensionObjIsoColimit G X) (fun φ =>
    app_comp_leftKanExtensionObjIsoColimit L H φ (L.lan.map φ)
      (fun Y => (congr_app (L.lanUnit.naturality φ) Y).symm) X)

end LanEvaluation

section Evaluation

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒜 : Type u₂} [Category.{v₂} 𝒜] [Abelian 𝒜]
  [HasSheafify (⊥ : GrothendieckTopology 𝒞) 𝒜]

omit [HasSheafify (⊥ : GrothendieckTopology 𝒞) 𝒜] in
/-- A sheaf whose underlying presheaf is zero is zero. -/
lemma isZero_of_isZero_val {J : GrothendieckTopology 𝒞} (M : Sheaf J 𝒜) (h : IsZero M.obj) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact Sheaf.hom_ext (h.eq_of_src _ _)

/-- **A complex of sheaves for the chaotic topology is acyclic as soon as it is after evaluation
at every object.** -/
lemma acyclic_of_forall_evaluation (K : CochainComplex (Sheaf (⊥ : GrothendieckTopology 𝒞) 𝒜) ℤ)
    (h : ∀ x : 𝒞ᵒᵖ, (((sheafToPresheaf ⊥ 𝒜 ⋙ (evaluation 𝒞ᵒᵖ 𝒜).obj x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic) : K.Acyclic := fun i => by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine isZero_of_isZero_val _ (Functor.isZero _ fun x => ?_)
  exact ((h x i).isZero_homology).of_iso ((K.sc i).mapHomologyIso
    (sheafToPresheaf ⊥ 𝒜 ⋙ (evaluation 𝒞ᵒᵖ 𝒜).obj x)).symm

/-- For the chaotic topology, sheafification is the identity: every presheaf is a sheaf. -/
def presheafToSheafCompSheafToPresheafIsoBot :
    presheafToSheaf (⊥ : GrothendieckTopology 𝒞) 𝒜 ⋙ sheafToPresheaf ⊥ 𝒜 ≅ 𝟭 _ :=
  have : ∀ P : 𝒞ᵒᵖ ⥤ 𝒜,
      IsIso ((sheafificationAdjunction (⊥ : GrothendieckTopology 𝒞) 𝒜).unit.app P) :=
    fun P => by
      rw [sheafificationAdjunction_unit_app]
      exact isIso_toSheafify _ (Presheaf.isSheaf_bot P)
  have : IsIso (sheafificationAdjunction (⊥ : GrothendieckTopology 𝒞) 𝒜).unit :=
    NatIso.isIso_of_isIso_app _
  (asIso (sheafificationAdjunction (⊥ : GrothendieckTopology 𝒞) 𝒜).unit).symm

end Evaluation

end Stacks.ChaoticSite

namespace CommAlgCat

open Stacks.ChaoticSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

section Bot

variable [(polynomialTowerThird A B C).IsContinuous ⊥ ⊥]

variable (U : PolynomialAugmentation B (towerRelativeAlgebra B C))

/-- **Lower shriek along `u₃`, evaluated at `(Q̄ → C)`, is the colimit over the fibre**: the
left Kan extension along `u₃` evaluated there is the colimit over the costructured arrows of `u₃`
over `(Q̄ → C)`, which are the small model of the site of towers over `Q̄`. -/
def lowerShriekThirdEvaluationIso :
    (polynomialTowerThird A B C).sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥ ⋙
        sheafToPresheaf ⊥ AddCommGrpCat.{u + 1} ⋙
          (evaluation _ AddCommGrpCat.{u + 1}).obj (op (op U)) ≅
      sheafToPresheaf ⊥ AddCommGrpCat.{u + 1} ⋙ fibreRestriction A U ⋙ colim :=
  Functor.isoWhiskerRight (Functor.sheafPullbackConstruction.sheafPullbackIso
      (polynomialTowerThird A B C) AddCommGrpCat.{u + 1} ⊥ ⊥) _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1} ⋙
        (polynomialTowerThird A B C).op.lan)
      (Functor.isoWhiskerRight
        (presheafToSheafCompSheafToPresheafIsoBot (𝒜 := AddCommGrpCat.{u + 1}))
        ((evaluation _ AddCommGrpCat.{u + 1}).obj (op (op U))) ≪≫
        Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1})
      (lanCompEvaluationIsoColim (polynomialTowerThird A B C).op AddCommGrpCat.{u + 1}
        (op (op U)) ≪≫
        Functor.isoWhiskerLeft _ (Functor.Final.colimIso (fibreSiteToCostructured A U)).symm)

variable (A B C) in
/-- The class of abelian sheaves on `C_{C/B/A}` acyclic on the fibres of `u₃`. -/
abbrev IsFibreAcyclicSheaf :
    ObjectProperty (Sheaf (⊥ : GrothendieckTopology (polynomialTowerSite A B C))
      AddCommGrpCat.{u + 1}) :=
  fun M => IsFibreAcyclic A B C M.obj

open ZeroObject in
/-- The class of abelian sheaves acyclic on the fibres of `u₃` contains a zero object. -/
instance : (IsFibreAcyclicSheaf A B C).ContainsZero :=
  ⟨⟨0, isZero_zero _, isFibreAcyclic_of_isZero
    (Functor.map_isZero (sheafToPresheaf _ _) (isZero_zero _))⟩⟩

omit [(polynomialTowerThird A B C).IsContinuous ⊥ ⊥] in
/-- Acyclicity on the fibres is closed under finite direct sums of sheaves. -/
lemma isFibreAcyclicSheaf_biprod (M N : Sheaf (⊥ : GrothendieckTopology (polynomialTowerSite A B C))
      AddCommGrpCat.{u + 1})
    (hM : IsFibreAcyclicSheaf A B C M) (hN : IsFibreAcyclicSheaf A B C N) :
    IsFibreAcyclicSheaf A B C (M ⊞ N) := fun U n => by
  let T := sheafToPresheaf ⊥ AddCommGrpCat.{u + 1} ⋙ fibreHomologyFunctor A U (n + 1)
  have hG : IsZero (T.obj M) := hM U n
  have hG' : IsZero (T.obj N) := hN U n
  change IsZero (T.obj (M ⊞ N))
  rw [IsZero.iff_id_eq_zero, ← T.map_id, ← biprod.total, T.map_add, T.map_comp, T.map_comp,
    hG.eq_of_tgt (T.map biprod.fst) 0, hG'.eq_of_tgt (T.map biprod.snd) 0, zero_comp, zero_comp,
    add_zero]

omit [(polynomialTowerThird A B C).IsContinuous ⊥ ⊥] in
/-- Every abelian sheaf on `C_{C/B/A}` is a quotient of one acyclic on the fibres of `u₃`. -/
lemma exists_epi_isFibreAcyclicSheaf
    (M : Sheaf (⊥ : GrothendieckTopology (polynomialTowerSite A B C)) AddCommGrpCat.{u + 1}) :
    ∃ (M' : Sheaf (⊥ : GrothendieckTopology (polynomialTowerSite A B C)) AddCommGrpCat.{u + 1})
      (_ : IsFibreAcyclicSheaf A B C M') (p : M' ⟶ M), Epi p := by
  obtain ⟨G', hG', p, hp⟩ := exists_epi_isFibreAcyclic A B C M.obj
  refine ⟨⟨G', Presheaf.isSheaf_bot G'⟩, hG', ⟨p⟩, ?_⟩
  exact (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1}).epi_of_epi_map hp

open ZeroObject in
/-- **Stacks 0794's acyclicity hypothesis for lower shriek along `u₃`**: a bounded above acyclic
complex of abelian sheaves acyclic on the fibres of `u₃` has acyclic lower shriek, because its
evaluation at `(Q̄ → C)` is the colimit over the fibre. -/
lemma acyclic_lowerShriekThird (a : ℤ)
    (K : CochainComplex (Sheaf (⊥ : GrothendieckTopology (polynomialTowerSite A B C))
      AddCommGrpCat.{u + 1}) ℤ) (_ : K.IsStrictlyLE a)
    (hK : ∀ n, IsFibreAcyclicSheaf A B C (K.X n)) (hac : K.Acyclic) :
    ((((polynomialTowerThird A B C).sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic := by
  refine acyclic_of_forall_evaluation _ fun y => ?_
  let K' := ((sheafToPresheaf ⊥ AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  have hK'a : ∀ p, a < p → IsZero (K'.X p) := fun p hp =>
    Functor.map_isZero (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1}) (K.isZero_of_isStrictlyLE a p hp)
  have hK'ac : K'.Acyclic := by
    have h0 : QuasiIso (0 : K ⟶ 0) := quasiIso_of_acyclic_of_isZero _ hac (isZero_zero _)
    exact acyclic_of_quasiIso' (((sheafToPresheaf ⊥ AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (0 : K ⟶ 0)) (HomologicalComplex.acyclic_of_isZero _
      (Functor.map_isZero ((sheafToPresheaf ⊥ AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)) (isZero_zero (CochainComplex (Sheaf (⊥ : GrothendieckTopology
          (polynomialTowerSite A B C)) AddCommGrpCat.{u + 1}) ℤ))))
  have h := acyclic_colim_fibreRestriction y.unop.unop K' a hK'a hK hK'ac
  exact acyclic_of_quasiIso' ((NatIso.mapHomologicalComplex
    (lowerShriekThirdEvaluationIso (A := A) y.unop.unop) (ComplexShape.up ℤ)).app K).hom h

variable (A B C) in
/-- **`g₃⁻¹` is fully faithful**: restriction of abelian sheaves along `u₃` is restriction of
abelian presheaves, whose left adjoint, the left Kan extension, has an invertible counit
(`CommAlgCat.isIso_lanAdjunction_counit_app`). -/
def fullyFaithfulThirdInverseImage :
    ((polynomialTowerThird A B C).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} ⊥ ⊥).FullyFaithful :=
  have : ∀ M, IsIso (((polynomialTowerThird A B C).op.lanAdjunction
      AddCommGrpCat.{u + 1}).counit.app M) := fun M => isIso_lanAdjunction_counit_app A B C M
  have : IsIso ((polynomialTowerThird A B C).op.lanAdjunction AddCommGrpCat.{u + 1}).counit :=
    NatIso.isIso_of_isIso_app _
  let ff := ((polynomialTowerThird A B C).op.lanAdjunction
    AddCommGrpCat.{u + 1}).fullyFaithfulROfIsIsoCounit
  { preimage := fun {_ _} φ => ⟨ff.preimage φ.hom⟩
    map_preimage := fun φ => Sheaf.hom_ext (ff.map_preimage φ.hom)
    preimage_map := fun f => Sheaf.hom_ext (ff.preimage_map f.hom) }

end Bot


section Statement

variable (J : GrothendieckTopology (polynomialTowerSite A B C))
  (K : GrothendieckTopology (polynomialSite B (towerRelativeAlgebra B C)))

/-- **Tag 08QW, the case `i = 3`, for topologies equal to the chaotic ones.** -/
def derivedLowerShriekThirdInverseImageIsoOfEqBot (hJ : J = ⊥) (hK : K = ⊥)
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify K AddCommGrpCat.{u + 1}]
    [(polynomialTowerThird A B C).IsContinuous J K]
    (L : DerivedCategory (Sheaf J AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((polynomialTowerThird A B C).sheafPullback AddCommGrpCat.{u + 1} J K).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))]
    (G : DerivedCategory (Sheaf K AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        J K).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ := by
  subst hJ
  subst hK
  let ff := fullyFaithfulThirdInverseImage A B C
  have : ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    ⊥ ⊥).Full := ff.full
  have : ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    ⊥ ⊥).Faithful := ff.faithful
  have := preservesFiniteLimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1}
    (polynomialTowerThird A B C)
  have := preservesFiniteColimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1}
    (polynomialTowerThird A B C)
  have : PreservesColimitsOfSize.{0, 0}
      ((polynomialTowerThird A B C).sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥) :=
    ((polynomialTowerThird A B C).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      ⊥ ⊥).leftAdjoint_preservesColimits
  have : HasExactColimitsOfShape ℕ (Sheaf (⊥ : GrothendieckTopology (polynomialTowerSite A B C))
      AddCommGrpCat.{u + 1}) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1})
  have : HasExactColimitsOfShape ℕ (Sheaf (⊥ : GrothendieckTopology
      (polynomialSite B (towerRelativeAlgebra B C))) AddCommGrpCat.{u + 1}) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1})
  have : PreservesColimitsOfShape ℕ ((polynomialTowerThird A B C).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} ⊥ ⊥) := by
    have : PreservesColimitsOfShape ℕ
        ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1} ⊥ ⊥ ⋙
          sheafToPresheaf ⊥ AddCommGrpCat.{u + 1}) :=
      preservesColimitsOfShape_of_natIso
        ((polynomialTowerThird A B C).sheafPushforwardContinuousCompSheafToPresheafIso
          AddCommGrpCat.{u + 1} ⊥ ⊥).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf ⊥ _)
  exact derivedCompositeOfCellularImage
    ((polynomialTowerThird A B C).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} ⊥ ⊥)
    (IsFibreAcyclicSheaf A B C) isFibreAcyclicSheaf_biprod exists_epi_isFibreAcyclicSheaf
    (fun a K hK hKP hac => acyclic_lowerShriekThird a K hK hKP hac)
    (fun N => isFibreAcyclic_inverseImage N.obj) L α G e

/-- **Tag 08QW, the case `i = 3`.** Inverse image along `g₃` followed by derived lower shriek is
the identity of `D(Ab(C_{C/B}))`. The statement is for an arbitrary left derived functor `L` of
lower shriek along `u₃`, presented by `α`, and an arbitrary derived functor `G` of inverse image,
presented by `e`.

The source applies Cohomology on Sites, Lemma 08PK: at an object `(Q̄ → C)` of `C_{C/B}`, the
derived lower shriek of `g₃⁻¹ℱ` is computed by the homology of `g₃⁻¹ℱ` over the fibre
`C_{Q̄/B/A}` of `u₃`, which vanishes in positive degrees and is `ℱ(Q̄ → C)` in degree zero by
Tag 08QV. Here the same two facts are used in the form Stacks 0794 needs: the class of abelian
sheaves acyclic on the fibres of `u₃` (`CommAlgCat.IsFibreAcyclicSheaf`) computes `Lg_{3,!}`,
contains the image of `g₃⁻¹`, and on it the counit `g_{3,!} g₃⁻¹ ⟶ id` is invertible
(`CommAlgCat.isIso_lanAdjunction_counit_app`), so
`Stacks.ChaoticSite.derivedCompositeOfCellularImage` applies. -/
def derivedLowerShriekThirdInverseImageIso
    (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTopology B (towerRelativeAlgebra B C))
        AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((polynomialTowerThird A B C).sheafPullback AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology B (towerRelativeAlgebra B C))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (G : DerivedCategory (Sheaf (polynomialTopology B (towerRelativeAlgebra B C))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology B (towerRelativeAlgebra B C))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ :=
  derivedLowerShriekThirdInverseImageIsoOfEqBot _ _ (polynomialTowerTopology_eq_bot A B C)
    (polynomialTopology_eq_bot B (towerRelativeAlgebra B C)) L α G e

end Statement

end CommAlgCat

end
