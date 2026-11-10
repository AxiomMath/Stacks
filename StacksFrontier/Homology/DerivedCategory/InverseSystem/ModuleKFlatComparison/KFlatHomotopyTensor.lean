module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleKFlatComparison.TensorModel

/-!
# Componentwise K-flat resolutions and the homotopy tensor product of module systems

The monoidal structure on compatible module systems, componentwise K-flat resolutions and
their left derivability structure, the evaluation comparison for total tensor complexes,
the signed symmetry of total tensor complexes, preservation of quasi-isomorphisms by tensoring
with K-flat systems, and the total tensor bifunctor on homotopy categories.
-/

open Stacks.HomologyColimit

/-! ### Construction of the derived tensor product -/

section Construction

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped ZeroObject

universe u t w u₁ u₂ v₁ v₂

namespace ModuleSystemKFlatComparison

private abbrev Modules (A : Functor ℕᵒᵖ CommRingCat.{u}) :=
  PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def liftedUnit (A : ℕᵒᵖ ⥤ CommRingCat.{u}) : Systems.{u, t} A where
  obj n := ModuleCat.of (A.obj n) (ULift.{t} (A.obj n))
  map {m n} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (A.map f).hom).obj
      (ModuleCat.of (A.obj n) (ULift.{t} (A.obj n))))
    { toFun := fun x => ULift.up ((A.map f).hom x.down)
      map_add' := by intros; apply ULift.ext; exact map_add _ _ _
      map_smul' := by intros; apply ULift.ext; exact map_mul _ _ _ }
  map_id n := by ext x; apply ULift.ext; change (A.map (𝟙 n)).hom x.down = x.down; simp
  map_comp f g := by ext x; apply ULift.ext; change (A.map (f ≫ g)).hom x.down = _; simp

private local instance systemsMonoidalStruct (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    MonoidalCategoryStruct (Systems.{u, t} A) where
  tensorObj := tensorSystem A
  tensorHom := tensorSystemMap A
  whiskerLeft M _ _ f := tensorSystemMap A (𝟙 M) f
  whiskerRight f M := tensorSystemMap A f (𝟙 M)
  tensorUnit := liftedUnit A
  associator M N K := PresheafOfModules.isoMk
    (fun n => (TensorProduct.assoc (A.obj n) (M.obj n) (N.obj n) (K.obj n)).toModuleIso)
    (by intros; apply ModuleCat.hom_ext; apply TensorProduct.ext_threefold; intros; rfl)
  leftUnitor M := PresheafOfModules.isoMk (fun n => λ_ (M.obj n)) (by
    intro m n f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact ((M.restrictₛₗ f).map_smulₛₗ x.down y).symm)
  rightUnitor M := PresheafOfModules.isoMk (fun n => ρ_ (M.obj n)) (by
    intro m n f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact ((M.restrictₛₗ f).map_smulₛₗ y.down x).symm)

private local instance systemsMonoidal (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    MonoidalCategory (Systems.{u, t} A) where
  tensorHom_def _ _ := by ext1; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intros; rfl
  id_tensorHom_id _ _ := by ext1; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intros; rfl
  tensorHom_comp_tensorHom _ _ _ _ := by ext1; apply tensorHom_comp_tensorHom
  whiskerLeft_id _ _ := by ext1; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intros; rfl
  id_whiskerRight _ _ := by ext1; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intros; rfl
  associator_naturality _ _ _ := by ext1; apply associator_naturality
  leftUnitor_naturality _ := by ext1; apply leftUnitor_naturality
  rightUnitor_naturality _ := by ext1; apply rightUnitor_naturality
  pentagon _ _ _ _ := by ext1; apply pentagon
  triangle _ _ := by ext1; apply triangle

private local instance liftedModuleSymmetric {R : Type u} [CommRing R] :
    SymmetricCategory (ModuleCat.{max u t} R) where
  braiding M N := (TensorProduct.comm R M N).toModuleIso
  braiding_naturality_right := by intros; ext : 1; apply TensorProduct.ext'; intros; rfl
  braiding_naturality_left := by intros; ext : 1; apply TensorProduct.ext'; intros; rfl
  hexagon_forward := by intros; ext : 1; apply TensorProduct.ext_threefold; intros; rfl
  hexagon_reverse := by intros; ext : 1; apply TensorProduct.ext_threefold'; intros; rfl
  symmetry := by intros; ext : 1; apply TensorProduct.ext'; intros; rfl

private local instance systemsSymmetric (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    SymmetricCategory (Systems.{u, t} A) where
  braiding M N := PresheafOfModules.isoMk
    (fun n => (TensorProduct.comm (A.obj n) (M.obj n) (N.obj n)).toModuleIso)
    (by intros; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intros; rfl)
  braiding_naturality_right _ _ _ _ := by ext1; apply BraidedCategory.braiding_naturality_right
  braiding_naturality_left _ _ := by ext1; apply BraidedCategory.braiding_naturality_left
  hexagon_forward _ _ _ := by ext1; apply BraidedCategory.hexagon_forward
  hexagon_reverse _ _ _ := by ext1; apply BraidedCategory.hexagon_reverse
  symmetry _ _ := by ext1; apply SymmetricCategory.symmetry

private local instance systemsMonoidalPreadditive (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    MonoidalPreadditive (Systems.{u, t} A) where
  whiskerLeft_zero := by
    intros
    ext1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intros
    exact TensorProduct.tmul_zero _ _
  zero_whiskerRight := by
    intros
    ext1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intros
    exact TensorProduct.zero_tmul _ _
  whiskerLeft_add := by
    intros
    ext1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intros
    exact TensorProduct.tmul_add _ _ _
  add_whiskerRight := by
    intros
    ext1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intros
    exact TensorProduct.add_tmul _ _ _

/-- The total tensor exists because systems have all small coproducts. -/
private local instance systemsHasTensor (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    ∀ K L : CochainComplex (Modules.{u, t} A) ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor (Modules.{u, t} A)) (.up ℤ) :=
  fun _ _ => inferInstance

private abbrev HasKFlatComponents (A : Functor ℕᵒᵖ CommRingCat.{u})
    (M : CochainComplex
      (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)) ℤ) : Prop :=
  ∀ n : ℕ,
    CochainComplex.KFlat
      (((PresheafOfModules.evaluation
        (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)

private theorem hasKFlatComponents_of_iso
    (A : Functor ℕᵒᵖ CommRingCat.{u})
    {M N : CochainComplex
      (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)) ℤ}
    (e : M ≅ N) (hM : HasKFlatComponents A M) : HasKFlatComponents A N := by
  intro n
  let E := (PresheafOfModules.evaluation
    (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
      (ComplexShape.up ℤ)
  intro X hX
  exact HomologicalComplex.Acyclic.of_iso
    (tensorIso (Iso.refl X) (E.mapIso e)) (hM n X hX)

private abbrev kFlatSystems (A : Functor ℕᵒᵖ CommRingCat.{u}) :
    ObjectProperty (CochainComplex (Modules.{u, t} A) ℤ) :=
  HasKFlatComponents A

/-- Quasi-isomorphisms of compatible complexes are quasi-isomorphisms at each index. -/
private theorem quasiIso_evaluation
    (A : Functor ℕᵒᵖ CommRingCat.{u})
    {M N : CochainComplex (Modules.{u, t} A) ℤ} (f : M ⟶ N) [QuasiIso f] (n : ℕ) :
    QuasiIso
      (((PresheafOfModules.evaluation
        (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) :=
  inferInstance

section SystemResolutions

/-- Module systems over `A` which are projective at every index. The module universe `max u t`
is independent of the ring universe `u`. -/
def pointwiseProjective (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    ObjectProperty (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)) :=
  fun M => ∀ n : ℕ, Projective (M.obj (op n))

/-- A biproduct of pointwise projective module systems is pointwise projective. -/
lemma projective_biprod (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    (M N : PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat))
    (hM : pointwiseProjective A M) (hN : pointwiseProjective A N) :
    pointwiseProjective A (M ⊞ N) := by
  intro n
  let E := PresheafOfModules.evaluation.{max u t} (A ⋙ forget₂ CommRingCat RingCat) (op n)
  let := preservesBinaryBiproducts_of_preservesBinaryProducts E
  have : Projective (E.obj M) := hM n
  have : Projective (E.obj N) := hN n
  exact Projective.of_iso (E.mapBiprod M N).symm inferInstance

/-- Free modules on the underlying sets give pointwise projective covers. -/
lemma free_cover (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    (M : PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)) :
    ∃ (P : PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat))
      (_ : pointwiseProjective A P) (f : P ⟶ M), Epi f := by
  let P : Modules.{u, t} A :=
    { obj := fun n => ModuleCat.of (A.obj n) (M.obj n →₀ A.obj n)
      map := fun {m n} f => ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars (A.map f).hom).obj
          (ModuleCat.of (A.obj n) (M.obj n →₀ A.obj n)))
        (Finsupp.linearCombination (A.obj m)
          (fun x => Finsupp.single (M.map f x) (1 : A.obj n)))
      map_id := by
        intro n
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext'
        intro x
        apply LinearMap.ext_ring
        simp [Finsupp.linearCombination]
        rfl
      map_comp := by
        intro m n k f g
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext'
        intro x
        apply LinearMap.ext_ring
        simp [Finsupp.linearCombination]
        rfl }
  let f : P ⟶ M :=
    { app := fun n => ModuleCat.ofHom (Finsupp.linearCombination (A.obj n) id)
      naturality := by
        intro m n g
        apply ModuleCat.hom_ext (R := A.obj m)
        apply Finsupp.lhom_ext'
        intro x
        apply LinearMap.ext_ring
        simp [P, Finsupp.linearCombination] }
  have hp : pointwiseProjective A P := by
    intro n
    change Projective (ModuleCat.of (A.obj (op n)) (M.obj (op n) →₀ A.obj (op n)))
    infer_instance
  have hf : Epi f := by
    apply PresheafOfModules.epi_of_surjective
    intro n x
    refine ⟨Finsupp.single x 1, ?_⟩
    change (Finsupp.linearCombination (A.obj n) (id : M.obj n → M.obj n)) _ = x
    simp only [Finsupp.linearCombination_single, one_smul, id_eq]
  exact ⟨P, hp, f, hf⟩

/-- The zero module system is pointwise projective. -/
lemma zero_prop (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    (pointwiseProjective.{u, t} A).ContainsZero :=
  ⟨0, isZero_zero _, fun n => ((PresheafOfModules.evaluation.{max u t}
    (A ⋙ forget₂ CommRingCat RingCat) (op n)).map_isZero (isZero_zero _)).projective⟩

section HomologyColimit

universe v

variable {A : Type v} [Category.{w} A] [Abelian A]

end HomologyColimit

private lemma exists_surjective_kFlat_system_resolution (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    (M : CochainComplex (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)) ℤ) :
    ∃ (K : CochainComplex (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)) ℤ)
      (f : K ⟶ M), QuasiIso f ∧ Epi f ∧ HasKFlatComponents A K := by
  let P := pointwiseProjective.{u, t} A
  let : P.ContainsZero := zero_prop A
  obtain ⟨Q, q, g, hq, hepi, hle, hproj, _, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P (projective_biprod A) (free_cover A) M
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk M
    (NatTrans.ofSequence (fun n => q n ≫ M.ιTruncLE (n : ℤ)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ M := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ M.ιTruncLE (n : ℤ) := fun n => hc.fac s n
  have hqi : QuasiIso α := by
    let : AB5OfSize.{0, 0, max u t, (max u t) + 1} AddCommGrpCat.{max u t} :=
      AB5OfSize_of_univLE.{0, 0, max u t, max u t} AddCommGrpCat.{max u t}
    let : HasExactColimitsOfShape ℕ (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat))
      :=
      ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦
        have : PreservesLimit F (colim (J := ℕ) ⋙ PresheafOfModules.toPresheaf (A ⋙ forget₂
          CommRingCat RingCat)) :=
          preservesLimit_of_natIso _
            (preservesColimitNatIso (PresheafOfModules.toPresheaf (A ⋙ forget₂ CommRingCat
              RingCat))).symm
        preservesLimit_of_reflects_of_preserves _
          (PresheafOfModules.toPresheaf (A ⋙ forget₂ CommRingCat RingCat))⟩⟩⟩
    exact StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE
      q hq hc α hα
  have hepiα : Epi α := by
    refine HomologicalComplex.epi_of_epi_f α fun i => ?_
    let n := i.toNat + 1
    have hi : i ≤ (n : ℕ) := by dsimp [n]; omega
    have hpre : (ComplexShape.embeddingUpIntLE (n : ℤ)).op.f ((n : ℤ) - i).natAbs = i := by
      change (n : ℤ) - (((n : ℤ) - i).natAbs : ℤ) = i
      omega
    have hnotboundary : ¬ (ComplexShape.embeddingUpIntLE (n : ℤ)).op.BoundaryGE
        ((n : ℤ) - i).natAbs := by
      rw [ComplexShape.Embedding.op_boundaryGE_iff, ComplexShape.boundaryLE_embeddingUpIntLE_iff]
      simpa only [Int.natAbs_eq_zero] using (show (n : ℤ) - i ≠ 0 by dsimp [n]; omega)
    have : IsIso ((M.op.πTruncGE (ComplexShape.embeddingUpIntLE (n : ℤ)).op).f i) := by
      dsimp only [HomologicalComplex.πTruncGE, HomologicalComplex.truncGE]
      rw [ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _ hpre]
      exact M.op.isIso_restrictionToTruncGE' _ _ hnotboundary
    have : IsIso ((M.ιTruncLE (n : ℤ)).f i) := by
      change IsIso ((M.op.πTruncGE (ComplexShape.embeddingUpIntLE (n : ℤ)).op).f i).unop
      infer_instance
    have : Epi ((c.ι.app n).f i ≫ α.f i) := by
      rw [← HomologicalComplex.comp_f, hα n, HomologicalComplex.comp_f]
      exact (epi_comp_iff_of_isIso _ _).2 (hepi n i)
    exact epi_of_epi ((c.ι.app n).f i) (α.f i)
  refine ⟨c.pt, α, hqi, hepiα, fun n => ?_⟩
  let E : CochainComplex (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat)) ℤ ⥤
      CochainComplex (ModuleCat.{max u t} (A.obj (op n))) ℤ :=
    (PresheafOfModules.evaluation.{max u t} (A ⋙ forget₂ CommRingCat RingCat)
      (op n)).mapHomologicalComplex (ComplexShape.up ℤ)
  have hkQ : ∀ j, (E.obj (Q j)).KFlat := by
    intro j
    have : (E.obj (Q j)).IsStrictlyLE (j : ℤ) := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (PresheafOfModules.evaluation.{max u t} (A ⋙ forget₂ CommRingCat RingCat)
        (op n)).map_isZero ((CochainComplex.isStrictlyLE_iff (Q j) (j : ℤ)).mp (hle j) i hi)
    have : ∀ i : ℤ, Module.Flat (A.obj (op n)) ((E.obj (Q j)).X i) := by
      intro i
      change Module.Flat (A.obj (op n)) (((Q j).X i).obj (op n))
      have : Projective (((Q j).X i).obj (op n)) := hproj j i n
      have : Module.Projective (A.obj (op n)) (((Q j).X i).obj (op n)) :=
        (((Q j).X i).obj (op n)).projective_of_module_projective
      infer_instance
    exact CochainComplex.KFlat.kFlat_of_flat (E.obj (Q j)) j
  have hk : (colimit (D ⋙ E)).KFlat := CochainComplex.KFlat.kFlat_colimit (D ⋙ E) hkQ
  exact CochainComplex.KFlat.of_iso (preservesColimitIso E D).symm hk


end SystemResolutions

open CategoryTheory.LocalizerMorphism

/-- Componentwise K-flat objects of the homotopy category. -/
private abbrev kFlatHomotopySystems (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    ObjectProperty (HomotopyCategory (Modules.{u, t} A) (ComplexShape.up ℤ)) :=
  fun K => HasKFlatComponents A K.as

/-- Componentwise K-flat resolutions define a left derivability structure. -/
private theorem kFlatHomotopySystems_hasLeftResolutions
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (ComplexShape.up ℤ))
      (kFlatHomotopySystems.{u, t} A)).HasLeftResolutions := by
  intro M
  obtain ⟨K, f, hf, _, hK⟩ := exists_surjective_kFlat_system_resolution A M.as
  exact ⟨LeftResolution.mk (X₁ := ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩)
    ((HomotopyCategory.quotient _ _).map f)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)⟩

/-- Localizing the componentwise K-flat homotopy category gives the derived category. -/
private theorem kFlatHomotopySystems_isLocalization
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (ComplexShape.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι) := by
  have := kFlatHomotopySystems_hasLeftResolutions A
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso (Modules.{u, t} A) (ComplexShape.up ℤ))
    (kFlatHomotopySystems.{u, t} A)
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (ComplexShape.up ℤ))
      (kFlatHomotopySystems.{u, t} A)) DerivedCategory.Qh

/-- Evaluation detects isomorphisms of compatible module systems. -/
private lemma isIso_of_isIso_app
    {J : Type*} [Category J] {R : Jᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{max u t} R} (f : M ⟶ N) (hf : ∀ j, IsIso (f.app j)) :
    IsIso f := by
  let e : M ≅ N := PresheafOfModules.isoMk (fun j => asIso (f.app j))
    (fun {_ _} g => f.naturality g)
  have he : e.hom = f := by ext; rfl
  rw [← he]
  infer_instance

/-- Evaluation detects quasi-isomorphisms of compatible complexes. -/
private lemma quasiIso_of_componentwise
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) {M N : CochainComplex (Modules.{u, t} A) ℤ} (f : M ⟶ N)
    (hf : ∀ n : ℕ, QuasiIso (((PresheafOfModules.evaluation
      (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_of_isIso_app
  intro n
  let E := PresheafOfModules.evaluation (A ⋙ forget₂ CommRingCat RingCat) n
  have := hf n.unop
  let φ : M.sc i ⟶ N.sc i :=
    (HomologicalComplex.shortComplexFunctor (Modules.{u, t} A) (ComplexShape.up ℤ) i).map f
  have hq : ShortComplex.QuasiIso (E.mapShortComplex.map φ) :=
    (quasiIsoAt_iff ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map f) i).1 inferInstance
  exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso E) φ).1
    (inferInstanceAs (IsIso (ShortComplex.homologyMap (E.mapShortComplex.map φ))))

private abbrev evaluationComplex (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    CochainComplex (Modules.{u, t} A) ℤ ⥤
      CochainComplex (ModuleCat.{max u t} (A.obj (op n))) ℤ :=
  (PresheafOfModules.evaluation (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Evaluation commutes with the total tensor product of two complexes. -/
private noncomputable def evaluationTensorIso
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) (M N : CochainComplex (Modules.{u, t} A) ℤ) :
    (TleftCochain ((evaluationComplex A n).obj M)).obj ((evaluationComplex A n).obj N) ≅
      (evaluationComplex A n).obj ((TleftCochain M).obj N) :=
  HomologicalComplex₂.TotalMap.totalIso
    (PresheafOfModules.evaluation (A ⋙ forget₂ CommRingCat RingCat) (op n))
    ((((curriedTensor (Modules.{u, t} A)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M).obj N)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the componentwise tensor comparison in both arguments. -/
private lemma evaluationTensorIso_naturality
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ)
    {M M' N N' : CochainComplex (Modules.{u, t} A) ℤ} (f : M ⟶ M') (g : N ⟶ N') :
    (evaluationTensorIso A n M N).hom ≫ (evaluationComplex A n).map
        (HomologicalComplex.mapBifunctorMap f g (curriedTensor (Modules.{u, t} A)) (.up ℤ)) =
      HomologicalComplex.mapBifunctorMap ((evaluationComplex A n).map f)
        ((evaluationComplex A n).map g) (curriedTensor (ModuleCat.{max u t} (A.obj (op n)))) (.up ℤ)
          ≫
          (evaluationTensorIso A n M' N').hom :=
  HomologicalComplex₂.TotalMap.totalIso_naturality _ _
    ((((curriedTensor (Modules.{u, t} A)).mapBifunctorHomologicalComplex _ _).map f).app N ≫
      (((curriedTensor (Modules.{u, t} A)).mapBifunctorHomologicalComplex _ _).obj M').map g)

section TensorSymmetry

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C] [HasZeroObject C] [HasBinaryBiproducts C]
  [∀ K L : CochainComplex C ℤ,
    HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]

/-- The ordinary braiding gives an isomorphism of tensor bicomplexes. -/
private noncomputable def tensorBicomplexFlipIso (K L : CochainComplex C ℤ) :
    (((curriedTensor C).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L ≅
      (((curriedTensor C).flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => BraidedCategory.braiding (K.X p) (L.X q))
      (by intros; exact (BraidedCategory.braiding_naturality_right _ _).symm))
    (by intros; ext q; exact (BraidedCategory.braiding_naturality_left _ _).symm)

/-- Symmetry of total tensor complexes includes the Koszul sign. -/
private noncomputable def tensorFlipIso (K L : CochainComplex C ℤ) :
    (TleftCochain K).obj L ≅ (TrightCochain K).obj L :=
  HomologicalComplex₂.total.mapIso (tensorBicomplexFlipIso K L) (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K (curriedTensor C) (.up ℤ)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The signed symmetry is natural in the second argument. -/
private lemma tensorFlipIso_naturality (K : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} (f : L ⟶ L') :
    (TleftCochain K).map f ≫ (tensorFlipIso K L').hom =
      (tensorFlipIso K L).hom ≫ (TrightCochain K).map f := by
  let F := curriedTensor C
  have h : (((F.mapBifunctorHomologicalComplex _ _).obj K).map f) ≫
        (tensorBicomplexFlipIso K L').hom =
      (tensorBicomplexFlipIso K L).hom ≫
        (((F.flip.mapBifunctorHomologicalComplex _ _).obj K).map f) := by
    ext p q
    exact BraidedCategory.braiding_naturality_right _ _
  have ht := congrArg (fun g => HomologicalComplex₂.total.map g (.up ℤ)) h
  change HomologicalComplex.mapBifunctorMap (𝟙 K) f F _ ≫
      (HomologicalComplex₂.total.map (tensorBicomplexFlipIso K L').hom _ ≫
        (HomologicalComplex.mapBifunctorFlipIso L' K F _).hom) =
    (HomologicalComplex₂.total.map (tensorBicomplexFlipIso K L).hom _ ≫
      (HomologicalComplex.mapBifunctorFlipIso L K F _).hom) ≫
        HomologicalComplex.mapBifunctorMap f (𝟙 K) F _
  rw [← Category.assoc]
  simp only [HomologicalComplex.mapBifunctorMap]
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, ← HomologicalComplex₂.total.map_comp, ht,
    HomologicalComplex₂.total.map_comp]
  simp only [Category.assoc]
  have hf' : HomologicalComplex₂.total.map
          (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).map f) (.up ℤ) ≫
        (HomologicalComplex.mapBifunctorFlipIso L' K F (.up ℤ)).hom =
      (HomologicalComplex.mapBifunctorFlipIso L K F (.up ℤ)).hom ≫
        HomologicalComplex₂.total.map
          (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).map f).app K) (.up ℤ) := by
    simpa [HomologicalComplex.mapBifunctorMap] using
      HomologicalComplex.mapBifunctorFlipIso_hom_naturality f (𝟙 K) F (.up ℤ)
  rw [hf']

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The signed symmetry is natural in the first argument. -/
private lemma tensorFlipIso_naturality_left {K K' : CochainComplex C ℤ}
    (f : K ⟶ K') (L : CochainComplex C ℤ) :
    (TrightCochain L).map f ≫ (tensorFlipIso K' L).hom =
      (tensorFlipIso K L).hom ≫ (TleftCochain L).map f := by
  let F := curriedTensor C
  have h : (((F.mapBifunctorHomologicalComplex _ _).map f).app L) ≫
        (tensorBicomplexFlipIso K' L).hom =
      (tensorBicomplexFlipIso K L).hom ≫
        (((F.flip.mapBifunctorHomologicalComplex _ _).map f).app L) := by
    ext p q
    exact BraidedCategory.braiding_naturality_left _ _
  have ht := congrArg (fun g => HomologicalComplex₂.total.map g (.up ℤ)) h
  change HomologicalComplex.mapBifunctorMap f (𝟙 L) F _ ≫
      (HomologicalComplex₂.total.map (tensorBicomplexFlipIso K' L).hom _ ≫
        (HomologicalComplex.mapBifunctorFlipIso L K' F _).hom) =
    (HomologicalComplex₂.total.map (tensorBicomplexFlipIso K L).hom _ ≫
      (HomologicalComplex.mapBifunctorFlipIso L K F _).hom) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 L) f F _
  rw [← Category.assoc]
  simp only [HomologicalComplex.mapBifunctorMap]
  rw [CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, ← HomologicalComplex₂.total.map_comp, ht,
    HomologicalComplex₂.total.map_comp]
  simp only [Category.assoc]
  have hf' : HomologicalComplex₂.total.map
          (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).map f).app L) (.up ℤ) ≫
        (HomologicalComplex.mapBifunctorFlipIso L K' F (.up ℤ)).hom =
      (HomologicalComplex.mapBifunctorFlipIso L K F (.up ℤ)).hom ≫
        HomologicalComplex₂.total.map
          (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj L).map f) (.up ℤ) := by
    simpa [HomologicalComplex.mapBifunctorMap] using
      HomologicalComplex.mapBifunctorFlipIso_hom_naturality (𝟙 L) f F (.up ℤ)
  rw [hf']

end TensorSymmetry

/-- Tensoring on the left preserves quasi-isomorphisms iff tensoring on the right does. -/
private lemma quasiIso_tleft_map_iff_tright_map {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u t} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{max u t} R) ℤ} (f : L ⟶ L') :
    QuasiIso ((TleftCochain K).map f) ↔ QuasiIso ((TrightCochain K).map f) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (tensorFlipIso K L) (tensorFlipIso K L')
    (tensorFlipIso_naturality K f).symm)

/-- Tensoring on the right by a K-flat complex preserves quasi-isomorphisms. -/
private lemma quasiIso_tright_map {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u t} R) ℤ) (hK : K.KFlat)
    {L L' : CochainComplex (ModuleCat.{max u t} R) ℤ} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso ((TrightCochain K).map f) := by
  have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 ‹QuasiIso f›
  have h := (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK) _ hf
  change HomotopyCategory.quasiIso (ModuleCat.{max u t} R) (.up ℤ)
    ((HomotopyCategory.quotient _ _).map ((TrightCochain K).map f)) at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

/-- Tensoring on the left by a K-flat complex preserves quasi-isomorphisms. -/
private lemma quasiIso_tleft_map {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u t} R) ℤ) (hK : K.KFlat)
    {L L' : CochainComplex (ModuleCat.{max u t} R) ℤ} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso ((TleftCochain K).map f) := by
  have := quasiIso_tright_map K hK f
  exact (quasiIso_tleft_map_iff_tright_map K f).2 inferInstance

/-- Tensoring componentwise K-flat systems preserves quasi-isomorphisms. -/
private lemma tensor_left_inverts (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    (K : CochainComplex (Modules.{u, t} A) ℤ) (hK : HasKFlatComponents A K)
    {L L' : CochainComplex (Modules.{u, t} A) ℤ} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso ((TleftCochain K).map f) := by
  apply quasiIso_of_componentwise A
  intro n
  have := quasiIso_evaluation A f n
  have hq := quasiIso_tleft_map ((evaluationComplex A n).obj K) (hK n)
    ((evaluationComplex A n).map f)
  have h := evaluationTensorIso_naturality A n (𝟙 K) f
  change (evaluationTensorIso A n K L).hom ≫
    (evaluationComplex A n).map ((TleftCochain K).map f) =
      (TleftCochain ((evaluationComplex A n).obj K)).map ((evaluationComplex A n).map f) ≫
        (evaluationTensorIso A n K L').hom at h
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (evaluationTensorIso A n K L)
    (evaluationTensorIso A n K L') h)).1 hq

/-- Tensoring a quasi-isomorphism between K-flat complexes with any complex on the right
preserves quasi-isomorphisms. -/
@[ega "III 6.10.3" "Remark 6.10.3(ii)"]
private lemma quasiIso_tright_map_between_kFlat {R : Type u} [CommRing R]
    {K K' : CochainComplex (ModuleCat.{max u t} R) ℤ} (f : K ⟶ K') [QuasiIso f]
    (hK : K.KFlat) (hK' : K'.KFlat) (L : CochainComplex (ModuleCat.{max u t} R) ℤ) :
    QuasiIso ((TrightCochain L).map f) := by
  have := CochainComplex.DerivedTensor.quasiIso_tleftCochain_map f hK hK' L
  exact (quasiIso_tleft_map_iff_tright_map L f).1 inferInstance

set_option maxHeartbeats 800000 in
-- The final `exact` unifies two `evaluationTensorIso` arrows, an expensive `whnf` check.
/-- Tensoring a quasi-isomorphism between componentwise K-flat systems with an arbitrary
system preserves quasi-isomorphisms. -/
private lemma tensor_right_inverts_between_kFlat (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    {K K' : CochainComplex (Modules.{u, t} A) ℤ}
    (hK : HasKFlatComponents A K) (hK' : HasKFlatComponents A K')
    (f : K ⟶ K') [QuasiIso f] (L : CochainComplex (Modules.{u, t} A) ℤ) :
    QuasiIso ((TrightCochain L).map f) := by
  apply quasiIso_of_componentwise A
  intro n
  have := quasiIso_evaluation A f n
  have hq : QuasiIso ((TrightCochain ((evaluationComplex A n).obj L)).map
      ((evaluationComplex A n).map f)) :=
    quasiIso_tright_map_between_kFlat ((evaluationComplex A n).map f)
      (hK n) (hK' n) ((evaluationComplex A n).obj L)
  have h := evaluationTensorIso_naturality A n f (𝟙 L)
  change (evaluationTensorIso A n K L).hom ≫
    (evaluationComplex A n).map ((TrightCochain L).map f) =
      (TrightCochain ((evaluationComplex A n).obj L)).map ((evaluationComplex A n).map f) ≫
        (evaluationTensorIso A n K' L).hom at h
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (evaluationTensorIso A n K L)
    (evaluationTensorIso A n K' L) h)).1 hq

section HomotopyTensor

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [∀ K L : CochainComplex C ℤ,
    HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a complex with a homotopy class of complexes is functorial in the complex. -/
private noncomputable def tensorToHomotopyFunctor :
    CochainComplex C ℤ ⥤ HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory C (.up ℤ) where
  obj := Tleft
  map {K K'} f :=
    { app := fun L => (HomotopyCategory.quotient _ _).map ((TrightCochain L.as).map f)
      naturality := fun {L L'} g => by
        obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
        change (HomotopyCategory.quotient _ _).map ((TleftCochain K).map g) ≫
          (HomotopyCategory.quotient _ _).map ((TrightCochain _).map f) =
          (HomotopyCategory.quotient _ _).map ((TrightCochain _).map f) ≫
            (HomotopyCategory.quotient _ _).map ((TleftCochain K').map g)
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        exact congrArg (HomotopyCategory.quotient _ _).map
          (((curriedTensor C).map₂CochainComplex.map f).naturality g) }
  map_id K := by
    ext L
    change (HomotopyCategory.quotient _ _).map ((TrightCochain L.as).map (𝟙 K)) = 𝟙 _
    simp only [CategoryTheory.Functor.map_id]
  map_comp f g := by
    ext L
    change (HomotopyCategory.quotient _ _).map ((TrightCochain L.as).map (f ≫ g)) =
      (HomotopyCategory.quotient _ _).map ((TrightCochain L.as).map f) ≫
        (HomotopyCategory.quotient _ _).map ((TrightCochain L.as).map g)
    simp only [CategoryTheory.Functor.map_comp]

/-- Total tensor product of complexes descends to a bifunctor on homotopy categories. -/
@[sga "4 XVII 1.1.6.2" "special case"]
private noncomputable def homotopyTensor :
    HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory C (.up ℤ) :=
  CategoryTheory.Quotient.lift _ tensorToHomotopyFunctor
    (fun K K' f g h => by
      ext L
      exact CategoryTheory.Quotient.sound _ (TrightCochain_preservesHomotopyRel L.as h))

set_option backward.isDefEq.respectTransparency false in
/-- Signed symmetry of the total tensor bifunctor on homotopy categories. -/
private noncomputable def homotopyTensorSymmetry [BraidedCategory C] :
    (homotopyTensor (C := C)) ≅ (homotopyTensor (C := C)).flip := by
  refine NatIso.ofComponents (fun K => NatIso.ofComponents (fun L =>
    (HomotopyCategory.quotient _ _).mapIso (tensorFlipIso K.as L.as)) ?_) ?_
  · intro L L' f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
    exact ((HomotopyCategory.quotient C (.up ℤ)).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient C (.up ℤ)).map
        (tensorFlipIso_naturality _ f)).trans
          ((HomotopyCategory.quotient C (.up ℤ)).map_comp _ _))
  · intro K K' f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
    ext L
    exact ((HomotopyCategory.quotient C (.up ℤ)).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient C (.up ℤ)).map
        (tensorFlipIso_naturality_left f _)).trans
          ((HomotopyCategory.quotient C (.up ℤ)).map_comp _ _))

end HomotopyTensor

end ModuleSystemKFlatComparison

end

end Construction
