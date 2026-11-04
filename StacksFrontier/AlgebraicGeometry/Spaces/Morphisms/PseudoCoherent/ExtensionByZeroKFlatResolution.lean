module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSigmaYonedaFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentLocalization

/-!
# K-flat resolutions whose extension by zero is K-flat

Let `u : U ⟶ W` be an étale morphism of algebraic spaces. Every complex of `𝒪_U`-modules receives
a quasi-isomorphism from a K-flat complex with flat terms whose extension by zero `u_!K` is again
a K-flat complex with flat terms.

The resolution is the one of Stacks 06YS, the colimit of the ladder of Stacks 077J, built from
the class of flat modules whose extension by zero is flat. That class contains a zero object, is
closed under binary biproducts, and every module is a quotient of one of its members: a free
module on a coproduct of representable sheaves `∐ j_{V!}𝒪_V` is flat
(`Stacks.SheafOfModules.SigmaYoneda.isFlat_freeSigmaYoneda`), and its extension by zero is the
free module on the coproduct of the representable sheaves of the composites `V → U → W`
(`Stacks.SheafOfModules.SigmaYoneda.leftAdjointObjFreeSigmaYonedaIso`), hence flat again. Since
extension by zero is exact and commutes with colimits, `u_!` of the colimit is the colimit of
the ladder of bounded above complexes `u_!Qₙ` with flat terms, which is K-flat by Stacks 06YQ
and 06YR.

## Main results

* `AlgebraicGeometry.Space.exists_quasiIso_isKFlat_extensionByZero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize
attribute [local instance 2000] abelian_ringedToposStructureRingSheafModules

section

variable {U W : AlgebraicSpaces B S hS} (u : U ⟶ W) (hu : IsEtale B S hS u.hom)

/-- Flat `𝒪_U`-modules whose extension by zero along `u` is flat. -/
def IsFlatAndExtensionByZeroFlat :
    ObjectProperty (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)) := fun F ↦
  AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (smallEtaleRingedTopos B S hS U).O)
      F ∧
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS W).O) ((etaleExtensionByZero B S hS u hu).obj F)

/-- Flatness of `𝒪_V`-modules is invariant under isomorphism. -/
private theorem isFlat_of_iso {V : AlgebraicSpaces B S hS}
    {M N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS V)} (e : M ≅ N)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS V).O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS V).O) N :=
  Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize.{u, u + 1, u} _ e hM

/-- Every `𝒪_U`-module is a quotient of a flat module whose extension by zero is flat. -/
theorem exists_epi_isFlatAndExtensionByZeroFlat
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)) :
    ∃ (Y : _) (_ : IsFlatAndExtensionByZeroFlat u hu Y) (p : Y ⟶ F), Epi p := by
  obtain ⟨ι, V, p, hp⟩ :=
    Stacks.SheafOfModules.SigmaYoneda.exists_epi_freeSigmaYoneda
      (ringedToposStructureRingSheaf B S hS U) F
  refine ⟨_, ⟨Stacks.SheafOfModules.SigmaYoneda.isFlat_freeSigmaYoneda _ V, ?_⟩, p, hp⟩
  exact isFlat_of_iso
    (Stacks.SheafOfModules.SigmaYoneda.leftAdjointObjFreeSigmaYonedaIso _
      (etaleModuleLowerShriekAdjunction B S hS u hu) V).symm
    (Stacks.SheafOfModules.SigmaYoneda.isFlat_freeSigmaYoneda _ _)

/-- Extension by zero preserves colimits, being a left adjoint. -/
instance preservesColimitsOfSize_etaleExtensionByZero :
    PreservesColimitsOfSize.{0, 0} (etaleExtensionByZero B S hS u hu) :=
  (etaleModuleLowerShriekAdjunction B S hS u hu).leftAdjoint_preservesColimits

/-- The flat modules whose extension by zero is flat contain a zero object. -/
theorem containsZero_isFlatAndExtensionByZeroFlat :
    (IsFlatAndExtensionByZeroFlat u hu).ContainsZero := by
  obtain ⟨Z, hZ, hflat⟩ :=
    (Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize.{u, u + 1, u}
      (smallEtaleRingedTopos B S hS U).O).exists_zero
  obtain ⟨Z', hZ', hflat'⟩ :=
    (Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize.{u, u + 1, u}
      (smallEtaleRingedTopos B S hS W).O).exists_zero
  exact ⟨⟨Z, hZ, hflat, isFlat_of_iso
    (hZ'.iso (Functor.map_isZero _ hZ)) hflat'⟩⟩

/-- The flat modules whose extension by zero is flat are closed under binary biproducts. -/
theorem isFlatAndExtensionByZeroFlat_biprod
    (X Y : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U))
    (hX : IsFlatAndExtensionByZeroFlat u hu X) (hY : IsFlatAndExtensionByZeroFlat u hu Y) :
    IsFlatAndExtensionByZeroFlat u hu (X ⊞ Y) :=
  have := preservesBinaryBiproduct_of_preservesBinaryCoproduct
    (F := etaleExtensionByZero B S hS u hu) (X := X) (Y := Y)
  ⟨Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize _ X Y hX.1 hY.1,
    isFlat_of_iso ((etaleExtensionByZero B S hS u hu).mapBiprod X Y).symm
      (Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize.{u, u + 1, u}
        (smallEtaleRingedTopos B S hS W).O _ _ hX.2 hY.2)⟩

open Stacks.SheafOfModules.KFlatResolution in
/-- **K-flat resolutions whose extension by zero is K-flat.**  Every complex of `𝒪_U`-modules
receives a quasi-isomorphism from a K-flat complex with flat terms whose extension by zero along
the étale morphism `u` is again K-flat with flat terms. -/
theorem exists_quasiIso_isKFlat_extensionByZero
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)) ℤ)
      (g : K ⟶ N), QuasiIso g ∧
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := smallEtaleRingedTopos B S hS U) ((HomotopyCategory.quotient _ _).obj K) ∧
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := smallEtaleRingedTopos B S hS W) ((HomotopyCategory.quotient _ _).obj
          (((etaleExtensionByZero B S hS u hu).mapHomologicalComplex _).obj K)) := by
  let R := (smallEtaleRingedTopos B S hS U).O
  let R' := (smallEtaleRingedTopos B S hS W).O
  have := hasColimitsOfShape_nat_ofSize.{u, u + 1, u} R
  have := hasExactColimitsOfShape_nat_ofSize.{u, u + 1, u} R
  have := hasColimitsOfShape_nat_ofSize.{u, u + 1, u} R'
  have := containsZero_isFlatAndExtensionByZeroFlat u hu
  obtain ⟨Q, q, g, hq, -, hle, hP, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE (IsFlatAndExtensionByZeroFlat u hu)
      (isFlatAndExtensionByZeroFlat_biprod u hu) (exists_epi_isFlatAndExtensionByZeroFlat u hu) N
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk N
    (NatTrans.ofSequence (fun n ↦ q n ≫ N.ιTruncLE (n : ℤ)) (fun n ↦ by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ N := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ N.ιTruncLE (n : ℤ) := fun n ↦ hc.fac s n
  let E := (etaleExtensionByZero B S hS u hu).mapHomologicalComplex (ComplexShape.up ℤ)
  refine ⟨colimit D, α,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq hc α hα,
    ⟨kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize R D (fun n ↦ ⟨n, hle n⟩) (fun n i ↦ (hP n i).1),
      isFlat_colimit_X_ofSize R D (fun n i ↦ (hP n i).1)⟩, ?_, ?_⟩
  · refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _ (E.mapCocone c)
      (isColimitOfPreserves E hc)
      (hF_sheafTensor_ofSize R') (hexact_sheafOfModules_ofSize R') (fun n ↦ ?_)
    have : (D.obj n).IsStrictlyLE n := hle n
    have : CochainComplex.IsStrictlyLE (E.obj (D.obj n)) n :=
      (CochainComplex.isStrictlyLE_iff _ n).2 fun i hi ↦
        Functor.map_isZero _ ((D.obj n).isZero_of_isStrictlyLE n i hi)
    exact CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ (E.obj (D.obj n)) n
      (hF_sheafTensor_ofSize R') (hexact_sheafOfModules_ofSize R')
      (fun i ↦ kFlat_single_of_isFlat_ofSize R' _ (hP n i).2 i)
  · exact fun i ↦ isFlat_of_iso
      ((HomologicalComplex.eval _ _ i).mapIso (preservesColimitIso E D)).symm
      (isFlat_colimit_X_ofSize R' (D ⋙ E) (fun n i ↦ (hP n i).2) i)

end

end AlgebraicGeometry.Space
