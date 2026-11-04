module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.ExtendScalars.Flat

@[expose] public section

/-!
# Base change of a two-term complex

Let `K` be an object of `D(R)` whose cohomology is concentrated in degrees `-1` and `0`, and let
`K⁻¹ → K⁰` be a two-term complex of `R`-modules representing it whose degree-zero term is flat.
For any ring map `R → R'` the termwise base change `K⁻¹ ⊗ R' → K⁰ ⊗ R'` then represents
`τ_{≥ -1}(K ⊗_R^L R')`.

## Main results

* `TwoTermComplex.twoTermBaseChange_iso_truncGE` (Stacks 0G9G): the canonical comparison from
  derived to termwise base change factors through the truncation projection `τ_{≥ -1}`, and the
  induced morphism is invertible.

## Implementation notes

Derived base change is not taken from a fixed model. It is quantified over: the statement takes
any functor together with a comparison transformation exhibiting it as a total left derived
functor of termwise extension of scalars, which pins it down up to unique isomorphism. "The
complex represents `τ_{≥ -1}(K ⊗^L R')`" is recorded as the existence of a factorization of that
comparison through `truncGEπ (-1)` by an isomorphism, so no choice of resolution enters the
statement.

The proof replaces `K` by a K-projective resolution `P → L`, where the comparison is an
isomorphism because K-projective complexes compute the total left derived functor. Flatness of
`K⁰` makes the base change of the (acyclic) mapping cone of `P → L` exact in its top three
degrees, which is what forces `τ_{≥ -1}` of the comparison to be an isomorphism.

Ring and module sizes carry independent universe parameters; the common module universe is the
one that accommodates extension of scalars.

## References

* [The Stacks Project, Lemma 15.86.6 (0G9G)](https://stacks.math.columbia.edu/tag/0G9G)
-/

open CategoryTheory Limits Functor ZeroObject
open scoped TensorProduct

namespace TwoTermComplex

universe u v w

attribute [local instance] HasDerivedCategory.standard

set_option backward.defeqAttrib.useBackward true in
public lemma isRightKanExtension_iff_precomp_of_fullyFaithful_whiskeringLeft
    {C C' D H : Type*} [Category* C] [Category* C']
    [Category* D] [Category* H] (q : C' ⥤ C)
    [((whiskeringLeft C' C H).obj q).Full]
    [((whiskeringLeft C' C H).obj q).Faithful]
    {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) :
    LF.IsRightKanExtension α ↔ LF.IsRightKanExtension
      ((Functor.associator _ _ _).hom ≫ whiskerLeft q α) := by
  have : (RightExtension.precomp L F q).IsEquivalence := by
    apply CostructuredArrow.isEquivalenceMap₂
  let eq : (RightExtension.mk LF α).IsUniversal ≃
      (RightExtension.mk LF ((Functor.associator _ _ _).hom ≫ whiskerLeft q α)).IsUniversal :=
    (IsTerminal.isTerminalIffObj (RightExtension.precomp L F q)
      (RightExtension.mk LF α)).trans
      (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  exact ⟨fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension LF α)⟩⟩,
    fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension LF _)⟩⟩⟩

public lemma isRightKanExtension_iff_of_iso
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    {L₀ L₁ : C ⥤ D} {F₀ F₁ : C ⥤ H} (LF : D ⥤ H)
    (eL : L₀ ≅ L₁) (eF : F₁ ≅ F₀) (α : L₁ ⋙ LF ⟶ F₁) :
    LF.IsRightKanExtension α ↔
      LF.IsRightKanExtension (whiskerRight eL.hom LF ≫ α ≫ eF.hom) := by
  have h₁ := isRightKanExtension_iff_postcomp₁ (𝟭 D)
    (Functor.rightUnitor L₀ ≪≫ eL) α
  have heq : (Functor.associator L₀ (𝟭 D) LF).inv ≫
      whiskerRight (Functor.rightUnitor L₀ ≪≫ eL).hom LF ≫ α =
      whiskerRight eL.hom LF ≫ α := by ext; simp
  rw [heq] at h₁
  exact h₁.trans (isRightKanExtension_iff_of_iso₂
    (whiskerRight eL.hom LF ≫ α) (whiskerRight eL.hom LF ≫ α ≫ eF.hom)
    eF (Iso.refl LF) (by simp))

private lemma hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [EnoughProjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape ℕ F] :
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let P := isProjective A
  let : P.ContainsZero := ⟨0, isZero_zero A, inferInstance⟩
  apply F.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex P
  · exact fun X Y (_ : Projective X) (_ : Projective Y) => inferInstanceAs (Projective (X ⊞ Y))
  · exact fun X => ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  · intro a L hL hP hacyc
    have (n : ℤ) : Projective (L.X n) := hP n
    have := CochainComplex.isKProjective_of_projective L a
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply (IsZero.iff_id_eq_zero _).2
    simpa using (F.mapHomotopy
      (CochainComplex.IsKProjective.homotopyZero (𝟙 L) hacyc)).homologyMap_eq n

/-- A localization that is fully faithful on maps from one object has an initial
index in the corresponding pointwise right Kan-extension diagram. -/
private noncomputable def structuredArrowMkIdInitialOfBijective
    {C D : Type*} [Category* C] [Category* D] (S : C ⥤ D) {X : C}
    (hS : ∀ Y : C, Function.Bijective (S.map : (X ⟶ Y) → (S.obj X ⟶ S.obj Y))) :
    IsInitial (StructuredArrow.mk (𝟙 (S.obj X))) :=
  IsInitial.ofUniqueHom
    (fun c ↦ StructuredArrow.homMk ((hS c.right).surjective c.hom).choose (by
      simp [((hS c.right).surjective c.hom).choose_spec]))
    (fun c m ↦ by
      ext
      simp only [StructuredArrow.homMk_right]
      apply (hS c.right).injective
      rw [((hS c.right).surjective c.hom).choose_spec]
      simpa using StructuredArrow.w m)

/-- K-projective complexes compute the total left-derived functor. -/
private lemma isIso_comparison_of_isKProjective
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [EnoughProjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape ℕ F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [LF.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso A (.up ℤ))]
    (P : CochainComplex A ℤ) [P.IsKProjective] : IsIso (α.app P) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let eL := DerivedCategory.quotientCompQhIso A
  let eF : q ⋙ Fh ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Qh ⋙ LF ⟶ Fh :=
    ((whiskeringLeft _ _ _).obj q).preimage
      ((Functor.associator _ _ _).inv ≫ whiskerRight eL.hom LF ≫ α ≫ eF.inv)
  have hβ : (Functor.associator _ _ _).hom ≫ whiskerLeft q β =
      whiskerRight eL.hom LF ≫ α ≫ eF.inv := by
    dsimp [β]
    rw [← whiskeringLeft_obj_map, map_preimage]
    simp
  have := IsLeftDerivedFunctor.isRightKanExtension LF α
    (HomologicalComplex.quasiIso A (.up ℤ))
  have : LF.IsRightKanExtension β := by
    rw [isRightKanExtension_iff_precomp_of_fullyFaithful_whiskeringLeft q LF β, hβ]
    exact (isRightKanExtension_iff_of_iso LF eL eF.symm α).1 inferInstance
  have : LF.IsLeftDerivedFunctor β (HomotopyCategory.quasiIso A (.up ℤ)) := ⟨inferInstance⟩
  have := hasPointwiseLeftDerivedFunctor_of_enoughProjectives F
  have hp := LF.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor β
    (HomotopyCategory.quasiIso A (.up ℤ)) (DerivedCategory.Qh.obj (q.obj P))
  have hinit := structuredArrowMkIdInitialOfBijective DerivedCategory.Qh
    (fun Y => CochainComplex.IsKProjective.Qh_map_bijective P Y)
  have hiso : IsIso (β.app (q.obj P)) := by
    simpa using hp.isIso_π_app_of_isInitial _ hinit
  have heq := congr_app hβ P
  simp only [NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
    Category.id_comp, whiskerRight_app] at heq
  rw [heq] at hiso
  have := IsIso.of_isIso_comp_left (LF.map (eL.hom.app P)) (α.app P ≫ eF.inv.app P)
  exact IsIso.of_isIso_comp_right (α.app P) (eF.inv.app P)

private lemma exact_map_of_mono_map_fromOpcycles
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (S : ShortComplex A) (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [Mono (F.map S.fromOpcycles)] : (S.map F).Exact := by
  let T := ShortComplex.mk S.f S.pOpcycles S.f_pOpcycles
  let φ : T.map F ⟶ S.map F :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map S.fromOpcycles
      comm₂₃ := by simp [T, ← F.map_comp] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    ((T.exact_of_g_is_cokernel S.opcyclesIsCokernel).map_of_epi_of_preservesCokernel F
      inferInstance inferInstance)

private lemma mono_extendScalars_map_of_flat
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] (φ : R →+* R')
    (S : ShortComplex (ModuleCat.{max u v w} R)) (hS : S.ShortExact)
    [Module.Flat R S.X₃] : Mono ((ModuleCat.extendScalars φ).map S.f) := by
  let := φ.toAlgebra
  rw [ModuleCat.mono_iff_injective]
  exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hS.moduleCat_surjective_g
    S.f.hom hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact) R'

private lemma exact_extendScalars_map_of_flat
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] (φ : R →+* R')
    (S : ShortComplex (ModuleCat.{max u v w} R)) (hS : S.Exact)
    {D : ModuleCat.{max u v w} R} (h : S.X₃ ⟶ D) [hh : Epi h]
    (hz : S.g ≫ h = 0) (hex : (ShortComplex.mk S.g h hz).Exact)
    [Module.Flat R D] : (S.map (ModuleCat.extendScalars φ)).Exact := by
  have : (ModuleCat.extendScalars.{u, v, max u v w} φ).IsLeftAdjoint :=
    ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u w} φ
  let T := ShortComplex.mk S.fromOpcycles h (by
    rw [← cancel_epi S.pOpcycles, ShortComplex.p_fromOpcycles_assoc, hz, comp_zero])
  let p : ShortComplex.mk S.g h hz ⟶ T :=
    { τ₁ := S.pOpcycles
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have : Mono S.fromOpcycles := hS.mono_fromOpcycles
  have : Mono ((ModuleCat.extendScalars φ).map S.fromOpcycles) :=
    mono_extendScalars_map_of_flat φ T ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono p).1 hex⟩
  exact exact_map_of_mono_map_fromOpcycles S (ModuleCat.extendScalars φ)

/-- Tensoring an acyclic bounded above complex with flat top term preserves
exactness in its top three degrees. -/
private lemma isLE_extendScalars_of_acyclic_of_flat
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ) (a : ℤ)
    [K.IsStrictlyLE a] (hK : K.Acyclic) [Module.Flat R (K.X a)] :
    CochainComplex.IsLE
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (a - 3) := by
  let F := ModuleCat.extendScalars.{u, v, max u v w} φ
  have : F.IsLeftAdjoint :=
    ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u w} φ
  have hK' : ∀ i j k : ℤ, i + 1 = j → j + 1 = k → (K.sc' i j k).Exact := fun i j k hij hjk =>
    (K.exactAt_iff' i j k (by simp [← hij]) (by simp [← hjk])).1 (hK j)
  have hF' : ∀ i j k : ℤ, i + 1 = j → j + 1 = k → ((K.sc' i j k).map F).Exact →
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K).ExactAt j :=
    fun i j k hij hjk => (HomologicalComplex.exactAt_iff'
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) i j k
      (by simp [← hij]) (by simp [← hjk])).2
  have htop : Epi (K.d (a - 1) a) :=
    ((K.sc' (a - 1) a (a + 1)).exact_iff_epi
      ((K.isZero_of_isStrictlyLE a (a + 1) (by omega)).eq_zero_of_tgt _)).1
      (hK' _ _ _ (by omega) rfl)
  rw [CochainComplex.isLE_iff]
  intro i hi
  by_cases hi0 : i = a
  · subst i
    refine hF' (a - 1) a (a + 1) (by omega) rfl ((ShortComplex.exact_iff_epi _ ?_).2 ?_)
    · exact (F.map_isZero (K.isZero_of_isStrictlyLE a (a + 1) (by omega))).eq_zero_of_tgt _
    · change Epi (F.map (K.d (a - 1) a))
      infer_instance
  by_cases hi1 : i = a - 1
  · subst i
    exact hF' (a - 2) (a - 1) a (by omega) (by omega)
      ((hK' _ _ _ (by omega) (by omega)).map_of_epi_of_preservesCokernel F htop inferInstance)
  by_cases hi2 : i = a - 2
  · subst i
    exact hF' (a - 3) (a - 2) (a - 1) (by omega) (by omega)
      (exact_extendScalars_map_of_flat (hh := htop) φ _ (hK' _ _ _ (by omega) (by omega))
        (K.d (a - 1) a) (K.d_comp_d _ _ _) (hK' _ _ _ (by omega) (by omega)))
  · apply HomologicalComplex.ExactAt.of_isZero
    exact F.map_isZero (K.isZero_of_isStrictlyLE a i (by omega))

private lemma acyclic_mappingCone_of_quasiIso
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    (CochainComplex.mappingCone f).Acyclic := by
  have hz :=
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)).isZero₃_of_isIso₁
      (DerivedCategory.mappingCone_triangle_distinguished f)
      (inferInstanceAs (IsIso (DerivedCategory.Q.map f)))
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((DerivedCategory.homologyFunctorFactors C i).app
    (CochainComplex.mappingCone f)).isZero_iff.1
      ((DerivedCategory.homologyFunctor C i).map_isZero hz)

private lemma isIso_truncGE_map_extendScalars_of_quasiIso
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] (φ : R →+* R')
    {P L : CochainComplex (ModuleCat.{max u v w} R) ℤ} (f : P ⟶ L) [QuasiIso f]
    (a : ℤ) [P.IsStrictlyLE a] [L.IsStrictlyLE a] [Module.Flat R (L.X a)] :
    IsIso ((DerivedCategory.TStructure.t.truncGE (a - 1)).map
      (DerivedCategory.Q.map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f))) := by
  let F := ModuleCat.extendScalars.{u, v, max u v w} φ
  have : F.IsLeftAdjoint :=
    ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u w} φ
  let C := CochainComplex.mappingCone f
  have hC : C.IsStrictlyLE a := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => (CochainComplex.mappingCone.isZero_X_iff f i).2
      ⟨P.isZero_of_isStrictlyLE a (i + 1) (by omega), L.isZero_of_isStrictlyLE a i hi⟩
  have hflat : Module.Flat R (C.X a) :=
    Module.Flat.of_linearEquiv
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f a (a + 1) rfl ≪≫
        (isoZeroBiprod (Y := L.X a)
          (P.isZero_of_isStrictlyLE a (a + 1) (by omega))).symm).toLinearEquiv
  have hFC : CochainComplex.IsLE ((F.mapHomologicalComplex (.up ℤ)).obj C) (a - 3) :=
    isLE_extendScalars_of_acyclic_of_flat φ C a (acyclic_mappingCone_of_quasiIso f)
  let f' := (F.mapHomologicalComplex (.up ℤ)).map f
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f')
  have hle : T.obj₃.IsLE (a - 3) := DerivedCategory.TStructure.t.isLE_of_iso
    (DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f F)) (a - 3)
  have hshift : DerivedCategory.TStructure.t.IsLE T.invRotate.obj₁ (a - 2) :=
    DerivedCategory.TStructure.t.isLE_shift T.obj₃ (a - 3) (-1) (a - 2) (by omega)
  exact DerivedCategory.TStructure.t.isIso₂_truncGE_map_of_isLE T.invRotate
    (Pretriangulated.inv_rot_of_distTriang T
      (DerivedCategory.mappingCone_triangle_distinguished f')) (a - 2) (a - 1) (by omega) hshift

private lemma exists_iso_truncGE_factorization
    {C : Type*} [Category* C] [Preadditive C] [Limits.HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (t : Triangulated.TStructure C)
    {X Y : C} (g : X ⟶ Y) (n : ℤ) [hY : t.IsGE Y n]
    [IsIso ((t.truncGE n).map g)] :
    ∃ f : (t.truncGE n).obj X ⟶ Y,
      (t.truncGEπ n).app X ≫ f = g ∧ IsIso f := by
  refine ⟨(t.truncGE n).map g ≫ inv ((t.truncGEπ n).app Y), ?_, inferInstance⟩
  rw [← Category.assoc, t.truncGEπ_naturality]
  simp

public lemma hasExactColimitsOfShape_nat_moduleCat {R : Type*} [Ring R] :
    HasExactColimitsOfShape ℕ (ModuleCat.{w} R) := by
  let : AB5OfSize.{0, 0, w, w + 1} AddCommGrpCat.{w} :=
    AB5OfSize_of_univLE.{0, 0, w, w} AddCommGrpCat.{w}
  exact HasExactColimitsOfShape.domain_of_functor ℕ
    (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})

/-- **Stacks 0G9G.** Termwise base change of a two-term representative whose degree-zero term
is flat represents the truncation in degrees at least `-1` of the derived base change: the
canonical comparison, transported along the representative isomorphism `e`, factors through
`truncGEπ (-1)` by an isomorphism. -/
@[stacks 0G9G]
public theorem twoTermBaseChange_iso_truncGE
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    (φ : R →+* R') :
    letI : (ModuleCat.extendScalars.{u, v, max v (max u w)} φ).IsLeftAdjoint :=
      ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u w} φ
    ∀ (K : DerivedCategory (ModuleCat.{max u v w} R))
      (L : CochainComplex (ModuleCat.{max u v w} R) ℤ)
      (e : DerivedCategory.Q.obj L ≅ K)
      (_hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
        Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) i).obj K))
      (_hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → Limits.IsZero (L.X i))
      (_hflat : Module.Flat R (L.X 0))
      (derivedBaseChange : DerivedCategory (ModuleCat.{max u v w} R) ⥤
        DerivedCategory (ModuleCat.{max u v w} R'))
      (comparison : DerivedCategory.Q ⋙ derivedBaseChange ⟶
        (ModuleCat.extendScalars.{u, v, max v (max u w)} φ).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      [derivedBaseChange.IsLeftDerivedFunctor comparison
        (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R) (ComplexShape.up ℤ))],
      ∃ f : ((DerivedCategory.TStructure.t (C := ModuleCat.{max u v w} R')).truncGE (-1)).obj
          (derivedBaseChange.obj K) ⟶
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, max v (max u w)} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L),
        ((DerivedCategory.TStructure.t (C := ModuleCat.{max u v w} R')).truncGEπ (-1)).app
          (derivedBaseChange.obj K) ≫ f = derivedBaseChange.map e.inv ≫ comparison.app L ∧
        IsIso f := by
  let : (ModuleCat.extendScalars.{u, v, max v (max u w)} φ).IsLeftAdjoint :=
    ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u w} φ
  intro K L e hK hL hflat LF α instLF
  let F := ModuleCat.extendScalars.{u, v, max v (max u w)} φ
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v w} R')
  have : HasExactColimitsOfShape ℕ (ModuleCat.{max u v w} R) :=
    hasExactColimitsOfShape_nat_moduleCat
  have : HasExactColimitsOfShape ℕ (ModuleCat.{max u v w} R') :=
    hasExactColimitsOfShape_nat_moduleCat
  have hLLE : L.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hL i (by omega) (by omega)
  let Pprop := isProjective (ModuleCat.{max u v w} R)
  let : Pprop.ContainsZero := ⟨0, isZero_zero _, inferInstance⟩
  obtain ⟨P, f, _, hq, hproj, hPLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pprop
      (fun X => ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩) 0).1 L
  have (n : ℤ) : Projective (P.X n) := hproj n
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P 0
  have : IsIso (α.app P) := isIso_comparison_of_isKProjective F LF α P
  have hf : IsIso ((t.truncGE (-1)).map
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f))) :=
    isIso_truncGE_map_extendScalars_of_quasiIso φ f 0
  have hα : IsIso ((t.truncGE (-1)).map (α.app L)) := by
    have hn := congrArg (t.truncGE (-1)).map (α.naturality f)
    simp only [Functor.map_comp, Functor.comp_map] at hn
    exact IsIso.of_isIso_fac_left hn
  have hge : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up ℤ)).obj L) (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => F.map_isZero (hL i (by omega) (by omega))
  have hGE : t.IsGE (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L)) (-1) :=
    inferInstance
  have : IsIso ((t.truncGE (-1)).map (LF.map e.inv ≫ α.app L)) := by
    rw [Functor.map_comp]
    infer_instance
  exact exists_iso_truncGE_factorization (hY := hGE) t (LF.map e.inv ≫ α.app L) (-1)

end TwoTermComplex
