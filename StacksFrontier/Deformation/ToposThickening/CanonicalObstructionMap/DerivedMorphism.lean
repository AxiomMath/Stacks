module

public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.Curvature
import all StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.FreeDifferentialLift
import all StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.Curvature

/-!
# The canonical obstruction morphism in the derived category

The comparison of the kernel tensor complex with the derived tensor product, the morphism of
`D(R)` represented by a lifted differential square (`LiftedDifferentialCurvature.toDerived`), its
independence of the free representative and of the lift, the characterization
`IsCanonicalObstructionMap`, the existence and uniqueness theorem, and `canonicalObstructionMap`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Deformation.Obstruction

variable {R' R : Type u} [CommRing R'] [CommRing R]

open CategoryTheory.MonoidalCategory HomologicalComplex CochainComplex.DerivedTensor

/-- The comparison of the ordinary kernel tensor complex with the derived tensor product.
It is normalized by the library's comparison on K-flat complexes. -/
noncomputable abbrev LiftedDifferentialCurvature.tensorComparison
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L) :
    DerivedCategory.Q.obj (P ⊗ kernelComplex f hf) ⟶
      ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).obj
        (squareZeroKernelObject f hf) := by
  letI := c.tensorResolution_isIso
  exact inv (DerivedCategory.Q.map (𝟙 P ⊗ₘ c.kernelResolutionMap)) ≫
    ((canonicalDerivedTensorProduct R).comparison P c.kernelResolution
      c.isKFlat c.kernelResolution_isKFlat).inv ≫
    ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
      (DerivedCategory.Q.map c.kernelResolutionMap)

/-- The tensor comparison may be computed through any K-projective, K-flat complex `T` mapping
to the kernel complex: composing with `1_P ⊗ q` turns it into the K-flat comparison for `T`
followed by the functorial image of `q`. The resolution recorded by `c` plays no special role. -/
lemma LiftedDifferentialCurvature.tensorComparison_after_resolution
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) [T.IsKProjective] (hT : T.KFlat)
    (q : T ⟶ kernelComplex f hf) :
    DerivedCategory.Q.map (𝟙 P ⊗ₘ q) ≫ c.tensorComparison =
      ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).inv ≫
        ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map q) := by
  have := c.kernelResolution_quasiIso
  have := c.tensorResolution_isIso
  obtain ⟨a, ⟨ha⟩⟩ := (CochainComplex.IsKProjective.exists_lift_of_quasiIso
    c.kernelResolutionMap q).1
  have hq : DerivedCategory.Q.map (a ≫ c.kernelResolutionMap) = DerivedCategory.Q.map q :=
    derived_map_eq_of_homotopy _ _ ha
  have ht : DerivedCategory.Q.map (𝟙 P ⊗ₘ (a ≫ c.kernelResolutionMap)) =
      DerivedCategory.Q.map (𝟙 P ⊗ₘ q) :=
    derived_map_eq_of_homotopy _ _
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 P) ha (curriedTensor _) (ComplexShape.up ℤ))
  have hn := (canonicalDerivedTensorProduct R).comparison_naturality (𝟙 P) a
    c.isKFlat c.isKFlat hT c.kernelResolution_isKFlat
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at hn
  simp only [NatTrans.id_app, Category.id_comp] at hn
  have hn' : DerivedCategory.Q.map (𝟙 P ⊗ₘ a) ≫
      ((canonicalDerivedTensorProduct R).comparison P c.kernelResolution
        c.isKFlat c.kernelResolution_isKFlat).inv =
      ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).inv ≫
        ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map a) := by
    have hn' : ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map a) ≫
        ((canonicalDerivedTensorProduct R).comparison P c.kernelResolution
          c.isKFlat c.kernelResolution_isKFlat).hom =
        ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).hom ≫
          DerivedCategory.Q.map (𝟙 P ⊗ₘ a) := hn
    apply (cancel_epi ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hn']
    simp
  rw [← ht]
  have hc : 𝟙 P ⊗ₘ (a ≫ c.kernelResolutionMap) =
      (𝟙 P ⊗ₘ a) ≫ (𝟙 P ⊗ₘ c.kernelResolutionMap) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hc, CategoryTheory.Functor.map_comp]
  dsimp only [LiftedDifferentialCurvature.tensorComparison]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hn', Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, hq]

private lemma exists_projective_kernel_resolution
    (f : R' →+* R) (hf : Function.Surjective f) :
    ∃ (T : CochainComplex (ModuleCat.{u} R) ℤ) (q : T ⟶ kernelComplex f hf),
      T.IsKProjective ∧ T.KFlat ∧ QuasiIso q := by
  have : (kernelComplex f hf).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega)
  obtain ⟨T, b, q, hTb, hproj, hq⟩ := exists_projective_resolution (kernelComplex f hf) 0
  have := hTb
  have := hproj
  exact ⟨T, q, CochainComplex.isKProjective_of_projective T b,
    kFlat_of_isStrictlyLE_projective T b hproj, hq⟩

private lemma LiftedDifferentialCurvature.tensorComparison_natural
    {f : R' →+* R} {hf : Function.Surjective f}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : FreeDifferentialLift f P} {M : FreeDifferentialLift f Q}
    (c : LiftedDifferentialCurvature f hf P L) (d : LiftedDifferentialCurvature f hf Q M)
    (a : P ⟶ Q) :
    DerivedCategory.Q.map (a ⊗ₘ 𝟙 (kernelComplex f hf)) ≫ d.tensorComparison =
      c.tensorComparison ≫ ((canonicalDerivedTensorProductFunctor R).map
        (DerivedCategory.Q.map a)).app (squareZeroKernelObject f hf) := by
  obtain ⟨T, q, hTp, hT, hq⟩ := exists_projective_kernel_resolution f hf
  have := hTp
  have := hq
  have : QuasiIso (𝟙 P ⊗ₘ q) := quasiIso_tensorLeft_map P c.isKFlat q
  apply (cancel_epi (DerivedCategory.Q.map (𝟙 P ⊗ₘ q))).mp
  rw [← Category.assoc]
  have hc : (𝟙 P ⊗ₘ q) ≫ (a ⊗ₘ 𝟙 (kernelComplex f hf)) =
      (a ⊗ₘ 𝟙 T) ≫ (𝟙 Q ⊗ₘ q) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [← CategoryTheory.Functor.map_comp, hc, CategoryTheory.Functor.map_comp, Category.assoc,
    d.tensorComparison_after_resolution T hT q, ← Category.assoc,
    ← Category.assoc, c.tensorComparison_after_resolution T hT q]
  have hn := (canonicalDerivedTensorProduct R).comparison_naturality a (𝟙 T)
    c.isKFlat d.isKFlat hT hT
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at hn
  simp only [Category.id_comp] at hn
  have hn' : DerivedCategory.Q.map (a ⊗ₘ 𝟙 T) ≫
      ((canonicalDerivedTensorProduct R).comparison Q T d.isKFlat hT).inv =
      ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).inv ≫
        ((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj T) := by
    have hn2 : ((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj T) ≫
        ((canonicalDerivedTensorProduct R).comparison Q T d.isKFlat hT).hom =
        ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).hom ≫
          DerivedCategory.Q.map (a ⊗ₘ 𝟙 T) := hn
    apply (cancel_epi ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hn2]
    simp
  rw [hn', Category.assoc]
  simpa only [Category.assoc, squareZeroKernelObject, kernelComplex,
    DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    SingleFunctors.postcomp, CategoryTheory.Functor.comp_obj,
    CochainComplex.singleFunctors, CochainComplex.singleFunctor] using congrArg (fun k =>
    ((canonicalDerivedTensorProduct R).comparison P T c.isKFlat hT).inv ≫ k)
    (((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map a)).naturality
      (DerivedCategory.Q.map q)).symm

/-- The morphism represented by a lifted differential square, transported along a chosen
identification of the free complex with a derived object. -/
noncomputable abbrev LiftedDifferentialCurvature.toDerived
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L)
    {K : DerivedCategory (ModuleCat.{u} R)} (e : DerivedCategory.Q.obj P ≅ K) :
    K ⟶ (((canonicalDerivedTensorProductFunctor R).obj K).obj
      (squareZeroKernelObject f hf))⟦(2 : ℤ)⟧ :=
  e.inv ≫ DerivedCategory.Q.map c.hom ≫
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (P ⊗ kernelComplex f hf) ≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
      (c.tensorComparison ≫
        ((canonicalDerivedTensorProductFunctor R).map e.hom).app
          (squareZeroKernelObject f hf))

private noncomputable def derivedCurvature
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L) :
    DerivedCategory.Q.obj P ⟶
      (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).obj
        (squareZeroKernelObject f hf))⟦(2 : ℤ)⟧ :=
  DerivedCategory.Q.map c.hom ≫
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (P ⊗ kernelComplex f hf) ≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map c.tensorComparison

private lemma LiftedDifferentialCurvature.toDerived_formula
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L)
    {K : DerivedCategory (ModuleCat.{u} R)} (e : DerivedCategory.Q.obj P ≅ K) :
    c.toDerived e = e.inv ≫ derivedCurvature c ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        (((canonicalDerivedTensorProductFunctor R).map e.hom).app
          (squareZeroKernelObject f hf)) := by
  simp only [LiftedDifferentialCurvature.toDerived, derivedCurvature,
    CategoryTheory.Functor.map_comp, Category.assoc]

private lemma derivedCurvature_natural
    {f : R' →+* R} {hf : Function.Surjective f}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : FreeDifferentialLift f P} {M : FreeDifferentialLift f Q}
    (c : LiftedDifferentialCurvature f hf P L) (d : LiftedDifferentialCurvature f hf Q M)
    (hzero : (RingHom.ker f) ^ 2 = ⊥) (a : P ⟶ Q) :
    DerivedCategory.Q.map a ≫ derivedCurvature d = derivedCurvature c ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        (((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map a)).app
          (squareZeroKernelObject f hf)) := by
  obtain ⟨h⟩ := c.hom_natural_homotopy d hzero a
  have hh := derived_map_eq_of_homotopy _ _ h
  simp only [CategoryTheory.Functor.map_comp] at hh
  let b := a ⊗ₘ 𝟙 (kernelComplex f hf)
  have hs := (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.naturality b
  change DerivedCategory.Q.map ((shiftFunctor _ (2 : ℤ)).map b) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app _ =
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app _ ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map
        (DerivedCategory.Q.map b) at hs
  dsimp only [derivedCurvature]
  simp only [← Category.assoc]
  rw [hh]
  simp only [Category.assoc]
  rw [← Category.assoc (DerivedCategory.Q.map ((shiftFunctor _ (2 : ℤ)).map b)), hs]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, c.tensorComparison_natural d a,
    CategoryTheory.Functor.map_comp]

private lemma projective_Q_map_surjective
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] :
    Function.Surjective (DerivedCategory.Q.map : (P ⟶ Q) → _) := by
  intro g
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj Q)).surjective
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app P ≫ g ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app Q)
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective β
  refine ⟨a, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} R) a
  rw [hβ] at h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  exact ((cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app P)).1 h).symm

private lemma LiftedDifferentialCurvature.toDerived_independent
    {f : R' →+* R} {hf : Function.Surjective f}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKProjective]
    {L : FreeDifferentialLift f P} {M : FreeDifferentialLift f Q}
    (c : LiftedDifferentialCurvature f hf P L) (d : LiftedDifferentialCurvature f hf Q M)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    {K : DerivedCategory (ModuleCat.{u} R)}
    (e : DerivedCategory.Q.obj P ≅ K) (e' : DerivedCategory.Q.obj Q ≅ K) :
    c.toDerived e = d.toDerived e' := by
  obtain ⟨a, ha⟩ := projective_Q_map_surjective P Q (e.hom ≫ e'.inv)
  have hn := derivedCurvature_natural c d hzero a
  rw [c.toDerived_formula, d.toDerived_formula]
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← ha, hn]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [ha]
  have hcomp :
      ((canonicalDerivedTensorProductFunctor R).map (e.hom ≫ e'.inv)).app
          (squareZeroKernelObject f hf) ≫
        ((canonicalDerivedTensorProductFunctor R).map e'.hom).app
          (squareZeroKernelObject f hf) =
      ((canonicalDerivedTensorProductFunctor R).map e.hom).app
        (squareZeroKernelObject f hf) := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hcomp]

/-- The full lifted-differential characterization of the canonical obstruction.
Existence of a free lift makes the characterization nonvacuous; the last field requires
agreement for every free representative, lift, factorization, and kernel resolution. -/
structure IsCanonicalObstructionMap (f : R' →+* R) (hf : Function.Surjective f)
    (K : DerivedCategory (ModuleCat.{u} R))
    (ω : K ⟶ (((canonicalDerivedTensorProductFunctor R).obj K).obj
      (squareZeroKernelObject f hf))⟦(2 : ℤ)⟧) : Prop where
  exists_free_representative : ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ),
    P.IsStrictlyLE b ∧ (∀ n, Module.Free R (P.X n)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K)
  exists_lift (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (hfree : ∀ n, Module.Free R (P.X n)) : Nonempty (FreeDifferentialLift f P)
  exists_curvature (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
      (hbound : P.IsStrictlyLE b) (hfree : ∀ n, Module.Free R (P.X n))
      (L : FreeDifferentialLift f P) : Nonempty (LiftedDifferentialCurvature f hf P L)
  eq_curvature (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
      (hbound : P.IsStrictlyLE b) (hfree : ∀ n, Module.Free R (P.X n))
      (e : DerivedCategory.Q.obj P ≅ K) (L : FreeDifferentialLift f P)
      (c : LiftedDifferentialCurvature f hf P L) : ω = c.toDerived e

/-- There is a unique morphism represented by the squares of lifted differentials on every
bounded-above free representative, independently of the lifts and all comparison data. -/
@[stacks 0DYR "canonical_obstruction_map"]
theorem existsUnique_isCanonicalObstructionMap
    (f : R' →+* R) (hf : Function.Surjective f) (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K) :
    ∃! ω : K ⟶ (((canonicalDerivedTensorProductFunctor R).obj K).obj
      (squareZeroKernelObject f hf))⟦(2 : ℤ)⟧, IsCanonicalObstructionMap f hf K ω :=
  by
    classical
    obtain ⟨P, b, hb, hfree, ⟨e⟩⟩ := exists_free_bounded_representative K hK
    obtain ⟨L⟩ := exists_freeDifferentialLift f hf P hfree
    obtain ⟨c⟩ := exists_liftedDifferentialCurvature f hf hzero P b hb hfree L
    have := hb
    have : ∀ n, Projective (P.X n) := fun n => by
      have := hfree n
      infer_instance
    have := CochainComplex.isKProjective_of_projective P b
    refine ⟨c.toDerived e, ?_, fun ω hω => ?_⟩
    · exact {
        exists_free_representative := ⟨P, b, hb, hfree, ⟨e⟩⟩
        exists_lift := exists_freeDifferentialLift f hf
        exists_curvature := exists_liftedDifferentialCurvature f hf hzero
        eq_curvature := fun Q _ _ _ e' M d => c.toDerived_independent d hzero e e' }
    · exact hω.eq_curvature P b hb hfree e L c

/-- The canonical obstruction morphism, together with its lifted-differential specification. -/
noncomputable abbrev canonicalObstructionMap
    (f : R' →+* R) (hf : Function.Surjective f) (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K) :
    { ω : K ⟶ (((canonicalDerivedTensorProductFunctor R).obj K).obj
        (squareZeroKernelObject f hf))⟦(2 : ℤ)⟧ // IsCanonicalObstructionMap f hf K ω } :=
  ⟨(existsUnique_isCanonicalObstructionMap f hf hzero K hK).exists.choose,
    (existsUnique_isCanonicalObstructionMap f hf hzero K hK).exists.choose_spec⟩

end Deformation.Obstruction
