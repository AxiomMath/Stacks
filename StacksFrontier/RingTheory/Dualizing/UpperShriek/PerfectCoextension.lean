module

public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Tensor
public import StacksFrontier.Homology.Tor.DerivedTensorBoundedAbove
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Basic
import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext

/-!
# Upper boundedness of derived Hom along a perfect finite quotient

For a surjection of Noetherian rings whose target is perfect as a module over the source,
derived Hom from the target preserves bounded-above complexes and bounded-above complexes
with finite cohomology.

## Main results

* `Dualizing.derivedCoextendScalars_mem_minus` — preservation of `D⁻`.
* `Dualizing.derivedCoextendScalars_finiteCohomology` — preservation of finite cohomology;
  together with the preceding result this gives preservation of `D⁻_Coh`.

## Implementation notes

Perfectness of the target module is expressed by `StacksDraft.Perfect.IsPerfect` applied to its
degree-zero complex in the derived category after restriction of scalars. Coherence over a
Noetherian ring is expressed by finiteness of every cohomology module. The two components of
preservation of `D⁻_Coh` are stated separately. The module universe is independent of the
ring universe, as in `Dualizing.derivedHom`; `ULift A` places the target module in that
universe. The rings share the universe required by that functor.

## References

* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK), the
  perfect-quotient step in the proof of (2).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

/-- Over a Noetherian ring, a bounded-above complex with finite cohomology modules is
pseudo-coherent. -/
private lemma isPseudoCoherent_of_minus_finiteCohomology
    {P : Type u} [CommRing P] [IsNoetherianRing P]
    (K : DerivedCategory (ModuleCat.{max v u} P))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} P)).minus K)
    (hKcoh : ∀ i : ℤ, Module.Finite P
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) i).obj K)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
  have hbound : ∃ b : ℤ, ∀ i : ℤ, b < i →
      CategoryTheory.Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) i).obj K) := by
    obtain ⟨N, hN⟩ := (DerivedCategory.minus_iff K).mp hK
    exact ⟨N - 1, fun i hi => hN i (by omega)⟩
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    K 0 (ULift.{v} P)).2.1.2 ⟨hbound, hKcoh⟩

/-- A perfect complex is pseudo-coherent. -/
private lemma isPseudoCoherent_of_isPerfect
    {P : Type u} [CommRing P]
    (K : DerivedCategory (ModuleCat.{max v u} P))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
  ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).1.mp hK).1

/-- Transport of finiteness of a Hom module along the equivalence of derived categories
induced by the universe lift `P ≃+* ULift P`. -/
private lemma finite_hom_of_scalarLift
    {P : Type u} [CommRing P]
    (X Y : DerivedCategory (ModuleCat.{max v u} P))
    (hfin : Module.Finite (ULift.{v} P)
      (((StacksDraft.TorAmplitude.scalarLift.{u, v} (R := P)).mapDerivedCategory.obj X) ⟶
        ((StacksDraft.TorAmplitude.scalarLift.{u, v} (R := P)).mapDerivedCategory.obj Y))) :
    Module.Finite P (X ⟶ Y) := by
  let ρ : P →+* ULift.{v} P := ULift.ringEquiv.symm.toRingHom
  let σ : ULift.{v} P →+* P := ULift.ringEquiv.toRingHom
  let : Linear P (ModuleCat.{max u v} (ULift.{v} P)) :=
    { homModule := fun X Y => Module.compHom (X ⟶ Y) ρ
      smul_comp := by
        intro X Y Z r f g
        show (ρ r • f) ≫ g = ρ r • (f ≫ g)
        exact Linear.smul_comp _ _ _ _ _ _
      comp_smul := by
        intro X Y Z f r g
        show f ≫ (ρ r • g) = ρ r • (f ≫ g)
        exact Linear.comp_smul _ _ _ _ _ _ }
  let F₀ := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := P)
  let : F₀.Linear P := by
    constructor
    intro X Y f r
    apply ModuleCat.hom_ext
    ext x
    rfl
  let F := F₀.mapDerivedCategory
  let : F.IsEquivalence := inferInstance
  let : F.Full := inferInstance
  let : F.Faithful := inferInstance
  let : Linear P (DerivedCategory (ModuleCat.{max u v} (ULift.{v} P))) := inferInstance
  let : F.Linear P := inferInstance
  let H := F.obj X ⟶ F.obj Y
  let : Module (ULift.{v} P) H := inferInstance
  let : Module.Finite (ULift.{v} P) H := hfin
  let : Module P H := Module.compHom H ρ
  have hfin' : Module.Finite P H := by
    let f : H →ₛₗ[σ] H :=
      { toFun := id
        map_add' := by intro x y; rfl
        map_smul' := by
          intro r x
          show r • x = ρ (σ r) • x
          simp [ρ, σ] }
    exact Module.Finite.of_surjective (R := ULift.{v} P) (M := H) (P := H)
      (σ := σ) f (fun x => ⟨x, rfl⟩)
  let l : (X ⟶ Y) →ₗ[P] H :=
    { toFun := F.map
      map_add' := by intro f g; exact F.map_add
      map_smul' := by intro r f; exact Functor.Linear.map_smul (F := F) f r }
  let e := LinearEquiv.ofBijective l ⟨F.map_injective, F.map_surjective⟩
  let : Module.Finite P H := hfin'
  exact Module.Finite.equiv e.symm

/-- The derived tensor product agrees with the tensor functor of a derived Hom datum, computed
on a K-flat representative of the second argument. -/
private lemma derivedTensorProduct_iso_derivedHomData_tensor
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (eP : K ≅ DerivedCategory.Q.obj P) (eQ : L ≅ DerivedCategory.Q.obj Q)
    (hQ : Q.KFlat) :
    Nonempty ((CochainComplex.DerivedTensor.derivedTensorProduct L).obj K ≅
      d.tensor.obj (K, L)) := by
  have eQ' : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q) ≅ L :=
    (DerivedCategory.quotientCompQhIso _).app Q ≪≫ eQ.symm
  obtain ⟨e⟩ := (CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution
    L Q Q (𝟙 Q) hQ eQ').1
  exact ⟨(CochainComplex.DerivedTensor.derivedTensorProduct L).mapIso
      (eP ≪≫ ((DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
    e.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app (HomologicalComplex.tensorObj P Q) ≪≫
    (d.tensorIso P Q hQ).symm ≪≫ (d.tensor.mapIso (eP.prod eQ)).symm⟩

/-- A scalar multiple of the identity commutes with every morphism in a linear category. -/
private lemma smul_id_comp_comm {R : Type u} [CommRing R] {C : Type*} [Category C] [Preadditive C]
    [Linear R C] {X Y : C} (r : R) (e : X ⟶ Y) : (r • 𝟙 X) ≫ e = e ≫ (r • 𝟙 Y) := by
  rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Category.comp_id]

/-- The tensor functor of a derived Hom datum is linear in its second argument, on objects
coming from cochain complexes with the second one K-flat. -/
private lemma derivedHomData_tensor_map_smul_right_Q_obj
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (hQ : Q.KFlat) (r : R) :
    d.tensor.map (𝟙 (DerivedCategory.Q.obj P), r • (𝟙 (DerivedCategory.Q.obj Q))) =
      r • 𝟙 (d.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  have h := d.tensorIso_naturality (𝟙 P) (r • (𝟙 Q)) hQ hQ
  have ht : HomologicalComplex.tensorHom (𝟙 P) (r • (𝟙 Q)) =
      r • 𝟙 (HomologicalComplex.tensorObj P Q) := by
    ext1 n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    simp [HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.map_smul] at h
  have hpid : DerivedCategory.Q.map (𝟙 P) = 𝟙 (DerivedCategory.Q.obj P) :=
    DerivedCategory.Q.map_id _
  have hqid : DerivedCategory.Q.map (𝟙 Q) = 𝟙 (DerivedCategory.Q.obj Q) :=
    DerivedCategory.Q.map_id _
  rw [hpid, hqid] at h
  apply (cancel_mono (d.tensorIso P Q hQ).hom).1
  calc
    _ = (d.tensorIso P Q hQ).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom (𝟙 P) (r • (𝟙 Q))) := h
    _ = (r • (𝟙 (d.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))) ≫
        (d.tensorIso P Q hQ).hom := by
      rw [ht]
      rw [Functor.map_smul]
      have hqid : DerivedCategory.Q.map (𝟙 (HomologicalComplex.tensorObj P Q)) =
          𝟙 (DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q)) :=
        DerivedCategory.Q.map_id _
      rw [hqid]
      exact (smul_id_comp_comm r _).symm

/-- The tensor functor of a derived Hom datum sends a scalar multiple of the identity in its
second argument to the same scalar multiple of the identity. -/
private lemma derivedHomData_tensor_map_smul_right
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    (K L : DerivedCategory (ModuleCat.{u} R)) (r : R) :
    d.tensor.map (𝟙 K, r • (𝟙 L)) = r • 𝟙 (d.tensor.obj (K, L)) := by
  let K₀ := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, _, hp, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K₀
  have eK : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let L₀ := DerivedCategory.Q.objPreimage L
  obtain ⟨Q, q, hQ, _, hq, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution L₀
  have eL : DerivedCategory.Q.obj Q ≅ L :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso L
  let eT := d.tensor.mapIso (eK.prod eL)
  have hcomm : d.tensor.map (𝟙 (DerivedCategory.Q.obj P), r • (𝟙 (DerivedCategory.Q.obj Q))) ≫
      eT.hom = eT.hom ≫ d.tensor.map (𝟙 K, r • (𝟙 L)) := by
    dsimp [eT]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp [Linear.smul_comp, Linear.comp_smul]
  rw [derivedHomData_tensor_map_smul_right_Q_obj d P Q hQ r, smul_id_comp_comm] at hcomm
  exact ((cancel_epi eT.hom).1 hcomm).symm

/-- The tensor functor of a derived Hom datum sends a scalar multiple of the identity in its
first argument to the same scalar multiple of the identity. -/
private lemma derivedHomData_tensor_map_smul_left
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    (K L : DerivedCategory (ModuleCat.{u} R)) (r : R) :
    d.tensor.map (r • (𝟙 K), 𝟙 L) = r • 𝟙 (d.tensor.obj (K, L)) := by
  have h := d.tensorSwap_naturality (r • (𝟙 K)) (𝟙 L)
  rw [derivedHomData_tensor_map_smul_right d L K r] at h
  rw [← smul_id_comp_comm] at h
  exact (cancel_mono (d.tensorSwap K L).hom).1 h

/-- Homology of complexes of modules is a linear functor. -/
private noncomputable instance homologyFunctor_linear
    {R : Type u} [CommRing R] (i : ℤ) :
    Functor.Linear R
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i) where
  map_smul f r := by
    change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).map
        (r • f)) = _
    rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℤ) i).map (r • f) = r •
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
          (ComplexShape.up ℤ) i).map f by rfl]
    apply CategoryTheory.ShortComplex.homologyMap_smul

/-- Homology sends a scalar multiple of the identity of a cochain complex to the same scalar
multiple of the identity. -/
private lemma homologyMap_smul_id
    {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : ℤ) (r : R) :
    HomologicalComplex.homologyMap (r • 𝟙 C) i = r • 𝟙
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj C) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  let : F.Linear R := homologyFunctor_linear i
  show F.map (r • 𝟙 C) = r • 𝟙 (F.obj C)
  rw [Functor.Linear.map_smul (F := F) (𝟙 C) r, F.map_id]

/-- The homology functors on the derived category send a scalar multiple of the identity to the
same scalar multiple of the identity. -/
private lemma derivedHomologyFunctor_map_smul_id
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (i : ℤ) (K : DerivedCategory (ModuleCat.{u} R)) (r : R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map (r • 𝟙 K) =
      r • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) i
  let K₀ := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  have h₀ : H.map (r • 𝟙 (DerivedCategory.Q.obj K₀)) =
      r • 𝟙 (H.obj (DerivedCategory.Q.obj K₀)) := by
    have hQ : DerivedCategory.Q.map (r • (𝟙 K₀)) =
        r • 𝟙 (DerivedCategory.Q.obj K₀) := by simp
    rw [← hQ]
    apply (cancel_mono ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} R) i).hom.app K₀)).1
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality, homologyMap_smul_id]
    exact (smul_id_comp_comm r _).symm
  have h := congrArg H.map (smul_id_comp_comm r e.hom)
  rw [Functor.map_comp, Functor.map_comp, h₀, smul_id_comp_comm] at h
  exact (cancel_epi (H.map e.hom)).1 h.symm

/-- Over a Noetherian ring, morphisms from a perfect complex to a pseudo-coherent complex form
a finite module. -/
private lemma finite_hom_of_perfect_pseudoCoherent
    {P : Type u} [CommRing P] [IsNoetherianRing P]
    (X Y : DerivedCategory (ModuleCat.{max v u} P))
    (hX : StacksDraft.Perfect.IsPerfect X)
    (hY : StacksDraft.PseudoCoherence.IsPseudoCoherent Y) :
    Module.Finite P (X ⟶ Y) := by
  let eRing : ULift.{v} P ≃+* P := ULift.ringEquiv
  let F := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := P)
  let X' := F.mapDerivedCategory.obj X
  let Y' := F.mapDerivedCategory.obj Y
  have hX' : StacksDraft.Perfect.IsPerfect X' :=
    StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv eRing X hX
  have hY' : StacksDraft.PseudoCoherence.IsPseudoCoherent Y' :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv eRing Y).2.mp hY
  let D : StacksDraft.DerivedHom.DerivedHomData (ULift.{v} P) :=
    StacksDraft.Perfect.derivedHomData.{u, v} (R := P)
  let : IsNoetherianRing (ULift.{v} P) :=
    isNoetherianRing_of_ringEquiv P eRing.symm
  let DX : DerivedCategory (ModuleCat.{max v u} (ULift.{v} P)) :=
    StacksDraft.Perfect.derivedDual.{u, v} X'
  let hDuality := StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos X' hX'
  have hDX : StacksDraft.PseudoCoherence.IsPseudoCoherent DX :=
    isPseudoCoherent_of_isPerfect DX hDuality.dual_isPerfect
  let Q₀ := DerivedCategory.Q.objPreimage DX
  obtain ⟨Q, q, hQ, _, hq, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution Q₀
  have hqIso : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  have eQ : DX ≅ DerivedCategory.Q.obj Q :=
    (DerivedCategory.Q.objObjPreimageIso DX).symm ≪≫ (asIso (DerivedCategory.Q.map q)).symm
  let Yi := Y'
  have hYi : StacksDraft.PseudoCoherence.IsPseudoCoherent Yi := hY'
  let P₀ := DerivedCategory.Q.objPreimage Yi
  have eP : Yi ≅ DerivedCategory.Q.obj P₀ :=
    (DerivedCategory.Q.objObjPreimageIso Yi).symm
  obtain ⟨eT⟩ := derivedTensorProduct_iso_derivedHomData_tensor.{max u v}
    D Yi DX P₀ Q eP eQ hQ
  have hTensorPC : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((CochainComplex.DerivedTensor.derivedTensorProduct DX).obj Yi) :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_derivedTensorProduct_largeUniverse
      (R := ULift.{v} P) Yi DX).2 hYi hDX
  let H := DerivedCategory.homologyFunctor
    (ModuleCat.{max v u} (ULift.{v} P)) 0
  have hHfinite : Module.Finite (ULift.{v} P) (H.obj
      ((CochainComplex.DerivedTensor.derivedTensorProduct DX).obj Yi)) :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      ((CochainComplex.DerivedTensor.derivedTensorProduct DX).obj Yi) 0
        (ULift.{0} (ULift.{v} P))).2.1.1 hTensorPC).2 0
  let eTensorH := CategoryTheory.Iso.toLinearEquiv (H.mapIso eT)
  let : Module.Finite (ULift.{v} P)
      (H.obj ((CochainComplex.DerivedTensor.derivedTensorProduct DX).obj Yi)) := hHfinite
  have hDfinite : Module.Finite (ULift.{v} P)
      (H.obj (D.tensor.obj (Yi, DX))) := Module.Finite.equiv eTensorH
  obtain ⟨eExt, hExtNat⟩ := hDuality.exists_extZeroEquiv
  let source := (H.obj (D.tensor.obj (Yi, DX)) : Type (max u v))
  let target := (X' ⟶ Yi)
  let eAdd : source ≃+ target := eExt Yi
  let l : source →ₗ[ULift.{v} P] target :=
    { toFun := eAdd
      map_add' := eAdd.map_add
      map_smul' := by
        intro r a
        have hm := hExtNat (r • (𝟙 Yi)) a
        have hmap : H.map (D.tensor.map (r • (𝟙 Yi), 𝟙 DX)) a = r • a := by
          rw [derivedHomData_tensor_map_smul_left D Yi DX r, derivedHomologyFunctor_map_smul_id]
          rfl
        rw [hmap] at hm
        simpa [target, Linear.comp_smul] using hm }
  let eLinear := LinearEquiv.ofBijective l ⟨eAdd.injective, eAdd.surjective⟩
  let : Module.Finite (ULift.{v} P) (H.obj (D.tensor.obj (Yi, DX))) := hDfinite
  have hTargetfinite : Module.Finite (ULift.{v} P) target := Module.Finite.equiv eLinear
  exact finite_hom_of_scalarLift X Y (by simpa [X', Y', F, target] using hTargetfinite)

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

/-- **The tensor functor of a derived Hom datum adds upper bounds**, with no lower bound on
either factor. -/
private lemma derivedHomData_tensor_isLE
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    (K L : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] :
    (d.tensor.obj (K, L)).IsLE (a + b) :=
  CochainComplex.DerivedTensor.isLE_of_kFlatComparison.{u, u}
    (d.tensor.obj (K, L)) K L a b
    fun P Q eP eQ _ hQ => ⟨d.tensor.mapIso (eP.prod eQ) ≪≫ d.tensorIso P Q hQ⟩

/-- Derived Hom from a perfect finite quotient preserves bounded-above complexes, and preserves
finiteness of all cohomology modules. -/
private lemma derivedCoextendScalars_bounds_and_finiteCohomology
    {P A : Type u} [CommRing P] [CommRing A]
    [IsNoetherianRing P] [IsNoetherianRing A]
    (f : P →+* A) (_hf : Function.Surjective f)
    (hperfect : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} P) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{v} A))))))
    (K : DerivedCategory (ModuleCat.{max v u} P))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} P)).minus K) :
    (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} A)).minus
        ((derivedHom.{u, v, u} f).obj K) ∧
      ((∀ i : ℤ,
          Module.Finite P ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) i).obj K)) →
        ∀ i : ℤ, Module.Finite A
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
            ((derivedHom.{u, v, u} f).obj K))) := by
  let M : ModuleCat.{max v u} P :=
    (ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{v} A))
  let X : DerivedCategory (ModuleCat.{max v u} P) :=
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj M
  let eX := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} P) 0).app M
  have hperfectX : StacksDraft.Perfect.IsPerfect X :=
    StacksDraft.Perfect.isPerfect_of_iso eX.symm hperfect
  let F := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := P)
  let X' := F.mapDerivedCategory.obj X
  let eRing : ULift.{v} P ≃+* P := ULift.ringEquiv
  have hX' : StacksDraft.Perfect.IsPerfect X' :=
    StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv eRing X hperfectX
  let Fd := F.mapDerivedCategory
  let D : StacksDraft.DerivedHom.DerivedHomData (ULift.{v} P) :=
    StacksDraft.Perfect.derivedHomData.{u, v} (R := P)
  let : IsNoetherianRing (ULift.{v} P) :=
    isNoetherianRing_of_ringEquiv P eRing.symm
  let DX : DerivedCategory (ModuleCat.{max v u} (ULift.{v} P)) :=
    StacksDraft.Perfect.derivedDual.{u, v} X'
  let hDuality := StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos X' hX'
  have hDX : StacksDraft.PseudoCoherence.IsPseudoCoherent DX :=
    isPseudoCoherent_of_isPerfect DX hDuality.dual_isPerfect
  obtain ⟨E, hE, ⟨eDX⟩⟩ := hDX
  obtain ⟨a, ha⟩ := hE.upperBound
  have hEisLE : CochainComplex.IsLE E a := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    let : CochainComplex.IsStrictlyLE E a := ha
    exact ShortComplex.exact_of_isZero_X₂ _ (E.isZero_of_isStrictlyLE a i hi)
  have hDXle : DX.IsLE a := by
    have : (DerivedCategory.Q.obj E).IsLE a := (DerivedCategory.isLE_Q_obj_iff E a).2 hEisLE
    exact DerivedCategory.TStructure.t.isLE_of_iso eDX a
  let RF := derivedHom.{u, v, u} f
  let α := (coextendScalarsToDerivedCategory f).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{max v u} P) (.up ℤ))
  let hComparison := derivedCoextendScalarsHomologyLinearEquivExt f RF α
  obtain ⟨b, hb⟩ := hK
  have hKle : K.IsLE b := hb
  have : Fd.IsEquivalence := inferInstance
  have : Fd.Full := inferInstance
  have : Fd.Faithful := inferInstance
  have hExtZero (i : ℤ) (hi : a + b < i) :
      Subsingleton (DerivedCategory.Ext X K i) := by
    let Y := Fd.obj (K⟦i⟧)
    have hYle : Y.IsLE (b - i) := by
      have hKi : (K⟦i⟧).IsLE (b - i) :=
        DerivedCategory.TStructure.t.isLE_shift K b i (b - i) (by omega)
      rw [DerivedCategory.isLE_iff]
      intro j hj
      exact (F.map_isZero (DerivedCategory.isZero_of_isLE (K⟦i⟧) (b - i) j hj)).of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F j).app (K⟦i⟧))
    let H := DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} (ULift.{v} P)) 0
    have hTensorLE : (D.tensor.obj (Y, DX)).IsLE (b - i + a) :=
      derivedHomData_tensor_isLE D Y DX (b - i) a
    have hHzero : IsZero (H.obj (D.tensor.obj (Y, DX))) :=
      DerivedCategory.isZero_of_isLE (D.tensor.obj (Y, DX)) (b - i + a) 0 (by omega)
    obtain ⟨eExt, _⟩ := hDuality.exists_extZeroEquiv
    let eAdd : (H.obj (D.tensor.obj (Y, DX)) : Type (max v u)) ≃+
        (X' ⟶ Y) := eExt Y
    have hHomSub : Subsingleton (X' ⟶ Y) := by
      let : Subsingleton (H.obj (D.tensor.obj (Y, DX))) :=
        ModuleCat.isZero_iff_subsingleton.mp hHzero
      refine ⟨fun x y => ?_⟩
      simpa using congrArg eAdd (Subsingleton.elim (eAdd.symm x) (eAdd.symm y))
    exact ⟨fun x y => Fd.map_injective (hHomSub.elim (Fd.map x) (Fd.map y))⟩
  refine ⟨?_, ?_⟩
  · refine ⟨a + b, (DerivedCategory.isLE_iff (RF.obj K) (a + b)).2 fun i hi => ?_⟩
    let e := hComparison.linearEquiv K i
    have hzero : Subsingleton
        ((ModuleCat.restrictScalars f).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj (RF.obj K))) :=
      ⟨fun x y => e.injective ((hExtZero i hi).elim (e x) (e y))⟩
    exact ModuleCat.isZero_iff_subsingleton.mpr hzero
  · intro hKcoh i
    have hminusShift : (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} P)).minus
        (K⟦i⟧) :=
      (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} P)).minus.le_shift i K ⟨b, hb⟩
    have hcohShift : ∀ j : ℤ, Module.Finite P
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) j).obj (K⟦i⟧)) := by
      intro j
      let eH := (StacksDraft.PseudoCoherence.homologyFunctorShiftIso i j).app K
      let : Module.Finite P
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) (i + j)).obj K) :=
        hKcoh (i + j)
      exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv eH).symm
    have hKshiftPC : StacksDraft.PseudoCoherence.IsPseudoCoherent (K⟦i⟧) :=
      isPseudoCoherent_of_minus_finiteCohomology (K⟦i⟧) hminusShift hcohShift
    have hExtFinite : Module.Finite P (DerivedCategory.Ext X K i) :=
      finite_hom_of_perfect_pseudoCoherent X (K⟦i⟧) hperfectX hKshiftPC
    let e := hComparison.linearEquiv K i
    let H := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj (RF.obj K)
    have : Module.Finite P ((ModuleCat.restrictScalars f).obj H) := Module.Finite.equiv e.symm
    exact finite_of_restrictScalars_finite f H

/-- Derived Hom from a perfect finite quotient carries bounded-above complexes to
bounded-above complexes. -/
theorem derivedCoextendScalars_mem_minus
    {P A : Type u} [CommRing P] [CommRing A]
    [IsNoetherianRing P] [IsNoetherianRing A]
    (f : P →+* A) (hf : Function.Surjective f)
    (hperfect : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} P) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{v} A))))))
    (K : DerivedCategory (ModuleCat.{max v u} P))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} P)).minus K) :
    (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} A)).minus
      ((derivedHom.{u, v, u} f).obj K) :=
  (derivedCoextendScalars_bounds_and_finiteCohomology f hf hperfect K hK).1

/-- Derived Hom from a perfect finite quotient carries complexes with finite cohomology to
complexes with finite cohomology. In conjunction with
`Dualizing.derivedCoextendScalars_mem_minus`, this is preservation of `D⁻_Coh`. -/
theorem derivedCoextendScalars_finiteCohomology
    {P A : Type u} [CommRing P] [CommRing A]
    [IsNoetherianRing P] [IsNoetherianRing A]
    (f : P →+* A) (hf : Function.Surjective f)
    (hperfect : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} P) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{v} A))))))
    (K : DerivedCategory (ModuleCat.{max v u} P))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{max v u} P)).minus K)
    (hKcoh : ∀ i : ℤ,
      Module.Finite P ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) i).obj K)) :
    ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
        ((derivedHom.{u, v, u} f).obj K)) :=
  (derivedCoextendScalars_bounds_and_finiteCohomology f hf hperfect K hK).2 hKcoh

end

end Dualizing
