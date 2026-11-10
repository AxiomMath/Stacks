module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.RingTheory.Dualizing.Complex

/-!
# Finiteness and injective dimension under polynomial base change

Auxiliary results for `Dualizing.polynomialBaseChange_isDualizingComplex`: dualizing complexes
are stable under isomorphism, and finite cohomology and finite injective dimension are preserved
by the exact functors (universe lifting, restriction of scalars along a ring equivalence and
extension of scalars to `A[X]`) used to define `Dualizing.polynomialBaseChange`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace Dualizing

universe u v w x

private theorem isDualizingComplex_of_iso {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K L : DerivedCategory (ModuleCat.{v} A)} (e : K ≅ L)
    (hK : IsDualizingComplex K) : IsDualizingComplex L := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hK.finiteInjectiveDimension with ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩
    exact ⟨a, b, I, hge, hle, hinj, ⟨e.symm ≪≫ eI⟩⟩
  · intro i
    let : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) :=
      hK.finiteCohomology i
    exact Module.Finite.equiv
      (((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso e).toLinearEquiv)
  · intro I hI hinj hbound
    rcases hI with ⟨eI⟩
    exact hK.homothetyQuasiIso I ⟨eI ≪≫ e.symm⟩ hinj hbound

private theorem pseudoCoherent_of_finiteInjectiveDimension_finiteCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hI : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K)
    (hH : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
  obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hI
  have : K.IsLE b := ⟨I, eI, hle⟩
  exact ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      K 0 PUnit).2.1).mpr
    ⟨⟨b, fun i hi => DerivedCategory.isZero_of_isLE K b i hi⟩,
      hH⟩

private theorem isGE_of_finiteInjectiveDimension
    {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hI : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    ∃ a : ℤ, K.IsGE a := by
  obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hI
  exact ⟨a, I, eI, hge⟩

private theorem cochainMap_bijective
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{x} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (I J : CochainComplex C ℤ) (n : ℤ) :
    Function.Bijective (fun z : CochainComplex.HomComplex.Cochain I J n => z.map F) := by
  constructor
  · intro z z' h
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply F.map_injective
    simpa only [CochainComplex.HomComplex.Cochain.map_v] using
      congrArg (fun t : CochainComplex.HomComplex.Cochain
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) n => t.v p q hpq) h
  · intro z
    refine ⟨CochainComplex.HomComplex.Cochain.mk
      (fun p q hpq => F.preimage (z.v p q hpq)), ?_⟩
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    simp only [CochainComplex.HomComplex.Cochain.map_v,
      CochainComplex.HomComplex.Cochain.mk_v, F.map_preimage]

private noncomputable def homComplexMap
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{v} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (I J : CochainComplex C ℤ) :
    CochainComplex.HomComplex I J ⟶ CochainComplex.HomComplex
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z => z.map F
      map_zero' := by simp
      map_add' := fun z z' => CochainComplex.HomComplex.Cochain.map_add z z' F }
  comm' n m _ := by
    ext z
    exact CochainComplex.HomComplex.δ_map n m z F

private theorem isIso_homComplexMap
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{v} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (I J : CochainComplex C ℤ) : IsIso (homComplexMap F I J) := by
  have (n : ℤ) : IsIso ((homComplexMap F I J).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (cochainMap_bijective F I J n)
  exact HomologicalComplex.Hom.isIso_of_components _

private noncomputable def homComplexMapLift
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{max v x} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (I J : CochainComplex C ℤ) :
    ((AddCommGrpCat.uliftFunctor.{x, v}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.HomComplex I J) ⟶
      CochainComplex.HomComplex
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z => z.down.map F
      map_zero' := CochainComplex.HomComplex.Cochain.map_zero I J n F
      map_add' := fun z z' =>
        CochainComplex.HomComplex.Cochain.map_add z.down z'.down F }
  comm' n m _ := by
    ext z
    exact CochainComplex.HomComplex.δ_map n m z.down F

private theorem isIso_homComplexMapLift
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{max v x} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (I J : CochainComplex C ℤ) : IsIso (homComplexMapLift F I J) := by
  have (n : ℤ) : IsIso ((homComplexMapLift F I J).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((cochainMap_bijective F I J n).comp Equiv.ulift.bijective)
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem finiteCohomology_mapDerivedCategory
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (F : ModuleCat.{w} R ⥤ ModuleCat.{x} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : ModuleCat.{w} R, Module.Finite R M → Module.Finite S (F.obj M))
    (K : DerivedCategory (ModuleCat.{w} R))
    (hK : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K)) :
    ∀ i : ℤ, Module.Finite S
      ((DerivedCategory.homologyFunctor (ModuleCat.{x} S) i).obj (F.mapDerivedCategory.obj K)) := by
  intro i
  let e := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app K
  have hfinite : Module.Finite S (F.obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K)) := hF _ (hK i)
  exact (Module.Finite.equiv_iff e.toLinearEquiv).mpr hfinite

theorem finiteInjectiveDimension_mapDerivedCategory
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{x} S]
    (F : ModuleCat.{w} R ⥤ ModuleCat.{x} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ (M : ModuleCat.{w} R), Injective M →
      ∃ n : ℕ, HasInjectiveDimensionLE (F.obj M) n)
    (K : DerivedCategory (ModuleCat.{w} R))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension (F.mapDerivedCategory.obj K) := by
  rcases hK with ⟨a, b, I, hGE, hLE, hI, ⟨e⟩⟩
  let L : CochainComplex (ModuleCat.{x} S) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hGE' : L.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact F.map_isZero ((CochainComplex.isStrictlyGE_iff I a).mp hGE i hi)
  have hLE' : L.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero ((CochainComplex.isStrictlyLE_iff I b).mp hLE i hi)
  have hL : ∀ i : ℤ, ∃ n : ℕ, HasInjectiveDimensionLE (L.X i) n := by
    intro i
    have hi : Injective (I.X i) := hI i
    obtain ⟨n, hn⟩ := hF (ModuleCat.of R (I.X i)) hi
    refine ⟨n, ?_⟩
    simpa [L] using hn
  have hbound : Nonempty (DerivedCategory.Q.obj L ≅ F.mapDerivedCategory.obj K) :=
    ⟨(F.mapDerivedCategoryFactors.app I).symm ≪≫ F.mapDerivedCategory.mapIso e.symm⟩
  exact (StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_of_bounded
    (F.mapDerivedCategory.obj K)).2 L hbound ⟨a, b, hGE', hLE'⟩ hL

private theorem finite_tensorProduct_left {R S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] (M : Type w) [AddCommGroup M] [Module R M]
    (hM : Module.Finite R M) : Module.Finite S (TensorProduct R S M) := by
  classical
  let : Module.Finite R M := hM
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := Algebra.TensorProduct.equivPiOfFiniteBasis S (Pi.basisFun R (Fin n))
  let g := f.baseChange S
  have hg : Function.Surjective g := LinearMap.baseChange_surjective S hf
  exact Module.Finite.of_surjective (g.comp e.symm.toLinearMap)
    (hg.comp e.symm.surjective)

private noncomputable def polynomialExtensionModuleEquiv
    {R : Type w} [CommRing R] (M : ModuleCat.{w} R) :
    (ModuleCat.extendScalars.{w, w, w} (algebraMap R (Polynomial R))).obj M ≃ₗ[
      Polynomial R] TensorProduct R (Polynomial R) M := by
  let f : R →+* Polynomial R := algebraMap R (Polynomial R)
  have hcomm : SMulCommClass R (Polynomial R)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of (Polynomial R) (Polynomial R))) :=
    ⟨fun r s t ↦ mul_left_comm (algebraMap R (Polynomial R) r) s t⟩
  let e : (ModuleCat.restrictScalars f).obj
      (ModuleCat.of (Polynomial R) (Polynomial R)) ≃ₗ[R] Polynomial R :=
    { AddEquiv.refl (Polynomial R) with
      map_smul' := fun r s ↦ (Algebra.smul_def (R := R) (A := Polynomial R) r s).symm }
  let e' : (ModuleCat.extendScalars f).obj M ≃+ TensorProduct R (Polynomial R) M :=
    (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv
  let l : (ModuleCat.extendScalars f).obj M ≃ₗ[Polynomial R]
      TensorProduct R (Polynomial R) M :=
    { e' with
      map_smul' := by
        change ∀ (s : Polynomial R) (z : (ModuleCat.extendScalars f).obj M),
          e' (s • z) = s • e' z
        intro s z
        -- `rw`/`simp` cannot abstract over the carrier of `(extendScalars f).obj M`, which is
        -- only definitionally a tensor product, so each step is taken in term mode instead.
        have hmap : ∀ {x y : (ModuleCat.extendScalars f).obj M}, x = y → e' x = e' y :=
          fun h => congrArg (fun w : (ModuleCat.extendScalars f).obj M => e' w) h
        have hpost : ∀ {x y : TensorProduct R (Polynomial R) M}, x = y → s • x = s • y :=
          fun h => congrArg (fun w : TensorProduct R (Polynomial R) M => s • w) h
        induction z using TensorProduct.inductionOn with
        | tmul t m =>
            have he : e (s • t) = s • e t := rfl
            calc
              e' (s • (t ⊗ₜ[R] m : (ModuleCat.extendScalars f).obj M))
                  = e' ((s • t) ⊗ₜ[R] m) := hmap (TensorProduct.smul_tmul' s t m)
              _ = e (s • t) ⊗ₜ[R] m :=
                  TensorProduct.congr_tmul e (LinearEquiv.refl R M) (s • t) m
              _ = (s • e t) ⊗ₜ[R] m :=
                  congrArg (fun w : Polynomial R => w ⊗ₜ[R] m) he
              _ = s • (e t ⊗ₜ[R] m) := (TensorProduct.smul_tmul' s (e t) m).symm
              _ = s • e' (t ⊗ₜ[R] m) :=
                  hpost (TensorProduct.congr_tmul e (LinearEquiv.refl R M) t m).symm
        | add z z' hz hz' =>
            calc
              e' (s • (z + z')) = e' (s • z + s • z') := hmap (smul_add s z z')
              _ = e' (s • z) + e' (s • z') := e'.map_add _ _
              _ = s • e' z + e' (s • z') :=
                  congrArg (fun w : TensorProduct R (Polynomial R) M => w + e' (s • z')) hz
              _ = s • e' z + s • e' z' :=
                  congrArg (fun w : TensorProduct R (Polynomial R) M => s • e' z + w) hz'
              _ = s • (e' z + e' z') := (smul_add s (e' z) (e' z')).symm
              _ = s • e' (z + z') := hpost (e'.map_add z z').symm }
  exact l

private theorem finiteInjectiveDimension_polynomialExtension
    {R : Type w} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{w} R))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    let f : R →+* Polynomial R := Polynomial.C
    let F := ModuleCat.extendScalars.{w, w, w} f
    let hf : f.Flat := by
      rw [show f = algebraMap R (Polynomial R) from rfl, RingHom.flat_algebraMap_iff]
      infer_instance
    letI : PreservesFiniteLimits F :=
      StacksDraft.TorAmplitude.preservesFiniteLimits_extendScalars hf
    letI : PreservesFiniteColimits F := inferInstance
    letI : F.Additive := StacksDraft.TorAmplitude.additive_extendScalars hf
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      (F.mapDerivedCategory.obj K) := by
  intro f F hf
  let : PreservesFiniteLimits F := StacksDraft.TorAmplitude.preservesFiniteLimits_extendScalars hf
  let : PreservesFiniteColimits F := inferInstance
  let : F.Additive := StacksDraft.TorAmplitude.additive_extendScalars hf
  have hF : ∀ (M : ModuleCat.{w} R), Injective M →
      ∃ n : ℕ, HasInjectiveDimensionLE (F.obj M) n := by
    intro M hM
    let : Module.Injective R M := Module.injective_module_of_injective_object R M
    refine ⟨1, ?_⟩
    let : Algebra R (Polynomial R) := f.toAlgebra
    exact (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv
      (polynomialExtensionModuleEquiv M) 1).mpr
      (Module.tensorProduct_polynomial_hasInjectiveDimensionLE
        (A := R) (E := (M : Type w)))
  exact finiteInjectiveDimension_mapDerivedCategory F hF K hK

private abbrev restrictScalarsLinearEquiv
    {R : Type u} {S : Type v} [Ring R] [Ring S] (e : S ≃+* R)
    (M : ModuleCat R) :
    LinearEquiv (σ' := (e : S →+* R)) (e.symm : R →+* S) M
    ((ModuleCat.restrictScalars e.toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = e (e.symm r) • x
    rw [e.apply_symm_apply]

private theorem finite_restrictScalars_of_ringEquiv
    {R : Type u} {S : Type v} [Ring R] [Ring S] (e : S ≃+* R)
    (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.restrictScalars e.toRingHom).obj M) :=
  Module.Finite.of_surjective (restrictScalarsLinearEquiv e M).toLinearMap
    (restrictScalarsLinearEquiv e M).surjective

end Dualizing
