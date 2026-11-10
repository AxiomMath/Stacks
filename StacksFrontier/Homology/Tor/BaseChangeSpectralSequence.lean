module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksFrontier.Algebra.Homology.SpectralSequence.Tor
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.Tor.ChangeOfRingsSpectralSequence
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# The Tor spectral sequence after a flat base change

Let `A → B` and `A → A'` be maps of commutative rings and put `B' = B ⊗[A] A'`. If `B` and the
`B`-modules `M` and `N` are flat over `A`, there is a spectral sequence
`Torᴬᵢ(Torᴮⱼ(M, N), A') ⇒ Torᴮʳᵢ₊ⱼ(M', N')`, where `M'` and `N'` are obtained from `M` and `N`
by extension of scalars from `B` to `B'`.

## Main definitions

* `RingTheory.TorBaseChange.BaseChangedAlgebra` is the tensor-product algebra `B ⊗[A] A'`.
* `RingTheory.TorBaseChange.baseChange` extends a `B`-module to `B ⊗[A] A'`.
* `RingTheory.TorBaseChange.baseChangeFromBase` extends its underlying `A`-module to `A'`.

## Main results

* `RingTheory.TorBaseChange.exists_tor_base_change_spectral_sequence` gives the Tor spectral
  sequence associated to a flat base change square.

## Implementation notes

The spectral sequence is the one of
`CochainComplex.Tor.exists_spectral_sequences_tor_homology_and_terms`
(Tag 061Z), applied to the complex computing `Torᴮ(M, N)` and to the module `A'`. That complex is
`M ⊗[B] Q` for a projective resolution `Q` of `N`, restricted to `A`; flatness of `B`, `M` and `N`
over `A` makes its terms flat over `A`, hence the complex K-flat, which is what identifies the
abutment with `Tor` over `B'`.

The spectral sequence is taken in `A`-modules. Thus both its second page and its abutment are
displayed after restriction to `A`; the abutment retains the canonical module structure over
`B ⊗[A] A'` before that restriction. Extension of scalars from `B` realizes the source's canonical
identification `M ⊗[B] (B ⊗[A] A') ≅ M ⊗[A] A'`, which is `baseChangeRestrictLinearEquiv` below.
The `A'` in the second Tor argument is universe-lifted, hence canonically equivalent to the regular
`A'`-module. With the bidegree convention inherited from Tag 061Z, bidegree `(i, j)` on the second
page denotes `Torᴬⱼ(Torᴮᵢ(M, N), A')`.

## References

* [The Stacks Project, Tag 0620](https://stacks.math.columbia.edu/tag/0620)
* [The Stacks Project, Tag 061Z](https://stacks.math.columbia.edu/tag/061Z)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory.TorBaseChange

open CochainComplex.Tor.ChangeOfRingsSpectralSequence

universe u v

/-- The pushout algebra `B' = B ⊗[A] A'`. -/
public abbrev BaseChangedAlgebra (A B A' : Type u) [CommRing A] [CommRing B]
    [CommRing A'] [Algebra A B] [Algebra A A'] : Type u :=
  B ⊗[A] A'

/-- The canonical ring map `B → B ⊗[A] A'`. -/
public noncomputable abbrev baseChangeRingHom
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] :
    B →+* BaseChangedAlgebra A B A' :=
  (Algebra.TensorProduct.includeLeft :
    B →ₐ[A] BaseChangedAlgebra A B A').toRingHom

/-- A module regarded as an `A`-module through a map `A → B`. -/
public noncomputable abbrev restrictScalars
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{max u v} B) : ModuleCat.{max u v} A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj M

/-- Extension of a `B`-module to the base-changed algebra `B ⊗[A] A'`. -/
public noncomputable abbrev baseChange
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (M : ModuleCat.{max u v} B) :
    ModuleCat.{max u v} (BaseChangedAlgebra A B A') :=
  ModuleCat.of (BaseChangedAlgebra A B A')
    (BaseChangedAlgebra A B A' ⊗[B] M)

/-- Extension of the underlying `A`-module of a `B`-module to `A'`. -/
public noncomputable abbrev baseChangeFromBase
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (M : ModuleCat.{max u v} B) :
    ModuleCat.{max u v} A' :=
  ModuleCat.of A' (A' ⊗[A] (restrictScalars A B M))

/-- The regular module, lifted to the universe used for the other module carriers. -/
public noncomputable abbrev regularModule (R : Type u) [CommRing R] :
    ModuleCat.{max u v} R :=
  ModuleCat.of R (ULift.{v} R)

/-! ### The spectral sequence of a complex calibrated to compute `Tor` over `B` -/

private theorem spectralSequenceOfCalibratedComplex
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (M N : ModuleCat.{max u v} B)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (K.X i))
    (hhom : ∀ i : ℤ, K.homology (-i) ≅
      restrictScalars A B (@CochainComplex.Tor.TorInDegree.{u, v} B _ i M N))
    (habut : ∀ (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
      (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ) 0).obj
          (restrictScalars A A' (@regularModule.{u, v} A' _))),
      QuasiIso ε →
      (∀ i : ℤ, Module.Free A (P.X i)) →
      (∀ i : ℤ, 0 < i → IsZero (P.X i)) →
      ∀ n : ℤ,
      (HomologicalComplex.mapBifunctor K P (CochainComplex.Tor.moduleTensorBifunctor A)
        (ComplexShape.up ℤ)).homology (-n) ≅
        (ModuleCat.restrictScalars
          (algebraMap A (BaseChangedAlgebra A B A'))).obj
          (@CochainComplex.Tor.TorInDegree.{u, v} (BaseChangedAlgebra A B A') _ n
            (@baseChange.{u, v} A B A' _ _ _ _ _ M)
            (@baseChange.{u, v} A B A' _ _ _ _ _ N))) :
    ∃ (E : CochainComplex.Tor.FirstTorSpectralSequence (ModuleCat.{max u v} A))
      (_e₂ : ∀ i j : ℤ,
        (E.page 2).X (i, j) ≅
          @CochainComplex.Tor.TorInDegree.{u, v} A _ j
            (restrictScalars A B
              (@CochainComplex.Tor.TorInDegree.{u, v} B _ i M N))
            (restrictScalars A A' (@regularModule.{u, v} A' _))),
      CochainComplex.Tor.HomologicalSpectralSequenceAbutsTo E
        (fun n ↦
          (ModuleCat.restrictScalars
            (algebraMap A (BaseChangedAlgebra A B A'))).obj
            (@CochainComplex.Tor.TorInDegree.{u, v} (BaseChangedAlgebra A B A') _ n
              (@baseChange.{u, v} A B A' _ _ _ _ _ M)
              (@baseChange.{u, v} A B A' _ _ _ _ _ N))) := by
  let Z := restrictScalars A A' (@regularModule.{u, v} A' _)
  let U := ModuleCat.uliftFunctor.{max u v, max u v} A
  let K' := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  obtain ⟨P, ε, hε, hfree, hbounded, h0, hother,
    E, E', e₂, e₁, F, F', S, S', hF, hF', hbF, hbF', hS, hS', hd⟩ :=
      CochainComplex.Tor.exists_spectral_sequences_tor_homology_and_terms A K hK Z
  refine ⟨E, ?_, ?_⟩
  · intro i j
    exact e₂ i j ≪≫ torInDegreeIso A j
      (HomologicalComplex.homologyMapIso (uliftComplexIso A K) (-i) ≪≫ hhom i)
      (uliftModuleIso A Z)
  · let ε' := ε ≫
      (HomologicalComplex.single (ModuleCat.{max u v} A) (ComplexShape.up ℤ) 0).map
        (uliftModuleIso A Z).hom
    have : QuasiIso ε := hε
    have : QuasiIso ε' := inferInstance
    let T := HomologicalComplex.mapBifunctor K' P
      (CochainComplex.Tor.moduleTensorBifunctor A) (ComplexShape.up ℤ)
    let eT : T ≅ HomologicalComplex.mapBifunctor K P
        (CochainComplex.Tor.moduleTensorBifunctor A) (ComplexShape.up ℤ) :=
      (((CochainComplex.Tor.moduleTensorBifunctor A).map₂CochainComplex).mapIso
        (uliftComplexIso A K)).app P
    exact (S.abutsTo_homology hS).of_iso (fun n ↦
      HomologicalComplex.homologyMapIso eT (-n) ≪≫
        habut P ε' inferInstance hfree hbounded n)

/-! ### The complex computing `Tor` over `B`, restricted to `A` -/

private noncomputable def torResolutionComplex
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M N : ModuleCat.{max u v} B) :
    CochainComplex (ModuleCat.{max u v} A) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (((((CochainComplex.Tor.moduleTensorBifunctor B).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (ProjectiveResolution.of N).complex).extend
          ComplexShape.embeddingDownNat)

private theorem torResolutionComplex_bounded
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M N : ModuleCat.{max u v} B) :
    ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero ((torResolutionComplex A B M N).X i) := by
  refine ⟨0, ?_⟩
  intro i hi
  let C := (((CochainComplex.Tor.moduleTensorBifunctor B).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (ProjectiveResolution.of N).complex
  change IsZero ((ModuleCat.restrictScalars (algebraMap A B)).obj
    ((C.extend ComplexShape.embeddingDownNat).X i))
  apply (ModuleCat.restrictScalars (algebraMap A B)).map_isZero
  apply HomologicalComplex.isZero_extend_X C ComplexShape.embeddingDownNat i
  intro n hn
  change -(n : ℤ) = i at hn
  omega

/-! ### Flatness over `A` of the terms of that complex -/

private theorem flat_of_injective_of_surjective
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.Flat R N] [Module.Flat R P]
    (i : M →ₗ[R] N) (p : N →ₗ[R] P)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (h : Function.Exact i p) : Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro V W _ _ _ _ f hf x y hxy
  apply LinearMap.lTensor_injective_of_exact_of_flat p hp i hi h V
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
  have hc : (f.rTensor N).comp (i.lTensor V) =
      (i.lTensor W).comp (f.rTensor M) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  change ((f.rTensor N).comp (i.lTensor V)) x =
    ((f.rTensor N).comp (i.lTensor V)) y
  rw [hc]
  exact congrArg (i.lTensor W) hxy

private theorem flatOfProjectiveOverFlatAlgebra
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : ModuleCat.{max u v} B)
    [Module.Projective B P] : Module.Flat A (restrictScalars A B P) := by
  let : Module A P := Module.compHom P (algebraMap A B)
  let : IsScalarTower A B P :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  change Module.Flat A P
  exact Module.Flat.trans A B P

private theorem flatTensorOfProjective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (P M : ModuleCat.{max u v} B)
    [Module.Projective B P]
    [Module.Flat A (restrictScalars A B M)] :
    Module.Flat A (restrictScalars A B (ModuleCat.of B (P ⊗[B] M))) := by
  classical
  obtain ⟨Q, hQadd, hQmod, hQfree, i, s, his⟩ :=
    (Module.Projective.iff_split (R := B) (P := P)).mp inferInstance
  let := hQadd
  let := hQmod
  let := hQfree
  let : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
  let : Module A M := Module.compHom M (algebraMap A B)
  have : Module.Flat A M := by
    change Module.Flat A (restrictScalars A B M)
    infer_instance
  let : IsScalarTower A B M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module A (P ⊗[B] M) := Module.compHom _ (algebraMap A B)
  let : Module A (Q ⊗[B] M) := Module.compHom _ (algebraMap A B)
  let : IsScalarTower A B (P ⊗[B] M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower A B (Q ⊗[B] M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let b := Module.Free.chooseBasis B Q
  let e := TensorProduct.equivFinsuppOfBasisLeft b (N := M)
  have hQflat : Module.Flat A (Q ⊗[B] M) := by
    have : Module.Flat A (DirectSum (Module.Free.ChooseBasisIndex B Q) (fun _ => M)) :=
      inferInstance
    have : Module.Flat A ((Module.Free.ChooseBasisIndex B Q) →₀ M) :=
      Module.Flat.of_linearEquiv
        (finsuppLEquivDirectSum A M (Module.Free.ChooseBasisIndex B Q))
    exact Module.Flat.of_linearEquiv (e.restrictScalars A)
  let iT := (i.rTensor M).restrictScalars A
  let sT := (s.rTensor M).restrictScalars A
  apply Module.Flat.of_retract iT sT
  refine LinearMap.ext fun x => ?_
  change (s.rTensor M) ((i.rTensor M) x) = x
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, his]
  simp

private theorem torResolutionComplex_flat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M N : ModuleCat.{max u v} B)
    [Module.Flat A (restrictScalars A B M)] :
    ∀ i : ℤ, Module.Flat A ((torResolutionComplex A B M N).X i) := by
  classical
  intro i
  let F := (CochainComplex.Tor.moduleTensorBifunctor.{u, v} B).obj M
  let C := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (ProjectiveResolution.of N).complex
  let R := ModuleCat.restrictScalars (algebraMap A B)
  change Module.Flat A (R.obj ((C.extend ComplexShape.embeddingDownNat).X i))
  cases hi : ComplexShape.embeddingDownNat.r i with
  | none =>
      have hz : IsZero ((C.extend ComplexShape.embeddingDownNat).X i) := by
        apply HomologicalComplex.isZero_extend_X C ComplexShape.embeddingDownNat i
        intro n hn
        have hf := ComplexShape.Embedding.r_f ComplexShape.embeddingDownNat n
        rw [hn] at hf
        simp [hi] at hf
      have : Subsingleton (R.obj ((C.extend ComplexShape.embeddingDownNat).X i)) := by
        rw [ModuleCat.isZero_iff_subsingleton] at hz
        exact hz
      infer_instance
  | some n =>
      have he : ComplexShape.embeddingDownNat.f n = i :=
        ComplexShape.Embedding.f_eq_of_r_eq_some ComplexShape.embeddingDownNat hi
      have : Projective ((ProjectiveResolution.of N).complex.X n) :=
        (ProjectiveResolution.of N).projective n
      have : Module.Projective B ((ProjectiveResolution.of N).complex.X n) :=
        inferInstance
      have hflat : Module.Flat A (R.obj (C.X n)) := by
        let P := (ProjectiveResolution.of N).complex.X n
        let : Module A M := Module.compHom M (algebraMap A B)
        let : IsScalarTower A B M :=
          IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
        let : Module A (M ⊗[B] P) := Module.compHom _ (algebraMap A B)
        let : Module A (P ⊗[B] M) := Module.compHom _ (algebraMap A B)
        let : IsScalarTower A B (M ⊗[B] P) :=
          IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
        let : IsScalarTower A B (P ⊗[B] M) :=
          IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
        have h : Module.Flat A (P ⊗[B] M) :=
          flatTensorOfProjective A B P M
        change Module.Flat A (M ⊗[B] P)
        have : LinearMap.CompatibleSMul (M ⊗[B] P) (P ⊗[B] M) A B :=
          ⟨fun f a x => by
            change f ((algebraMap A B a) • x) = (algebraMap A B a) • f x
            exact map_smul f _ _⟩
        have : LinearMap.CompatibleSMul (P ⊗[B] M) (M ⊗[B] P) A B :=
          ⟨fun f a x => by
            change f ((algebraMap A B a) • x) = (algebraMap A B a) • f x
            exact map_smul f _ _⟩
        have compat : LinearMap.CompatibleSMul (M ⊗[B] P) (P ⊗[B] M) A B :=
          inferInstance
        let e : (M ⊗[B] P) ≃ₗ[A] (P ⊗[B] M) :=
          @LinearEquiv.restrictScalars A B (M ⊗[B] P) (P ⊗[B] M)
            _ _ _ _ _ _ _ _ compat (TensorProduct.comm B M P)
        exact Module.Flat.of_linearEquiv e
      exact Module.Flat.of_linearEquiv
        (R.mapIso (HomologicalComplex.extendXIso C ComplexShape.embeddingDownNat he)).toLinearEquiv

/-! ### Tensoring with a single module, and extension along an embedding of shapes -/

open CategoryTheory.MonoidalCategory HomologicalComplex
open TotalTensorComplex.SingleTensor

-- Mathlib's monoidal structure on `ModuleCat` requires the module universe to equal the ring's.
-- Instance search reaches it first and then fails trying to unify `max u v =?= u`, which Lean does
-- not treat as "does not apply", so it does not fall through to the lifted structure. Making the
-- lifted tensor product a local instance settles the choice for the rest of this file.
attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive
set_option backward.isDefEq.respectTransparency false

/-! ### The abutment: homology of `K ⊗ P` is `Tor` over `B'` -/

private theorem quasiIso_tensorModule_map
    {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R)
    {C D : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : C ⟶ D) [QuasiIso f]
    (hC : CochainComplex.KFlat.{u, v} C) (hD : CochainComplex.KFlat.{u, v} D) :
    QuasiIso (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have ht := CochainComplex.DerivedTensor.quasiIso_tleftCochain_map f hC hD
    ((single _ (ComplexShape.up ℤ) 0).obj N)
  have hcomp : QuasiIso ((singleTensorIso N C).inv ≫
      (TleftCochain ((single _ (ComplexShape.up ℤ) 0).obj N)).map f) := inferInstance
  rw [singleTensorIso_naturality] at hcomp
  exact (quasiIso_iff_comp_right _ (singleTensorIso N D).inv).mp hcomp

private theorem kFlat_single
    {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R) [Module.Flat R N] :
    CochainComplex.KFlat.{u, v} ((single _ (ComplexShape.up ℤ) 0).obj N) := by
  let K : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    (single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj N
  have hflat : ∀ n : ℤ, Module.Flat R (K.X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact Module.Flat.of_linearEquiv (singleObjXSelf (ComplexShape.up ℤ) 0 N).toLinearEquiv
    · have : Subsingleton (K.X n) := (ModuleCat.isZero_iff_subsingleton).mp
        (isZero_single_obj_X (ComplexShape.up ℤ) 0 N n hn)
      infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat K 0

private noncomputable def baseChangeRestrictLinearEquiv
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (M : ModuleCat.{max u v} B) :
    (restrictScalars A A' (regularModule A')) ⊗[A] (restrictScalars A B M) ≃ₗ[A]
      restrictScalars A (BaseChangedAlgebra A B A') (baseChange A B A' M) := by
  letI : Algebra A' (BaseChangedAlgebra A B A') := Algebra.TensorProduct.rightAlgebra
  letI : Module A M := Module.compHom M (algebraMap A B)
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let e := Algebra.IsPushout.cancelBaseChange A A' B (BaseChangedAlgebra A B A') M
  let eU : restrictScalars A A' (@regularModule.{u,v} A' _) ≃ₗ[A] A' :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change algebraMap A A' a * x.down = a • x.down
        exact (Algebra.smul_def a x.down).symm }
  let eB : (BaseChangedAlgebra A B A' ⊗[B] M) ≃ₗ[A]
      restrictScalars A (BaseChangedAlgebra A B A') (baseChange A B A' M) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change a • x = algebraMap A (BaseChangedAlgebra A B A') a • x
        exact (IsScalarTower.algebraMap_smul (BaseChangedAlgebra A B A') a x).symm }
  exact (TensorProduct.congr eU (LinearEquiv.refl A M)).trans
    ((e.symm.restrictScalars A).trans eB)

private lemma baseChangeRestrictLinearEquiv_naturality
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] {M N : ModuleCat.{max u v} B} (f : M ⟶ N) :
    (baseChangeRestrictLinearEquiv A B A' N).toLinearMap.comp
      (((ModuleCat.restrictScalars (algebraMap A B)).map f).hom.lTensor
        (restrictScalars A A' (regularModule A'))) =
      (((ModuleCat.restrictScalars (algebraMap A (BaseChangedAlgebra A B A'))).map
        (ModuleCat.ofHom (f.hom.baseChange (BaseChangedAlgebra A B A')))).hom.comp
          (baseChangeRestrictLinearEquiv A B A' M).toLinearMap) := by
  let : Algebra A' (BaseChangedAlgebra A B A') := Algebra.TensorProduct.rightAlgebra
  let : Module A M := Module.compHom M (algebraMap A B)
  let : Module A N := Module.compHom N (algebraMap A B)
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  apply TensorProduct.ext'
  intro a m
  change (Algebra.IsPushout.cancelBaseChange A A' B (BaseChangedAlgebra A B A') N).symm
      (a.down ⊗ₜ[A] f m) =
    (f.hom.baseChange (BaseChangedAlgebra A B A'))
      ((Algebra.IsPushout.cancelBaseChange A A' B (BaseChangedAlgebra A B A') M).symm
        (a.down ⊗ₜ[A] m))
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul,
    Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

private theorem quasiIso_tensor_restrict_projectiveResolution
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (N : ModuleCat.{max u v} B) [Module.Flat A (restrictScalars A B N)]
    (Z : ModuleCat.{max u v} A) (Q : ProjectiveResolution N) :
    QuasiIso (((tensorLeft Z).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map Q.π')) := by
  let F := ModuleCat.restrictScalars (algebraMap A B)
  let K : CochainComplex (ModuleCat.{max u v} A) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q.cochainComplex
  let L : CochainComplex (ModuleCat.{max u v} A) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} B) 0).obj N)
  have hKflat : ∀ i : ℤ, Module.Flat A (K.X i) := fun i =>
    flatOfProjectiveOverFlatAlgebra A B (Q.cochainComplex.X i)
  have hLflat : ∀ i : ℤ, Module.Flat A (L.X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact Module.Flat.of_linearEquiv
        (F.mapIso (singleObjXSelf (ComplexShape.up ℤ) 0 N)).toLinearEquiv
    · have : Subsingleton (L.X i) := ModuleCat.isZero_iff_subsingleton.mp
        (F.map_isZero (isZero_single_obj_X (ComplexShape.up ℤ) 0 N i hi))
      infer_instance
  have hKle : K.IsStrictlyLE 0 := by
    dsimp [K]
    rw [CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff]
    infer_instance
  have hLle : L.IsStrictlyLE 0 := by
    dsimp [L]
    rw [CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff]
    infer_instance
  exact quasiIso_tensorModule_map Z _ (CochainComplex.KFlat.kFlat_of_flat K 0)
    (CochainComplex.KFlat.kFlat_of_flat L 0)

private noncomputable def extendScalarsObjIso
    (B S : Type u) [CommRing B] [CommRing S] [Algebra B S]
    (M : ModuleCat.{max u v} B) :
    (ModuleCat.extendScalars (algebraMap B S)).obj M ≅ ModuleCat.of S (S ⊗[B] M) := by
  let X := (ModuleCat.restrictScalars (algebraMap B S)).obj (ModuleCat.of S S)
  have : IsScalarTower B S X := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let e : X ≃ₗ[S] S := LinearEquiv.refl S S
  exact (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl B M)).toModuleIso

private noncomputable def baseChangeRestrictIso
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] :
    ModuleCat.restrictScalars (algebraMap A B) ⋙
        tensorLeft (restrictScalars A A' (@regularModule.{u,v} A' _)) ≅
      ModuleCat.extendScalars (algebraMap B (BaseChangedAlgebra A B A')) ⋙
        ModuleCat.restrictScalars (algebraMap A (BaseChangedAlgebra A B A')) := by
  refine NatIso.ofComponents (fun M ↦ (baseChangeRestrictLinearEquiv A B A' M).toModuleIso ≪≫
    (ModuleCat.restrictScalars (algebraMap A (BaseChangedAlgebra A B A'))).mapIso
      (extendScalarsObjIso B (BaseChangedAlgebra A B A') M).symm) ?_
  intro M N f
  ext : 1
  apply TensorProduct.ext'
  intro a m
  let : Algebra A' (BaseChangedAlgebra A B A') := Algebra.TensorProduct.rightAlgebra
  let : Module A M := Module.compHom M (algebraMap A B)
  let : Module A N := Module.compHom N (algebraMap A B)
  have : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  change (extendScalarsObjIso B (BaseChangedAlgebra A B A') N).inv
      ((Algebra.IsPushout.cancelBaseChange A A' B (BaseChangedAlgebra A B A') N).symm
        (a.down ⊗ₜ[A] f m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  change _ = (ModuleCat.extendScalars (algebraMap B (BaseChangedAlgebra A B A'))).map f
    ((extendScalarsObjIso B (BaseChangedAlgebra A B A') M).inv
      ((Algebra.IsPushout.cancelBaseChange A A' B (BaseChangedAlgebra A B A') M).symm
        (a.down ⊗ₜ[A] m)))
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

private theorem quasiIso_extendScalars_projectiveResolution
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [Module.Flat A B]
    (N : ModuleCat.{max u v} B) [Module.Flat A (restrictScalars A B N)]
    (Q : ProjectiveResolution N) :
    QuasiIso (((ModuleCat.extendScalars
      (algebraMap B (BaseChangedAlgebra A B A'))).mapHomologicalComplex
        (ComplexShape.down ℕ)).map Q.π) := by
  let E := ModuleCat.extendScalars (algebraMap B (BaseChangedAlgebra A B A'))
  let R := ModuleCat.restrictScalars (algebraMap A (BaseChangedAlgebra A B A'))
  let S := ModuleCat.restrictScalars (algebraMap A B)
  let T := tensorLeft (restrictScalars A A' (@regularModule.{u,v} A' _))
  let e := Functor.mapHomologicalComplexCompIso (baseChangeRestrictIso.{u,v} A B A')
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ R)) (ComplexShape.up ℤ)).symm
  have : QuasiIso ((S.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      T.mapHomologicalComplex (ComplexShape.up ℤ)).map Q.π') :=
    quasiIso_tensor_restrict_projectiveResolution A B N
      (restrictScalars A A' (@regularModule.{u,v} A' _)) Q
  have hc : QuasiIso (((S.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      T.mapHomologicalComplex (ComplexShape.up ℤ)).map Q.π') ≫ e.hom.app _) := inferInstance
  rw [e.hom.naturality] at hc
  have ht := (quasiIso_iff_comp_left (e.hom.app _) _).mp hc
  have he : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map Q.π') :=
    (quasiIso_map_iff_of_preservesHomology _ R).mp ht
  have hext : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (extendMap Q.π ComplexShape.embeddingDownNat)) := by
    unfold ProjectiveResolution.π' at he
    rw [Functor.map_comp] at he
    exact (quasiIso_iff_comp_right _ _).mp he
  have hc' : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (extendMap Q.π ComplexShape.embeddingDownNat) ≫
        (mapHomologicalComplexExtendIso E _ ComplexShape.embeddingDownNat).inv) := inferInstance
  rw [mapHomologicalComplexExtendIso_inv_naturality] at hc'
  have ht' := (quasiIso_iff_comp_left
    (mapHomologicalComplexExtendIso E _ ComplexShape.embeddingDownNat).inv _).mp hc'
  exact (quasiIso_extendMap_iff _ ComplexShape.embeddingDownNat).mp ht'

private noncomputable def baseChangedProjectiveResolution
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [Module.Flat A B]
    (N : ModuleCat.{max u v} B) [Module.Flat A (restrictScalars A B N)]
    (Q : ProjectiveResolution N) : ProjectiveResolution (baseChange A B A' N) := by
  let E := ModuleCat.extendScalars (algebraMap B (BaseChangedAlgebra A B A'))
  have h := quasiIso_extendScalars_projectiveResolution A B A' N Q
  refine { complex := (E.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
           π := (E.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π ≫
             (singleMapHomologicalComplex E (ComplexShape.down ℕ) 0).hom.app N ≫
             (single _ (ComplexShape.down ℕ) 0).map
               (extendScalarsObjIso B (BaseChangedAlgebra A B A') N).hom
           projective := fun n => (ModuleCat.extendRestrictScalarsAdj
             (algebraMap B (BaseChangedAlgebra A B A'))).map_projective _ (Q.projective n)
           quasiIso := by infer_instance }

private noncomputable def tensorBaseChangeRestrictIso
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (M : ModuleCat.{max u v} B) :
    (CochainComplex.Tor.moduleTensorBifunctor.{u, v} B).obj M ⋙
        ModuleCat.restrictScalars (algebraMap A B) ⋙
          tensorLeft (restrictScalars A A' (@regularModule.{u,v} A' _)) ≅
      ModuleCat.extendScalars (algebraMap B (BaseChangedAlgebra A B A')) ⋙
        (CochainComplex.Tor.moduleTensorBifunctor.{u, v} (BaseChangedAlgebra A B A')).obj
          (baseChange A B A' M) ⋙
        ModuleCat.restrictScalars (algebraMap A (BaseChangedAlgebra A B A')) := by
  refine NatIso.ofComponents (fun X ↦
    (baseChangeRestrictLinearEquiv A B A'
      (ModuleCat.of B (M ⊗[B] X))).toModuleIso ≪≫
    (ModuleCat.restrictScalars (algebraMap A (BaseChangedAlgebra A B A'))).mapIso
      ((TensorProduct.AlgebraTensorModule.distribBaseChange B
        (BaseChangedAlgebra A B A') M X).toModuleIso ≪≫
      ((CochainComplex.Tor.moduleTensorBifunctor.{u, v} (BaseChangedAlgebra A B A')).obj
          (baseChange A B A' M)).mapIso
        (extendScalarsObjIso B (BaseChangedAlgebra A B A') X).symm)) ?_
  intro X Y f
  ext : 1
  apply TensorProduct.ext'
  intro a t
  let : Algebra A' (BaseChangedAlgebra A B A') := Algebra.TensorProduct.rightAlgebra
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, TensorProduct.tmul_add, ht, ht']
  | tmul m x =>
    let : Module A (M ⊗[B] X) := Module.compHom _ (algebraMap A B)
    let : Module A (M ⊗[B] Y) := Module.compHom _ (algebraMap A B)
    have : IsScalarTower A B (M ⊗[B] X) := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    have : IsScalarTower A B (M ⊗[B] Y) := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    change ((CochainComplex.Tor.moduleTensorBifunctor.{u, v}
          (BaseChangedAlgebra A B A')).obj (baseChange A B A' M)).map
        (extendScalarsObjIso B (BaseChangedAlgebra A B A') Y).inv
      (TensorProduct.AlgebraTensorModule.distribBaseChange B (BaseChangedAlgebra A B A') M Y
        ((Algebra.IsPushout.cancelBaseChange A A' B (BaseChangedAlgebra A B A')
          (M ⊗[B] Y)).symm (a.down ⊗ₜ[A] (m ⊗ₜ[B] f x)))) = _
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
    change _ = ((CochainComplex.Tor.moduleTensorBifunctor.{u, v}
          (BaseChangedAlgebra A B A')).obj (baseChange A B A' M)).map
        ((ModuleCat.extendScalars (algebraMap B (BaseChangedAlgebra A B A'))).map f)
      (((CochainComplex.Tor.moduleTensorBifunctor.{u, v}
          (BaseChangedAlgebra A B A')).obj (baseChange A B A' M)).map
        (extendScalarsObjIso B (BaseChangedAlgebra A B A') X).inv
      (TensorProduct.AlgebraTensorModule.distribBaseChange B (BaseChangedAlgebra A B A') M X
        ((Algebra.IsPushout.cancelBaseChange A A' B (BaseChangedAlgebra A B A')
          (M ⊗[B] X)).symm (a.down ⊗ₜ[A] (m ⊗ₜ[B] x)))))
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
    rfl

private noncomputable def resolutionTensorHomologyIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M N : ModuleCat.{max u v} B) (Q : ProjectiveResolution N) (i : ℤ) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((((CochainComplex.Tor.moduleTensorBifunctor B).obj M).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Q.complex).extend
            ComplexShape.embeddingDownNat)).homology (-i) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (@CochainComplex.Tor.TorInDegree.{u, v} B _ i M N) := by
  let F := (CochainComplex.Tor.moduleTensorBifunctor.{u, v} B).obj M
  let C := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let T := C.extend ComplexShape.embeddingDownNat
  let R := ModuleCat.restrictScalars (algebraMap A B)
  by_cases hi : 0 ≤ i
  · have he : ComplexShape.embeddingDownNat.f i.toNat = -i := by
      change -(i.toNat : ℤ) = -i
      rw [Int.toNat_of_nonneg hi]
    have eT : T.homology (-i) ≅ C.homology i.toNat :=
      HomologicalComplex.extendHomologyIso C ComplexShape.embeddingDownNat he
    have eP : (F.leftDerived i.toNat).obj N ≅ C.homology i.toNat :=
      Q.isoLeftDerivedObj F i.toNat
    have e := restrictHomologyIso (algebraMap A B) T (-i) ≪≫ R.mapIso (eT ≪≫ eP.symm)
    simpa only [CochainComplex.Tor.TorInDegree, dite_eq_left hi] using e
  · have hX : IsZero ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj T |>.X (-i)) := by
      change IsZero (R.obj (T.X (-i)))
      apply R.map_isZero
      apply HomologicalComplex.isZero_extend_X C ComplexShape.embeddingDownNat (-i)
      intro n hn
      change -(n : ℤ) = -i at hn
      omega
    have hleft := ShortComplex.isZero_homology_of_isZero_X₂
      (((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj T).sc (-i)) hX
    have hright : IsZero (R.obj (@CochainComplex.Tor.TorInDegree.{u, v} B _ i M N)) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      unfold CochainComplex.Tor.TorInDegree
      simp only [dite_eq_right hi]
      change Subsingleton (ULift.{v} (Fin 0 → B))
      infer_instance
    exact hleft.iso hright

private noncomputable def torResolutionComplex_baseChangeIso
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [Module.Flat A B]
    (M N : ModuleCat.{max u v} B) [Module.Flat A (restrictScalars A B N)] (n : ℤ) :
    (((tensorLeft (restrictScalars A A' (@regularModule.{u,v} A' _))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (torResolutionComplex A B M N)).homology (-n) ≅
      (ModuleCat.restrictScalars (algebraMap A (BaseChangedAlgebra A B A'))).obj
        (@CochainComplex.Tor.TorInDegree.{u, v} (BaseChangedAlgebra A B A') _ n
          (baseChange A B A' M) (baseChange A B A' N)) := by
  let B' := BaseChangedAlgebra A B A'
  let Q := ProjectiveResolution.of N
  let Q' := baseChangedProjectiveResolution A B A' N Q
  let S := ModuleCat.restrictScalars (algebraMap A B)
  let T := tensorLeft (restrictScalars A A' (@regularModule.{u,v} A' _))
  let E := ModuleCat.extendScalars (algebraMap B B')
  let R := ModuleCat.restrictScalars (algebraMap A B')
  let FB := (CochainComplex.Tor.moduleTensorBifunctor.{u, v} B).obj M
  let FB' := (CochainComplex.Tor.moduleTensorBifunctor.{u, v} B').obj (baseChange A B A' M)
  let emb := ComplexShape.embeddingDownNat
  let e₁ : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj (torResolutionComplex A B M N) ≅
      ((S ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((FB.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex |>.extend emb) :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (S ⋙ T)) (ComplexShape.up ℤ)).app _
  let e₂ := (mapHomologicalComplexExtendIso (S ⋙ T)
    ((FB.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) emb).symm
  let e₃ : ((S ⋙ T).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((FB.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≅
      ((R.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((FB'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q'.complex)) :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (FB ⋙ S ⋙ T))
        (ComplexShape.down ℕ)).app _ ≪≫
      (NatIso.mapHomologicalComplex (tensorBaseChangeRestrictIso A B A' M)
        (ComplexShape.down ℕ)).app _ ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ FB' ⋙ R))
        (ComplexShape.down ℕ)).app _).symm ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (FB' ⋙ R))
        (ComplexShape.down ℕ)).app _).symm
  let e₄ := mapHomologicalComplexExtendIso R
    ((FB'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q'.complex) emb
  exact HomologicalComplex.homologyMapIso
      (e₁ ≪≫ e₂ ≪≫ (emb.extendFunctor _).mapIso e₃ ≪≫ e₄) (-n) ≪≫
    resolutionTensorHomologyIso A B' (baseChange A B A' M) (baseChange A B A' N) Q' n

/-! ### The spectral sequence -/

/-- If `A → B` and the `B`-modules `M` and `N` are flat over `A`, then for
`B' = B ⊗[A] A'`, `M' = M ⊗[B] B'`, and `N' = N ⊗[B] B'`, there is a homological spectral sequence
`Torᴬᵢ(Torᴮⱼ(M, N), A') ⇒ Torᴮʳᵢ₊ⱼ(M', N')`.

Both sides are viewed as `A`-modules in order to state the spectral sequence in one abelian
category. -/
@[stacks 0620, ega "III 6.9.8" "(6.9.8.1)"]
public theorem exists_tor_base_change_spectral_sequence
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (M N : ModuleCat.{max u v} B)
    [Module.Flat A B]
    [Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M)]
    [Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj N)] :
    ∃ (E : CochainComplex.Tor.FirstTorSpectralSequence (ModuleCat.{max u v} A))
      (_e₂ : ∀ i j : ℤ,
        (E.page 2).X (i, j) ≅
          @CochainComplex.Tor.TorInDegree.{u, v} A _ j
            (restrictScalars A B
              (@CochainComplex.Tor.TorInDegree.{u, v} B _ i M N))
            (restrictScalars A A' (@regularModule.{u, v} A' _))),
      CochainComplex.Tor.HomologicalSpectralSequenceAbutsTo E
        (fun n ↦
          (ModuleCat.restrictScalars
            (algebraMap A (BaseChangedAlgebra A B A'))).obj
            (@CochainComplex.Tor.TorInDegree.{u, v} (BaseChangedAlgebra A B A') _ n
              (@baseChange.{u, v} A B A' _ _ _ _ _ M)
              (@baseChange.{u, v} A B A' _ _ _ _ _ N))) := by
  apply spectralSequenceOfCalibratedComplex A B A' M N
    (torResolutionComplex A B M N)
    (torResolutionComplex_bounded A B M N)
    (fun i ↦ resolutionTensorHomologyIso A B M N (ProjectiveResolution.of N) i)
  intro P ε hε hfree hbounded n
  let K := torResolutionComplex A B M N
  have hflat : ∀ i : ℤ, Module.Flat A (K.X i) := torResolutionComplex_flat A B M N
  have hle : K.IsStrictlyLE 0 := by
    change CochainComplex.IsStrictlyLE
      (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj _) 0
    rw [CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff]
    infer_instance
  have hk : CochainComplex.KFlat.{u, v} K := CochainComplex.KFlat.kFlat_of_flat K 0
  have : QuasiIso ε := hε
  exact tensorResolutionHomologyIso K hk
    (restrictScalars A A' (@regularModule.{u,v} A' _)) ε (-n) ≪≫
      torResolutionComplex_baseChangeIso A B A' M N n

end RingTheory.TorBaseChange

end
