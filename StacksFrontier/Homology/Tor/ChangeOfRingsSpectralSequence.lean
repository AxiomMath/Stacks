module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.Tor
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.ProjectiveResolution
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# The change-of-rings spectral sequence for Tor

Let `f : R → S` be a homomorphism of commutative rings, `M` an `R`-module and `N` an `S`-module.
Choose a free resolution `P^•` of `M` over `R`. Extending scalars gives a complex `P^• ⊗_R S` of
`S`-modules whose homology is `Tor_*^R(M, S)`, again as `S`-modules; tensoring that complex with
`N` over `S` gives a complex whose homology is `Tor_*^R(M, N)`, because `P^•` is K-flat over `R`.
The first spectral sequence of Tag 061Z applied to `P^• ⊗_R S` and `N` therefore reads
```
E_2^{n,m} = Tor_n^S(Tor_m^R(M, S), N)  ⟹  Tor_{n+m}^R(M, N).
```

## Main definitions

* `baseChangeComplex`: the degreewise extension of scalars of a cochain complex along a ring
  homomorphism.
* `baseChangeTensorComplex`: the tensor product over `S` of that scalar extension with an
  `S`-module, retaining its `S`-module structure.

## Main results

* `exists_tor_change_of_rings_spectral_sequence`: the change-of-rings spectral sequence, together
  with the identifications of the homology of `P^• ⊗_R S` with `Tor_*^R(M, S)` and of the homology
  of `(P^• ⊗_R S) ⊗_S N` with `Tor_*^R(M, N)` after restriction of scalars.

## Implementation notes

The `S`-module structure on `Tor_m^R(M, S)` is what makes the statement say more than a
restatement of Tag 061Z, and it is retained by realizing that Tor group as the homology of the
scalar extension of a chosen free resolution of `M`; after restriction of scalars along `f` that
homology is identified with `Tor_m^R(M, S)` as computed over `R`. Both identifications go through
the fact that a bounded-above complex of flat modules is K-flat (Tag 064K), so any K-flat
resolution computes Tor: the comparison `torIsoOfKFlatResolution` is the composite of the flip of
the tensor bicomplex with the two quasi-isomorphism invariances.

Homological degrees are represented by negated cochain degrees, as in the spectral sequence of
Tag 061Z, so chain degree `n` is cochain degree `-n`. The coefficient module `S` is universe-lifted
so that module carriers may lie in a universe larger than that of the rings.

The flip isomorphism `CochainComplex.DerivedTensor.tensorFlipIso` and the preservation of
quasi-isomorphisms `CochainComplex.DerivedTensor.quasiIso_tright_map` are taken from
`StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse` rather than reproved here.

## References

* [The Stacks Project, Tag 068F](https://stacks.math.columbia.edu/tag/068F)
* [The Stacks Project, Tag 061Z](https://stacks.math.columbia.edu/tag/061Z)
* [The Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CochainComplex.Tor.ChangeOfRingsSpectralSequence

universe u v


/-- Degreewise extension of scalars of a cochain complex along a ring homomorphism. -/
public noncomputable abbrev baseChangeComplex
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    CochainComplex (ModuleCat.{max u v} S) ℤ :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- The complex `(P ⊗_R S) ⊗_S N`, retaining its natural `S`-module structure. -/
public noncomputable abbrev baseChangeTensorComplex
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (N : ModuleCat.{max u v} S) :
    CochainComplex (ModuleCat.{max u v} S) ℤ :=
  (((moduleTensorBifunctor S).obj N).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (baseChangeComplex f P)

/-! ### Comparisons of Tor groups with the homology of tensor products -/

/-- An isomorphism `X ≅ Y` of `R`-modules induces an isomorphism
`Tor_n^R(X, Z) ≅ Tor_n^R(Y, Z)` in each degree `n`. -/
noncomputable def torInDegreeCongr
    (R : Type u) [CommRing R] (n : ℤ)
    {X Y : ModuleCat.{max u v} R} (e : X ≅ Y)
    (Z : ModuleCat.{max u v} R) :
    TorInDegree R n X Z ≅ TorInDegree R n Y Z := by
  unfold TorInDegree
  split
  next h =>
    let F := moduleTensorBifunctor.{u, v} R
    let τ : F.obj X ≅ F.obj Y := F.mapIso e
    let ρ : (F.obj X).leftDerived n.toNat ≅ (F.obj Y).leftDerived n.toNat :=
      { hom := NatTrans.leftDerived τ.hom n.toNat
        inv := NatTrans.leftDerived τ.inv n.toNat
        hom_inv_id := by
          rw [← NatTrans.leftDerived_comp, τ.hom_inv_id, NatTrans.leftDerived_id]
        inv_hom_id := by
          rw [← NatTrans.leftDerived_comp, τ.inv_hom_id, NatTrans.leftDerived_id] }
    exact ρ.app Z
  next h => exact Iso.refl _

/-- The universe lift of an `R`-module whose carrier already lies in the target universe is
isomorphic to the module itself. -/
noncomputable def uliftModuleIso (R : Type u) [CommRing R]
    (X : ModuleCat.{max u v} R) :
    (ModuleCat.uliftFunctor.{max u v, max u v} R).obj X ≅ X :=
  ULift.moduleEquiv.toModuleIso

/-- The degreewise universe lift of a cochain complex of `R`-modules whose carriers already lie
in the target universe is isomorphic to the complex itself. -/
noncomputable def uliftComplexIso (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    ((ModuleCat.uliftFunctor.{max u v, max u v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ uliftModuleIso R (K.X i))
    (fun _ _ _ ↦ rfl)

/-- Isomorphisms `X ≅ X'` and `Y ≅ Y'` of `R`-modules induce an isomorphism
`Tor_n^R(X, Y) ≅ Tor_n^R(X', Y')` in each degree `n`, between the two universe parameters
of `TorInDegree`. -/
noncomputable def torInDegreeIso
    (R : Type u) [CommRing R] (n : ℤ)
    {X X' Y Y' : ModuleCat.{max u v} R} (e : X ≅ X') (f : Y ≅ Y') :
    TorInDegree.{u, max u v} R n X Y ≅ TorInDegree.{u, v} R n X' Y' := by
  by_cases hn : 0 ≤ n
  · have g := torInDegreeCongr R n e Y
    simp only [TorInDegree, dite_eq_left hn] at g ⊢
    exact g ≪≫ (((moduleTensorBifunctor R).obj X').leftDerived n.toNat).mapIso f
  · simp only [TorInDegree, dite_eq_right hn]
    exact (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).iso
      (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)

/-- Restriction of scalars along `f : A →+* B` commutes with homology: the `i`-th homology of
the restriction of scalars of a cochain complex `T` of `B`-modules is isomorphic to the
restriction of scalars of the `i`-th homology of `T`. -/
noncomputable def restrictHomologyIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (T : CochainComplex (ModuleCat.{max u v} B) ℤ) (i : ℤ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj T).homology i ≅
      (ModuleCat.restrictScalars f).obj (T.homology i) := by
  let F := ModuleCat.restrictScalars.{max u v} f
  have : F.PreservesHomology := inferInstance
  exact (HomologicalComplex.homologyMapIso (Iso.refl _) i).symm ≪≫
    ShortComplex.mapHomologyIso (T.sc i) F

section Construction

open CategoryTheory.MonoidalCategory HomologicalComplex
open TotalTensorComplex.SingleTensor

-- Mathlib's monoidal instance on `ModuleCat` requires the module universe to equal the ring's.
-- Instance search reaches it first and fails by universe unification, which Lean does not treat
-- as "does not apply", so it never falls through to the lifted structure. Making the lifted
-- tensor product a local instance settles the choice for this file.
attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

set_option backward.isDefEq.respectTransparency false

/-! ### K-flat resolutions compute Tor -/

/-- **Contracting a resolution inside a total tensor complex against a K-flat factor.** If `K`
is K-flat and `ε : P ⟶ Z` is a quasi-isomorphism onto the module `Z` placed in degree `0`, then
`Tot(K ⊗_R P)` and `Z ⊗_R K` have the same homology: tensoring with a K-flat complex preserves
quasi-isomorphisms. -/
noncomputable def tensorResolutionHomologyIso
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (hK : K.KFlat)
    (Z : ModuleCat.{max u v} R) {P : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (ε : P ⟶ (single _ (ComplexShape.up ℤ) 0).obj Z) [QuasiIso ε] (n : ℤ) :
    (HomologicalComplex.mapBifunctor K P (moduleTensorBifunctor R) (ComplexShape.up ℤ)).homology n ≅
      (((tensorLeft Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n := by
  have hε := CochainComplex.DerivedTensor.quasiIso_tright_map K hK ε
  exact homologyMapIso (CochainComplex.DerivedTensor.tensorFlipIso K P) n ≪≫
    isoOfQuasiIsoAt ((TrightCochain K).map ε) n ≪≫
      homologyMapIso (singleTensorIso Z K) n

private theorem freeResolutionBridge
    (R : Type u) [CommRing R] (M : ModuleCat.{max u v} R) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ),
      ∃ (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj M)
        (_ : QuasiIso ε),
        (∀ i : ℤ, Module.Free R (P.X i)) ∧
        (∀ i : ℤ, 0 < i → IsZero (P.X i)) ∧
        Nonempty (P.homology 0 ≅ M) ∧
        (∀ i : ℤ, i ≠ 0 → IsZero (P.homology i)) := by
  let Z : CochainComplex (ModuleCat.{max u v} R) ℤ :=
    (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj M
  have hZ : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (Z.X i) :=
    ⟨0, fun i hi ↦ HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 M i (by omega)⟩
  obtain ⟨P, ε, hε, hfree, hle, hzero, hne, _⟩ :=
    exists_spectral_sequences_tor_homology_and_terms R Z hZ M
  let eM : (ModuleCat.uliftFunctor.{max u v, max u v} R).obj M ≅ M :=
    (ULift.moduleEquiv : ULift.{max u v, max u v} M ≃ₗ[R] M).toModuleIso
  let ε' := ε ≫
    (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).map eM.hom
  have hε' : QuasiIso ε' := quasiIso_comp _ _
  refine ⟨P, ε', hε', hfree, hle, ?_, ?_⟩
  · exact ⟨hzero.some ≪≫ eM⟩
  · exact hne

private theorem kFlat_of_free_of_bounded {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hfree : ∀ i : ℤ, Module.Free R (P.X i)) (hle : ∀ i : ℤ, 0 < i → IsZero (P.X i)) :
    P.KFlat := by
  have : P.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff P 0).2 hle
  have : ∀ n : ℤ, Module.Flat R (P.X n) := fun n ↦
    have := hfree n
    inferInstance
  exact KFlat.kFlat_of_flat P 0

private theorem isZero_torInDegree_of_neg (R : Type u) [CommRing R] {n : ℤ} (hn : n < 0)
    (X Y : ModuleCat.{max u v} R) : IsZero (TorInDegree.{u, v} R n X Y) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  unfold TorInDegree
  simp only [dite_eq_right (show ¬ 0 ≤ n by omega)]
  show Subsingleton (ULift.{v} (Fin 0 → R))
  infer_instance

/-- **A K-flat resolution computes `Tor` in nonnegative degrees.** If `ε : P ⟶ M` is a
quasi-isomorphism from a K-flat complex onto the module `M` placed in degree `0`, then the
`(-n)`-th homology of `X ⊗ P` is `Tor_n^R(M, X)`.

This is the nonnegative-degree case of `torIsoOfKFlatResolution`, which it does not need to bound
the complex `P` for: the hypothesis `P.IsStrictlyLE 0` enters there only in negative degrees, to
see that both sides vanish. -/
@[ega "III 6.3.4" "special case"]
noncomputable def torIsoOfKFlatResolution_natCast {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} {P : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (ε : P ⟶ (single _ (ComplexShape.up ℤ) 0).obj M) [QuasiIso ε]
    (hP : P.KFlat) (X : ModuleCat.{max u v} R) (n : ℕ) :
    (((tensorLeft X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology (-(n : ℤ)) ≅
      TorInDegree.{u, v} R (n : ℤ) M X := by
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  let Q := ProjectiveResolution.of X
  let F := (moduleTensorBifunctor.{u, v} R).obj M
  let C := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  have he : ComplexShape.embeddingDownNat.f (n : ℤ).toNat = -(n : ℤ) := by
    change -(((n : ℤ)).toNat : ℤ) = -(n : ℤ)
    rw [Int.toNat_of_nonneg hn]
  have eT : (C.extend ComplexShape.embeddingDownNat).homology (-(n : ℤ)) ≅
      C.homology (n : ℤ).toNat :=
    HomologicalComplex.extendHomologyIso C ComplexShape.embeddingDownNat he
  have eP : (F.leftDerived (n : ℤ).toNat).obj X ≅ C.homology (n : ℤ).toNat :=
    Q.isoLeftDerivedObj F (n : ℤ).toNat
  have e₀ : (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      Q.cochainComplex).homology (-(n : ℤ)) ≅
      (C.extend ComplexShape.embeddingDownNat).homology (-(n : ℤ)) :=
    homologyMapIso (HomologicalComplex.mapHomologicalComplexExtendIso (tensorLeft M)
      Q.complex ComplexShape.embeddingDownNat).symm (-(n : ℤ))
  have e := (tensorResolutionHomologyIso P hP X Q.π' (-(n : ℤ))).symm ≪≫
    homologyMapIso (CochainComplex.DerivedTensor.tensorFlipIso P Q.cochainComplex) (-(n : ℤ)) ≪≫
    tensorResolutionHomologyIso Q.cochainComplex
      (_root_.CochainComplex.KFlat.kFlat_projectiveResolution Q) M ε (-(n : ℤ)) ≪≫
    e₀ ≪≫ eT ≪≫ eP.symm
  simpa only [TorInDegree, dite_eq_left hn] using e

/-- A K-flat resolution `P` of `M` computes `Tor^R(M, X)` as the homology of `X ⊗ P`. -/
private noncomputable def torIsoOfKFlatResolution {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} {P : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (ε : P ⟶ (single _ (ComplexShape.up ℤ) 0).obj M) [QuasiIso ε] [P.IsStrictlyLE 0]
    (hP : P.KFlat) (X : ModuleCat.{max u v} R) (n : ℤ) :
    (((tensorLeft X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology (-n) ≅
      TorInDegree.{u, v} R n M X := by
  by_cases hn : 0 ≤ n
  · cases n with
    | ofNat m => exact torIsoOfKFlatResolution_natCast ε hP X m
    | negSucc m => omega
  · have hX : IsZero ((((tensorLeft X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).X (-n)) :=
      (tensorLeft X).map_isZero (CochainComplex.isZero_of_isStrictlyLE P 0 (-n) (by omega))
    exact (ShortComplex.isZero_homology_of_isZero_X₂ _ hX).iso
      (isZero_torInDegree_of_neg R (by omega) M X)

/-- **K-flat resolutions of both factors compute `Tor` from the total tensor complex.** If
`εP : P ⟶ M` and `εQ : Q ⟶ N` are quasi-isomorphisms onto the two modules placed in degree `0`,
with `P` K-flat, then the `(-n)`-th homology of the total tensor complex `Tot(P ⊗_R Q)` is
`Tor_n^R(M, N)`.

Only `P` is required to be K-flat: the second resolution is contracted against it, which is what
`tensorResolutionHomologyIso` does. -/
noncomputable def mapBifunctorHomologyTorIso {R : Type u} [CommRing R]
    {M N : ModuleCat.{max u v} R} {P Q : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (εP : P ⟶ (single _ (ComplexShape.up ℤ) 0).obj M) [QuasiIso εP] (hP : P.KFlat)
    (εQ : Q ⟶ (single _ (ComplexShape.up ℤ) 0).obj N) [QuasiIso εQ] (n : ℕ) :
    (HomologicalComplex.mapBifunctor P Q (moduleTensorBifunctor.{u, v} R)
        (ComplexShape.up ℤ)).homology (-(n : ℤ)) ≅
      TorInDegree.{u, v} R (n : ℤ) M N :=
  tensorResolutionHomologyIso P hP N εQ (-(n : ℤ)) ≪≫
    torIsoOfKFlatResolution_natCast εP hP N n

/-! ### Restricting the base change back along `f` -/

/-- The `R`-linear identification `N ⊗_S (S ⊗_R X) ≃ N ⊗_R X`. -/
private noncomputable def restrictTensorExtendLinearEquiv
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (N : ModuleCat.{max u v} S) (X : ModuleCat.{max u v} R) :
    (ModuleCat.restrictScalars f).obj
        (((moduleTensorBifunctor S).obj N).obj
          ((ModuleCat.extendScalars f).obj X)) ≃ₗ[R]
      (tensorLeft ((ModuleCat.restrictScalars f).obj N)).obj X := by
  let : Algebra R S := f.toAlgebra
  let : Module R N := Module.compHom N f
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N X
  exact
    { toFun := fun t ↦ e t
      invFun := fun t ↦ e.symm t
      left_inv := fun t ↦ e.symm_apply_apply t
      right_inv := fun t ↦ e.apply_symm_apply t
      map_add' := fun s t ↦ e.map_add s t
      map_smul' := fun r t ↦ by
        change e (f r • t) = r • e t
        rw [e.map_smul]
        exact IsScalarTower.algebraMap_smul S r (e t) }

private noncomputable def restrictTensorExtendIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (N : ModuleCat.{max u v} S) :
    ModuleCat.extendScalars.{u, u, max u v} f ⋙
        (moduleTensorBifunctor.{u, v} S).obj N ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft ((ModuleCat.restrictScalars f).obj N) := by
  refine NatIso.ofComponents (fun X ↦ (restrictTensorExtendLinearEquiv f N X).toModuleIso) ?_
  intro X Y g
  ext w
  change (N ⊗[S] ((ModuleCat.extendScalars f).obj X)) at w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul n t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero]
    | add t t' ht ht' => simp only [map_add, TensorProduct.tmul_add, ht, ht']
    | tmul s x => rfl

/-- The `R`-linear identification of the restricted scalar extension `S ⊗_R X` with the tensor
product of `X` with the restriction of the regular module. -/
private noncomputable def restrictExtendLinearEquiv
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (X : ModuleCat.{max u v} R) :
    (ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj X) ≃ₗ[R]
      (tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of S (ULift.{v} S)))).obj X := by
  let eU : (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) ≃ₗ[R]
      (ModuleCat.restrictScalars f).obj (ModuleCat.of S (ULift.{v} S)) :=
    { toFun := ULift.up
      invFun := ULift.down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let e := TensorProduct.congr eU (LinearEquiv.refl R X)
  exact
    { toFun := fun t ↦ e t
      invFun := fun t ↦ e.symm t
      left_inv := fun t ↦ e.symm_apply_apply t
      right_inv := fun t ↦ e.apply_symm_apply t
      map_add' := fun s t ↦ e.map_add s t
      map_smul' := fun r t ↦ by
        change e (f r • t) = r • e t
        induction t using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add a b ha hb => simp only [smul_add, map_add, ha, hb]
        | tmul s x => rfl }

private noncomputable def restrictExtendIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat.extendScalars.{u, u, max u v} f ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of S (ULift.{v} S))) := by
  refine NatIso.ofComponents (fun X ↦ (restrictExtendLinearEquiv f X).toModuleIso) ?_
  intro X Y g
  ext w
  change (TensorProduct R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) X) at w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s x => rfl

private noncomputable def restrictBaseChangeHomologyIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ) :
    (ModuleCat.restrictScalars f).obj ((baseChangeComplex f P).homology i) ≅
      (((tensorLeft ((ModuleCat.restrictScalars f).obj
        (ModuleCat.of S (ULift.{v} S)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).homology i :=
  (restrictHomologyIso f (baseChangeComplex f P) i).symm ≪≫
    homologyMapIso
      ((Functor.mapHomologicalComplexCompIso (restrictExtendIso f) (ComplexShape.up ℤ)).app P) i

private noncomputable def restrictBaseChangeTensorHomologyIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (N : ModuleCat.{max u v} S) (i : ℤ) :
    (ModuleCat.restrictScalars f).obj ((baseChangeTensorComplex f P N).homology i) ≅
      (((tensorLeft ((ModuleCat.restrictScalars f).obj N)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i :=
  (restrictHomologyIso f (baseChangeTensorComplex f P N) i).symm ≪≫
    homologyMapIso
      (((Functor.mapHomologicalComplexCompIso
          (Iso.refl ((moduleTensorBifunctor.{u, v} S).obj N ⋙
            ModuleCat.restrictScalars f)) (ComplexShape.up ℤ)).app _) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.extendScalars.{u, u, max u v} f ⋙
            (moduleTensorBifunctor.{u, v} S).obj N ⋙
              ModuleCat.restrictScalars f)) (ComplexShape.up ℤ)).app P ≪≫
        (Functor.mapHomologicalComplexCompIso (restrictTensorExtendIso f N)
          (ComplexShape.up ℤ)).app P) i

private theorem baseChangeComplex_isZero {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hle : ∀ i : ℤ, 0 < i → IsZero (P.X i)) (i : ℤ) (hi : 0 < i) :
    IsZero ((baseChangeComplex f P).X i) :=
  (ModuleCat.extendScalars f).map_isZero (hle i hi)

private theorem baseChangeComplex_free {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : ∀ i : ℤ, Module.Free R (P.X i)) (i : ℤ) :
    Module.Free S ((baseChangeComplex f P).X i) := by
  let _ : Algebra R S := f.toAlgebra
  have : Module.Free R (P.X i) := hP i
  show Module.Free S (TensorProduct R S (P.X i))
  infer_instance

/-! ### The change-of-rings spectral sequence -/

/-- **Stacks 068F.** Let `R → S` be a homomorphism of commutative rings, `M` an `R`-module and
`N` an `S`-module. There is a free resolution `P^•` of `M` over `R` such that the homology of
`P^• ⊗_R S`, with its natural `S`-module structure, computes `Tor_*^R(M, S)`, and there is a
spectral sequence
```
Tor_n^S(Tor_m^R(M, S), N) ⟹ Tor_{n+m}^R(M, N).
```
The second-page identification is displayed, and the last clause records the abutment; the two
`Nonempty` clauses before it record that the homology of the two base-changed complexes is
`Tor_*^R(M, S)` and `Tor_*^R(M, N)` after restricting scalars along `R → S`. -/
@[stacks 068F,
  ega "III 6.9.3" "special case",
  ega "III 6.9.3.2" "special case",
  ega "III 6.9.3.3" "special case", sga "7 VIII 2.1" "special case"]
public theorem exists_tor_change_of_rings_spectral_sequence
    (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{max u v} R) (N : ModuleCat.{max u v} S) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ),
      ∃ (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) 0).obj M)
        (_ : QuasiIso ε),
      (∀ i : ℤ, Module.Free R (P.X i)) ∧
      (∀ i : ℤ, 0 < i → IsZero (P.X i)) ∧
      Nonempty (P.homology 0 ≅ M) ∧
      (∀ i : ℤ, i ≠ 0 → IsZero (P.homology i)) ∧
      (∀ i : ℤ, Nonempty
        ((ModuleCat.restrictScalars f).obj ((baseChangeComplex f P).homology (-i)) ≅
          TorInDegree.{u, v} R i M
            ((ModuleCat.restrictScalars f).obj (ModuleCat.of S (ULift.{v} S))))) ∧
      (∀ n : ℤ, Nonempty
        ((ModuleCat.restrictScalars f).obj
            ((baseChangeTensorComplex f P N).homology (-n)) ≅
          TorInDegree.{u, v} R n M ((ModuleCat.restrictScalars f).obj N))) ∧
      ∃ (E : FirstTorSpectralSequence (ModuleCat.{max u v} S))
        (_e₂ : ∀ i j : ℤ, (E.page 2).X (i, j) ≅
          TorInDegree.{u, v} S j ((baseChangeComplex f P).homology (-i)) N),
        HomologicalSpectralSequenceAbutsTo E
          (fun n ↦ (baseChangeTensorComplex f P N).homology (-n)) := by
  obtain ⟨P, ε, hε, hfree, hle, h0, hother⟩ := freeResolutionBridge R M
  have : QuasiIso ε := hε
  have : P.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff P 0).2 hle
  have hPflat : P.KFlat := kFlat_of_free_of_bounded P hfree hle
  refine ⟨P, ε, hε, hfree, hle, h0, hother,
    fun i ↦ ⟨restrictBaseChangeHomologyIso f P (-i) ≪≫ torIsoOfKFlatResolution ε hPflat _ i⟩,
    fun n ↦ ⟨restrictBaseChangeTensorHomologyIso f P N (-n) ≪≫
      torIsoOfKFlatResolution ε hPflat _ n⟩, ?_⟩
  let K := baseChangeComplex f P
  have hKflat : K.KFlat :=
    kFlat_of_free_of_bounded K (baseChangeComplex_free f P hfree)
      (baseChangeComplex_isZero f P hle)
  let K' := ((ModuleCat.uliftFunctor.{max u v, max u v} S).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  obtain ⟨Q, η, hη, _, _, _, _, E, _, e₂, _, _, _, SS, _, _, _, _, _, hSS, _, _⟩ :=
    exists_spectral_sequences_tor_homology_and_terms S K ⟨0, baseChangeComplex_isZero f P hle⟩ N
  refine ⟨E, fun i j ↦ e₂ i j ≪≫ torInDegreeIso S j
    (HomologicalComplex.homologyMapIso (uliftComplexIso S K) (-i)) (uliftModuleIso S N), ?_⟩
  let η' := η ≫
    (HomologicalComplex.single (ModuleCat.{max u v} S) (ComplexShape.up ℤ) 0).map
      (uliftModuleIso S N).hom
  have : QuasiIso η := hη
  have : QuasiIso η' := inferInstance
  let eT : HomologicalComplex.mapBifunctor K' Q
      (moduleTensorBifunctor S) (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor K Q
      (moduleTensorBifunctor S) (ComplexShape.up ℤ) :=
    (((moduleTensorBifunctor S).map₂CochainComplex).mapIso
      (uliftComplexIso S K)).app Q
  exact (TorFiltrationData.abutsTo_homology SS hSS).of_iso (fun n ↦
    HomologicalComplex.homologyMapIso eT (-n) ≪≫
      tensorResolutionHomologyIso K hKflat N η' (-n))

end Construction

end CochainComplex.Tor.ChangeOfRingsSpectralSequence

end
