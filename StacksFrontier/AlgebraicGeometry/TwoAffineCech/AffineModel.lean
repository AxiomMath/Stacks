module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.OverScheme
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.ModuleIso

/-!
# A finite projective model of the two-term Čech complex over an arbitrary affine base

Let `X` be proper over a field `k`, covered by two affine opens, and let `L` be an invertible
module on `X_A` for an arbitrary `k`-algebra `A`. Then the two-term Čech differential of `L` has
a finite projective model over `A`: `L` descends to `X_{A'}` for a finitely generated, hence
Noetherian, subalgebra `A'`
(`Stacks.FGSubalgebraLimit.exists_fg_subalgebra_isInvertible_pullback_iso`), over which the model
exists, and the model base changes.

Consequently, when every fibre has vanishing `H¹`, the differential is onto and its kernel
`H⁰(X_A, L)` is a finite projective `A`-module, commuting with arbitrary base change, whose rank
at a point is the dimension of `H⁰` of the fibre.

## Main results

* `Stacks.TwoAffineCech.hasFiniteProjectiveModel_affine`: the two-term Čech differential of an
  invertible module on `X_A` has a finite projective model over `A`.
* `Stacks.TwoAffineCech.surjective_cechD_of_fibres`: if `H¹` vanishes on every fibre, the Čech
  differential is surjective.
* `Stacks.TwoAffineCech.projective_ker_cechD_of_fibres`: if `H¹` vanishes on every fibre,
  `H⁰(X_A, L)` is a finite projective `A`-module.
* `Stacks.TwoAffineCech.baseChangeKerCechDEquiv`: under the same hypothesis, `H⁰` commutes with
  arbitrary base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.FibreCohomology
open scoped TensorProduct

universe u

namespace Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A]

/-- A morphism property stable under base change passes from `X` to the projection `X_A ⟶ Spec A`.
-/
private theorem fst_of_baseChange {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] (hf : P fX)
    {A : Type u} [CommRing A] [Algebra k A] :
    P (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).flip hf

/-- The projection `X_A ⟶ X` is affine. -/
private theorem isAffineHom_snd_baseChange {k : Type u} [Field k] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) {A : Type u} [CommRing A] [Algebra k A] :
    IsAffineHom (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX)
    (isAffineHom_of_isAffine _)

/-- An invertible module on a scheme flat over `Z` is flat over `Z`. -/
private theorem isFlatOver_of_isInvertible {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Flat f] (L : Y.Modules)
    [L.IsQuasicoherent] (hL : SheafOfModules.IsInvertible _ _ L) :
    IsFlatOver f.toLRSHom.toShHom L :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L hL)
  AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f L

include hU hUaff in
/-- **The two-term Čech differential of an invertible module on `X_A` has a finite projective
model**, for an arbitrary `k`-algebra `A`. -/
theorem hasFiniteProjectiveModel_affine
    (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).Modules)
    [Stacks.Ample.IsInvertibleModule _ L] :
    Stacks.TwoTermComplex.HasFiniteProjectiveModel
      (cechD (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX)
        (fun i => pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX ⁻¹ᵁ U i) L) := by
  have : CompactSpace X := ⟨QuasiCompact.isCompact_preimage (f := fX) _ isOpen_univ isCompact_univ⟩
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  obtain ⟨A', hA', L', hL', p, hp₁, hp₂, ⟨e⟩⟩ :=
    Stacks.FGSubalgebraLimit.exists_fg_subalgebra_isInvertible_pullback_iso X fX L
      (isInvertible_of_isInvertibleModule L)
  set fA := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX
  set pA := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX
  set fA' := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX
  set pA' := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX
  have hsqA' : IsPullback fA' pA' (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX :=
    IsPullback.of_hasPullback _ _
  have hcomp : Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A')) =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    rw [← Spec.map_comp]; rfl
  have hbig : IsPullback (p ≫ pA') fA fX
      (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A'))) := by
    rw [hp₂, hcomp]; exact (IsPullback.of_hasPullback _ _).flip
  have hsq : IsPullback p fA fA' (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom)) :=
    IsPullback.of_right hbig hp₁ hsqA'.flip
  have : IsProper fA' := fst_of_baseChange fX (P := @IsProper) inferInstance
  have : IsSeparated fA' := fst_of_baseChange fX (P := @IsSeparated) inferInstance
  have : IsSeparated fA := fst_of_baseChange fX (P := @IsSeparated) inferInstance
  have : IsAffineHom pA' := isAffineHom_snd_baseChange fX
  have : IsAffineHom pA := isAffineHom_snd_baseChange fX
  have : Algebra.FiniteType k A' := (Subalgebra.fg_iff_finiteType _).1 hA'
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing k A'
  have : IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX) :=
    LocallyOfFiniteType.isLocallyNoetherian fA'
  have : L'.IsFinitePresentation := @Stacks.Divisors.isFinitePresentation_of_isInvertible _ L' hL'
  have : L'.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation L' inferInstance
  have : L'.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L').1
  have : Flat fA' := fst_of_baseChange fX (P := @Flat) inferInstance
  have hflat : IsFlatOver fA'.toLRSHom.toShHom L' := isFlatOver_of_isInvertible fA' L' hL'
  have hU' := top_eq_iSup_preimage pA' U hU
  have hUaff' : ∀ i, IsAffineOpen (pA' ⁻¹ᵁ U i) := fun i => (hUaff i).preimage pA'
  have hmodel := hasFiniteProjectiveModel fA' (fun i => pA' ⁻¹ᵁ U i) L' hU' hUaff' hflat
  have := flat_X fA' (fun i => pA' ⁻¹ᵁ U i) L' hUaff' hflat 1
  let φ : A' →+* A := (Subalgebra.val A').toRingHom
  let : Algebra A' A := φ.toAlgebra
  have h1 := (hmodel.baseChange A).of_linearEquiv _ _ _
    (baseChangeEquiv_comm φ fA' fA p hsq (fun i => pA' ⁻¹ᵁ U i) L' hUaff')
  have hcover : (fun i => p ⁻¹ᵁ (pA' ⁻¹ᵁ U i)) = fun i => pA ⁻¹ᵁ U i := by
    funext i
    rw [← Scheme.Hom.comp_preimage, hp₂]
  have h2 : Stacks.TwoTermComplex.HasFiniteProjectiveModel
      (cechD fA (fun i => pA ⁻¹ᵁ U i) ((Scheme.Modules.pullback p).obj L')) :=
    hcover ▸ h1
  exact h2.of_linearEquiv _ _ _ (cechD_congr fA (fun i => pA ⁻¹ᵁ U i) e.symm)

end Stacks.TwoAffineCech

namespace Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A]
  (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).Modules)
  [Stacks.Ample.IsInvertibleModule _ L]

/-- The projection `X_A ⟶ Spec A` of the base change of `X` to `Spec A`. -/
abbrev baseFamily : pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX ⟶ Spec (.of A) :=
  pullback.fst _ _

/-- The two-affine cover of `X_A` induced by the cover of `X`. -/
abbrev baseCover :
    Cover.{u} → (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).Opens :=
  fun i => pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX ⁻¹ᵁ U i

omit [IsProper fX] [Stacks.Ample.IsInvertibleModule _ L] in
include hU in
/-- The opens `baseCover fX U i` cover `X_A`. -/
theorem iSup_baseCover : (⊤ : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).Opens) =
    ⨆ i, baseCover fX U (A := A) i :=
  top_eq_iSup_preimage _ U hU

omit [IsProper fX] [Stacks.Ample.IsInvertibleModule _ L] in
include hUaff in
/-- Each open `baseCover fX U i` of `X_A` is affine. -/
theorem isAffineOpen_baseCover (i : Cover.{u}) : IsAffineOpen (baseCover fX U (A := A) i) :=
  have : IsAffineHom (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX) :=
    isAffineHom_snd_baseChange fX
  (hUaff i).preimage _

/-- The projection `X_A ⟶ Spec A` is separated. -/
instance : IsSeparated (baseFamily fX (A := A)) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).flip
    inferInstance

/-- The projection `X_A ⟶ Spec A` is proper. -/
instance : IsProper (baseFamily fX (A := A)) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).flip
    inferInstance

omit [IsProper fX] in
/-- An invertible module on `X_A` is flat over `A`. -/
theorem isFlatOver_of_isInvertibleModule :
    IsFlatOver (baseFamily fX (A := A)).toLRSHom.toShHom L := by
  have : Flat (baseFamily fX (A := A)) := fst_of_baseChange fX (P := @Flat) inferInstance
  exact isFlatOver_of_isInvertible _ L (isInvertible_of_isInvertibleModule L)

include hUaff in
/-- The terms of the two-term Čech complex of an invertible module on `X_A` are flat. -/
theorem flat_cech (n : ℕ) :
    Module.Flat A
      ((Stacks.Cech.alternatingCechModuleComplex (baseFamily fX) (baseCover fX U) L).X n) :=
  have : L.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  flat_X (baseFamily fX) (baseCover fX U) L (isAffineOpen_baseCover fX U hUaff)
    (isFlatOver_of_isInvertibleModule fX L) n

include hU hUaff in
/-- **If `H¹` vanishes on every fibre, the two-term Čech differential is onto.** -/
theorem surjective_cechD_of_fibres
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology (baseFamily fX) L x 1) = 0) :
    Function.Surjective (cechD (baseFamily fX) (baseCover fX U) L) := by
  have : L.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have hmodel := hasFiniteProjectiveModel_affine fX U hU hUaff L
  have := flat_cech fX U hUaff L 1
  refine hmodel.surjective_of_forall fun p => ?_
  have hfin := hmodel.finiteDimensional_coker_fibre p
  have hdim := finrank_cohomologyOverField_one_eq (baseFamily fX) (baseCover fX U) L
    (iSup_baseCover fX U hU) (isAffineOpen_baseCover fX U hUaff) p
  rw [finrank_fibre_eq_fibreCohomology, h] at hdim
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact Module.finrank_zero_iff.1 hdim.symm

include hU hUaff in
/-- **If `H¹` vanishes on every fibre, `H⁰(X_A, L)`, the kernel of the two-term Čech
differential, is a finite projective `A`-module.** -/
theorem projective_ker_cechD_of_fibres
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology (baseFamily fX) L x 1) = 0) :
    Module.Finite A (LinearMap.ker (cechD (baseFamily fX) (baseCover fX U) L)) ∧
      Module.Projective A (LinearMap.ker (cechD (baseFamily fX) (baseCover fX U) L)) :=
  have := flat_cech fX U hUaff L 1
  (hasFiniteProjectiveModel_affine fX U hU hUaff L).projective_ker
    (surjective_cechD_of_fibres fX U hU hUaff L h)

end Stacks.TwoAffineCech

namespace Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A]
  (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).Modules)
  [Stacks.Ample.IsInvertibleModule _ L]

include hU hUaff in
/-- **`H⁰` commutes with base change when every fibre has vanishing `H¹`**: for any
`A`-algebra `B`, `B ⊗_A H⁰(X_A, L)` is the kernel of the base-changed Čech differential. -/
noncomputable def baseChangeKerCechDEquiv
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology (baseFamily fX) L x 1) = 0) (B : Type u) [CommRing B] [Algebra A B] :
    B ⊗[A] LinearMap.ker (cechD (baseFamily fX) (baseCover fX U) L) ≃ₗ[B]
      LinearMap.ker ((cechD (baseFamily fX) (baseCover fX U) L).baseChange B) :=
  haveI := flat_cech fX U hUaff L 1
  Stacks.TwoTermComplex.baseChangeKerEquiv _ (surjective_cechD_of_fibres fX U hU hUaff L h) B

include hU hUaff in
/-- **The rank of `H⁰(X_A, L)` at a point is the dimension of `H⁰` of the fibre**, when every
fibre has vanishing `H¹`. -/
theorem finrank_residueField_tensor_ker_cechD
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology (baseFamily fX) L x 1) = 0) (p : PrimeSpectrum A) :
    Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (cechD (baseFamily fX) (baseCover fX U) L)) =
      Module.finrank ((Spec (.of A)).residueField (specPoint p))
        (fibreCohomology (baseFamily fX) L (specPoint p) 0) := by
  have : L.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  rw [(baseChangeKerCechDEquiv fX U hU hUaff L h p.asIdeal.ResidueField).finrank_eq,
    ← finrank_fibre_eq_fibreCohomology,
    finrank_cohomologyOverField_zero_eq (baseFamily fX) (baseCover fX U) L
      (iSup_baseCover fX U hU) (isAffineOpen_baseCover fX U hUaff) p]

end Stacks.TwoAffineCech
