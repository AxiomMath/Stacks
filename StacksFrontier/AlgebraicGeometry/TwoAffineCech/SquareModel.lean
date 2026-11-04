module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.AffineModel
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# The two-term Čech engine on an arbitrary affine base change

The results of `StacksFrontier.AlgebraicGeometry.TwoAffineCech.AffineModel` are stated for the
chosen fibre product `X_A = Spec A ×_k X`. This file restates them for any cartesian square
`XT ⟶ X`, `XT ⟶ Spec A` over `X ⟶ Spec k` and `Spec A ⟶ Spec k`, with the two-affine cover of
`XT` pulled back from `X`, by transporting the finite projective model along the comparison
isomorphism `XT ≅ X_A`.

## Main results

* `Stacks.TwoAffineCech.hasFiniteProjectiveModel_of_isPullback`: the two-term Čech differential
  of an invertible module on `XT` has a finite projective model.
* `Stacks.TwoAffineCech.surjective_cechD_of_isPullback`: if `H¹` vanishes on every fibre, the
  differential is surjective.
* `Stacks.TwoAffineCech.projective_ker_cechD_of_isPullback`: if `H¹` vanishes on every fibre,
  its kernel `H⁰` is a finite projective `A`-module.
* `Stacks.TwoAffineCech.finrank_residueField_tensor_ker_cechD_of_isPullback`: under the same
  hypothesis, the rank of `H⁰` at a point is the dimension of `H⁰` of the fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.FibreCohomology
open scoped TensorProduct

universe u

namespace Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A] {XT : Scheme.{u}} (gT : XT ⟶ X)
  (fT : XT ⟶ Spec (.of A))
  (hT : IsPullback gT fT fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  (L : XT.Modules) [Stacks.Ample.IsInvertibleModule XT L]

/-- The two-affine cover of `XT` pulled back from `X`. -/
abbrev sqCover : Cover.{u} → XT.Opens := fun i => gT ⁻¹ᵁ U i

include hU in
/-- The opens `gT ⁻¹ᵁ U i` cover `XT`. -/
theorem iSup_sqCover : (⊤ : XT.Opens) = ⨆ i, sqCover U gT i := by
  rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]

omit [IsProper fX] in
include hT hUaff in
/-- Each pulled-back open `gT ⁻¹ᵁ U i` is affine. -/
theorem isAffineOpen_sqCover (i : Cover.{u}) : IsAffineOpen (sqCover U gT i) :=
  have : IsAffineHom gT := MorphismProperty.of_isPullback hT.flip (isAffineHom_of_isAffine _)
  (hUaff i).preimage _

include hT in
/-- The base change `fT : XT ⟶ Spec A` of `fX` is separated. -/
theorem isSeparated_of_isPullback' : IsSeparated fT :=
  MorphismProperty.of_isPullback hT inferInstance

include hT in
/-- The base change `fT : XT ⟶ Spec A` of `fX` is proper. -/
theorem isProper_of_isPullback' : IsProper fT :=
  MorphismProperty.of_isPullback hT inferInstance

omit [IsProper fX] in
include hT in
/-- An invertible module on a base change of `X` to an affine scheme is flat over the base. -/
theorem isFlatOver_of_isPullback : IsFlatOver fT.toLRSHom.toShHom L := by
  have hL' : SheafOfModules.IsInvertible _ _ L := isInvertible_of_isInvertibleModule L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L hL')
  have : Flat fT := MorphismProperty.of_isPullback hT inferInstance
  exact AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree _ L

include hT hUaff in
/-- Each term of the alternating Čech complex of `L` for the pulled-back cover is a flat
`A`-module. -/
theorem flat_cech_of_isPullback (n : ℕ) :
    Module.Flat A ((Stacks.Cech.alternatingCechModuleComplex fT (sqCover U gT) L).X n) :=
  have : IsSeparated fT := isSeparated_of_isPullback' fX gT fT hT
  flat_X fT (sqCover U gT) L (isAffineOpen_sqCover fX U hUaff gT fT hT)
    (isFlatOver_of_isPullback fX gT fT hT L) n

include hU hUaff hT in
/-- **The two-term Čech differential of an invertible module on any base change of `X` to an
affine scheme has a finite projective model.** -/
theorem hasFiniteProjectiveModel_of_isPullback :
    Stacks.TwoTermComplex.HasFiniteProjectiveModel (cechD fT (sqCover U gT) L) := by
  let e : XT ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX := hT.flip.isoPullback
  have he₁ : e.hom ≫ pullback.fst _ _ = fT := hT.flip.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd _ _ = gT := hT.flip.isoPullback_hom_snd
  let LA := (Scheme.Modules.pullback e.inv).obj L
  have hmodel := hasFiniteProjectiveModel_affine fX U hU hUaff LA
  have hsq : IsPullback e.hom fT (baseFamily fX (A := A))
      (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    have : Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _ := by
      rw [← Spec.map_id]; rfl
    rw [this]
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id]; exact he₁
  have : IsSeparated (baseFamily fX (A := A)) := inferInstance
  have := flat_cech fX U hUaff LA 1
  have hbc := hmodel.baseChange A
  have hcomm := baseChangeEquiv_comm (RingHom.id A) (baseFamily fX) fT e.hom hsq
    (baseCover fX U) LA (isAffineOpen_baseCover fX U hUaff)
  have h1 := hbc.of_linearEquiv _ _ _ hcomm
  have hcover : (fun i => e.hom ⁻¹ᵁ (baseCover fX U (A := A) i)) = sqCover U gT := by
    funext i
    rw [← Scheme.Hom.comp_preimage, he₂]
  have h2 : Stacks.TwoTermComplex.HasFiniteProjectiveModel
      (cechD fT (sqCover U gT) ((Scheme.Modules.pullback e.hom).obj LA)) :=
    hcover ▸ h1
  let iso : (Scheme.Modules.pullback e.hom).obj LA ≅ L :=
    (Scheme.Modules.pullbackComp e.hom e.inv).app L ≪≫
      (Scheme.Modules.pullbackCongr e.hom_inv_id).app L ≪≫ (Scheme.Modules.pullbackId XT).app L
  exact h2.of_linearEquiv _ _ _ (cechD_congr fT (sqCover U gT) iso)

include hU hUaff hT in
/-- **If `H¹` vanishes on every fibre, the two-term Čech differential is onto.** -/
theorem surjective_cechD_of_isPullback
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology fT L x 1) = 0) :
    Function.Surjective (cechD fT (sqCover U gT) L) := by
  have : IsProper fT := isProper_of_isPullback' fX gT fT hT
  have hmodel := hasFiniteProjectiveModel_of_isPullback fX U hU hUaff gT fT hT L
  have := flat_cech_of_isPullback fX U hUaff gT fT hT L 1
  refine hmodel.surjective_of_forall fun p => ?_
  have hfin := hmodel.finiteDimensional_coker_fibre p
  have hdim := finrank_cohomologyOverField_one_eq fT (sqCover U gT) L
    (iSup_sqCover U hU gT) (isAffineOpen_sqCover fX U hUaff gT fT hT) p
  rw [finrank_fibre_eq_fibreCohomology, h] at hdim
  have hsub := Module.finrank_zero_iff.1 hdim.symm
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact hsub

include hU hUaff hT in
/-- **If `H¹` vanishes on every fibre, `H⁰`, the kernel of the two-term Čech differential, is a
finite projective module.** -/
theorem projective_ker_cechD_of_isPullback
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology fT L x 1) = 0) :
    Module.Finite A (LinearMap.ker (cechD fT (sqCover U gT) L)) ∧
      Module.Projective A (LinearMap.ker (cechD fT (sqCover U gT) L)) :=
  have := flat_cech_of_isPullback fX U hUaff gT fT hT L 1
  (hasFiniteProjectiveModel_of_isPullback fX U hU hUaff gT fT hT L).projective_ker
    (surjective_cechD_of_isPullback fX U hU hUaff gT fT hT L h)

include hU hUaff hT in
/-- **The rank of `H⁰` at a point is the dimension of `H⁰` of the fibre**, when every fibre has
vanishing `H¹`. -/
theorem finrank_residueField_tensor_ker_cechD_of_isPullback
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology fT L x 1) = 0) (p : PrimeSpectrum A) :
    Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (cechD fT (sqCover U gT) L)) =
      Module.finrank ((Spec (.of A)).residueField (specPoint p))
        (fibreCohomology fT L (specPoint p) 0) := by
  have : IsProper fT := isProper_of_isPullback' fX gT fT hT
  have := flat_cech_of_isPullback fX U hUaff gT fT hT L 1
  rw [(Stacks.TwoTermComplex.baseChangeKerEquiv _
      (surjective_cechD_of_isPullback fX U hU hUaff gT fT hT L h)
      p.asIdeal.ResidueField).finrank_eq,
    ← finrank_fibre_eq_fibreCohomology,
    finrank_cohomologyOverField_zero_eq fT (sqCover U gT) L
      (iSup_sqCover U hU gT) (isAffineOpen_sqCover fX U hUaff gT fT hT) p]

end Stacks.TwoAffineCech
