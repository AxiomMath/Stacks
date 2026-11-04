module

public import StacksFrontier.AlgebraicGeometry.RelativeSegre.Glue
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.Quasicoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative Segre morphism is a closed immersion

Let `H` and `G` be quasi-coherent modules of finite type on a scheme `X`. The relative Segre
morphism `σ : 𝐏(H) ×_X 𝐏(G) ⟶ 𝐏(H ⊗ G)` of `Stacks.RelativeSegre.segre` is a morphism over `X`
and a closed immersion. This is the relative form of Stacks 01WD.

Over the standard open `D₊(a ⊗ b)` of the chart of `𝐏(H ⊗ G)` over an affine open `U` of `X`,
`σ` restricts to the piece `D₊(a) ×_U D₊(b)`, and there it is the spectrum of the surjection
`Γ(U, Sym(H ⊗ G))_{(a ⊗ b)} ⟶ Γ(U, Sym H)_{(a)} ⊗ Γ(U, Sym G)_{(b)}`. These standard opens cover
the image of `σ`, which is closed because `σ` is proper.

## Main results

* `Stacks.RelativeSegre.segre_toBase`: `σ` is a morphism over `X`.
* `Stacks.RelativeSegre.surjective_segreRingHom`: the Segre ring map of a piece is surjective.
* `Stacks.RelativeSegre.isClosedImmersion_segre`: `σ` is a closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProjBridge
open scoped TensorProduct

universe u

namespace Stacks.RelativeSegre

variable {X : Scheme.{u}}

section Base

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent]

/-- The chart of `𝐏(E)` over an affine open `U` lies over `Spec Γ(X, U) ⟶ X`. -/
theorem chart_toBase (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    (bun E).chart U hU ≫ (bun E).toBase =
      Proj.toSpecZero ((alg E).grading U) ≫
        Spec.map (Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf (alg E) U) ≫
          hU.fromSpec := by
  rw [((bun E).chart_isPullback U hU).w]
  show (Proj.toSpecZero _ ≫
    Spec.map (Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf (alg E) U) ≫
      hU.isoSpec.inv) ≫ U.ι = _
  rw [Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι]

/-- The Segre morphism of a piece lies over `X`. -/
theorem pieceSegre_toBase {U : X.Opens} (hU : IsAffineOpen U) (a : (alg H).grading U 1)
    (b : (alg G).grading U 1) :
    pieceSegre H G hU a b ≫ (bun (tens H G)).toBase =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (pieceRing H G a b))) ≫ hU.fromSpec := by
  rw [pieceSegre, Category.assoc, chart_toBase, Proj.fromOfGlobalSections_toSpecZero_assoc,
    ← Spec.map_comp_assoc]
  have hring : Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf (alg (tens H G)) U ≫
      CommRingCat.ofHom ((segreΓ H G hU a b).comp (algebraMap _ _)) =
      CommRingCat.ofHom (algebraMap Γ(X, U) (pieceRing H G a b)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (pieceRing H G a b))).inv := by
    ext r
    show segreΓ H G hU a b ((Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf
      (alg (tens H G)) U r : (alg (tens H G)).grading U 0) : (alg (tens H G)).sectionRing U) = _
    rw [Stacks.AlgebraicGeometry.ProjBundleSurjection.coe_strZeroSheaf_apply, segreΓ,
      RingHom.comp_apply, segreRingHom_strHom]
    rfl
  rw [hring, Spec.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Spec _).toSpecΓ, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- A piece lies over `X` along `Spec Γ(X, U) ⟶ X`. -/
theorem pieceMap_toBase {U : X.Opens} (hU : IsAffineOpen U) (a : (alg H).grading U 1)
    (b : (alg G).grading U 1) :
    pieceMap H G hU a b ≫ pullback.fst (bun H).toBase (bun G).toBase ≫ (bun H).toBase =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (pieceRing H G a b))) ≫ hU.fromSpec := by
  rw [pieceMap_fst_assoc, chartι_toBase, ← Spec.map_comp_assoc]
  rfl

/-- **The relative Segre morphism lies over `X`.** -/
theorem segre_toBase :
    segre H G ≫ (bun (tens H G)).toBase =
      pullback.fst (bun H).toBase (bun G).toBase ≫ (bun H).toBase := by
  refine (pieceCover H G).hom_ext _ _ fun (i : PieceIndex H G) => ?_
  show pieceMap H G i.hU i.a i.b ≫ _ = pieceMap H G i.hU i.a i.b ≫ _
  rw [← Category.assoc, pieceMap_segre, pieceSegre_toBase, pieceMap_toBase]

end Base

/-! ### Surjectivity of the Segre ring map -/

section Surjective

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

/-- **Every element of `Γ(U, Sym E)_{(a)}` lies in a subring containing the structure map and the
ratios `h / a`.** -/
theorem away_mem_of_ratios (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (a : (alg E).grading U 1) {S : Type*} [Ring S]
    (φ : Away ((alg E).grading U) (a : (alg E).sectionRing U) →+* S) (T : Subring S)
    (h0 : ∀ r : Γ(X, U), φ (awayAlgHom E a r) ∈ T)
    (h1 : ∀ h : Γ(E, U), φ (ratioOf E hU a h) ∈ T) (z : Away ((alg E).grading U)
      (a : (alg E).sectionRing U)) : φ z ∈ T := by
  set e := Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hU
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
  have key : ∀ (n : ℕ), ∀ y ∈ SymPow.symmetricPower n Γ(X, U) Γ(E, U),
      ∀ (x : (alg E).sectionRing U) (hx : x ∈ (alg E).grading U (n • 1)), e x = y →
        φ (Away.mk ((alg E).grading U) a.2 n x hx) ∈ T := by
    intro n
    induction n with
    | zero =>
      intro y hy x hx hxy
      have h1' : SymPow.symmetricPower 0 Γ(X, U) Γ(E, U) =
          LinearMap.range (Algebra.linearMap Γ(X, U) (SymmetricAlgebra Γ(X, U) Γ(E, U))) :=
        (pow_zero _).trans Submodule.one_eq_range
      rw [h1'] at hy
      obtain ⟨r, rfl⟩ := hy
      have hx' : x = (alg E).strHom U r := by
        rw [← Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap E
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) hU r]
        exact (e.symm_apply_apply x).symm.trans (congrArg e.symm hxy)
      have : Away.mk ((alg E).grading U) a.2 0 x hx = awayAlgHom E a r := by
        apply HomogeneousLocalization.val_injective
        rw [Away.val_mk, val_awayAlgHom, hx']
        congr 1
      rw [this]
      exact h0 r
    | succ n ih =>
      intro y hy
      have hsucc : SymPow.symmetricPower (n + 1) Γ(X, U) Γ(E, U) =
          SymPow.symmetricPower n Γ(X, U) Γ(E, U) *
            LinearMap.range (SymmetricAlgebra.ι Γ(X, U) Γ(E, U)) := pow_succ _ _
      rw [hsucc] at hy
      refine Submodule.mul_induction_on' (C := fun y _ => ∀ (x : (alg E).sectionRing U)
        (hx : x ∈ (alg E).grading U ((n + 1) • 1)), e x = y →
          φ (Away.mk ((alg E).grading U) a.2 (n + 1) x hx) ∈ T) ?_ ?_ hy
      · intro y₁ hy₁ z hz x hx hxy
        obtain ⟨h, rfl⟩ := hz
        have hy₁' : e.symm y₁ ∈ (alg E).grading U (n • 1) := by
          rw [smul_eq_mul, mul_one]
          refine (Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv E hU _ n
            _).mp ?_
          rwa [RingEquiv.apply_symm_apply]
        have hx' : x = e.symm y₁ * deg1 E hU h :=
          (e.symm_apply_apply x).symm.trans ((congrArg e.symm hxy).trans (map_mul e.symm _ _))
        have : Away.mk ((alg E).grading U) a.2 (n + 1) x hx =
            Away.mk ((alg E).grading U) a.2 n (e.symm y₁) hy₁' * ratioOf E hU a h := by
          apply HomogeneousLocalization.val_injective
          rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, ratioOf, ratio,
            Away.val_mk, Localization.mk_mul, hx']
          congr 1
          exact Subtype.ext ((pow_succ _ _).trans (congrArg _ (pow_one _).symm))
        rw [this, map_mul]
        exact T.mul_mem (ih y₁ hy₁ _ hy₁' (e.apply_symm_apply y₁)) (h1 h)
      · intro y₁ hy₁ y₂ hy₂ ih₁ ih₂ x hx hxy
        have hm : ∀ w ∈ SymPow.symmetricPower n Γ(X, U) Γ(E, U) *
            LinearMap.range (SymmetricAlgebra.ι Γ(X, U) Γ(E, U)),
            e.symm w ∈ (alg E).grading U ((n + 1) • 1) := by
          intro w hw
          rw [smul_eq_mul, mul_one]
          refine (Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv E hU _
            (n + 1) _).mp ?_
          rw [RingEquiv.apply_symm_apply, hsucc]
          exact hw
        have hx' : x = e.symm y₁ + e.symm y₂ :=
          (e.symm_apply_apply x).symm.trans ((congrArg e.symm hxy).trans (map_add e.symm _ _))
        have : Away.mk ((alg E).grading U) a.2 (n + 1) x hx =
            Away.mk ((alg E).grading U) a.2 (n + 1) (e.symm y₁) (hm y₁ hy₁) +
              Away.mk ((alg E).grading U) a.2 (n + 1) (e.symm y₂) (hm y₂ hy₂) := by
          apply HomogeneousLocalization.val_injective
          rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
            Localization.add_mk_self, hx']
        rw [this, map_add]
        exact T.add_mem (ih₁ _ _ (e.apply_symm_apply y₁)) (ih₂ _ _ (e.apply_symm_apply y₂))
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective ((alg E).grading U) a.2 z
  refine key n (e x) ?_ x hx rfl
  refine (Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv E hU _ n x).mpr ?_
  simpa only [smul_eq_mul, mul_one] using hx

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
  (hU : IsAffineOpen U) (a : (alg H).grading U 1) (b : (alg G).grading U 1)

/-- **The Segre ring map of a piece is surjective.** -/
theorem surjective_segreRingHom : Function.Surjective (segreRingHom H G hU a b) := by
  rw [← RingHom.range_eq_top]
  set T := (segreRingHom H G hU a b).range
  have hL : ∀ z, Algebra.TensorProduct.includeLeftRingHom z ∈ T := by
    refine away_mem_of_ratios H hU a _ T (fun r => ⟨(alg (tens H G)).strHom U r, ?_⟩)
      (fun h => ⟨deg1Tensor H G hU h (secOf hU G b), ?_⟩)
    · rw [segreRingHom_strHom]
      rfl
    · rw [segreRingHom_deg1Tensor, ratioOf_secOf]
      rfl
  have hR : ∀ z, (Algebra.TensorProduct.includeRight (R := Γ(X, U))
      (A := Away ((alg H).grading U) (a : (alg H).sectionRing U))
      (B := Away ((alg G).grading U) (b : (alg G).sectionRing U)) : _ →ₐ[Γ(X, U)] _).toRingHom z
        ∈ T := by
    refine away_mem_of_ratios G hU b _ T (fun r => ⟨(alg (tens H G)).strHom U r, ?_⟩)
      (fun g => ⟨deg1Tensor H G hU (secOf hU H a) g, ?_⟩)
    · rw [segreRingHom_strHom]
      exact (Algebra.TensorProduct.includeRight (R := Γ(X, U))
        (A := Away ((alg H).grading U) (a : (alg H).sectionRing U))
        (B := Away ((alg G).grading U) (b : (alg G).sectionRing U))).commutes r |>.symm
    · rw [segreRingHom_deg1Tensor, ratioOf_secOf]
      rfl
  refine eq_top_iff.mpr fun w _ => ?_
  induction w using TensorProduct.induction_on with
  | zero => exact T.zero_mem
  | tmul x y =>
    have : x ⊗ₜ[Γ(X, U)] y = Algebra.TensorProduct.includeLeftRingHom x *
        (Algebra.TensorProduct.includeRight (R := Γ(X, U))).toRingHom y := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact T.mul_mem (hL x) (hR y)
  | add x y hx hy => exact T.add_mem (hx trivial) (hy trivial)

end Surjective

/-! ### The Segre morphism of a piece onto the standard open `D₊(a ⊗ b)` -/

section PieceClosed

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
  (hU : IsAffineOpen U) (a : (alg H).grading U 1) (b : (alg G).grading U 1)

/-- The standard open `D₊(a ⊗ b)` of the chart of `𝐏(H ⊗ G)` over `U`, mapped into `𝐏(H ⊗ G)`. -/
def unitChart : Spec (CommRingCat.of (Away ((alg (tens H G)).grading U) (unitElt H G hU a b))) ⟶
    (bun (tens H G)).scheme :=
  Proj.awayι _ (unitElt H G hU a b) (unitElt_mem H G hU a b) Nat.one_pos ≫
    (bun (tens H G)).chart U hU

/-- The standard open `D₊(a ⊗ b)` is an open immersion into `𝐏(H ⊗ G)`. -/
instance : IsOpenImmersion (unitChart H G hU a b) := by
  have := isOpenImmersion_chart (tens H G) hU
  unfold unitChart
  infer_instance

/-- The image of the morphism of the Segre ring map of a piece lies in the standard open
`D₊(a ⊗ b)` of `Proj Γ(U, Sym(H ⊗ G))`. -/
theorem range_fromOfGlobalSections_segre :
    Set.range (Proj.fromOfGlobalSections ((alg (tens H G)).grading U) (segreΓ H G hU a b)
        (map_irrelevant_segreΓ H G hU a b)) ⊆
      Set.range (Proj.awayι _ (unitElt H G hU a b) (unitElt_mem H G hU a b) Nat.one_pos) := by
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ Proj.fromOfGlobalSections ((alg (tens H G)).grading U) (segreΓ H G hU a b)
      (map_irrelevant_segreΓ H G hU a b) ⁻¹ᵁ Proj.basicOpen _ (unitElt H G hU a b) := by
    rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos (unitElt_mem H G hU a b),
      segreΓ_unitElt, Scheme.basicOpen_one]
    trivial
  show _ ∈ (Proj.awayι _ (unitElt H G hU a b) (unitElt_mem H G hU a b) Nat.one_pos).opensRange
  rw [Proj.opensRange_awayι]
  exact hy

/-- The Segre ring map of a piece, into the global sections of its spectrum, is surjective. -/
theorem surjective_segreΓ : Function.Surjective (segreΓ H G hU a b) := by
  intro x
  obtain ⟨y, hy⟩ := surjective_segreRingHom H G hU a b
    ((Scheme.ΓSpecIso (CommRingCat.of (pieceRing H G a b))).hom x)
  refine ⟨y, ?_⟩
  rw [segreΓ, RingHom.comp_apply, hy]
  exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (pieceRing H G a b))) x

/-- The basic open of the image of `a ⊗ b` under the Segre ring map is the whole spectrum of the
piece. -/
theorem basicOpen_segreΓ_unitElt :
    (Spec (CommRingCat.of (pieceRing H G a b))).basicOpen
      (segreΓ H G hU a b (unitElt H G hU a b)) = ⊤ := by
  rw [segreΓ_unitElt, Scheme.basicOpen_one]

/-- The Segre morphism of a piece, as a morphism to the standard open `D₊(a ⊗ b)`. -/
def pieceToUnit : Spec (CommRingCat.of (pieceRing H G a b)) ⟶
    Spec (CommRingCat.of (Away ((alg (tens H G)).grading U) (unitElt H G hU a b))) :=
  (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_segreΓ_unitElt H G hU a b).symm).hom ≫
    Proj.toBasicOpenOfGlobalSections _ (segreΓ H G hU a b) rfl Nat.one_pos
      (unitElt_mem H G hU a b) ≫
    (Proj.basicOpenIsoSpec _ (unitElt H G hU a b) (unitElt_mem H G hU a b) Nat.one_pos).hom

/-- Followed by the inclusion of `D₊(a ⊗ b)` into `Proj Γ(U, Sym(H ⊗ G))`, `pieceToUnit` is the
morphism of the Segre ring map of the piece. -/
@[reassoc]
theorem pieceToUnit_awayι :
    pieceToUnit H G hU a b ≫
        Proj.awayι _ (unitElt H G hU a b) (unitElt_mem H G hU a b) Nat.one_pos =
      Proj.fromOfGlobalSections ((alg (tens H G)).grading U) (segreΓ H G hU a b)
        (map_irrelevant_segreΓ H G hU a b) := by
  have e1 := Proj.basicOpen_ι_comp_fromOfGlobalSections ((alg (tens H G)).grading U)
    (segreΓ H G hU a b) (map_irrelevant_segreΓ H G hU a b) Nat.one_pos (unitElt_mem H G hU a b)
  have e2 : (Proj.basicOpenIsoSpec _ (unitElt H G hU a b) (unitElt_mem H G hU a b)
      Nat.one_pos).hom ≫ Proj.awayι _ (unitElt H G hU a b) (unitElt_mem H G hU a b) Nat.one_pos =
      (Proj.basicOpen _ (unitElt H G hU a b)).ι := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  unfold pieceToUnit
  simp only [Category.assoc]
  rw [e2, ← e1, Scheme.isoOfEq_hom_ι_assoc, ← Scheme.topIso_hom, Iso.inv_hom_id_assoc]

/-- Followed by `unitChart`, `pieceToUnit` is the Segre morphism `pieceSegre` of the piece. -/
@[reassoc]
theorem pieceToUnit_unitChart :
    pieceToUnit H G hU a b ≫ unitChart H G hU a b = pieceSegre H G hU a b := by
  rw [unitChart, ← Category.assoc, pieceToUnit_awayι]
  rfl

/-- **The Segre morphism of a piece is a closed immersion onto `D₊(a ⊗ b)`.** -/
theorem isClosedImmersion_pieceToUnit : IsClosedImmersion (pieceToUnit H G hU a b) := by
  have hci := Proj.isClosedImmersion_toBasicOpenOfGlobalSections ((alg (tens H G)).grading U)
    (segreΓ H G hU a b) (surjective_segreΓ H G hU a b) (unitElt_mem H G hU a b) rfl
    (segreΓ_unitElt H G hU a b)
  unfold pieceToUnit
  infer_instance

end PieceClosed

/-! ### The preimage of `D₊(a ⊗ b)` is the piece `D₊(a) ×_U D₊(b)` -/

section Preimage

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

/-- The ratio `x / a'` of degree-one elements is the localization element of Mathlib's
`AlgebraicGeometry.Proj.awayι_preimage_basicOpen`. -/
theorem ratio_eq_isLocalizationElem (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens}
    (a x : (alg E).grading U 1) :
    ratio E a x = Away.isLocalizationElem a.2 x.2 := by
  apply HomogeneousLocalization.val_injective
  simp only [ratio, Away.val_mk, pow_one]

/-- A point of the standard chart of `a'` at which the ratio `x / a'` is a unit lies in the
standard chart of `x`. -/
theorem mem_range_chartι_of_unit (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (a x : (alg E).grading U 1)
    (q : Spec (CommRingCat.of (Away ((alg E).grading U) (a : (alg E).sectionRing U))))
    (hq : q ∈ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv (ratio E a x))) :
    chartι E hU a q ∈ Set.range (chartι E hU x) := by
  rw [basicOpen_eq_of_affine, ratio_eq_isLocalizationElem,
    ← Proj.awayι_preimage_basicOpen _ a.2 Nat.one_pos x.2 Nat.one_pos] at hq
  obtain ⟨q', hq'⟩ : Proj.awayι _ (a : (alg E).sectionRing U) a.2 Nat.one_pos q ∈
      (Proj.awayι _ (x : (alg E).sectionRing U) x.2 Nat.one_pos).opensRange := by
    rw [Proj.opensRange_awayι]
    exact hq
  refine ⟨q', ?_⟩
  rw [chartι, chartι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hq']

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent]

/-- On the spectrum of the piece, the basic open of `x ⊗ y` is the intersection of the preimages
under the two projections of the basic opens of `x` and of `y`. -/
theorem basicOpen_tmul {U : X.Opens} (a : (alg H).grading U 1) (b : (alg G).grading U 1)
    (x : Away ((alg H).grading U) (a : (alg H).sectionRing U))
    (y : Away ((alg G).grading U) (b : (alg G).sectionRing U)) :
    (Spec (CommRingCat.of (pieceRing H G a b))).basicOpen
        ((Scheme.ΓSpecIso _).inv (x ⊗ₜ[Γ(X, U)] y)) =
      prL H G a b ⁻¹ᵁ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv x) ⊓
        prR H G a b ⁻¹ᵁ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv y) := by
  have hxy : x ⊗ₜ[Γ(X, U)] y = Algebra.TensorProduct.includeLeftRingHom x *
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := Γ(X, U))
        (A := Away ((alg H).grading U) (a : (alg H).sectionRing U))
        (B := Away ((alg G).grading U) (b : (alg G).sectionRing U)))) y := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [hxy, map_mul, Scheme.basicOpen_mul, Scheme.preimage_basicOpen_top,
    Scheme.preimage_basicOpen_top]
  congr 2
  · exact congrArg (fun k => k.hom x)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := Γ(X, U))
          (A := Away ((alg H).grading U) (a : (alg H).sectionRing U))
          (B := Away ((alg G).grading U) (b : (alg G).sectionRing U)))))
  · exact congrArg (fun k => k.hom y)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := Γ(X, U))
          (A := Away ((alg H).grading U) (a : (alg H).sectionRing U))
          (B := Away ((alg G).grading U) (b : (alg G).sectionRing U))))))

/-- **The preimage under the relative Segre morphism of the standard open `D₊(a ⊗ b)` is the
piece `D₊(a) ×_U D₊(b)`.** -/
theorem preimage_unitChart (i : PieceIndex H G) :
    segre H G ⁻¹ᵁ (unitChart H G i.hU i.a i.b).opensRange =
      (pieceMap H G i.hU i.a i.b).opensRange := by
  have := isOpenImmersion_chart (tens H G) i.hU
  apply le_antisymm
  · rintro z ⟨w, hw⟩
    have hzU : (bun H).toBase (pullback.fst (bun H).toBase (bun G).toBase z) ∈ i.U := by
      rw [← Scheme.Hom.comp_apply, ← segre_toBase, Scheme.Hom.comp_apply, ← hw, unitChart,
        Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (bun (tens H G)).toBase, chart_toBase,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact i.hU.range_fromSpec.subset ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := exists_mem_range_chartι H i.hU _ hzU
    have hzU' : (bun G).toBase (pullback.snd (bun H).toBase (bun G).toBase z) ∈ i.U := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      exact hzU
    obtain ⟨b', hb'⟩ := exists_mem_range_chartι G i.hU _ hzU'
    obtain ⟨y, rfl⟩ : z ∈ Set.range (pieceMap H G i.hU a' b') := by
      rw [range_pieceMap]
      exact ⟨ha', hb'⟩
    have h1 : Proj.fromOfGlobalSections ((alg (tens H G)).grading i.U)
        (segreΓ H G i.hU a' b') (map_irrelevant_segreΓ H G i.hU a' b') y =
          Proj.awayι _ (unitElt H G i.hU i.a i.b) (unitElt_mem H G i.hU i.a i.b) Nat.one_pos w := by
      apply ((bun (tens H G)).chart i.U i.hU).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      show pieceSegre H G i.hU a' b' y = unitChart H G i.hU i.a i.b w
      rw [hw, ← pieceMap_segre H G ⟨i.U, i.hU, a', b'⟩]
      rfl
    have h2 : y ∈ (Spec _).basicOpen (segreΓ H G i.hU a' b' (unitElt H G i.hU i.a i.b)) := by
      rw [← Proj.fromOfGlobalSections_preimage_basicOpen _ _
        (map_irrelevant_segreΓ H G i.hU a' b') Nat.one_pos (unitElt_mem H G i.hU i.a i.b)]
      show _ ∈ Proj.basicOpen _ _
      rw [h1, ← Proj.opensRange_awayι _ _ (unitElt_mem H G i.hU i.a i.b) Nat.one_pos]
      exact ⟨w, rfl⟩
    rw [segreΓ, RingHom.comp_apply, unitElt, segreRingHom_deg1Tensor, basicOpen_tmul] at h2
    have hA : ratioOf H i.hU a' (secOf i.hU H i.a) = ratio H a' i.a := by
      rw [ratioOf]
      exact congrArg (ratio H a') (Subtype.ext (deg1_secOf i.hU H i.a))
    have hB : ratioOf G i.hU b' (secOf i.hU G i.b) = ratio G b' i.b := by
      rw [ratioOf]
      exact congrArg (ratio G b') (Subtype.ext (deg1_secOf i.hU G i.b))
    rw [hA, hB] at h2
    show _ ∈ Set.range (pieceMap H G i.hU i.a i.b)
    rw [range_pieceMap]
    refine ⟨?_, ?_⟩
    · show pullback.fst (bun H).toBase (bun G).toBase (pieceMap H G i.hU a' b' y) ∈
        Set.range (chartι H i.hU i.a)
      rw [← Scheme.Hom.comp_apply, pieceMap_fst]
      exact mem_range_chartι_of_unit H i.hU a' i.a _ h2.1
    · show pullback.snd (bun H).toBase (bun G).toBase (pieceMap H G i.hU a' b' y) ∈
        Set.range (chartι G i.hU i.b)
      rw [← Scheme.Hom.comp_apply, pieceMap_snd]
      exact mem_range_chartι_of_unit G i.hU b' i.b _ h2.2
  · rintro _ ⟨y, rfl⟩
    refine ⟨pieceToUnit H G i.hU i.a i.b y, ?_⟩
    rw [← Scheme.Hom.comp_apply, pieceToUnit_unitChart, ← pieceMap_segre H G i,
      Scheme.Hom.comp_apply]

end Preimage

/-! ### The relative Segre morphism is a closed immersion -/

section ClosedImmersion

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

/-- The degree-one element of a section determines the section. -/
theorem deg1_injective (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (deg1 E hU) := fun _ _ h =>
  SymmetricAlgebra.ι_injective _ _ ((Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hU
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)).symm.injective h)

/-- The section attached to the degree-one element of a section `h` is `h`. -/
theorem secOf_deg1' (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (h : Γ(E, U)) : secOf hU E (deg1' E hU h) = h :=
  deg1_injective E hU (deg1_secOf hU E (deg1' E hU h))

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent]

/-- **The standard opens `D₊(a ⊗ b)` cover the chart** `Proj Γ(U, Sym(H ⊗ G))`. -/
theorem iSup_basicOpen_unitElt_eq_top {U : X.Opens} (hU : IsAffineOpen U) :
    ⨆ p : (alg H).grading U 1 × (alg G).grading U 1,
      Proj.basicOpen ((alg (tens H G)).grading U) (unitElt H G hU p.1 p.2) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun p => ⟨1, unitElt_mem H G hU p.1 p.2⟩) ?_
  refine eq_top_iff.mpr ((Stacks.SymGraded.adjoin_grading_one_eq_top (tens H G) U
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent (tens H G)) hU).symm.le.trans ?_)
  refine Algebra.adjoin_le fun x hx => ?_
  obtain ⟨q, rfl⟩ := exists_deg1_eq hU (tens H G) ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := (Stacks.SectionTensorFormula.tensorSectionEquiv H G hU).surjective q
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    simp only [deg1, map_zero]
    exact Subalgebra.zero_mem _
  | tmul h g =>
    rw [Stacks.SectionTensorFormula.tensorSectionEquiv_tmul]
    refine Algebra.subset_adjoin ⟨(deg1' H hU h, deg1' G hU g), ?_⟩
    show deg1Tensor H G hU (secOf hU H (deg1' H hU h)) (secOf hU G (deg1' G hU g)) = _
    rw [secOf_deg1', secOf_deg1']
    rfl
  | add t₁ t₂ ih₁ ih₂ =>
    rw [map_add, deg1_add]
    exact Subalgebra.add_mem _ (ih₁ (deg1_mem _ hU _)) (ih₂ (deg1_mem _ hU _))

/-- The standard opens `D₊(a ⊗ b)` of the charts of `𝐏(H ⊗ G)` cover `𝐏(H ⊗ G)`. -/
theorem exists_mem_range_unitChart (w : (bun (tens H G)).scheme) :
    ∃ i : PieceIndex H G, w ∈ Set.range (unitChart H G i.hU i.a i.b) := by
  obtain ⟨U, hU', hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show (bun (tens H G)).toBase w ∈ (⊤ : X.Opens) from trivial)
  have hU : IsAffineOpen U := hU'
  have := isOpenImmersion_chart (tens H G) hU
  have hw : w ∈ (bun (tens H G)).chart U hU ''ᵁ ⊤ := by
    rw [Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top]
    exact hxU
  obtain ⟨t, -, rfl⟩ := hw
  have ht : t ∈ ⨆ p : (alg H).grading U 1 × (alg G).grading U 1,
      Proj.basicOpen ((alg (tens H G)).grading U) (unitElt H G hU p.1 p.2) := by
    rw [iSup_basicOpen_unitElt_eq_top H G hU]
    trivial
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
  rw [← Proj.opensRange_awayι _ _ (unitElt_mem H G hU p.1 p.2) Nat.one_pos] at hp
  obtain ⟨q, rfl⟩ := hp
  exact ⟨⟨U, hU, p.1, p.2⟩, q, rfl⟩

/-- The open cover of `𝐏(H ⊗ G)` by the standard opens `D₊(a ⊗ b)`. -/
def unitCover : (bun (tens H G)).scheme.OpenCover :=
  Scheme.Cover.mkOfCovers (PieceIndex H G)
    (fun i => Spec (CommRingCat.of
      (Away ((alg (tens H G)).grading i.U) (unitElt H G i.hU i.a i.b))))
    (fun i => unitChart H G i.hU i.a i.b)
    (exists_mem_range_unitChart H G)
    (fun _ => inferInstance)

/-- The square formed by a piece, the standard open `D₊(a ⊗ b)` and the relative Segre morphism is
cartesian. -/
theorem isPullback_pieceToUnit (i : PieceIndex H G) :
    IsPullback (pieceMap H G i.hU i.a i.b) (pieceToUnit H G i.hU i.a i.b) (segre H G)
      (unitChart H G i.hU i.a i.b) :=
  (IsOpenImmersion.isPullback (pieceToUnit H G i.hU i.a i.b) (pieceMap H G i.hU i.a i.b)
    (unitChart H G i.hU i.a i.b) (segre H G)
    ((pieceMap_segre H G i).trans (pieceToUnit_unitChart H G i.hU i.a i.b).symm)
    (preimage_unitChart H G i)).flip

/-- **The relative Segre morphism `𝐏(H) ×_X 𝐏(G) ⟶ 𝐏(H ⊗ G)` is a closed immersion** (the
relative form of Stacks 01WD). -/
@[ega "II 4.3.3"]
theorem isClosedImmersion_segre : IsClosedImmersion (segre H G) := by
  refine IsZariskiLocalAtTarget.of_openCover (unitCover H G) fun (i : PieceIndex H G) => ?_
  have h := isPullback_pieceToUnit H G i
  have e : pullback.snd (segre H G) (unitChart H G i.hU i.a i.b) =
      h.isoPullback.inv ≫ pieceToUnit H G i.hU i.a i.b := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  show IsClosedImmersion (pullback.snd (segre H G) (unitChart H G i.hU i.a i.b))
  rw [e]
  have := isClosedImmersion_pieceToUnit H G i.hU i.a i.b
  infer_instance

end ClosedImmersion

end Stacks.RelativeSegre

end
