module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessSetup
public import StacksFrontier.AlgebraicGeometry.Cube.GlueTrivial
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleDegreeZero
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.Homology.Perfect.ConeDegreeZeroLift
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent

/-!
# Face cocycles in the openness step of the theorem of the cube

Let `k` be a field, `X` and `Y` schemes over `k` with rational points `x` and `y`, `R` a
`k`-algebra, and `L` a module on `Q = (X ×_k Y) ×_k Spec R` whose restriction to the face `X_R`
(respectively `Y_R`) is trivial, and let `𝔭` be a prime of `R`. This file shows that every
degree-zero cocycle of the base change `κ(𝔭) ⊗_R DX` of the Čech complex of the face restriction
is, after multiplication by an element `t ∉ 𝔭`, the image of a degree-zero cocycle of `DX`
(respectively `DY`). This is an input of the openness step
([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)) of the theorem of the cube.

## Main results

* `AlgebraicGeometry.Cube.Openness.exists_lift_DX`, `exists_lift_DY`: face cocycles lift up to a
  unit.
* `AlgebraicGeometry.Cube.Openness.exists_lift_of_nonempty_iso_unit`: the general statement, for
  the Čech complex of a trivial module on a finite affine cover of a scheme separated over
  `Spec R` whose fibre over `𝔭` has functions `κ(𝔭)`.

## Implementation notes

The degree-zero cocycles of the fibre of the Čech complex are the sections of the module on the
fibre (`Stacks.Cech.range_sectionsToAlternatingₗ`, through the base-change isomorphism of Čech
cochains `Stacks.Cech.alternatingCechModuleObjBaseChangeIso`). For a trivial module these form
the one-dimensional `κ(𝔭)`-space spanned by the pullback of the trivializing section
(`AlgebraicGeometry.Cube.Openness.exists_eq_smul_pullbackSections`), and an element of `κ(𝔭)` is
a fraction `a / t` with `t ∉ 𝔭`. The face families are affine and cover the faces because the
second (respectively first) coordinate of a face is constant at a rational point, whose preimage
of an open of `Y` (respectively `X`) is empty or everything.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Cube.Openness

/-- Every element of the residue field `κ(𝔭)` is a fraction `a / t` with `t ∉ 𝔭`. -/
theorem exists_mul_eq_algebraMap_residueField {R : Type u} [CommRing R] (𝔭 : Ideal R)
    [𝔭.IsPrime] (c : 𝔭.ResidueField) :
    ∃ a t : R, t ∉ 𝔭 ∧ algebraMap R 𝔭.ResidueField t * c = algebraMap R 𝔭.ResidueField a := by
  obtain ⟨⟨x, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (R ⧸ 𝔭)) c
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : R ⧸ 𝔭)
  refine ⟨a, t, fun htp =>
    nonZeroDivisors.coe_ne_zero s (ht ▸ Ideal.Quotient.eq_zero_iff_mem.mpr htp), ?_⟩
  rw [IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) 𝔭.ResidueField,
    IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) 𝔭.ResidueField a]
  simp only [Ideal.Quotient.algebraMap_eq, ht]
  rwa [mul_comm]

/-- An open of the spectrum of a field is empty or everything. -/
theorem eq_bot_or_eq_top_of_spec_field {K : Type u} [Field K] (V : (Spec (.of K)).Opens) :
    V = ⊥ ∨ V = ⊤ := by
  by_cases h : (V : Set (Spec (.of K))).Nonempty
  · right
    obtain ⟨v, hv⟩ := h
    ext w
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim w v]
  · left
    ext w
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hw => h ⟨w, hw⟩

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [Algebra k R]
  {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)

/-- The face `jX : X_R ⟶ Q` followed by the projection `Q ⟶ X ×_k Y` is the projection
`X_R ⟶ X` followed by `x' ↦ (x', y)`. -/
theorem jX_fst : jX f g y hy R ≫ pullback.fst (pullback.fst f g ≫ f) (φR R) =
    pullback.fst f (φR R) ≫ pullback.lift (𝟙 X) (f ≫ y) (by simp [hy]) := by
  rw [jX]
  exact pullback.lift_fst _ _ _

/-- The preimage of `W s` under the face `jX` is the intersection of the preimage of `UX s.1` with
the preimage of the constant `y⁻¹(UY s.2)`. -/
theorem jX_preimage_W (s : I × J) :
    jX f g y hy R ⁻¹ᵁ W f g R UX UY s =
      pullback.fst f (φR R) ⁻¹ᵁ UX s.1 ⊓
        (pullback.fst f (φR R) ≫ f) ⁻¹ᵁ (y ⁻¹ᵁ UY s.2) := by
  rw [W, ← Scheme.Hom.comp_preimage, jX_fst, Scheme.Hom.preimage_inf]
  simp only [← Scheme.Hom.comp_preimage, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    Category.comp_id]

/-- Preimages of the products of members of two open covers cover the source. -/
private theorem top_eq_iSup_preimage_inf {T : Scheme.{u}} (F : T ⟶ X) (G : T ⟶ Y)
    (hUX : ⊤ = ⨆ a, UX a) (hUY : ⊤ = ⨆ b, UY b) :
    (⊤ : T.Opens) = ⨆ s : I × J, F ⁻¹ᵁ UX s.1 ⊓ G ⁻¹ᵁ UY s.2 := by
  refine (top_le_iff.mp fun p _ => ?_).symm
  have hpa : F.base p ∈ (⨆ a, UX a) := hUX ▸ trivial
  have hpb : G.base p ∈ (⨆ b, UY b) := hUY ▸ trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hpa
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp hpb
  exact Opens.mem_iSup.mpr ⟨(a, b), ha, hb⟩

/-- The face family on `X_R` covers `X_R`. -/
theorem iSup_jX_preimage_W (hUX : ⊤ = ⨆ a, UX a) (hUY : ⊤ = ⨆ b, UY b) :
    (⊤ : (XR f R).Opens) = ⨆ s, jX f g y hy R ⁻¹ᵁ W f g R UX UY s := by
  simp only [jX_preimage_W]
  exact top_eq_iSup_preimage_inf UX UY (pullback.fst f (φR R)) (pullback.fst f (φR R) ≫ f ≫ y)
    hUX hUY

/-- The base change of a scheme over `k` to `Spec R` is affine over it. -/
theorem isAffineHom_pullback_fst_φR {T : Scheme.{u}} (h : T ⟶ Spec (.of k)) :
    IsAffineHom (pullback.fst h (φR (k := k) R)) :=
  @MorphismProperty.IsStableUnderBaseChange.of_isPullback _ _ @IsAffineHom
    isAffineHom_isStableUnderBaseChange _ _ _ _ _ _ _ _
    (IsPullback.of_hasPullback h (φR R)).flip inferInstance

/-- An affine open of a base change to `Spec R`, cut down by the preimage of an open of `Y` under
a constant map, is affine. -/
private theorem isAffineOpen_preimage_inf_const {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k))
    {V : Z.Opens} (hV : IsAffineOpen V) (c : Spec (.of k) ⟶ Y) (W : Y.Opens) :
    IsAffineOpen (pullback.fst h (φR R) ⁻¹ᵁ V ⊓ (pullback.fst h (φR R) ≫ h) ⁻¹ᵁ (c ⁻¹ᵁ W)) := by
  rcases eq_bot_or_eq_top_of_spec_field (c ⁻¹ᵁ W) with h' | h'
  · rw [h', Scheme.Hom.preimage_bot, inf_bot_eq]
    exact isAffineOpen_bot _
  · rw [h', Scheme.Hom.preimage_top, inf_top_eq]
    have := isAffineHom_pullback_fst_φR R h
    exact hV.preimage (pullback.fst h (φR R))

/-- The members of the face family on `X_R` are affine. -/
theorem isAffineOpen_jX_preimage_W (hUXa : ∀ a, IsAffineOpen (UX a)) (s : I × J) :
    IsAffineOpen (jX f g y hy R ⁻¹ᵁ W f g R UX UY s) := by
  rw [jX_preimage_W]
  exact isAffineOpen_preimage_inf_const R f (hUXa s.1) y (UY s.2)

/-- The face `jY : Y_R ⟶ Q` followed by the projection `Q ⟶ X ×_k Y` is the projection
`Y_R ⟶ Y` followed by `y' ↦ (x, y')`. -/
theorem jY_fst : jY f g x hx R ≫ pullback.fst (pullback.fst f g ≫ f) (φR R) =
    pullback.fst g (φR R) ≫ pullback.lift (g ≫ x) (𝟙 Y) (by simp [hx]) := by
  rw [jY]
  exact pullback.lift_fst _ _ _

/-- The preimage of `W s` under the face `jY` is the intersection of the preimage of the constant
`x⁻¹(UX s.1)` with the preimage of `UY s.2`. -/
theorem jY_preimage_W (s : I × J) :
    jY f g x hx R ⁻¹ᵁ W f g R UX UY s =
      (pullback.fst g (φR R) ≫ g) ⁻¹ᵁ (x ⁻¹ᵁ UX s.1) ⊓
        pullback.fst g (φR R) ⁻¹ᵁ UY s.2 := by
  rw [W, ← Scheme.Hom.comp_preimage, jY_fst, Scheme.Hom.preimage_inf]
  simp only [← Scheme.Hom.comp_preimage, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    Category.comp_id]

/-- The face family on `Y_R` covers `Y_R`. -/
theorem iSup_jY_preimage_W (hUX : ⊤ = ⨆ a, UX a) (hUY : ⊤ = ⨆ b, UY b) :
    (⊤ : (YR g R).Opens) = ⨆ s, jY f g x hx R ⁻¹ᵁ W f g R UX UY s := by
  simp only [jY_preimage_W]
  exact top_eq_iSup_preimage_inf UX UY (pullback.fst g (φR R) ≫ g ≫ x) (pullback.fst g (φR R))
    hUX hUY

/-- The members of the face family on `Y_R` are affine. -/
theorem isAffineOpen_jY_preimage_W (hUYa : ∀ b, IsAffineOpen (UY b)) (s : I × J) :
    IsAffineOpen (jY f g x hx R ⁻¹ᵁ W f g R UX UY s) := by
  rw [jY_preimage_W, inf_comm]
  exact isAffineOpen_preimage_inf_const R g (hUYa s.2) x (UX s.1)

section Core

open Stacks.Cech

variable {Z Z' : Scheme.{u}} (gp : Z' ⟶ Z) (M : Z.Modules)
  (e : M ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- The section of a trivial module corresponding to `1`. -/
abbrev trivSection : Γ(M, ⊤) := e.inv.app ⊤ (1 : Γ(Z, ⊤))

/-- **On a base change of a trivial module, the pulled-back trivializing section maps to `1`.** -/
theorem pullbackUnitIso_pullback_trivialization :
    ((Scheme.Modules.pullback gp).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso gp).hom.app
        (gp ⁻¹ᵁ ⊤) (pullbackSections gp M ⊤ (trivSection M e)) = (1 : Γ(Z', gp ⁻¹ᵁ ⊤)) := by
  have h1 := Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_naturality_module
    gp e.hom ⊤ (trivSection M e)
  have h2 : e.hom.app ⊤ (trivSection M e) = (1 : Γ(Z, ⊤)) :=
    (ConcreteCategory.comp_apply (e.inv.app ⊤) (e.hom.app ⊤) _).symm.trans
      (ConcreteCategory.congr_hom ((Scheme.Modules.Hom.comp_app e.inv e.hom (U := ⊤)).symm.trans
          (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) e.inv_hom_id)) (1 : Γ(Z, ⊤)))
  rw [h2] at h1
  have h3 := Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections gp
    (1 : Γ(Z, ⊤))
  rw [map_one] at h3
  exact ((ConcreteCategory.comp_apply (((Scheme.Modules.pullback gp).map e.hom).app (gp ⁻¹ᵁ ⊤))
    ((Scheme.Modules.pullbackUnitIso gp).hom.app (gp ⁻¹ᵁ ⊤)) _).trans (congrArg _ h1)).trans h3

include e in
/-- **The sections of a base change of a trivial module are the multiples of the pulled-back
trivializing section**, when a ring maps onto the functions of the base change. -/
theorem exists_eq_smul_pullbackSections {A : Type*} [CommRing A] (β : A →+* Γ(Z', gp ⁻¹ᵁ ⊤))
    (hβ : Function.Surjective β) (s : Γ((Scheme.Modules.pullback gp).obj M, gp ⁻¹ᵁ ⊤)) :
    ∃ c : A, s = β c • pullbackSections gp M ⊤ (trivSection M e) := by
  let eN := (Scheme.Modules.pullback gp).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso gp
  obtain ⟨c, hc⟩ := hβ (eN.hom.app (gp ⁻¹ᵁ ⊤) s)
  refine ⟨c, ?_⟩
  have hinv : ∀ a, eN.inv.app (gp ⁻¹ᵁ ⊤) (eN.hom.app (gp ⁻¹ᵁ ⊤) a) = a := fun a => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    rfl
  apply Function.LeftInverse.injective hinv
  rw [Scheme.Modules.Hom.app_smul, pullbackUnitIso_pullback_trivialization gp M e, hc]
  exact (mul_one (M := Γ(Z', gp ⁻¹ᵁ ⊤)) _).symm

end Core

section Lift

open Stacks.Cech StacksDraft.ConeLift

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of R)) [IsSeparated q]
  {ι : Type u} [Finite ι] (U : ι → Z.Opens) (hUa : ∀ i, IsAffineOpen (U i))
  (hU : (⊤ : Z.Opens) = ⨆ i, U i) (M : Z.Modules)
  (e : M ≅ SheafOfModules.unit Z.ringCatSheaf) (𝔭 : Ideal R) [𝔭.IsPrime]

/-- A `κ(𝔭)`-multiple of the base change of a cocycle is, after multiplication by some `t ∉ 𝔭`,
the image of a cocycle. -/
theorem exists_lift_of_eq_smul_one_tmul {C D : ModuleCat.{u} R} (d : C ⟶ D) (e0 : C)
    (he0 : d.hom e0 = 0) (z : bcObj (algebraMap R 𝔭.ResidueField) C) (c : 𝔭.ResidueField)
    (hz : z = c • show (ModuleCat.extendScalars (algebraMap R 𝔭.ResidueField)).obj C from
      (1 : 𝔭.ResidueField) ⊗ₜ[R] e0) :
    ∃ z' : C, d.hom z' = 0 ∧
      ∃ t : R, t ∉ 𝔭 ∧ (bcUnit (algebraMap R 𝔭.ResidueField) C).hom z' = t • z := by
  let ρ := algebraMap R 𝔭.ResidueField
  let w : (ModuleCat.extendScalars ρ).obj C := (1 : 𝔭.ResidueField) ⊗ₜ[R] e0
  obtain ⟨a, t, ht, hat⟩ := exists_mul_eq_algebraMap_residueField 𝔭 c
  refine ⟨a • e0, by rw [map_smul, he0, smul_zero], t, ht, ?_⟩
  have hL : (bcUnit ρ C).hom (a • e0) = ρ a • w :=
    ((bcUnit ρ C).hom.map_smul a e0).trans (ModuleCat.restrictScalars.smul_def ρ a _)
  rw [hL, hz]
  show ρ a • w = ρ t • (c • w)
  rw [smul_smul, hat]

include hUa hU e in
/-- **Degree-zero cocycles of the fibre of the Čech complex of a trivial module lift up to a
unit.** Let `q : Z ⟶ Spec R` be separated, `U` a finite affine open cover of `Z` and `M` a
trivial `𝒪_Z`-module, and suppose the functions on the fibre `Z_𝔭` are the elements of `κ(𝔭)`.
Then every degree-zero cocycle of `κ(𝔭) ⊗_R Č(U, M)` is, after multiplication by some `t ∉ 𝔭`,
the image of a degree-zero cocycle of `Č(U, M)`. -/
theorem exists_lift_of_nonempty_iso_unit
    (hfib : Function.Surjective (baseRingHom
      (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.ResidueField))))
      (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.ResidueField))) ⁻¹ᵁ ⊤)).hom) :
    ∀ z : bcObj (algebraMap R 𝔭.ResidueField) ((alternatingCechModuleComplex q U M).X 0),
      (bcMap (algebraMap R 𝔭.ResidueField) ((alternatingCechModuleComplex q U M).d 0 1)).hom z =
        0 →
      ∃ z' : (alternatingCechModuleComplex q U M).X 0,
        ((alternatingCechModuleComplex q U M).d 0 1).hom z' = 0 ∧
        ∃ t : R, t ∉ 𝔭 ∧ (bcUnit (algebraMap R 𝔭.ResidueField) _).hom z' = t • z := by
  intro z hz
  let ρ := algebraMap R 𝔭.ResidueField
  let ψ := Spec.map (CommRingCat.ofHom ρ)
  let fp := pullback.snd q ψ
  let gp := pullback.fst q ψ
  have hsq : IsPullback gp fp q ψ := IsPullback.of_hasPullback q ψ
  have : M.IsQuasicoherent := Stacks.Descent.isQuasicoherent_of_iso e.symm inferInstance
  let U' : ι → (pullback q ψ).Opens := fun i => gp ⁻¹ᵁ U i
  let M' := (Scheme.Modules.pullback gp).obj M
  have hbase := fun W => baseRingHom_comp_app ρ q fp gp hsq W
  let iso0 := alternatingCechModuleObjBaseChangeIso gp U U' (Equiv.refl ι) M (fun _ => rfl) ρ q fp
    hbase hsq hUa 0
  have hcomm := alternatingCechModuleObjBaseChangeIso_comm gp U U' (Equiv.refl ι) M
    (fun _ => rfl) ρ q fp hbase hsq hUa 0
  have hz' : (ModuleCat.extendScalars ρ).map (alternatingCechModuleDiff q U M 0) z = 0 := by
    rwa [← alternatingCechModuleComplex_d q U M 0]
  have hw : alternatingCechModuleD fp U' M' 0 (iso0.hom z) = 0 := by
    have h1 := ConcreteCategory.congr_hom hcomm z
    refine h1.trans ?_
    simp only [ModuleCat.hom_comp]
    exact (LinearMap.comp_apply _ _ z).trans ((congrArg _ hz').trans (map_zero _))
  have hUW' : ∀ i, U' i ≤ gp ⁻¹ᵁ ⊤ := fun i => Scheme.Hom.preimage_mono gp le_top
  have hUW : ∀ i, U i ≤ (⊤ : Z.Opens) := fun _ => le_top
  let := sectionsModule fp M' (gp ⁻¹ᵁ ⊤)
  let := cochainModule fp U' M' 0
  let := cochainModule fp U' M' 1
  let := sectionsModule q M ⊤
  let := cochainModule q U M 0
  let := cochainModule q U M 1
  obtain ⟨σ, hσ⟩ : iso0.hom z ∈ LinearMap.range (sectionsToAlternatingₗ fp U' M' hUW') := by
    rwa [range_sectionsToAlternatingₗ fp U' M' hUW' (by rw [hU, Scheme.Hom.preimage_iSup])]
  obtain ⟨c, hc⟩ := exists_eq_smul_pullbackSections gp M e (baseRingHom fp (gp ⁻¹ᵁ ⊤)).hom hfib σ
  let e0 := sectionsToAlternatingₗ q U M hUW (trivSection M e)
  let c' : 𝔭.ResidueField := c
  let w0 : (ModuleCat.extendScalars ρ).obj (alternatingCechModuleObj q U M 0) :=
    (1 : 𝔭.ResidueField) ⊗ₜ[R] e0
  have hz0 : z = c' • w0 := by
    apply iso0.toLinearEquiv.injective
    show iso0.hom.hom z = iso0.hom.hom (c' • w0)
    rw [map_smul]
    show iso0.hom.hom z = c' • iso0.hom.hom ((1 : 𝔭.ResidueField) ⊗ₜ[R] e0)
    rw [alternatingCechModuleObjBaseChangeIso_hom_one_tmul gp U U' (Equiv.refl ι) M
        (fun _ => rfl) ρ q fp hbase hsq hUa 0 e0,
      alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ q U M hUW gp U'
        (Equiv.refl ι) (fun _ => rfl) ρ fp hbase (trivSection M e), ← hσ, hc]
    exact map_smul (sectionsToAlternatingₗ fp U' M' hUW') c' _
  refine exists_lift_of_eq_smul_one_tmul 𝔭 _ e0 ?_ z c' hz0
  rw [alternatingCechModuleComplex_d]
  exact (range_sectionsToAlternatingₗ q U M hUW hU.le).le ⟨_, rfl⟩

end Lift

section Fibre

open Stacks.Cech

/-- **The base ring maps onto the functions on `Y`** when the canonical map to the global
sections is an isomorphism; read on any open equal to `⊤`. -/
theorem surjective_baseRingHom_of_isIso {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of A)) (hI : IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ h.appTop))
    (V : Y.Opens) (hV : V = ⊤) : Function.Surjective (baseRingHom h V).hom := by
  subst hV
  have hb : baseRingHom h ⊤ = (Scheme.ΓSpecIso (.of A)).inv ≫ h.appTop := by
    rw [baseRingHom, globalRingHom, show (homOfLE le_top : (⊤ : Y.Opens) ⟶ ⊤) = 𝟙 _ from rfl,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [hb]
  exact (ConcreteCategory.bijective_of_isIso _).2

end Fibre

section Faces

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  {I J : Type u} [Finite I] [Finite J] (UX : I → X.Opens) (UY : J → Y.Opens)
  (hUXa : ∀ a, IsAffineOpen (UX a)) (hUYa : ∀ b, IsAffineOpen (UY b))
  (hUX : ⊤ = ⨆ a, UX a) (hUY : ⊤ = ⨆ b, UY b)
  {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
  (L : (Q f g R).Modules) (𝔭 : PrimeSpectrum R)

open StacksDraft.ConeLift

omit [IsProper g] [GeometricallyIntegral g] [IsNoetherianRing R] in
include hUXa hUX hUY in
/-- **Face cocycles on `X_R` lift up to a unit.** If `L` is trivial on the face `X_R`, then every
degree-zero cocycle of `κ(𝔭) ⊗_R DX` is, after multiplication by some `t ∉ 𝔭`, the image of a
degree-zero cocycle of `DX`. -/
theorem exists_lift_DX
    (hfX : Nonempty ((Scheme.Modules.pullback (jX f g y hy R)).obj L ≅ SheafOfModules.unit _)) :
    ∀ z : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((DX f g y hy R UX UY L).X 0),
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((DX f g y hy R UX UY L).d 0 1)).hom z = 0 →
      ∃ z' : (DX f g y hy R UX UY L).X 0, ((DX f g y hy R UX UY L).d 0 1).hom z' = 0 ∧
        ∃ t : R, t ∉ 𝔭.asIdeal ∧ (bcUnit (algebraMap R 𝔭.asIdeal.ResidueField) _).hom z' = t • z :=
  exists_lift_of_nonempty_iso_unit (qX f R) _
    (isAffineOpen_jX_preimage_W f g y hy R UX UY hUXa)
    (iSup_jX_preimage_W f g y hy R UX UY hUX hUY) _ hfX.some 𝔭.asIdeal
    (surjective_baseRingHom_of_isIso _
      (isIso_globalSections_of_geometricallyIntegral _ _) _ (Scheme.Hom.preimage_top _))

omit [IsProper f] [GeometricallyIntegral f] [IsNoetherianRing R] in
include hUYa hUX hUY in
/-- **Face cocycles on `Y_R` lift up to a unit.** The statement of
`AlgebraicGeometry.Cube.Openness.exists_lift_DX` for the face `Y_R`. -/
theorem exists_lift_DY
    (hfY : Nonempty ((Scheme.Modules.pullback (jY f g x hx R)).obj L ≅ SheafOfModules.unit _)) :
    ∀ z : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((DY f g x hx R UX UY L).X 0),
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((DY f g x hx R UX UY L).d 0 1)).hom z = 0 →
      ∃ z' : (DY f g x hx R UX UY L).X 0, ((DY f g x hx R UX UY L).d 0 1).hom z' = 0 ∧
        ∃ t : R, t ∉ 𝔭.asIdeal ∧ (bcUnit (algebraMap R 𝔭.asIdeal.ResidueField) _).hom z' = t • z :=
  exists_lift_of_nonempty_iso_unit (qY g R) _
    (isAffineOpen_jY_preimage_W f g x hx R UX UY hUYa)
    (iSup_jY_preimage_W f g x hx R UX UY hUX hUY) _ hfY.some 𝔭.asIdeal
    (surjective_baseRingHom_of_isIso _
      (isIso_globalSections_of_geometricallyIntegral _ _) _ (Scheme.Hom.preimage_top _))

end Faces

end AlgebraicGeometry.Cube.Openness

end

end
