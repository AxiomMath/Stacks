module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.BoxSectionsAffine
public import
  StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProductQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Transport

/-!
# The Künneth formula for quasi-coherent modules over a field

Let `k` be a field, `X` and `Y` quasi-compact schemes over `k` with affine diagonal, `ℱ` a
quasi-coherent `𝒪_X`-module and `𝒢` a quasi-coherent `𝒪_Y`-module. Then
`Hⁿ(X ×_k Y, pr₁^*ℱ ⊗ pr₂^*𝒢) ≅ ⨁_{p + q = n} Hᵖ(X, ℱ) ⊗_k H^q(Y, 𝒢)` [Stacks, Tag 0BED].

## The proof

Choose finite affine open coverings `𝒰` of `X` and `𝒱` of `Y`; since `X` and `Y` have affine
diagonal, their finite intersections are affine, and so are those of the covering `𝒲` of
`X ×_k Y` by the `U_i × V_j`. The cohomology of a quasi-coherent module is therefore computed by
these coverings ([Stacks, Tag 01XD]; `Stacks.CechKunneth.cechEquiv`). On products of affine opens
`Γ(U × V, ℱ ⊠ 𝒢) = Γ(U, ℱ) ⊗_k Γ(V, 𝒢)` (`Stacks.CechKunneth.bijective_boxMap_app`), so the Čech
complex of `𝒲` with coefficients in `ℱ ⊠ 𝒢` is the Čech complex, for the product family, of the
presheaf `(U, V) ↦ Γ(U, ℱ) ⊗_k Γ(V, 𝒢)` on pairs of opens. For that presheaf the Alexander–Whitney
product `⨁_{p+q=n} Ȟᵖ(𝒰, ℱ) ⊗_k Ȟ^q(𝒱, 𝒢) ⟶ Ȟⁿ(𝒲, ℱ ⊠ 𝒢)` — the Čech-level form of the map of the
source, the cup product of the pullbacks of the two classes ([Stacks, Tag 0BEE]) — is an
isomorphism by the dévissage of `Stacks.CechKunneth.bijective_kunnethMap`.

## Main definitions

* `Stacks.CechKunneth.cohomologyK`: the cohomology `Hⁿ(X, ℱ)` of a module on a scheme over `k`,
  as a `k`-module; it is Mathlib's right derived functor of global sections, with scalars
  restricted along `k = Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)`.
* `Stacks.CechKunneth.kunnethIsoOfCovers`: the Künneth isomorphism for given finite affine
  coverings.
* `Stacks.CechKunneth.kunnethIsoOfAffineDiagonal`: **the Künneth isomorphism**, [Stacks, Tag 0BED].

## Main results

* `Stacks.CechKunneth.kunnethIsoOfCovers_symm_lof_tmul`: on the classes of Čech
  cocycles of the chosen coverings the inverse isomorphism is the Alexander–Whitney product of
  the cocycles, read as sections of `ℱ ⊠ 𝒢`.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 0BEE](https://stacks.math.columbia.edu/tag/0BEE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct
open Stacks.Cech.Hypercohomology

universe u

namespace Stacks.CechKunneth

/-! ### Finite affine coverings -/

section Cover

variable (X : Scheme.{u})

/-- A finite covering of a scheme by affine opens. -/
structure FiniteAffineCover where
  /-- The index type. -/
  I : Type u
  [fintype : Fintype I]
  [decEq : DecidableEq I]
  /-- The members of the covering. -/
  U : I → X.Opens
  /-- Every member of the covering is affine. -/
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  /-- The members of the covering cover the scheme. -/
  iSup_eq : ⊤ = ⨆ i, U i

attribute [instance] FiniteAffineCover.fintype FiniteAffineCover.decEq

/-- **A quasi-compact scheme has a finite covering by affine opens.** -/
theorem nonempty_finiteAffineCover [CompactSpace X] : Nonempty (FiniteAffineCover X) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => (V : X.Opens).isOpen)
    (fun x _ => by
      have hx : x ∈ (⨆ V : X.affineOpens, (V : X.Opens)) := top_eq_iSup_affineOpens X ▸ trivial
      obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine ⟨⟨t, fun i => (i.1 : X.Opens), fun i => i.1.2, (eq_top_iff.2 fun x _ => ?_).symm⟩⟩
  obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, hxV⟩

/-- A chosen finite covering of a quasi-compact scheme by affine opens. -/
def finiteAffineCover [CompactSpace X] : FiniteAffineCover X :=
  (nonempty_finiteAffineCover X).some

/-- **On a scheme with affine diagonal the finite intersections of affine opens are affine.** -/
theorem FiniteAffineCover.isAffineOpen_inter [IsAffineHom (pullback.diagonal (terminal.from X))]
    (C : FiniteAffineCover X) {p : ℕ} (s : Fin (p + 1) → C.I) : IsAffineOpen (inter C.U s) :=
  IsAffineOpen.iInf fun j => C.isAffineOpen (s j)

end Cover

/-! ### The product covering -/

section Product

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) {I J : Type u} (U : I → X.Opens)
  (V : J → Y.Opens)

/-- A point lies in a finite intersection of opens if and only if it lies in each one. -/
theorem mem_iInf_opens {T : TopCat.{u}} {p : ℕ} (W : Fin (p + 1) → Opens T) (x : T) :
    x ∈ (⨅ j, W j) ↔ ∀ j, x ∈ W j := by
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- **The nerve of the product covering is the box of the nerves**: `pr₁⁻¹` and `pr₂⁻¹` commute
with finite intersections. -/
theorem boxOpen_inter_prodCover {p : ℕ} (σ : Fin (p + 1) → I × J) :
    (boxOpen a b).obj (inter (prodCover U V) σ) =
      inter ((boxOpen a b).obj ∘ prodCover U V) σ := by
  rw [boxOpen_obj, fst_inter_prodCover, snd_inter_prodCover]
  ext z
  change z ∈ ((pullback.fst a b ⁻¹ᵁ (⨅ j, U (σ j).1) ⊓ pullback.snd a b ⁻¹ᵁ (⨅ j, V (σ j).2) :
      (pullback a b).Opens) : Set _) ↔
    z ∈ ((⨅ j, (pullback.fst a b ⁻¹ᵁ U (σ j).1 ⊓ pullback.snd a b ⁻¹ᵁ V (σ j).2) :
      (pullback a b).Opens) : Set _)
  simp only [Opens.coe_inf, Opens.coe_iInf, Set.mem_inter_iff, Set.mem_iInter,
    SetLike.mem_coe, Scheme.Hom.mem_preimage, mem_iInf_opens]
  exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩

/-- The product covering covers the fibre product. -/
theorem iSup_boxOpen_prodCover (hU : ⊤ = ⨆ i, U i) (hV : ⊤ = ⨆ j, V j) :
    ⊤ = ⨆ ij, ((boxOpen a b).obj ∘ prodCover U V) ij := by
  refine (eq_top_iff.2 fun z _ => ?_).symm
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU ▸ trivial : pullback.fst a b z ∈ ⨆ i, U i)
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hV ▸ trivial : pullback.snd a b z ∈ ⨆ j, V j)
  exact Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩

/-- **The box of two affine opens over an affine base is affine.** -/
theorem isAffineOpen_boxOpen [IsAffine S] (Z : LatProd X.Opens Y.Opens) (hA : IsAffineOpen Z.fst)
    (hB : IsAffineOpen Z.snd) : IsAffineOpen ((boxOpen a b).obj Z) := by
  rw [← image_topChart a b Z hA hB, Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

end Product

/-! ### The Künneth isomorphism -/

variable {k : Type u} [Field k]

/-- The ring map `k ⟶ Γ(X, 𝒪_X)` of a scheme over `Spec k`. -/
abbrev structureRingHom {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  baseRingHom (Scheme.ΓSpecIso (.of k)).inv.hom f

/-- **The cohomology `Hⁿ(X, ℱ)` of a module on a scheme over `k`, as a `k`-module**: Mathlib's
right derived functor of global sections, with scalars restricted along
`k = Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)`. -/
abbrev cohomologyK {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules) (n : ℕ) :
    ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (structureRingHom f)).obj
    (((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj F)

/-- The ring map `k → Γ(Spec k, 𝒪)` is bijective. -/
theorem bijective_ΓSpecIso_inv : Function.Bijective (Scheme.ΓSpecIso (.of k)).inv.hom :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv

variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (CX : FiniteAffineCover X) (CY : FiniteAffineCover Y)
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))]
  (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- `Hᵖ(X, ℱ)` computed by a finite affine covering. -/
def cechEquivX (p : ℕ) : H (sectionsK X (structureRingHom f) F) CX.U p ≃ₗ[k] cohomologyK f F p :=
  cechEquiv X (structureRingHom f) F CX.U CX.iSup_eq p
    (bijective_cechClass_of_isAffineOpen X CX.U CX.iSup_eq F
      (fun _ s => CX.isAffineOpen_inter X s) _)

/-- `cechEquivX` carries the class of a Čech cocycle to its class in cohomology, through the
comparison `Stacks.Cech.Hypercohomology.rightDerivedIsoHypercohomology` of Mathlib's right derived
functors with hypercohomology. -/
theorem cechEquivX_Hmk {p : ℕ} (c : Cochain (sectionsK X (structureRingHom f) F) CX.U p)
    (hc : d _ CX.U p c = 0) :
    cechEquivX f CX F p (Hmk _ _ c hc) =
      (rightDerivedIsoHypercohomology X F p).inv.hom
        (classK X (structureRingHom f) F CX.U CX.iSup_eq c hc) :=
  rfl

/-- The nerve of the product covering consists of affine opens. -/
theorem isAffineOpen_inter_boxOpen_prodCover {p : ℕ} (σ : Fin (p + 1) → CX.I × CY.I) :
    IsAffineOpen (inter ((boxOpen f g).obj ∘ prodCover CX.U CY.U) σ) := by
  rw [← boxOpen_inter_prodCover]
  exact isAffineOpen_boxOpen f g _
    ((fst_inter_prodCover CX.U CY.U σ).symm ▸ CX.isAffineOpen_inter X _)
    ((snd_inter_prodCover CX.U CY.U σ).symm ▸ CY.isAffineOpen_inter Y _)

/-- `Hⁿ(X ×_k Y, ℱ ⊠ 𝒢)` computed by the product covering. -/
def cechEquivProd (n : ℕ) :
    H (sectionsK (pullback f g) (structureRingHom (pullback.fst f g ≫ f))
        (externalTensorProduct f g F G)) ((boxOpen f g).obj ∘ prodCover CX.U CY.U) n ≃ₗ[k]
      cohomologyK (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n :=
  cechEquiv (pullback f g) (structureRingHom (pullback.fst f g ≫ f))
    (externalTensorProduct f g F G) _ (iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq)
    n (bijective_cechClass_of_isAffineOpen (pullback f g) _ _ _
      (fun _ σ => isAffineOpen_inter_boxOpen_prodCover f g CX CY σ) _)

/-- `cechEquivProd` carries the class of a Čech cocycle to its class in cohomology. -/
theorem cechEquivProd_Hmk {n : ℕ} (z : Cochain (sectionsK (pullback f g)
      (structureRingHom (pullback.fst f g ≫ f)) (externalTensorProduct f g F G))
      ((boxOpen f g).obj ∘ prodCover CX.U CY.U) n) (hz : d _ _ n z = 0) :
    cechEquivProd f g CX CY F G n (Hmk _ _ z hz) =
      (rightDerivedIsoHypercohomology (pullback f g) (externalTensorProduct f g F G) n).inv.hom
        (classK (pullback f g) (structureRingHom (pullback.fst f g ≫ f))
          (externalTensorProduct f g F G) _
          (iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq) z hz) :=
  rfl

/-- The Čech cohomology of the product covering with coefficients in `ℱ ⊠ 𝒢` is that of the
presheaf `(A, B) ↦ Γ(A, ℱ) ⊗_k Γ(B, 𝒢)` on pairs of opens. -/
def cechEquivBox (n : ℕ) :
    H (extTensor (sectionsK X (structureRingHom f) F) (sectionsK Y (structureRingHom g) G))
        (prodCover CX.U CY.U) n ≃ₗ[k]
      H (sectionsK (pullback f g) (structureRingHom (pullback.fst f g ≫ f))
        (externalTensorProduct f g F G)) ((boxOpen f g).obj ∘ prodCover CX.U CY.U) n :=
  (LinearEquiv.ofBijective _ (bijective_Hmap_of_bijective (prodCover CX.U CY.U)
    (boxMap (Scheme.ΓSpecIso (.of k)).inv.hom f g F G) (fun σ =>
      bijective_boxMap_app _ f g F G _ bijective_ΓSpecIso_inv
        ((fst_inter_prodCover CX.U CY.U σ).symm ▸ CX.isAffineOpen_inter X _)
        ((snd_inter_prodCover CX.U CY.U σ).symm ▸ CY.isAffineOpen_inter Y _)) n)).trans
    (transportEquiv (boxOpen f g) _ (prodCover CX.U CY.U)
      (fun σ => boxOpen_inter_prodCover f g CX.U CY.U σ) n)

/-- **The Künneth isomorphism**, for chosen finite affine coverings. -/
def kunnethIsoOfCovers (n : ℕ) :
    cohomologyK (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n ≃ₗ[k]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => cohomologyK f F pq.1.1 ⊗[k] cohomologyK g G pq.1.2) :=
  (cechEquivProd f g CX CY F G n).symm.trans ((cechEquivBox f g CX CY F G n).symm.trans
    ((kunnethEquiv CX.U CY.U (sectionsK X (structureRingHom f) F)
      (sectionsK Y (structureRingHom g) G) n).symm.trans
    ((LinearEquiv.piCongrRight fun pq : Idx n =>
      TensorProduct.congr (cechEquivX f CX F pq.1.1) (cechEquivX g CY G pq.1.2)).trans
      (DirectSum.linearEquivFunOnFintype k (Idx n) _).symm)))

/-- The Alexander–Whitney product of two Čech cochains of `ℱ` and `𝒢`, read as a Čech cochain of
`ℱ ⊠ 𝒢` for the product covering: its value on `U_{i₀ … iₙ} × V_{j₀ … jₙ}` is the section
`c_{i₀ … i_p}| ⊠ e_{j_p … jₙ}|`. -/
def boxCup {n : ℕ} (pq : Idx n) (c : Cochain (sectionsK X (structureRingHom f) F) CX.U pq.1.1)
    (e : Cochain (sectionsK Y (structureRingHom g) G) CY.U pq.1.2) :
    Cochain (sectionsK (pullback f g) (structureRingHom (pullback.fst f g ≫ f))
      (externalTensorProduct f g F G)) ((boxOpen f g).obj ∘ prodCover CX.U CY.U) n :=
  transportCochain (boxOpen f g) _ (prodCover CX.U CY.U)
    (fun σ => boxOpen_inter_prodCover f g CX.U CY.U σ) n
    (mapCochain (prodCover CX.U CY.U) (boxMap (Scheme.ΓSpecIso (.of k)).inv.hom f g F G) n
      (cup pq.2 c e))

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] [F.IsQuasicoherent] [G.IsQuasicoherent] in
/-- The product `boxCup` of two Čech cocycles is a Čech cocycle of `ℱ ⊠ 𝒢`. -/
theorem d_boxCup {n : ℕ} (pq : Idx n)
    {c : Cochain (sectionsK X (structureRingHom f) F) CX.U pq.1.1}
    {e : Cochain (sectionsK Y (structureRingHom g) G) CY.U pq.1.2}
    (hc : d _ CX.U pq.1.1 c = 0) (he : d _ CY.U pq.1.2 e = 0) :
    d _ _ n (boxCup f g CX CY F G pq c e) = 0 := by
  refine (transportCochain_d (boxOpen f g) _ (prodCover CX.U CY.U)
    (fun σ => boxOpen_inter_prodCover f g CX.U CY.U σ) n _).trans ?_
  change transportCochain _ _ _ _ (n + 1) (d (boxPresheaf _ f g F G) _ n _) = 0
  rw [← mapCochain_d, d_cup_eq_zero pq.2 hc he, map_zero]
  exact map_zero (transportCochain (boxOpen f g) (sectionsK (pullback f g)
    (structureRingHom (pullback.fst f g ≫ f)) (externalTensorProduct f g F G))
    (prodCover CX.U CY.U) (fun σ => boxOpen_inter_prodCover f g CX.U CY.U σ) (n + 1))

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] in
/-- The member of the nerve of the product covering selected by `σ` lies in the preimage under
`pr₁` of the intersection of the `U` indexed by the first components of `σ ∘ θ`, for any `θ`. -/
theorem inter_boxOpen_prodCover_le_fst {n m : ℕ} (σ : Fin (n + 1) → CX.I × CY.I)
    (θ : Fin (m + 1) → Fin (n + 1)) :
    inter ((boxOpen f g).obj ∘ prodCover CX.U CY.U) σ ≤
      pullback.fst f g ⁻¹ᵁ inter CX.U (Prod.fst ∘ σ ∘ θ) :=
  (boxOpen_inter_prodCover f g CX.U CY.U σ).ge.trans
    ((boxOpen_le_fst f g _).trans (Scheme.Hom.preimage_mono _
      (fst_inter_prodCover_le CX.U CY.U σ θ)))

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] in
/-- The member of the nerve of the product covering selected by `σ` lies in the preimage under
`pr₂` of the intersection of the `V` indexed by the second components of `σ ∘ θ`, for any `θ`. -/
theorem inter_boxOpen_prodCover_le_snd {n m : ℕ} (σ : Fin (n + 1) → CX.I × CY.I)
    (θ : Fin (m + 1) → Fin (n + 1)) :
    inter ((boxOpen f g).obj ∘ prodCover CX.U CY.U) σ ≤
      pullback.snd f g ⁻¹ᵁ inter CY.U (Prod.snd ∘ σ ∘ θ) :=
  (boxOpen_inter_prodCover f g CX.U CY.U σ).ge.trans
    ((boxOpen_le_snd f g _).trans (Scheme.Hom.preimage_mono _
      (snd_inter_prodCover_le CX.U CY.U σ θ)))

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] [F.IsQuasicoherent] [G.IsQuasicoherent] in
/-- **The value of `boxCup`**: on the member of the nerve of the product covering selected by `σ`,
it is the section `c_{σ₀ … σ_p} ⊠ e_{σ_p … σₙ}` of `ℱ ⊠ 𝒢`. -/
theorem boxCup_apply {n : ℕ} (pq : Idx n)
    (c : Cochain (sectionsK X (structureRingHom f) F) CX.U pq.1.1)
    (e : Cochain (sectionsK Y (structureRingHom g) G) CY.U pq.1.2)
    (σ : Fin (n + 1) → CX.I × CY.I) :
    boxCup f g CX CY F G pq c e σ =
      Stacks.Tag01VSPullbackTensor.externalTensorSection f g F G
        (show Γ(F, inter CX.U (Prod.fst ∘ σ ∘
          Stacks.Cech.LinearCupProduct.frontIdx pq.1.1 n (by omega))) from
          c (Prod.fst ∘ σ ∘ Stacks.Cech.LinearCupProduct.frontIdx pq.1.1 n (by omega)))
        (show Γ(G, inter CY.U (Prod.snd ∘ σ ∘
          Stacks.Cech.LinearCupProduct.backIdx pq.1.1 pq.1.2 n pq.2.le)) from
          e (Prod.snd ∘ σ ∘ Stacks.Cech.LinearCupProduct.backIdx pq.1.1 pq.1.2 n pq.2.le))
        (inter ((boxOpen f g).obj ∘ prodCover CX.U CY.U) σ)
        (inter_boxOpen_prodCover_le_fst f g CX CY σ _)
        (inter_boxOpen_prodCover_le_snd f g CX CY σ _) :=
  (Stacks.Tag01VSPullbackTensor.externalTensorSection_presheaf_map f g F G _ _
    (boxOpen_le_fst f g _) (boxOpen_le_snd f g _)
    ((boxOpen_inter_prodCover f g CX.U CY.U σ).ge.trans (boxOpen_le_fst f g _))
    ((boxOpen_inter_prodCover f g CX.U CY.U σ).ge.trans (boxOpen_le_snd f g _)) _).trans
    (externalTensorSection_res f g F G _ _ _ _ _ _ _)

/-- **The Künneth isomorphism is the Čech cup product of pulled-back cocycles**
([Stacks, Tag 0BEE]): its inverse carries `α ⊗ β`, for `α` and `β` the classes of Čech cocycles `c`
of `ℱ` on `𝒰` and `e` of `𝒢` on `𝒱`, to the class of their Alexander–Whitney product on the
product covering. -/
theorem kunnethIsoOfCovers_symm_lof_tmul {n : ℕ} (pq : Idx n)
    (c : Cochain (sectionsK X (structureRingHom f) F) CX.U pq.1.1) (hc : d _ CX.U pq.1.1 c = 0)
    (e : Cochain (sectionsK Y (structureRingHom g) G) CY.U pq.1.2) (he : d _ CY.U pq.1.2 e = 0) :
    (kunnethIsoOfCovers f g CX CY F G n).symm (DirectSum.lof k _
        (fun pq : Idx n => cohomologyK f F pq.1.1 ⊗[k] cohomologyK g G pq.1.2) pq
        (cechEquivX f CX F pq.1.1 (Hmk _ _ c hc) ⊗ₜ cechEquivX g CY G pq.1.2 (Hmk _ _ e he))) =
      cechEquivProd f g CX CY F G n (Hmk _ _ (boxCup f g CX CY F G pq c e)
        (d_boxCup f g CX CY F G pq hc he)) := by
  simp only [kunnethIsoOfCovers, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, DirectSum.linearEquivFunOnFintype_lof]
  congr 1
  have h₁ : (LinearEquiv.piCongrRight fun pq : Idx n =>
      TensorProduct.congr (cechEquivX f CX F pq.1.1) (cechEquivX g CY G pq.1.2)).symm
        (Pi.single pq (cechEquivX f CX F pq.1.1 (Hmk _ _ c hc) ⊗ₜ
          cechEquivX g CY G pq.1.2 (Hmk _ _ e he))) =
      Pi.single pq (Hmk _ _ c hc ⊗ₜ Hmk _ _ e he) := by
    funext q
    rw [LinearEquiv.piCongrRight_symm, LinearEquiv.piCongrRight_apply]
    by_cases hq : q = pq
    · subst hq
      rw [Pi.single_eq_same, Pi.single_eq_same, TensorProduct.congr_symm_tmul,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    · rw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq, map_zero]
  have h₂ : kunnethEquiv CX.U CY.U (sectionsK X (structureRingHom f) F)
      (sectionsK Y (structureRingHom g) G) n (Pi.single pq (Hmk _ _ c hc ⊗ₜ Hmk _ _ e he)) =
      Hmk _ _ (cup pq.2 c e) (d_cup_eq_zero pq.2 hc he) := by
    change kunnethMap _ _ _ _ n _ = _
    rw [kunnethMap_apply, Fintype.sum_eq_single pq (fun q hq => by
      rw [Pi.single_eq_of_ne hq, map_zero]), Pi.single_eq_same]
    rfl
  rw [h₁, h₂]
  rfl

variable (k) in
/-- **The Künneth formula** [Stacks, Tag 0BED]. For a field `k`, quasi-compact schemes `X` and `Y`
over `k` with affine diagonal, a quasi-coherent `𝒪_X`-module `ℱ` and a quasi-coherent
`𝒪_Y`-module `𝒢`,
`Hⁿ(X ×_k Y, pr₁^*ℱ ⊗_{𝒪_{X ×_k Y}} pr₂^*𝒢) ≅ ⨁_{p + q = n} Hᵖ(X, ℱ) ⊗_k H^q(Y, 𝒢)`.

The isomorphism is the one of the source: computed on finite affine coverings `𝒰` of `X` and `𝒱`
of `Y` (chosen by `Stacks.CechKunneth.finiteAffineCover`), it carries the class of the
Alexander–Whitney product of the pullbacks of two Čech cocycles — the Čech form of
`pr₁^*α ∪ pr₂^*β`, [Stacks, Tag 0BEE] — to `α ⊗ β`; see
`Stacks.CechKunneth.kunnethIsoOfCovers_symm_lof_tmul`. The cohomology groups are Mathlib's right
derived functors of global sections, regarded as `k`-modules through the structure morphisms
(`Stacks.CechKunneth.cohomologyK`). -/
@[stacks 0BED "for X and Y quasi-compact with affine diagonal over a field k and F, G \
quasi-coherent: H^n(X x_k Y, pr_1^*F (x) pr_2^*G) is the direct sum over p + q = n of \
H^p(X, F) (x)_k H^q(Y, G), the isomorphism being the Cech-level cup product of pulled-back \
cocycles"]
def kunnethIsoOfAffineDiagonal [CompactSpace X] [CompactSpace Y] (n : ℕ) :
    cohomologyK (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n ≃ₗ[k]
      DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => cohomologyK f F pq.1.1 ⊗[k] cohomologyK g G pq.1.2) :=
  kunnethIsoOfCovers f g (finiteAffineCover X) (finiteAffineCover Y) F G n

end Stacks.CechKunneth

end
