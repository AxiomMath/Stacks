module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Locality
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine

/-!
# Flat base change for the derived direct image of a quasi-coherent module

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. For every cartesian
square
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `g` flat and every quasi-coherent `𝒪_X`-module `ℱ`, the base change map of
[Stacks, Tag 02N7]

`g^* Rf_* ℱ ⟶ Rf'_* (g')^* ℱ`

is an isomorphism in `D⁺(𝒪_{S'})`.

The proof is by induction on the source. The statement is local on `S`
(`isIso_schemeBaseChange_of_cover_base`), so `S` may be taken affine. If `X` is separated and
covered by `n + 1` affine opens, cover it by the union `U` of the first `n` and the last one `V`:
the inclusions of `U`, `V` and `U ∩ V` into `X` and their composites with `f` are again separated
over an affine base and covered by at most `n` affine opens (locally on the base, for the
inclusions), and the Mayer–Vietoris statement `isIso_schemeBaseChange_of_cover` finishes. A
quasi-separated `X` over an affine base is covered by finitely many separated quasi-compact opens,
and the same induction on their number, now with the separated case as input, finishes.

## Main definitions

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.BaseChangeIsIso`: the assertion that the base
  change map of every cartesian square over `f` with flat base is an isomorphism at every
  quasi-coherent module.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.baseChangeIsIso_of_isSeparated`: the separated
  case over an affine base.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.baseChangeIsIso`: the general case.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeDerived

attribute [local instance] HasDerivedCategory.standard

/-- The base change map of [Stacks, Tag 02N7] of every cartesian square over `f` with flat base
is an isomorphism at every quasi-coherent `𝒪_X`-module. -/
def BaseChangeIsIso {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ ⦃S' X' : Scheme.{u}⦄ (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (H : IsPullback g' f' f g)
    [Flat g] [Flat g'] (F : X.Modules) [F.IsQuasicoherent],
    IsIso ((schemeBaseChange f f' g g' H.w).app ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- `BaseChangeIsIso` depends only on the morphism. -/
theorem BaseChangeIsIso.congr {X S : Scheme.{u}} {f f₂ : X ⟶ S} (h : f = f₂)
    (hf : BaseChangeIsIso f) : BaseChangeIsIso f₂ :=
  h ▸ hf

/-- **The affine case.** -/
theorem baseChangeIsIso_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    BaseChangeIsIso f :=
  fun _ _ _ _ _ H _ _ F _ => isIso_schemeBaseChange_of_isAffineHom H F

/-- **Locality on the base.** -/
theorem baseChangeIsIso_of_cover_base {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type*}
    (U : ι → S.Opens) (hU : IsOpenCover U) (h : ∀ i, BaseChangeIsIso (f ∣_ U i)) :
    BaseChangeIsIso f := by
  intro S' X' g f' g' H _ _ F _
  refine isIso_schemeBaseChange_of_cover_base H U hU F (fun i => ?_)
  have : ((Scheme.Modules.pullback (f ⁻¹ᵁ U i).ι).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F
  exact h i _ _ _ (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isPullback_restrictBasesSquare
    H (U i) le_rfl) ((Scheme.Modules.pullback (f ⁻¹ᵁ U i).ι).obj F)

/-- **Mayer–Vietoris on the source.** -/
theorem baseChangeIsIso_of_cover_source {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (hT : ∀ W ∈ ({U, V, U ⊓ V} : Set X.Opens), BaseChangeIsIso W.ι)
    (hC : ∀ W ∈ ({U, V, U ⊓ V} : Set X.Opens), BaseChangeIsIso (W.ι ≫ f)) :
    BaseChangeIsIso f := by
  intro S' X' g f' g' H _ _ F _
  have (W : X.Opens) : ((Scheme.Modules.pullback W.ι).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F
  refine isIso_schemeBaseChange_of_cover H.w U V hUV F (fun W hW => ?_) (fun W hW => ?_)
  · exact hT W hW _ _ _ (isPullback_morphismRestrict g' W) ((Scheme.Modules.pullback W.ι).obj F)
  · exact hC W hW _ _ _ ((isPullback_morphismRestrict g' W).paste_vert H)
      ((Scheme.Modules.pullback W.ι).obj F)

/-- Mayer–Vietoris on the source, with the hypotheses on `U`, `V` and `U ⊓ V` given pairwise. -/
private theorem baseChangeIsIso_of_cover_source_of_pairs {X S : Scheme.{u}} (f : X ⟶ S)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (hU : BaseChangeIsIso U.ι ∧ BaseChangeIsIso (U.ι ≫ f))
    (hV : BaseChangeIsIso V.ι ∧ BaseChangeIsIso (V.ι ≫ f))
    (hUV' : BaseChangeIsIso (U ⊓ V).ι ∧ BaseChangeIsIso ((U ⊓ V).ι ≫ f)) :
    BaseChangeIsIso f := by
  have key : ∀ W ∈ ({U, V, U ⊓ V} : Set X.Opens),
      BaseChangeIsIso W.ι ∧ BaseChangeIsIso (W.ι ≫ f) := by
    intro W hW
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
    rcases hW with rfl | rfl | rfl <;> assumption
  exact baseChangeIsIso_of_cover_source f U V hUV (fun W hW => (key W hW).1)
    fun W hW => (key W hW).2

/-! ### Covers by finitely many opens -/

section Covers

/-- An open covered by the first `n` of `n + 1` opens and the last one. -/
theorem iSup_fin_succ {α : Type*} [CompleteLattice α] {n : ℕ} (A : Fin (n + 1) → α) :
    ⨆ i, A i = (⨆ i : Fin n, A i.castSucc) ⊔ A (Fin.last n) := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (iSup_le fun j => le_iSup _ _) (le_iSup _ _))
  induction i using Fin.lastCases with
  | last => exact le_sup_right
  | cast j => exact le_sup_of_le_left (le_iSup (fun j : Fin n => A j.castSucc) j)

/-- The range of the inclusion of an open of an open subscheme. -/
theorem opensRange_ι_preimage_comp {Y : Scheme.{u}} (W B : Y.Opens) :
    ((W.ι ⁻¹ᵁ B).ι ≫ W.ι).opensRange = W ⊓ B := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- **Covers pull back along open immersions.** Affine opens of `Y` covering the range of an open
immersion `e` pull back to affine opens covering its source. -/
theorem affineCover_preimage {Z Y : Scheme.{u}} (e : Z ⟶ Y) [IsOpenImmersion e] {m : ℕ}
    (B : Fin m → Y.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hsup : ⨆ i, B i = e.opensRange) :
    (∀ i, IsAffineOpen (e ⁻¹ᵁ B i)) ∧ ⨆ i, e ⁻¹ᵁ B i = ⊤ := by
  refine ⟨fun i => (hB i).preimage_of_isOpenImmersion e (hsup ▸ le_iSup B i), ?_⟩
  rw [← Scheme.Hom.preimage_iSup, hsup, Scheme.Hom.preimage_opensRange]

/-- A morphism factoring through an open immersion into an open over which `k` is separated is
separated over the target of `k`. -/
theorem isSeparated_comp_of_le {Z Y T : Scheme.{u}} (e : Z ⟶ Y) [IsOpenImmersion e]
    (k : Y ⟶ T) (W : Y.Opens) (hle : e.opensRange ≤ W) [IsSeparated (W.ι ≫ k)] :
    IsSeparated (e ≫ k) := by
  have h : Set.range e.base ⊆ Set.range W.ι.base := by
    rwa [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
  rw [← IsOpenImmersion.lift_fac W.ι e h, Category.assoc]
  infer_instance

/-- A quasi-compact scheme is covered by finitely many affine opens, indexed by `Fin n`. -/
theorem exists_fin_affineOpen_cover (Y : Scheme.{u}) [CompactSpace Y] :
    ∃ (n : ℕ) (A : Fin n → Y.Opens), (∀ i, IsAffineOpen (A i)) ∧ ⨆ i, A i = ⊤ := by
  obtain ⟨ι, hι, V, hVaff, hVcov⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover Y
  have := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => V (e.symm i), fun i => hVaff _,
    le_antisymm le_top fun x _ => ?_⟩
  obtain ⟨a, ha⟩ := hVcov x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨e a, by simpa using ha⟩

end Covers

/-! ### The separated case -/

section Separated

/-- A scheme covered by no open is empty. -/
theorem isEmpty_of_iSup_fin_zero {Y : Scheme.{u}} (A : Fin 0 → Y.Opens) (hA : ⨆ i, A i = ⊤) :
    IsEmpty Y := by
  refine ⟨fun y => ?_⟩
  have hy : y ∈ (⊤ : Y.Opens) := trivial
  rw [← hA, iSup_of_empty] at hy
  exact hy

/-- A scheme separated over an affine scheme has affine diagonal. -/
theorem isAffineHom_diagonal {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T) [IsSeparated k] :
    IsAffineHom (pullback.diagonal (terminal.from Y)) := by
  have : IsSeparated (terminal.from Y) := by
    rw [show terminal.from Y = k ≫ terminal.from T from terminal.hom_ext _ _]
    infer_instance
  infer_instance

/-- The inductive step of the separated case: if the statement holds for every separated
morphism to an affine scheme whose source is covered by `n` affine opens, then it holds for the
inclusion of a union `W` of `n` affine opens of `Y` and for its composite with `k`. -/
theorem baseChangeIsIso_of_iSup_affine (n : ℕ)
    (ih : ∀ {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T) [IsSeparated k] (A : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (A i)) → ⨆ i, A i = ⊤ → BaseChangeIsIso k)
    {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T) [IsSeparated k] {m : ℕ} (A : Fin m → Y.Opens)
    (hAff : ∀ i, IsAffineOpen (A i)) (hA : ⨆ i, A i = ⊤) (C : Fin n → Y.Opens)
    (hC : ∀ i, IsAffineOpen (C i)) (W : Y.Opens) (hW : ⨆ i, C i = W) :
    BaseChangeIsIso (W.ι ≫ k) ∧ BaseChangeIsIso W.ι := by
  have := isAffineHom_diagonal k
  constructor
  · obtain ⟨h₁, h₂⟩ := affineCover_preimage W.ι C hC (hW.trans W.opensRange_ι.symm)
    exact ih (W.ι ≫ k) _ h₁ h₂
  · refine baseChangeIsIso_of_cover_base W.ι A hA (fun j => ?_)
    have : IsAffine (A j).toScheme := hAff j
    let e := (W.ι ⁻¹ᵁ A j).ι ≫ W.ι
    obtain ⟨h₁, h₂⟩ := affineCover_preimage e (fun i => C i ⊓ A j)
      (fun i => (hC i).inf (hAff j))
      (by rw [← iSup_inf_eq, hW, opensRange_ι_preimage_comp])
    exact ih (W.ι ∣_ A j) _ h₁ h₂

/-- **The separated case over an affine base, by induction on the number of affine opens
covering the source.** -/
theorem baseChangeIsIso_of_isSeparated_of_cover (n : ℕ) :
    ∀ {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T) [IsSeparated k] (A : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (A i)) → ⨆ i, A i = ⊤ → BaseChangeIsIso k := by
  induction n with
  | zero =>
    intro Y T _ k _ A _ hA
    have := isEmpty_of_iSup_fin_zero A hA
    exact baseChangeIsIso_of_isAffineHom k
  | succ n ih =>
    intro Y T _ k _ A hAff hA
    have := isAffineHom_diagonal k
    let U : Y.Opens := ⨆ i : Fin n, A i.castSucc
    let V : Y.Opens := A (Fin.last n)
    have hUV : U ⊔ V = ⊤ := (iSup_fin_succ A).symm.trans hA
    have hV : IsAffine V.toScheme := hAff (Fin.last n)
    have hVι : IsAffineHom V.ι := IsAffineHom.of_comp V.ι k
    have hU := baseChangeIsIso_of_iSup_affine n ih k A hAff hA (fun i => A i.castSucc)
      (fun i => hAff _) U rfl
    have hUV' := baseChangeIsIso_of_iSup_affine n ih k A hAff hA
      (fun i => A i.castSucc ⊓ V) (fun i => (hAff _).inf (hAff _)) (U ⊓ V) (iSup_inf_eq _ _).symm
    exact baseChangeIsIso_of_cover_source_of_pairs k U V hUV ⟨hU.2, hU.1⟩
      ⟨baseChangeIsIso_of_isAffineHom _, baseChangeIsIso_of_isAffineHom _⟩ ⟨hUV'.2, hUV'.1⟩

/-- **The separated case.** For a separated quasi-compact morphism to an affine scheme, the base
change map of every cartesian square with flat base is an isomorphism at every quasi-coherent
module. -/
theorem baseChangeIsIso_of_isSeparated {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T)
    [IsSeparated k] [QuasiCompact k] : BaseChangeIsIso k := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  obtain ⟨n, A, hA, hcov⟩ := exists_fin_affineOpen_cover Y
  exact baseChangeIsIso_of_isSeparated_of_cover n k A hA hcov

end Separated

/-! ### The quasi-separated case -/

section QuasiSeparated

/-- Quasi-compact opens pull back along open immersions to quasi-compact opens covering the source,
when they cover its range. -/
theorem compactCover_preimage {Z Y : Scheme.{u}} (e : Z ⟶ Y) [IsOpenImmersion e] {m : ℕ}
    (B : Fin m → Y.Opens) (hB : ∀ i, IsCompact (B i : Set Y)) (hsup : ⨆ i, B i = e.opensRange) :
    (∀ i, IsCompact ((e ⁻¹ᵁ B i : Z.Opens) : Set Z)) ∧ ⨆ i, e ⁻¹ᵁ B i = ⊤ := by
  refine ⟨fun i => ?_, ?_⟩
  · have hle : (B i : Set Y) ⊆ Set.range e.base := by
      rw [← Scheme.Hom.coe_opensRange, ← hsup]
      exact le_iSup B i
    exact (e.isOpenEmbedding.isInducing.isCompact_preimage_iff hle).2 (hB i)
  · rw [← Scheme.Hom.preimage_iSup, hsup, Scheme.Hom.preimage_opensRange]

/-- **The inclusion of a quasi-compact open into a quasi-separated scheme over an affine scheme.**
Locally on the target it is the inclusion of a quasi-compact open into an affine scheme, which is
separated and quasi-compact over that affine scheme. -/
theorem baseChangeIsIso_ι_of_isCompact {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T)
    [QuasiSeparated k] (W : Y.Opens) (hW : IsCompact (W : Set Y)) : BaseChangeIsIso W.ι := by
  have : QuasiSeparatedSpace Y := (quasiSeparated_iff_quasiSeparatedSpace k).mp inferInstance
  refine baseChangeIsIso_of_cover_base W.ι (fun B : Y.affineOpens => (B : Y.Opens))
    (iSup_affineOpens_eq_top Y) (fun B => ?_)
  have : IsAffine (B : Y.Opens).toScheme := B.2
  have hc : IsCompact ((W.ι ⁻¹ᵁ (B : Y.Opens) : W.toScheme.Opens) : Set W.toScheme) := by
    have h₁ : IsCompact ((W : Set Y) ∩ (B : Set Y)) :=
      QuasiSeparatedSpace.inter_isCompact _ _ W.2 hW B.1.2 B.2.isCompact
    have h₂ : (W : Set Y) ∩ (B : Set Y) ⊆ Set.range W.ι.base := by
      rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
      exact Set.inter_subset_left
    have h₃ := W.ι.isOpenEmbedding.isInducing.isCompact_preimage' h₁ h₂
    have h₄ : W.ι.base ⁻¹' ((W : Set Y) ∩ (B : Set Y)) =
        ((W.ι ⁻¹ᵁ (B : Y.Opens) : W.toScheme.Opens) : Set W.toScheme) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    exact h₄ ▸ h₃
  have : CompactSpace (W.ι ⁻¹ᵁ (B : Y.Opens)).toScheme := isCompact_iff_compactSpace.mp hc
  have : QuasiCompact (W.ι ∣_ (B : Y.Opens)) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  exact baseChangeIsIso_of_isSeparated (W.ι ∣_ (B : Y.Opens))

/-- A finite union of affine opens is quasi-compact. -/
theorem isCompact_iSup_affine {Y : Scheme.{u}} {n : ℕ} (A : Fin n → Y.Opens)
    (hA : ∀ i, IsAffineOpen (A i)) : IsCompact ((⨆ i, A i : Y.Opens) : Set Y) := by
  rw [TopologicalSpace.Opens.coe_iSup]
  exact isCompact_iUnion fun i => (hA i).isCompact

/-- **The quasi-separated case over an affine base, by induction on the number of affine opens
covering the source.** -/
theorem baseChangeIsIso_of_quasiSeparated_of_cover (n : ℕ) :
    ∀ {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T) [QuasiSeparated k] (A : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (A i)) → ⨆ i, A i = ⊤ → BaseChangeIsIso k := by
  induction n with
  | zero =>
    intro Y T _ k _ A _ hA
    have := isEmpty_of_iSup_fin_zero A hA
    exact baseChangeIsIso_of_isAffineHom k
  | succ n ih =>
    intro Y T _ k _ A hAff hA
    have : QuasiSeparatedSpace Y := (quasiSeparated_iff_quasiSeparatedSpace k).mp inferInstance
    let U : Y.Opens := ⨆ i : Fin n, A i.castSucc
    let V : Y.Opens := A (Fin.last n)
    have hUV : U ⊔ V = ⊤ := (iSup_fin_succ A).symm.trans hA
    have hV : IsAffine V.toScheme := hAff (Fin.last n)
    have hUc : IsCompact (U : Set Y) := isCompact_iSup_affine _ fun i => hAff _
    have hUVc : IsCompact ((U ⊓ V : Y.Opens) : Set Y) :=
      QuasiSeparatedSpace.inter_isCompact _ _ U.2 hUc V.2 (hAff _).isCompact
    refine baseChangeIsIso_of_cover_source_of_pairs k U V hUV
      ⟨baseChangeIsIso_ι_of_isCompact k _ hUc, ?_⟩
      ⟨baseChangeIsIso_ι_of_isCompact k _ (hAff _).isCompact, baseChangeIsIso_of_isAffineHom _⟩
      ⟨baseChangeIsIso_ι_of_isCompact k _ hUVc, ?_⟩
    · obtain ⟨h₁, h₂⟩ := affineCover_preimage U.ι (fun i => A i.castSucc) (fun i => hAff _)
        U.opensRange_ι.symm
      exact ih (U.ι ≫ k) _ h₁ h₂
    · have : IsSeparated (V.ι ≫ k) := IsSeparated.of_isAffineHom _
      have : IsSeparated ((U ⊓ V).ι ≫ k) :=
        isSeparated_comp_of_le (U ⊓ V).ι k V (by
          rw [Scheme.Opens.opensRange_ι]
          exact inf_le_right)
      have : CompactSpace (U ⊓ V).toScheme := isCompact_iff_compactSpace.mp hUVc
      have : QuasiCompact ((U ⊓ V).ι ≫ k) := (quasiCompact_iff_compactSpace _).mpr inferInstance
      exact baseChangeIsIso_of_isSeparated _

/-- **The quasi-separated case.** For a quasi-compact quasi-separated morphism to an affine
scheme, the base change map of every cartesian square with flat base is an isomorphism at every
quasi-coherent module. -/
theorem baseChangeIsIso_of_isAffine {Y T : Scheme.{u}} [IsAffine T] (k : Y ⟶ T)
    [QuasiCompact k] [QuasiSeparated k] : BaseChangeIsIso k := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  obtain ⟨n, A, hA, hcov⟩ := exists_fin_affineOpen_cover Y
  exact baseChangeIsIso_of_quasiSeparated_of_cover n k A hA hcov

/-- **Flat base change for the derived direct image.** For a quasi-compact quasi-separated
morphism of schemes `f : X ⟶ S`, every cartesian square with `g : S' ⟶ S` flat and every
quasi-coherent `𝒪_X`-module `ℱ`, the base change map `g^* Rf_* ℱ ⟶ Rf'_* (g')^* ℱ` of
[Stacks, Tag 02N7] is an isomorphism. -/
theorem baseChangeIsIso {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    BaseChangeIsIso f :=
  baseChangeIsIso_of_cover_base f (fun B : S.affineOpens => (B : S.Opens))
    (iSup_affineOpens_eq_top S) (fun B =>
      have : IsAffine (B : S.Opens).toScheme := B.2
      baseChangeIsIso_of_isAffine (f ∣_ (B : S.Opens)))

end QuasiSeparated

end Stacks.AlgebraicGeometry.FlatBaseChangeDerived

end
