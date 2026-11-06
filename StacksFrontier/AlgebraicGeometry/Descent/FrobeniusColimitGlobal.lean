module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitLocal
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafAssembly

/-!
# Full faithfulness of `colim_F Vect(Y) ⥤ colim_F Vect(X)`: the Zariski-local argument

This file passes from the affine free case of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitLocal` to an arbitrary quasi-compact
(for injectivity) and quasi-compact quasi-separated (for surjectivity) base, by the Zariski sheaf
property of the presheaf of morphisms (`AlgebraicGeometry.isSheafFor_presheafHom_zariski_over`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius
open Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace AlgebraicGeometry

/-! ### The presheaf of morphisms acts by restriction -/

/-- The comparison of the module pseudofunctor is `pullbackComp`, up to `pullbackCongr`. -/
lemma modulePullbackPseudofunctor_mapComp'_hom {S T T' : Scheme.{u}} (f : T ⟶ S) (g : T' ⟶ T)
    (h : T' ⟶ S) (hh : g ≫ f = h) :
    (modulePullbackPseudofunctor.mapComp' f.op.toLoc g.op.toLoc h.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hh])).hom.toNatTrans =
      (Scheme.Modules.pullbackCongr hh).inv ≫ (Scheme.Modules.pullbackComp g f).inv := by
  subst hh
  show (modulePullbackPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
    (f.op.toLoc ≫ g.op.toLoc) rfl).hom.toNatTrans = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  simp [modulePullbackPseudofunctor, Scheme.Modules.pullbackCongr, Bicategory.Adj.forget₁]
  rfl

/-- **The action of the presheaf of morphisms is restriction.** -/
lemma presheafHom_map_eq_homRes {S : Scheme.{u}} (M N : S.Modules) {T T' : Over S}
    (v : T' ⟶ T) (φ : HomAt T.hom M N) :
    (modulePullbackPseudofunctor.presheafHom M N).map v.op φ = homRes v.left (Over.w v) φ := by
  have hhom := modulePullbackPseudofunctor_mapComp'_hom T.hom v.left T'.hom (Over.w v)
  let E := Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapComp' T.hom.op.toLoc v.left.op.toLoc
    T'.hom.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w v]))
  have hEhom : E.hom = (Scheme.Modules.pullbackCongr (Over.w v)).inv ≫
      (Scheme.Modules.pullbackComp v.left T.hom).inv := hhom
  let A' : (Scheme.Modules.pullback T'.hom).obj M ⟶
      (Scheme.Modules.pullback v.left).obj ((Scheme.Modules.pullback T.hom).obj M) :=
    E.hom.app M
  let AN : (Scheme.Modules.pullback T'.hom).obj N ⟶
      (Scheme.Modules.pullback v.left).obj ((Scheme.Modules.pullback T.hom).obj N) :=
    E.hom.app N
  let B' : (Scheme.Modules.pullback v.left).obj ((Scheme.Modules.pullback T.hom).obj N) ⟶
      (Scheme.Modules.pullback T'.hom).obj N :=
    E.inv.app N
  have hA : A' = (Scheme.Modules.pullbackCongr (Over.w v)).inv.app M ≫
      (Scheme.Modules.pullbackComp v.left T.hom).inv.app M := by
    show E.hom.app M = _
    rw [hEhom]
    rfl
  have hAN : AN = (Scheme.Modules.pullbackCongr (Over.w v)).inv.app N ≫
      (Scheme.Modules.pullbackComp v.left T.hom).inv.app N := by
    show E.hom.app N = _
    rw [hEhom]
    rfl
  have hAB : AN ≫ B' = 𝟙 _ := E.hom_inv_id_app N
  have hB : B' = (Scheme.Modules.pullbackComp v.left T.hom).hom.app N ≫
      (Scheme.Modules.pullbackCongr (Over.w v)).hom.app N := by
    calc B' = (((Scheme.Modules.pullbackComp v.left T.hom).hom.app N ≫
          (Scheme.Modules.pullbackCongr (Over.w v)).hom.app N) ≫ AN) ≫ B' := by
            rw [hAN]; simp
      _ = _ := by rw [Category.assoc, hAB, Category.comp_id]
  have h1 : (modulePullbackPseudofunctor.presheafHom M N).map v.op φ =
      A' ≫ (Scheme.Modules.pullback v.left).map φ ≫ B' := rfl
  rw [h1, hA, hB]
  simp only [homRes, Category.assoc]
  rfl

/-! ### Restriction along equal morphisms; monotonicity of twists -/

variable {Y : Scheme.{u}} {p : ℕ} [Fact p.Prime] {hY : IsInCharacteristic Y p}

/-- Restrictions along equal morphisms agree. -/
lemma homRes_congr {T T' : Scheme.{u}} {u u' : T' ⟶ T} (h : u = u') {K : T ⟶ Y} {K' : T' ⟶ Y}
    (hu : u ≫ K = K') (hu' : u' ≫ K = K') {A B : Y.Modules} (φ : HomAt K A B) :
    homRes u hu φ = homRes u' hu' φ := by
  subst h
  rfl

/-- If two morphisms have equal `m`-fold Frobenius twists, then their `M`-fold twists agree for
every `M ≥ m`. -/
lemma twistIter_eq_of_le {T : Scheme.{u}} {K : T ⟶ Y} {A B : Y.Modules} {a b : HomAt K A B}
    {m M : ℕ} (h : twistIter p hY m a = twistIter p hY m b) (hle : m ≤ M) :
    twistIter p hY M a = twistIter p hY M b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => exact h
  | succ d ih => exact congrArg (twist p hY) (ih (Nat.le_add_right m d))

/-! ### Zariski covers -/

/-- A finite family of opens of `T` with supremum `⊤` is a Zariski covering of `T`. -/
lemma ofArrows_opens_mem_zariskiPrecoverage {T : Scheme.{u}} {n : ℕ} (W : Fin n → T.Opens)
    (hW : ⨆ k, W k = ⊤) :
    Presieve.ofArrows (fun k ↦ (W k).toScheme) (fun k ↦ (W k).ι) ∈
      Scheme.zariskiPrecoverage.{u} T := by
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun k ↦ inferInstance⟩
  have hx : x ∈ (⨆ k, W k : T.Opens) := hW ▸ trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨k, by rwa [Scheme.Opens.range_ι]⟩

/-- **Morphisms over `K` are determined by their restrictions to an open cover.** -/
lemma homAt_ext_of_cover {T : Scheme.{u}} {K : T ⟶ Y} {n : ℕ} (W : Fin n → T.Opens)
    (hW : ⨆ k, W k = ⊤) {A B : Y.Modules} (φ ψ : HomAt K A B)
    (h : ∀ k, homRes (W k).ι rfl φ = homRes (W k).ι rfl ψ) : φ = ψ := by
  have hs := isSheafFor_presheafHom_zariski_over A B (Over.mk K) (fun k ↦ (W k).ι)
    (ofArrows_opens_mem_zariskiPrecoverage W hW)
  refine hs.isSeparatedFor.ext fun Z f hf ↦ ?_
  cases hf with
  | mk k =>
    rw [presheafHom_map_eq_homRes, presheafHom_map_eq_homRes]
    exact h k

/-! ### Local decompositions -/

/-- Every point has an affine open neighbourhood over which `A` pulls back to a free module. -/
def HasLocalDecomp {T : Scheme.{u}} (K : T ⟶ Y) (A : Y.Modules) : Prop :=
  ∀ x : T, ∃ W : T.Opens, IsAffineOpen W ∧ x ∈ W ∧ Nonempty (FreeDecomp (W.ι ≫ K) A)

/-- Restricting a decomposition along an inclusion of opens. -/
def FreeDecomp.restrictLE {T : Scheme.{u}} {K : T ⟶ Y} {A : Y.Modules} {W W' : T.Opens}
    (D : FreeDecomp (W.ι ≫ K) A) (hle : W' ≤ W) : FreeDecomp (W'.ι ≫ K) A :=
  D.homRes (T.homOfLE hle) (by rw [← Category.assoc, Scheme.homOfLE_ι])

/-- Local decompositions pull back along any morphism `v : T' ⟶ T`. -/
lemma HasLocalDecomp.comp {T T' : Scheme.{u}} {K : T ⟶ Y} {A : Y.Modules}
    (h : HasLocalDecomp K A) (v : T' ⟶ T) : HasLocalDecomp (v ≫ K) A := by
  intro x
  obtain ⟨W, -, hx, ⟨D⟩⟩ := h (v x)
  obtain ⟨W', ⟨hW'⟩, hxW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    T'.isBasis_affineOpens (show x ∈ v ⁻¹ᵁ W from hx)
  let W'' : T'.Opens := W'
  have hrange : Set.range (W''.ι ≫ v) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hle y.2
  exact ⟨W'', ⟨hW'⟩, hxW', ⟨D.homRes (IsOpenImmersion.lift W.ι _ hrange)
    (by rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc])⟩⟩

/-- Restriction along a morphism with any target is the restriction with the literal target,
conjugated by `pullbackCongr`. -/
lemma homRes_eq_conj {T T' : Scheme.{u}} (u : T' ⟶ T) {K : T ⟶ Y} {K' : T' ⟶ Y}
    (hu : u ≫ K = K') {A B : Y.Modules} (φ : HomAt K A B) :
    homRes u hu φ = (Scheme.Modules.pullbackCongr hu).inv.app A ≫ homRes u rfl φ ≫
      (Scheme.Modules.pullbackCongr hu).hom.app B := by
  simp [homRes, Scheme.Modules.pullbackCongr]

/-- Two composites of restrictions along equal composites of morphisms agree. -/
lemma homRes_homRes_eq_of_comp {T T₁ T₂ T' : Scheme.{u}} {K : T ⟶ Y} {K₁ : T₁ ⟶ Y}
    {K₂ : T₂ ⟶ Y} {K' : T' ⟶ Y} (u₁ : T₁ ⟶ T) (v₁ : T' ⟶ T₁) (u₂ : T₂ ⟶ T) (v₂ : T' ⟶ T₂)
    (h : v₁ ≫ u₁ = v₂ ≫ u₂) (hu₁ : u₁ ≫ K = K₁) (hv₁ : v₁ ≫ K₁ = K') (hu₂ : u₂ ≫ K = K₂)
    (hv₂ : v₂ ≫ K₂ = K') {A B : Y.Modules} (φ : HomAt K A B) :
    homRes v₁ hv₁ (homRes u₁ hu₁ φ) = homRes v₂ hv₂ (homRes u₂ hu₂ φ) := by
  rw [homRes_homRes, homRes_homRes]
  exact homRes_congr h _ _ φ

/-- `homAt_ext_of_cover` with arbitrary targets of the restrictions. -/
lemma homAt_ext_of_cover' {T : Scheme.{u}} {K : T ⟶ Y} {n : ℕ} (W : Fin n → T.Opens)
    (hW : ⨆ k, W k = ⊤) {A B : Y.Modules} (φ ψ : HomAt K A B) (Kk : ∀ k : Fin n, (W k).toScheme ⟶ Y)
    (hk : ∀ k, (W k).ι ≫ K = Kk k)
    (h : ∀ k, homRes (W k).ι (hk k) φ = homRes (W k).ι (hk k) ψ) : φ = ψ := by
  refine homAt_ext_of_cover W hW φ ψ fun k ↦ ?_
  have h' := h k
  rw [homRes_eq_conj, homRes_eq_conj (W k).ι (hk k) ψ] at h'
  simpa using h'

/-- The restriction `f ∣_ U` of a surjective morphism to the preimage of an open is surjective. -/
lemma surjective_morphismRestrict {X T : Scheme.{u}} (f : X ⟶ T) [Surjective f] (U : T.Opens) :
    Surjective (f ∣_ U) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹_›

/-- **A finite affine cover by opens over which two modules are free.** -/
lemma exists_finite_decomp_cover {T : Scheme.{u}} [CompactSpace T] {K : T ⟶ Y} {A B : Y.Modules}
    (hA : HasLocalDecomp K A) (hB : HasLocalDecomp K B) :
    ∃ (n : ℕ) (W : Fin n → T.Opens), (⨆ k, W k = ⊤) ∧ ∀ k, IsAffineOpen (W k) ∧
      Nonempty (FreeDecomp ((W k).ι ≫ K) A) ∧ Nonempty (FreeDecomp ((W k).ι ≫ K) B) := by
  classical
  have hpt : ∀ x : T, ∃ W : T.Opens, x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (FreeDecomp (W.ι ≫ K) A) ∧ Nonempty (FreeDecomp (W.ι ≫ K) B) := by
    intro x
    obtain ⟨WA, -, hxA, ⟨DA⟩⟩ := hA x
    obtain ⟨WB, -, hxB, ⟨DB⟩⟩ := hB x
    obtain ⟨W, ⟨hW⟩, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      T.isBasis_affineOpens (show x ∈ WA ⊓ WB from ⟨hxA, hxB⟩)
    exact ⟨W, hxW, ⟨hW⟩, ⟨DA.restrictLE (hle.trans inf_le_left)⟩,
      ⟨DB.restrictLE (hle.trans inf_le_right)⟩⟩
  choose Wf hxWf hWf using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (Wf x : Set T))
    (fun x ↦ (Wf x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxWf x⟩)
  refine ⟨t.card, fun k ↦ Wf (t.equivFin.symm k), ?_, fun k ↦ hWf _⟩
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
  obtain ⟨hxt, hy⟩ := Set.mem_iUnion.mp hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  simpa using hy

/-! ### Injectivity over a quasi-compact base -/

/-- **Injectivity over a quasi-compact base.** -/
theorem exists_twistIter_eq_of_homRes_eq_of_compactSpace {T X' : Scheme.{u}} [CompactSpace T]
    (K : T ⟶ Y) (ρ : X' ⟶ T) [Surjective ρ] {A B : Y.Modules} (hA : HasLocalDecomp K A)
    (hB : HasLocalDecomp K B) (a b : HomAt K A B) (hab : homRes ρ rfl a = homRes ρ rfl b) :
    ∃ m, twistIter p hY m a = twistIter p hY m b := by
  classical
  obtain ⟨n, W, hW, hWk⟩ := exists_finite_decomp_cover hA hB
  have hloc : ∀ k, ∃ m, twistIter p hY m (homRes (W k).ι rfl a) =
      twistIter p hY m (homRes (W k).ι rfl b) := by
    intro k
    obtain ⟨hk, ⟨DA⟩, ⟨DB⟩⟩ := hWk k
    have : IsAffine (W k) := hk
    have := surjective_morphismRestrict ρ (W k)
    refine exists_twistIter_eq_of_homRes_eq ((W k).ι ≫ K) (ρ ∣_ (W k)) DA DB _ _ ?_
    have hjk : (ρ ⁻¹ᵁ W k).ι ≫ ρ ≫ K = (ρ ∣_ W k) ≫ (W k).ι ≫ K := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have key : ∀ φ : HomAt K A B, homRes (ρ ∣_ W k) rfl (homRes (W k).ι rfl φ) =
        homRes (ρ ⁻¹ᵁ W k).ι hjk (homRes ρ rfl φ) := fun φ ↦
      homRes_homRes_eq_of_comp (W k).ι (ρ ∣_ W k) ρ (ρ ⁻¹ᵁ W k).ι
        (morphismRestrict_ι ρ (W k)) rfl rfl rfl hjk φ
    rw [key a, key b, hab]
  choose m hm using hloc
  let M := Finset.univ.sup m
  refine ⟨M, homAt_ext_of_cover' W hW _ _ _ (fun k ↦ comp_frobPow (W k).ι rfl M) fun k ↦ ?_⟩
  rw [homRes_twistIter (W k).ι rfl M a, homRes_twistIter (W k).ι rfl M b]
  exact twistIter_eq_of_le (hm k) (Finset.le_sup (Finset.mem_univ k))

/-! ### Transport along the identity -/

/-- **Restriction along the identity does nothing.** -/
lemma homRes_one {T : Scheme.{u}} {K : T ⟶ Y} (h : 𝟙 T ≫ K = K) {A B : Y.Modules}
    (φ : HomAt K A B) : homRes (𝟙 T) h φ = φ := by
  have hb := presheafHom_map_eq_homRes A B (𝟙 (Over.mk K)) φ
  have hid : (modulePullbackPseudofunctor.presheafHom A B).map (𝟙 (Over.mk K)).op φ = φ :=
    Functor.map_id_apply _ _ _
  exact (homRes_congr (by simp) _ _ φ).trans (hb.symm.trans hid)

/-- Transports along the identity compose. -/
lemma homRes_one_one {T : Scheme.{u}} {K₁ K₂ K₃ : T ⟶ Y} (h₁ : 𝟙 T ≫ K₁ = K₂)
    (h₂ : 𝟙 T ≫ K₂ = K₃) {A B : Y.Modules} (φ : HomAt K₁ A B) :
    homRes (𝟙 T) h₂ (homRes (𝟙 T) h₁ φ) =
      homRes (𝟙 T) (by rw [← h₂, ← h₁]; simp) φ := by
  rw [homRes_homRes]
  exact homRes_congr (by simp) _ _ φ

/-- `frobPow` is additive in the exponent: `d` further powers after `N` are `N + d` powers. -/
lemma frobPow_add {T : Scheme.{u}} (H : T ⟶ Y) (N : ℕ) :
    ∀ d, frobPow p hY (frobPow p hY H N) d = frobPow p hY H (N + d)
  | 0 => rfl
  | d + 1 => by
    show frobOf p hY (frobPow p hY (frobPow p hY H N) d) ≫ frobPow p hY (frobPow p hY H N) d =
      frobOf p hY (frobPow p hY H (N + d)) ≫ frobPow p hY H (N + d)
    rw [frobPow_add H N d]

/-- **Iterated twists compose**, up to the transport along `frobPow_add`. -/
lemma twistIter_twistIter {T : Scheme.{u}} {H : T ⟶ Y} {A B : Y.Modules} (φ : HomAt H A B)
    (N : ℕ) : ∀ d, homRes (𝟙 T) (by rw [Category.id_comp, frobPow_add])
      (twistIter p hY d (twistIter p hY N φ)) = twistIter p hY (N + d) φ
  | 0 => homRes_one _ _
  | d + 1 => by
    have h := homRes_twist (p := p) (hY := hY) (𝟙 T)
      (show 𝟙 T ≫ frobPow p hY (frobPow p hY H N) d = frobPow p hY H (N + d) by
        rw [Category.id_comp, frobPow_add]) (twistIter p hY d (twistIter p hY N φ))
    exact (homRes_congr rfl _ _ _).trans
      (h.trans (congrArg (twist p hY) (twistIter_twistIter φ N d)))

/-- Restricting a transported `D`-fold twist is transporting the `D`-fold twist of the
restriction. -/
private lemma homRes_homRes_one_twistIter {T T' : Scheme.{u}} {K : T ⟶ Y} {K' : T' ⟶ Y}
    (u : T' ⟶ T) (hu : u ≫ K = K') {A B : Y.Modules} (N D : ℕ) (a : HomAt (frobPow p hY K N) A B) :
    homRes u (comp_frobPow u hu (N + D))
      (homRes (𝟙 T) (by rw [Category.id_comp, frobPow_add]) (twistIter p hY D a)) =
    homRes (𝟙 T') (by rw [Category.id_comp, frobPow_add])
      (twistIter p hY D (homRes u (comp_frobPow u hu N) a)) := by
  rw [homRes_homRes_eq_of_comp (𝟙 _) u u (𝟙 _) (by simp) _ _
    (comp_frobPow u (comp_frobPow u hu N) D) (by rw [Category.id_comp, frobPow_add]) _,
    homRes_twistIter u (comp_frobPow u hu N) D a]

/-- Local decompositions persist under the Frobenius. -/
lemma HasLocalDecomp.frobPow {T : Scheme.{u}} {K : T ⟶ Y} {A : Y.Modules}
    (h : HasLocalDecomp K A) (N : ℕ) : HasLocalDecomp (frobPow p hY K N) A := by
  intro x
  obtain ⟨W, hW, hx, ⟨D⟩⟩ := h x
  exact ⟨W, hW, hx, ⟨(D.twistIter p hY N).homRes (𝟙 _)
    (by rw [Category.id_comp, comp_frobPow W.ι rfl N])⟩⟩

/-- **Solutions of the affine free case exist at every large level.** -/
theorem exists_level_homRes_eq_twistIter {V X' : Scheme.{u}} [IsAffine V] (H : V ⟶ Y)
    (ρ : X' ⟶ V) [IsProper ρ] [Surjective ρ] [GeometricallyConnected ρ] {A B : Y.Modules}
    (DA : FreeDecomp H A) (DB : FreeDecomp H B) (c : HomAt (ρ ≫ H) A B) :
    ∃ m, ∀ M, m ≤ M → ∃ a : HomAt (frobPow p hY H M) A B,
      homRes ρ (comp_frobPow ρ rfl M) a = twistIter p hY M c := by
  obtain ⟨m, a, ha⟩ := exists_homRes_eq_twistIter (p := p) (hY := hY) H ρ DA DB c
  refine ⟨m, fun M hM ↦ ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction d with
  | zero => exact ⟨a, ha⟩
  | succ d ih =>
    obtain ⟨a', ha'⟩ := ih (Nat.le_add_right m d)
    exact ⟨twist p hY a',
      (homRes_twist ρ (comp_frobPow ρ rfl (m + d)) a').trans (congrArg (twist p hY) ha')⟩

/-! ### Surjectivity over a quasi-compact quasi-separated base -/

/-- The bookkeeping of one overlap: restricting a local solution to a smaller open and then
along the base change of `ρ` is restricting the twisted morphism upstairs. -/
lemma homRes_solution_restrict {T X' W Wo XW XWo : Scheme.{u}} (K : T ⟶ Y) (ρ : X' ⟶ T)
    (ιW : W ⟶ T) (ιo : Wo ⟶ T) (r : Wo ⟶ W) (hr : r ≫ ιW = ιo) (ρW : XW ⟶ W) (jW : XW ⟶ X')
    (hW : jW ≫ ρ = ρW ≫ ιW) (ρo : XWo ⟶ Wo) (jo : XWo ⟶ X') (q : XWo ⟶ XW) (hq : q ≫ jW = jo)
    (hqρ : q ≫ ρW = ρo ≫ r) (N : ℕ) {A B : Y.Modules} (c : HomAt (ρ ≫ K) A B)
    (a : HomAt (frobPow p hY (ιW ≫ K) N) A B)
    (ha : homRes ρW (comp_frobPow ρW rfl N) a = twistIter p hY N
      (homRes jW (show jW ≫ ρ ≫ K = ρW ≫ ιW ≫ K by rw [← Category.assoc, hW, Category.assoc])
        c)) :
    homRes ρo rfl (homRes r (comp_frobPow r (show r ≫ ιW ≫ K = ιo ≫ K by
      rw [← Category.assoc, hr]) N) a) =
      homRes jo (show jo ≫ frobPow p hY (ρ ≫ K) N = ρo ≫ frobPow p hY (ιo ≫ K) N by
        rw [comp_frobPow jo rfl N, comp_frobPow ρo rfl N]; congr 1
        simp only [← hq, ← hr, Category.assoc, reassoc_of% hW, reassoc_of% hqρ])
        (twistIter p hY N c) := by
  have hjW : jW ≫ ρ ≫ K = ρW ≫ ιW ≫ K := by rw [← Category.assoc, hW, Category.assoc]
  rw [homRes_homRes_eq_of_comp r ρo ρW q hqρ.symm _ rfl (comp_frobPow ρW rfl N)
    (by rw [comp_frobPow q rfl N, comp_frobPow ρo rfl N]; congr 1
        simp only [← hr, reassoc_of% hqρ, Category.assoc]) a, ha, ← homRes_twistIter jW hjW N c,
    homRes_homRes]
  exact homRes_congr hq _ _ _

/-- **Surjectivity over a quasi-compact quasi-separated base.** -/
theorem exists_homRes_eq_twistIter_of_qcqs {T X' : Scheme.{u}} [CompactSpace T]
    [QuasiSeparatedSpace T] (K : T ⟶ Y) (ρ : X' ⟶ T) [IsProper ρ] [Surjective ρ]
    [GeometricallyConnected ρ] {A B : Y.Modules} (hA : HasLocalDecomp K A)
    (hB : HasLocalDecomp K B) (c : HomAt (ρ ≫ K) A B) :
    ∃ L, ∃ t : HomAt (frobPow p hY K L) A B,
      homRes ρ (comp_frobPow ρ rfl L) t = twistIter p hY L c := by
  classical
  obtain ⟨n, W, hW, hWk⟩ := exists_finite_decomp_cover hA hB
  have hjk : ∀ k, (ρ ⁻¹ᵁ W k).ι ≫ ρ ≫ K = (ρ ∣_ W k) ≫ (W k).ι ≫ K := fun k ↦ by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have hloc : ∀ k, ∃ m, ∀ M, m ≤ M → ∃ a : HomAt (frobPow p hY ((W k).ι ≫ K) M) A B,
      homRes (ρ ∣_ W k) (comp_frobPow _ rfl M) a =
        twistIter p hY M (homRes (ρ ⁻¹ᵁ W k).ι (hjk k) c) := by
    intro k
    obtain ⟨hk, ⟨DA⟩, ⟨DB⟩⟩ := hWk k
    have : IsAffine (W k) := hk
    exact exists_level_homRes_eq_twistIter _ (ρ ∣_ W k) DA DB _
  choose m hm using hloc
  set N := Finset.univ.sup m
  choose a ha using fun k ↦ hm k N (Finset.le_sup (Finset.mem_univ k))
  have hr : ∀ (j : Fin n) (V : T.Opens) (hV : V ≤ W j),
      T.homOfLE hV ≫ (W j).ι ≫ K = V.ι ≫ K := fun j V hV ↦ by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hres := fun (j : Fin n) (V : T.Opens) (hV : V ≤ W j) ↦
    homRes_solution_restrict K ρ (W j).ι V.ι _ (Scheme.homOfLE_ι _ _) (ρ ∣_ W j)
      (ρ ⁻¹ᵁ W j).ι (morphismRestrict_ι ρ (W j)).symm (ρ ∣_ V) (ρ ⁻¹ᵁ V).ι
      (X'.homOfLE (ρ.preimage_mono hV)) (Scheme.homOfLE_ι _ _)
      (morphismRestrict_homOfLE ρ _ _ hV).symm N c (a j) (ha j)
  have hcompat : ∀ k l, ∃ d, twistIter p hY d
      (homRes (T.homOfLE (inf_le_left : W k ⊓ W l ≤ W k)) (comp_frobPow _ (hr k _ inf_le_left) N)
        (a k)) = twistIter p hY d
      (homRes (T.homOfLE (inf_le_right : W k ⊓ W l ≤ W l))
        (comp_frobPow _ (hr l _ inf_le_right) N) (a l)) := by
    intro k l
    have hcpt : IsCompact ((W k ⊓ W l : T.Opens) : Set T) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W k).isOpen (hWk k).1.isCompact (W l).isOpen
        (hWk l).1.isCompact
    have : CompactSpace (W k ⊓ W l : T.Opens).toScheme := isCompact_iff_compactSpace.mp hcpt
    have := surjective_morphismRestrict ρ (W k ⊓ W l)
    exact exists_twistIter_eq_of_homRes_eq_of_compactSpace _ (ρ ∣_ (W k ⊓ W l))
      ((hA.comp _).frobPow N) ((hB.comp _).frobPow N) _ _
      ((hres k _ inf_le_left).trans (hres l _ inf_le_right).symm)
  choose d hd using hcompat
  set D := Finset.univ.sup (fun kl : Fin n × Fin n ↦ d kl.1 kl.2)
  have hdD : ∀ k l, d k l ≤ D := fun k l ↦
    Finset.le_sup (f := fun kl : Fin n × Fin n ↦ d kl.1 kl.2) (Finset.mem_univ (k, l))
  -- solutions at the common level `N + D`
  have hL : ∀ k, 𝟙 _ ≫ frobPow p hY (frobPow p hY ((W k).ι ≫ K) N) D =
      frobPow p hY ((W k).ι ≫ K) (N + D) := fun k ↦ by rw [Category.id_comp, frobPow_add]
  let sol : ∀ k, HomAt (frobPow p hY ((W k).ι ≫ K) (N + D)) A B :=
    fun k ↦ homRes (𝟙 _) (hL k) (twistIter p hY D (a k))
  have hsol : ∀ k, homRes (ρ ∣_ W k) (comp_frobPow _ rfl (N + D)) (sol k) =
      twistIter p hY (N + D) (homRes (ρ ⁻¹ᵁ W k).ι (hjk k) c) := by
    intro k
    rw [homRes_homRes_one_twistIter (ρ ∣_ W k) rfl N D (a k), ha k]
    exact twistIter_twistIter _ N D
  have hover : ∀ k l,
      homRes (T.homOfLE (inf_le_left : W k ⊓ W l ≤ W k))
        (comp_frobPow _ (hr k _ inf_le_left) (N + D)) (sol k) =
      homRes (T.homOfLE (inf_le_right : W k ⊓ W l ≤ W l))
        (comp_frobPow _ (hr l _ inf_le_right) (N + D)) (sol l) := by
    intro k l
    rw [homRes_homRes_one_twistIter _ (hr k _ inf_le_left) N D (a k),
      homRes_homRes_one_twistIter _ (hr l _ inf_le_right) N D (a l),
      twistIter_eq_of_le (hd k l) (hdD k l)]
  -- glueing
  have hs := (Presieve.isSheafFor_arrows_iff _ _).mp (isSheafFor_presheafHom_zariski_over A B
    (Over.mk (frobPow p hY K (N + D))) (fun k ↦ (W k).ι)
    (ofArrows_opens_mem_zariskiPrecoverage W hW))
  have hx : ∀ k, 𝟙 _ ≫ frobPow p hY ((W k).ι ≫ K) (N + D) =
      (W k).ι ≫ frobPow p hY K (N + D) := fun k ↦ by
    rw [Category.id_comp, comp_frobPow (W k).ι rfl (N + D)]
  obtain ⟨t, ht, -⟩ := hs (fun k ↦ homRes (𝟙 _) (hx k) (sol k)) (by
    intro k l Z gk gl hkl
    rw [presheafHom_map_eq_homRes, presheafHom_map_eq_homRes]
    dsimp only
    have hkl' : gk.left ≫ (W k).ι = gl.left ≫ (W l).ι := congrArg CommaMorphism.left hkl
    have hrange : Set.range (gk.left ≫ (W k).ι) ⊆ Set.range (W k ⊓ W l).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, ?_⟩
      · exact (gk.left y).2
      · rw [hkl']; exact (gl.left y).2
    let z := IsOpenImmersion.lift (W k ⊓ W l).ι (gk.left ≫ (W k).ι) hrange
    have hz : z ≫ (W k ⊓ W l).ι = gk.left ≫ (W k).ι := IsOpenImmersion.lift_fac _ _ _
    have hzk : gk.left ≫ 𝟙 _ = z ≫ T.homOfLE (inf_le_left : W k ⊓ W l ≤ W k) := by
      rw [Category.comp_id, ← cancel_mono (W k).ι, Category.assoc, Scheme.homOfLE_ι, hz]
    have hzl : gl.left ≫ 𝟙 _ = z ≫ T.homOfLE (inf_le_right : W k ⊓ W l ≤ W l) := by
      rw [Category.comp_id, ← cancel_mono (W l).ι, Category.assoc, Scheme.homOfLE_ι, hz, hkl']
    have hZ : z ≫ frobPow p hY ((W k ⊓ W l).ι ≫ K) (N + D) = Z.hom := by
      rw [← Over.w gk]
      show _ = gk.left ≫ (W k).ι ≫ frobPow p hY K (N + D)
      rw [comp_frobPow (W k).ι rfl (N + D), comp_frobPow gk.left rfl (N + D),
        comp_frobPow z rfl (N + D), ← Category.assoc z, hz, Category.assoc]
    exact (homRes_homRes_eq_of_comp (𝟙 _) gk.left _ z hzk (hx k) _
      (comp_frobPow _ (hr k _ inf_le_left) (N + D)) hZ (sol k)).trans
      ((congrArg (homRes z hZ) (hover k l)).trans
        (homRes_homRes_eq_of_comp (𝟙 _) gl.left _ z hzl (hx l) _
          (comp_frobPow _ (hr l _ inf_le_right) (N + D)) hZ (sol l)).symm))
  refine ⟨N + D, t, ?_⟩
  have hcov : ⨆ k, ρ ⁻¹ᵁ W k = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx' : ρ x ∈ (⨆ k, W k : T.Opens) := hW ▸ trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩
  refine homAt_ext_of_cover' (fun k ↦ ρ ⁻¹ᵁ W k) hcov _ _
    (fun k ↦ frobPow p hY ((ρ ∣_ W k) ≫ (W k).ι ≫ K) (N + D))
    (fun k ↦ comp_frobPow _ (hjk k) (N + D)) fun k ↦ ?_
  have hv₂ : (ρ ∣_ W k) ≫ (W k).ι ≫ frobPow p hY K (N + D) =
      frobPow p hY ((ρ ∣_ W k) ≫ (W k).ι ≫ K) (N + D) := by
    rw [← Category.assoc, comp_frobPow _ rfl (N + D), Category.assoc]
  have e1 := homRes_homRes_eq_of_comp ρ (ρ ⁻¹ᵁ W k).ι (W k).ι (ρ ∣_ W k)
    (morphismRestrict_ι ρ (W k)).symm (comp_frobPow ρ rfl (N + D))
    (comp_frobPow _ (hjk k) (N + D)) rfl hv₂ t
  refine e1.trans ?_
  have e2 : homRes (W k).ι rfl t = homRes (𝟙 _) (hx k) (sol k) := by
    exact (presheafHom_map_eq_homRes A B (T := Over.mk (frobPow p hY K (N + D)))
      (Over.homMk (W k).ι : Over.mk ((W k).ι ≫ frobPow p hY K (N + D)) ⟶
        Over.mk (frobPow p hY K (N + D))) t).symm.trans (ht k)
  exact (congrArg (homRes (ρ ∣_ W k) hv₂) e2).trans ((homRes_homRes _ _ _ _ _).trans
    ((homRes_congr (Category.comp_id _) _ (comp_frobPow _ rfl (N + D)) (sol k)).trans
      ((hsol k).trans (homRes_twistIter _ (hjk k) (N + D) c).symm)))

end AlgebraicGeometry

end
