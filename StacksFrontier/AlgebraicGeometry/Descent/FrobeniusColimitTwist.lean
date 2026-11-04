module

public import StacksFrontier.AlgebraicGeometry.Modules.PullbackCanonical
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullback

/-!
# Frobenius-twisted morphisms of modules over schemes over `Y`

Let `p` be a prime and `Y` a scheme in characteristic `p`. For a scheme `h : T ⟶ Y` over `Y`
write `h_k = F_T^k ≫ h : T ⟶ Y`. For `𝒪_Y`-modules `A` and `B` the morphisms
`h_k^*A ⟶ h_k^*B` are the morphisms `F^{k,*}h^*A ⟶ F^{k,*}h^*B` of Stacks Tag 0EXA read through
single pullbacks; pullback along `F_T` is the **Frobenius twist** from level `k` to level `k + 1`,
and pullback along a morphism `u : T' ⟶ T` over `Y` is **restriction**. This file sets up both
operations with the comparison isomorphisms `Scheme.Modules.pullbackComp` and
`Scheme.Modules.pullbackCongr` of the pullback
pseudofunctor, and proves the two coherences the Zariski-local arguments of Stacks Tag 0EXH need:

* `AlgebraicGeometry.homRes_homRes`: restriction is functorial;
* `AlgebraicGeometry.homRes_twist`: **the Frobenius twist commutes with restriction.**

Both are reduced to the uniqueness of canonical comparisons
(`AlgebraicGeometry.Scheme.Modules.IsCanonical.ext`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {Y : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hY : IsInCharacteristic Y p)

/-- The absolute Frobenius of a scheme over `Y`. -/
abbrev frobOf {T : Scheme.{u}} (h : T ⟶ Y) : T ⟶ T :=
  absoluteFrobenius T p (isInCharacteristic_of_hom h p hY)

/-- The morphisms `h_k = F_T^k ≫ h`, with `h_{k+1} = F_T ≫ h_k`. -/
def frobIter {T : Scheme.{u}} (h : T ⟶ Y) : ℕ → (T ⟶ Y)
  | 0 => h
  | k + 1 => frobOf p hY h ≫ frobIter h k

variable {p hY}

/-- `h_0 = h`. -/
@[simp] lemma frobIter_zero {T : Scheme.{u}} (h : T ⟶ Y) : frobIter p hY h 0 = h := rfl

/-- `h_{k+1} = F_T ≫ h_k`. -/
lemma frobIter_succ {T : Scheme.{u}} (h : T ⟶ Y) (k : ℕ) :
    frobIter p hY h (k + 1) = frobOf p hY h ≫ frobIter p hY h k := rfl

/-- `u ≫ F_T = F_{T'} ≫ u` for `u ≫ H = H'`, by the naturality of the absolute Frobenius. -/
private lemma comp_frobOf_comm {T T' : Scheme.{u}} (u : T' ⟶ T) {H : T ⟶ Y} {H' : T' ⟶ Y}
    (hu : u ≫ H = H') : u ≫ frobOf p hY H = frobOf p hY H' ≫ u := by
  subst hu
  exact (absoluteFrobenius_naturality u p _ _).symm

/-- `u ≫ h_k = (u ≫ h)_k`, by the naturality of the absolute Frobenius (Stacks Tag 0CC7). -/
lemma comp_frobIter {T T' : Scheme.{u}} (u : T' ⟶ T) (h : T ⟶ Y) (h' : T' ⟶ Y)
    (hu : u ≫ h = h') (k : ℕ) : u ≫ frobIter p hY h k = frobIter p hY h' k := by
  subst hu
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [frobIter_succ, frobIter_succ, ← ih, ← Category.assoc, ← Category.assoc,
      comp_frobOf_comm u rfl]

/-- Morphisms `H^*A ⟶ H^*B` over a scheme `H : T ⟶ Y` over `Y`. -/
abbrev HomAt {T : Scheme.{u}} (H : T ⟶ Y) (A B : Y.Modules) : Type u :=
  (Scheme.Modules.pullback H).obj A ⟶ (Scheme.Modules.pullback H).obj B

variable (p hY)

/-- **The Frobenius twist**: pullback along the absolute Frobenius `F_T`, from `H^*A ⟶ H^*B` to
`(F_T ≫ H)^*A ⟶ (F_T ≫ H)^*B`. -/
def twist {T : Scheme.{u}} {H : T ⟶ Y} {A B : Y.Modules} (φ : HomAt H A B) :
    HomAt (frobOf p hY H ≫ H) A B :=
  (Scheme.Modules.pullbackComp (frobOf p hY H) H).inv.app A ≫
    (Scheme.Modules.pullback (frobOf p hY H)).map φ ≫
      (Scheme.Modules.pullbackComp (frobOf p hY H) H).hom.app B

variable {p hY}

/-- **Restriction** along a morphism `u : T' ⟶ T` over `Y`. -/
def homRes {T T' : Scheme.{u}} (u : T' ⟶ T) {H : T ⟶ Y} {H' : T' ⟶ Y} (hu : u ≫ H = H')
    {A B : Y.Modules} (φ : HomAt H A B) : HomAt H' A B :=
  (Scheme.Modules.pullbackCongr hu).inv.app A ≫
    (Scheme.Modules.pullbackComp u H).inv.app A ≫ (Scheme.Modules.pullback u).map φ ≫
      (Scheme.Modules.pullbackComp u H).hom.app B ≫ (Scheme.Modules.pullbackCongr hu).hom.app B

/-! ### Algebra -/

section Algebra

variable {T T' : Scheme.{u}} {H : T ⟶ Y} {A B C : Y.Modules}

/-- The Frobenius twist preserves composition. -/
lemma twist_comp (φ : HomAt H A B) (ψ : HomAt H B C) :
    twist p hY (φ ≫ ψ) = twist p hY φ ≫ twist p hY ψ := by
  simp only [twist, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The Frobenius twist of an identity morphism is the identity. -/
@[simp]
lemma twist_id : twist p hY (𝟙 ((Scheme.Modules.pullback H).obj A)) = 𝟙 _ := by
  simp [twist]

/-- The Frobenius twist is additive. -/
lemma twist_add (φ ψ : HomAt H A B) : twist p hY (φ + ψ) = twist p hY φ + twist p hY ψ := by
  simp only [twist, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- The Frobenius twist preserves subtraction. -/
lemma twist_sub (φ ψ : HomAt H A B) : twist p hY (φ - ψ) = twist p hY φ - twist p hY ψ := by
  simp only [twist, Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub]

/-- The Frobenius twist preserves finite sums. -/
lemma twist_sum {ι : Type} (s : Finset ι) (φ : ι → HomAt H A B) :
    twist p hY (∑ i ∈ s, φ i) = ∑ i ∈ s, twist p hY (φ i) := by
  simp only [twist, Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]

variable {u : T' ⟶ T} {H' : T' ⟶ Y} (hu : u ≫ H = H')

/-- Restriction preserves composition. -/
lemma homRes_comp (φ : HomAt H A B) (ψ : HomAt H B C) :
    homRes u hu (φ ≫ ψ) = homRes u hu φ ≫ homRes u hu ψ := by
  simp only [homRes, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Restriction of an identity morphism is the identity. -/
@[simp]
lemma homRes_id : homRes u hu (𝟙 ((Scheme.Modules.pullback H).obj A)) = 𝟙 _ := by
  simp [homRes]

/-- Restriction is additive. -/
lemma homRes_add (φ ψ : HomAt H A B) :
    homRes u hu (φ + ψ) = homRes u hu φ + homRes u hu ψ := by
  simp only [homRes, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- Restriction preserves subtraction. -/
lemma homRes_sub (φ ψ : HomAt H A B) :
    homRes u hu (φ - ψ) = homRes u hu φ - homRes u hu ψ := by
  simp only [homRes, Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub]

/-- Restriction preserves finite sums. -/
lemma homRes_sum {ι : Type} (s : Finset ι) (φ : ι → HomAt H A B) :
    homRes u hu (∑ i ∈ s, φ i) = ∑ i ∈ s, homRes u hu (φ i) := by
  simp only [homRes, Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]

end Algebra

/-! ### Coherence -/

/-- Components of canonical transformations with the same ends agree. -/
lemma app_eq_of_isCanonical {Z W : Scheme.{u}} {k₁ k₂ : Z ⟶ W}
    {α β : Scheme.Modules.pullback k₂ ⟶ Scheme.Modules.pullback k₁}
    (hα : Scheme.Modules.IsCanonical α) (hβ : Scheme.Modules.IsCanonical β) (A : W.Modules) :
    α.app A = β.app A := by
  rw [Scheme.Modules.IsCanonical.ext hα hβ]

/-- Two isomorphisms `H''^* ≅ H^* ⋙ K^*` agree if both are canonical after composing with
`pullbackComp K H`. -/
private lemma iso_eq_of_isCanonical_comp {Z W V : Scheme.{u}} {K : Z ⟶ W} {H : W ⟶ V}
    {H'' : Z ⟶ V} (X Y : Scheme.Modules.pullback H'' ≅
      Scheme.Modules.pullback H ⋙ Scheme.Modules.pullback K)
    (hX : Scheme.Modules.IsCanonical (X.hom ≫ (Scheme.Modules.pullbackComp K H).hom))
    (hY : Scheme.Modules.IsCanonical (Y.hom ≫ (Scheme.Modules.pullbackComp K H).hom)) :
    X = Y :=
  Iso.ext ((cancel_mono _).mp (Scheme.Modules.IsCanonical.ext hX hY))

/-- **Restriction is functorial.** -/
lemma homRes_homRes {T T' T'' : Scheme.{u}} (u : T' ⟶ T) (v : T'' ⟶ T') {H : T ⟶ Y}
    {H' : T' ⟶ Y} {H'' : T'' ⟶ Y} (hu : u ≫ H = H') (hv : v ≫ H' = H'')
    {A B : Y.Modules} (φ : HomAt H A B) :
    homRes v hv (homRes u hu φ) =
      homRes (v ≫ u) (by rw [Category.assoc, hu, hv]) φ := by
  have e₃ : (v ≫ u) ≫ H = H'' := by rw [Category.assoc, hu, hv]
  let Xiso : Scheme.Modules.pullback H'' ≅
      Scheme.Modules.pullback H ⋙ Scheme.Modules.pullback (v ≫ u) :=
    (Scheme.Modules.pullbackCongr hv).symm ≪≫ (Scheme.Modules.pullbackComp v H').symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.pullbackCongr hu).symm _ ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pullbackComp u H).symm _ ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Scheme.Modules.pullbackComp v u)
  let Yiso : Scheme.Modules.pullback H'' ≅
      Scheme.Modules.pullback H ⋙ Scheme.Modules.pullback (v ≫ u) :=
    (Scheme.Modules.pullbackCongr e₃).symm ≪≫ (Scheme.Modules.pullbackComp (v ≫ u) H).symm
  have hXY : Xiso = Yiso := by
    refine iso_eq_of_isCanonical_comp _ _ ?_ ?_
    · have h := Scheme.Modules.isCanonical_comp (Scheme.Modules.isCanonical_pullbackCongr_inv hv)
          (Scheme.Modules.isCanonical_comp
            (Scheme.Modules.isCanonical_whiskerRight
              (Scheme.Modules.isCanonical_pullbackCongr_inv hu) v)
            (Scheme.Modules.isCanonical_assoc v u H))
      convert h using 1
      simp only [Xiso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Category.assoc, Iso.hom_inv_id_assoc]
    · simpa only [Yiso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id] using Scheme.Modules.isCanonical_pullbackCongr_inv e₃
  have hL : homRes v hv (homRes u hu φ) = Xiso.hom.app A ≫
      (Scheme.Modules.pullback (v ≫ u)).map φ ≫ Xiso.inv.app B := by
    have hn := (Scheme.Modules.pullbackComp v u).hom.naturality φ
    simp only [Functor.comp_map] at hn
    simp only [homRes, Xiso, Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp]
    rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]
  have hR : homRes (v ≫ u) e₃ φ = Yiso.hom.app A ≫
      (Scheme.Modules.pullback (v ≫ u)).map φ ≫ Yiso.inv.app B := by
    simp only [homRes, Yiso, Category.assoc, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, NatTrans.comp_app]
  rw [hL, hR, hXY]

/-- `u ≫ F_T ≫ H = F_{T'} ≫ H'` for `u ≫ H = H'`. -/
lemma comp_frobOf_comp {T T' : Scheme.{u}} (u : T' ⟶ T) {H : T ⟶ Y} {H' : T' ⟶ Y}
    (hu : u ≫ H = H') : u ≫ frobOf p hY H ≫ H = frobOf p hY H' ≫ H' := by
  rw [← Category.assoc, comp_frobOf_comm u hu, Category.assoc, hu]

/-- **The Frobenius twist commutes with restriction.** -/
lemma homRes_twist {T T' : Scheme.{u}} (u : T' ⟶ T) {H : T ⟶ Y} {H' : T' ⟶ Y}
    (hu : u ≫ H = H') {A B : Y.Modules} (φ : HomAt H A B) :
    homRes u (comp_frobOf_comp u hu) (twist p hY φ) = twist p hY (homRes u hu φ) := by
  set FT := frobOf p hY H
  set FT' := frobOf p hY H'
  have hcomm : u ≫ FT = FT' ≫ u := comp_frobOf_comm u hu
  let Cn := Scheme.Modules.pullbackCongr hcomm
  let Xiso : Scheme.Modules.pullback (FT' ≫ H') ≅
      Scheme.Modules.pullback H ⋙ Scheme.Modules.pullback (FT' ≫ u) :=
    (Scheme.Modules.pullbackCongr (comp_frobOf_comp u hu)).symm ≪≫
      (Scheme.Modules.pullbackComp u (FT ≫ H)).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pullbackComp FT H).symm _ ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Scheme.Modules.pullbackComp u FT) ≪≫
              Functor.isoWhiskerLeft _ Cn
  let Yiso : Scheme.Modules.pullback (FT' ≫ H') ≅
      Scheme.Modules.pullback H ⋙ Scheme.Modules.pullback (FT' ≫ u) :=
    (Scheme.Modules.pullbackComp FT' H').symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.pullbackCongr hu).symm _ ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pullbackComp u H).symm _ ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Scheme.Modules.pullbackComp FT' u)
  have hXY : Xiso = Yiso := by
    refine iso_eq_of_isCanonical_comp _ _ ?_ ?_
    · have h := Scheme.Modules.isCanonical_comp
        (Scheme.Modules.isCanonical_pullbackCongr_inv (comp_frobOf_comp u hu))
        (Scheme.Modules.isCanonical_comp (Scheme.Modules.isCanonical_assoc u FT H)
          (Scheme.Modules.isCanonical_whiskerLeft
            (Scheme.Modules.isCanonical_pullbackCongr hcomm) H))
      convert h using 1
      simp only [Xiso, Cn, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Category.assoc, Iso.hom_inv_id_assoc]
    · have h := Scheme.Modules.isCanonical_comp
        (Scheme.Modules.isCanonical_whiskerRight
          (Scheme.Modules.isCanonical_pullbackCongr_inv hu) FT')
        (Scheme.Modules.isCanonical_assoc FT' u H)
      convert h using 1
      simp only [Yiso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have hL : homRes u (comp_frobOf_comp u hu) (twist p hY φ) = Xiso.hom.app A ≫
      (Scheme.Modules.pullback (FT' ≫ u)).map φ ≫ Xiso.inv.app B := by
    have hn := (Scheme.Modules.pullbackComp u FT).hom.naturality φ
    have hc := Cn.hom.naturality φ
    simp only [Functor.comp_map] at hn
    simp only [homRes, twist, Xiso, Functor.map_comp, Category.assoc, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp]
    rw [← reassoc_of% hc, ← reassoc_of% hn, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  have hR : twist p hY (homRes u hu φ) = Yiso.hom.app A ≫
      (Scheme.Modules.pullback (FT' ≫ u)).map φ ≫ Yiso.inv.app B := by
    have hn := (Scheme.Modules.pullbackComp FT' u).hom.naturality φ
    simp only [Functor.comp_map] at hn
    simp only [homRes, twist, Yiso, Functor.map_comp, Category.assoc, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp]
    rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]
  rw [hL, hR, hXY]

end AlgebraicGeometry

end
