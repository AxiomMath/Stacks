module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ClosedImmersionIdealSheaves

/-!
# Fibre powers of a family of closed immersions

Let `ν : Y ⟶ S` be a morphism and let `ε i : A i ⟶ Y` be an open cover of `Y` by opens each of
which maps to `S` by a closed immersion, say with `A i` isomorphic over `S` to the closed
subscheme cut out by `I i : S.IdealSheafData`. This file decomposes the `n`-fold fibre power of
`ν` into opens indexed by the `n`-tuples `t : Fin n → ι`, and identifies the open indexed by `t`
with the scheme theoretic intersection of the `n` closed subschemes `I (t 0), …, I (t (n - 1))`,
that is, with the closed subscheme cut out by `⨆ k, I (t k)`.

## Main definitions

* `AlgebraicGeometry.fibrePowerTupleOpens` is the open of the `n`-fold fibre power of `ν` whose
  `k`-th coordinate lies in `A (t k)`.

## Main results

* `AlgebraicGeometry.exists_mem_fibrePowerTupleOpens`: the tuple opens cover the fibre power.
* `AlgebraicGeometry.injective_of_mem_fibrePowerDistinctLocus`: a point of a tuple open that lies
  off the fat diagonal forces the tuple to be injective.
* `AlgebraicGeometry.fibrePowerTupleOpens_subset_distinctLocus`: conversely, if the members of the
  family have pairwise disjoint ranges then an injective tuple's open lies off the fat diagonal.
* `AlgebraicGeometry.exists_iso_fibrePowerTupleOpens`: the open indexed by `t` is, over `S`, the
  closed subscheme cut out by `⨆ k, I (t k)`.
* `AlgebraicGeometry.exists_iso_pullback_subschemeι_sup`: the fibre product over `S` of two closed
  subschemes of `S` is the closed subscheme cut out by the supremum of their ideal sheaves.
* `AlgebraicGeometry.exists_iso_pullback_preimage_inf`: the intersection of the preimages of two
  opens in a fibre product is a fibre product of those two opens.

## Implementation notes

The identification of a tuple open with an intersection of closed subschemes is phrased as the
existence of an isomorphism compatible with the two morphisms to `S`, rather than as an equality
of subobjects, because the fibre power is built by iterated choice of pullbacks and carries no
canonical closed immersion into `S`. The same convention is used for the hypothesis on the
family: `A i` is only assumed isomorphic over `S` to `(I i).subscheme`.

No `Mono` hypothesis is needed in `AlgebraicGeometry.lift_eq_comp_diagonal`: the two coordinates
of the lift already agree as morphisms, so the factorisation through the diagonal is formal.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 0C4I](https://stacks.math.columbia.edu/tag/0C4I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

section Lattice

/-- An infimum over `Fin (n + 1)` is the infimum over the first `n` indices met with the value at
the last index. -/
private theorem iInf_fin_castSucc {α : Type*} [CompleteLattice α] {n : ℕ} (F : Fin (n + 1) → α) :
    ⨅ k, F k = (⨅ k : Fin n, F k.castSucc) ⊓ F (Fin.last n) := by
  refine le_antisymm (le_inf (le_iInf fun k => iInf_le _ _) (iInf_le _ _)) (le_iInf fun k => ?_)
  induction k using Fin.lastCases with
  | last => exact inf_le_right
  | cast k => exact inf_le_left.trans (iInf_le (fun k : Fin n => F k.castSucc) k)

/-- A supremum over `Fin (n + 1)` is the supremum over the first `n` indices joined with the value
at the last index. -/
private theorem iSup_fin_castSucc {α : Type*} [CompleteLattice α] {n : ℕ} (F : Fin (n + 1) → α) :
    ⨆ k, F k = (⨆ k : Fin n, F k.castSucc) ⊔ F (Fin.last n) := by
  refine le_antisymm (iSup_le fun k => ?_)
    (sup_le (iSup_le fun k => le_iSup F k.castSucc) (le_iSup F (Fin.last n)))
  induction k using Fin.lastCases with
  | last => exact le_sup_right
  | cast k => exact (le_iSup (fun k : Fin n => F k.castSucc) k).trans le_sup_left

/-- Membership in a finite infimum of open sets is membership in each of them. -/
private theorem mem_iInf_opens {α : Type*} [TopologicalSpace α] {κ : Type*} [Finite κ]
    (U : κ → TopologicalSpace.Opens α) (x : α) : x ∈ ⨅ i, U i ↔ ∀ i, x ∈ U i := by
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
  simp

/-- The preimage of a finite infimum of opens is the infimum of the preimages. -/
private theorem preimage_iInf_of_finite {X Y : Scheme.{u}} (f : X ⟶ Y) {κ : Type*} [Finite κ]
    (U : κ → Y.Opens) : f ⁻¹ᵁ (⨅ i, U i) = ⨅ i, f ⁻¹ᵁ U i :=
  SetLike.ext fun x => by simp only [Scheme.Hom.mem_preimage, mem_iInf_opens]

end Lattice

section Pullback

variable {P Q S : Scheme.{u}}

/-- The intersection of the preimages of an open `U` of `P` and an open `V` of `Q` in the fibre
product of `f : P ⟶ S` and `g : Q ⟶ S` is a fibre product of `U` and `V` over `S`, compatibly
with the first projections. -/
public theorem exists_iso_pullback_preimage_inf (f : P ⟶ S) (g : Q ⟶ S) (U : P.Opens)
    (V : Q.Opens) :
    ∃ e : (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : (pullback f g).Opens).toScheme ≅
        pullback (U.ι ≫ f) (V.ι ≫ g),
      e.hom ≫ pullback.fst (U.ι ≫ f) (V.ι ≫ g) ≫ U.ι =
        (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : (pullback f g).Opens).ι ≫
          pullback.fst f g := by
  obtain ⟨m, hm⟩ : ∃ m : pullback (U.ι ≫ f) (V.ι ≫ g) ⟶ pullback f g,
      m = pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp) := ⟨_, rfl⟩
  have : IsOpenImmersion m := hm ▸ inferInstance
  have hmfst : m ≫ pullback.fst f g = pullback.fst (U.ι ≫ f) (V.ι ≫ g) ≫ U.ι := by
    rw [hm]; exact pullback.lift_fst _ _ _
  have hrange : Set.range m =
      Set.range (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : (pullback f g).Opens).ι := by
    rw [hm, Scheme.Pullback.range_map, Scheme.Opens.range_ι]
    simp [Scheme.Opens.range_ι]
  refine ⟨(IsOpenImmersion.isoOfRangeEq m _ hrange).symm, ?_⟩
  rw [Iso.symm_hom, ← hmfst, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac]

/-- The fibre product over `S` of two closed subschemes of `S`, each presented by an isomorphism
onto the subscheme cut out by an ideal sheaf, is the subscheme cut out by the supremum of the two
ideal sheaves. -/
public theorem exists_iso_pullback_of_iso_subscheme {Z₁ Z₂ : Scheme.{u}} {a : Z₁ ⟶ S}
    {b : Z₂ ⟶ S} {I J : S.IdealSheafData} (eI : Z₁ ≅ I.subscheme)
    (hI : eI.hom ≫ I.subschemeι = a) (eJ : Z₂ ≅ J.subscheme)
    (hJ : eJ.hom ≫ J.subschemeι = b) :
    ∃ e : pullback a b ≅ (I ⊔ J).subscheme,
      e.hom ≫ (I ⊔ J).subschemeι = pullback.fst a b ≫ a := by
  have hpb : IsPullback (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) ≫ eI.inv)
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J) ≫ eJ.inv) a b :=
    (Scheme.IdealSheafData.isPullback_subscheme_sup S I J).of_iso (Iso.refl _) eI.symm eJ.symm
      (Iso.refl _) (by simp) (by simp) (by simp [← hI]) (by simp [← hJ])
  have key : (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) ≫ eI.inv) ≫ a
      = (I ⊔ J).subschemeι := by simp [← hI]
  refine ⟨hpb.isoPullback.symm, ?_⟩
  rw [Iso.symm_hom, ← key, ← Category.assoc, hpb.isoPullback_inv_fst]

/-- The fibre product over `S` of the closed subschemes cut out by `I` and `J` is the closed
subscheme cut out by `I ⊔ J`. -/
public theorem exists_iso_pullback_subschemeι_sup (I J : S.IdealSheafData) :
    ∃ e : pullback I.subschemeι J.subschemeι ≅ (I ⊔ J).subscheme,
      e.hom ≫ (I ⊔ J).subschemeι = pullback.fst _ _ ≫ I.subschemeι :=
  exists_iso_pullback_of_iso_subscheme (Iso.refl _) (by simp) (Iso.refl _) (by simp)

/-- A morphism to the fibre square of `ν` both of whose coordinates are `g` is `g` followed by the
diagonal. -/
public theorem lift_eq_comp_diagonal {Y A : Scheme.{u}} (ν : Y ⟶ S) (g : A ⟶ Y) :
    pullback.lift (f := ν) (g := ν) g g rfl = g ≫ pullback.diagonal ν := by
  apply pullback.hom_ext <;> simp

end Pullback

section FibrePower

variable {S Y : Scheme.{u}} (ν : Y ⟶ S) {ι : Type v} {A : ι → Scheme.{u}}
    (ε : ∀ i, A i ⟶ Y) [∀ i, IsOpenImmersion (ε i)]

/-- The open of the `n`-fold fibre power on which the `k`-th coordinate lies in `A (t k)`. -/
public def fibrePowerTupleOpens (ν : Y ⟶ S) (ε : ∀ i, A i ⟶ Y) [∀ i, IsOpenImmersion (ε i)]
    (n : ℕ) (t : Fin n → ι) : (fibrePower ν n).Opens :=
  ⨅ k, (fibrePowerLeg ν n k) ⁻¹ᵁ (ε (t k)).opensRange

/-- A point of the `n`-fold fibre power lies in the open indexed by `t` exactly when each of its
coordinates lies in the range of the corresponding member of the family. -/
public theorem mem_fibrePowerTupleOpens_iff (n : ℕ) (t : Fin n → ι) (z : fibrePower ν n) :
    z ∈ fibrePowerTupleOpens ν ε n t ↔
      ∀ k, (fibrePowerLeg ν n k).base z ∈ Set.range (ε (t k)).base := by
  change z ∈ (⨅ k, (fibrePowerLeg ν n k) ⁻¹ᵁ (ε (t k)).opensRange) ↔ _
  rw [mem_iInf_opens]
  rfl

/-- The open of the `(n + 1)`-fold fibre power indexed by `t` is the intersection of the preimage
of the open of the `n`-fold fibre power indexed by the first `n` entries of `t` and the preimage
of the range of the last member of the family. -/
public theorem fibrePowerTupleOpens_succ (n : ℕ) (t : Fin (n + 1) → ι) :
    fibrePowerTupleOpens ν ε (n + 1) t =
      pullback.fst (fibrePowerProj ν n) ν ⁻¹ᵁ
          fibrePowerTupleOpens ν ε n (fun k => t k.castSucc) ⊓
        pullback.snd (fibrePowerProj ν n) ν ⁻¹ᵁ (ε (t (Fin.last n))).opensRange := by
  change (⨅ k, (fibrePowerLeg ν (n + 1) k) ⁻¹ᵁ (ε (t k)).opensRange) = _
  rw [iInf_fin_castSucc, fibrePowerLeg_last]
  congr 1
  change (⨅ k : Fin n, (fibrePowerLeg ν (n + 1) k.castSucc) ⁻¹ᵁ (ε (t k.castSucc)).opensRange)
      = pullback.fst (fibrePowerProj ν n) ν ⁻¹ᵁ
          (⨅ k : Fin n, (fibrePowerLeg ν n k) ⁻¹ᵁ (ε (t k.castSucc)).opensRange)
  rw [preimage_iInf_of_finite]
  exact iInf_congr fun k => by rw [fibrePowerLeg_castSucc, Scheme.Hom.comp_preimage]

/-- Every point of the `n`-fold fibre power lies in the open indexed by some tuple, as soon as the
family covers `Y`. -/
public theorem exists_mem_fibrePowerTupleOpens
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (ε i).base) (n : ℕ) (z : fibrePower ν n) :
    ∃ t : Fin n → ι, z ∈ fibrePowerTupleOpens ν ε n t := by
  choose t ht using fun k : Fin n => hcover ((fibrePowerLeg ν n k).base z)
  exact ⟨t, (mem_fibrePowerTupleOpens_iff ν ε n t z).2 ht⟩

/-- The first coordinate of the morphism to the fibre square reading off two coordinates. -/
public theorem fibrePowerPair_fst (n : ℕ) (k l : Fin n) :
    fibrePowerPair ν n k l ≫ pullback.fst ν ν = fibrePowerLeg ν n k :=
  pullback.lift_fst _ _ _

/-- The second coordinate of the morphism to the fibre square reading off two coordinates. -/
public theorem fibrePowerPair_snd (n : ℕ) (k l : Fin n) :
    fibrePowerPair ν n k l ≫ pullback.snd ν ν = fibrePowerLeg ν n l :=
  pullback.lift_snd _ _ _

/-- When every member of the family maps to `S` by a closed immersion, a point of a tuple open
which lies off the fat diagonal has an injective tuple. -/
public theorem injective_of_mem_fibrePowerDistinctLocus
    [∀ i, IsClosedImmersion (ε i ≫ ν)] (n : ℕ) (t : Fin n → ι) (z : fibrePower ν n)
    (hz : z ∈ fibrePowerTupleOpens ν ε n t)
    (hd : z ∈ fibrePowerDistinctLocus ν n) : Function.Injective t := by
  intro k l hkl
  by_contra hne
  refine hd k l hne ?_
  have hrange : ∀ m : Fin n,
      Set.range ((fibrePowerTupleOpens ν ε n t).ι ≫ fibrePowerLeg ν n m) ⊆
        Set.range (ε (t m)) := by
    rintro m y ⟨w, rfl⟩
    exact (mem_fibrePowerTupleOpens_iff ν ε n t _).1 w.2 m
  have hlift : ∀ m : Fin n, t m = t k → ∃ a : (fibrePowerTupleOpens ν ε n t).toScheme ⟶ A (t k),
      a ≫ ε (t k) = (fibrePowerTupleOpens ν ε n t).ι ≫ fibrePowerLeg ν n m ∧
        a ≫ (ε (t k) ≫ ν) = (fibrePowerTupleOpens ν ε n t).ι ≫ fibrePowerProj ν n := by
    intro m hm
    obtain ⟨a, ha⟩ : ∃ a : (fibrePowerTupleOpens ν ε n t).toScheme ⟶ A (t k),
        a ≫ ε (t k) = (fibrePowerTupleOpens ν ε n t).ι ≫ fibrePowerLeg ν n m :=
      ⟨IsOpenImmersion.lift _ _ (hm ▸ hrange m), IsOpenImmersion.lift_fac _ _ _⟩
    exact ⟨a, ha, by rw [← Category.assoc, ha, Category.assoc, fibrePowerLeg_comp]⟩
  obtain ⟨ak, hak, h₁⟩ := hlift k rfl
  obtain ⟨al, hal, h₂⟩ := hlift l hkl.symm
  have heq : ak = al := (cancel_mono (ε (t k) ≫ ν)).1 (h₁.trans h₂.symm)
  have hpair : (fibrePowerTupleOpens ν ε n t).ι ≫ fibrePowerPair ν n k l =
      (ak ≫ ε (t k)) ≫ pullback.diagonal ν := by
    apply pullback.hom_ext
    · simp only [Category.assoc, fibrePowerPair_fst, pullback.diagonal_fst, Category.comp_id, hak]
    · simp only [Category.assoc, fibrePowerPair_snd, pullback.diagonal_snd, Category.comp_id,
        heq, hal]
  obtain ⟨w, hw⟩ : z ∈ Set.range (fibrePowerTupleOpens ν ε n t).ι := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨(ak ≫ ε (t k)) w, ?_⟩
  show (pullback.diagonal ν) ((ak ≫ ε (t k)) w) = (fibrePowerPair ν n k l) z
  rw [← Scheme.Hom.comp_apply, ← hpair, Scheme.Hom.comp_apply, hw]

/-- When the members of the family have pairwise disjoint ranges, the open indexed by an injective
tuple lies entirely off the fat diagonal. -/
public theorem fibrePowerTupleOpens_subset_distinctLocus
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (ε i).base) (Set.range (ε j).base))
    (n : ℕ) (t : Fin n → ι) (ht : Function.Injective t) :
    ↑(fibrePowerTupleOpens ν ε n t) ⊆ fibrePowerDistinctLocus ν n := by
  intro z hz k l hne hmem
  obtain ⟨w, hw⟩ := hmem
  have key : ∀ (p : pullback ν ν ⟶ Y) (m : Fin n), fibrePowerPair ν n k l ≫ p =
      fibrePowerLeg ν n m → pullback.diagonal ν ≫ p = 𝟙 Y → (fibrePowerLeg ν n m).base z = w := by
    intro p m h₁ h₂
    have e : (fibrePowerPair ν n k l ≫ p) z = (pullback.diagonal ν ≫ p) w := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw]
    rw [h₁, h₂] at e
    simpa using e
  have hk := key _ k (fibrePowerPair_fst ν n k l) (pullback.diagonal_fst ν)
  have hl := key _ l (fibrePowerPair_snd ν n k l) (pullback.diagonal_snd ν)
  exact (hdisj (t k) (t l) (ht.ne hne)).ne_of_mem
    (hk ▸ (mem_fibrePowerTupleOpens_iff ν ε n t z).1 hz k)
    (hl ▸ (mem_fibrePowerTupleOpens_iff ν ε n t z).1 hz l) rfl

/-- Each tuple open of the `n`-fold fibre power is, over `S`, the scheme theoretic intersection of
the `n` closed subschemes picked out by the tuple: it is isomorphic to the closed subscheme cut
out by `⨆ k, I (t k)` compatibly with the morphisms to `S`. For `n = 0` both sides are `S`. -/
public theorem exists_iso_fibrePowerTupleOpens (I : ι → S.IdealSheafData)
    (hI : ∀ i, ∃ e : A i ≅ (I i).subscheme, e.hom ≫ (I i).subschemeι = ε i ≫ ν)
    (n : ℕ) (t : Fin n → ι) :
    ∃ e : (fibrePowerTupleOpens ν ε n t).toScheme ≅ (⨆ k, I (t k)).subscheme,
      e.hom ≫ (⨆ k, I (t k)).subschemeι =
        (fibrePowerTupleOpens ν ε n t).ι ≫ fibrePowerProj ν n := by
  induction n with
  | zero =>
      have h0 : fibrePowerTupleOpens ν ε 0 t = ⊤ := iInf_of_empty _
      have hbot : (⨆ k, I (t k)) = (⊥ : S.IdealSheafData) := iSup_of_empty _
      have hp0 : fibrePowerProj ν 0 = 𝟙 S := rfl
      rw [h0, hbot, hp0]
      refine ⟨(Scheme.topIso (fibrePower ν 0)).trans
        (asIso (Scheme.IdealSheafData.subschemeι (⊥ : S.IdealSheafData))).symm, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨eU, hU⟩ := ih (fun k => t k.castSucc)
      obtain ⟨eA, hA⟩ := hI (t (Fin.last n))
      obtain ⟨eV, hV⟩ : ∃ e : (ε (t (Fin.last n))).opensRange.toScheme ≅
          (I (t (Fin.last n))).subscheme,
          e.hom ≫ (I (t (Fin.last n))).subschemeι =
            (ε (t (Fin.last n))).opensRange.ι ≫ ν := by
        refine ⟨(ε (t (Fin.last n))).isoOpensRange.symm.trans eA, ?_⟩
        rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hA, ← Category.assoc,
          Scheme.Hom.isoOpensRange_inv_comp]
      obtain ⟨e₁, h₁⟩ := exists_iso_pullback_preimage_inf (fibrePowerProj ν n) ν
        (fibrePowerTupleOpens ν ε n fun k => t k.castSucc)
        (ε (t (Fin.last n))).opensRange
      obtain ⟨e₂, h₂⟩ := exists_iso_pullback_of_iso_subscheme eU hU eV hV
      rw [fibrePowerTupleOpens_succ, iSup_fin_castSucc, fibrePowerProj_succ]
      refine ⟨e₁.trans e₂, ?_⟩
      rw [Iso.trans_hom, Category.assoc, h₂]
      exact (reassoc_of% h₁) _

end FibrePower

end AlgebraicGeometry

end
