module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Étale coordinates centred at a rational point

Let `X` be separated over a field `k` with `X_K` smooth of relative dimension `d` over an
extension field `K`, and let `x` be a `k`-rational point of `X`. Then `X` is smooth over `k`
(smoothness descends along `Spec K ⟶ Spec k`), and there are an affine open `V ∋ x` and an étale
`π : V ⟶ 𝔸^d_k` over `k` whose coordinates vanish simultaneously only at `x`
(`Stacks.EtaleCohomology.exists_etale_affineSpace_rationalPoint`): the étale coordinates of the
closed point `x ⟶ X` (`AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback`)
cut `x` out as the preimage of the origin, and the number of coordinates is `d`, by base change
to `K` (`Stacks.EtaleCohomology.Purity.eq_of_etale_affineSpace`).

## Main results

* `Stacks.EtaleCohomology.eq_of_forall_notMem_basicOpen_coord`: the origin is the only point of
  `𝔸^n_k` where all coordinates vanish.
* `Stacks.EtaleCohomology.smooth_of_smooth_fieldBaseChange`
* `Stacks.EtaleCohomology.exists_etale_affineSpace_centred_rationalPoint`,
  `Stacks.EtaleCohomology.exists_etale_affineSpace_rationalPoint`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section AffineSpace

variable {k : Type u} [Field k] {ι : Type u}

/-- A point of `𝔸^ι_k` where all coordinates vanish corresponds to the ideal of the origin. -/
theorem asIdeal_eq_of_forall_notMem_basicOpen_coord
    (y : PrimeSpectrum (MvPolynomial ι k))
    (hy : ∀ j, (AffineSpace.SpecIso ι (.of k)).inv.base y ∉
      𝔸(ι; Spec (.of k)).basicOpen (AffineSpace.coord (Spec (.of k)) j)) :
    y.asIdeal = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ι k →+* k) := by
  have hX : ∀ j, (MvPolynomial.X j : MvPolynomial ι k) ∈ y.asIdeal := by
    intro j
    have h1 : (AffineSpace.SpecIso ι (.of k)).inv ⁻¹ᵁ
        𝔸(ι; Spec (.of k)).basicOpen (AffineSpace.coord (Spec (.of k)) j) =
          PrimeSpectrum.basicOpen (MvPolynomial.X j : MvPolynomial ι k) := by
      rw [Scheme.preimage_basicOpen_top, AffineSpace.SpecIso_inv_appTop_coord,
        basicOpen_eq_of_affine]
    have h2 : y ∉ PrimeSpectrum.basicOpen (MvPolynomial.X j : MvPolynomial ι k) := h1 ▸ hy j
    simpa [PrimeSpectrum.mem_basicOpen] using h2
  have hle : RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ι k →+* k) ≤ y.asIdeal := by
    intro f hf
    have hspan : f ∈ Ideal.span (MvPolynomial.X '' Set.univ : Set (MvPolynomial ι k)) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [MvPolynomial.mem_support_iff] at hm
        rw [RingHom.mem_ker, MvPolynomial.constantCoeff_eq] at hf
        exact hm hf
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
      exact ⟨i, Set.mem_univ _, hi⟩
    refine (Ideal.span_le.2 ?_) hspan
    rintro _ ⟨i, -, rfl⟩
    exact hX i
  have hmax : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ι k →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨MvPolynomial.C a, by simp⟩
  exact (hmax.eq_of_le y.isPrime.ne_top hle).symm

/-- **The origin is the only point of `𝔸^ι_k` where all coordinates vanish.** -/
theorem eq_of_forall_notMem_basicOpen_coord {z z' : 𝔸(ι; Spec (.of k))}
    (hz : ∀ j, z ∉ 𝔸(ι; Spec (.of k)).basicOpen (AffineSpace.coord (Spec (.of k)) j))
    (hz' : ∀ j, z' ∉ 𝔸(ι; Spec (.of k)).basicOpen (AffineSpace.coord (Spec (.of k)) j)) :
    z = z' := by
  obtain ⟨y, rfl⟩ := (Scheme.homeoOfIso (AffineSpace.SpecIso ι (.of k)).symm).surjective z
  obtain ⟨y', rfl⟩ := (Scheme.homeoOfIso (AffineSpace.SpecIso ι (.of k)).symm).surjective z'
  exact congrArg _ (PrimeSpectrum.ext ((asIdeal_eq_of_forall_notMem_basicOpen_coord y hz).trans
    (asIdeal_eq_of_forall_notMem_basicOpen_coord y' hz').symm))

end AffineSpace

section Descent

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K]

/-- The morphism `Spec K ⟶ Spec k` induced by a field extension `k → K` is surjective. -/
instance surjective_specAlgebraMap : Surjective (specAlgebraMap k K) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

/-- The morphism `Spec K ⟶ Spec k` induced by a field extension `k → K` is flat. -/
instance flat_specAlgebraMap : Flat (specAlgebraMap k K) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- **Smoothness descends from `X_K` to `X`.** -/
theorem smooth_of_smooth_fieldBaseChange [Smooth (pullback.snd f (specAlgebraMap k K))] :
    Smooth f :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback f (specAlgebraMap k K)).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end Descent

section Chart

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f]
  (K : Type u) [Field K] [Algebra k K] (d : ℕ)
  [SmoothOfRelativeDimension d (pullback.snd f (specAlgebraMap k K))]

/-- Reindexing affine space along a right inverse gives a right inverse. -/
theorem reindex_comp_reindex_of_rightInverse {m n : Type u} (a : m → n) (b : n → m)
    (h : ∀ x, a (b x) = x) (S : Scheme.{u}) :
    AffineSpace.reindex a S ≫ AffineSpace.reindex b S = 𝟙 _ := by
  refine AffineSpace.hom_ext ?_ fun j => ?_
  · simp
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      AffineSpace.reindex_appTop_coord, h, Scheme.Hom.id_appTop]
    rfl

/-- A point lying over the image of the second leg of a cartesian square lies in the image of
the first. -/
theorem mem_range_fst_of_isPullback {A B C D : Scheme.{u}} {fst : A ⟶ B} {snd : A ⟶ C}
    {g₁ : B ⟶ D} {g₂ : C ⟶ D} (h : IsPullback fst snd g₁ g₂) (b : B)
    (hb : g₁.base b ∈ Set.range g₂.base) : b ∈ Set.range fst.base := by
  obtain ⟨a, rfl⟩ : b ∈ Set.range (pullback.fst g₁ g₂).base := by
    rwa [Scheme.Pullback.range_fst]
  refine ⟨h.isoPullback.inv.base a, ?_⟩
  rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]

/-- Reindexing affine space along a bijection is an isomorphism. -/
private theorem isIso_reindex_of_rightInverse {m n : Type u} (a : m → n) (b : n → m)
    (h₁ : ∀ x, a (b x) = x) (h₂ : ∀ x, b (a x) = x) (S : Scheme.{u}) :
    IsIso (AffineSpace.reindex a S) :=
  ⟨⟨AffineSpace.reindex b S, reindex_comp_reindex_of_rightInverse a b h₁ S,
    reindex_comp_reindex_of_rightInverse b a h₂ S⟩⟩

/-- Reindexing affine space pulls the basic open of a coordinate back to that of the
reindexed coordinate. -/
private theorem preimage_reindex_basicOpen_coord {m n : Type u} (a : m → n) (S : Scheme.{u})
    (j : m) :
    AffineSpace.reindex a S ⁻¹ᵁ 𝔸(m; S).basicOpen (AffineSpace.coord S j) =
      𝔸(n; S).basicOpen (AffineSpace.coord S (a j)) := by
  rw [Scheme.preimage_basicOpen_top, AffineSpace.reindex_appTop_coord]

/-- Along a surjective reindexing, all coordinates of `g ≫ reindex a` vanish at a point exactly
when all coordinates of `g` do. -/
private theorem forall_notMem_basicOpen_appTop_reindex_iff {m n : Type u} {a : m → n}
    (ha : Function.Surjective a) {S Y : Scheme.{u}} (g : Y ⟶ 𝔸(n; S)) (y : Y) :
    (∀ j, y ∉ Y.basicOpen ((g ≫ AffineSpace.reindex a S).appTop (AffineSpace.coord S j))) ↔
      ∀ j, g.base y ∉ 𝔸(n; S).basicOpen (AffineSpace.coord S j) := by
  simp only [← Scheme.preimage_basicOpen_top, Scheme.Hom.comp_preimage,
    preimage_reindex_basicOpen_coord]
  refine ⟨fun h j => ?_, fun h j => h (a j)⟩
  obtain ⟨j, rfl⟩ := ha j
  exact h j

/-- The coordinate embedding `𝔸^0_S ⟶ 𝔸^{0+n}_S` lands off the basic open of every
coordinate. -/
private theorem coordinateSubspaceEmbedding_zero_notMem_basicOpen_coord (S : Scheme.{u}) (n : ℕ)
    (p : 𝔸(ULift.{u} (Fin 0); S)) (j : ULift.{u} (Fin (0 + n))) :
    (_root_.Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S 0 n).base p ∉
      𝔸(ULift.{u} (Fin (0 + n)); S).basicOpen (AffineSpace.coord S j) := by
  intro hj
  have hj' : j = ULift.up (Fin.natAdd 0 (Fin.cast (Nat.zero_add n) j.down)) := by
    ext
    simp
  have h0 := _root_.Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_lastCoordinate
    S 0 n (Fin.cast (Nat.zero_add n) j.down)
  rw [hj'] at hj
  have hj₂ : p ∈ (_root_.Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S 0 n) ⁻¹ᵁ
      𝔸(ULift.{u} (Fin (0 + n)); S).basicOpen (AffineSpace.coord S
        (ULift.up (Fin.natAdd 0 (Fin.cast (Nat.zero_add n) j.down)))) := hj
  rw [Scheme.preimage_basicOpen_top, h0, Scheme.basicOpen_zero] at hj₂
  exact hj₂

/-- Over an open `W ≤ U`, a point lies over the image of the last leg of a cartesian square on
`s.resLE` exactly when it lies in the image of `s`. -/
private theorem mem_range_iff_of_isPullback_resLE {Y A B : Scheme.{u}} (s : Y ⟶ X) {U W : X.Opens}
    (hWU : W ≤ U) {q : (s ⁻¹ᵁ U).toScheme ⟶ A} {π : U.toScheme ⟶ B} {e : A ⟶ B}
    (hpb : IsPullback (s.resLE U (s ⁻¹ᵁ U) le_rfl) q π e) (v : W.toScheme) :
    π.base ((X.homOfLE hWU).base v) ∈ Set.range e.base ↔ W.ι.base v ∈ Set.range s.base := by
  have h₁ : s.resLE U (s ⁻¹ᵁ U) le_rfl ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ s := Scheme.Hom.resLE_comp_ι _ _
  have h₂ : X.homOfLE hWU ≫ U.ι = W.ι := Scheme.homOfLE_ι _ _
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := mem_range_fst_of_isPullback hpb _ h
    refine ⟨(s ⁻¹ᵁ U).ι.base w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← h₁, Scheme.Hom.comp_apply, hw, ← h₂]
    rfl
  rintro ⟨t, ht⟩
  have ht' : t ∈ s ⁻¹ᵁ U := by
    show s.base t ∈ U
    rw [ht, ← h₂, Scheme.Hom.comp_apply]
    exact ((X.homOfLE hWU).base v).2
  let w : (s ⁻¹ᵁ U).toScheme := ⟨t, ht'⟩
  have hu : (s.resLE U (s ⁻¹ᵁ U) le_rfl).base w = (X.homOfLE hWU).base v := by
    apply U.ι.isOpenEmbedding.injective
    show (s.resLE U (s ⁻¹ᵁ U) le_rfl ≫ U.ι).base w = (X.homOfLE hWU ≫ U.ι).base v
    rw [h₁, h₂, Scheme.Hom.comp_apply]
    exact ht
  refine ⟨q.base w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hpb.w, Scheme.Hom.comp_apply, hu]

omit [IsSeparated f] in
include K in
/-- The relative dimension of `X_K` is the number of coordinates of any étale chart of `X`
over `k` with nonempty source. -/
private theorem eq_of_etale_affineSpace_of_fieldBaseChange {U : X.Opens} {x : X} (hx : x ∈ U)
    {n : ℕ} (π : U.toScheme ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k))) [Etale π]
    (hover : π ≫ (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) = U.ι ≫ f) : d = n := by
  let s' := specAlgebraMap k K
  let pr := pullback.fst f s'
  let UY := pr ⁻¹ᵁ U
  have hbig : IsPullback (pr ∣_ U) (UY.ι ≫ pullback.snd f s') (U.ι ≫ f) s' :=
    (isPullback_morphismRestrict pr U).paste_vert (IsPullback.of_hasPullback f s')
  have hA := AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) s'
  let πY : UY.toScheme ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of K)) :=
    hA.lift (pr ∣_ U ≫ π) (UY.ι ≫ pullback.snd f s') (by rw [Category.assoc, hover]; exact hbig.w)
  have hsq : IsPullback (pr ∣_ U) πY π (AffineSpace.map _ s') :=
    IsPullback.of_bot (by rw [hA.lift_snd, hover]; exact hbig) (hA.lift_fst _ _ _).symm hA
  have : Etale πY := MorphismProperty.of_isPullback (P := @Etale) hsq inferInstance
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback x
    (default : Spec (.of K)) (f := f) (g := s') (Subsingleton.elim _ _)
  have hyU : y ∈ UY := by
    show pr.base y ∈ U
    rwa [hy]
  exact Purity.eq_of_etale_affineSpace K (pullback.snd f s') d UY ⟨y, hyU⟩ n πY

include K in
/-- **Étale coordinates centred at a rational point.** For `x = s(pt)` a `k`-rational point of
`X`, there are an affine open `V ∋ x` and an étale `π : V ⟶ 𝔸^d_k` over `k` whose coordinates
vanish simultaneously exactly at `x`: `x` is the preimage of the origin. -/
theorem exists_etale_affineSpace_centred_rationalPoint (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))),
      Etale π ∧ π ≫ (𝔸(ULift.{u} (Fin d); Spec (.of k)) ↘ Spec (.of k)) = V.ι ≫ f ∧
      (∃ v : V, V.ι.base v ∈ Set.range s.base) ∧
      ∀ v : V, (∀ j : Fin d, v ∉ V.toScheme.basicOpen
          (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up j)))) ↔
        V.ι.base v ∈ Set.range s.base := by
  have : Smooth (pullback.snd f (specAlgebraMap k K)) := SmoothOfRelativeDimension.smooth d _
  have : Smooth f := smooth_of_smooth_fieldBaseChange f K
  have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  have : Smooth (s ≫ f) := hs ▸ inferInstance
  let pt : Spec (.of k) := default
  obtain ⟨m, n, U, hxU, π, q, hπ, hover, hpb⟩ :=
    _root_.Stacks.AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback f s pt
  have := hπ
  have hover : π ≫ (𝔸(ULift.{u} (Fin (m + n)); Spec (.of k)) ↘ Spec (.of k)) = U.ι ≫ f := hover
  have : Etale q := MorphismProperty.of_isPullback (P := @Etale) hpb hπ
  obtain rfl : m = 0 :=
    (Purity.eq_of_etale_affineSpace k (𝟙 (Spec (.of k))) 0 (s ⁻¹ᵁ U) ⟨pt, hxU⟩ m q).symm
  have hd : d = 0 + n :=
    eq_of_etale_affineSpace_of_fieldBaseChange f K d (show s.base pt ∈ U from hxU) π hover
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show s.base pt ∈ U from hxU) U.2
  have hWU : W ≤ U := hWU₀
  let pt0 : 𝔸(ULift.{u} (Fin 0); Spec (.of k)) := q.base ⟨pt, hxU⟩
  let i : ULift.{u} (Fin d) → ULift.{u} (Fin (0 + n)) := fun j => ULift.up (Fin.cast hd j.down)
  let i' : ULift.{u} (Fin (0 + n)) → ULift.{u} (Fin d) :=
    fun j => ULift.up (Fin.cast hd.symm j.down)
  have : IsIso (AffineSpace.reindex i (Spec (.of k))) :=
    isIso_reindex_of_rightInverse i i' (fun x => by simp [i, i']) (fun x => by simp [i, i']) _
  let πW : Scheme.Opens.toScheme (X := X) W ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k)) :=
    (X.homOfLE hWU ≫ π) ≫ AffineSpace.reindex i (Spec (.of k))
  have hπW : Etale πW := by
    dsimp only [πW]
    infer_instance
  refine ⟨W, hW, πW, hπW, ?_, ⟨⟨_, hxW⟩, ⟨pt, rfl⟩⟩, ?_⟩
  · simp only [πW, Category.assoc, AffineSpace.reindex_over, hover]
    rw [← Category.assoc, Scheme.homOfLE_ι]
  intro v
  have hv := forall_notMem_basicOpen_appTop_reindex_iff
    (fun j => ⟨i' j, by simp [i, i']⟩ : Function.Surjective i) (X.homOfLE hWU ≫ π) v
  rw [← mem_range_iff_of_isPullback_resLE s hWU hpb v]
  refine ⟨fun h => ⟨pt0, eq_of_forall_notMem_basicOpen_coord
    (coordinateSubspaceEmbedding_zero_notMem_basicOpen_coord _ n pt0) (hv.1 fun j => h j.down)⟩,
    ?_⟩
  rintro ⟨p, hp⟩ j
  refine hv.2 (fun j' => ?_) (ULift.up j)
  show π.base ((X.homOfLE hWU).base v) ∉ _
  rw [← hp]
  exact coordinateSubspaceEmbedding_zero_notMem_basicOpen_coord _ n p j'

include K in
/-- **Étale coordinates centred at a rational point**, the zero set bounded above: the only point
of `V` where all coordinates of `π` vanish is `x`
(`Stacks.EtaleCohomology.exists_etale_affineSpace_centred_rationalPoint` says it is a zero). -/
theorem exists_etale_affineSpace_rationalPoint (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))),
      Etale π ∧ π ≫ (𝔸(ULift.{u} (Fin d); Spec (.of k)) ↘ Spec (.of k)) = V.ι ≫ f ∧
      (∃ v : V, V.ι.base v ∈ Set.range s.base) ∧
      ∀ v : V, (∀ j : Fin d, v ∉ V.toScheme.basicOpen
          (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up j)))) →
        V.ι.base v ∈ Set.range s.base := by
  obtain ⟨V, hV, π, hπ, hover, hx, h⟩ := exists_etale_affineSpace_centred_rationalPoint f K d s hs
  exact ⟨V, hV, π, hπ, hover, hx, fun v => (h v).1⟩

end Chart

end Stacks.EtaleCohomology

end
