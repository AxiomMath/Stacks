module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionBaseChange
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Data.Finite.Perm

/-!
# A finite extension over which the `n`-torsion of a Picard group is defined

Let `X` be a quasi-compact, quasi-separated scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, and
let `K/k` be a Galois extension such that the `n`-torsion `Pic(X_K)[n]` is finite. Suppose `X`
has a point with values in a finite subextension `L/k`. Then there is a finite subextension
`E ⊇ L` with `[E : k] ≤ [L : k] · |Pic(X_K)[n]|!` such that pullback is a bijection
`Pic(X_E)[n] → Pic(X_K)[n]`. This is the Galois-theoretic half of the proof of
[Stacks, Tag 0CDU].

## Main results

* `Stacks.Picard.exists_intermediateField_finrank_le_forall_smul_eq`: for a continuous action of
  `Gal(K/k)` on a finite set `T` and a finite subextension `L`, there is a finite subextension
  `E ⊇ L` of degree at most `[L : k] · |T|!` whose Galois group `Gal(K/E)` acts trivially on `T`.
* `Stacks.Picard.exists_schemePullbackClass_stageProjection_eq`: a class of `Pic(X_K)` fixed by
  `Gal(K/E)` comes from `Pic(X_E)`, when `X_E` has an `E`-rational point (Tag 0CDT applied to
  `X_E` over `E`).
* `Stacks.Picard.exists_intermediateField_bijOn_zsmulTorsion`: the finite subextension `E` of
  the statement above.

## Implementation notes

The source proves the bound by letting `Gal(k^{sep}/k)` act on `Pic(X_{k^{sep}})[n]`, taking the
fixed field of the kernel, and bounding the image of the Galois group by the permutation group
of a set with `n^{2g}` elements. Here the Galois extension `K` is arbitrary. The kernel of the
action is open because every stabiliser is
(`Stacks.Picard.isOpen_stabilizer_galoisPicardAction`, the continuity clause of Tag 0CDT) and
the set is finite; it is intersected with the open subgroup `Gal(K/L)` so that `E` contains `L`,
which is what carries the rational point to `X_E`; the index of the intersection is at most
the product of the indices.

The comparison of the Galois action of `Gal(K/E)` on `(X_E)_K` with the restriction of the
action of `Gal(K/k)` on `X_K` goes through the isomorphism
`Stacks.Picard.stageBaseChangeIso : X_K ≅ (X_E)_K` given by
`Stacks.Picard.isPullback_stageProjection`.

## References

* [Stacks Project, Tag 0CDU](https://stacks.math.columbia.edu/tag/0CDU)
* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

/-! ### Pullback along an isomorphism and torsion subgroups -/

/-- Pullback along an isomorphism of schemes is a bijection of Picard groups, with inverse the
pullback along the inverse isomorphism. -/
theorem bijective_schemePullbackClass_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (schemePullbackClass f) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨schemePullbackClass (inv f), fun x => ?_, fun y => ?_⟩
  · rw [schemePullbackClass_comp, IsIso.inv_hom_id, schemePullbackClass_id]
  · rw [schemePullbackClass_comp, IsIso.hom_inv_id, schemePullbackClass_id]

/-- A homomorphism of abelian groups which restricts to a bijection of the `n`-torsion sets is an
isomorphism of the `n`-torsion subgroups `A[n] ≅ B[n]`. -/
def torsionByAddEquivOfBijOn {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B)
    (n : ℤ) (h : Set.BijOn φ (zsmulTorsion A n) (zsmulTorsion B n)) :
    Submodule.torsionBy ℤ A n ≃+ Submodule.torsionBy ℤ B n :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun x : Submodule.torsionBy ℤ A n =>
        (⟨φ (x : A), (Submodule.mem_torsionBy_iff _ _).2
          (h.mapsTo ((Submodule.mem_torsionBy_iff _ _).1 x.2))⟩ : Submodule.torsionBy ℤ B n))
      fun x y => Subtype.ext (map_add φ (x : A) (y : A)))
    ⟨fun x y hxy => Subtype.ext (h.injOn ((Submodule.mem_torsionBy_iff _ _).1 x.2)
        ((Submodule.mem_torsionBy_iff _ _).1 y.2) (congrArg Subtype.val hxy)),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := h.surjOn ((Submodule.mem_torsionBy_iff _ _).1 y.2)
        exact ⟨⟨x, (Submodule.mem_torsionBy_iff _ _).2 hx⟩, Subtype.ext hxy⟩⟩

/-! ### A finite subextension trivialising a continuous action on a finite set -/

/-- **The degree bound of Tag 0CDU.** Let `K/k` be a Galois extension, let `Gal(K/k)` act on a
finite set `T` with open stabilisers, and let `L/k` be a finite subextension. Then there is a
finite subextension `E ⊇ L` of `K/k` with `[E : k] ≤ [L : k] · |T|!` such that `Gal(K/E)` acts
trivially on `T`.

`E` is the fixed field of `Gal(K/L) ∩ N`, where `N` is the kernel of `Gal(K/k) → Perm(T)`. Both
are open subgroups, so their intersection is closed and is the Galois group of its fixed field;
its index is at most `[L : k]` times the order of the image of `Gal(K/k)` in `Perm(T)`. -/
theorem exists_intermediateField_finrank_le_forall_smul_eq {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsGalois k K] {T : Type*} [MulAction (K ≃ₐ[k] K) T] [Finite T]
    (hT : ∀ t : T, IsOpen (MulAction.stabilizer (K ≃ₐ[k] K) t : Set (K ≃ₐ[k] K)))
    (L : IntermediateField k K) [FiniteDimensional k L] :
    ∃ E : IntermediateField k K, L ≤ E ∧ FiniteDimensional k E ∧
      Module.finrank k E ≤ Module.finrank k L * (Nat.card T).factorial ∧
      ∀ σ ∈ E.fixingSubgroup, ∀ t : T, σ • t = t := by
  classical
  let φ := MulAction.toPermHom (K ≃ₐ[k] K) T
  have hker : (φ.ker : Set (K ≃ₐ[k] K)) =
      ⋂ t : T, (MulAction.stabilizer (K ≃ₐ[k] K) t : Set (K ≃ₐ[k] K)) := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter,
      MulAction.mem_stabilizer_iff, Equiv.Perm.ext_iff, Equiv.Perm.coe_one, id_eq]
    rfl
  have hkeropen : IsOpen (φ.ker : Set (K ≃ₐ[k] K)) := by
    rw [hker]
    exact isOpen_iInter_of_finite hT
  let S : Subgroup (K ≃ₐ[k] K) := L.fixingSubgroup ⊓ φ.ker
  have hSopen : IsOpen (S : Set (K ≃ₐ[k] K)) :=
    (IntermediateField.fixingSubgroup_isOpen L).inter hkeropen
  have hE : (IntermediateField.fixedField S).fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨S, Subgroup.isClosed_of_isOpen S hSopen⟩
  refine ⟨IntermediateField.fixedField S, (IntermediateField.le_iff_le _ _).2 inf_le_left,
    ?_, ?_, ?_⟩
  · rw [← InfiniteGalois.isOpen_iff_finite]
    change IsOpen ((IntermediateField.fixedField S).fixingSubgroup : Set (K ≃ₐ[k] K))
    rwa [hE]
  · rw [IntermediateField.finrank_eq_fixingSubgroup_index, hE,
      IntermediateField.finrank_eq_fixingSubgroup_index]
    refine Subgroup.index_inf_le.trans (Nat.mul_le_mul_left _ ?_)
    rw [Subgroup.index_ker, ← Nat.card_perm]
    exact Finite.card_subtype_le _
  · intro σ hσ t
    rw [hE] at hσ
    exact DFunLike.congr_fun (MonoidHom.mem_ker.1 hσ.2) t

/-! ### Comparison of `X_K` with the base change of a stage `X_E` -/

section Tower

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))

/-- The stage `X_E = X ×_k E`, as a scheme over `Spec E`. -/
abbrev stageOver (E : IntermediateField k K) : Over (Spec (.of E)) :=
  Over.mk (pullback.snd X.hom (spectrumMap k E))

/-- **`X_K ≅ (X_E)_K`.** The base change of `X` to `K` is the base change of the stage `X_E`
along `Spec K ⟶ Spec E` (`Stacks.Picard.isPullback_stageProjection`). -/
def stageBaseChangeIso (E : IntermediateField k K) :
    SchemeOver.baseChange k K X ≅ SchemeOver.baseChange E K (stageOver X E) :=
  (isPullback_stageProjection X E).isoPullback

/-- The isomorphism `X_K ≅ (X_E)_K` followed by the projection `(X_E)_K ⟶ X_E` is the projection
`stageProjection X E : X_K ⟶ X_E`. -/
@[reassoc (attr := simp)]
theorem stageBaseChangeIso_hom_fst (E : IntermediateField k K) :
    (stageBaseChangeIso X E).hom ≫
        pullback.fst (stageOver X E).hom (Spec.map (CommRingCat.ofHom (algebraMap E K))) =
      stageProjection X E :=
  (isPullback_stageProjection X E).isoPullback_hom_fst

/-- The isomorphism `X_K ≅ (X_E)_K` followed by the structure morphism `(X_E)_K ⟶ Spec K` is the
structure morphism `X_K ⟶ Spec K`. -/
@[reassoc (attr := simp)]
theorem stageBaseChangeIso_hom_snd (E : IntermediateField k K) :
    (stageBaseChangeIso X E).hom ≫
        pullback.snd (stageOver X E).hom (Spec.map (CommRingCat.ofHom (algebraMap E K))) =
      pullback.snd X.hom (spectrumMap k K) :=
  (isPullback_stageProjection X E).isoPullback_hom_snd

/-- An `E`-automorphism of `K`, viewed as a `k`-automorphism, fixes `E`. -/
theorem restrictScalars_mem_fixingSubgroup (E : IntermediateField k K) (σ : K ≃ₐ[E] K) :
    σ.restrictScalars k ∈ E.fixingSubgroup :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩

variable [IsGalois k K]

omit [IsGalois k K] in
/-- **The twist by `σ ∈ Gal(K/E)` on `(X_E)_K` is the twist by `σ` on `X_K`.** Under
`X_K ≅ (X_E)_K`, the automorphism `id × Spec(σ)` of `(X_E)_K` attached to an `E`-automorphism
`σ` of `K` corresponds to the automorphism of `X_K` attached to `σ` viewed as a
`k`-automorphism. -/
theorem galoisTwist_restrictScalars_comp_stageBaseChangeIso_hom (E : IntermediateField k K)
    (σ : K ≃ₐ[E] K) :
    galoisTwist k K X (σ.restrictScalars k) ≫ (stageBaseChangeIso X E).hom =
      (stageBaseChangeIso X E).hom ≫ galoisTwist E K (stageOver X E) σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, galoisTwist_comp_fst E K (stageOver X E) σ,
      stageBaseChangeIso_hom_fst]
    exact galoisTwist_comp_eq_of_mem_fixingSubgroup X E _
      (restrictScalars_mem_fixingSubgroup E σ)
      _ (stageProjection_comp_fst X E) (stageProjection_comp_snd X E)
  · rw [Category.assoc, Category.assoc, galoisTwist_comp_snd E K (stageOver X E) σ,
      stageBaseChangeIso_hom_snd, stageBaseChangeIso_hom_snd_assoc,
      galoisTwist_comp_snd k K X (σ.restrictScalars k)]
    rfl

/-- **Classes fixed by `Gal(K/E)` come from the stage `X_E`.** Let `X` be a quasi-compact,
quasi-separated scheme over `k` with `H⁰(X, 𝒪_X) = k`, let `K/k` be Galois, and let `E` be an
intermediate field such that `X_E` has an `E`-rational point. Then every class of `Pic(X_K)`
fixed by every element of `Gal(K/E)` is pulled back from `Pic(X_E)`.

This is the surjectivity clause of Tag 0CDT for `X_E` over `E` and the Galois extension `K/E`,
transported along `X_K ≅ (X_E)_K`. -/
theorem exists_schemePullbackClass_stageProjection_eq [CompactSpace X.left]
    [QuasiSeparatedSpace X.left]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)) (E : IntermediateField k K)
    (pt : Spec (.of E) ⟶ pullback X.hom (spectrumMap k E))
    (hpt : pt ≫ pullback.snd X.hom (spectrumMap k E) = 𝟙 _)
    (y : ofScheme (SchemeOver.baseChange k K X))
    (hy : ∀ σ ∈ E.fixingSubgroup, schemePullbackClass (galoisTwist k K X σ) y = y) :
    ∃ x, schemePullbackClass (stageProjection X E) x = y := by
  have : IsGalois E K := IsGalois.tower_top_of_isGalois k E K
  have : CompactSpace (stageOver X E).left := compactSpace_stage X E
  have : QuasiSeparatedSpace (stageOver X E).left := quasiSeparatedSpace_stage X E
  have hz : schemePullbackClass (stageBaseChangeIso X E).inv y ∈
      galoisFixedClasses E K (stageOver X E) := by
    rw [mem_galoisFixedClasses]
    intro σ
    have hc : galoisTwist E K (stageOver X E) σ ≫ (stageBaseChangeIso X E).inv =
        (stageBaseChangeIso X E).inv ≫ galoisTwist k K X (σ.restrictScalars k) := by
      rw [← cancel_mono (stageBaseChangeIso X E).hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, galoisTwist_restrictScalars_comp_stageBaseChangeIso_hom,
        Iso.inv_hom_id_assoc]
    rw [schemePullbackClass_comp, hc, ← schemePullbackClass_comp,
      hy _ (restrictScalars_mem_fixingSubgroup E σ)]
  obtain ⟨x, -, hx⟩ := surjOn_schemePullbackClass_galoisFixedClasses E K (stageOver X E)
    (isIso_appTop_stage X hΓ E) pt hpt hz
  refine ⟨x, ?_⟩
  rw [← stageBaseChangeIso_hom_fst, ← schemePullbackClass_comp, hx, schemePullbackClass_comp,
    Iso.hom_inv_id, schemePullbackClass_id]

/-- **The bounded extension trivialising the Galois action on `n`-torsion.** Let `X` be a
quasi-compact, quasi-separated scheme over `k` with `H⁰(X, 𝒪_X) = k`, let `K/k` be a Galois
extension with `Pic(X_K)[n]` finite, and let `L ⊆ K` be a finite subextension together with a
`k`-morphism `Spec L ⟶ X`. Then there is a finite subextension `E ⊇ L` with
`[E : k] ≤ [L : k] · |Pic(X_K)[n]|!` such that pullback along `X_K ⟶ X_E` is a bijection
`Pic(X_E)[n] → Pic(X_K)[n]`.

`E` is given by `Stacks.Picard.exists_intermediateField_finrank_le_forall_smul_eq` applied to the
action of `Gal(K/k)` on `Pic(X_K)[n]`, whose stabilisers are open by the continuity clause of
Tag 0CDT. Injectivity is Tag 0CC5 at the stage; surjectivity is
`Stacks.Picard.exists_schemePullbackClass_stageProjection_eq`, the point of `X_E` coming from
`Spec E ⟶ Spec L ⟶ X`. -/
theorem exists_intermediateField_bijOn_zsmulTorsion [CompactSpace X.left]
    [QuasiSeparatedSpace X.left]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)) (n : ℤ)
    (hfin : (zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) n).Finite)
    (L : IntermediateField k K) [FiniteDimensional k L]
    (s : Spec (.of L) ⟶ X.left) (hs : s ≫ X.hom = spectrumMap k L) :
    ∃ E : IntermediateField k K, L ≤ E ∧ FiniteDimensional k E ∧
      Module.finrank k E ≤ Module.finrank k L *
        (Nat.card (zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) n)).factorial ∧
      Set.BijOn (schemePullbackClass (stageProjection X E))
        (zsmulTorsion (ofScheme (pullback X.hom (spectrumMap k E))) n)
        (zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) n) := by
  let := galoisPicardAction k K X
  let p : SubMulAction (K ≃ₐ[k] K) (ofScheme (SchemeOver.baseChange k K X)) :=
    { carrier := zsmulTorsion _ n
      smul_mem' := fun σ _ hx => mapsTo_schemePullbackClass_zsmulTorsion _ n hx }
  have : Finite p := hfin.to_subtype
  have hopen : ∀ t : p, IsOpen (MulAction.stabilizer (K ≃ₐ[k] K) t : Set (K ≃ₐ[k] K)) := by
    intro t
    rw [SubMulAction.stabilizer_of_subMul]
    exact isOpen_stabilizer_galoisPicardAction X _
  obtain ⟨E, hLE, hEfin, hEdeg, hEfix⟩ :=
    exists_intermediateField_finrank_le_forall_smul_eq hopen L
  let pt : Spec (.of E) ⟶ pullback X.hom (spectrumMap k E) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hLE).toRingHom) ≫ s)
      (𝟙 _) (by rw [Category.assoc, hs, specMap_inclusion_comp_spectrumMap, Category.id_comp])
  have hinj := injective_schemePullbackClass_stageProjection X hΓ E
  refine ⟨E, hLE, hEfin, hEdeg, mapsTo_schemePullbackClass_zsmulTorsion _ n, hinj.injOn,
    fun y hy => ?_⟩
  obtain ⟨x, hx⟩ :=
    exists_schemePullbackClass_stageProjection_eq X hΓ E pt (pullback.lift_snd _ _ _) y
      fun σ hσ => congrArg Subtype.val (hEfix σ hσ ⟨y, hy⟩)
  refine ⟨x, ?_, hx⟩
  rw [mem_zsmulTorsion]
  apply hinj
  have h₁ : schemePullbackClass (stageProjection X E) (n • x) =
      n • schemePullbackClass (stageProjection X E) x :=
    map_zsmul (schemePullbackClassHom (stageProjection X E)) n x
  have h₀ : schemePullbackClass (stageProjection X E) 0 = 0 :=
    map_zero (schemePullbackClassHom (stageProjection X E))
  rwa [h₁, h₀, hx]

end Tower

end Stacks.Picard

end
