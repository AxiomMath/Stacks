module

public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Comp
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Reduction

/-!
# Noetherian approximation by induction on an affine cover

A quasi-compact quasi-separated scheme `S` is approximated relative to a quasi-compact open
`U ⊆ S` by adding one affine open to `U` at a time: the complement of `U` is covered by
finitely many affine opens, and along the resulting chain
`U ⊆ U ∪ A₀ ⊆ U ∪ A₀ ∪ A₁ ⊆ ⋯ ⊆ S` every link enlarges the open by a single affine.  This
file performs that induction, so that approximation relative to a quasi-compact open follows
from the single-affine case.

The single-affine case is isolated as the predicate
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`, and
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIsOneAffineOpenStep` derives the general
statement from it.

## Main definitions

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsCofinal`: an approximation whose
  reindexing map has cofinal image.
* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofEqTop`: the approximation of a scheme
  relative to the whole scheme, given by the original inverse system itself.
* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`: the single-affine
  case of Noetherian approximation, where the ambient scheme is the union of the given
  quasi-compact open with one affine open.

## Main results

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.exists_of_isOneAffineOpenStep` and
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIsOneAffineOpenStep`: approximation of
  `S` relative to any quasi-compact open follows from the single-affine case.

## Implementation notes

Composing two consecutive links of the chain uses
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.comp`, which requires the reindexing map of
the outer approximation to have cofinal image in the index preorder of the inner one.  The
single-affine case is therefore required to produce an approximation that is `IsCofinal`, and
the induction reproduces that property; cofinality is preserved by composition because the
composite reindexing map is the composite of the two.

Each link of the chain is an open subscheme `U ∪ A` of `S`, which is again quasi-compact and
quasi-separated, and the given open and the added affine are transported into it along the
inclusion.  The transport isomorphism is `AlgebraicGeometry.Scheme.Opens.isoPreimage` below:
it identifies `U` with `T.ι ⁻¹ᵁ U` when `U ≤ T`, by
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` at the two inclusions, which have the same
image, and `AlgebraicGeometry.Scheme.Opens.compactSpace_preimage_ι` and
`AlgebraicGeometry.Scheme.Opens.isAffineOpen_preimage_ι` carry quasi-compactness and affineness
across it.

## Transparency gotchas

* Quasi-compactness of an open as a scheme and compactness of its carrier as a set are one
  unfolding apart and the instance for one is not found from the other; the bridge is
  Mathlib's `isCompact_iff_compactSpace`, applied to the instance by name.

* `AlgebraicGeometry.Scheme.Opens.topIso_hom_eq_ι` must not be given to `simp`: Mathlib's
  `AlgebraicGeometry.Scheme.topIso_hom` is the same equation the other way round and the pair
  loops.  It is used by `rw` only.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Transporting an open into a larger open -/

namespace Scheme.Opens

variable {S : Scheme.{u}} (T : S.Opens)

/-- The inclusion of an open pulls that open back to everything. -/
lemma preimage_ι_self : T.ι ⁻¹ᵁ T = ⊤ := top_unique fun x _ ↦ x.2

/-- The inclusion of the top open is the canonical isomorphism with the scheme. -/
lemma topIso_hom_eq_ι (X : Scheme.{u}) : (⊤ : X.Opens).ι = X.topIso.hom := by
  simp [Scheme.topIso]

variable {U : S.Opens} (hU : U ≤ T)

include hU in
/-- The image of an open of a larger open, read in the ambient scheme. -/
lemma image_preimage_ι : T.ι ''ᵁ (T.ι ⁻¹ᵁ U) = U :=
  TopologicalSpace.Opens.ext (Set.image_preimage_eq_of_subset fun x hx ↦ ⟨⟨x, hU hx⟩, rfl⟩)

include hU in
/-- The two inclusions of an open of a larger open have the same image. -/
lemma range_ι_comp_ι :
    Set.range (U.ι).base =
      Set.range ((T.ι ⁻¹ᵁ U : (T : Scheme.{u}).Opens).ι ≫ T.ι).base :=
  congrArg (fun W : S.Opens ↦ (W : Set S))
    ((opensRange_ι U).trans (((Scheme.Hom.opensRange_comp _ _).trans
      (congrArg (fun W : (T : Scheme.{u}).Opens ↦ T.ι ''ᵁ W) (opensRange_ι _))).trans
        (image_preimage_ι T hU)).symm)

/-- **An open of a larger open is isomorphic to the open it cuts out of that larger one.** -/
noncomputable def isoPreimage :
    (U : Scheme.{u}) ≅ ((T.ι ⁻¹ᵁ U : (T : Scheme.{u}).Opens) : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq U.ι ((T.ι ⁻¹ᵁ U : (T : Scheme.{u}).Opens).ι ≫ T.ι)
    (range_ι_comp_ι T hU)

@[reassoc]
lemma isoPreimage_hom_ι :
    (isoPreimage T hU).hom ≫ (T.ι ⁻¹ᵁ U : (T : Scheme.{u}).Opens).ι = S.homOfLE hU := by
  rw [← cancel_mono T.ι, Category.assoc, Scheme.homOfLE_ι]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (range_ι_comp_ι T hU)

include hU in
/-- Quasi-compactness transported to the open cut out of a larger open. -/
lemma compactSpace_preimage_ι (hUc : IsCompact ((U : S.Opens) : Set S)) :
    CompactSpace ((T.ι ⁻¹ᵁ U : (T : Scheme.{u}).Opens) : Scheme.{u}) := by
  refine isCompact_iff_compactSpace.mp ?_
  rw [T.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  exact congrArg (fun W : S.Opens ↦ IsCompact (W : Set S)) (image_preimage_ι T hU) ▸ hUc

include hU in
/-- Affineness transported to the open cut out of a larger open. -/
lemma isAffineOpen_preimage_ι (hUa : IsAffineOpen U) :
    IsAffineOpen (T.ι ⁻¹ᵁ U : (T : Scheme.{u}).Opens) := by
  rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion T.ι, image_preimage_ι T hU]
  exact hUa

end Scheme.Opens

/-- Quasi-compactness of the union of two quasi-compact opens. -/
lemma compactSpace_sup {S : Scheme.{u}} (U V : S.Opens)
    (hU : IsCompact ((U : S.Opens) : Set S)) (hV : IsCompact ((V : S.Opens) : Set S)) :
    CompactSpace ((U ⊔ V : S.Opens) : Scheme.{u}) :=
  isCompact_iff_compactSpace.mp (by simpa using hU.union hV)

/-- Splitting a finite supremum off its first term. -/
lemma iSup_fin_succ_split {α : Type u} [CompleteLattice α] {m : ℕ} (f : Fin (m + 1) → α) :
    (⨆ a, f a) = f 0 ⊔ ⨆ a : Fin m, f a.succ := by
  refine le_antisymm (iSup_le fun a ↦ ?_)
    (sup_le (le_iSup f 0) (iSup_le fun a ↦ le_iSup f a.succ))
  induction a using Fin.cases with
  | zero => exact le_sup_left
  | succ i => exact le_sup_of_le_right (le_iSup (fun a : Fin m ↦ f a.succ) i)

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteTypeApproximation

attribute [local instance] indexPreorder indexNonempty indexDirected

section Cofinal

variable {I : Type u} [Preorder I] {D : Iᵒᵈ ⥤ Scheme.{u}} {S : Scheme.{u}} {U : S.Opens}
  {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}

/-- An approximation is cofinal when every index of the original inverse system is dominated by
the image of some index of the approximating system.  Restricting an inverse limit along such a
reindexing does not change the limit, which is what makes two approximations composable. -/
def IsCofinal (Q : FiniteTypeApproximation D S U p) : Prop :=
  ∀ i : I, ∃ j : Q.indexType, i ≤ Q.index j

end Cofinal

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵈ ⥤ Scheme.{u})
  [∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
  [∀ i, QuasiCompact (terminal.from (D.obj i))]

/-- A scheme which is the limit of a finite-type inverse system on the whole of itself is
approximated relative to that open by the system itself, reindexed by the identity. -/
noncomputable def ofEqTop (S : Scheme.{u}) {U : S.Opens} (hU : U = ⊤)
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    FiniteTypeApproximation D S U p :=
  let e : (U : Scheme.{u}) ≅ S := S.isoOfEq hU ≪≫ S.topIso
  have he : e.hom = U.ι := by
    simp [e, Scheme.isoOfEq_hom_ι]
  { indexType := I
    index := OrderHom.id
    ambient := D
    openPart := D
    inclusion := 𝟙 D
    comparison := NatIso.ofComponents (fun j ↦ Iso.refl _) (by
      intro j j' f
      have h : (OrderHom.id (α := I)).monotone.dual.functor.map f = f := Subsingleton.elim _ _
      change D.map f ≫ 𝟙 (D.obj j') =
        𝟙 (D.obj j) ≫ D.map ((OrderHom.id (α := I)).monotone.dual.functor.map f)
      rw [h, Category.comp_id, Category.id_comp]
      rfl)
    ambientCone := ((Cone.mk (U : Scheme.{u}) p).extend e.inv).π
    openCone := p
    transition_affine := fun f ↦ inferInstance
    locallyOfFiniteType := fun j ↦ inferInstance
    quasiCompact := fun j ↦ inferInstance
    inclusion_isOpenImmersion := fun j ↦ by
      change IsOpenImmersion (𝟙 (D.obj j)); infer_instance
    transition_isPullback := fun f ↦ by
      refine IsPullback.of_vert_isIso ⟨?_⟩
      change D.map f ≫ 𝟙 _ = 𝟙 _ ≫ D.map f
      simp
    ambientCone_isLimit := by
      refine IsLimit.ofIsoLimit hp (Cone.ext e ?_)
      intro j
      simp
    openCone_isLimit := hp
    inclusion_compatibility := fun j ↦ by
      have : U.ι ≫ e.inv = 𝟙 _ := by rw [← he]; simp
      simp [reassoc_of% this]
    comparison_compatibility := fun j ↦ by
      change p.app j ≫ 𝟙 (D.obj j) = p.app j
      rw [Category.comp_id] }

/-- The approximation of a scheme by the inverse system on the whole of itself is cofinal: its
reindexing map is the identity. -/
theorem isCofinal_ofEqTop (S : Scheme.{u}) {U : S.Opens} (hU : U = ⊤)
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    IsCofinal (ofEqTop D S hU p hp) :=
  fun i ↦ ⟨i, le_rfl⟩

/-- The single-affine case of Noetherian approximation: a finite-type inverse system with
affine transition morphisms on a quasi-compact open `U` of a quasi-compact quasi-separated
scheme `S` extends to such a system on `S`, cofinally, whenever `S` is the union of `U` with
one affine open. -/
def IsOneAffineOpenStep : Prop :=
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵈ ⥤ Scheme.{u}),
    (∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)) →
    (∀ i, LocallyOfFiniteType (terminal.from (D.obj i))) →
    (∀ i, QuasiCompact (terminal.from (D.obj i))) →
    ∀ (S : Scheme.{u}), CompactSpace S → QuasiSeparatedSpace S →
    ∀ (U A : S.Opens), CompactSpace (U : Scheme.{u}) → IsAffineOpen A → U ⊔ A = ⊤ →
    ∀ (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D),
      IsLimit (Cone.mk (U : Scheme.{u}) p) →
      ∃ Q : FiniteTypeApproximation D S U p, IsCofinal Q

private theorem exists_aux (hstep : IsOneAffineOpenStep.{u}) (S : Scheme.{u})
    (hS : CompactSpace S) (hQS : QuasiSeparatedSpace S) (n : ℕ) :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Iᵒᵈ ⥤ Scheme.{u}),
      (∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)) →
      (∀ i, LocallyOfFiniteType (terminal.from (D.obj i))) →
      (∀ i, QuasiCompact (terminal.from (D.obj i))) →
      ∀ (U : S.Opens), CompactSpace (U : Scheme.{u}) →
      ∀ (A : Fin n → S.Opens), (∀ l, IsAffineOpen (A l)) → U ⊔ ⨆ l, A l = ⊤ →
      ∀ (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D),
        IsLimit (Cone.mk (U : Scheme.{u}) p) →
        ∃ Q : FiniteTypeApproximation D S U p, IsCofinal Q := by
  have := hS
  have := hQS
  induction n with
  | zero =>
    intro I _ _ _ D hAff hFT hQC U hU A hA hcov p hp
    have hU' : U = ⊤ := by simpa using hcov
    exact ⟨ofEqTop D S hU' p hp, isCofinal_ofEqTop D S hU' p hp⟩
  | succ n ih =>
    intro I _ _ _ D hAff hFT hQC U hU A hA hcov p hp
    have := hU
    have hUc : IsCompact ((U : S.Opens) : Set S) := isCompact_iff_compactSpace.mpr hU
    set V : S.Opens := U ⊔ A 0 with hVdef
    have hUV : U ≤ V := le_sup_left
    have hAV : A 0 ≤ V := le_sup_right
    have hVc : CompactSpace (V : Scheme.{u}) := by
      rw [hVdef]
      exact compactSpace_sup U (A 0) hUc (hA 0).isCompact
    have hVqs : QuasiSeparatedSpace (V : Scheme.{u}) :=
      QuasiSeparatedSpace.of_isOpenEmbedding V.ι.isOpenEmbedding
    have hU1c : CompactSpace ((V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) : Scheme.{u}) :=
      Scheme.Opens.compactSpace_preimage_ι V hUV hUc
    have hA1 : IsAffineOpen (V.ι ⁻¹ᵁ A 0 : (V : Scheme.{u}).Opens) :=
      Scheme.Opens.isAffineOpen_preimage_ι V hAV (hA 0)
    have hcovV : (V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) ⊔ V.ι ⁻¹ᵁ A 0 = ⊤ := by
      have h : (V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) ⊔ V.ι ⁻¹ᵁ A 0 = V.ι ⁻¹ᵁ V := rfl
      rw [h]
      exact Scheme.Opens.preimage_ι_self V
    set σ := Scheme.Opens.isoPreimage V hUV with hσ
    set p₁ := ((Cone.mk (U : Scheme.{u}) p).extend σ.inv).π with hp₁def
    have hp₁ : IsLimit (Cone.mk
        ((V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) : Scheme.{u}) p₁) := by
      refine IsLimit.ofIsoLimit hp (Cone.ext σ ?_)
      intro j
      simp [hp₁def]
    obtain ⟨Q₁, hQ₁⟩ := hstep D hAff hFT hQC (V : Scheme.{u}) hVc hVqs _ _ hU1c hA1 hcovV p₁ hp₁
    have hcov' : V ⊔ ⨆ l : Fin n, A l.succ = ⊤ := by
      rw [← hcov, iSup_fin_succ_split, hVdef, sup_assoc]
    obtain ⟨Q₂, hQ₂⟩ := ih Q₁.ambient (fun f ↦ Q₁.transition_affine f) Q₁.locallyOfFiniteType
      Q₁.quasiCompact V hVc (fun l ↦ A l.succ) (fun l ↦ hA l.succ) hcov'
      Q₁.ambientCone Q₁.ambientCone_isLimit
    refine ⟨Q₁.comp Q₂ (𝟙 _) (fun j ↦ Category.id_comp _) hUV σ ?_ hQ₂ ?_, ?_⟩
    · rw [hσ, Category.comp_id]
      exact Scheme.Opens.isoPreimage_hom_ι V hUV
    · intro i
      simp [hp₁def]
    · intro i
      obtain ⟨j₁, hj₁⟩ := hQ₁ i
      obtain ⟨j, hj⟩ := hQ₂ j₁
      exact ⟨j, hj₁.trans (Q₁.index.monotone hj)⟩

/-- **Noetherian approximation relative to a quasi-compact open, from the single-affine case.**
Given the single-affine case `IsOneAffineOpenStep`, a finite-type inverse system with affine
transition morphisms on a quasi-compact open of a quasi-compact quasi-separated scheme extends
to such a system on the whole scheme. -/
theorem exists_of_isOneAffineOpenStep (hstep : IsOneAffineOpenStep.{u})
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    Nonempty (FiniteTypeApproximation D S U p) := by
  obtain ⟨n, A, hA⟩ := Scheme.exists_finite_affineOpens_sup_eq_top S U
  obtain ⟨Q, -⟩ := exists_aux hstep S ‹_› ‹_› n D (fun f ↦ inferInstance)
    (fun i ↦ inferInstance) (fun i ↦ inferInstance) U ‹_›
    (fun l ↦ ((A l : S.affineOpens) : S.Opens)) (fun l ↦ (A l).2) hA p hp
  exact ⟨Q⟩

/-- The approximation produced by `exists_of_isOneAffineOpenStep`, as data. -/
noncomputable def ofIsOneAffineOpenStep (hstep : IsOneAffineOpenStep.{u})
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    FiniteTypeApproximation D S U p :=
  (exists_of_isOneAffineOpenStep D hstep S U p hp).some

end AlgebraicGeometry.Scheme.FiniteTypeApproximation

end
