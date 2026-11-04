module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffine

/-!
# Characterizations of ind-quasi-affine morphisms

An ind-quasi-affine morphism can be recognized by testing quasi-compact open subschemes above
affine opens, or more generally above quasi-compact and quasi-separated opens. It is enough to
make the latter test above the members of one such open cover of the target. An open
subscheme `U` above an open `V` maps to `V` by its open immersion followed by the restriction of
the original morphism, written `U.ι ≫ f ∣_ V`.

## Main results

* `AlgebraicGeometry.isIndQuasiAffineHom_tfae` gives four equivalent characterizations of an
  ind-quasi-affine morphism.
* `AlgebraicGeometry.isIndQuasiAffine_of_iso`: a scheme isomorphic to an ind-quasi-affine scheme
  is ind-quasi-affine.
* `AlgebraicGeometry.isIndQuasiAffineHom_of_isIndQuasiAffine_source`: a morphism with
  ind-quasi-affine source is ind-quasi-affine.
* `AlgebraicGeometry.isIndQuasiAffineHom_respectsIso`: ind-quasi-affineness of a morphism is
  invariant under isomorphisms of the source and of the target.
* `AlgebraicGeometry.isIndQuasiAffineHom_isZariskiLocalAtTarget`: ind-quasi-affineness of a
  morphism is Zariski local on the base.
* `AlgebraicGeometry.isIndQuasiAffineHom_iff_isIndQuasiAffine`: above an affine target,
  ind-quasi-affineness of a morphism is ind-quasi-affineness of its source.

## References

* [Stacks Project, Tag 0F1U](https://stacks.math.columbia.edu/tag/0F1U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme isomorphic to an ind-quasi-affine scheme is ind-quasi-affine. -/
lemma isIndQuasiAffine_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [IsIndQuasiAffine X] :
    IsIndQuasiAffine Y := by
  refine ⟨fun U hU => ?_⟩
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have hc : CompactSpace (e.hom ⁻¹ᵁ U).toScheme :=
    (TopCat.homeoOfIso (asIso (e.hom.preimageIso U).inv.base)).compactSpace
  have : (e.hom ⁻¹ᵁ U).toScheme.IsQuasiAffine :=
    IsIndQuasiAffine.isQuasiAffine _ (isCompact_iff_compactSpace.mpr hc)
  exact Scheme.IsQuasiAffine.of_isAffineHom ((e.hom.preimageIso U).symm).hom

/-- A morphism of schemes whose source is ind-quasi-affine is ind-quasi-affine. -/
lemma isIndQuasiAffineHom_of_isIndQuasiAffine_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIndQuasiAffine X] : IsIndQuasiAffineHom f := by
  refine ⟨fun U _ => ⟨fun W hW => ?_⟩⟩
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  have hO : IsCompact (((f ⁻¹ᵁ U).ι ''ᵁ W : X.Opens) : Set X) :=
    hW.image (f ⁻¹ᵁ U).ι.continuous
  have : ((f ⁻¹ᵁ U).ι ''ᵁ W).toScheme.IsQuasiAffine := IsIndQuasiAffine.isQuasiAffine _ hO
  exact Scheme.IsQuasiAffine.of_isAffineHom ((f ⁻¹ᵁ U).ι.isoImage W).hom

/-- A morphism of schemes with affine target is ind-quasi-affine exactly when its source is an
ind-quasi-affine scheme. -/
lemma isIndQuasiAffineHom_iff_isIndQuasiAffine {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    IsIndQuasiAffineHom f ↔ IsIndQuasiAffine X := by
  refine ⟨fun hf => ?_, fun _ => isIndQuasiAffineHom_of_isIndQuasiAffine_source f⟩
  have h := hf.isIndQuasiAffine_preimage ⊤ (isAffineOpen_top Y)
  rw [Scheme.Hom.preimage_top] at h
  exact isIndQuasiAffine_of_iso X.topIso

/-- Ind-quasi-affineness of a morphism of schemes is invariant under isomorphisms of the source
and of the target. -/
instance isIndQuasiAffineHom_respectsIso :
    MorphismProperty.RespectsIso (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    refine ⟨fun V hV => ?_⟩
    have : IsIndQuasiAffine (f ⁻¹ᵁ V).toScheme := hf.isIndQuasiAffine_preimage V hV
    rw [Scheme.Hom.comp_preimage]
    exact isIndQuasiAffine_of_iso (e.hom.preimageIso (f ⁻¹ᵁ V)).symm
  · intro X Y Z e f hf
    refine ⟨fun V hV => ?_⟩
    rw [Scheme.Hom.comp_preimage]
    exact hf.isIndQuasiAffine_preimage _ (hV.preimage_of_isIso e.hom)

/-- Above a quasi-separated open `V` of the target, any quasi-compact open of the ind-quasi-affine
preimage of `V` maps quasi-affinely to `V`. -/
private lemma isQuasiAffineHom_comp_restrict_of_isIndQuasiAffine {X Y : Scheme.{u}} {f : X ⟶ Y}
    {V : Y.Opens} [IsIndQuasiAffine (f ⁻¹ᵁ V).toScheme] (hV : IsQuasiSeparated (V : Set Y))
    (U : (f ⁻¹ᵁ V).toScheme.Opens) (hU : IsCompact (U : Set (f ⁻¹ᵁ V).toScheme)) :
    IsQuasiAffineHom (U.ι ≫ f ∣_ V) := by
  have : U.toScheme.IsQuasiAffine := IsIndQuasiAffine.isQuasiAffine U hU
  have : QuasiSeparatedSpace V.toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ V.isOpen).mp hV
  exact isQuasiAffineHom_of_isQuasiAffine_of_quasiSeparatedSpace (U.ι ≫ f ∣_ V)

/-- Ind-quasi-affineness of a morphism of schemes can be tested on the quasi-compact open
subschemes above the affine opens of the target, above the members of one cover of the target by
quasi-compact quasi-separated opens, or above all quasi-compact quasi-separated opens of the
target. -/
@[stacks 0F1U "equivalent characterizations"]
theorem isIndQuasiAffineHom_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE [
      IsIndQuasiAffineHom f,
      ∀ (V : Y.Opens), IsAffineOpen V →
        ∀ (U : (f ⁻¹ᵁ V).toScheme.Opens), IsCompact (U : Set (f ⁻¹ᵁ V).toScheme) →
          IsQuasiAffineHom (U.ι ≫ f ∣_ V),
      ∃ (ι : Type u) (V : ι → Y.Opens),
        (iSup V = ⊤) ∧
          (∀ j, IsCompact (V j : Set Y)) ∧
          (∀ j, IsQuasiSeparated (V j : Set Y)) ∧
          (∀ j (U : (f ⁻¹ᵁ V j).toScheme.Opens),
              IsCompact (U : Set (f ⁻¹ᵁ V j).toScheme) →
                IsQuasiAffineHom (U.ι ≫ f ∣_ (V j))),
      ∀ (V : Y.Opens), IsCompact (V : Set Y) → IsQuasiSeparated (V : Set Y) →
        ∀ (U : (f ⁻¹ᵁ V).toScheme.Opens), IsCompact (U : Set (f ⁻¹ᵁ V).toScheme) →
          IsQuasiAffineHom (U.ι ≫ f ∣_ V)] := by
  classical
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hf V hV U hU
      have := hf.isIndQuasiAffine_preimage V hV
      exact isQuasiAffineHom_comp_restrict_of_isIndQuasiAffine hV.isQuasiSeparated U hU
    · intro h
      refine ⟨fun V hV => ⟨fun U hU => ?_⟩⟩
      have : IsQuasiAffineHom (U.ι ≫ f ∣_ V) := h V hV U hU
      have : IsAffine V.toScheme := hV
      exact Scheme.IsQuasiAffine.of_isQuasiAffineHom (U.ι ≫ f ∣_ V)
  tfae_have 2 → 3 := fun h =>
    ⟨Y.affineOpens, fun W => (W : Y.Opens), iSup_affineOpens_eq_top Y,
      fun W => W.2.isCompact, fun W => W.2.isQuasiSeparated, fun W => h _ W.2⟩
  tfae_have 4 → 2 := fun h V hV U hU => h V hV.isCompact hV.isQuasiSeparated U hU
  tfae_have 3 → 4 := by
    rintro ⟨ι, Vj, hcover, -, -, hall⟩ V hVc hVqs U hU
    have hxcover (x : V.toScheme) : (V.ι x) ∈ (⨆ i, Vj i : Y.Opens) := by rw [hcover]; trivial
    let j : V.toScheme → ι := fun x => Classical.choose (Opens.mem_iSup.mp (hxcover x))
    have hj (x : V.toScheme) : (V.ι x) ∈ Vj (j x) :=
      Classical.choose_spec (Opens.mem_iSup.mp (hxcover x))
    have hExists (x : V.toScheme) : ∃ W : V.toScheme.Opens, IsAffineOpen W ∧ x ∈ W ∧
        W ≤ V.ι ⁻¹ᵁ Vj (j x) := by
      obtain ⟨_, ⟨W, hWaff, rfl⟩, hxW, hWsub⟩ :=
        V.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (hj x) (V.ι ⁻¹ᵁ Vj (j x)).isOpen
      exact ⟨W, hWaff, hxW, hWsub⟩
    choose W hWaff hWmem hWsub using hExists
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    have : QuasiSeparatedSpace V.toScheme :=
      (isQuasiSeparated_iff_quasiSeparatedSpace _ V.isOpen).mp hVqs
    have hqc : QuasiCompact (U.ι ≫ f ∣_ V) := quasiCompact_of_compactSpace _
    refine (isQuasiAffineHom_iff_of_iSup_eq_top (U.ι ≫ f ∣_ V) W hWaff
      (top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hWmem x⟩)).2 fun x => ?_
    have hW₁aff : IsAffineOpen (V.ι ''ᵁ W x) := (hWaff x).image_of_isOpenImmersion V.ι
    have hW₁j : V.ι ''ᵁ W x ≤ Vj (j x) := by rintro y ⟨z, hz, rfl⟩; exact hWsub x hz
    have hU₀ : IsCompact (((U.ι ≫ f ∣_ V) ⁻¹ᵁ W x : U.toScheme.Opens) : Set U.toScheme) :=
      (quasiCompact_iff_forall_isAffineOpen.mp hqc) (W x) (hWaff x)
    have : CompactSpace ((U.ι ≫ f ∣_ V) ⁻¹ᵁ W x : U.toScheme.Opens).toScheme :=
      isCompact_iff_compactSpace.mp hU₀
    have hOP : (f ⁻¹ᵁ V).ι ''ᵁ (U.ι ''ᵁ ((U.ι ≫ f ∣_ V) ⁻¹ᵁ W x)) ≤ f ⁻¹ᵁ (V.ι ''ᵁ W x) := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨(f ∣_ V) (U.ι t), ht, congrArg (fun k : (f ⁻¹ᵁ V).toScheme ⟶ Y => k (U.ι t))
        (morphismRestrict_ι f V)⟩
    have hOQ : (f ⁻¹ᵁ V).ι ''ᵁ (U.ι ''ᵁ ((U.ι ≫ f ∣_ V) ⁻¹ᵁ W x)) ≤ f ⁻¹ᵁ Vj (j x) :=
      fun y hy => hW₁j (hOP hy)
    set U' : (f ⁻¹ᵁ Vj (j x)).toScheme.Opens :=
      (f ⁻¹ᵁ Vj (j x)).ι ⁻¹ᵁ ((f ⁻¹ᵁ V).ι ''ᵁ (U.ι ''ᵁ ((U.ι ≫ f ∣_ V) ⁻¹ᵁ W x))) with hU'def
    set eU : ((U.ι ≫ f ∣_ V) ⁻¹ᵁ W x : U.toScheme.Opens).toScheme ≅ U'.toScheme :=
      U.ι.isoImage _ ≪≫ (f ⁻¹ᵁ V).ι.isoImage _ ≪≫ (Scheme.Opens.isoOfLE hOQ).symm with heU
    have hU'c : CompactSpace U'.toScheme := (TopCat.homeoOfIso (asIso eU.hom.base)).compactSpace
    have : IsQuasiAffineHom (U'.ι ≫ f ∣_ (Vj (j x))) :=
      hall (j x) U' (isCompact_iff_compactSpace.mpr hU'c)
    have hW₂aff : IsAffineOpen ((Vj (j x)).ι ⁻¹ᵁ (V.ι ''ᵁ W x)) :=
      hW₁aff.preimage_of_isOpenImmersion (Vj (j x)).ι
        (by simpa [Scheme.Opens.opensRange_ι] using hW₁j)
    have hpre : (U'.ι ≫ f ∣_ (Vj (j x))) ⁻¹ᵁ ((Vj (j x)).ι ⁻¹ᵁ (V.ι ''ᵁ W x)) = ⊤ := by
      refine top_le_iff.mp fun y _ => ?_
      show ((U'.ι ≫ f ∣_ (Vj (j x))) ≫ (Vj (j x)).ι) y ∈ V.ι ''ᵁ W x
      rw [Category.assoc, morphismRestrict_ι f (Vj (j x)), ← Category.assoc]
      exact hOP y.property
    have hQAtop : (⊤ : U'.toScheme.Opens).toScheme.IsQuasiAffine := by
      rw [← hpre]
      exact IsQuasiAffineHom.isQuasiAffine_preimage _ hW₂aff
    have : U'.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom
        U'.toScheme.topIso.symm.hom
    exact Scheme.IsQuasiAffine.of_isAffineHom eU.hom
  tfae_finish

/-- The restriction of an ind-quasi-affine morphism above an open of the target is
ind-quasi-affine. -/
private lemma isIndQuasiAffineHom_restrict {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsIndQuasiAffineHom f) (V : Y.Opens) : IsIndQuasiAffineHom (f ∣_ V) := by
  refine ⟨fun W hW => ?_⟩
  have : IsIndQuasiAffine (f ⁻¹ᵁ (V.ι ''ᵁ W)).toScheme :=
    hf.isIndQuasiAffine_preimage _ (hW.image_of_isOpenImmersion V.ι)
  exact isIndQuasiAffine_of_iso (((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ W) ≪≫
    X.isoOfEq (image_morphismRestrict_preimage f V W)).symm)

/-- If `f ∣_ V` is ind-quasi-affine then so is the inverse image of any open contained in `V`. -/
private lemma isIndQuasiAffine_preimage_of_le {X Y : Scheme.{u}} {f : X ⟶ Y} {V W : Y.Opens}
    (hf : IsIndQuasiAffineHom (f ∣_ V)) (hWV : W ≤ V) (hW : IsAffineOpen W) :
    IsIndQuasiAffine (f ⁻¹ᵁ W).toScheme := by
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hWV]
  have : IsIndQuasiAffine ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)).toScheme :=
    hf.isIndQuasiAffine_preimage _ (hW.preimage_of_isOpenImmersion V.ι
      (by simpa [Scheme.Opens.opensRange_ι] using hWV))
  refine isIndQuasiAffine_of_iso ((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)) ≪≫
    X.isoOfEq ?_)
  rw [image_morphismRestrict_preimage f V (V.ι ⁻¹ᵁ W), himg]

/-- Ind-quasi-affineness of a morphism may be checked above the members of an open cover of the
target. -/
private lemma isIndQuasiAffineHom_of_iSup_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u}
    (V : ι → Y.Opens) (hV : iSup V = ⊤) (hf : ∀ i, IsIndQuasiAffineHom (f ∣_ V i)) :
    IsIndQuasiAffineHom f := by
  classical
  have h3 : ∃ (κ : Type u) (W : κ → Y.Opens),
      (iSup W = ⊤) ∧
        (∀ j, IsCompact (W j : Set Y)) ∧
        (∀ j, IsQuasiSeparated (W j : Set Y)) ∧
        (∀ j (U : (f ⁻¹ᵁ W j).toScheme.Opens),
            IsCompact (U : Set (f ⁻¹ᵁ W j).toScheme) →
              IsQuasiAffineHom (U.ι ≫ f ∣_ (W j))) := by
    refine ⟨{p : ι × Y.Opens // IsAffineOpen p.2 ∧ p.2 ≤ V p.1}, fun p => p.1.2, ?_,
      fun p => p.2.1.isCompact, fun p => p.2.1.isQuasiSeparated, ?_⟩
    · refine top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ?_
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show y ∈ (⨆ i, V i : Y.Opens) by rw [hV]; trivial)
      obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW₀, hW₀V⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hi (V i).isOpen
      exact ⟨⟨(i, W₀), hW₀, hW₀V⟩, hyW₀⟩
    · intro p U hU
      have : IsIndQuasiAffine (f ⁻¹ᵁ p.1.2).toScheme :=
        isIndQuasiAffine_preimage_of_le (hf p.1.1) p.2.2 p.2.1
      exact isQuasiAffineHom_comp_restrict_of_isIndQuasiAffine p.2.1.isQuasiSeparated U hU
  exact ((isIndQuasiAffineHom_tfae f).out 3 1).mp h3

/-- Being an ind-quasi-affine morphism is Zariski local on the base. -/
@[stacks 0F1U "Zariski locality on the base"]
instance isIndQuasiAffineHom_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u}) :=
  IsZariskiLocalAtTarget.mk' (P := @IsIndQuasiAffineHom)
    (fun _ V hf => isIndQuasiAffineHom_restrict hf V) isIndQuasiAffineHom_of_iSup_eq_top

end AlgebraicGeometry
