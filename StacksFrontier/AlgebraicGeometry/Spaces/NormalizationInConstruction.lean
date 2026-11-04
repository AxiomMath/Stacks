module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FunctorialComposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Size
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationQuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite

/-!
# Constructing the normalization of an algebraic space in another over a representable base

For a morphism `f : X ⟶ Y` of algebraic spaces, `AlgebraicGeometry.Space.NormalizationInData` is
the normalization of `Y` in `X` as data: a factorization `X ⟶ Y' ⟶ Y` of `f` whose base change
along every étale scheme chart of `Y` is the relative normalization of that chart. This file
constructs such data whenever `Y` is representable, and shows that it is unique up to a unique
compatible isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationInData.ofRepresentable` is the normalization of the
  algebraic space represented by an object `Y₀` of the big fppf site in the one represented by
  an object `X₀`, for a quasi-compact quasi-separated morphism `f₀ : X₀ ⟶ Y₀` of the site.
* `AlgebraicGeometry.Space.NormalizationInData.ofIsoSource` transports normalization data along
  an isomorphism of the source over the target.
* `AlgebraicGeometry.Space.NormalizationInData.ofRepresentableTarget` is the normalization of an
  arbitrary algebraic space `X` in a representable one, for a quasi-finite separated morphism.

## Main results

* `AlgebraicGeometry.Space.contains_normalization`: the big fppf site contains the relative
  normalization of a quasi-compact quasi-separated morphism of its objects.
* `AlgebraicGeometry.Space.NormalizationInData.exists_iso_yoneda_of_representable`: every
  normalization datum of such a morphism is represented by the relative normalization scheme,
  compatibly with both legs of the factorization.
* `AlgebraicGeometry.Space.NormalizationInData.existsUnique_hom_of_representable` and
  `AlgebraicGeometry.Space.NormalizationInData.exists_iso_of_representable`: any two
  normalization data of such a morphism are identified by a unique compatible morphism, and that
  morphism is an isomorphism.
* `AlgebraicGeometry.Space.zariskiMainTheorem_ofRepresentable`: for a quasi-finite separated
  morphism of representable algebraic spaces, the canonical morphism to the normalization is a
  quasi-compact open immersion and the normalization morphism is integral.
* `AlgebraicGeometry.Space.zariskiMainTheorem_ofRepresentableTarget` is the same conjunction for
  a quasi-finite separated morphism from an arbitrary algebraic space to a representable one.

## References

* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The site contains the relative normalization of a quasi-compact quasi-separated morphism
of its objects.** -/
theorem contains_normalization (X₀ Y₀ : BigFppfOver B S hS) (f₀ : X₀ ⟶ Y₀)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)] :
    B.Contains ((BigFppfOver.toScheme B S hS).map f₀).normalization :=
  (Scheme.Hom.size_normalization_le ((BigFppfOver.toScheme B S hS).map f₀)).trans_lt
    (max_lt X₀.left.property Y₀.left.property)

/-- In a cartesian square whose lower horizontal is the identity, the upper horizontal is an
isomorphism. -/
theorem isIso_fst_of_isPullback_id
    {P X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback fst snd f (𝟙 Y)) : IsIso fst := by
  obtain ⟨c, hcf, hcs⟩ : ∃ c : X ⟶ P, c ≫ fst = 𝟙 X ∧ c ≫ snd = f :=
    ⟨h.lift (𝟙 X) f (by simp), h.lift_fst _ _ _, h.lift_snd _ _ _⟩
  refine ⟨c, h.hom_ext ?_ ?_, hcf⟩
  · rw [Category.assoc, hcf, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, hcs, Category.id_comp]
    simpa using h.w

namespace NormalizationInData

/-- **The normalization of one representable algebraic space in another.** Let `f₀ : X₀ ⟶ Y₀`
be a morphism of the big fppf site of `S` whose underlying morphism of schemes is quasi-compact
and quasi-separated. Then the relative normalization, read in the site, is normalization data
for the morphism `yoneda.map f₀` of the algebraic spaces the two objects represent. -/
def ofRepresentable (X₀ Y₀ : BigFppfOver B S hS) (f₀ : X₀ ⟶ Y₀)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)] :
    NormalizationInData B S hS (yoneda.map f₀) :=
  let hcontains : B.Contains ((BigFppfOver.toScheme B S hS).map f₀).normalization :=
    contains_normalization B S hS X₀ Y₀ f₀
  let N₀ : BigFppfOver B S hS := BigFppfOver.mk B S hS hcontains
    (((BigFppfOver.toScheme B S hS).map f₀).fromNormalization ≫ B.inclusion.map Y₀.hom)
  let hν : ∃ ν : N₀ ⟶ Y₀, (BigFppfOver.toScheme B S hS).map ν =
      ((BigFppfOver.toScheme B S hS).map f₀).fromNormalization :=
    BigFppfOver.exists_hom_of_comp_eq B S hS _ rfl
  let ht : ∃ t : X₀ ⟶ N₀, (BigFppfOver.toScheme B S hS).map t =
      ((BigFppfOver.toScheme B S hS).map f₀).toNormalization :=
    BigFppfOver.exists_hom_of_comp_eq B S hS _ (by
      change ((BigFppfOver.toScheme B S hS).map f₀).toNormalization ≫
          (((BigFppfOver.toScheme B S hS).map f₀).fromNormalization ≫
            B.inclusion.map Y₀.hom) = B.inclusion.map X₀.hom
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
        toScheme_map_comp_inclusion_hom])
  let hcomp : ht.choose ≫ hν.choose = f₀ :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, ht.choose_spec, hν.choose_spec]
      exact Scheme.Hom.toNormalization_fromNormalization _)
  { space := yoneda.obj N₀
    isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS N₀
    toNorm := yoneda.map ht.choose
    fromNorm := yoneda.map hν.choose
    fac := by rw [← yoneda.map_comp, hcomp]
    chart := by
      intro W XW w pq a hwet hsq hqc hqs
      obtain ⟨w₀, rfl⟩ : ∃ w₀ : W ⟶ Y₀, yoneda.map w₀ = w :=
        ⟨yoneda.preimage w, yoneda.map_preimage w⟩
      obtain ⟨a₀, rfl⟩ : ∃ a₀ : XW ⟶ X₀, yoneda.map a₀ = a :=
        ⟨yoneda.preimage a, yoneda.map_preimage a⟩
      have hsite : IsPullback a₀ pq f₀ w₀ := IsPullback.of_map_of_faithful yoneda hsq
      have hschemes := hsite.map (BigFppfOver.toScheme B S hS)
      have hetale : Etale ((BigFppfOver.toScheme B S hS).map w₀) :=
        (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
          (@AlgebraicGeometry.Etale.{u}) w₀).1 hwet
      have hsmooth : Smooth ((BigFppfOver.toScheme B S hS).map w₀) := inferInstance
      have hpb : IsPullback (pullback.fst hν.choose w₀) (pullback.snd hν.choose w₀)
          hν.choose w₀ := IsPullback.of_hasPullback _ _
      have hpbs := hpb.map (BigFppfOver.toScheme B S hS)
      rw [hν.choose_spec] at hpbs
      have hnorm := isPullback_normalizationMap_of_smooth
        ((BigFppfOver.toScheme B S hS).map f₀)
        ((BigFppfOver.toScheme B S hS).map w₀) hschemes
      have hlift : (a₀ ≫ ht.choose) ≫ hν.choose = pq ≫ w₀ := by
        rw [Category.assoc, hcomp]
        exact hsite.w
      have hefst := hnorm.isoIsPullback_hom_fst _ _ hpbs
      have hesnd := hnorm.isoIsPullback_hom_snd _ _ hpbs
      have hinvsnd := hnorm.isoIsPullback_inv_snd _ _ hpbs
      have hrfst : (BigFppfOver.toScheme B S hS).map
          (pullback.lift (a₀ ≫ ht.choose) pq hlift ≫ pullback.fst hν.choose w₀) =
            (BigFppfOver.toScheme B S hS).map a₀ ≫
              ((BigFppfOver.toScheme B S hS).map f₀).toNormalization := by
        rw [pullback.lift_fst, Functor.map_comp]
        exact congrArg (fun x ↦ (BigFppfOver.toScheme B S hS).map a₀ ≫ x) ht.choose_spec
      have hrsnd : (BigFppfOver.toScheme B S hS).map
          (pullback.lift (a₀ ≫ ht.choose) pq hlift ≫ pullback.snd hν.choose w₀) =
            (BigFppfOver.toScheme B S hS).map pq :=
        congrArg (BigFppfOver.toScheme B S hS).map (pullback.lift_snd _ _ _)
      have hkey : (BigFppfOver.toScheme B S hS).map
          (pullback.lift (a₀ ≫ ht.choose) pq hlift) =
            ((BigFppfOver.toScheme B S hS).map pq).toNormalization ≫
              (hnorm.isoIsPullback _ _ hpbs).hom := by
        refine hpbs.hom_ext
          (((Functor.map_comp _ _ _).symm.trans hrfst).trans
            (((Scheme.Hom.toNormalization_normalizationMap _ _ _ _ _).symm.trans
              (congrArg (fun x ↦ ((BigFppfOver.toScheme B S hS).map pq).toNormalization ≫ x)
                hefst.symm)).trans (Category.assoc _ _ _).symm))
          (((Functor.map_comp _ _ _).symm.trans hrsnd).trans
            (((Scheme.Hom.toNormalization_fromNormalization _).symm.trans
              (congrArg (fun x ↦ ((BigFppfOver.toScheme B S hS).map pq).toNormalization ≫ x)
                hesnd.symm)).trans (Category.assoc _ _ _).symm))
      refine ⟨pullback hν.choose w₀, pullback.snd hν.choose w₀,
        yoneda.map (pullback.fst hν.choose w₀),
        pullback.lift (a₀ ≫ ht.choose) pq hlift,
        (hnorm.isoIsPullback _ _ hpbs).symm, hpb.map yoneda, ?_, ?_, ?_⟩
      · rw [← yoneda.map_comp, ← yoneda.map_comp, pullback.lift_fst]
      · rwa [Iso.symm_hom, Iso.comp_inv_eq]
      · rwa [Iso.symm_hom] }

/-! ### Transport along an isomorphism of the source -/

/-- **Normalization data transports along an isomorphism of the source.**  If `ψ : X ≅ X'` is an
isomorphism of algebraic spaces over `Y` — that is, `ψ.hom ≫ f' = f` — then normalization data
for `f'` is normalization data for `f`, with the same normalization and the same normalization
morphism, and with the canonical morphism precomposed with `ψ`. -/
def ofIsoSource {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {f' : X' ⟶ Y}
    (ψ : X ≅ X') (hψ : ψ.hom ≫ f' = f) (N : NormalizationInData B S hS f') :
    NormalizationInData B S hS f where
  space := N.space
  isAlgebraicSpace := N.isAlgebraicSpace
  toNorm := ψ.hom ≫ N.toNorm
  fromNorm := N.fromNorm
  fac := by rw [Category.assoc, N.fac, hψ]
  chart := by
    intro W XW w p a hwet hsq hqc hqs
    have hiso : IsPullback ψ.hom f f' (𝟙 Y) :=
      IsPullback.of_horiz_isIso ⟨by rw [hψ, Category.comp_id]⟩
    have hsq' : IsPullback (a ≫ ψ.hom) (yoneda.map p) f' w := by
      have hp := hsq.paste_horiz hiso
      rwa [Category.comp_id] at hp
    obtain ⟨W', q, b, r, e, hbq, hrb, hre, heq⟩ := N.chart W XW w p (a ≫ ψ.hom) hwet hsq'
    exact ⟨W', q, b, r, e, hbq, by rw [hrb, Category.assoc], hre, heq⟩

/-! ### Independence of the datum -/

/-- A morphism between the underlying schemes of two objects of the big fppf category over `S`,
both given over an object `Y₀`, which commutes with the two morphisms to `Y₀`, comes from a
morphism of the category. -/
private theorem exists_hom_of_comp_over {Y₀ A C : BigFppfOver B S hS} (νA : A ⟶ Y₀)
    (νC : C ⟶ Y₀)
    (m : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (hm : m ≫ (BigFppfOver.toScheme B S hS).map νC = (BigFppfOver.toScheme B S hS).map νA) :
    ∃ μ : A ⟶ C, (BigFppfOver.toScheme B S hS).map μ = m :=
  BigFppfOver.exists_hom_of_comp_eq B S hS m (by
    rw [← toScheme_map_comp_inclusion_hom B S hS νC, ← Category.assoc, hm,
      toScheme_map_comp_inclusion_hom])

/-- **Every normalization datum of a representable morphism is represented by the relative
normalization scheme.** Let `f₀ : X₀ ⟶ Y₀` be a morphism of the big fppf site of `S` whose
underlying morphism of schemes is quasi-compact and quasi-separated, and let `N` be any
normalization datum for the induced morphism of algebraic spaces. Then `N.space` is represented
by an object `N₀` of the site whose underlying scheme is the relative normalization of that
morphism, compatibly with both legs of the factorization. -/
theorem exists_iso_yoneda_of_representable (X₀ Y₀ : BigFppfOver B S hS) (f₀ : X₀ ⟶ Y₀)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)]
    (N : NormalizationInData B S hS (yoneda.map f₀)) :
    ∃ (N₀ : BigFppfOver B S hS) (t : X₀ ⟶ N₀) (ν : N₀ ⟶ Y₀)
      (e : (BigFppfOver.toScheme B S hS).obj N₀ ≅
        ((BigFppfOver.toScheme B S hS).map f₀).normalization)
      (φ : N.space ≅ yoneda.obj N₀),
      N.toNorm ≫ φ.hom = yoneda.map t ∧
      φ.hom ≫ yoneda.map ν = N.fromNorm ∧
      (BigFppfOver.toScheme B S hS).map t ≫ e.hom =
        ((BigFppfOver.toScheme B S hS).map f₀).toNormalization ∧
      e.hom ≫ ((BigFppfOver.toScheme B S hS).map f₀).fromNormalization =
        (BigFppfOver.toScheme B S hS).map ν := by
  have hwet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 Y₀)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.Etale.{u}) (𝟙 Y₀)).2 (by
        rw [(BigFppfOver.toScheme B S hS).map_id]; infer_instance)
  have hsq : IsPullback (yoneda.map (𝟙 X₀)) (yoneda.map f₀) (yoneda.map f₀)
      (yoneda.map (𝟙 Y₀)) := by
    rw [yoneda.map_id, yoneda.map_id]
    exact IsPullback.of_id_fst
  obtain ⟨N₀, ν, b, t, e, hbq, hrb, hre, heq⟩ :=
    N.chart Y₀ X₀ (yoneda.map (𝟙 Y₀)) f₀ (yoneda.map (𝟙 X₀)) hwet hsq
  rw [yoneda.map_id] at hbq
  rw [yoneda.map_id, Category.id_comp] at hrb
  have hbw : b ≫ N.fromNorm = yoneda.map ν := by simpa using hbq.w
  have hiso : IsIso b := isIso_fst_of_isPullback_id B S hS hbq
  have hcq : inv b ≫ yoneda.map ν = N.fromNorm := by rw [IsIso.inv_comp_eq, hbw]
  refine ⟨N₀, t, ν, e, (asIso b).symm, ?_, ?_, hre, heq⟩
  · rw [Iso.symm_hom, asIso_inv, ← hrb, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [Iso.symm_hom, asIso_inv, hcq]

/-- **Uniqueness of the normalization datum, for a representable morphism.** Any two
normalization data for a morphism of representable algebraic spaces whose underlying morphism of
schemes is quasi-compact and quasi-separated are identified by a unique morphism compatible
with both legs of the factorization. -/
theorem existsUnique_hom_of_representable (X₀ Y₀ : BigFppfOver B S hS) (f₀ : X₀ ⟶ Y₀)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)]
    (N₁ N₂ : NormalizationInData B S hS (yoneda.map f₀)) :
    ∃! h : N₁.space ⟶ N₂.space,
      N₁.toNorm ≫ h = N₂.toNorm ∧ h ≫ N₂.fromNorm = N₁.fromNorm := by
  obtain ⟨A, t₁, ν₁, e₁, φ₁, ht₁, hν₁, he₁, heq₁⟩ :=
    exists_iso_yoneda_of_representable B S hS X₀ Y₀ f₀ N₁
  obtain ⟨C, t₂, ν₂, e₂, φ₂, ht₂, hν₂, he₂, heq₂⟩ :=
    exists_iso_yoneda_of_representable B S hS X₀ Y₀ f₀ N₂
  have hmν : (e₁.hom ≫ e₂.inv) ≫ (BigFppfOver.toScheme B S hS).map ν₂ =
      (BigFppfOver.toScheme B S hS).map ν₁ := by
    rw [Category.assoc, ← heq₂, Iso.inv_hom_id_assoc, heq₁]
  obtain ⟨μ, hμ⟩ := exists_hom_of_comp_over B S hS ν₁ ν₂ (e₁.hom ≫ e₂.inv) hmν
  have hμν : μ ≫ ν₂ = ν₁ :=
    (BigFppfOver.toScheme B S hS).map_injective (by rw [Functor.map_comp, hμ, hmν])
  have hμt : t₁ ≫ μ = t₂ :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, hμ, ← Category.assoc, he₁, ← he₂, Category.assoc,
        Iso.hom_inv_id, Category.comp_id])
  refine ⟨φ₁.hom ≫ yoneda.map μ ≫ φ₂.inv, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, ht₁, ← yoneda.map_comp, hμt, ← ht₂,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · have h₂ : φ₂.inv ≫ N₂.fromNorm = yoneda.map ν₂ := by
      rw [← hν₂, Iso.inv_hom_id_assoc]
    rw [Category.assoc, Category.assoc, h₂, ← yoneda.map_comp, hμν, hν₁]
  · rintro h ⟨hhs, hht⟩
    obtain ⟨k, hk⟩ : ∃ k : A ⟶ C, yoneda.map k = φ₁.inv ≫ h ≫ φ₂.hom :=
      ⟨yoneda.preimage _, yoneda.map_preimage _⟩
    have hkν : k ≫ ν₂ = ν₁ := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, hk, Category.assoc, Category.assoc, hν₂, hht, ← hν₁,
        Iso.inv_hom_id_assoc]
    have hkt : t₁ ≫ k = t₂ := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, hk, ← ht₁, ← ht₂, Category.assoc, Iso.hom_inv_id_assoc,
        ← Category.assoc, hhs]
    have hend : e₁.inv ≫ (BigFppfOver.toScheme B S hS).map k ≫ e₂.hom =
        𝟙 ((BigFppfOver.toScheme B S hS).map f₀).normalization := by
      refine Scheme.Hom.normalization_endo_eq_id _ _ ?_ ?_
      · rw [← he₁, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, hkt,
          he₂, he₁]
      · have hkey : (BigFppfOver.toScheme B S hS).map k ≫ (BigFppfOver.toScheme B S hS).map ν₂ =
            e₁.hom ≫ Scheme.Hom.fromNormalization ((BigFppfOver.toScheme B S hS).map f₀) := by
          rw [← Functor.map_comp, hkν, ← heq₁]
        rw [Category.assoc, Category.assoc, heq₂, hkey, Iso.inv_hom_id_assoc]
    have hkm : (BigFppfOver.toScheme B S hS).map k = (BigFppfOver.toScheme B S hS).map μ := by
      rw [hμ]
      calc (BigFppfOver.toScheme B S hS).map k
          = e₁.hom ≫ (e₁.inv ≫ (BigFppfOver.toScheme B S hS).map k ≫ e₂.hom) ≫ e₂.inv := by
            simp
        _ = e₁.hom ≫ e₂.inv := by rw [hend]; simp
    have : k = μ := (BigFppfOver.toScheme B S hS).map_injective hkm
    rw [← this, hk]
    simp

/-- **Any two normalization data of a representable morphism are isomorphic**, by an isomorphism
compatible with both legs of the factorization. -/
theorem exists_iso_of_representable (X₀ Y₀ : BigFppfOver B S hS) (f₀ : X₀ ⟶ Y₀)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)]
    (N₁ N₂ : NormalizationInData B S hS (yoneda.map f₀)) :
    ∃ φ : N₁.space ≅ N₂.space,
      N₁.toNorm ≫ φ.hom = N₂.toNorm ∧ φ.hom ≫ N₂.fromNorm = N₁.fromNorm := by
  obtain ⟨h₁₂, ⟨hs₁₂, ht₁₂⟩, -⟩ := existsUnique_hom_of_representable B S hS X₀ Y₀ f₀ N₁ N₂
  obtain ⟨h₂₁, ⟨hs₂₁, ht₂₁⟩, -⟩ := existsUnique_hom_of_representable B S hS X₀ Y₀ f₀ N₂ N₁
  obtain ⟨u₁, -, hu₁⟩ := existsUnique_hom_of_representable B S hS X₀ Y₀ f₀ N₁ N₁
  obtain ⟨u₂, -, hu₂⟩ := existsUnique_hom_of_representable B S hS X₀ Y₀ f₀ N₂ N₂
  refine ⟨⟨h₁₂, h₂₁, ?_, ?_⟩, hs₁₂, ht₁₂⟩
  · exact (hu₁ _ ⟨by rw [← Category.assoc, hs₁₂, hs₂₁], by rw [Category.assoc, ht₂₁, ht₁₂]⟩).trans
      (hu₁ _ ⟨by simp, by simp⟩).symm
  · exact (hu₂ _ ⟨by rw [← Category.assoc, hs₂₁, hs₁₂], by rw [Category.assoc, ht₁₂, ht₂₁]⟩).trans
      (hu₂ _ ⟨by simp, by simp⟩).symm

/-! ### The case of a representable target -/

/-- **The normalization of an arbitrary algebraic space in a representable one.** A quasi-finite
separated morphism `f : X ⟶ Y₀` from an algebraic space over `S` to a representable one has
normalization data. -/
noncomputable def ofRepresentableTarget (Y₀ : BigFppfOver B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj Y₀)
    (hX : IsAlgebraicSpace B S hS X) (hqf : IsQuasiFinite B S hS f)
    (hsep : IsSeparated B S hS f) :
    NormalizationInData B S hS f := by
  have hY : IsAlgebraicSpace B S hS (yoneda.obj Y₀) := isAlgebraicSpace_yoneda B S hS Y₀
  have hrep : yoneda.relativelyRepresentable f :=
    relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hX hY hqf.1 hsep
  have hsq : IsPullback (hrep.fst (𝟙 (yoneda.obj Y₀)))
      (yoneda.map (hrep.snd (𝟙 (yoneda.obj Y₀)))) f (𝟙 (yoneda.obj Y₀)) :=
    hrep.isPullback (𝟙 (yoneda.obj Y₀))
  haveI : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (𝟙 (yoneda.obj Y₀)))) :=
    ((isSeparated_iff_presheaf B S hS f hX hY hrep).1 hsep).property _ _ _ hsq
  haveI : QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (𝟙 (yoneda.obj Y₀)))) :=
    ((presheaf_quasiCompact_iff_isQuasiCompact B S hS hrep).2 hqf.2).property _ _ _ hsq
  haveI : QuasiSeparated ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (𝟙 (yoneda.obj Y₀)))) := inferInstance
  haveI := isIso_fst_of_isPullback_id B S hS hsq
  refine ofIsoSource B S hS (asIso (hrep.fst (𝟙 (yoneda.obj Y₀)))).symm ?_
    (ofRepresentable B S hS (hrep.pullback (𝟙 (yoneda.obj Y₀))) Y₀
      (hrep.snd (𝟙 (yoneda.obj Y₀))))
  have hw : hrep.fst (𝟙 (yoneda.obj Y₀)) ≫ f =
      yoneda.map (hrep.snd (𝟙 (yoneda.obj Y₀))) := by simpa using hsq.w
  rw [Iso.symm_hom, asIso_inv, ← hw, IsIso.inv_hom_id_assoc]

end NormalizationInData

/-- **Zariski's main theorem for a quasi-finite separated morphism of representable algebraic
spaces.** Let `f₀ : X₀ ⟶ Y₀` be a morphism of the big fppf site whose underlying morphism of
schemes is quasi-compact and quasi-separated, and suppose the induced morphism of algebraic
spaces is quasi-finite and separated. Then the canonical morphism to the normalization
`AlgebraicGeometry.Space.NormalizationInData.ofRepresentable` of `Y₀` in `X₀` is a quasi-compact
open immersion and the normalization morphism is integral. -/
theorem zariskiMainTheorem_ofRepresentable (X₀ Y₀ : BigFppfOver B S hS) (f₀ : X₀ ⟶ Y₀)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)]
    (hqf : IsQuasiFinite B S hS (yoneda.map f₀))
    (hsep : IsSeparated B S hS (yoneda.map f₀)) :
    IsOpenImmersion B S hS
        (NormalizationInData.ofRepresentable B S hS X₀ Y₀ f₀).toNorm ∧
      IsQuasiCompact B S hS
        (NormalizationInData.ofRepresentable B S hS X₀ Y₀ f₀).toNorm ∧
      IsIntegralHom B S hS
        (NormalizationInData.ofRepresentable B S hS X₀ Y₀ f₀).fromNorm :=
  ⟨(NormalizationInData.ofRepresentable B S hS X₀ Y₀
      f₀).isOpenImmersion_toNorm_of_isQuasiFinite_isSeparated
      (isAlgebraicSpace_yoneda B S hS X₀) (isAlgebraicSpace_yoneda B S hS Y₀) hqf hsep,
    (NormalizationInData.ofRepresentable B S hS X₀ Y₀
      f₀).isQuasiCompact_toNorm_of_isQuasiFinite_isSeparated
      (isAlgebraicSpace_yoneda B S hS X₀) (isAlgebraicSpace_yoneda B S hS Y₀) hqf hsep,
    (NormalizationInData.ofRepresentable B S hS X₀ Y₀
      f₀).isIntegralHom_fromNorm_of_isQuasiFinite_isSeparated
      (isAlgebraicSpace_yoneda B S hS X₀) (isAlgebraicSpace_yoneda B S hS Y₀) hqf hsep⟩

/-- **Zariski's main theorem for a quasi-finite separated morphism to a representable algebraic
space.** Let `f : X ⟶ Y₀` be a quasi-finite separated morphism from an algebraic space over `S`
to the algebraic space represented by an object of the big fppf site. Then the canonical
morphism to the normalization
`AlgebraicGeometry.Space.NormalizationInData.ofRepresentableTarget` of `Y₀` in `X` is a
quasi-compact open immersion and the normalization morphism is integral. -/
theorem zariskiMainTheorem_ofRepresentableTarget (Y₀ : BigFppfOver B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj Y₀)
    (hX : IsAlgebraicSpace B S hS X) (hqf : IsQuasiFinite B S hS f)
    (hsep : IsSeparated B S hS f) :
    IsOpenImmersion B S hS
        (NormalizationInData.ofRepresentableTarget B S hS Y₀ f hX hqf hsep).toNorm ∧
      IsQuasiCompact B S hS
        (NormalizationInData.ofRepresentableTarget B S hS Y₀ f hX hqf hsep).toNorm ∧
      IsIntegralHom B S hS
        (NormalizationInData.ofRepresentableTarget B S hS Y₀ f hX hqf hsep).fromNorm :=
  ⟨(NormalizationInData.ofRepresentableTarget B S hS Y₀ f hX hqf
      hsep).isOpenImmersion_toNorm_of_isQuasiFinite_isSeparated hX
      (isAlgebraicSpace_yoneda B S hS Y₀) hqf hsep,
    (NormalizationInData.ofRepresentableTarget B S hS Y₀ f hX hqf
      hsep).isQuasiCompact_toNorm_of_isQuasiFinite_isSeparated hX
      (isAlgebraicSpace_yoneda B S hS Y₀) hqf hsep,
    (NormalizationInData.ofRepresentableTarget B S hS Y₀ f hX hqf
      hsep).isIntegralHom_fromNorm_of_isQuasiFinite_isSeparated hX
      (isAlgebraicSpace_yoneda B S hS Y₀) hqf hsep⟩

end AlgebraicGeometry.Space

end
