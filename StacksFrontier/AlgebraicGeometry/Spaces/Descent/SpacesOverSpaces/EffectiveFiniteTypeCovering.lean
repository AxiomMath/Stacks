module

public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraicSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveCountableCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Effectivity of descent data along fppf coverings of any size (Stacks 0ADV, part (2))

Let `{f i : X i ⟶ T}` be an fppf covering of algebraic spaces over `S`, indexed by a type of
any size. This file proves that a descent datum `(Y i, φ i j)` relative to it is effective as
soon as each `Y i ⟶ X i` is of finite type. This is part (2) of Stacks 0ADV. It also proves
effectivity for a covering of any size when the spaces of the covering and of the descent
datum have atlases of uniformly bounded size, the bound and the index set both lying below
the cutoff of the site.

The obstruction to effectivity for a large index set is the size of the sheaf `F` the datum
descends to (Stacks 0ADT). By Stacks 04S6, `F` is an algebraic space as soon as some fppf covering
`{R k ⟶ T}` has algebraic sheaf coproducts `∐ R k` and `∐ (R k ×_T F)`. Stacks 02WQ provides
those coproducts once the atlases of the summands are uniformly bounded below the cutoff and
the index set is bounded too (`AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le`).

For part (2) the covering is first refined, as in the source's proof. Choose a scheme atlas
`U ⟶ T`. The pullback of the covering to `U` is refined by schemes (Stacks 042T), and then
by an fppf covering of `U` by affine schemes, at most `size U` of them, each of size at most
`size U` (`AlgebraicGeometry.exists_small_affine_refinement`, Stacks 04T7 for the bound). Over
each affine member `R k`, the fibre `R k ×_T F = R k ×_{X i} Y i` is of finite type, hence
quasi-compact. So it has an affine étale atlas, which is locally of finite type over `R k`,
and Stacks 04T7 bounds its size by `size (R k) ≤ size U`. This is the size bound of the
source's appeal to Stacks 04U0, used directly.

## Main results

* `AlgebraicGeometry.exists_small_affine_refinement`: an fppf covering of a scheme `X` is
  refined by an fppf covering by at most `size X` affine schemes, each of size at most
  `size X`.
* `AlgebraicGeometry.Space.exists_affine_refinement_of_isFppfCovering`: an fppf covering of an
  algebraic space is refined by an fppf covering by affine objects of the site, with the index
  type and the sizes of the members bounded by one cardinal below the cutoff.
* `AlgebraicGeometry.Space.exists_atlas_size_le_of_isFiniteType`: an algebraic space of finite
  type over an affine object `R` has an étale atlas of size at most `size R`.
* `AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_size_le`: a descent datum along
  an fppf covering of any size is effective when the index type and the atlases of all the
  spaces involved are bounded by one cardinal below the cutoff.
* `AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_isFiniteType`: **Stacks 0ADV,
  part (2)**.

## References

* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 042T](https://stacks.math.columbia.edu/tag/042T)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 04U0](https://stacks.math.columbia.edu/tag/04U0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v

namespace AlgebraicGeometry

/-- **An fppf covering of a scheme is refined by a small fppf covering by affine schemes.**

Let `𝒞` be an fppf covering of a scheme `X`. There is an fppf covering `𝒲` of `X` refining
`𝒞` whose members are affine schemes, with at most `size X` members, each of size at most
`size X`. The members are affine opens of members of `𝒞`, finitely many for each affine open
of `X`. Each is quasi-compact and locally of finite type over `X`, so Stacks 04T7 bounds its
size. -/
theorem exists_small_affine_refinement (X : Scheme.{u}) (𝒞 : FppfCovering.{v} X) :
    ∃ 𝒲 : FppfCovering.{u} X, 𝒲.IsRefinement 𝒞 ∧ #𝒲.ι ≤ X.size ∧
      (∀ j, IsAffine (𝒲.X j)) ∧ ∀ j, (𝒲.X j).size ≤ X.size := by
  choose n a V hVaff hVcov using 𝒞.exists_finite_affineOpens_cover
  refine ⟨{ ι := Σ U : X.affineOpens, Fin (n U)
            X := fun j => (V j.1 j.2).toScheme
            f := fun j => (V j.1 j.2).ι ≫ 𝒞.f (a j.1 j.2)
            flat := fun j => by have := 𝒞.flat (a j.1 j.2); infer_instance
            lfp := fun j => by have := 𝒞.lfp (a j.1 j.2); infer_instance
            jointly_surjective := ?_ }, fun j => ⟨a j.1 j.2, (V j.1 j.2).ι, rfl⟩, ?_,
            fun j => hVaff j.1 j.2, ?_⟩
  · intro t
    obtain ⟨W, hW, htW, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top t)
    have htU : t ∈ ⋃ k, (𝒞.f (a ⟨W, hW⟩ k)) '' (V ⟨W, hW⟩ k : Set (𝒞.X (a ⟨W, hW⟩ k))) := by
      rw [hVcov ⟨W, hW⟩]; exact htW
    obtain ⟨k, x, hxV, hxt⟩ := Set.mem_iUnion.mp htU
    exact ⟨⟨⟨W, hW⟩, k⟩, ⟨x, hxV⟩, hxt⟩
  · change #(Σ U : X.affineOpens, Fin (n U)) ≤ X.size
    rw [Cardinal.mk_sigma]
    refine (sum_le_sum _ (fun _ => (ℵ₀ : Cardinal.{0})) fun _ => mk_lt_aleph0.le).trans ?_
    rw [sum_const, lift_uzero, lift_aleph0]
    exact (mul_le_mul' X.mk_affineOpens_le_size X.aleph0_le_size).trans_eq
      (Cardinal.mul_eq_self X.aleph0_le_size)
  · rintro ⟨U, k⟩
    have := 𝒞.flat (a U k)
    have := 𝒞.lfp (a U k)
    have : IsAffine (V U k).toScheme := hVaff U k
    exact Scheme.size_le_of_locallyOfFiniteType ((V U k).ι ≫ 𝒞.f (a U k))

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An fppf covering of an algebraic space is refined by a bounded fppf covering by affine
objects of the site.**

Let `{f i : X i ⟶ T}` be an fppf covering of algebraic spaces over `S`, indexed by a type of
any size. There are a cardinal `μ` with `ℵ₀ ≤ μ < B.cutoff`, an index type `K` of the working
universe with `#K ≤ μ`, and objects `R k` of the site with affine underlying schemes of size at
most `μ`, such that the family `{R k ⟶ T}` is an fppf covering and each of its members factors
through a member of the given covering.

Here `μ` is the size of a scheme atlas `U ⟶ T`. The pullback of the covering to `U` is refined
by schemes (Stacks 042T), and then by affine schemes
(`AlgebraicGeometry.exists_small_affine_refinement`). -/
theorem exists_affine_refinement_of_isFppfCovering {ι : Type v}
    {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ T} (hcov : IsFppfCovering B S hS X f) :
    ∃ (K : Type u) (R : K → BigFppfOver B S hS) (r : ∀ k, yoneda.obj (R k) ⟶ T)
      (a : K → ι) (b : ∀ k, yoneda.obj (R k) ⟶ X (a k)) (μ : Cardinal.{u}),
      IsFppfCovering B S hS (fun k ↦ yoneda.obj (R k)) r ∧ (∀ k, b k ≫ f (a k) = r k) ∧
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (R k))) ∧
      ℵ₀ ≤ μ ∧ μ < B.cutoff ∧ #K ≤ μ ∧
      ∀ k, ((BigFppfOver.toScheme B S hS).obj (R k)).size ≤ μ := by
  classical
  have hT := hcov.target_isAlgebraicSpace
  obtain ⟨U, u, hus, hue⟩ := hT.exists_atlas
  let G := BigFppfOver.toScheme B S hS
  let Tsp : AlgebraicSpaces B S hS := ⟨T, hT⟩
  let Xsp : ι → AlgebraicSpaces B S hS := fun i ↦ ⟨X i, hcov.source_isAlgebraicSpace i⟩
  let usp : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ Tsp :=
    ObjectProperty.homMk u
  let fsp : ∀ i, Xsp i ⟶ Tsp := fun i ↦ ObjectProperty.homMk (f i)
  have hP := isFppfCovering_fibreProduct B S hS Xsp fsp usp hcov
  obtain ⟨W, h, hW⟩ := exists_fppfCovering_scheme_refinement B S hS _ _ hP
  change ∀ i, yoneda.obj (W i) ⟶ pullback u (f i) at h
  let q : ∀ i, W i ⟶ U := fun i ↦ yoneda.preimage (h i ≫ pullback.fst u (f i))
  have hq : ∀ i, yoneda.map (q i) = h i ≫ pullback.fst u (f i) := fun i ↦ yoneda.map_preimage _
  have hW' : IsFppfCovering B S hS (fun i ↦ yoneda.obj (W i)) (fun i ↦ yoneda.map (q i)) := by
    rwa [funext hq]
  let 𝒞 : FppfCovering.{v} (G.obj U) :=
    { ι := ι
      X := fun i ↦ G.obj (W i)
      f := fun i ↦ G.map (q i)
      flat := fun i ↦ hW'.flat i (W i) U (𝟙 _) (𝟙 _) (q i) (presheaf_etale_id B S hS (W i))
        (presheaf_etale_id B S hS U) (by simp)
      lfp := fun i ↦ hW'.locallyOfFinitePresentation i (W i) U (𝟙 _) (𝟙 _) (q i)
        (presheaf_etale_id B S hS (W i)) (presheaf_etale_id B S hS U) (by simp)
      jointly_surjective :=
        exists_preimage_of_jointlySurjective_yoneda B S hS W U q hW'.jointly_surjective }
  obtain ⟨𝒲, href, hcard, haff, hsize⟩ := exists_small_affine_refinement (G.obj U) 𝒞
  choose c g hg using href
  have hcont : ∀ k, B.Contains (𝒲.X k) := fun k ↦ (hsize k).trans_lt U.left.property
  let R : 𝒲.ι → BigFppfOver B S hS := fun k ↦
    Over.mk (ObjectProperty.homMk (X := B.obj (hcont k)) (Y := B.obj hS) (𝒲.f k ≫ U.hom.hom))
  have hρ : ∀ k, ∃ ρ : R k ⟶ U, G.map ρ = 𝒲.f k := fun k ↦
    BigFppfOver.exists_hom_of_comp_eq B S hS (X := R k) (Y := U) (𝒲.f k) rfl
  choose ρ hρ using hρ
  have hWhom : ∀ i, B.inclusion.map (W i).hom = G.map (q i) ≫ B.inclusion.map U.hom := by
    intro i
    rw [← Over.w (q i), Functor.map_comp]
    rfl
  have hγ : ∀ k, ∃ γ : R k ⟶ W (c k), G.map γ = g k := fun k ↦
    BigFppfOver.exists_hom_of_comp_eq B S hS (X := R k) (Y := W (c k)) (g k) (by
      rw [hWhom, ← Category.assoc, hg k]
      rfl)
  choose γ hγ using hγ
  have hργ : ∀ k, γ k ≫ q (c k) = ρ k := fun k ↦
    G.map_injective (by rw [G.map_comp, hγ, hρ]; exact hg k)
  have hRU : IsFppfCovering B S hS (fun k ↦ yoneda.obj (R k)) (fun k ↦ yoneda.map (ρ k)) :=
    isFppfCovering_yoneda_map B S hS R ρ (fun k ↦ by rw [hρ]; exact 𝒲.flat k)
      (fun k ↦ by rw [hρ]; exact 𝒲.lfp k)
      (fun x ↦ by
        obtain ⟨k, y, hy⟩ := 𝒲.jointly_surjective x
        exact ⟨k, y, by rw [hρ]; exact hy⟩)
  have hUT : IsFppfCovering B S hS (fun _ : PUnit.{1} ↦ yoneda.obj U) (fun _ ↦ u) :=
    isFppfCovering_atlas B S hS hT hus hue
  have hcomp := isFppfCovering_comp B S hS PUnit.{1} (fun _ ↦ 𝒲.ι) (fun _ ↦ yoneda.obj U)
    (fun _ k ↦ yoneda.obj (R k)) (fun _ ↦ u) (fun _ k ↦ yoneda.map (ρ k)) hUT (fun _ ↦ hRU)
  have hcovR := hcomp.reindex B S hS
    (σ := fun k : 𝒲.ι ↦ (⟨PUnit.unit, k⟩ : Σ _ : PUnit.{1}, 𝒲.ι))
    (fun p ↦ by obtain ⟨⟨⟩, k⟩ := p; exact ⟨k, rfl⟩)
  refine ⟨𝒲.ι, R, fun k ↦ yoneda.map (ρ k) ≫ u, c,
    fun k ↦ yoneda.map (γ k) ≫ h (c k) ≫ pullback.snd u (f (c k)), (G.obj U).size, hcovR,
    fun k ↦ ?_, haff, (G.obj U).aleph0_le_size, U.left.property, hcard, hsize⟩
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (h (c k)), ← hq,
    ← Category.assoc, ← Functor.map_comp, hργ]

/-- **An algebraic space of finite type over an affine object has an atlas no larger than that
object.**

Let `p : Z ⟶ h_R` be a morphism of finite type from an algebraic space to the representable
presheaf of an object `R` of the site whose underlying scheme is affine. Then `Z` has a
surjective étale atlas `h_V ⟶ Z` with `size V ≤ size R`. `Z` is quasi-compact, so it has an
affine surjective étale atlas `V` (Stacks 03H6). The composite `V ⟶ R` is locally of finite
type, so Stacks 04T7 bounds `size V` by `size R`. -/
theorem exists_atlas_size_le_of_isFiniteType {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) {R : BigFppfOver B S hS}
    (hR : IsAffine ((BigFppfOver.toScheme B S hS).obj R)) (p : Z ⟶ yoneda.obj R)
    (hp : IsFiniteType B S hS p) :
    ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Z),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤
        ((BigFppfOver.toScheme B S hS).obj R).size := by
  have hR' := isAlgebraicSpace_yoneda B S hS R
  have hqc : IsQuasiCompactSpace B S hS Z :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 (yoneda.obj R)) p))
      (hp.2 _ hR' (isQuasiCompactSpace_yoneda_of_isAffine B S hS R hR) (𝟙 _))
  obtain ⟨V, a, hVaff, hsurj, hetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z hZ).1 hqc
  refine ⟨V, a, hsurj, (isEtale_iff_presheaf_of_yoneda B S hS a).1 hetale, ?_⟩
  have hcomp : IsLocallyOfFiniteType B S hS (a ≫ p) :=
    isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS V) hZ hR' a p
      (holdsOnEveryEtaleChart_of_isEtale B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (fun _ hg => have := hg; inferInstance) hZ hetale)
      hp.1
  have hgmap : IsLocallyOfFiniteType B S hS (yoneda.map (yoneda.preimage (a ≫ p))) := by
    rwa [Functor.map_preimage]
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ p))) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (yoneda.preimage (a ≫ p))).1 hgmap
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := by
    have := hVaff
    infer_instance
  exact Scheme.size_le_of_locallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ p)))

namespace Descent

/-- **A coproduct, in sheaves, of algebraic spaces with uniformly bounded atlases is an
algebraic space**, when the index type is bounded by the same cardinal below the cutoff.

This is Stacks 02WQ in the form `AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le`,
read on the coproduct of sheaves and with the index type transported to the working universe
along `equivShrink`. -/
theorem isAlgebraicSpace_sigma_of_size_le {ι : Type v} [Small.{u} ι]
    (Z : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : ∀ i, IsAlgebraicSpace B S hS (Z i))
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hι : #(Shrink.{u} ι) ≤ μ)
    (hat : ∀ i, ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Z i),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ) :
    IsAlgebraicSpace B S hS (∐ fun i ↦ spaceSheaf (Z i) (hZ i)).obj := by
  choose V a hsurj hetale hsize using hat
  exact isAlgebraicSpace_coproduct_of_size_le B S hS Z hZ _ (Sigma.ι _)
    (coproductIsCoproduct _) V a hsurj hetale (equivShrink.{u} ι).symm hℵ hμ hι hsize

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ T}
    {hT : IsAlgebraicSpace B S hS T} {hX : ∀ i, IsAlgebraicSpace B S hS (X i)}

namespace DescentData

variable (D : DescentData f hT hX)

/-- **Descent data along an fppf covering of any size are effective under a uniform size
bound.**

Let `{f i : X i ⟶ T}` be an fppf covering of algebraic spaces over `S` and let
`(Y i, φ i j)` be a descent datum relative to it. Let `μ` be a cardinal with
`ℵ₀ ≤ μ < B.cutoff` which bounds the index type, and assume each `X i` and each `Y i` has a
surjective étale atlas by a scheme of size at most `μ`. Then the descent datum is effective.

This is the generalization the footnote to Stacks 0ADV has in mind: "We can allow larger index
sets here if we can bound the size of the algebraic spaces which we are descending." The
proof of part (1) applies verbatim once the coproducts `∐ X i` and `∐ Y i` are algebraic
spaces, which Stacks 02WQ gives under the bound. -/
theorem isEffective_of_size_le [Small.{u} ι] (hcov : IsFppfCovering B S hS X f)
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hι : #(Shrink.{u} ι) ≤ μ)
    (hXat : ∀ i, ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ X i),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ)
    (hYat : ∀ i, ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ (D.obj i).left),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ) :
    D.IsEffective :=
  (isAlgebraicSpace_inverse_iff_isEffective f hcov D).1 <|
    isAlgebraicSpace_of_isPullback_of_isAlgebraicSpace_sigma hcov
      ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).property.1
      ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom
      (fun i ↦ (D.obj i).left) D.obj_isAlgebraicSpace (descentInclusion f hcov D)
      (fun i ↦ (D.obj i).hom) (isPullback_descentInclusion f hcov D)
      (isAlgebraicSpace_sigma_of_size_le X hX hℵ hμ hι hXat)
      (isAlgebraicSpace_sigma_of_size_le _ D.obj_isAlgebraicSpace hℵ hμ hι hYat)

/-- **Stacks 0ADV, part (2).** Let `{f i : X i ⟶ T}` be an fppf covering of algebraic spaces
over `S`, indexed by a type of any size. Then every descent datum `(Y i, φ i j)` relative to it
with each `Y i ⟶ X i` of finite type is effective.

The proof is the source's. The sheaf `F` of Stacks 0ADT the datum descends to has
`X i ×_T F = Y i`. Refine the covering by an fppf covering `{R k ⟶ T}` by affine objects of
the site, with the index type and the sizes of the members bounded by the size `μ` of an atlas
of `T`
(`AlgebraicGeometry.Space.exists_affine_refinement_of_isFppfCovering`, which uses Stacks 042T).
If `R k ⟶ T` factors through `X i`, then `R k ×_T F = R k ×_{X i} Y i` is of finite type over
the affine `R k`. So it has an atlas of size at most `size (R k) ≤ μ` by Stacks 04T7
(`AlgebraicGeometry.Space.exists_atlas_size_le_of_isFiniteType`). This is the size bound the
source draws from Stacks 04U0. Stacks 02WQ then makes the coproducts `∐ R k` and
`∐ (R k ×_T F)` algebraic spaces, and Stacks 04S6 makes `F` an algebraic space. -/
@[stacks 0ADV "part (2): finite type, index set of any size"]
theorem isEffective_of_isFiniteType (hcov : IsFppfCovering B S hS X f)
    (hft : ∀ i, IsFiniteType B S hS (D.obj i).hom) : D.IsEffective := by
  obtain ⟨K, R, r, a, b, μ, hcovR, hbr, haff, hℵ, hμ, hK, hsize⟩ :=
    exists_affine_refinement_of_isFppfCovering hcov
  have hKs : #(Shrink.{u} K) ≤ μ := (Cardinal.mk_congr (equivShrink.{u} K)).symm.trans_le hK
  let Z : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun k ↦ pullback (D.obj (a k)).hom (b k)
  have hZ : ∀ k, IsAlgebraicSpace B S hS (Z k) := fun k ↦
    isAlgebraicSpace_pullback B S hS _ _ (D.obj_isAlgebraicSpace (a k))
      (isAlgebraicSpace_yoneda B S hS (R k)) (hX (a k))
  have hpb : ∀ k, IsPullback
      (pullback.fst (D.obj (a k)).hom (b k) ≫ descentInclusion f hcov D (a k))
      (pullback.snd (D.obj (a k)).hom (b k))
      ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom (r k) := fun k ↦ by
    rw [← hbr k]
    exact (IsPullback.of_hasPullback (D.obj (a k)).hom (b k)).paste_horiz
      (isPullback_descentInclusion f hcov D (a k))
  have hZat : ∀ k, ∃ (V : BigFppfOver B S hS) (e : yoneda.obj V ⟶ Z k),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) e ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) e ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := fun k ↦ by
    obtain ⟨V, e, hsurj, hetale, hV⟩ := exists_atlas_size_le_of_isFiniteType (hZ k) (haff k)
      (pullback.snd (D.obj (a k)).hom (b k))
      (IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback (D.obj (a k)).hom (b k)).flip
        (D.obj_isAlgebraicSpace (a k)) (hX (a k)) (hft (a k)))
    exact ⟨V, e, hsurj, hetale, hV.trans (hsize k)⟩
  have hRat : ∀ k, ∃ (V : BigFppfOver B S hS) (e : yoneda.obj V ⟶ yoneda.obj (R k)),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) e ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) e ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := fun k ↦
    ⟨R k, 𝟙 _, presheaf_surjective_id B S hS (R k), presheaf_etale_id B S hS (R k), hsize k⟩
  exact (isAlgebraicSpace_inverse_iff_isEffective f hcov D).1 <|
    isAlgebraicSpace_of_isPullback_of_isAlgebraicSpace_sigma (hX := fun k ↦
      isAlgebraicSpace_yoneda B S hS (R k)) hcovR
      ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).property.1
      ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom Z hZ
      (fun k ↦ pullback.fst (D.obj (a k)).hom (b k) ≫ descentInclusion f hcov D (a k))
      (fun k ↦ pullback.snd (D.obj (a k)).hom (b k)) hpb
      (isAlgebraicSpace_sigma_of_size_le _ _ hℵ hμ hKs hRat)
      (isAlgebraicSpace_sigma_of_size_le Z hZ hℵ hμ hKs hZat)

end DescentData

end Descent

end Space

end AlgebraicGeometry

end
