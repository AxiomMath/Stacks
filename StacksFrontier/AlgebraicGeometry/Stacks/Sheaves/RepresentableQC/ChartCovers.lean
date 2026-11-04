module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteCartesianModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.ChartFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coverings of `𝒳_{affine}` by the affine étale charts of a representing algebraic space

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids which is representable by an
algebraic space `F`, and let `j : F_{affine, étale} ⥤ 𝒳_{affine}` be the functor of
`AlgebraicGeometry.Stack.affineEtaleInclusion`. This file shows that every object `x` of
`𝒳_{affine}` has a finite étale covering `x_i ⟶ x` in the associated affine étale site whose
members map to objects in the image of `j`, and that such a covering is jointly faithfully
flat on the rings of functions: a module over `𝒪(x)` whose base changes to all the `𝒪(x_i)`
vanish is zero.

## Main results

* `ModuleCat.isZero_of_isZero_extendScalars_of_faithfullyFlat_pi`: extension of scalars along a
  finite family of ring maps whose product is faithfully flat detects the zero module.
* `CategoryTheory.GrothendieckTopology.coversTop_comp_of_isCoverDense`: precomposing a family of
  objects covering the final object with a cover-dense functor, along a continuous functor,
  still covers the final object.
* `AlgebraicGeometry.Stack.coversTop_affineEtaleInclusion`: the objects `j(y)` cover the final
  object of the associated affine étale site of `𝒳`.
* `AlgebraicGeometry.Stack.AffineCategory.exists_finite_etale_covering`: a covering sieve of the
  associated affine étale site contains a finite covering family lying over an étale covering
  of affine schemes.
* `AlgebraicGeometry.Stack.AffineCategory.isZero_of_isZero_extendScalars`: along a finite family
  of `𝒳_{affine}` lying over a flat covering, extension of scalars on the rings of functions
  detects the zero module.
* `AlgebraicGeometry.Stack.exists_finite_etale_covering_affineEtaleInclusion`: **every object of
  `𝒳_{affine}` has a finite étale covering by objects mapping to the image of `j`, jointly
  faithfully flat on the rings of functions.**

## References

* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m t

/-! ### Extension of scalars along a faithfully flat finite product -/

/-- **Extension of scalars along a finite family of ring maps whose product is faithfully flat
detects the zero module**: if `B_i ⊗_A M = 0` for every `i` then `M = 0`. -/
@[ega "IV 2.2.7" "partial"]
theorem ModuleCat.isZero_of_isZero_extendScalars_of_faithfullyFlat_pi {A : Type u}
    [CommRing A] {ι : Type*} [Finite ι] {B : ι → Type v} [∀ i, CommRing (B i)]
    (φ : ∀ i, A →+* B i) (h : (RingHom.pi φ).FaithfullyFlat) (M : ModuleCat.{m} A)
    (hM : ∀ i, IsZero ((ModuleCat.extendScalars (φ i)).obj M)) : IsZero M := by
  classical
  have := Fintype.ofFinite ι
  let : ∀ i, Algebra A (B i) := fun i => (φ i).toAlgebra
  have : Module.FaithfullyFlat A (∀ i, B i) := h
  have (i : ι) : Subsingleton (TensorProduct A (B i) M) :=
    ModuleCat.isZero_iff_subsingleton.mp (hM i)
  have : Subsingleton (TensorProduct A (∀ i, B i) M) :=
    (TensorProduct.piLeft A M B).toEquiv.subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A (∀ i, B i)).mp this)

namespace CategoryTheory.GrothendieckTopology

/-- **Covering the final object through a cover-dense functor.** If the objects `G(c)` cover the
final object of `(D, K)` and `G` is continuous, then for a cover-dense `i : C' ⥤ C` the objects
`G(i(c'))` cover it as well. -/
theorem coversTop_comp_of_isCoverDense {C' C D : Type*} [Category* C'] [Category* C]
    [Category* D] (i : C' ⥤ C) (G : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [i.IsCoverDense J] [G.IsContinuous J K]
    (hG : K.CoversTop G.obj) : K.CoversTop (i ⋙ G).obj := by
  intro X
  refine K.transitive (hG X) _ ?_
  rintro Z f ⟨Y, ⟨h⟩⟩
  have h₁ : (Sieve.coverByImage i Y).functorPushforward G ∈ K (G.obj Y) :=
    (CoverPreserving.of_isContinuous G J K).cover_preserve (Functor.IsCoverDense.is_cover Y)
  refine K.superset_covering ?_ (K.pullback_stable h ↑h₁)
  rintro W g ⟨V, b, a, ⟨hb⟩, hfac⟩
  exact ⟨hb.1, ⟨a ≫ G.map hb.lift⟩⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- **The affine étale charts of `F` cover `𝒳_{affine, étale}`**: the objects `j(y)`, for `y` an
affine étale chart of `F`, cover the final object of the associated affine étale site of `𝒳`. -/
theorem coversTop_affineEtaleInclusion (hF : IsAlgebraicSpace B S hS F)
    (hp : p.IsFiberedInGroupoids) :
    (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS)).CoversTop
      (affineEtaleInclusion B S hS F p e).obj := by
  have hd := isDenseSubsite_affineInclusion_etale B S hS p hp
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2.isCoverDense
  have : (restrictionFunctor B S hS F p e).IsContinuous (Space.SmallEtale.topology B S hS F)
      (associatedTopology B S hS p B.etaleTopology) :=
    restrictionFunctor_isContinuous B S hS F p hp e
  have hK : (associatedTopology B S hS p B.etaleTopology).CoversTop
      (affineEtaleInclusion B S hS F p e ⋙ AffineCategory.inclusion B S hS p).obj :=
    GrothendieckTopology.coversTop_comp_of_isCoverDense (AffineEtale.inclusion B S hS F)
      (restrictionFunctor B S hS F p e) (Space.SmallEtale.topology B S hS F) _
      (restrictionFunctor_coversTop B S hS F p hF hp e)
  intro x
  refine GrothendieckTopology.superset_covering _ ?_
    ((AffineCategory.inclusion B S hS p).cover_lift _
      (associatedTopology B S hS p B.etaleTopology)
      (hK ((AffineCategory.inclusion B S hS p).obj x)))
  rintro z f ⟨y, ⟨g⟩⟩
  exact ⟨y, ⟨(AffineCategory.inclusion B S hS p).preimage g⟩⟩

namespace AffineCategory

/-- **A covering sieve of the associated affine étale site contains a finite covering family
lying over an étale covering of affine schemes.** -/
theorem exists_finite_etale_covering (hp : p.IsFiberedInGroupoids)
    {x : AffineCategory B S hS p} (T : Sieve x)
    (hT : T ∈ associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS) x) :
    ∃ E : PreZeroHypercover.{u + 1} x, Finite E.I₀ ∧
      (E.map (toScheme B S hS p)).presieve₀ ∈
        Scheme.precoverage @Etale ((toScheme B S hS p).obj x) ∧
      E.sieve₀ ∈
        associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS) x ∧
      E.sieve₀ ≤ T := by
  classical
  let q := toAffine B S hS p
  let L := BigAffineFppf.toScheme B S hS
  have hq := isFiberedInGroupoids_toAffine B S hS p hp
  have hT' := (Functor.mem_inheritedTopology_iff_functorPushforward q
    (BigAffineEtale.topology B.toBigEtaleSite S hS) hq T).1 hT
  obtain ⟨D₀, hD, hle⟩ := exists_covering_refining_sieve
    (BigAffineEtale.IsCovering B.toBigEtaleSite S hS)
    (BigAffineEtale.precoverage B.toBigEtaleSite S hS)
    (fun {_ _} hR => by obtain ⟨E, rfl, hE⟩ := hR; exact ⟨E, hE, rfl⟩)
    (BigAffineEtale.isSite B.toBigEtaleSite S hS) hT'
  let D : PreZeroHypercover.{u + 1} (q.obj x) := D₀
  have hcov : D.sieve₀ ∈ BigAffineEtale.topology B.toBigEtaleSite S hS (q.obj x) :=
    Precoverage.generate_mem_toGrothendieck ⟨D₀, rfl, hD⟩
  have hetale : (D.map L).presieve₀ ∈ Scheme.precoverage @Etale (L.obj (q.obj x)) :=
    hD.1.etale
  obtain ⟨hsurj, het⟩ := (Scheme.presieve₀_mem_precoverage_iff (D.map L)).mp hetale
  have hfin : Finite D.I₀ := hD.2.2.1
  have hmem : ∀ k : D.I₀, ∃ (y : AffineCategory B S hS p) (g : y ⟶ x) (h : D.X k ⟶ q.obj y),
      T g ∧ D.f k = h ≫ q.map g := fun k => hle _ _ (Presieve.ofArrows.mk k)
  choose y g h hg hfac using hmem
  have hlift : ∀ k, ∃ (z : AffineCategory B S hS p) (φ : z ⟶ y k), q.IsHomLift (h k) φ :=
    fun k => hq.exists_lift (h k) (y k) rfl
  choose z φ hφ using hlift
  have hmap : ∀ k, q.map (φ k ≫ g k) =
      eqToHom (IsHomLift.domain_eq q (h k) (φ k)) ≫ D.f k := by
    intro k
    have := hφ k
    rw [q.map_comp, IsHomLift.fac' q (h k) (φ k), hfac k]
    simp
  let E : PreZeroHypercover.{u + 1} x := ⟨D.I₀, z, fun k => φ k ≫ g k⟩
  refine ⟨E, hfin, ?_, ?_, ?_⟩
  · refine (Scheme.presieve₀_mem_precoverage_iff (E.map (toScheme B S hS p))).mpr ⟨?_, ?_⟩
    · intro a
      obtain ⟨k, b, rfl⟩ := hsurj a
      have := hφ k
      let c := L.map (eqToHom (IsHomLift.domain_eq q (h k) (φ k)))
      obtain ⟨d, rfl⟩ := (inferInstance : Surjective c).surj b
      refine ⟨k, d, ?_⟩
      show (L.map (q.map (φ k ≫ g k))) d = _
      rw [hmap k, L.map_comp, Scheme.Hom.comp_apply]
      rfl
    · intro k
      show Etale (L.map (q.map (φ k ≫ g k)))
      rw [hmap k, L.map_comp]
      have := het k
      change Etale (L.map (D.f k)) at this
      infer_instance
  · apply (Functor.mem_inheritedTopology_iff_functorPushforward q _ hq _).mpr
    refine GrothendieckTopology.superset_covering _ ?_ hcov
    rintro _ _ ⟨_, a, _, ⟨k⟩, rfl⟩
    have := hφ k
    refine ⟨z k, φ k ≫ g k, a ≫ eqToHom (IsHomLift.domain_eq q (h k) (φ k)).symm,
      Sieve.ofArrows_mk _ _ k, ?_⟩
    rw [hmap k]
    simp
  · rintro _ _ ⟨_, a, _, ⟨k⟩, rfl⟩
    rw [← Category.assoc]
    exact T.downward_closed (hg k) (a ≫ φ k)

/-- **Along a finite family of `𝒳_{affine}` lying over a flat covering of affine schemes,
extension of scalars on the rings of functions detects the zero module**: a module `M` over
`𝒪(x)` with `M ⊗_{𝒪(x)} 𝒪(x_i) = 0` for every member `x_i ⟶ x` is zero. -/
theorem isZero_of_isZero_extendScalars {x : AffineCategory B S hS p}
    (E : PreZeroHypercover.{m} x) (hfin : Finite E.I₀)
    (hE : (E.map (toScheme B S hS p)).presieve₀ ∈
      Scheme.precoverage @Flat ((toScheme B S hS p).obj x))
    (M : ModuleCat.{t} ((affineStructureCommPresheaf B S hS p).obj (Opposite.op x)))
    (hM : ∀ i, IsZero ((ModuleCat.extendScalars
      ((affineStructureCommPresheaf B S hS p).map (E.f i).op).hom).obj M)) :
    IsZero M :=
  ModuleCat.isZero_of_isZero_extendScalars_of_faithfullyFlat_pi _
    (faithfullyFlat_pi_map B S hS p _ rfl E hfin hE) M hM

end AffineCategory

/-- **The affine étale charts of a representing algebraic space give jointly faithfully flat
étale coverings of `𝒳_{affine}`.** Every object `x` of `𝒳_{affine}` has a finite covering
family `x_i ⟶ x` of the associated affine étale site lying over an étale covering of affine
schemes, each `x_i` mapping to `j(y_i)` for an affine étale chart `y_i` of `F`, and such that a
module over `𝒪(x)` whose base changes to all the `𝒪(x_i)` vanish is zero. -/
theorem exists_finite_etale_covering_affineEtaleInclusion (hF : IsAlgebraicSpace B S hS F)
    (hp : p.IsFiberedInGroupoids) (x : AffineCategory B S hS p) :
    ∃ E : PreZeroHypercover.{u + 1} x, Finite E.I₀ ∧
      (E.map (AffineCategory.toScheme B S hS p)).presieve₀ ∈
        Scheme.precoverage @Etale ((AffineCategory.toScheme B S hS p).obj x) ∧
      E.sieve₀ ∈
        associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS) x ∧
      (∀ i, ∃ y : AffineEtale B S hS F,
        Nonempty (E.X i ⟶ (affineEtaleInclusion B S hS F p e).obj y)) ∧
      ∀ M : ModuleCat.{t} ((affineStructureCommPresheaf B S hS p).obj (Opposite.op x)),
        (∀ i, IsZero ((ModuleCat.extendScalars
          ((affineStructureCommPresheaf B S hS p).map (E.f i).op).hom).obj M)) → IsZero M := by
  obtain ⟨E, hfin, het, hcov, hle⟩ := AffineCategory.exists_finite_etale_covering B S hS p hp _
    (coversTop_affineEtaleInclusion B S hS F p e hF hp x)
  refine ⟨E, hfin, het, hcov, fun i => hle _ (Sieve.ofArrows_mk _ _ i), fun M hM => ?_⟩
  obtain ⟨hsurj, het'⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp het
  refine AffineCategory.isZero_of_isZero_extendScalars B S hS p E hfin
    ((Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨hsurj, fun i => ?_⟩) M hM
  have := het' i
  infer_instance

end AlgebraicGeometry.Stack
