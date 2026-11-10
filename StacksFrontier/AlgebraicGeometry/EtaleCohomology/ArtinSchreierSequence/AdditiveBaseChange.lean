module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

public import StacksFrontier.Algebra.Category.Grp.DirectSumCoproduct
public import StacksFrontier.Algebra.Category.Grp.DirectSumCoproductUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ChangeOfUniverse
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsBaseChange.Basic
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectImageCohomologyEdge
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.HigherDirectImageAffineVanishing

/-!
# The étale cohomology of `𝐆_a` under extension of the ground field

Let `X` be a quasi-compact and quasi-separated scheme over a field `k` and `k'/k` a field
extension, with `π : X_{k'} = X ×_{Spec k} Spec k' ⟶ X` the projection. Restriction along `π`
on the étale cohomology of the additive group,

  `R : H ^ q (X_étale, 𝐆_a) ⟶ H ^ q ((X_{k'})_étale, 𝐆_a)`,

is injective and its image spans the target over `k'`. This is the flat base change of the
cohomology of the structure sheaf along `k ⟶ k'` ([Stacks, Tag 02KH] part (2)), read on the
étale cohomology of `𝐆_a` through [Stacks, Tag 03P2], and it is the input of
[Stacks, Tag 0A3P] part (2).

## Main definitions

* `Stacks.ArtinSchreier.scalarExtensionLeg`: for `c ∈ k'`, the map `𝐆_{a,X} ⟶ π_* 𝐆_{a,X_{k'}}`,
  `s ↦ c π^* s`.

## Main results

* `Stacks.ArtinSchreier.additiveCohomologyRestriction_scalarExtension`: **restriction on the
  cohomology of `𝐆_a` along `X_{k'} ⟶ X` is injective with `k'`-spanning image**, in every `Ext`
  universe.
* `Stacks.ArtinSchreier.isZero_rightDerived_etaleAbelianDirectImage_additiveSheaf_of_isAffineHom`:
  `𝐆_a` has no higher direct images along an affine morphism.
* `Stacks.ArtinSchreier.etaleCohomologyDirectImageEdge_sheafH_map_additiveDirectImageComparison`:
  the edge map of the direct image, applied after the comparison `𝐆_{a,X} ⟶ π_* 𝐆_{a,Y}`, is
  restriction on the cohomology of `𝐆_a`.
* `Stacks.ArtinSchreier.preservesColimitsOfShape_discrete_sheafSections_smallEtale` and
  `Stacks.ArtinSchreier.bijective_toAddMonoid_sheafH_map_sigmaι`: sections over a quasi-compact
  and quasi-separated object, and étale cohomology of a quasi-compact and quasi-separated
  scheme, commute with direct sums.
* `Stacks.ArtinSchreier.isIso_sigmaDesc_scalarExtensionLeg`: a basis of `k'` over `k`
  identifies `π_* 𝐆_a` with a direct sum of copies of `𝐆_a`.

## Implementation notes

The argument is the étale form of the source's. `π` is affine, so `𝐆_a` has no higher direct
images along it ([Stacks, Tag 03P2] over affine schemes) and the edge map
`H ^ q (X, π_* 𝐆_a) ⟶ H ^ q (X_{k'}, 𝐆_a)` is bijective
(`Stacks.EtaleCohomology.bijective_etaleCohomologyDirectImageEdge`). Over an affine étale
`U ⟶ X` the sections of `π_* 𝐆_a` are `Γ(U, 𝒪) ⊗_k k'`, so a basis `(e_j)` of `k'` over `k`
identifies `π_* 𝐆_a` with the direct sum of copies of `𝐆_a` indexed by the basis, the `j`-th
summand mapping by `s ↦ e_j π^* s`. Étale cohomology of the quasi-compact and quasi-separated `X`
commutes with direct sums ([Stacks, Tag 03Q5]), and through the edge map the `j`-th summand of
`⨁_j H ^ q (X, 𝐆_a)` goes to `H ^ q (X_{k'}, 𝐆_a)` by `x ↦ e_j R(x)`. That map being bijective,
`R` is injective (take `e_j = 1`) and its image spans over `k'`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0A3P](https://stacks.math.columbia.edu/tag/0A3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.EtaleCohomology

universe w w' v u

namespace Stacks.ArtinSchreier

/-! ### No higher direct images along an affine morphism -/

/-- The first projection of a pullback along an affine morphism is affine. -/
private theorem isAffineHom_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] : IsAffineHom (pullback.fst f g) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback f g).flip ‹_›

/-- The category of abelian sheaves on a small étale site has `Ext` in the object universe. -/
private theorem hasExt_sheaf_smallEtale_objectUniverse (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  inferInstance

/-- **`𝐆_a` has no higher direct images along an affine morphism.** For `π : Y ⟶ X` affine and
`n ≥ 1`, `R ^ n π_* 𝐆_{a,Y} = 0` on the small étale site of `X`. Over an affine `V` étale over
`X` the cohomology presheaf of [Stacks, Tag 072W] is `H ^ n ((V ×_X Y)_étale, 𝐆_a)`, which is the
Zariski cohomology `H ^ n (V ×_X Y, 𝒪)` by [Stacks, Tag 03P2], and that vanishes because
`V ×_X Y` is affine ([Stacks, Tag 01XB]). -/
theorem isZero_rightDerived_etaleAbelianDirectImage_additiveSheaf_of_isAffineHom
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π] (n : ℕ) (hn : 1 ≤ n) :
    IsZero (((etaleAbelianDirectImage.{u, 0} π).rightDerived n).obj (additiveSheaf.{u, 0} Y)) := by
  refine SmoothBaseChange.isZero_rightDerived_pushforward_of_affineEtale π n _ fun Z => ?_
  let V := (Scheme.AffineEtale.Spec X).obj Z
  let W := (smallEtaleBaseChange π).obj V
  have : IsAffine V.left := (inferInstance : IsAffine (Spec Z.left.unop))
  have : IsAffine W.left :=
    @isAffine_of_isAffineHom _ _ (pullback.fst V.hom π) (isAffineHom_pullback_fst V.hom π) ‹_›
  have := hasExt_sheaf_smallEtale_objectUniverse W.left
  refine SmoothBaseChange.isZero_rightDerived_sectionsOverObject_of_subsingleton W n _ ?_
  have hH : IsZero (Hgroup W.left.ringCatSheaf ⊤ n (SheafOfModules.unit W.left.ringCatSheaf)) :=
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W.left
    Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen W.left _ ⊤ (isAffineOpen_top _) n
      (by omega)
  exact subsingleton_sheafH_additiveSheaf_of_isZero_hgroup_unconditional.{u + 1, 0} W.left n
    (by omega) hH

/-! ### The edge map and restriction -/

section Edge

variable {X Y : Scheme.{u}} (π : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction on the cohomology of `𝐆_a` through the direct image.** The edge map of the
direct image along `π : Y ⟶ X`, applied after the comparison `𝐆_{a,X} ⟶ π_* 𝐆_{a,Y}` followed by
the direct image of an endomorphism `φ` of `𝐆_{a,Y}`, is restriction on the cohomology of `𝐆_a`
followed by `φ`. -/
theorem etaleCohomologyDirectImageEdge_sheafH_map_additiveDirectImageComparison
    (φ : additiveSheaf.{u, v} Y ⟶ additiveSheaf.{u, v} Y) (q : ℕ)
    (x : Sheaf.H.{w} (additiveSheaf.{u, v} X) q) :
    etaleCohomologyDirectImageEdge.{u, v, w} π (additiveSheaf.{u, v} Y) q
        (Sheaf.H.map (additiveDirectImageComparisonGeneral.{u, v} π ≫
          (etaleAbelianDirectImage.{u, v} π).map φ) q x) =
      Sheaf.H.map φ q (additiveCohomologyRestriction.{u, v, w} π q x) := by
  rw [Sheaf.H.map_comp_apply, etaleCohomologyDirectImageEdge_map]
  congr 1
  calc etaleCohomologyDirectImageEdge.{u, v, w} π (additiveSheaf.{u, v} Y) q
        (Sheaf.H.map (additiveDirectImageComparisonGeneral.{u, v} π) q x)
      = Sheaf.H.map ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).counit.app _) q
          (Sheaf.H.map ((etaleAbelianInverseImage.{u, v} π).map
            (additiveDirectImageComparisonGeneral.{u, v} π)) q
              (etaleCohomologyRestrictionMap.{u, v, w} π _ q x)) :=
        congrArg (Sheaf.H.map ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).counit.app _) q)
          (etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} π
            (additiveDirectImageComparisonGeneral.{u, v} π) q x)
    _ = additiveCohomologyRestriction.{u, v, w} π q x := by
        rw [← Sheaf.H.map_comp_apply]
        change _ = Sheaf.H.map
          (((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).symm
          (additiveDirectImageComparisonGeneral.{u, v} π)) q
            (etaleCohomologyRestrictionMap.{u, v, w} π (additiveSheaf.{u, v} X) q x)
        rw [Adjunction.homEquiv_counit]

end Edge

/-! ### Direct sums -/

section DirectSums

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

open scoped DirectSum

/-- **Sections over a quasi-compact and quasi-separated étale `X`-scheme commute with direct
sums** of abelian sheaves on `X_étale`. A direct sum is the filtered colimit of its finite
sub-sums; sections over such an object commute with filtered colimits (the degree-zero case of
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_smallEtale_of_qcqs`) and
with finite direct sums, being additive. -/
theorem preservesColimitsOfShape_discrete_sheafSections_smallEtale {X : Scheme.{u}}
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] (α : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete α)
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) := by
  let E := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)
  have : E.Additive := Functor.additive_of_preserves_binary_products _
  let : HasCoproducts.{u + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    fun _ => Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology.{u, 0} X _
  let : HasColimitsOfShape (Finset (Discrete α))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology.{u, 0} X _
  have : PreservesColimitsOfShape (Finset (Discrete α)) (E.rightDerived 0) :=
    ⟨fun {K} =>
      have := isIso_colimit_post_rightDerived_sheafSections_smallEtale_of_qcqs.{0} 0 U K
      preservesColimit_of_isIso_post (F := K) (G := E.rightDerived 0)⟩
  have : PreservesColimitsOfShape (Finset (Discrete α)) E :=
    preservesColimitsOfShape_of_natIso E.rightDerivedZeroIsoSelf
  exact CoproductsFromFiltered.preservesColimitsOfShape_discrete E

/-- **Étale cohomology of a quasi-compact and quasi-separated scheme commutes with direct sums,
elementwise**: every class of `H ^ q (X_étale, ∐ F)` is uniquely a finite sum of images of classes
of the summands. This is [Stacks, Tag 03Q5] for the direct sum
(`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale`), read
through the identification of the right derived functors of global sections with
`CategoryTheory.Sheaf.functorH`, with `Ext` in the coefficient universe. -/
theorem bijective_toAddMonoid_sheafH_map_sigmaι {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {α : Type (u + 1)} [DecidableEq α]
    (F : α → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [HasCoproduct F] (q : ℕ) :
    Function.Bijective (DirectSum.toAddMonoid fun a => Sheaf.H.map.{u + 1} (Sigma.ι F a) q) := by
  have : PreservesColimitsOfShape (Discrete α)
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q) :=
    preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale.{0} X q α
  exact AddCommGrpCat.bijective_toAddMonoid_of_isColimit.{u + 1, 0} _
    ((isColimitMapCoconeCofanMkEquiv _ F (Sigma.ι F))
      (IsColimit.mapCoconeEquiv
        (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{0} X.smallEtaleTopology q)
        (isColimitOfPreserves _ (coproductIsCoproduct F))))

end DirectSums

/-! ### A basis gives a direct sum decomposition -/

section Basis

open scoped DirectSum

/-- **A basis gives a direct sum decomposition, through additive identifications.** Let `b` be a
basis of an `S`-module `N`, and `L i : A →+ B` additive maps which, read through additive
bijections `A ≃+ S` and `B ≃+ N`, are `s ↦ s • b i`. Then the induced map `⨁ i, A ⟶ B` is
bijective. -/
theorem bijective_toAddMonoid_of_basis {S N ι : Type*} [CommRing S] [AddCommGroup N]
    [Module S N] [DecidableEq ι] (b : Module.Basis ι S N) {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (eA : A ≃+ S) (eB : B ≃+ N) (L : ι → A →+ B)
    (hL : ∀ i a, eB (L i a) = eA a • b i) :
    Function.Bijective (DirectSum.toAddMonoid L) := by
  let M : (⨁ _ : ι, A) →+ ⨁ _ : ι, S := DirectSum.map fun _ => eA.toAddMonoidHom
  have hM : Function.Bijective M := by
    refine Function.bijective_iff_has_inverse.2
      ⟨DirectSum.map fun _ => eA.symm.toAddMonoidHom, fun d => ?_, fun d => ?_⟩ <;>
    · refine DFinsupp.ext fun i => ?_
      simp [M, DirectSum.map_apply]
  have h : ∀ d, eB (DirectSum.toAddMonoid L d) =
      b.repr.symm ((finsuppLEquivDirectSum S S ι).symm (M d)) := by
    intro d
    induction d using DirectSum.induction_on with
    | zero => simp
    | of i a =>
      rw [DirectSum.toAddMonoid_of, hL]
      simp only [M, DirectSum.map_of, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
      rw [← DirectSum.lof_eq_of S, finsuppLEquivDirectSum_symm_lof, Module.Basis.repr_symm_single]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  have hfun : (DirectSum.toAddMonoid L : (⨁ _ : ι, A) → B) =
      eB.symm ∘ (b.repr.symm ∘ (finsuppLEquivDirectSum S S ι).symm ∘ M) := by
    funext d
    simp only [Function.comp_apply, ← h, AddEquiv.symm_apply_apply]
  rw [hfun]
  exact eB.symm.bijective.comp (b.repr.symm.bijective.comp
    ((finsuppLEquivDirectSum S S ι).symm.bijective.comp hM))

end Basis

/-! ### The direct image of `𝐆_a` along a scalar extension -/

section ScalarExtension

open scoped DirectSum

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **Multiplication by `c ∈ k'` after the comparison**: `𝐆_{a,X} ⟶ π_* 𝐆_{a,X_{k'}}`,
`s ↦ c π^* s`. -/
def scalarExtensionLeg (c : k') :
    additiveSheaf.{u, 0} X ⟶
      (etaleAbelianDirectImage.{u, 0} (scalarExtensionFst k k' f)).obj
        (additiveSheaf.{u, 0} (scalarExtension k k' f)) :=
  additiveDirectImageComparisonGeneral.{u, 0} (scalarExtensionFst k k' f) ≫
    (etaleAbelianDirectImage.{u, 0} (scalarExtensionFst k k' f)).map
      (scalarMap.{u, 0} (scalarExtension k k' f)
        (((Scheme.ΓSpecIso (.of k')).inv ≫
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) c))

/-- `scalarExtensionLeg` on sections. -/
theorem scalarExtensionLeg_app_ofSection (c : k') (U : X.Etale) (a : Γ(U.left, ⊤)) :
    (scalarExtensionLeg k k' f c).hom.app (op U) (ofSection.{u, 0} a) =
      ofSection.{u, 0} (U := (smallEtaleBaseChange (scalarExtensionFst k k' f)).obj U)
        ((pullback.snd U.hom (scalarExtensionFst k k' f)).appTop
            (((Scheme.ΓSpecIso (.of k')).inv ≫
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) c) *
          (pullback.fst U.hom (scalarExtensionFst k k' f)).appTop a) :=
  rfl

/-- **Over an affine étale `X`-scheme `U`, a basis of `k'` over `k` decomposes the sections of
`π_* 𝐆_a` as a direct sum.** The sections over `U` are `Γ(U ×_X X_{k'}, 𝒪) = Γ(U, 𝒪) ⊗_k k'`
(degree-zero flat base change,
`Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.isPushout_appTop`),
so for a basis `(e_j)` of `k'` over `k` the elements `1 ⊗ e_j` form a basis over `Γ(U, 𝒪)`, and
the legs `s ↦ e_j π^* s` exhibit the sections as `⨁_j Γ(U, 𝒪)`. -/
theorem bijective_toAddMonoid_scalarExtensionLeg_app {ι : Type*} [DecidableEq ι]
    (e : Module.Basis ι k k') (U : X.Etale) [IsAffine U.left] :
    Function.Bijective (DirectSum.toAddMonoid fun j =>
      ((scalarExtensionLeg k k' f (e j)).hom.app (op U)).hom) := by
  let φ := CommRingCat.ofHom (algebraMap k k')
  let p := pullback.fst U.hom (scalarExtensionFst k k' f)
  let iY := pullback.snd U.hom (scalarExtensionFst k k' f) ≫
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have hpb : IsPullback p iY (U.hom ≫ f) (Spec.map φ) :=
    (IsPullback.of_hasPullback U.hom (scalarExtensionFst k k' f)).paste_vert
      (IsPullback.of_hasPullback f (Spec.map φ))
  have hflat : φ.hom.Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  have : CompactSpace ((𝟭 Scheme).obj U.left) := inferInstanceAs (CompactSpace U.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (QuasiSeparatedSpace U.left)
  have hP := Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.isPushout_appTop hpb hflat
  have hP' : IsPushout ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.hom ≫ f).appTop) φ p.appTop
      ((Scheme.ΓSpecIso (.of k')).inv ≫ iY.appTop) :=
    hP.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of k')) (Iso.refl _)
      (by simp) (Scheme.ΓSpecIso_naturality φ) (by simp) (by simp)
  let S := Γ(U.left, ⊤)
  let S' := Γ(pullback U.hom (scalarExtensionFst k k' f), ⊤)
  let : Algebra k S := ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.hom ≫ f).appTop).hom.toAlgebra
  let : Algebra S S' := p.appTop.hom.toAlgebra
  let : Algebra k' S' := ((Scheme.ΓSpecIso (.of k')).inv ≫ iY.appTop).hom.toAlgebra
  let : Algebra k S' := (p.appTop.hom.comp
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.hom ≫ f).appTop).hom).toAlgebra
  have : IsScalarTower k S S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k k' S' := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom hP'.w)
  have hpush : Algebra.IsPushout k k' S S' := CommRingCat.isPushout_iff_isPushout.1 hP'.flip
  have ibc := (hpush.symm).out
  let b' := ibc.basis e
  refine bijective_toAddMonoid_of_basis b' AddEquiv.ulift AddEquiv.ulift _ fun j a => ?_
  obtain ⟨a, rfl⟩ := ofSection_surjective.{u, 0} (X := X) (U := U) a
  change (_ * _ : S') = (a : S) • b' j
  rw [IsBaseChange.basis_apply, Algebra.smul_def, mul_comm]
  rfl

/-- **The direct sum of copies of `𝐆_{a,X}` indexed by a basis of `k'` over `k` is `π_* 𝐆_a`.**
For a basis `(e_j)` of `k'` over `k`, the map `⨁_j 𝐆_{a,X} ⟶ π_* 𝐆_{a,X_{k'}}` whose `j`-th
component is `s ↦ e_j π^* s` is an isomorphism of sheaves on `X_étale`. Affine étale `X`-schemes
are dense in the small étale site, and over each of them the map is bijective on sections:
sections over an affine object commute with direct sums
(`preservesColimitsOfShape_discrete_sheafSections_smallEtale`), and the sections of the target
are the direct sum by `bijective_toAddMonoid_scalarExtensionLeg_app`. -/
theorem isIso_sigmaDesc_scalarExtensionLeg {J : Type (u + 1)}
    (e : Module.Basis J k k') [HasCoproduct fun _ : J => additiveSheaf.{u, 0} X] :
    IsIso (Sigma.desc fun j => scalarExtensionLeg k k' f (e j)) := by
  classical
  set Sg := Sigma.desc fun j => scalarExtensionLeg k k' f (e j)
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := Scheme.AffineEtale.Spec X)
    (K := X.smallEtaleTopology) Sg ?_
  have hZ : ∀ Z : (Scheme.AffineEtale X)ᵒᵖ,
      IsIso ((Functor.whiskerLeft (Scheme.AffineEtale.Spec X).op Sg.hom).app Z) := by
    intro Z
    let U := (Scheme.AffineEtale.Spec X).obj Z.unop
    have : IsAffine U.left := (inferInstance : IsAffine (Spec Z.unop.left.unop))
    have := preservesColimitsOfShape_discrete_sheafSections_smallEtale U J
    have hσ := AddCommGrpCat.bijective_toAddMonoid_of_isColimit.{u + 1, 0} _
      (isColimitOfHasCoproductOfPreservesColimit
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U))
        (fun _ : J => additiveSheaf.{u, 0} X))
    have hσ' : Function.Bijective (DirectSum.toAddMonoid (fun j =>
        (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)).map
          (Sigma.ι (fun _ : J => additiveSheaf.{u, 0} X) j)).hom)) := hσ
    have hφ := bijective_toAddMonoid_scalarExtensionLeg_app k k' f e U
    have hcomp : ∀ d, (Sg.hom.app (op U)) (DirectSum.toAddMonoid (fun j =>
        (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)).map
          (Sigma.ι (fun _ : J => additiveSheaf.{u, 0} X) j)).hom) d) =
        DirectSum.toAddMonoid (fun j =>
          ((scalarExtensionLeg k k' f (e j)).hom.app (op U)).hom) d := by
      intro d
      induction d using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | of j x =>
        rw [DirectSum.toAddMonoid_of]
        have h := congrArg (fun m => m.hom.app (op U))
          (Sigma.ι_comp_desc (fun j => scalarExtensionLeg k k' f (e j)) j)
        simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
        exact (ConcreteCategory.congr_hom h x).trans (DirectSum.toAddMonoid_of
          (fun j => ((scalarExtensionLeg k k' f (e j)).hom.app (op U)).hom) j x).symm
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    change IsIso (Sg.hom.app (op U))
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun y => ?_⟩
    · obtain ⟨a, rfl⟩ := hσ'.2 a
      obtain ⟨b, rfl⟩ := hσ'.2 b
      rw [hcomp, hcomp] at hab
      rw [hφ.1 hab]
    · obtain ⟨d, rfl⟩ := hφ.2 y
      exact ⟨_, hcomp d⟩
  exact NatIso.isIso_of_isIso_app _

/-- Multiplication by `1` on `𝐆_a` is the identity. -/
theorem scalarMap_one (Y : Scheme.{u}) : scalarMap.{u, 0} Y 1 = 𝟙 _ := by
  ext U x
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, 0} x
  rw [scalarMap_app_ofSection, map_one, one_mul]
  rfl

/-- **Restriction on the cohomology of `𝐆_a` along a scalar extension is injective with spanning
image, with `Ext` in the coefficient universe.** This is the case of
`additiveCohomologyRestriction_scalarExtension` in which `Ext` is computed in `Type (u + 1)`; see
there. -/
theorem additiveCohomologyRestriction_scalarExtension_coefficientUniverse
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) :
    Function.Injective
        (additiveCohomologyRestriction.{u, 0, u + 1} (scalarExtensionFst k k' f) q) ∧
      ∀ y : Sheaf.H.{u + 1} (additiveSheaf.{u, 0} (scalarExtension k k' f)) q,
        y ∈ AddSubgroup.closure (Set.range fun cz :
          k' × Sheaf.H.{u + 1} (additiveSheaf.{u, 0} X) q =>
          Sheaf.H.map (scalarMap.{u, 0} (scalarExtension k k' f)
            (((Scheme.ΓSpecIso (.of k')).inv ≫
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) cz.1)) q
            (additiveCohomologyRestriction.{u, 0, u + 1} (scalarExtensionFst k k' f) q cz.2)) := by
  classical
  set π := scalarExtensionFst k k' f
  have hs : LinearIndepOn k id ({1} : Set k') := (linearIndepOn_singleton_iff k).2 one_ne_zero
  let J := ULift.{u + 1} (hs.extend (Set.subset_univ _))
  let e : Module.Basis J k k' := (Module.Basis.extend hs).reindex Equiv.ulift.symm
  let j₀ : J := ⟨⟨1, Module.Basis.subset_extend hs (Set.mem_singleton 1)⟩⟩
  have he₀ : e j₀ = 1 := by
    simp only [e, Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.extend_apply_self]
    rfl
  have : HasCoproduct fun _ : J => additiveSheaf.{u, 0} X :=
    Scheme.hasColimit_sheaf_smallEtaleTopology.{u, 0} X _
  let Sg := Sigma.desc fun j => scalarExtensionLeg k k' f (e j)
  have hSg : IsIso Sg := isIso_sigmaDesc_scalarExtensionLeg k k' f e
  have : IsAffineHom π := isAffineHom_pullback_fst _ _
  have hedge := bijective_etaleCohomologyDirectImageEdge.{u, 0, u + 1} π q
    (additiveSheaf.{u, 0} (scalarExtension k k' f))
    (fun n hn => isZero_rightDerived_etaleAbelianDirectImage_additiveSheaf_of_isAffineHom π n hn)
  have hHSg : Function.Bijective (Sheaf.H.map.{u + 1} Sg q) := by
    refine Function.bijective_iff_has_inverse.2 ⟨Sheaf.H.map.{u + 1} (inv Sg) q, fun x => ?_,
      fun x => ?_⟩
    · rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]
    · rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply]
  let T := DirectSum.toAddMonoid fun j => Sheaf.H.map.{u + 1}
    (Sigma.ι (fun _ : J => additiveSheaf.{u, 0} X) j) q
  let Θ := fun d => etaleCohomologyDirectImageEdge.{u, 0, u + 1} π _ q (Sheaf.H.map Sg q (T d))
  have hΘ : Function.Bijective Θ := hedge.comp (hHSg.comp
    (bijective_toAddMonoid_sheafH_map_sigmaι (fun _ : J => additiveSheaf.{u, 0} X) q))
  have hΘof : ∀ j x, Θ (DirectSum.of _ j x) =
      Sheaf.H.map (scalarMap.{u, 0} (scalarExtension k k' f)
        (((Scheme.ΓSpecIso (.of k')).inv ≫
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) (e j))) q
        (additiveCohomologyRestriction.{u, 0, u + 1} π q x) := by
    intro j x
    simp only [Θ, T]
    rw [DirectSum.toAddMonoid_of, ← Sheaf.H.map_comp_apply, Sigma.ι_comp_desc]
    exact etaleCohomologyDirectImageEdge_sheafH_map_additiveDirectImageComparison π _ q x
  have hΘadd : ∀ a b, Θ (a + b) = Θ a + Θ b := fun a b => by
    simp only [Θ, map_add]
  have hΘzero : Θ 0 = 0 := by simp only [Θ, map_zero]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · have h1 : additiveCohomologyRestriction.{u, 0, u + 1} π q x = Θ (DirectSum.of _ j₀ x) := by
      rw [hΘof, he₀, map_one, scalarMap_one, Sheaf.H.map_id_apply]
    rw [h1, ← hΘzero] at hx
    exact DirectSum.of_injective j₀ ((hΘ.1 hx).trans (map_zero _).symm)
  · obtain ⟨d, rfl⟩ := hΘ.2 y
    induction d using DirectSum.induction_on with
    | zero =>
      rw [hΘzero]
      exact zero_mem _
    | of j x =>
      rw [hΘof]
      exact AddSubgroup.subset_closure ⟨(e j, x), rfl⟩
    | add a b ha hb =>
      rw [hΘadd]
      exact add_mem ha hb

section ChangeOfUniverse

variable {Y : Scheme.{u}} (π : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w'} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The change of `Ext` universe commutes with the maps a morphism of sheaves induces on
cohomology. -/
theorem chgUniv_sheafH_map {Z : Scheme.{u}}
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w'} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}} (g : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    Ext.chgUniv.{w'} (Sheaf.H.map.{w} g q x) = Sheaf.H.map.{w'} g q (Ext.chgUniv.{w'} x) := by
  change Ext.chgUniv (x.comp (Ext.mk₀ g) (add_zero q)) =
    (Ext.chgUniv x).comp (Ext.mk₀ g) (add_zero q)
  rw [Ext.chgUniv_comp, Ext.chgUniv_mk₀]

/-- The change of `Ext` universe commutes with restriction on the cohomology of `𝐆_a`. -/
theorem chgUniv_additiveCohomologyRestriction (q : ℕ) (x : Sheaf.H.{w} (additiveSheaf.{u, 0} X) q) :
    Ext.chgUniv.{w'} (additiveCohomologyRestriction.{u, 0, w} π q x) =
      additiveCohomologyRestriction.{u, 0, w'} π q (Ext.chgUniv.{w'} x) := by
  simp only [additiveCohomologyRestriction, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [chgUniv_sheafH_map, etaleCohomologyRestrictionMap_apply, etaleCohomologyRestrictionMap_apply,
    Ext.chgUniv_comp, Ext.chgUniv_mk₀]
  exact congrArg (fun z => Sheaf.H.map.{w'} (additiveInverseImageComparisonGeneral.{u, 0} π) q
    ((Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} π).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv).comp z (zero_add q)))
    (Ext.chgUniv_mapExactFunctor.{w, w', w, w'} (etaleAbelianInverseImage.{u, 0} π) x)

end ChangeOfUniverse

/-- **Restriction on the cohomology of `𝐆_a` along a scalar extension is injective, and its image
spans the target over `k'`** ([Stacks, Tag 02KH] part (2) along `k ⟶ k'`, read on étale cohomology
through [Stacks, Tag 03P2]). For `X` quasi-compact and quasi-separated over `k` and a field
extension `k'/k`, restriction `H ^ q (X_étale, 𝐆_a) ⟶ H ^ q ((X_{k'})_étale, 𝐆_a)` along the
projection `X_{k'} ⟶ X` is injective, and every class upstairs is a sum of classes `c R(z)`,
`c ∈ k'` acting through multiplication by its image in `Γ(X_{k'}, 𝒪)`.

With `Ext` in the coefficient universe this is
`additiveCohomologyRestriction_scalarExtension_coefficientUniverse`; the change of `Ext`
universe is an additive bijection commuting with restriction and with the maps induced by
morphisms of sheaves, so the statement holds in every `Ext` universe. -/
theorem additiveCohomologyRestriction_scalarExtension [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) :
    Function.Injective
        (additiveCohomologyRestriction.{u, 0, w} (scalarExtensionFst k k' f) q) ∧
      ∀ y : Sheaf.H.{w} (additiveSheaf.{u, 0} (scalarExtension k k' f)) q,
        y ∈ AddSubgroup.closure (Set.range fun cz : k' × Sheaf.H.{w} (additiveSheaf.{u, 0} X) q =>
          Sheaf.H.map (scalarMap.{u, 0} (scalarExtension k k' f)
            (((Scheme.ΓSpecIso (.of k')).inv ≫
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) cz.1)) q
            (additiveCohomologyRestriction.{u, 0, w} (scalarExtensionFst k k' f) q cz.2)) := by
  have := hasExt_sheaf_smallEtale_objectUniverse X
  have := hasExt_sheaf_smallEtale_objectUniverse (scalarExtension k k' f)
  obtain ⟨hinj, hspan⟩ :=
    additiveCohomologyRestriction_scalarExtension_coefficientUniverse k k' f q
  set π := scalarExtensionFst k k' f
  let EX : Sheaf.H.{w} (additiveSheaf.{u, 0} X) q ≃+ Sheaf.H.{u + 1} (additiveSheaf.{u, 0} X) q :=
    Ext.chgUnivAddEquiv
  let EY : Sheaf.H.{w} (additiveSheaf.{u, 0} (scalarExtension k k' f)) q ≃+
      Sheaf.H.{u + 1} (additiveSheaf.{u, 0} (scalarExtension k k' f)) q := Ext.chgUnivAddEquiv
  have hR : ∀ x, EY (additiveCohomologyRestriction.{u, 0, w} π q x) =
      additiveCohomologyRestriction.{u, 0, u + 1} π q (EX x) :=
    chgUniv_additiveCohomologyRestriction.{w, u + 1, u} π q
  refine ⟨fun a b hab => EX.injective (hinj ?_), fun y => ?_⟩
  · rw [← hR, ← hR, hab]
  · have hy := hspan (EY y)
    have key : ∀ z : Sheaf.H.{u + 1} (additiveSheaf.{u, 0} (scalarExtension k k' f)) q,
        z ∈ AddSubgroup.closure (Set.range fun cz :
        k' × Sheaf.H.{u + 1} (additiveSheaf.{u, 0} X) q =>
          Sheaf.H.map.{u + 1} (scalarMap.{u, 0} (scalarExtension k k' f)
            (((Scheme.ΓSpecIso (.of k')).inv ≫
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) cz.1)) q
            (additiveCohomologyRestriction.{u, 0, u + 1} π q cz.2)) →
        EY.symm z ∈ AddSubgroup.closure (Set.range fun cz :
          k' × Sheaf.H.{w} (additiveSheaf.{u, 0} X) q =>
            Sheaf.H.map.{w} (scalarMap.{u, 0} (scalarExtension k k' f)
              (((Scheme.ΓSpecIso (.of k')).inv ≫
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop) cz.1)) q
              (additiveCohomologyRestriction.{u, 0, w} π q cz.2)) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨⟨c, x⟩, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨(c, EX.symm x), EY.injective ?_⟩
        simp only [AddEquiv.apply_symm_apply]
        change Ext.chgUniv.{u + 1} (Sheaf.H.map.{w} _ q _) = _
        rw [chgUniv_sheafH_map]
        exact congrArg _ ((hR _).trans (congrArg _ (EX.apply_symm_apply x)))
      | zero => rw [map_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
    simpa only [AddEquiv.symm_apply_apply] using key _ hy

end ScalarExtension

end Stacks.ArtinSchreier

end
