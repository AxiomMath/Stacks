module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Representability by algebraic spaces descends along an étale covering of the source

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Condition (5) of **Stacks 0AN4** asks for a covering
`{Xᵢ ⟶ X}` as in Definition 0AIM together with factorizations `Xᵢ ⟶ Yᵢ ⟶ Y` through affine
formal algebraic spaces `Yᵢ`, with `Yᵢ ⟶ Y` and `Xᵢ ⟶ Yᵢ` representable by algebraic spaces.
This file proves that it implies condition (1), that `f` is representable by algebraic spaces.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRepresentableAfterSourceCover`: condition (5) of
  **Stacks 0AN4**.

## Main results

* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_of_etaleFamily`: an fppf sheaf receiving a
  surjection from an object of the site and a jointly surjective family of étale charts out of
  objects of the site is an algebraic space.
* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_etaleCover_comp`:
  representability by algebraic spaces descends along a jointly surjective family of
  representable étale morphisms into the source, as soon as the source satisfies the
  set-theoretic condition of Stacks 0AIS and the target is a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isRepresentable_of_isRepresentableAfterSourceCover`:
  **Stacks 0AN4**, condition (5) implies condition (1).

## Implementation notes

The source passes through condition (2), setting `U = ∐ Xᵢ` and `V = ∐ Yᵢ`, and closes with
Stacks 0AMP applied to `U ⟶ X ⟶ Y`. Neither step is available as stated here: the covering is
indexed by a type of `Type (u + 1)`, and a coproduct of that many algebraic spaces is not an
algebraic space over the chosen site, its atlas being too large for the site's cutoff; and
Stacks 0AMP is equivalent to the bootstrap theorem Stacks 04S6, part (3). The argument here
uses that the covering is étale, which the source's does not need, and works one scheme-valued
point `ξ : T ⟶ Y` at a time. The base change `F = T ×_Y X` is covered by the algebraic spaces
`T ×_Y Xᵢ`, each a base change of `Xᵢ ⟶ Yᵢ` along the algebraic space `T ×_Y Yᵢ`, hence by the
schemes of their atlases. The size problem is settled by the set-theoretic condition of `X`:
an object `V₀` of the site surjecting onto `X` gives the object `T ×_Y V₀` of the site, which is
representable because the diagonal of `Y` is (Stacks 0AIP), surjecting onto `F`; that bounds
every affine étale chart of `F` and leaves one chart for each of its points, exactly as in
Stacks 0AIS, observation (2). The resulting chart of `F` is representable by objects of the
site, so Stacks 0BGR concludes.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AMP](https://stacks.math.columbia.edu/tag/0AMP)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of an affine open of an object `T` of the site is an open immersion of schemes. -/
private theorem isOpenImmersion_map_openSubobjectHom (T : BigFppfOver B S hS)
    (a : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (Space.openSubobjectHom B S hS T a.1.ι inferInstance)) := by
  rw [Space.toScheme_map_openSubobjectHom]
  exact (inferInstance : AlgebraicGeometry.IsOpenImmersion a.1.ι)

/-- The affine opens of an object `T` of the site, pulled back along `z : W ⟶ T`, cover `W`. -/
theorem ofArrows_pullback_affineOpens_mem {W T : BigFppfOver B S hS} (z : W ⟶ T) :
    Sieve.ofArrows
      (fun a : ((BigFppfOver.toScheme B S hS).obj T).affineOpens ↦
        pullback (Space.openSubobjectHom B S hS T a.1.ι inferInstance) z)
      (fun a ↦ pullback.snd (Space.openSubobjectHom B S hS T a.1.ι inferInstance) z) ∈
      BigFppfOver.topology B S hS W := by
  let A := BigFppfOver.toScheme B S hS
  let k (a : (A.obj T).affineOpens) := Space.openSubobjectHom B S hS T a.1.ι inferInstance
  have hk (a : (A.obj T).affineOpens) : A.map (k a) = a.1.ι :=
    Space.toScheme_map_openSubobjectHom B S hS T a.1.ι _
  have hr (a : (A.obj T).affineOpens) : AlgebraicGeometry.IsOpenImmersion
      (pullback.snd (k a) z).left.hom :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback (k a) z).map A)
      (isOpenImmersion_map_openSubobjectHom B S hS T a)
  refine fppf_ofArrows_mem B S hS _ _ (fun a ↦ by have := hr a; infer_instance)
    (fun a ↦ by have := hr a; infer_instance) fun w ↦ ?_
  obtain ⟨a, ha, hwa, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := A.obj T) (x := A.map z w) (U := ⊤) trivial
  let a' : (A.obj T).affineOpens := ⟨a, ha⟩
  have hp : A.map (k a') ⟨A.map z w, hwa⟩ = A.map z w := by
    rw [hk a']
    rfl
  obtain ⟨y, -, hy⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := A.map (k a')) (g := A.map z) ⟨A.map z w, hwa⟩ w hp
  refine ⟨a', ((IsPullback.of_hasPullback _ z).map A).isoPullback.inv y, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  exact (congrArg (fun φ ↦ φ y)
    ((IsPullback.of_hasPullback (k a') z).map A).isoPullback_inv_snd).trans hy

/-- **An fppf sheaf receiving a surjection from an object of the site and a jointly surjective
family of étale charts out of objects of the site is an algebraic space.** This is
`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_of_affineEtaleFamily` with the members of
the family no longer required to be affine: each member is replaced by the family of its affine
opens, which is a Zariski covering of it, so the refined family still covers the section `t'`
of `X`. -/
theorem isAlgebraicSpaceULift_of_etaleFamily
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (t' : uliftYoneda.{u + 1}.obj U ⟶ X.obj)
    (ht' : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) t')
    {I : Type (u + 1)} (Ui : I → AlgebraicGeometry.BigFppfOver B S hS)
    (gi : ∀ i, uliftYoneda.{u + 1}.obj (Ui i) ⟶ X.obj)
    (hgi : ∀ i, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (gi i))
    (hcov : (⨆ i, Presheaf.imageSieve (gi i) (uliftYonedaEquiv t')) ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS U) :
    AlgebraicGeometry.Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let Yo := uliftYoneda.{u + 1} (C := C)
  let A := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let K := Σ i, (A.obj (Ui i)).affineOpens
  let V : K → C := fun p =>
    AlgebraicGeometry.Space.openSubobject B S hS (Ui p.1) p.2.1.ι inferInstance
  let k : ∀ p : K, V p ⟶ Ui p.1 := fun p =>
    AlgebraicGeometry.Space.openSubobjectHom B S hS (Ui p.1) p.2.1.ι inferInstance
  have hgk (p : K) : (AlgebraicGeometry.Space.etaleOnSite B S hS).relative Yo
      (Yo.map (k p) ≫ gi p.1) := by
    have := isOpenImmersion_map_openSubobjectHom B S hS (Ui p.1) p.2
    exact MorphismProperty.comp_mem _ _ _
      (AlgebraicGeometry.Space.relative_uliftYoneda_map B S hS _ (k p) inferInstance) (hgi p.1)
  refine isAlgebraicSpaceULift_of_affineEtaleFamily B S hS X U t' ht' V
    (fun p => p.2.2) (fun p => Yo.map (k p) ≫ gi p.1) hgk ?_
  refine J.transitive hcov _ fun W g hg ↦ ?_
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hg
  obtain ⟨_, ⟨i, rfl⟩, z, hz⟩ := hg
  let zz : W ⟶ Ui i := z.down
  refine J.superset_covering ?_ (ofArrows_pullback_affineOpens_mem B S hS zz)
  rintro W' gg ⟨Z, h, g', ⟨a⟩, rfl⟩
  refine Sieve.downward_closed _ ?_ h
  refine (le_iSup (fun p : K =>
    Presheaf.imageSieve (Yo.map (k p) ≫ gi p.1) (uliftYonedaEquiv t')) ⟨i, a⟩) _
    (?_ : Presheaf.imageSieve (Yo.map (k ⟨i, a⟩) ≫ gi i) (uliftYonedaEquiv t')
      (pullback.snd (k ⟨i, a⟩) zz ≫ g))
  refine ⟨ULift.up (pullback.fst (k ⟨i, a⟩) zz), ?_⟩
  change (gi i).app (op (Limits.pullback (k ⟨i, a⟩) zz))
    (ULift.up (pullback.fst (k ⟨i, a⟩) zz ≫ k ⟨i, a⟩)) = _
  rw [pullback.condition, op_comp, Functor.map_comp, types_comp_apply, ← hz]
  exact NatTrans.naturality_apply (gi i) (pullback.snd (k ⟨i, a⟩) zz).op z

/-- **The atlas of an étale base change is a relatively étale chart.** Let `a : U ⟶ X` be
representable by algebraic spaces and étale, with `a ≫ f` representable by algebraic spaces, and
let `ξ : T ⟶ Y` be a scheme-valued point. Then the base change `(T ×_Y X) ×_X U` is an algebraic
space, and an atlas of it, composed with the projection to `T ×_Y X`, is relatively étale. -/
theorem exists_atlas_relative_etale_pullback_fst {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {T : BigFppfOver B S hS} (ξ : uliftYoneda.{u + 1}.obj T ⟶ Y.obj) {U : FppfSheaf B S hS}
    (a : U ⟶ X) (ha : IsRepresentableEtale B S hS a)
    (hc : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ (a ≫ f).hom)) :
    ∃ (Z : BigFppfOver B S hS)
      (q : uliftYoneda.{u + 1}.obj Z ⟶ pullback (pullback.snd ξ f.hom) a.hom),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} q ∧
      (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} (q ≫ pullback.fst _ _) := by
  let PE := Space.etaleOnSite B S hS
  have : (PE.relative uliftYoneda.{u + 1}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange PE
  have : (PE.relative uliftYoneda.{u + 1}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition PE
  have hsq : IsPullback (pullback.snd (pullback.snd ξ f.hom) a.hom) (pullback.fst _ _)
      a.hom (pullback.snd ξ f.hom) :=
    (IsPullback.of_hasPullback _ _).flip
  have hπrep := Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hsq ha.1
  obtain ⟨Z, q, hqS, hqE⟩ := (Space.isAlgebraicSpaceULift_of_iso B S hS
    (pullbackLeftPullbackSndIso ξ f.hom a.hom).symm hc).exists_atlas
  exact ⟨Z, q, hqS, hqE, relative_etale_of_isEtale_of_schemeSource B S hS Z _
    (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (Space.isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable q hqE.rep) hπrep)
    (isEtaleULift_pullback_fst_comp B S hS hπrep
      (isEtaleULift_pullback_fst_of_isPullback B S hS hsq ha.2) fun W ζ V φ hφ ↦
        MorphismProperty.comp_mem _ _ _ hφ
          (MorphismProperty.of_isPullback (IsPullback.of_hasPullback ζ q).flip hqE))⟩

/-- **Surjective atlases of the base changes of a covering cover the base change.** Let
`{aᵢ : Uᵢ ⟶ X}` be jointly surjective, `ξ : T ⟶ Y` a scheme-valued point and `tF` a section of
`T ×_Y X` over `M`. If each `qᵢ` is a surjective étale chart of `(T ×_Y X) ×_X Uᵢ`, the images
of the composites `qᵢ ≫ pr₁` cover the section `tF`. -/
theorem iSup_imageSieve_atlas_pullback_fst_mem {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {T : BigFppfOver B S hS} (ξ : uliftYoneda.{u + 1}.obj T ⟶ Y.obj)
    {I : Type (u + 1)} (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc a))
    {M : BigFppfOver B S hS} (tF : uliftYoneda.{u + 1}.obj M ⟶ pullback ξ f.hom)
    {Z : I → BigFppfOver B S hS}
    (q : ∀ i, uliftYoneda.{u + 1}.obj (Z i) ⟶ pullback (pullback.snd ξ f.hom) (a i).hom)
    (hqS : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (q i))
    (hqE : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (q i)) :
    (⨆ i, Presheaf.imageSieve (q i ≫ pullback.fst _ _) (uliftYonedaEquiv tF)) ∈
      BigFppfOver.topology B S hS M := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let Yo := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let π (i : I) : pullback (pullback.snd ξ f.hom) (a i).hom ⟶ pullback ξ f.hom :=
    pullback.fst _ _
  refine J.transitive (family_imageSieve_mem J U X a hsurj M
    ((pullback.snd ξ f.hom).app _ (uliftYonedaEquiv tF))) _ fun W g hg ↦ ?_
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hg
  obtain ⟨_, ⟨i, rfl⟩, z, hz⟩ := hg
  let σ : Yo.obj W ⟶ pullback ξ f.hom :=
    uliftYonedaEquiv.symm ((pullback ξ f.hom).map g.op (uliftYonedaEquiv tF))
  let τ : Yo.obj W ⟶ (U i).obj := uliftYonedaEquiv.symm z
  have hw : σ ≫ pullback.snd ξ f.hom = τ ≫ (a i).hom := by
    apply uliftYonedaEquiv.injective
    simpa [uliftYonedaEquiv_comp, σ, τ] using
      (hz.trans (NatTrans.naturality_apply (pullback.snd ξ f.hom) g.op
        (uliftYonedaEquiv tF)).symm).symm
  let l : Yo.obj W ⟶ pullback (pullback.snd ξ f.hom) (a i).hom := pullback.lift σ τ hw
  refine J.superset_covering ?_ ((isLocallySurjective_of_surjective_etale_uliftYoneda B S hS
    (q i) (hqS i) (hqE i)).imageSieve_mem (uliftYonedaEquiv l))
  rintro W' h ⟨y, hy⟩
  refine (le_iSup (fun i ↦ Presheaf.imageSieve (q i ≫ π i) (uliftYonedaEquiv tF)) i) _
    (?_ : Presheaf.imageSieve (q i ≫ π i) (uliftYonedaEquiv tF) (h ≫ g))
  refine ⟨y, ?_⟩
  have hl : (π i).app _ (uliftYonedaEquiv l) =
      (pullback ξ f.hom).map g.op (uliftYonedaEquiv tF) := by
    rw [← uliftYonedaEquiv_comp, pullback.lift_fst]
    exact Equiv.apply_symm_apply _ _
  simp only [NatTrans.comp_app, types_comp_apply, op_comp, Functor.map_comp]
  rw [hy, NatTrans.naturality_apply, hl]

/-- **Representability by algebraic spaces descends along an étale covering of the source.**
Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S`, with `X` satisfying
the set-theoretic condition of Stacks 0AIS and `Y` a formal algebraic space, and let
`{aᵢ : Uᵢ ⟶ X}` be a jointly surjective family of morphisms representable by algebraic spaces
and étale. If every composite `aᵢ ≫ f` is representable by algebraic spaces, so is `f`.

At a scheme-valued point `ξ : T ⟶ Y` the base change `F = T ×_Y X` is covered étale-ly by the
algebraic spaces `T ×_Y Uᵢ`, and so by the schemes of their atlases; it receives a surjection
from the object `T ×_Y V₀` of the site, `V₀ ⟶ X` being the surjection of the set-theoretic
condition and `T ×_Y V₀` being representable because the diagonal of `Y` is (Stacks 0AIP).
`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_of_etaleFamily` then makes `F` an algebraic
space. -/
theorem isRepresentableByAlgebraicSpacesULift_of_etaleCover_comp
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : SatisfiesSetTheoreticCondition B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    {I : Type (u + 1)} (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
    (ha : ∀ i, IsRepresentableEtale B S hS (a i))
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc a))
    (hc : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (a i ≫ f).hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  classical
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let Yo := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  intro T ξ
  let Fs : FppfSheaf B S hS := ⟨pullback ξ f.hom, Presheaf.isSheaf_pullback _ ξ f.hom
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T).isSheaf X.property Y.property⟩
  obtain ⟨V₀, R, hV, hR, ⟨eV⟩, -, t, ht, -⟩ := hX
  let tX : Yo.obj V₀ ⟶ X.obj := eV.inv ≫ t.hom
  have htX : Presheaf.IsLocallySurjective J tX := by
    have : Sheaf.IsLocallySurjective t := (Sheaf.isLocallySurjective_iff_epi t).mpr ht
    dsimp only [tX]
    infer_instance
  obtain ⟨M, ⟨eM⟩⟩ := essImage_pullback_of_isFormalAlgebraicSpace B S hS hY T V₀ ξ (tX ≫ f.hom)
  let eM' : Yo.obj M ≅ pullback (pullback.snd ξ f.hom) tX :=
    eM ≪≫ (pullbackLeftPullbackSndIso ξ f.hom tX).symm
  let tF : Yo.obj M ⟶ Fs.obj := eM'.hom ≫ pullback.fst (pullback.snd ξ f.hom) tX
  have htF : Presheaf.IsLocallySurjective J tF := by
    have := Presheaf.isLocallySurjective_pullback_fst J (pullback.snd ξ f.hom) tX
    dsimp only [tF]
    infer_instance
  choose Z q hqS hqE hgi using fun i ↦
    exists_atlas_relative_etale_pullback_fst B S hS f ξ (a i) (ha i) (hc i T ξ)
  exact isAlgebraicSpaceULift_of_etaleFamily B S hS Fs M tF htF Z _ hgi
    (iSup_imageSieve_atlas_pullback_fst_mem B S hS f ξ U a hsurj tF q hqS hqE)

/-- **Stacks 0AN4, condition (5).** There is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and,
for each `i`, a factorization `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space `Vᵢ` with
`Vᵢ ⟶ Y` and `Uᵢ ⟶ Vᵢ` representable by algebraic spaces. -/
abbrev IsRepresentableAfterSourceCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U a ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (b : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧
          Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS b.hom ∧
          Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ∧
          a i ≫ f = t ≫ b

/-- **Stacks 0AN4, condition (5) implies condition (1).** Let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S` admitting a covering `{Uᵢ ⟶ X}` as in Definition 0AIM whose members
factor through affine formal algebraic spaces `Vᵢ` with `Vᵢ ⟶ Y` and `Uᵢ ⟶ Vᵢ` representable by
algebraic spaces. Then `f` is representable by algebraic spaces.

Each composite `Uᵢ ⟶ X ⟶ Y` equals `Uᵢ ⟶ Vᵢ ⟶ Y`, which is representable by algebraic spaces by
Stacks 0APY, and representability descends along the étale covering by
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_etaleCover_comp`. Of the
hypothesis that `X` is a formal algebraic space only the set-theoretic condition of Stacks 0AIS
is used, and affineness of the `Vᵢ` is not used. -/
@[stacks 0AN4 "condition (5) implies condition (1)"]
theorem isRepresentable_of_isRepresentableAfterSourceCover {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsRepresentableAfterSourceCover B S hS f) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  obtain ⟨I, U, a, ⟨-, ha, hsurj⟩, hfac⟩ := hf
  choose V b t _ hb ht hsq using hfac
  refine isRepresentableByAlgebraicSpacesULift_of_etaleCover_comp B S hS f hX.1 hY U a ha hsurj
    fun i ↦ ?_
  rw [hsq i]
  exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ (ht i) (hb i)

end AlgebraicGeometry.FormalSpace

end
