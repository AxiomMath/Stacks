module

public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent

/-!
# The quasi-compactness conjunct, removed at the monomorphisms locally of finite type

The theorem
`isEffectiveDescentAlongSurjectiveEtale_isSeparated_locallyQuasiFinite_locallyOfFiniteType`
removes the quasi-compactness conjunct from the property of Stacks 02W8 at the cost of assuming
Stacks 0247, effective descent for the quasi-affine morphisms. The reason it has to pass through
quasi-affineness is that the pieces of the covering built by the second step of Stacks 02W8 are
quasi-compact, and Stacks 02LR identifies a quasi-compact separated locally quasi-finite morphism
as a quasi-affine one.

At the monomorphisms locally of finite type that detour is unnecessary: a quasi-compact open of a
monomorphism is again a monomorphism, so the pieces stay inside the property one started from and
the hypothesis needed is effective descent at the *quasi-compact* monomorphisms locally of finite
type. That property is below the monomorphisms, which is what makes it reachable from a
construction rather than from a sheaf-theoretic argument — see
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_hasDescendedHull`.

This matters because the monomorphisms locally of finite type are the property at which the
diagonal of a sheaf with an étale atlas consumes effective descent, by
`AlgebraicGeometry.relativelyRepresentable_diag_of_surjective_etale_atlas`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_monomorphisms_inf_quasiCompact`:
  the third and fourth steps of Stacks 02W8 at one piece of the covering, for a monomorphic
  datum, with the quasi-compact monomorphisms in place of the quasi-affine morphisms.
* `isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_quasiCompact`,
  in the namespace `AlgebraicGeometry.Space`: effective descent along the surjective étale
  morphisms of the site for the quasi-compact monomorphisms locally of finite type implies it for
  all of them.

## Implementation notes

The argument is that of
`isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom`, with Stacks 02LR deleted. The piece
of the covering is the composite `i ≫ ρ₀` of a quasi-compact open immersion of the chart with the
monomorphism underlying the datum: it is a monomorphism because both factors are, it is locally
of finite type for the same reason, and it is quasi-compact because its source is a quasi-compact
scheme and its target is affine, hence a quasi-separated space
(`AlgebraicGeometry.quasiCompact_of_compactSpace`). Where the quasi-affine form invokes Stacks
02LR to leave the property, this stays in it.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The third and fourth steps of Stacks 02W8 at one piece of the covering, for a monomorphic
datum.** Let `G` be a sheaf on the big fppf site of `S` carrying a morphism `π : G ⟶ yoneda.obj a`
and let `g : yoneda.obj U ⟶ G` be a chart of `G` presented as a base change of a surjective étale
`q : c ⟶ a` with `c` affine, whose other leg `ρ` is, after every represented base change, a
monomorphism locally of finite type. Let `W` be a set of points of `G` and suppose that the part
of the chart lying over the subfunctor `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by
`W` is, Cartesianly, an open `i : b ⟶ U` of the chart whose image is quasi-compact. Then that
subfunctor is representable.

The piece whose descent is asked of the hypothesis is `i ≫ ρ₀`, a quasi-compact monomorphism
locally of finite type; no passage to the quasi-affine morphisms is involved. -/
theorem isRepresentable_openSubspaceOfPoints_of_monomorphisms_inf_quasiCompact
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact))
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {a c : BigFppfOver B S hS} (π : G ⟶ yoneda.obj a) (q : c ⟶ a)
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G} {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ π (yoneda.map q))
    (hρ : (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
      (BigFppfOver.toScheme B S hS)).presheaf ρ)
    {W : Set (points B S hS G)} {b : BigFppfOver B S hS} {i : b ⟶ U}
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hbqc : IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map i)))
    {k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor}
    (hsqb : IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g) :
    (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable := by
  have _hc := hc
  have _hi := hi
  have _hbc' : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := .inf
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact) := .inf
  have _hri : MorphismProperty.RespectsIso
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- the morphism of the site underlying `ρ`, and the property it carries
  set ρ₀ : U ⟶ c := yoneda.preimage ρ
  have hρmap : yoneda.map ρ₀ = ρ := Functor.map_preimage _ _
  obtain ⟨hmono, hft⟩ :
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
        ((BigFppfOver.toScheme B S hS).map ρ₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ρ₀).1 (hρmap ▸ hρ)
  have _hmono : Mono ((BigFppfOver.toScheme B S hS).map ρ₀) := hmono
  have _hft := hft
  -- the open `b` is a quasi-compact scheme, so `i ≫ ρ₀` is a quasi-compact morphism
  have _hcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) :=
    ⟨hi.base_open.isEmbedding.isCompact_iff.2 (by rwa [Set.image_univ])⟩
  have _hqsp : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj c) :=
    quasiSeparatedSpace_of_isAffine _
  -- the piece stays inside the property: it is a quasi-compact monomorphism of finite type
  have hQ : (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)
      ((BigFppfOver.toScheme B S hS).map (i ≫ ρ₀)) := by
    rw [Functor.map_comp]
    exact ⟨⟨inferInstance, inferInstance⟩, quasiCompact_of_compactSpace _⟩
  have hQp : (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i ≫ ρ) := by
    rw [← hρmap, ← Functor.map_comp]
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (i ≫ ρ₀)).2 hQ
  -- the pasted square is the datum of the open subfunctor over `yoneda.obj a`
  have sqF : IsPullback k (yoneda.map i ≫ ρ)
      ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q) := hsqb.paste_vert sqg
  have hpb := IsPullback.of_hasPullback
    ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q)
  have hV : (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)
      (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q)) := by
    rw [← hpb.isoIsPullback_hom_snd _ _ sqF]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hQp
  have hqs' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs
  have hqe' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe
  exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (presheaf_of_surjectiveEtaleChart hdesc
      (isSheaf_openSubspaceOfPoints B S hS hG W)
      (BigFppfOver.isSheaf_yoneda_obj B S hS a) hqs' hqe' hV).rep

/-- **Effective descent for the monomorphisms locally of finite type, from its quasi-compact
case.** Effective descent along the surjective étale morphisms of the big fppf site of `S` for the
quasi-compact monomorphisms locally of finite type implies it for the monomorphisms locally of
finite type, with no quasi-compactness conjunct.

The conjunct cannot be removed by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le`, which transfers effective
descent only downwards along `≤`. It comes off through the second step of Stacks 02W8, which
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_of_affineBase`
reduces the statement to and which
`isRepresentable_openSubspaceOfPoints_of_monomorphisms_inf_quasiCompact` discharges. -/
theorem isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_quasiCompact
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := by
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := .inf
  have _hri : MorphismProperty.RespectsIso
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hd := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  refine isEffectiveDescentAlongSurjectiveEtale_of_representable_of_affineBase ?_
  intro X Y f hX hY a c h q ha hc hqs hqe hqqc A m r sq hr U g ρ sqg T b i k hi hirange hcomp hsqb
  have sq₂ := sq.of_right' (IsPullback.of_hasPullback f h)
  have hρ : (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
      (BigFppfOver.toScheme B S hS)).presheaf ρ := by
    rw [← sqg.isoIsPullback_hom_snd _ _ sq₂]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hr
  exact isRepresentable_openSubspaceOfPoints_of_monomorphisms_inf_quasiCompact hdesc
    (BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY) (pullback.snd f h) q hc hqs hqe sqg hρ
    hi (hirange ▸ hcomp) hsqb

end AlgebraicGeometry.Space

end
