module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseQuasiCompactDescent
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteDescentFromQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Effective descent for separated locally quasi-finite morphisms, from Stacks 0247

Effective descent along the surjective étale morphisms of the big fppf site of `S` for the
quasi-affine morphisms of schemes, which is Stacks 0247, implies effective descent for the
separated, locally quasi-finite morphisms which are locally of finite type, the property of
Stacks 02W8, with no quasi-compactness conjunct. It also implies effective descent for immersions.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom`: let `G` be a
  sheaf on the big fppf site of `S` with a morphism `π : G ⟶ yoneda.obj a`, and let
  `g : yoneda.obj U ⟶ G` be a chart presented as a base change of a surjective étale `q : c ⟶ a`
  with `c` affine, whose other leg `ρ` is separated, locally quasi-finite and locally of finite
  type. If the part of the chart lying over the subfunctor
  `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by a set `W` of points of `G` is,
  Cartesianly, a *quasi-compact* open `b ⟶ U` of the chart, then that subfunctor is
  representable.
* `isEffectiveDescentAlongSurjectiveEtale_isSeparated_locallyQuasiFinite_locallyOfFiniteType`, in
  the namespace `AlgebraicGeometry.Space`: effective descent along the surjective étale morphisms
  of the big fppf site of `S` for the quasi-affine morphisms of schemes implies it for the
  separated, locally quasi-finite morphisms which are locally of finite type.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion_of_isQuasiAffineHom`:
  the same implication for immersions.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 01SO](https://stacks.math.columbia.edu/tag/01SO)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Representability of an open subspace of points -/

/-- A property respecting isomorphisms holds for one leg of a pullback square as soon as it holds
for the same leg of another pullback square over the same cospan. -/
private theorem snd_of_isPullback_of_isPullback {D : Type*} [Category D]
    {P : MorphismProperty D} [P.RespectsIso] {X X' Y Y' Z : D} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst : Y' ⟶ X} {snd : Y' ⟶ Y} {fst' : X' ⟶ X} {snd' : X' ⟶ Y}
    (sq : IsPullback fst snd f g) (sq' : IsPullback fst' snd' f g) (h : P snd') : P snd := by
  rw [← sq.isoIsPullback_hom_snd _ _ sq']
  exact MorphismProperty.RespectsIso.precomp _ _ _ h

/-- Let `G` be a sheaf on the big fppf site of `S` carrying a morphism `π : G ⟶ yoneda.obj a`, and
let `g : yoneda.obj U ⟶ G` be a chart of `G` presented as a base change of a surjective étale
morphism `q : c ⟶ a` of the site with `c` affine, whose other leg `ρ` is separated, locally
quasi-finite and locally of finite type after every represented base change. Let `W` be a set of
points of `G` and suppose that the part of the chart lying over the subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by `W` is, Cartesianly, an open `i : b ⟶ U`
of the chart whose image is quasi-compact. Then that subfunctor is representable. -/
theorem isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom
    (h0247 : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}))
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {a c : BigFppfOver B S hS} (π : G ⟶ yoneda.obj a) (q : c ⟶ a)
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G} {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ π (yoneda.map q))
    (hρ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ρ)
    {W : Set (points B S hS G)} {b : BigFppfOver B S hS} {i : b ⟶ U}
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hbqc : IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map i)))
    {k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor}
    (hsqb : IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g) :
    (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable := by
  have _hc := hc
  have _hi := hi
  have _hqari := isQuasiAffineHom_respectsIso.{u}
  have _hsepbc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  set ρ₀ : U ⟶ c := yoneda.preimage ρ
  have hρmap : yoneda.map ρ₀ = ρ := Functor.map_preimage _ _
  obtain ⟨⟨_hsep, _hqf⟩, _hft⟩ :
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) ((BigFppfOver.toScheme B S hS).map ρ₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ρ₀).1 (hρmap ▸ hρ)
  -- the open `b` is a quasi-compact scheme, so `i ≫ ρ₀` is a quasi-compact morphism
  have _hcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) :=
    ⟨hi.base_open.isEmbedding.isCompact_iff.2 (by rwa [Set.image_univ])⟩
  have _hqsp : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj c) :=
    quasiSeparatedSpace_of_isAffine _
  have hQA : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i ≫ ρ₀)) := by
    rw [Functor.map_comp]
    exact isSeparated_inf_quasiFinite_le_isQuasiAffineHom _
      ⟨⟨⟨inferInstance, inferInstance⟩, inferInstance⟩, inferInstance⟩
  have hQAp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i ≫ ρ) := by
    rw [← hρmap, ← Functor.map_comp]
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (i ≫ ρ₀)).2 hQA
  have sqF : IsPullback k (yoneda.map i ≫ ρ)
      ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q) := hsqb.paste_vert sqg
  have hpb := IsPullback.of_hasPullback
    ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q)
  exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (presheaf_of_surjectiveEtaleChart h0247
      (isSheaf_openSubspaceOfPoints B S hS hG W)
      (BigFppfOver.isSheaf_yoneda_obj B S hS a) 
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe)
      (snd_of_isPullback_of_isPullback hpb sqF hQAp)).rep

/-! ### Separated locally quasi-finite morphisms -/

/-- Effective descent along the surjective étale morphisms of the big fppf site of `S` for the
quasi-affine morphisms of schemes implies effective descent for the separated, locally
quasi-finite morphisms which are locally of finite type. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isSeparated_locallyQuasiFinite_locallyOfFiniteType
    (h0247 : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) := by
  have _hdesc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  have _hbc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine isEffectiveDescentAlongSurjectiveEtale_of_representable_of_affineBase ?_
  intro X Y f hX hY a c h q ha hc hqs hqe hqqc A m r sq hr U g ρ sqg T b i k hi hirange hcomp hsqb
  have sq₂ := sq.of_right' (IsPullback.of_hasPullback f h)
  exact isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom h0247
    (BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY) (pullback.snd f h) q hc hqs hqe sqg
    (snd_of_isPullback_of_isPullback sqg sq₂ hr) hi (hirange ▸ hcomp) hsqb

/-! ### Immersions -/

/-- Effective descent along the surjective étale morphisms of the big fppf site of `S` for the
quasi-affine morphisms of schemes implies effective descent for immersions. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isImmersion_of_isQuasiAffineHom
    (h0247 : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) := by
  have _hdesc := Stacks.Descent.isImmersion_descendsAlong_fppf.{u}
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine isEffectiveDescentAlongSurjectiveEtale_of_le
    (isEffectiveDescentAlongSurjectiveEtale_isSeparated_locallyQuasiFinite_locallyOfFiniteType
      h0247) ?_
  intro _ _ j hj
  have : _root_.AlgebraicGeometry.IsImmersion j := hj
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end AlgebraicGeometry.Space

end
