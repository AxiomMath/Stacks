module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasFiniteSubcoverRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsRepresentable

/-!
# Joint surjectivity of a family of representable étale charts, read off its points

Let `S` be a scheme contained in a big fppf site `B` and let `{fᵢ : Xᵢ ⟶ X}` be a family of
morphisms of fppf sheaves on the big fppf site of `S` whose sources are affine formal algebraic
spaces and which are representable by algebraic spaces and étale, as the members of a covering
as in Definition **Stacks 0AIM** are. Such a family is a surjection of sheaves out of the
coproduct as soon as it is *jointly surjective on points*: every point of `X` is the image of a
point of some `Xᵢ`.

That is the criterion
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_jointly_surjective_points`
below. It is the family form of the step of the proof of **Stacks 03Y8** carried by
`AlgebraicGeometry.FormalSpace.isLocallySurjective_of_isSurjective_of_flat`, which upgrades
surjectivity on points of a *single* representable flat morphism to a surjection of sheaves;
the family form cannot be reduced to it, because a morphism out of a coproduct of sheaves
indexed by a type of `Type (u + 1)` is not known to be representable by algebraic spaces —
that is `AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`, which this library does
not prove.

## Main results

* `AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_etale`: a jointly surjective family of
  étale morphisms of the big fppf category over `S` generates a covering sieve. This is the
  étale counterpart of
  `AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`.
* `AlgebraicGeometry.FormalSpace.surjective_pointsMapULift_of_relative_surjective`: a morphism
  out of a universe-lifted Yoneda presheaf which is representable by objects of the site and
  surjective after every represented base change is surjective on points.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_jointly_surjective_points`:
  the criterion itself.

## Implementation notes

The criterion is proved one section at a time. A section of `X` over an object `T` of the site
is a morphism `c : h_T ⟶ X`; **Stacks 0AIG** in the form
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isEtale_of_isAffineFormal` makes each
`fᵢ` representable by objects of the site, so the base changes `Vᵢ = Xᵢ ×_X T` are objects of
the site and the morphisms `Vᵢ ⟶ T` are étale, exactly as in
`StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasFiniteSubcover`. They are jointly surjective on
the points of `T`: a point of the scheme `T` is a point of `h_T` by
`AlgebraicGeometry.Space.pointsEquivSchemeULift`, its image in `X` lifts to some `Xᵢ` by
hypothesis, and the two compatible points assemble to a point of the fibre product by
`AlgebraicGeometry.Space.exists_point_of_isPullbackULift`. A jointly surjective étale family
generates a covering sieve, and over each of its arrows the section lifts to the corresponding
`Xᵢ` tautologically, through the fibre product square.

The covering-sieve statement is proved here rather than reused: the corresponding statement for
a family which is flat and locally of finite presentation is private to
`StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionTfae` and is indexed by a type of
`Type u`, whereas an atlas as in Definition 0AIM is indexed by a type of `Type (u + 1)`.

## References

* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A jointly surjective family of étale morphisms of the big fppf category over `S`
generates a covering sieve.** The family is an étale covering of the underlying schemes, hence
an fppf covering of them, and the covering sieves of the slice over `S` are those of the
ambient site.

The index type lives in `Type (u + 1)`, the universe in which an atlas as in Definition
**Stacks 0AIM** is indexed. This is the étale counterpart of
`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`. -/
theorem ofArrows_mem_topology_of_etale {U : BigFppfOver B S hS} {I : Type (u + 1)}
    (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ U)
    (hetale : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (v i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i))) :
    Sieve.ofArrows V v ∈ BigFppfOver.topology B S hS U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} U.left :=
    ⟨I, fun i => (V i).left, fun i => (v i).left⟩
  have heq : E.presieve₀ =
      Presieve.ofArrows (fun i => (V i).left) (fun i => (v i).left) := rfl
  rw [Sieve.ofArrows, ← heq]
  apply B.generate_mem_topology_of_isFppfCovering E
  rw [IsFppfCovering, Precoverage.mem_comap_iff, heq, Presieve.map_ofArrows]
  exact Scheme.etalePrecoverage_le_fppfPrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff
      (@Etale.{u} : MorphismProperty Scheme.{u})).2 ⟨hcov, hetale⟩)

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism out of a universe-lifted Yoneda presheaf which is representable by objects of
the site and surjective after every represented base change is surjective on points.**

A point of the target is a section over the spectrum `A` of a field of the site; the base change
of the morphism along it is a morphism `W ⟶ A` of the site which is surjective, and `A` is
nonempty, so `W` has a point. That point is a point of `h_W`, by
`AlgebraicGeometry.Space.pointsEquivSchemeULift`, and its image in `h_A` is the tautological
point of `h_A` because the underlying scheme of `A` is a one-point space; so its image under the
given morphism is the point one started from. -/
theorem surjective_pointsMapULift_of_relative_surjective
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U : BigFppfOver B S hS}
    (a : uliftYoneda.{u + 1}.obj U ⟶ F)
    (ha : (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) a) :
    Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _ a) := by
  intro xr
  obtain ⟨pt, rfl⟩ := Quot.exists_rep xr
  let A : BigFppfOver B S hS := pt.siteObject B S hS F
  let ξ : uliftYoneda.{u + 1}.obj A ⟶ F := uliftYonedaEquiv.{u + 1}.symm pt.value
  have hsnd : Surjective ((BigFppfOver.toScheme B S hS).map (ha.rep.snd ξ)) :=
    ha.property_snd ξ
  obtain ⟨w, -⟩ := hsnd.surj
    (IsLocalRing.closedPoint pt.carrier : (BigFppfOver.toScheme B S hS).obj A)
  let pW : Space.pointsULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj (ha.rep.pullback ξ)) :=
    (Space.pointsEquivSchemeULift.{u + 1} B S hS (ha.rep.pullback ξ)).symm w
  let q₀ : Space.FieldValuedPointULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj A) :=
    ⟨pt.carrier, pt.contained, pt.toBase, ULift.up (𝟙 A)⟩
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj A) := by
    change Subsingleton (Spec (CommRingCat.of pt.carrier))
    infer_instance
  have hA : Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (ha.rep.snd ξ)) pW
      = q₀.class B S hS _ :=
    (Space.pointsEquivSchemeULift.{u + 1} B S hS A).injective (Subsingleton.elim _ _)
  have hξpt : Space.pointsMapULift B S hS (uliftYoneda.{u + 1}.obj A) ξ (q₀.class B S hS _)
      = pt.class B S hS F := by
    refine Quot.sound ⟨pt, ⟨𝟙 _, ?_⟩, ⟨𝟙 _, by simp⟩⟩
    change F.map (𝟙 A).op (ξ.app (Opposite.op A) (ULift.up (𝟙 A))) = pt.value
    simp [ξ]
  refine ⟨Space.pointsMapULift B S hS _ (ha.rep.fst ξ) pW, ?_⟩
  calc Space.pointsMapULift B S hS _ a
          (Space.pointsMapULift B S hS _ (ha.rep.fst ξ) pW)
      = Space.pointsMapULift B S hS _ (ha.rep.fst ξ ≫ a) pW := by
        rw [Space.pointsMapULift_comp]
        rfl
    _ = Space.pointsMapULift B S hS _
          (uliftYoneda.{u + 1}.map (ha.rep.snd ξ) ≫ ξ) pW := by
        rw [(ha.rep.isPullback ξ).w]
    _ = Space.pointsMapULift B S hS _ ξ
          (Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (ha.rep.snd ξ)) pW) := by
        rw [Space.pointsMapULift_comp]
        rfl
    _ = pt.class B S hS F := by rw [hA, hξpt]

/-- **A family of representable étale morphisms out of affine formal algebraic spaces which is
jointly surjective on points is a surjection of sheaves out of the coproduct.** This is the
clause of Definition **Stacks 0AIM** which asks an atlas to be jointly surjective, deduced from
joint surjectivity on points alone.

A section of the target over an object `T` of the site base changes the family to a family of
étale morphisms `Vᵢ ⟶ T` of the site, by **Stacks 0AIG**; joint surjectivity on points makes
that family jointly surjective on the points of `T`, hence a covering family, and over each of
its members the section lifts to the corresponding source through the fibre product square.

This is the family form of
`AlgebraicGeometry.FormalSpace.isLocallySurjective_of_isSurjective_of_flat`, this library's
**Stacks 03Y8**, which applies to a single morphism representable by algebraic spaces and
cannot be applied to the morphism out of the coproduct: that morphism is representable by
algebraic spaces only by
`AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`, which is unproved here. -/
theorem isLocallySurjective_sigmaDesc_of_jointly_surjective_points
    {X : FppfSheaf B S hS} {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS}
    (f : ∀ i, Xi i ⟶ X)
    (haffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hetale : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hpoints : ∀ x : Space.pointsULift.{u + 1} B S hS X.obj,
      ∃ (i : I) (z : Space.pointsULift.{u + 1} B S hS (Xi i).obj),
        Space.pointsMapULift B S hS (Xi i).obj (f i).hom z = x) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc f) := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let Yo := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  -- Stacks 0AIG: every member is representable by objects of the site
  have hrep : ∀ i, Yo.relativelyRepresentable (f i).hom := by
    intro i
    obtain ⟨hfi, he⟩ := hetale i
    exact relativelyRepresentable_of_isEtale_of_isAffineFormal B S hS (f i) (haffine i) hfi he
  change Presheaf.IsLocallySurjective J (Sigma.desc f).hom
  refine ⟨?_⟩
  intro T y
  let c : Yo.obj T ⟶ X.obj := uliftYonedaEquiv.{u + 1}.symm y
  have hy : uliftYonedaEquiv.{u + 1} c = y := Equiv.apply_symm_apply _ _
  choose V q ξ hsq using fun i ↦ hrep i c
  -- étaleness of the member after the represented base change along the section
  have hetfst : ∀ i, Space.IsEtaleULift.{u + 1} B S hS (pullback.fst c (f i).hom) := by
    intro i
    obtain ⟨_, he⟩ := hetale i
    exact he T c
  have hq : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (q i)) := by
    intro i
    rw [← Space.isEtaleULift_uliftYoneda_map_iff.{u + 1, u} B S hS (q i)]
    intro W φ hφ
    have he : Yo.map (q i) = (hsq i).flip.isoPullback.hom ≫ pullback.fst c (f i).hom :=
      ((hsq i).flip.isoPullback_hom_fst).symm
    rw [he, ← Category.assoc]
    exact hetfst i W (φ ≫ (hsq i).flip.isoPullback.hom)
      (((P.relative Yo).cancel_right_of_respectsIso φ _).mpr hφ)
  -- the base changed family covers the points of `T`
  have hpoint : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i)) := by
    intro x
    obtain ⟨i, z, hz⟩ := hpoints (Space.pointsMapULift B S hS _ c
      ((Space.pointsEquivSchemeULift.{u + 1} B S hS T).symm x))
    obtain ⟨v, -, hv⟩ := Space.exists_point_of_isPullbackULift B S hS (hsq i) z _ hz
    refine ⟨i, Space.pointsEquivSchemeULift.{u + 1} B S hS (V i) v, ?_⟩
    rw [← Space.pointsEquivSchemeULift_naturality B S hS (q i) v, hv]
    exact (Space.pointsEquivSchemeULift.{u + 1} B S hS T).apply_symm_apply x
  -- so it is a covering family, and the section lifts over each of its members
  refine J.superset_covering ?_
    (BigFppfOver.ofArrows_mem_topology_of_etale B S hS V q hq hpoint)
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro Z a ⟨i⟩
  refine ⟨uliftYonedaEquiv.{u + 1} (ξ i ≫ (Sigma.ι Xi i).hom), ?_⟩
  have hid : (Sigma.ι Xi i).hom ≫ (Sigma.desc f).hom = (f i).hom :=
    congrArg (fun k : Xi i ⟶ X => k.hom) (Sigma.ι_comp_desc f i)
  calc (Sigma.desc f).hom.app (Opposite.op (V i))
          (uliftYonedaEquiv.{u + 1} (ξ i ≫ (Sigma.ι Xi i).hom))
      = uliftYonedaEquiv.{u + 1}
          ((ξ i ≫ (Sigma.ι Xi i).hom) ≫ (Sigma.desc f).hom) := (uliftYonedaEquiv_comp _ _).symm
    _ = uliftYonedaEquiv.{u + 1} (ξ i ≫ (f i).hom) := by rw [Category.assoc, hid]
    _ = uliftYonedaEquiv.{u + 1} (Yo.map (q i) ≫ c) := by rw [(hsq i).w]
    _ = X.obj.map (q i).op y := by
        rw [← hy]
        exact (uliftYonedaEquiv_naturality.{u + 1} c _).symm

end AlgebraicGeometry.FormalSpace

end
