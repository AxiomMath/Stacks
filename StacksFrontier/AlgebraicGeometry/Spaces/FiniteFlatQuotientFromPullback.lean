module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientRepresents
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.PointsLocallySurjective

/-!
# A finite locally free quotient map represents the fppf quotient sheaf

**Nothing here is Stacks 07S6, and nothing here carries that tag.** That proposition asserts the
*existence* of a finite locally free morphism `U ⟶ M` with `R = U ×_M U` representing the fppf
quotient sheaf `U/R`, and the existence of such a morphism is precisely what is assumed in this
file. What is proved is that the third conclusion follows from the first two: for a groupoid
scheme `(U, R, s, t, c)` over a scheme `S` and a morphism `f : U ⟶ M` of `S`-schemes which is
finite locally free, surjective, and whose kernel pair is the pair `(t, s)`, the scheme `M`
represents `U/R` on *every* big fppf site of `S` containing `S`, `U`, `R` and `M`, compatibly with
`f`, so that `f` exhibits `M` as a finite flat quotient of the groupoid in the sense of
`Stacks.Groupoids.FiniteFlatQuotient`.

The use of this is to take the sheaf-theoretic half of the conclusion of Tag 07S6 off the
critical path, leaving an obligation purely about schemes: a quotient scheme and a quotient map
with the two geometric properties. In particular no comparison between two big fppf sites is
needed anywhere, because the statement proved here is site-generic — representation on one site
is never used to obtain representation on another, which a glueing argument carried out on a
single site could not provide.

## Main definitions

* `AlgebraicGeometry.finiteFlatQuotientOfIsPullback` assembles such a quotient map into a term of
  `Stacks.Groupoids.FiniteFlatQuotient`.

## Main results

* `AlgebraicGeometry.quotientSheaf_isRepresented_of_isPullback`: the representation of the
  quotient sheaf by `M`, with the representing isomorphism exhibited as the descent of `f` along
  the canonical projection, on an arbitrary big fppf site of `S`.

## Implementation notes

The representation is `AlgebraicGeometry.quotientSheaf_isRepresentedBy_of_locallySurjective`,
which is Tag 03C5: a map out of the objects which equalizes the two legs of the relation, induces
a surjection of fppf sheaves, and whose associated relation `U ×_M U` is covered by `R`, exhibits
`M` as the quotient. Both surjectivity hypotheses are supplied by
`AlgebraicGeometry.isLocallySurjective_points_map_of_fppf`: for the first because a finite locally
free morphism is flat and locally of finite presentation by Tag 02KB and is assumed surjective,
and for the second because the kernel-pair hypothesis makes the comparison `R ⟶ U ×_M U` an
isomorphism, so in particular surjective, flat and locally of finite presentation. The
`CategoryTheory.HasSheafify` hypothesis for `Type u` which Tag 03C5 needs is a theorem on these
sites, `AlgebraicGeometry.BigFppfOver.hasSheafify_type`, not an instance, and is discharged with
a `have`.

The field `Stacks.Groupoids.FiniteFlatQuotient.represents` asks for an isomorphism of presheaves
of `Type (u + 1)` out of the sheafification of the lifted quotient presheaf, not for the
isomorphism of sheaves of `Type u` that Tag 03C5 produces; the two are reconciled by
`Stacks.Groupoids.exists_iso_sheafifyUlift_quotientPresheaf`, exactly as in
`AlgebraicGeometry.affineFiniteFlatQuotient`.

The proof is the proof of `AlgebraicGeometry.quotientSheaf_isRepresented` with the hypotheses
[affine objects and arrows, equivalence relation, invariant spectrum] replaced by [kernel pair],
so that one is now the special case `f := AlgebraicGeometry.quotientProjection G` of this one, its
kernel-pair hypothesis being `AlgebraicGeometry.relation_isPullback_over`; likewise
`AlgebraicGeometry.affineFiniteFlatQuotient` is the corresponding special case of the definition
here. Both should be collapsed to applications, which this file deliberately does not do because
it does not edit `StacksFrontier/AlgebraicGeometry/Groupoids/Stabilizer/AffineQuotient.lean`.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry

/-- **A finite locally free surjection whose kernel pair is the given relation represents the
fppf quotient sheaf.** Let `(U, R, s, t, c)` be a groupoid scheme over `S` and let `f : U ⟶ M` be
finite locally free and surjective with `IsPullback G.target G.source f f`, which says that `(t,
s)` is the kernel pair of `f`. Then on any big fppf site of `S` the restricted functor of points
of `M` is a sheaf, and the descent of `f` along the canonical projection onto the quotient sheaf
of the pre-relation `(t, s)` is an isomorphism.

This is Tag 03C5 applied to `f`: it is a surjection of fppf sheaves because `f` is surjective,
flat and locally of finite presentation, and the comparison `R ⟶ U ×_M U` is an isomorphism by
the kernel-pair hypothesis, hence in particular a surjection of fppf sheaves. It is *not* Tag
07S6, whose content is the construction of `f`. -/
theorem quotientSheaf_isRepresented_of_isPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {M : Over S} (f : G.objects ⟶ M)
    (hflf : IsFiniteLocallyFree f.left) (hsurj : Surjective f.left)
    (hpb : IsPullback G.target G.source f f)
    (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
    let J := BigFppfOver.topology B S hS
    let j : PreRelation G.arrows G.objects := prod.lift G.target G.source
    ∃ hM : Presheaf.IsSheaf J (points F M),
      ∃ q : quotientSheaf J F j ⟶ (⟨points F M, hM⟩ : Sheaf J (Type u)),
        IsIso q ∧ toQuotientSheaf J F j ≫ q.hom = F.op.whiskerLeft (yoneda.map f) := by
  classical
  let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let J := BigFppfOver.topology B S hS
  let j : PreRelation G.arrows G.objects := prod.lift G.target G.source
  have htgt : PreRelation.target j = G.target := prod.lift_fst G.target G.source
  have hsrc : PreRelation.source j = G.source := prod.lift_snd G.target G.source
  have hf : PreRelation.target j ≫ f = PreRelation.source j ≫ f := by
    rw [htgt, hsrc]; exact hpb.w
  have hπ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f.left).mp hflf
  let _ : Flat f.left := hπ.2.1
  let _ : LocallyOfFinitePresentation f.left := hπ.2.2
  let _ : Surjective f.left := hsurj
  have hM : Presheaf.IsSheaf J (points F M) :=
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS M
  have hU := isLocallySurjective_points_map_of_fppf B S hS f
  let k : G.arrows ⟶ pullback f f :=
    pullback.lift (PreRelation.target j) (PreRelation.source j) hf
  have hk : IsIso k := by
    let e := hpb.isoIsPullback G.objects G.objects (IsPullback.of_hasPullback f f)
    have he : e.hom = k := by
      apply pullback.hom_ext
      · calc
          e.hom ≫ pullback.fst f f = G.target := by simp [e]
          _ = pullback.lift (PreRelation.target j) (PreRelation.source j) hf
                ≫ pullback.fst f f := by rw [pullback.lift_fst, htgt]
      · calc
          e.hom ≫ pullback.snd f f = G.source := by simp [e]
          _ = pullback.lift (PreRelation.target j) (PreRelation.source j) hf
                ≫ pullback.snd f f := by rw [pullback.lift_snd, hsrc]
    rw [← he]
    infer_instance
  have : IsIso k.left := by
    change IsIso ((Over.forget S).map k)
    infer_instance
  have hR := isLocallySurjective_points_map_of_fppf B S hS k
  obtain ⟨q, hq, hfac⟩ :=
    quotientSheaf_isRepresentedBy_of_locallySurjective J F j f hf hM hU hR
  exact ⟨hM, q, hq, hfac⟩

/-- **A finite locally free surjection whose kernel pair is the given relation is a finite flat
quotient.** For a groupoid scheme `(U, R, s, t, c)` over `S`, a morphism `f : U ⟶ M` of
`S`-schemes which is finite locally free, surjective and has `(t, s)` for its kernel pair makes
`M` a finite flat quotient of the groupoid in the sense of
`Stacks.Groupoids.FiniteFlatQuotient`.

The three given properties are the first three fields verbatim; the only thing proved is the
fourth, that `M` represents the fppf quotient sheaf on every big fppf site containing the base,
the objects, the arrows and `M`, which is
`AlgebraicGeometry.quotientSheaf_isRepresented_of_isPullback` composed with the universe
comparison `Stacks.Groupoids.exists_iso_sheafifyUlift_quotientPresheaf`.

This is not an existence statement for finite flat quotients: the quotient scheme and the
quotient map are inputs. -/
def finiteFlatQuotientOfIsPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {M : Over S} (f : G.objects ⟶ M)
    (hflf : IsFiniteLocallyFree f.left) (hsurj : Surjective f.left)
    (hpb : IsPullback G.target G.source f f) : FiniteFlatQuotient G where
  space := M
  quotientMap := f
  finiteLocallyFree := hflf
  surjective := hsurj
  kernelPair := hpb
  represents := by
    intro B hS _hU _hR _hM
    have _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
      BigFppfOver.hasSheafify_type B S hS
    obtain ⟨hMs, q, hq, hfac⟩ :=
      quotientSheaf_isRepresented_of_isPullback G f hflf hsurj hpb B hS
    exact exists_iso_sheafifyUlift_quotientPresheaf _ _ _ _ hMs q hq hfac

end AlgebraicGeometry

end

end
