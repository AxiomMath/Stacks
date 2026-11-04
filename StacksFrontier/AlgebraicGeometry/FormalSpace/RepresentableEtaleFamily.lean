module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeEtaleFamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined

/-!
# Representability by algebraic spaces on the covering families of Stacks 0AN4

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0AN4** compares six ways of asking that `f` be
representable by algebraic spaces; conditions (1), (2) and (3) — the ones about commutative
squares — are proved equivalent in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget`, where
condition (4) is written down as well. This file adds condition (5) and the two implications
out of the covering conditions:

4. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uⱼᵢ ⟶ Vⱼ` representable by algebraic
   spaces;
5. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` of `Xᵢ ⟶ X ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y`
   representable by algebraic spaces and `Xᵢ ⟶ Yᵢ` representable by algebraic spaces.

Condition (6) of the source is the text *add more here*, a placeholder and not a condition.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRepresentableOnFactoredAtlas`: condition (5) of
  **Stacks 0AN4**.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_etaleFamily`:
  **representability by algebraic spaces is local on the source along a jointly surjective
  family of representable étale morphisms.**
* `AlgebraicGeometry.FormalSpace.isRepresentableOnFactoredAtlas_of_afterTargetCover`:
  **Stacks 0AN4**, condition (4) implies condition (5).
* `AlgebraicGeometry.FormalSpace.isRepresentable_of_onFactoredAtlas`: **Stacks 0AN4**,
  condition (5) implies condition (1).

## Implementation notes

Condition (5) is read with the coverings of Definition 0AIM as
`AlgebraicGeometry.FormalSpace.IsAffineEtaleCover`, that is affine formal algebraic spaces
mapping to `X` by representable étale morphisms whose coproduct map is a surjection of sheaves,
which is how that definition records surjectivity of an atlas.

The implication from condition (4) to condition (5) composes the coverings of the fibre
products `Vⱼ ×_Y X` with the second projections: that gives a covering of `X` indexed by the
pairs `(j, i)`, whose member `Uⱼᵢ ⟶ X` factors as `Uⱼᵢ ⟶ Vⱼ ⟶ Y` over `f` through the first
projection, which condition (4) asserts to be representable by algebraic spaces, while `Vⱼ` is
an affine formal algebraic space and `Vⱼ ⟶ Y` is representable étale, hence representable by
algebraic spaces. That the composite family is again a covering as in Definition 0AIM holds on
each of its three clauses: the sources are unchanged, representable étaleness of
`Uⱼᵢ ⟶ Vⱼ ×_Y X ⟶ X` is `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.comp` together
with `AlgebraicGeometry.FormalSpace.isRepresentableEtale_pullback_snd`, and joint surjectivity
is `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_comp'` applied to the base
changed covering `{Vⱼ ×_Y X ⟶ X}`, which is jointly surjective by
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`.

The implication from condition (5) to condition (1) is locality of representability on the
source along a *family*: each member `Xᵢ ⟶ X` of the covering composes with `f` to
`Xᵢ ⟶ Yᵢ ⟶ Y`, which is representable by algebraic spaces by Stacks 0APY. The covering is only
*jointly* surjective, so
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_locallySurjective`
does not apply to it, and the coproduct of the covering is of no use in its place: a coproduct
of algebraic spaces indexed by a type of `Type (u + 1)` need not be an algebraic space over
`S`, because the disjoint union of their scheme atlases is an object of the site only under a
uniform size bound, and the cutoff of a big fppf site carries only
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof`. What is done instead is what the proof of
the representability assertion of Stacks 0AIP does, in the form in which
`AlgebraicGeometry.FormalSpace.exists_chart_of_etaleChartFamily` carries it out: the family of
charts of a base change `T ×_Y X` is cut down to one member for each *point* of an object of
the site surjecting onto that base change — the fibre product of the point `T ⟶ Y` with the
surjection onto `X` supplied by the set-theoretic condition of Stacks 0AIS — and each surviving
member is shrunk to an affine open, which is no larger than that object because an affine chart
of a sheaf covered by one object of the site is bounded by it
(`AlgebraicGeometry.FormalSpace.affineChart_size_le'`). No finiteness enters, which is why the
same chart production serves Stacks 0ANL, where the property descended is local finite type,
and Stacks 0AN4, where it is representability alone.

The implications *into* conditions (4) and (5) are not proved. Both ask for a covering as in
Definition 0AIM of a fibre product `Vⱼ ×_Y X`, which presupposes that this fibre product is a
formal algebraic space; that is **Stacks 0AJ3**, available in this library only through
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable`, whose
undischarged input is **Stacks 0AIU** — that a directed colimit of algebraic spaces along
thickenings is a formal algebraic space. Asking the charts of that fibre product to be affine
formal does not avoid it: the base changed charts are fibre products of two affine formal
algebraic spaces, which are affine formal only over a separated base (Stacks 0AN3, clause (1),
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback`), and Stacks 0AN4 asks no
separatedness. This is the same situation as for the corresponding implications of Stacks 0ANL.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
* [Stacks Project, Tag 0APY](https://stacks.math.columbia.edu/tag/0APY)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Locality on the source along a family -/

/-- **Representability by algebraic spaces is local on the source, along a jointly surjective
étale family.** Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S` with
`X` satisfying the set-theoretic condition of **Stacks 0AIS** and `Y` a formal algebraic space
over `S`. If `{pᵢ : Uᵢ ⟶ X}` is a family of representable étale morphisms which is jointly
surjective as a family of morphisms of sheaves and each composite `pᵢ ≫ f` is representable by
algebraic spaces, then `f` is representable by algebraic spaces.

Nothing is asked of the sources `Uᵢ` beyond the sheaf condition. At a scheme-valued point
`ξ : T ⟶ Y` the member `pᵢ` contributes the chart
`AlgebraicGeometry.FormalSpace.exists_memberChart_pullback` of `T ×_Y X`, those charts jointly
cover it, and `AlgebraicGeometry.FormalSpace.exists_chart_of_etaleChartFamily` replaces them by
a single one, which is representable by objects of the site, surjective and étale; **Stacks
0BGR** then makes `T ×_Y X` an algebraic space over `S`.

This is the family form of
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_locallySurjective`,
which consumes a single surjective representable étale morphism, and the representability
counterpart of `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_etaleFamily`. -/
theorem isRepresentableByAlgebraicSpacesULift_of_etaleFamily {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : SatisfiesSetTheoreticCondition B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    {I : Type (u + 1)} {U : I → FppfSheaf B S hS} (p : ∀ i, U i ⟶ X)
    (hp : ∀ i, IsRepresentableEtale B S hS (p i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc p))
    (hrep : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p i ≫ f).hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro T ξ
  have hEsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ f.hom) :=
    Presheaf.isSheaf_pullback _ ξ f.hom
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T).isSheaf X.property Y.property
  choose Zt β hβS hβE hge using fun i =>
    exists_memberChart_pullback B S hS f (p i) (hp i) (hrep i) T ξ
  obtain ⟨W', t, ht⟩ := exists_representable_locallySurjective_pullback B S hS f hX hY T ξ
  obtain ⟨Z, q, hqs, hqe, -⟩ := exists_chart_of_etaleChartFamily B S hS
    (E := (⟨pullback ξ f.hom, hEsheaf⟩ : FppfSheaf B S hS)) t ht
    (fun i => β i ≫ pullback.fst (pullback.snd ξ f.hom) (p i).hom) hge
    (imageSieve_iSup_mem_comp (BigFppfOver.topology B S hS)
      (fun i => pullback.fst (pullback.snd ξ f.hom) (p i).hom) β
      (fun i => isLocallySurjective_of_relative_surjective_etale B S hS (β i) (hβS i) (hβE i))
      (imageSieve_iSup_mem_pullback_fst (BigFppfOver.topology B S hS)
        (fun i => (p i).hom) (pullback.snd ξ f.hom)
        (fun V x => family_imageSieve_mem (BigFppfOver.topology B S hS) U X p hcov V x)))
  exact Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS hEsheaf
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Z) q hqs hqe

/-! ### Conditions (4) and (5) of Stacks 0AN4 -/

/-- **Stacks 0AN4, condition (5).** There is an affine étale covering of the source, each
member of which factors over `f` through an affine formal algebraic space representable by
algebraic spaces over the target by a map which is itself representable by algebraic spaces. -/
abbrev IsRepresentableOnFactoredAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U a ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (v : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧
          Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS v.hom ∧
          a i ≫ f = t ≫ v ∧
          Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom

/-- **Stacks 0AN4, condition (4) implies condition (5).** Composing the coverings of the fibre
products `Vⱼ ×_Y X` with the second projections gives a covering of `X` indexed by the pairs
`(j, i)`, and its member `Uⱼᵢ ⟶ X` factors as `Uⱼᵢ ⟶ Vⱼ ⟶ Y` over `f` through the first
projection, which condition (4) asserts to be representable by algebraic spaces; `Vⱼ` is an
affine formal algebraic space and `Vⱼ ⟶ Y` is representable étale, hence representable by
algebraic spaces.

That the composite family is again a covering as in Definition 0AIM holds on each of the three
clauses: its sources are the sources of the given coverings, representable étaleness of
`Uⱼᵢ ⟶ Vⱼ ×_Y X ⟶ X` is `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.comp` together
with `AlgebraicGeometry.FormalSpace.isRepresentableEtale_pullback_snd`, the second projection
being a base change of `Vⱼ ⟶ Y`, and joint surjectivity is
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_comp'` applied to the base changed
covering `{Vⱼ ×_Y X ⟶ X}`. -/
theorem isRepresentableOnFactoredAtlas_of_afterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsRepresentableAfterTargetCover B S hS f) :
    IsRepresentableOnFactoredAtlas B S hS f := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, hVcover, hcharts⟩ := hf
  choose I U w hUcover hUrep using hcharts
  refine ⟨Σ j, I j, fun ji ↦ U ji.1 ji.2, fun ji ↦ w ji.1 ji.2 ≫ pullback.snd (v ji.1) f,
    ⟨fun ji ↦ (hUcover ji.1).1 ji.2, fun ji ↦ IsRepresentableEtale.comp B S hS
      ((hUcover ji.1).2.1 ji.2)
      (isRepresentableEtale_pullback_snd B S hS (v ji.1) f (hVcover.2.1 ji.1)),
    isLocallySurjective_sigmaDesc_comp' B S hS (fun j ↦ pullback.snd (v j) f) w
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVcover.2.2)
      fun j ↦ (hUcover j).2.2⟩, fun ji ↦ ?_⟩
  refine ⟨V ji.1, v ji.1, w ji.1 ji.2 ≫ pullback.fst (v ji.1) f, hVcover.1 ji.1,
    (hVcover.2.1 ji.1).1, ?_, hUrep ji.1 ji.2⟩
  rw [Category.assoc, Category.assoc, ← pullback.condition]

/-- **Stacks 0AN4, condition (5) implies condition (1).** Let `{Xᵢ ⟶ X}` be a covering as in
Definition 0AIM each member of which factors as `Xᵢ ⟶ Yᵢ ⟶ Y` over `f` through an affine formal
algebraic space with both arrows representable by algebraic spaces. Each composite
`Xᵢ ⟶ Yᵢ ⟶ Y` is then representable by algebraic spaces by Stacks 0APY; it equals
`Xᵢ ⟶ X ⟶ Y`, and representability by algebraic spaces is local on the source along the jointly
surjective family of representable étale morphisms `{Xᵢ ⟶ X}`. -/
theorem isRepresentable_of_onFactoredAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsRepresentableOnFactoredAtlas B S hS f) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  obtain ⟨I, U, a, hcover, hfac⟩ := hf
  refine isRepresentableByAlgebraicSpacesULift_of_etaleFamily B S hS f hX.1 hY a
    hcover.2.1 hcover.2.2 fun i ↦ ?_
  obtain ⟨V, v, t, -, hv, hcomm, ht⟩ := hfac i
  rw [congrArg (fun k : U i ⟶ Y ↦ k.hom) hcomm]
  exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS t.hom v.hom ht hv

end AlgebraicGeometry.FormalSpace

end
