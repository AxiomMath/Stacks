module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.Limits.EtaleChartDescent
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
public import StacksCore.Tactic.StacksAttribute

/-!
# Representable constructible sheaves on a limit of schemes come from a finite stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms inside a big étale site, and let `f_i : X ⟶ X_i` be the
projections. This file proves that every sheaf of sets on `X_étale` represented by a
quasi-compact and quasi-separated object of `X_étale` is the inverse image of a *constructible*
sheaf of sets at some stage. This is the essential surjectivity assertion of Tag 09YU, clause
(1), for the representable sheaves — the case to which the source reduces that assertion.

## The source's argument

The source proves essential surjectivity for clause (1) by writing a constructible sheaf as a
coequalizer of finite coproducts of representables (Tag 09Y9) and then says: "it suffices to
prove this for `h_U` for some quasi-compact and quasi-separated object `U` of `X_étale`. In this
case we have to show that `U` is the base change of a quasi-compact and quasi-separated scheme
étale over `X_i` for some `i`." That geometric step is already a theorem of this library,
`AlgebraicGeometry.exists_isPullback_etale_of_etale`, which combines Tag 01ZM part (1) with
Tag 07RP. What is proved here is the passage from it to the assertion about sheaves: the
descended scheme is an object of the small étale site of the stage, inverse image carries its
representable sheaf to the representable sheaf of `U`, and a representable sheaf on a
quasi-compact quasi-separated object is constructible by Tag 03S8 part (1).

## Main results

* `AlgebraicGeometry.exists_stage_smallEtaleModel_of_qcqs` — a quasi-compact and quasi-separated
  object of the small étale site of the limit is, up to isomorphism, the small étale base change
  of a quasi-compact and quasi-separated object of the small étale site of some stage.
* `AlgebraicGeometry.exists_stage_isConstructibleSetSheaf_iso_sheafifiedYoneda` — **Tag 09YU,
  clause (1), the essential surjectivity assertion for the sheaves represented by a
  quasi-compact and quasi-separated object.**

## Implementation notes

The descended scheme belongs to the big étale site because it is quasi-compact and locally of
finite type over a scheme of that site, which is Tag 000R (5) in the form
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`; so no size hypothesis
has to be imposed on it.

The comparison isomorphism is built once, at the level of schemes, from the uniqueness of a
pullback: both the object of the limit and the small étale base change of the descended object
sit in a pullback square over the same cospan, and the inclusion of the big étale site into all
schemes preserves the pullback. It is then carried back along that inclusion and along the
inclusion of the small étale site, both of which are fully faithful.

Essential surjectivity for all constructible sheaves of sets needs, besides this, the fullness
assertion of clause (1), which the source deduces from the degree-zero set-valued sections
identity of Theorem Tag 09YQ; that identity is not available for sheaves of sets in this
library, so only the representable case is proved here.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section RepresentableEssSurj

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- **A quasi-compact and quasi-separated object of the small étale site of the limit comes from
a stage.** Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms inside a big étale site. Every
quasi-compact and quasi-separated object of `X_étale` is isomorphic to the small étale base
change of a quasi-compact and quasi-separated object of `(X_i)_étale` for some `i`.

This is the geometric step of the essential surjectivity assertion of Tag 09YU clause (1), read
on the small étale sites: the underlying schemes are descended by
`AlgebraicGeometry.exists_isPullback_etale_of_etale`, which is Tag 01ZM part (1) followed by
Tag 07RP, and the descended scheme lies in the big étale site by Tag 000R (5). -/
public theorem exists_stage_smallEtaleModel_of_qcqs (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (U : SmallEtale B c.pt hX)
    (hUc : CompactSpace U.obj.left.obj) (hUq : QuasiSeparatedSpace U.obj.left.obj) :
    ∃ (i : I) (Ui : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property),
      CompactSpace Ui.obj.left.obj ∧ QuasiSeparatedSpace Ui.obj.left.obj ∧
        Nonempty ((smallEtaleBaseChange B
            (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i))).obj Ui ≅
          U) := by
  have haff' : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) :=
    fun e => haff e
  have hqc' : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have hqs' : ∀ p : Iᵒᵖ, QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqs p.unop
  have : Etale (B.inclusion.map U.obj.hom) := U.property
  have : CompactSpace (B.inclusion.obj U.obj.left) := hUc
  have : QuasiSeparatedSpace (B.inclusion.obj U.obj.left) := hUq
  -- Descend the underlying scheme, with its structure morphism, to a stage.
  obtain ⟨k, U', u', θ, hu', hcU, hqU, hpb⟩ :=
    exists_isPullback_etale_of_etale (Dg ⋙ B.inclusion) c hc (B.inclusion.map U.obj.hom)
  have : QuasiCompact u' := quasiCompact_of_compactSpace u'
  -- Tag 000R (5): the descended scheme lies in the big étale site.
  have hU' : B.Contains U' :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact u' (Dg.obj k).property
  -- Read it as an object of the small étale site of the stage.
  let pk : B.obj c.pt hX ⟶ Dg.obj k := ObjectProperty.homMk (c.π.app k)
  let uk : B.obj U' hU' ⟶ Dg.obj k := ObjectProperty.homMk u'
  -- Both `U` and the base change of `Ui` are pullbacks of `u'` along `c.π.app k`.
  have hbc : IsPullback (B.inclusion.map (pullback.fst (Over.mk uk).hom pk))
      (B.inclusion.map (pullback.snd (Over.mk uk).hom pk)) u' (c.π.app k) :=
    (IsPullback.of_hasPullback (Over.mk uk).hom pk).map B.inclusion
  let eS : B.inclusion.obj U.obj.left ≅
      B.inclusion.obj (pullback (Over.mk uk).hom pk) := hpb.isoIsPullback _ _ hbc
  -- Carry the comparison back through the two fully faithful inclusions.
  let eB : U.obj.left ≅ pullback (Over.mk uk).hom pk := B.inclusion.preimageIso eS
  have heB : B.inclusion.map eB.hom = eS.hom := B.inclusion.map_preimage _
  have hwB : eB.hom ≫ pullback.snd (Over.mk uk).hom pk = U.obj.hom :=
    B.inclusion.map_injective <| by
      rw [B.inclusion.map_comp, heB, hpb.isoIsPullback_hom_snd _ _ hbc]
  exact ⟨k.unop, ⟨Over.mk uk, hu'⟩, hcU, hqU,
    ⟨(SmallEtale.inclusion B c.pt hX).preimageIso (Over.isoMk eB (by simpa using hwB)).symm⟩⟩

/-- **Stacks 09YU, clause (1), the essential surjectivity assertion for a representable sheaf.**
Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms inside a big étale site. For every quasi-compact and
quasi-separated object `U` of `X_étale` there is a stage `i` and a *constructible* sheaf of sets
on `(X_i)_étale` whose inverse image to `X_étale` is the sheaf `h_U` represented by `U`.

This is the case of the essential surjectivity assertion of clause (1) to which the source
reduces it through Tag 09Y9. The object `U` is descended to the stage by
`AlgebraicGeometry.exists_stage_smallEtaleModel_of_qcqs`; inverse image carries the representable
sheaf of the descended object to the representable sheaf of its base change, because inverse
image along a continuous functor commutes with the sheafified Yoneda embedding; and the
representable sheaf of a quasi-compact and quasi-separated object is constructible by Tag 03S8
part (1). -/
@[stacks 09YU "clause (1), the essential surjectivity assertion for the sheaves represented by \
a quasi-compact and quasi-separated object of the small etale site, which is the case the \
source's proof reduces that assertion to"]
public theorem exists_stage_isConstructibleSetSheaf_iso_sheafifiedYoneda (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (U : SmallEtale B c.pt hX)
    (hUc : CompactSpace U.obj.left.obj) (hUq : QuasiSeparatedSpace U.obj.left.obj) :
    ∃ (i : I) (Fi : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property) (Type (u + 1))),
      IsConstructibleSetSheaf B (Dg.obj (op i)) Fi ∧
        Nonempty ((smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj Fi ≅
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B c.pt hX)).obj U) := by
  obtain ⟨i, Ui, _, _, ⟨e⟩⟩ :=
    exists_stage_smallEtaleModel_of_qcqs B Dg c hX hc haff hqc hqs U hUc hUq
  have : CompactSpace (Dg.obj (op i)).obj := hqc i
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  have eRep := (Sheaf.sheafifiedYonedaCompSheafPullbackIso
    (smallEtaleBaseChange B
      (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i)))
    (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (SmallEtale.topology B c.pt hX)).app Ui
  exact ⟨i, (Sheaf.sheafifiedYoneda (SmallEtale.topology B (Dg.obj (op i)).obj
    (Dg.obj (op i)).property)).obj Ui, isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B _ Ui,
    ⟨eRep ≪≫ (Sheaf.sheafifiedYoneda (SmallEtale.topology B c.pt hX)).mapIso e⟩⟩

end RepresentableEssSurj

end AlgebraicGeometry

end
