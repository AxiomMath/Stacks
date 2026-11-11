module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCoverGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal

/-!
# Separatedness along a universally injective flat cover (Stacks 0CPQ)

Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S` with composition
`h = f ≫ g`. **Stacks 0CPQ** asserts that if `f` is surjective, flat, locally of finite
presentation and universally injective, and if `h` is separated, then `g` is separated.

The route is the source's. The comparison 1-morphism

    i : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳

of **Stacks 050H** is a base change of `Δ_g` along `f × f : 𝒳 ×_𝒵 𝒳 ⟶ 𝒴 ×_𝒵 𝒴`, and `Δ_h`
factors as `Δ_f ≫ i` (**Stacks 050K**). Since `f` is universally injective, `Δ_f` is surjective
(**Stacks 0CPN**); properness of `Δ_h` then transfers to `i` by the two statements about the
image of a surjection — **Stacks 08AJ** for universal closedness and quasi-compactness and
**Stacks 05Z2** part (4) for separatedness — and properness of `Δ_g` descends from `i` along
`f × f` by **Stacks 0CPP**, which is separatedness of `g`.

## Main results

* `AlgebraicGeometry.Stack.prop_baseChangeNatTrans_of_relative`: a relative property of the
  first of two composable 1-morphisms representable by algebraic spaces is a property of the
  comparison morphism of the two representing algebraic spaces over a scheme-valued point of the
  last stack.
* `AlgebraicGeometry.Stack.isProper_of_isSurjective_universallyClosed_comp`: **Stacks 08AJ**
  and **Stacks 05Z2** part (4) transferred to the relative conditions of Properties of Stacks,
  Section 04XB: if `a : 𝒜 ⟶ ℬ` is surjective and universally closed, `a ≫ b` is proper and `b`
  is locally of finite type, then `b` is proper.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquareStacks` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_mapBaseSquareStacks`: the square of
  **Stacks 050H** read in the 2-category of algebraic stacks rather than in the 2-category of
  categories fibred in groupoids, which is the form the fppf descent of Stacks 0CPP consumes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isSeparated_comp_of_universallyInjective`
  is **Stacks 0CPQ**, with the three hypotheses discussed below; it is untagged, the corrected
  form being registered in the module
  `StacksFrontier.AlgebraicGeometry.Stacks.SeparationUniversallyInjectiveCoverCorrected`.

## Implementation notes

**The relative diagonal of `f` is assumed universally closed, and the statement of Stacks 0CPQ is
false without that assumption.** The source derives universal closedness of `Δ_f` from `Δ_f` being
a surjective section of the first projection of `𝒳 ×_𝒴 𝒳`. The reason one might give for algebraic
spaces, that a section is a monomorphism and a surjective monomorphism locally of finite type is a
closed immersion, is false: `Spec k ⊔ (𝔸¹ ∖ {0}) → 𝔸¹` is a surjective monomorphism locally of
finite type and not a closed immersion. For algebraic stacks the inference fails outright: `Δ_f` is
a monomorphism exactly when `f` is faithful, and `f` need not be. Concretely, let `S` be the affine
line over a field, let `H → S` be the affine line with the origin doubled, a group scheme over `S`
representing the pushforward of `ℤ/2` from the origin, and let `q : (ℤ/2)_S → H` be the
homomorphism carrying the two sections onto the two charts of `H`; it is étale and surjective, with
kernel `S ⊔ (S ∖ {0})`. Put `𝒳 = B(ℤ/2)_S`, `𝒴 = BH`, `𝒵 = S` and `f = Bq`. Then `f` is surjective,
flat and locally of finite presentation because `q` is, and universally injective because `Δ_f`
pulls back along the chart of `𝒳 ×_𝒴 𝒳` to the kernel of `q`, which is surjective over `S`. The
composition `h` is separated, since `Δ_h` pulls back to the finite morphism `(ℤ/2)_S → S`; but `g`
is not, since `Δ_g` pulls back to `H → S`, which is universally closed and of finite type yet not
separated, hence not proper. The same kernel `S ⊔ (S ∖ {0}) → S` is surjective and not closed, so
`Δ_f` is not universally closed: that is the one place the published argument fails, and assuming
it repairs the statement, universal closedness of `Δ_f` being strictly weaker than the properness
of `Δ_f` that separatedness of `f` asks for. As a condition on `f` alone the correction recorded in
the errata ledger is that `f` is separated: it suffices, and it is necessary, since `h` and `g`
separated force `f` separated (Stacks 050M (3)).

**Given the other hypotheses, the repaired statement is an equivalence.** Universal closedness of
`Δ_f` is also a consequence of separatedness of `g`: properness of `Δ_g` passes to its base change
`i` (**Stacks 045C**), so `i` is separated, and the composite `Δ_h = Δ_f ≫ i` being proper then
makes `Δ_f` proper by **Stacks 0CPT**. So the content of the theorem is the descent direction, and
a reader should not expect the hypothesis on `Δ_f` to be a side condition that the remaining
hypotheses might one day discharge.

**Local finite type of the relative diagonal is assumed, generically.** Properness in the sense
of Properties of Stacks, Section 04XB, includes being of finite type, and local finite type of
`Δ_g` does not descend along the surjection `Δ_f`: a surjective closed immersion of affine
schemes can have a source of finite type over the base and a target which is not. It is part (2)
of **Stacks 04XS**, which holds for every 1-morphism of algebraic stacks and rests on local
finite type of the isomorphism spaces of **Stacks 04XR**; that is not available here, so it is
assumed in the quantified form the tag has.

**That `f × f` is surjective, flat and locally of finite presentation is assumed, generically.**
This is the sentence "the right vertical arrow is surjective, flat, and locally of finite
presentation" of the source's proof, and it is what carries the three geometric hypotheses on `f`.
It is a permanence statement: `k × k : 𝒰 ×_𝒲 𝒰 ⟶ 𝒱 ×_𝒲 𝒱` is the composition of two base changes
of `k`, one factor at a time, so **Stacks 04ZU**, **Stacks 06PY** and **Stacks 06Q4** give the
three properties of each factor and they compose. What is not available is the comparison that
identifies the twice-pasted model of `𝒰 ×_𝒲 𝒰` — the apex produced by
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_pasteFst_of_isTwoFibreProduct`, on
which the two factors *are* projections of 2-fibre product squares over `k` with nothing to
recognise — with the canonical `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProduct`, together
with the transport of the three properties across the resulting 2-isomorphism. The comparison is
an equivalence by `AlgebraicGeometry.Stack.isEquivalence_homFunctor_preHom` and the transports
exist (`AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointsMap_of_isEquivalence` for
surjectivity and `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso` together with
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence` for the other two); what
is missing is the identification of the composite cover with
`AlgebraicGeometry.Stack.AlgebraicStacks.mapCospan` up to 2-isomorphism, which is the uniqueness
half of the universal property of `𝒱 ×_𝒲 𝒱`.

The two auxiliary results about relative properties are stated for 1-morphisms of categories
fibred in groupoids, which is where the base-change statements of Stacks 045C and 04XC live, and
the transfer of implications between properties of morphisms of algebraic spaces to the relative
conditions on 1-morphisms representable by algebraic spaces is pointwise over a scheme-valued
point of the target, as Properties of Stacks, Section 04XB, describes. Stacks 0CPP, by contrast,
is stated in the 2-category of algebraic stacks, which is why the square of Stacks 050H has to be
read there; the transfer is
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids`, the
2-category of algebraic stacks being a full sub-2-category. None of the auxiliary results carries
a tag: the two statements about images of surjections are tagged where they are proved, on
morphisms of algebraic spaces, and the square of Stacks 050H is tagged where it is built.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0CPP](https://stacks.math.columbia.edu/tag/0CPP)
* [Stacks Project, Tag 0CPQ](https://stacks.math.columbia.edu/tag/0CPQ)
* [Stacks Project, Tag 0CPT](https://stacks.math.columbia.edu/tag/0CPT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v w

/-- **A relative property of the first factor of a composite is a property of the comparison
morphism of representing algebraic spaces.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of
categories fibred in groupoids over the big fppf site of `S` with `f` representable by algebraic
spaces and satisfying the condition of Stacks 04XB for `P`, and fix a scheme-valued point `z` of
`𝒵` over `U` together with algebraic spaces `Fp`, `Gq` over `U` representing the base changes of
`f ≫ g` and of `g` along `z`. Then the morphism `Λ Fp ⟶ Λ Gq` induced by `f` has `P`.

Locality of `P` on the target reduces the claim to a scheme atlas of `Λ Gq`, and the base change
of the comparison morphism to a member of that atlas is an algebraic space representing a base
change of `f` along a scheme-valued point of `𝒴`. -/
theorem prop_baseChangeNatTrans_of_relative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u} .fppf B S hS)]
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hPf : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (U : BigFppfOver B S hS)
    (zz : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
    (hz : zz ⋙ 𝒵.val.p = Over.map U.hom)
    (Fp Gq : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hFp : IsAlgebraicSpace B U.left.1 U.left.2 Fp)
    (hGq : IsAlgebraicSpace B U.left.1 U.left.2 Gq)
    (E : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒵.val.p zz
        (CatFiberedInGroupoids.homFunctor (f ≫ g)))
      (presheafOfCategories (Fp ⋙ typeToCat)).p)
    (EG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒴.val.p 𝒵.val.p zz
        (CatFiberedInGroupoids.homFunctor g))
      (presheafOfCategories (Gq ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (baseChangeNatTrans U.hom zz f.hom.w E EG) :
      (⟨(relocalizePresheafFunctor U.hom).obj Fp,
          Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fp hFp⟩ :
        AlgebraicSpaces B S hS) ⟶
      ⟨(relocalizePresheafFunctor U.hom).obj Gq,
        Space.isAlgebraicSpace_relocalizePresheaf B S hS U Gq hGq⟩) := by
  have hΛGq := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Gq hGq
  obtain ⟨T, aa, hsurj, hetale⟩ := hΛGq.exists_atlas
  refine (Space.prop_iff_pullbackSnd_atlas.{u, u} B S hS P _ hsurj hetale).2 ?_
  obtain ⟨fib, c, y, hc, hy, ⟨Efib⟩⟩ :=
    exists_isPullback_baseChangeNatTrans U.hom zz f.hom.w E EG g.hom.w hz
      𝒳.property 𝒴.property 𝒵.property T.left T.hom aa
  obtain ⟨F', hF', ⟨E'⟩⟩ := hf (Over.mk T.hom) y hy
  have hfib : IsAlgebraicSpace B T.left.1 T.left.2 fib :=
    isAlgebraicSpace_of_iso B T.left.1 T.left.2 (isoOfEquivalenceOver Efib E') hF'
  have hΛfib := Space.isAlgebraicSpace_relocalizePresheaf B S hS (Over.mk T.hom) fib hfib
  have hPfib : P (ObjectProperty.homMk (relocalizeToYoneda T.hom fib) :
      (⟨(relocalizePresheafFunctor T.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (Over.mk T.hom), isAlgebraicSpace_yoneda B S hS (Over.mk T.hom)⟩) :=
    (Space.prop_relocalizeToYoneda_iff B S hS P (Over.mk T.hom) fib hfib).2
      (hPf (Over.mk T.hom) y hy fib hfib ⟨Efib⟩)
  have hsq : IsPullback
      (ObjectProperty.homMk c :
        (⟨(relocalizePresheafFunctor T.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Fp,
            Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fp hFp⟩)
      (ObjectProperty.homMk (relocalizeToYoneda T.hom fib) :
        (⟨(relocalizePresheafFunctor T.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      (ObjectProperty.homMk (baseChangeNatTrans U.hom zz f.hom.w E EG) :
        (⟨(relocalizePresheafFunctor U.hom).obj Fp,
            Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fp hFp⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩)
      (ObjectProperty.homMk aa :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hc
  rw [← P.cancel_left_of_respectsIso hsq.isoPullback.hom, hsq.isoPullback_hom_snd]
  exact hPfib

/-- **Properness of the image of a surjection, for the relative conditions of Properties of
Stacks, Section 04XB.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in
groupoids over the big fppf site of `S`, with `f` and `f ≫ g` representable by algebraic spaces.
If `f` is surjective and universally closed, `f ≫ g` is proper and `g` is locally of finite
type, then `g` is proper.

Over a scheme-valued point of `𝒵` the two representing algebraic spaces are compared by a
morphism which is surjective and universally closed, by
`AlgebraicGeometry.Stack.prop_baseChangeNatTrans_of_relative`; universal closedness and
quasi-compactness of the target then come from Stacks 08AJ and Stacks 040W and separatedness
from part (4) of Stacks 05Z2. -/
theorem isProper_of_isSurjective_universallyClosed_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hfg : IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom)
    (hfSurj : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsSurjective B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (hfUC : UniversallyClosed B S hS f)
    (hfgProper : IsProper B S hS (f ≫ g))
    (hgLFT : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒴.val.p 𝒵.val.p z
            (CatFiberedInGroupoids.homFunctor g))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsLocallyOfFiniteType B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    IsProper B S hS g := by
  intro U zz hz Fq hFq hE
  obtain ⟨EG⟩ := hE
  obtain ⟨Fp, hFp, ⟨E⟩⟩ := hfg U zz hz
  have hΛFp := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fp hFp
  have hΛFq := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fq hFq
  have hyon := isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)
  have hprRI : (Space.properProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hlftRI : (Space.locallyOfFiniteTypeProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hucFpqc : (Space.universallyClosedProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fpqc B S hS) :=
    Space.universallyClosed_isLocalAtTarget_fpqc B S hS
  have hucLT : (Space.universallyClosedProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fppf B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.precoverage.{u, u} .fpqc B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hmSurj : Space.IsSurjective B S hS (baseChangeNatTrans U.hom zz f.hom.w E EG) :=
    prop_baseChangeNatTrans_of_relative B S hS
      (Space.surjectiveMorphismProperty B S hS) f g hf hfSurj U zz hz Fp Fq hFp hFq E EG
  have hmUC : Space.UniversallyClosed B S hS (baseChangeNatTrans U.hom zz f.hom.w E EG) :=
    prop_baseChangeNatTrans_of_relative B S hS
      (Space.universallyClosedProperty B S hS) f g hf hfUC U zz hz Fp Fq hFp hFq E EG
  have hcomp : baseChangeNatTrans U.hom zz f.hom.w E EG ≫ relocalizeToYoneda U.hom Fq =
      relocalizeToYoneda U.hom Fp :=
    baseChangeNatTrans_comp_relocalizeToYoneda U.hom zz f.hom.w E EG
  have hPp : Space.IsProper B S hS (relocalizeToYoneda U.hom Fp) :=
    (Space.prop_relocalizeToYoneda_iff B S hS (Space.properProperty B S hS) U Fp hFp).2
      (hfgProper U zz hz Fp hFp ⟨E⟩)
  have hPlft : Space.IsLocallyOfFiniteType B S hS (relocalizeToYoneda U.hom Fq) :=
    (Space.prop_relocalizeToYoneda_iff B S hS (Space.locallyOfFiniteTypeProperty B S hS)
      U Fq hFq).2 (hgLFT U zz hz Fq hFq ⟨EG⟩)
  refine (Space.prop_relocalizeToYoneda_iff B S hS (Space.properProperty B S hS) U Fq hFq).1
    ⟨?_, ⟨hPlft, ?_⟩, ?_⟩
  · exact Space.isSeparated_of_isSurjective_of_universallyClosed B S hS hΛFp hΛFq hyon
      (baseChangeNatTrans U.hom zz f.hom.w E EG) (relocalizeToYoneda U.hom Fq)
      hmSurj hmUC (by rw [hcomp]; exact hPp.1)
  · exact Space.isQuasiCompact_of_comp_surjective B S hS hΛFp hΛFq hyon
      (baseChangeNatTrans U.hom zz f.hom.w E EG) (relocalizeToYoneda U.hom Fp)
      (relocalizeToYoneda U.hom Fq) hcomp.symm hmSurj hPp.2.1.2
  · exact Space.universallyClosed_of_isSurjective_comp B S hS hΛFp hΛFq hyon
      (baseChangeNatTrans U.hom zz f.hom.w E EG) (relocalizeToYoneda U.hom Fq)
      (by rw [hcomp]; exact hPp.2.2) hmSurj

namespace AlgebraicStacks

/-- **The square of Stacks 050H in the 2-category of algebraic stacks.** For 1-morphisms
`f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` of algebraic stacks over `S` this is the 2-commutative square

```text
  𝒳 ×_𝒴 𝒳  --- i --->  𝒳 ×_𝒵 𝒳
     |                    |
  fst ≫ f             f × f
     v                    v
     𝒴   --- Δ_g ----> 𝒴 ×_𝒵 𝒴
```

read in the 2-category of algebraic stacks of Stacks 03YP rather than in the 2-category of
categories fibred in groupoids, which is the form `AlgebraicGeometry.Stack`
`.hasRelativeProperty_iff_of_fppfCoverStack` consumes. -/
noncomputable def mapBaseSquareStacks (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    Bicategory.TwoCommSq (mapCospan B S hS f f g) (relativeDiagonal B S hS g) where
  pt := twoFibreProduct B S hS f f
  fst := mapBase B S hS f f g
  snd := (twoFibreProductSquare B S hS f f).fst ≫ f
  iso := Bicategory.InducedBicategory.isoMk (mapBaseSquare B S hS f f g).iso

/-- **Stacks 050H in the 2-category of algebraic stacks: `i` is a base change of `Δ_g`.** The
underlying square of categories fibred in groupoids is a 2-fibre product, and the 2-category of
algebraic stacks is a full sub-2-category. -/
noncomputable def isTwoFibreProduct_mapBaseSquareStacks (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    Bicategory.IsTwoFibreProduct (mapBaseSquareStacks B S hS f g) :=
  isTwoFibreProduct_of_toCatFiberedInGroupoids B S hS _
    (isTwoFibreProduct_mapBaseSquare B S hS f f g)

/-- **Stacks 0CPQ, with universal closedness of `Δ_f` assumed.** Let `f : 𝒳 ⟶ 𝒴` and
`g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If `f` is surjective, flat, locally of
finite presentation and universally injective, if the relative diagonal of `f` is universally
closed, and if `f ≫ g` is separated, then `g` is separated.

The relative diagonal of `f` is surjective by Stacks 0CPN, so properness of `Δ_{f ≫ g} = Δ_f ≫ i`
gives properness of the comparison 1-morphism `i : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳`; and `i` is a base change
of `Δ_g` along `f × f`, so properness of `Δ_g` descends by Stacks 0CPP.

Given the other hypotheses, universal closedness of `Δ_f` is also a consequence of the
conclusion, so the implication below is in fact an equivalence; and local finite type of a
relative diagonal (part (2) of Stacks 04XS) and the three properties of `f × f` are assumed. See
the implementation notes.

It carries no tag: the module
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationUniversallyInjectiveCoverCorrected` removes the
last two assumptions, and the registration of Stacks 0CPQ sits on the corrected form
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSeparated_of_isSeparated_comp_of_universallyInjective_of_isSeparated_diagonal`; the statement as
written is false, see
`Stacks.Examples.not_forall_isSeparated_of_isSeparated_comp_of_universallyInjective`. -/
theorem isSeparated_of_isSeparated_comp_of_universallyInjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfSurj : Stack.IsSurjective B S hS f)
    (hfFlat : IsFlat B S hS f)
    (hfLfp : IsLocallyOfFinitePresentation B S hS f)
    (hfUI : Stack.UniversallyInjective B S hS f)
    (hh : IsSeparated B S hS (f ≫ g))
    (hdiagUC : Stack.UniversallyClosed B S hS (relativeDiagonal B S hS f).hom)
    (hdiagLFT : ∀ {𝒰 𝒱 : Stack.AlgebraicStacks.{u, w} B S hS} (k : 𝒰 ⟶ 𝒱)
      (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ (twoFibreProduct B S hS k k).val.val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS k k).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒰.val.val.p
            (twoFibreProduct B S hS k k).val.val.p y
            (CatFiberedInGroupoids.homFunctor (relativeDiagonal B S hS k).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsLocallyOfFiniteType B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (hCospan : ∀ {𝒰 𝒱 𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (k : 𝒰 ⟶ 𝒱) (l : 𝒱 ⟶ 𝒲),
      Stack.IsSurjective B S hS k → IsFlat B S hS k →
      IsLocallyOfFinitePresentation B S hS k →
      Stack.IsSurjective B S hS (mapCospan B S hS k k l) ∧
        IsFlat B S hS (mapCospan B S hS k k l) ∧
        IsLocallyOfFinitePresentation B S hS (mapCospan B S hS k k l)) :
    IsSeparated B S hS g := by
  have hrepf := Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hreph :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS (f ≫ g)
  have hrepg := Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS g
  have hdec : Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val (f ≫ g).hom =
      (relativeDiagonal B S hS f).hom ≫ (mapBase B S hS f f g).hom :=
    congrArg (fun k => k.hom) (relativeDiagonal_comp B S hS f g)
  have hreph' : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val (f ≫ g).hom).hom := hreph
  have hh' : Stack.IsProper B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val (f ≫ g).hom) := hh
  rw [hdec] at hreph' hh'
  have hiLFT := Stack.relativeProperty_baseChange.{u, u, u + 1} B S hS
    (Space.locallyOfFiniteTypeProperty B S hS) 𝒴.val
    (twoFibreProduct B S hS g g).val (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val
    (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)
    (mapCospan B S hS f f g).hom (mapBaseSquare B S hS f f g)
    (isTwoFibreProduct_mapBaseSquare B S hS f f g) (hdiagLFT g)
  have hdfSurj := (Stack.pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
      (relativeDiagonal B S hS f) hrepf).1
    (Stack.isSurjective_relativeDiagonal_of_universallyInjective B S hS f hfUI)
  have hiProper := Stack.isProper_of_isSurjective_universallyClosed_comp B S hS
    (relativeDiagonal B S hS f).hom (mapBase B S hS f f g).hom
    hrepf hreph' hdfSurj hdiagUC hh' hiLFT
  have hBC : (Space.properProperty B S hS).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have hLT : (Space.properProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fppf B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  obtain ⟨hcSurj, hcFlat, hcLfp⟩ := hCospan f g hfSurj hfFlat hfLfp
  refine (Stack.hasRelativeProperty_iff_of_fppfCoverStack B S hS
    (Space.properProperty B S hS) (relativeDiagonal B S hS g) (mapCospan B S hS f f g) hrepg
    hcSurj hcFlat hcLfp (mapBaseSquareStacks B S hS f g)
    (isTwoFibreProduct_mapBaseSquareStacks B S hS f g)).2 ⟨?_, hiProper⟩
  exact Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒴.val
    (twoFibreProduct B S hS g g).val (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val
    (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)
    (mapCospan B S hS f f g).hom (mapBaseSquare B S hS f f g)
    (isTwoFibreProduct_mapBaseSquare B S hS f f g) hrepg

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
