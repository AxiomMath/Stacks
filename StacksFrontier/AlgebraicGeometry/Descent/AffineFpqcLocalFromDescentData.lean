module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumCocycleDiagram
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge

/-!
# Affineness is fpqc local on the base, from effectivity of descent data alone

`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc` of
`StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal` is the conclusion of Stacks 041Z —
affineness of morphisms of algebraic spaces over `S` is fpqc local on the base — carrying the
named hypothesis `AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc`;
`StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent` discharges that hypothesis from
the fpqc sheaf condition for algebraic spaces, which is Stacks 0APL; and
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SeparatedAtlas`,
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentSizeBound` and
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge` reduce Stacks 0APL to Stacks
0APK, in two interchangeable shapes.

**This file composes that chain**, so that the conclusion of Stacks 041Z is available from a
single hypothesis in each of the shapes in which a prover might supply it: the fpqc sheaf
condition itself, the bespoke descent conclusion of Stacks 0APK, and effectivity of descent data
in the vocabulary of `AlgebraicGeometry.DescentDatum` — over a morphism of the site, over a
morphism of affine schemes, and over an arbitrary morphism of schemes. Nothing beyond that
hypothesis is used —
in particular the four other tags that Stacks 041Z cites in its proof, Stacks 0245, 02L5, 041Y
and 041J, are all discharged upstream — so these statements record, machine-checkably, that the
residue of Stacks 041Z in this development is Stacks 0APK and nothing else.

## Main definitions

There are no new definitions, structures or classes, and no new named hypothesis is coined.
Each of the hypotheses below is quoted from the declaration that consumes it, so that the
statements differ only in which already-recorded shape of the residue they take.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isSheaf_fpqc`: the conclusion of
  Stacks 041Z from Stacks 0APL, the fpqc sheaf condition for algebraic spaces over `S`.
* `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffectiveFpqcDescent_scheme`:
  the conclusion of Stacks 041Z from the bespoke descent conclusion that
  `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme` consumes.
* `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_descentDatum`:
  the conclusion of Stacks 041Z from effectivity of descent data of schemes relative to a
  surjective flat quasi-compact morphism between affine objects of the site, which is Stacks
  0APK in this repository's canonical vocabulary.
* `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_affine_indQuasiAffine`:
  the conclusion of Stacks 041Z from Stacks 0APK over an *affine* base — effectivity of every
  descent datum relative to a surjective flat quasi-compact morphism of affine schemes whose
  scheme over the source is ind-quasi-affine. **This is the one of the five that the reduction
  of Stacks 0APK in `StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue` can reach**,
  that reduction needing `[IsAffine S]` and `[IsAffine X]`.
* `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_indQuasiAffine`:
  the conclusion of Stacks 041Z from Stacks 0APK stated for an arbitrary surjective flat
  quasi-compact morphism of schemes, with ind-quasi-affineness of the scheme over the source
  as the only condition on the descent datum. This is the statement of the tag itself, for a
  one-member covering, and it mentions no part of the big fppf site.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_legs_of_restrictOpen`: **the conclusion of
  Stacks 0APL — not of Stacks 041Z — from the three obligations that remain of Stacks 0APK.**
  The fpqc sheaf condition for an algebraic space over `S`, from `hlegs`, `hrestrict` and
  `hglueing` alone, the coassociativity obligation of the earlier four-obligation reduction
  having been discharged.
* `AlgebraicGeometry.DescentDatum.isEffective_restrictOpen_and_isEffective_of_canonical`: the
  **inhabitation witness** for the last two of those three obligations — both hold for every
  canonical descent datum, so neither is an absurd condition.

## Implementation notes

*Why the fpqc sheaf condition cannot be avoided.* The source's own proof invokes it: having
descended the affine `X' → Z'` to an affine `Y → Z` and obtained the comparison isomorphism
`ψ : Z' ×_Z Y → X'`, it reads `ψ` as a section of `X` over `Z' ×_Z Y` and amalgamates it over
the one-member fpqc covering `{Z' ×_Z Y → Y}` by Stacks 0APL. The formalization reaches the
same point from the other side: in
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc` every step
but the last consumes only the sheaf conditions of *representable* presheaves, which are
unconditional at the fpqc topology by
`AlgebraicGeometry.BigFppfOver.isSheaf_fpqc_yoneda_obj`; the last step turns local bijectivity
of the comparison morphism into invertibility, and its *injectivity* half is likewise
unconditional, through `AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`. What is left is
the amalgamation of a compatible family on an fpqc covering, for the algebraic space
`X ×_Y h_a`. The covering in question is a one-member faithfully flat quasi-compact covering of
an affine object by an affine object, which is exactly the case to which
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isSheafFor_singleton_affine` reduces Stacks
0APL; so the hypothesis of the first statement below is not a convenient over-approximation of
what the argument needs, and weakening it to that single case would gain nothing.

*Why five statements and not one.* The five hypotheses are related by implications that are
already proved elsewhere, so each statement below is a corollary of the one before it. They are
all kept because they are the five shapes in which a proof of Stacks 0APK can arrive: a
scheme-theoretic descent conclusion in the shape the middle paragraph of Stacks 0APL produces
its input (the second), effectivity of a descent datum relative to a morphism of the site (the
third), effectivity of a descent datum relative to a morphism of *affine* schemes (the
fourth), effectivity of a descent datum relative to an arbitrary morphism of schemes (the
fifth), and — for a prover who closes Stacks 0APL by a route that does not pass through Stacks
0APK at all — the sheaf condition itself (the first).

Each statement is therefore strictly weaker than the one before it, the fifth most of all. The
fourth is the one this development can actually reach, because the reduction of Stacks 0APK in
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue` needs an affine base; the fifth is
kept because it is the only one whose hypothesis mentions no part of the big fppf site *and*
places no condition on the base: Stacks 0APK belongs to the chapter on more on groupoids, which
knows nothing of the site of Stacks 021R, so a proof of it will be stated for a morphism of
schemes. The three site-shaped hypotheses above would each need that proof to be re-expressed
before it could be used; the last two consume it as it stands.

*Why the last two statements are here and not in a file of their own.* They need both
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffective_affine_indQuasiAffine`, of
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge`, and
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen`, of
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumCocycleDiagram`, and this is the file which
already imports the first and has no importer of its own, so joining the two costs nothing
downstream. The second import is the only change to the five statements above.

*What the join measures.* The reduction of Stacks 0APK states its three obligations for one
descent datum with the affineness, flatness, surjectivity, quasi-compactness and
ind-quasi-affineness in scope as instances; the statement it has to feed quantifies over every
such morphism and datum with those as explicit arguments. That the obligations transport across
that change of quantification with no coercion is what the join records, and no search over
names can see it.

*Nothing is tagged.* Every statement here carries a hypothesis which no declaration of this
repository discharges, so none of them is Stacks 041Z or Stacks 0APL: a hypothesis-carrying
statement under the tag of an unconditional one would misreport the state of the development.
The tag belongs on the instance which Stacks 041Z states, once Stacks 0APK is proved; at
that point each of these is one application away from it.

## References

* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- **The conclusion of Stacks 041Z from Stacks 0APL.** If every algebraic space over `S` is a
sheaf for the fpqc topology of the big fppf category over `S`, then affineness of morphisms of
algebraic spaces over `S` is fpqc local on the base.

This is `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc` with its named hypothesis
discharged by `AlgebraicGeometry.Space.isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc`. -/
theorem isAffineHom_isLocalAtTarget_fpqc_of_isSheaf_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hAPL : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      Presheaf.IsSheaf
        (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck F) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  isAffineHom_isLocalAtTarget_fpqc B S hS
    (isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc B S hS hAPL)

/-- **The conclusion of Stacks 041Z from the bespoke shape of Stacks 0APK.** Suppose that for
every surjective flat quasi-compact morphism `f : T' ⟶ T` between affine objects of the big
fppf site of `S`, every chart base change of an algebraic space along a compatible section of it
over `T'` descends to a scheme over `T`, in the shape the middle paragraph of Stacks 0APL
consumes. Then affineness of morphisms of algebraic spaces over `S` is fpqc local on the base.

This is `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isSheaf_fpqc` with its
hypothesis discharged by
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme`. -/
theorem isAffineHom_isLocalAtTarget_fpqc_of_isEffectiveFpqcDescent_scheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hAPK : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      ∀ (T T' : BigFppfOver B S hS) (f : T' ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      Surjective ((BigFppfOver.toScheme B S hS).map f) →
      Flat ((BigFppfOver.toScheme B S hS).map f) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) →
      ∀ (U V : BigFppfOver B S hS) (u : yoneda.obj U ⟶ F) (q : V ⟶ U) (p : V ⟶ T')
      (c : yoneda.obj T' ⟶ F), IsPullback (yoneda.map q) (yoneda.map p) u c →
      Surjective ((BigFppfOver.toScheme B S hS).map p) →
      Etale ((BigFppfOver.toScheme B S hS).map p) →
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) →
      IsIndQuasiAffineHom ((BigFppfOver.toScheme B S hS).map p) →
      yoneda.map (pullback.fst f f) ≫ c = yoneda.map (pullback.snd f f) ≫ c →
      ∃ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ (BigFppfOver.toScheme B S hS).obj T)
        (α₀ : pullback ((BigFppfOver.toScheme B S hS).map f) w₀ ≅
          (BigFppfOver.toScheme B S hS).obj V),
        α₀.hom ≫ (BigFppfOver.toScheme B S hS).map p =
            pullback.fst ((BigFppfOver.toScheme B S hS).map f) w₀ ∧
          pullback.fst (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀)
                (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀) ≫
              α₀.hom ≫ (BigFppfOver.toScheme B S hS).map q =
            pullback.snd (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀)
                (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀) ≫
              α₀.hom ≫ (BigFppfOver.toScheme B S hS).map q) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  isAffineHom_isLocalAtTarget_fpqc_of_isSheaf_fpqc B S hS
    fun hF => hF.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme (hAPK hF)

/-- **The conclusion of Stacks 041Z from Stacks 0APK.** Suppose that every descent datum of
schemes relative to a surjective flat quasi-compact morphism between affine objects of the big
fppf site of `S`, whose scheme over the source is surjective, étale, separated and
ind-quasi-affine, is effective. Then affineness of morphisms of algebraic spaces over `S` is
fpqc local on the base.

The hypothesis is Stacks 0APK, restricted to the case its own proof reduces to by Stacks 02W3
and further restricted to the data that the proof of Stacks 0APL produces; it is therefore
weaker than that tag. This is
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isSheaf_fpqc` with its hypothesis
discharged by
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffective_descentDatum`. -/
theorem isAffineHom_isLocalAtTarget_fpqc_of_isEffective_descentDatum
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hAPK : ∀ (T T' : BigFppfOver B S hS) (f : T' ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      Surjective ((BigFppfOver.toScheme B S hS).map f) →
      Flat ((BigFppfOver.toScheme B S hS).map f) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) →
      ∀ D : DescentDatum ((BigFppfOver.toScheme B S hS).map f),
        Surjective D.over.hom → Etale D.over.hom →
        _root_.AlgebraicGeometry.IsSeparated D.over.hom →
        IsIndQuasiAffineHom D.over.hom → DescentData.IsEffective D) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  isAffineHom_isLocalAtTarget_fpqc_of_isSheaf_fpqc B S hS
    fun hF => hF.isSheaf_fpqc_of_isEffective_descentDatum hAPK

/-- **The conclusion of Stacks 041Z from Stacks 0APK over an affine base.** Suppose that every
descent datum of schemes relative to a surjective flat quasi-compact morphism `g : T' ⟶ T` of
*affine* schemes, whose scheme over `T'` is ind-quasi-affine, is effective. Then affineness of
morphisms of algebraic spaces over `S` is fpqc local on the base.

This is the statement of this family that the reduction of Stacks 0APK in
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue` can actually reach, and it is the
one to use. That reduction derives effectivity from four named obligations under the instance
hypotheses `[IsAffine S]`, `[IsAffine X]`, `[Flat f]`, `[Surjective f]`, `[QuasiCompact f]` and
`[IsIndQuasiAffineHom D.over.hom]`, which is the case Stacks 02W3 reduces the tag to; so the
hypothesis below is its universally quantified conclusion, verbatim, and
`fun g _ _ _ _ _ D _ ↦ D.isEffective_of_unitCoassoc_of_preimage_of_restrictOpen hkey
hpreimage hrestrict hglueing` discharges it the moment those four obligations are proved.

It sits strictly between the two statements around it. Its hypothesis is stronger than that of
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_descentDatum`, since
it must deliver effectivity without being told that `D.over.hom` is surjective, étale and
separated, and from a morphism of schemes rather than of the site; and it is weaker than that
of `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_indQuasiAffine`,
which demands effectivity over an arbitrary base. The statement below is therefore stronger
than the next one, and the next one follows from it by discarding the two affineness
arguments — but the next one is kept, because it is Stacks 0APK as the source states it.

The hypothesis is not vacuous: the family it quantifies over is inhabited, by
`AlgebraicGeometry.exists_isAffine_descentDatum_isIndQuasiAffineHom`. No tag is carried, for
the reason given in the module documentation; and nothing here closes anything, because the
last of the four obligations is Stacks 0AP4, which this repository does not prove. -/
theorem isAffineHom_isLocalAtTarget_fpqc_of_isEffective_affine_indQuasiAffine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hAPK : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T), IsAffine T → IsAffine T' →
      Surjective g → Flat g → QuasiCompact g →
      ∀ D : DescentDatum g, IsIndQuasiAffineHom D.over.hom → DescentData.IsEffective D) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  isAffineHom_isLocalAtTarget_fpqc_of_isEffective_descentDatum B S hS
    fun _ _ f hT hT' hs hfl hqc D _ _ _ hiqa =>
      hAPK ((BigFppfOver.toScheme B S hS).map f) hT hT' hs hfl hqc D hiqa

/-- **The conclusion of Stacks 041Z from Stacks 0APK as that tag states it.** Suppose that
every descent datum of schemes relative to a surjective flat quasi-compact morphism of schemes,
whose scheme over the source is ind-quasi-affine, is effective. Then affineness of morphisms of
algebraic spaces over `S` is fpqc local on the base.

The hypothesis is Stacks 0APK for a one-member covering: ind-quasi-affineness of the scheme
over the source is the only condition it places on the descent datum, and it quantifies over
every surjective flat quasi-compact morphism of schemes rather than over the morphisms of the
big fppf site of `S`. It is therefore stronger than the hypothesis of
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_descentDatum`, and
this statement is correspondingly weaker; it is stated because it is the form in which a proof
of Stacks 0APK, which is about schemes alone, will be available. -/
theorem isAffineHom_isLocalAtTarget_fpqc_of_isEffective_indQuasiAffine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hAPK : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T), Surjective g → Flat g → QuasiCompact g →
      ∀ D : DescentDatum g, IsIndQuasiAffineHom D.over.hom → DescentData.IsEffective D) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  isAffineHom_isLocalAtTarget_fpqc_of_isEffective_descentDatum B S hS
    fun _ _ f _ _ hs hfl hqc D _ _ _ hiqa =>
      hAPK ((BigFppfOver.toScheme B S hS).map f) hs hfl hqc D hiqa

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.DescentDatum

/-- **The last two obligations of Stacks 0APK hold for every canonical descent datum.** Let
`g : T' ⟶ T` be a surjective flat quasi-compact morphism of affine schemes and let `D` be the
canonical descent datum of a scheme over `T`. Then

* the conclusion of the obligation `hrestrict` of
  `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` holds for `D` — every
  invariant open of its scheme, restricted to which `D` is effective; and
* the conclusion of the obligation `hglueing` of that statement holds for `D`, since `D` is
  effective outright.

The two conclusions are
`AlgebraicGeometry.DescentData.isEffective_restrictOpen_canonical` and
`AlgebraicGeometry.DescentDatum.isEffective_canonical`; the hypothesis `hD` naming `D` as a
canonical datum is what makes them applicable, and both controls confirm it is used (dropping
`hD`, or negating either conclusion, fails to elaborate).

*Why this is stated at all, given that its proof is two applications.* The statement, not the
proof, is the content: it is the two obligation bodies verbatim, and it exhibits data satisfying
them. No automated check detects a theorem made vacuous by an unsatisfiable hypothesis,
and the hypotheses `hrestrict` and `hglueing` of
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_legs_of_restrictOpen` below are long enough
that their satisfiability is not evident by inspection. The witness offered elsewhere for those
statements —
`AlgebraicGeometry.exists_isAffine_descentDatum_isIndQuasiAffineHom` — shows only that the
*family quantified over* is inhabited; this shows that the *conditions asked of its members* are
met by a geometrically described family, namely all canonical data. The two families do meet:
the datum that witness exhibits is itself a canonical datum, as its proof shows. This says
nothing about `hlegs`, whose body is an equality of two subsets of a spectrum and for which no
witness is exhibited here. -/
theorem isEffective_restrictOpen_and_isEffective_of_canonical {T T' : Scheme.{u}} {g : T' ⟶ T}
    {D : DescentDatum g} [IsAffine T] [IsAffine T'] [Flat g] [Surjective g] [QuasiCompact g]
    (hD : ∃ U₀ : Over T, D = (DescentDatum.canonical g).obj U₀) :
    (∀ (E : Set D.over.left)
      [Algebra ↥Γ(T, ⊤) ↥Γ(T', ⊤)] [Algebra ↥Γ(T, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(T, ⊤) ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      (hRA : CommRingCat.ofHom (algebraMap ↥Γ(T, ⊤) ↥Γ(T', ⊤)) = g.appTop)
      (hRC : CommRingCat.ofHom (algebraMap ↥Γ(T, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        (D.over.hom ≫ g).appTop ≫ D.over.left.topToSubset E)
      (hAC : CommRingCat.ofHom (algebraMap ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        D.over.hom.appTop ≫ D.over.left.topToSubset E)
      [QuasiSeparatedSpace D.over.left] {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
      (h₁ : (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E))
      (h₂ : (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E))
      (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(T, ⊤) ↥Γ(T', ⊤)
          ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
      (_hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
            (ModuleCat.descentInvariants ↥Γ(T, ⊤) ↥Γ(T', ⊤)
              ↥(D.over.left.sectionsRingOnSubset E)
              (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
            ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
            (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
          Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
        subsetΓSpecImage D.over.left E (W : Set D.over.left)),
      DescentData.IsEffective (D.restrictOpen W hWinv)) ∧
    ((∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) →
      DescentData.IsEffective D) := by
  obtain ⟨U₀, rfl⟩ := hD
  refine ⟨?_, fun _ => DescentDatum.isEffective_canonical g U₀⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W hWinv _ _ _
  exact DescentData.isEffective_restrictOpen_canonical g U₀ W hWinv

end AlgebraicGeometry.DescentDatum

namespace AlgebraicGeometry.IsAlgebraicSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}}
variable {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The conclusion of Stacks 0APL from the three remaining obligations of Stacks 0APK.**
Suppose that for every surjective flat quasi-compact morphism `g : T' ⟶ T` of affine schemes and
every descent datum `D` relative to `g` whose scheme over `T'` is ind-quasi-affine, the three
obligations `hlegs`, `hrestrict` and `hglueing` of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` hold. Then every algebraic
space over `S` is a sheaf for the fpqc topology of the big fppf category over `S`.

This is the *existence* half of Stacks 0APL reduced to those three obligations: the uniqueness
half is unconditional already, as `AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`. The
proof is
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffective_affine_indQuasiAffine` fed by
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen`, so the whole content is
that the obligations survive the change of quantification; the elaborator checks the quotation.

The three hypotheses are byte-identical to those of
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_legs_of_restrictOpen`, so one
supplier of them discharges both this statement and the conclusion of Stacks 041Z.

`hglueing` is [Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4). `hrestrict` is
asked only at the named transition algebra
`AlgebraicGeometry.DescentDatum.descentAlgebraTransition`, not at an arbitrary subalgebra
carrying a pushout square: that weaker shape cannot be discharged, because every route to it
needs the subalgebra to be syntactically the invariants, and the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsProjections` say so.

None of the three is vacuously satisfied. The family quantified over is inhabited, by
`AlgebraicGeometry.exists_isAffine_descentDatum_isIndQuasiAffineHom`; and the conclusions of
`hrestrict` and `hglueing` are met by every canonical descent datum, by
`AlgebraicGeometry.DescentDatum.isEffective_restrictOpen_and_isEffective_of_canonical`, so
neither asks for something absurd. No such witness is offered for `hlegs`.

**This is not Stacks 0APL and carries no tag**, since all three hypotheses are open; the tag
belongs on the eventual unconditional sheaf condition whose only hypothesis is `hF`. -/
theorem isSheaf_fpqc_of_legs_of_restrictOpen (hF : IsAlgebraicSpace B S hS F)
    (hlegs : ∀ {T T' : Scheme.{u}} {g : T' ⟶ T} (D : DescentDatum g) [IsAffine T]
      [IsAffine T'] [Flat g] [Surjective g] [QuasiCompact g]
      [IsIndQuasiAffineHom D.over.hom]
      (E : Set D.over.left) {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left))
      (_hE : E = ⋂ i, (U i : Set D.over.left)) (hEinv : D.IsTransitionInvariantSet E)
      (W : D.over.left.Opens) (_hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E),
      (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ g) g) E
            (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E
            (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
            (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)).hom)).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left) =
        (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd g (D.over.hom ≫ g)) E
            (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E) (Set.Subset.refl _))).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left))
    (hrestrict : ∀ {T T' : Scheme.{u}} {g : T' ⟶ T} (D : DescentDatum g) [IsAffine T]
      [IsAffine T'] [Flat g] [Surjective g] [QuasiCompact g]
      [IsIndQuasiAffineHom D.over.hom]
      (E : Set D.over.left)
      [Algebra ↥Γ(T, ⊤) ↥Γ(T', ⊤)] [Algebra ↥Γ(T, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(T, ⊤) ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      (hRA : CommRingCat.ofHom (algebraMap ↥Γ(T, ⊤) ↥Γ(T', ⊤)) = g.appTop)
      (hRC : CommRingCat.ofHom (algebraMap ↥Γ(T, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        (D.over.hom ≫ g).appTop ≫ D.over.left.topToSubset E)
      (hAC : CommRingCat.ofHom (algebraMap ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        D.over.hom.appTop ≫ D.over.left.topToSubset E)
      [QuasiSeparatedSpace D.over.left] {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
      (h₁ : (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E))
      (h₂ : (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E))
      (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(T, ⊤) ↥Γ(T', ⊤)
          ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
      (_hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
            (ModuleCat.descentInvariants ↥Γ(T, ⊤) ↥Γ(T', ⊤)
              ↥(D.over.left.sectionsRingOnSubset E)
              (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
            ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
            (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
          Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
        subsetΓSpecImage D.over.left E (W : Set D.over.left)),
      DescentData.IsEffective (D.restrictOpen W hWinv))
    (hglueing : ∀ {T T' : Scheme.{u}} {g : T' ⟶ T} (D : DescentDatum g) [IsAffine T]
      [IsAffine T'] [Flat g] [Surjective g] [QuasiCompact g]
      [IsIndQuasiAffineHom D.over.hom],
      (∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) →
      DescentData.IsEffective D) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F :=
  hF.isSheaf_fpqc_of_isEffective_affine_indQuasiAffine
    fun _g _hT _hT' _hs _hfl _hqc D _hiqa =>
      D.isEffective_of_legs_of_restrictOpen (hlegs D) (hrestrict D) (hglueing D)

end AlgebraicGeometry.IsAlgebraicSpace

end
