module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentChaoticSite
public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineRingedTopos
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCoarsening
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# Quasi-coherent modules and affines

Let `S` be a scheme and let `τ` be one of the Zariski, étale, smooth, syntomic or fppf
topologies. An *affine site* of `S` is the full subcategory of affine objects of one of the
small or big `τ`-sites of `S`, carrying the restriction of the sheaf of global functions
`T ↦ Γ(T, 𝒪_T)` as its structure sheaf. For a sheaf of modules `𝓕` on such a site and a
morphism `U ⟶ U'` of it, extension of scalars along `𝒪(U') ⟶ 𝒪(U)` produces a base-change map
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)`.

Two sufficient conditions for `𝓕` to be quasi-coherent on the ringed site, in the sense of
Modules on Sites, Definition 03DL(6), are proved: that all of those base-change maps are
isomorphisms, and that `𝓕` is the restriction of a quasi-coherent module on the ambient
`τ`-site. These are the quasi-coherence conjunct of condition (2) of Stacks 0GZX, for `τ`
Zariski and étale, and of conditions (2)–(6) of Stacks 0GZV, deduced from condition (1) and
from condition (3), respectively condition (7), of those statements.

## Main definitions

* `AlgebraicGeometry.RingedSite.chaotic`: a ringed site with its topology replaced by the
  chaotic one, the structure sheaf unchanged.
* `AlgebraicGeometry.affineRingedSite`: a subsite with the restriction of a structure sheaf,
  read as a ringed site.
* `AlgebraicGeometry.smallZariskiRingedSite`,
  `AlgebraicGeometry.smallEtaleRingedSite` and
  `AlgebraicGeometry.smallAffineZariskiRingedSite`,
  `AlgebraicGeometry.smallAffineEtaleRingedSite`: the two small sites of Stacks 0GZX and their
  affine subsites, as ringed sites. The structure sheaves of the last two are those of
  `AlgebraicGeometry.SmallAffineZariski.ringedTopos` and
  `AlgebraicGeometry.SmallAffineEtale.ringedTopos`. The étale one is the ringed site of
  `AlgebraicGeometry.smallEtaleRingedSite`, which the library already carries, repackaged
  reducibly so that its projections reduce for instance search.
* `AlgebraicGeometry.bigZariskiOverRingedSite` and its étale, smooth, syntomic and fppf
  counterparts, together with `AlgebraicGeometry.bigAffineZariskiRingedSite` and its four
  counterparts: the five big sites of Stacks 0GZV and their affine subsites, as ringed sites.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`: on an arbitrary ringed
  site, a sheaf of modules all of whose base-change maps are isomorphisms is quasi-coherent.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite`: the restriction of a
  quasi-coherent module along the inclusion of a cocontinuous dense subsite, over the restricted
  structure sheaf, is quasi-coherent.
* `AlgebraicGeometry.smallAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso` and
  `AlgebraicGeometry.smallAffineZariski_isQuasicoherentOnSite_restriction`, with their étale
  counterparts: Stacks 0GZX, conditions (1) and (3) each imply the quasi-coherence conjunct of
  condition (2).
* `AlgebraicGeometry.bigAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso` and
  `AlgebraicGeometry.bigAffineZariski_isQuasicoherentOnSite_restriction`, with their four
  counterparts: Stacks 0GZV, conditions (1) and (7) each imply the quasi-coherence conjunct of
  each of conditions (2)–(6).

## Implementation notes

Neither core argument uses the geometry of the affine sites, nor any property of the topology,
so each is proved once for an arbitrary ringed site and instantiated seven times. The inputs to
the first are Stacks 0GZN, `Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso`, which
characterises quasi-coherence by the base-change maps when the topology is chaotic, and
`SheafOfModules.IsQuasicoherentOnSite.of_coarser`, which carries quasi-coherence from a coarser
topology to a finer one. The base-change map of the chaotic reading of a ringed site is the
base-change map of the site itself, because both are the adjoint transpose of the same
restriction map, so the two inputs compose with no comparison. The input to the second is
`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`, whose hypothesis on the localizations
of the inclusion is supplied by `Stacks.Sites.overPost_isDenseSubsite`.

The structure sheaf of an affine site is the literal restriction of the structure sheaf of the
ambient site along the inclusion of the affine objects, which is what the source says it is; for
the two small affine sites this is the structure sheaf already used for Stacks 0GZW, as recorded
by `AlgebraicGeometry.smallAffineZariskiRingedSite_O` and its étale counterpart. The sections of
the structure sheaves stay in the universe `u` of the schemes, rather than being raised as in
`AlgebraicGeometry.uliftRingSheaf`, because nothing here compares sheaves of modules across two
universes.

## Coverage limits

Condition (2) of Stacks 0GZX and conditions (2)–(6) of Stacks 0GZV each conjoin the sheaf
condition with quasi-coherence. Only the quasi-coherence conjunct is proved *here*: the
statements below take `𝓕` already given as a sheaf of modules. For Stacks 0GZV the two
conjuncts are put together, for a presheaf of modules and at the same universe `u` of the
sections, in `StacksFrontier.AlgebraicGeometry.Descent.BigAffineSitePresheafConditions`.

For Stacks 0GZX the sheaf conjunct and its converse are both supplied, at `τ` Zariski and
étale, in `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesSheaf`: the
sheaf conjunct of condition (2) by
`AlgebraicGeometry.smallAffineZariski_isSheaf_of_baseChange_isIso` and its étale counterpart,
and condition (1) back from condition (2) by
`AlgebraicGeometry.smallAffineZariski_canonicalMap_isIso_of_isQuasicoherentOnSite` and its
étale counterpart, so conditions (1) and (2) of Stacks 0GZX are equivalent. Those proofs
follow Stacks 0H04 rather than the route of the source and need no part of Descent,
Proposition 03DX.

Condition (4) of Stacks 0GZX implies condition (1), at `τ` Zariski and étale, by
`AlgebraicGeometry.smallAffineZariski_isIso_restrictionBaseChange_associatedModule` and its
étale counterpart in
`StacksFrontier.AlgebraicGeometry.Descent.SmallAffineSiteAssociatedModuleCartesian`, which is the
affine base-change isomorphism of Stacks 02KH, the same input the five big affine instances of
Stacks 0GZV (8) ⇒ (1) use. The *uniqueness* of `𝒢` in condition (4) at `τ = étale` is
`AlgebraicGeometry.fullyFaithfulSmallAffineEtaleAssociatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesUnique`: the functor
`𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` is fully faithful, being Stacks 0GN7 at `τ = étale` followed by
the Comparison Lemma for sheaves of modules on the dense subsite of affine objects. Its
*existence* at `τ = étale` is
`AlgebraicGeometry.smallAffineEtale_essImage_associatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesExists`, which also gives
condition (3) from condition (2) there, so that conditions (1)–(4) of Stacks 0GZX are all
equivalent at `τ = étale`. Of those, only the existence of `𝒢` uses Descent, Proposition 03DX —
clause (2) of it, at `τ = étale`, which this development has unconditionally.

The same two statements hold at `τ = Zariski`: the uniqueness of `𝒢` is
`AlgebraicGeometry.fullyFaithfulSmallAffineZariskiAssociatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiUnique`, Stacks 0GN7
at `τ = Zariski` for the functor of Remark 03FH followed by the same Comparison Lemma, and its
existence is `AlgebraicGeometry.smallAffineZariski_essImage_associatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists`, which also
gives condition (3) from condition (2) there. That route uses no part of Descent,
Proposition 03DX: `𝒢` is the restriction of the Comparison Lemma's preimage of `𝓕` along the
morphism of ringed sites of Remark 03FH, proved quasi-coherent in the sense of Stacks 01BD
directly. So conditions (1)–(4) of Stacks 0GZX are equivalent at both of the topologies the tag
quantifies over, and nothing of the tag is left open.

For Stacks 0GZV the sheaf conjunct is supplied at all five topologies, in
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCartesianSheaf`, by
`AlgebraicGeometry.bigAffineFppf_isSheaf_of_cartesian` and its Zariski, étale, smooth and
syntomic counterparts. Each is faithfully flat descent, Stacks 023M, run on the coverings of
`(Aff/S)_τ`: such a covering is a finite family of affine schemes over an affine scheme whose
members are open immersions, étale, smooth, syntomic or flat morphisms as `τ` is the Zariski,
étale, smooth, syntomic or fppf topology, and all five of those are flat.

Condition (8) of Stacks 0GZV implies condition (1): that is
`AlgebraicGeometry.bigAffineFppf_isIso_restrictionBaseChange_associatedModule` and its four
counterparts in `StacksFrontier.AlgebraicGeometry.Descent.AffineSiteAssociatedModuleCartesian`,
which use the affine base-change isomorphism of Stacks 02KH and no part of Descent,
Proposition 03DX.

Each of conditions (2)–(6) of Stacks 0GZV implies condition (1) back, so **conditions (1) and
(2)–(6) are equivalent**: that is
`AlgebraicGeometry.bigAffineFppf_isIso_canonicalMap_of_isQuasicoherentOnSite` and its four
counterparts in `StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteQuasicoherentCartesian`,
packaged as the five equivalences
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_iff_canonicalMap_isIso` and counterparts,
for a sheaf of modules — the sheaf conjunct of (2)–(6) being carried by the type there, as for
Stacks 0GZX. Those converses do not go through the descent step that proves them on a small
site, `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover`, which requires the ring
map of the morphism being descended along to be flat: on a small étale or Zariski site every
morphism is, while on `(Aff/S)_τ` the morphisms are arbitrary morphisms of affine schemes over
`S` and are not. That step is used for the *flat* morphisms only, and the general case is
obtained by reflecting along a faithfully flat base change with
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_faithfullyFlat_family`.

Conditions (7) and (8) of Stacks 0GZV are equivalent at `τ = fppf`, and the uniqueness of `𝒢`
in condition (8) holds there: that is
`AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_iff_isRestrictedAssociatedModule`
and `AlgebraicGeometry.fullyFaithfulBigAffineFppfAssociatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteAssociatedModuleUnique`. The uniqueness is
Stacks 0GN7 for the big site followed by the Comparison Lemma for sheaves of modules on the
dense subsite of affine objects, and uses no part of Descent, Proposition 03DX; (7) ⇒ (8) is the
essential surjectivity half of Descent, Proposition 03DX (1), which this development has
unconditionally at `τ = fppf`,
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`.

The implication **condition (1) ⇒ (7)** of Stacks 0GZV, equivalently (6) ⇒ (7), is covered at
`τ = fppf`, by
`AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_of_canonicalMap_isIso` in
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteModuleComparisonLemma`. It has two inputs.
Quasi-coherence transports *to* the affine subsite by
`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction` above and **back** by
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect` in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesReflect`, so each of the
seven restriction statements of this file is an equivalence. The other input, a sheaf of modules
on the big site restricting to the given cartesian `𝓕` at all, is
`AlgebraicGeometry.bigAffineFppf_exists_moduleLift`: restriction of sheaves of modules to the
affine objects is essentially surjective at the universe `u` of the module sections, so the
Comparison Lemma for sheaves of modules holds there.

(Two remarks on where the difficulty does *not* lie. First, the reflection of quasi-coherence
does not ask for the full Comparison Lemma at the raised module universe in which a global
presentation lives, only for its *full faithfulness* half there, which holds at every universe of
module sections —
`Stacks.DenseSubsiteModules.fullyFaithful_moduleRestrictionRaised` — and the presentation is
transported back without ever recognising anything as lying in the image of the restriction. Second,
on the existence side, the limits over
`CategoryTheory.StructuredArrow X (BigAffineFppf.inclusion B S hS).op` exist in
`AddCommGrpCat.{u}` and not only in `AddCommGrpCat.{u + 1}`, even though those categories have
their objects in `Type (u + 1)`:
`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` asks only for the index category to
be *essentially* `u`-small, which it is, by `AlgebraicGeometry.essentiallySmall_bigAffineFppf`
and local `u`-smallness of `(Sch/S)_fppf`. Nothing has to be descended from `u + 1`, and the
raising of the sections in `AlgebraicGeometry.uliftRingSheaf` for Stacks 0GZU is a convenience
of that statement — it keeps a free section universe `w` — not a necessity.)

Conditions (7) and (8) at the four coarser `τ` are covered too, in
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCoarserAssociatedModule`, by the
`SiteKind`-indexed
`AlgebraicGeometry.bigAffine_isRestrictionOfQuasicoherentOf_of_canonicalMap_isIso`,
`AlgebraicGeometry.bigAffine_isIso_canonicalMapOf_of_isRestrictionOfQuasicoherentOf`,
`AlgebraicGeometry.bigAffine_isRestrictedAssociatedModuleOf_of_canonicalMap_isIso` and
`AlgebraicGeometry.bigAffine_isRestrictionOfQuasicoherentOf_iff_isRestrictedAssociatedModuleOf`,
so that conditions (1), (7) and (8) are equivalent at every one of the five topologies.
(The input is that the affine inclusion is a dense subsite inclusion not only for the five
independently chosen big sites of this file but also for `AlgebraicGeometry.BigAffineFppf B S hS`
with the inherited coarser topologies: `AlgebraicGeometry.BigAffineFppf.inclusion_isDenseSubsite`.)

**Stacks 0GZX is fully covered**: its four conditions are equivalent at `τ = étale` and at
`τ = Zariski`, which are the two topologies it quantifies over. Beyond what is proved here, the
étale half is
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesSheaf` ((1) ⇔ (2)),
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesUnique` (the uniqueness of
`𝒢`) and `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesExists` (its
existence, and (3)); the Zariski half is that same (1) ⇔ (2), together with
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiUnique` and
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists`. At each
topology conditions (2) ⇔ (3) and (2) ⇔ (4) are also recorded as equivalences of categories of
quasi-coherent modules, which is how the source states them.

The two topologies differ only in bookkeeping. The small affine `τ`-site of this file sits inside
`AlgebraicGeometry.SmallEtale B S hS` resp. `AlgebraicGeometry.SmallZariski B S hS`, and the
associated-module functor of Descent, Definition 03DU (4) there is the pullback along the
morphism of ringed sites of Remark 03FH; Stacks 0GN7 for those two functors is
`AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'` and
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh`. (0GN7 at `τ = Zariski` is
also registered for the reading of the small Zariski site as `S.Opens`, where `𝓕ᵃ = 𝓕` by
`SheafOfModules.pullbackId`; that reading is about a coefficient sheaf isomorphic to the one
Definition 03DU (2) names rather than equal to it, so it is not the statement this file's affine
Zariski site needs.)

(Three remarks on what is and is not needed. `S_Zar` carries a pullback-form associated-module
functor, `AlgebraicGeometry.SmallZariski.associatedModule`. At `τ = étale` the reflection of
quasi-coherence along the Comparison Lemma at the raised module universe where a global
presentation lives is unavailable, but it is not needed — the counit argument of Descent,
Proposition 03DX (2) consumes quasi-coherence only through the restriction to the affine subsite.
At `τ = Zariski` the existence of `𝒢` is not blocked: the structure map of that site is available
in `CommRingCat`-valued form, `AlgebraicGeometry.smallZariskiCommStructureIso`, and the
opacity of the chosen object over an open — the inverse of the equivalence of Stacks 020X picks
it by `Classical.choice` — obstructs nothing, since the comparison `ΓIsoTop` exists at an
arbitrary object of the site.)

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁ u₂ v₂

namespace AlgebraicGeometry

/-- A ringed site read with the chaotic topology, for which every presheaf is a sheaf. The
underlying category and the structure sheaf are unchanged. -/
public noncomputable def RingedSite.chaotic (X : RingedSite.{u, v, w}) : RingedSite.{u, v, w} where
  C := X.C
  J := ⊥
  O := X.O.ofLE bot_le

/-- A subsite together with the restriction of a structure sheaf along its inclusion, read as a
ringed site. -/
@[reducible]
public noncomputable def affineRingedSite {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (i : C ⥤ D)
    [i.IsContinuous J K] (O : Sheaf K CommRingCat.{w}) : RingedSite.{u₁, v₁, w} where
  C := C
  J := J
  O := (i.sheafPushforwardContinuous CommRingCat.{w} J K).obj O

end AlgebraicGeometry

namespace Stacks.SheafOfModules

open AlgebraicGeometry

/-- **The core of condition (1) of Stacks 0GZX and 0GZV.** A sheaf of modules on a ringed site
whose base-change maps `F(V) ⊗_{𝒪(V)} 𝒪(U) ⟶ F(U)` are all isomorphisms is quasi-coherent in
the sense of Stacks 03DL(6). -/
public theorem isQuasicoherentOnSite_of_canonicalMap_isIso (X : RingedSite.{u, v, w})
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (h : ∀ ⦃U V : X.C⦄ (f : U ⟶ V), IsIso (canonicalMap X F f)) :
    F.IsQuasicoherentOnSite := by
  have hs : ∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{max u v w} := fun U =>
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (X.J.over U)).1
  have hw : ∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v w} := fun U =>
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (X.J.over U)
  have h0 : ((_root_.SheafOfModules.ofLE bot_le
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F).IsQuasicoherentOnSite :=
    (isQuasicoherent_iff_canonicalMap_isIso X.chaotic
      ((_root_.SheafOfModules.ofLE bot_le
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F) rfl).mpr fun _ _ f => h f
  exact _root_.SheafOfModules.IsQuasicoherentOnSite.of_coarser h0

/-- **The core of condition (3) of Stacks 0GZX and condition (7) of Stacks 0GZV.** The
restriction of a quasi-coherent sheaf of modules along the inclusion of a cocontinuous dense
subsite, taken over the restricted structure sheaf, is quasi-coherent. -/
public theorem isQuasicoherentOnSite_restrictionAlongSubsite {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (i : C ⥤ D) [i.Full] [i.Faithful] [i.IsDenseSubsite J K] [i.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (M : _root_.SheafOfModules.{w} R)
    (hM : M.IsQuasicoherentOnSite) :
    ((_root_.SheafOfModules.pushforward.{w} (F := i)
      (S := (i.sheafPushforwardContinuous RingCat.{w} J K).obj R) (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  have _hc : ∀ X : C,
      (Over.post (X := X) i).IsContinuous (J.over X) (K.over (i.obj X)) := fun X =>
    have := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) i X
    inferInstance
  isQuasicoherentOnSite_restriction i R M hM

end Stacks.SheafOfModules

namespace AlgebraicGeometry

/-! ### The two small affine sites of Stacks 0GZX -/

/-- The small Zariski site of `S` with its sheaf of global functions `T ↦ Γ(T, 𝒪_T)` as
structure sheaf, read as a ringed site. -/
public noncomputable abbrev smallZariskiRingedSite (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} where
  C := SmallZariski B S hS
  J := SmallZariski.topology B S hS
  O := (SmallZariski.ringedTopos B S hS).O

/-- The small affine Zariski site of `S` with the restriction of the sheaf of global functions
of the small Zariski site as its structure sheaf. -/
public noncomputable abbrev smallAffineZariskiRingedSite (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (SmallAffineZariski.topology B S hS) (smallZariskiRingedSite B S hS).J
    (SmallAffineZariski.inclusion B S hS) (smallZariskiRingedSite B S hS).O

/-- The structure sheaf of `smallAffineZariskiRingedSite` is the one used for Stacks 0GZW. -/
public theorem smallAffineZariskiRingedSite_O (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (smallAffineZariskiRingedSite B S hS).O = (SmallAffineZariski.ringedTopos B S hS).O :=
  rfl

/-- The small affine étale site of `S` with the restriction of the sheaf of global functions of
the small étale site as its structure sheaf. -/
public noncomputable abbrev smallAffineEtaleRingedSite (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (SmallAffineEtale.topology B S hS) (SmallEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (SmallEtale.ringedTopos B S hS).O

/-- The structure sheaf of `smallAffineEtaleRingedSite` is the one used for Stacks 0GZW. -/
public theorem smallAffineEtaleRingedSite_O (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (smallAffineEtaleRingedSite B S hS).O = (SmallAffineEtale.ringedTopos B S hS).O :=
  rfl

/-- **Stacks 0GZX, Zariski case.** A sheaf of modules on the small affine Zariski site of `S`
whose base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are all isomorphisms is quasi-coherent on
the ringed site `(S_{affine, Zar}, 𝒪_affine)`. -/
@[stacks 0GZX "(1) ⇒ (2) at τ = Zariski, quasi-coherence conjunct of (2)"]
public theorem smallAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineZariskiRingedSite B S hS).O))
    (h : ∀ ⦃U V : SmallAffineZariski B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineZariskiRingedSite B S hS) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

/-- **Stacks 0GZX, Zariski case.** The restriction to the small affine Zariski site of `S` of a
quasi-coherent module on the ringed site `(S_Zar, 𝒪)` is quasi-coherent on
`(S_{affine, Zar}, 𝒪_affine)`. -/
@[stacks 0GZX "(3) ⇒ (2) at τ = Zariski, quasi-coherence conjunct of (2)"]
public theorem smallAffineZariski_isQuasicoherentOnSite_restriction
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallZariskiRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := SmallAffineZariski.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallZariskiRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineZariskiRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

/-- **Stacks 0GZX, étale case.** A sheaf of modules on the small affine étale site of `S` whose
base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are all isomorphisms is quasi-coherent on the
ringed site `(S_{affine, étale}, 𝒪_affine)`. -/
@[stacks 0GZX "(1) ⇒ (2) at τ = étale, quasi-coherence conjunct of (2)"]
public theorem smallAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite B S hS).O))
    (h : ∀ ⦃U V : SmallAffineEtale B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineEtaleRingedSite B S hS) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

/-- **Stacks 0GZX, étale case.** The restriction to the small affine étale site of `S` of a
quasi-coherent module on the ringed site `(S_étale, 𝒪)` is quasi-coherent on
`(S_{affine, étale}, 𝒪_affine)`. -/
@[stacks 0GZX "(3) ⇒ (2) at τ = étale, quasi-coherence conjunct of (2)"]
public theorem smallAffineEtale_isQuasicoherentOnSite_restriction
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := SmallAffineEtale.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

/-! ### The five big affine sites of Stacks 0GZV -/

/-- The big Zariski site over `S` with its sheaf of global functions as structure sheaf, read as
a ringed site. -/
public noncomputable abbrev bigZariskiOverRingedSite (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} where
  C := BigZariskiOver B S hS
  J := BigZariskiOver.topology B S hS
  O := commStructureSheaf S (BigZariskiOver.topology B S hS) (Over.post B.inclusion)
    (BigZariskiOver.structure_isSheaf B S hS)

/-- The big affine Zariski site of `S` with the restriction of the sheaf of global functions as
its structure sheaf. -/
public noncomputable abbrev bigAffineZariskiRingedSite (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (BigAffineZariski.topology B S hS) (bigZariskiOverRingedSite B S hS).J
    (BigAffineZariski.inclusion B S hS) (bigZariskiOverRingedSite B S hS).O

/-- The big étale site over `S` with its sheaf of global functions as structure sheaf, read as a
ringed site. -/
public noncomputable abbrev bigEtaleOverRingedSite (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} where
  C := BigEtaleOver B S hS
  J := BigEtaleOver.topology B S hS
  O := commStructureSheaf S (BigEtaleOver.topology B S hS) (Over.post B.inclusion)
    (BigEtaleOver.structure_isSheaf B S hS)

/-- The big affine étale site of `S` with the restriction of the sheaf of global functions as
its structure sheaf. -/
public noncomputable abbrev bigAffineEtaleRingedSite (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (BigAffineEtale.topology B S hS) (bigEtaleOverRingedSite B S hS).J
    (BigAffineEtale.inclusion B S hS) (bigEtaleOverRingedSite B S hS).O

/-- The big smooth site over `S` with its sheaf of global functions as structure sheaf, read as
a ringed site. -/
public noncomputable abbrev bigSmoothOverRingedSite (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) : RingedSite.{u + 1, u, u} where
  C := BigSmoothOver B S hS
  J := BigSmoothOver.topology B S hS
  O := commStructureSheaf S (BigSmoothOver.topology B S hS) (Over.post (ObjectProperty.ι _))
    (BigSmoothOver.structure_isSheaf B S hS)

/-- The big affine smooth site of `S` with the restriction of the sheaf of global functions as
its structure sheaf. -/
public noncomputable abbrev bigAffineSmoothRingedSite (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (BigAffineSmooth.topology B S hS) (bigSmoothOverRingedSite B S hS).J
    (BigAffineSmooth.inclusion B S hS) (bigSmoothOverRingedSite B S hS).O

/-- The big syntomic site over `S` with its sheaf of global functions as structure sheaf, read
as a ringed site. -/
public noncomputable abbrev bigSyntomicOverRingedSite (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} where
  C := BigSyntomicOver B S hS
  J := BigSyntomicOver.topology B S hS
  O := commStructureSheaf S (BigSyntomicOver.topology B S hS) (Over.post B.inclusion)
    (BigSyntomicOver.structure_isSheaf B S hS)

/-- The big affine syntomic site of `S` with the restriction of the sheaf of global functions as
its structure sheaf. -/
public noncomputable abbrev bigAffineSyntomicRingedSite (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (BigAffineSyntomic.topology B S hS) (bigSyntomicOverRingedSite B S hS).J
    (BigAffineSyntomic.inclusion B S hS) (bigSyntomicOverRingedSite B S hS).O

/-- The big fppf site over `S` with its sheaf of global functions as structure sheaf, read as a
ringed site. -/
public noncomputable abbrev bigFppfOverRingedSite (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} where
  C := BigFppfOver B S hS
  J := BigFppfOver.topology B S hS
  O := commStructureSheaf S (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (BigFppfOver.structure_isSheaf B S hS)

/-- The big affine fppf site of `S` with the restriction of the sheaf of global functions as its
structure sheaf. -/
public noncomputable abbrev bigAffineFppfRingedSite (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (BigAffineFppf.topology B S hS) (bigFppfOverRingedSite B S hS).J
    (BigAffineFppf.inclusion B S hS) (bigFppfOverRingedSite B S hS).O

/-- **Stacks 0GZV, condition (2).** A sheaf of modules on `(Aff/S)_Zar` whose base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are all isomorphisms is quasi-coherent on the ringed site
`((Aff/S)_Zar, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (2), quasi-coherence conjunct of (2)"]
public theorem bigAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineZariskiRingedSite B S hS).O))
    (h : ∀ ⦃U V : BigAffineZariski B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineZariskiRingedSite B S hS) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

/-- **Stacks 0GZV, condition (2).** The restriction to `(Aff/S)_Zar` of a quasi-coherent module
on the ringed site `((Sch/S)_Zar, 𝒪)` is quasi-coherent on `((Aff/S)_Zar, 𝒪_Aff)`. -/
@[stacks 0GZV "(7) ⇒ (2) at τ = Zariski, quasi-coherence conjunct of (2)"]
public theorem bigAffineZariski_isQuasicoherentOnSite_restriction
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := BigAffineZariski.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineZariskiRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

/-- **Stacks 0GZV, condition (3).** A sheaf of modules on `(Aff/S)_étale` whose base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are all isomorphisms is quasi-coherent on the ringed site
`((Aff/S)_étale, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (3), quasi-coherence conjunct of (3)"]
public theorem bigAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineEtaleRingedSite B S hS).O))
    (h : ∀ ⦃U V : BigAffineEtale B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineEtaleRingedSite B S hS) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

/-- **Stacks 0GZV, condition (3).** The restriction to `(Aff/S)_étale` of a quasi-coherent
module on the ringed site `((Sch/S)_étale, 𝒪)` is quasi-coherent on
`((Aff/S)_étale, 𝒪_Aff)`. -/
@[stacks 0GZV "(7) ⇒ (3) at τ = étale, quasi-coherence conjunct of (3)"]
public theorem bigAffineEtale_isQuasicoherentOnSite_restriction
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := BigAffineEtale.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineEtaleRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

/-- **Stacks 0GZV, condition (4).** A sheaf of modules on `(Aff/S)_smooth` whose base-change
maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are all isomorphisms is quasi-coherent on the ringed site
`((Aff/S)_smooth, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (4), quasi-coherence conjunct of (4)"]
public theorem bigAffineSmooth_isQuasicoherentOnSite_of_canonicalMap_isIso
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSmoothRingedSite B S hS).O))
    (h : ∀ ⦃U V : BigAffineSmooth B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineSmoothRingedSite B S hS) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

/-- **Stacks 0GZV, condition (4).** The restriction to `(Aff/S)_smooth` of a quasi-coherent
module on the ringed site `((Sch/S)_smooth, 𝒪)` is quasi-coherent on
`((Aff/S)_smooth, 𝒪_Aff)`. -/
@[stacks 0GZV "(7) ⇒ (4) at τ = smooth, quasi-coherence conjunct of (4)"]
public theorem bigAffineSmooth_isQuasicoherentOnSite_restriction
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := BigAffineSmooth.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSmoothRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

/-- **Stacks 0GZV, condition (5).** A sheaf of modules on `(Aff/S)_syntomic` whose base-change
maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are all isomorphisms is quasi-coherent on the ringed site
`((Aff/S)_syntomic, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (5), quasi-coherence conjunct of (5)"]
public theorem bigAffineSyntomic_isQuasicoherentOnSite_of_canonicalMap_isIso
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSyntomicRingedSite B S hS).O))
    (h : ∀ ⦃U V : BigAffineSyntomic B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineSyntomicRingedSite B S hS) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

/-- **Stacks 0GZV, condition (5).** The restriction to `(Aff/S)_syntomic` of a quasi-coherent
module on the ringed site `((Sch/S)_syntomic, 𝒪)` is quasi-coherent on
`((Aff/S)_syntomic, 𝒪_Aff)`. -/
@[stacks 0GZV "(7) ⇒ (5) at τ = syntomic, quasi-coherence conjunct of (5)"]
public theorem bigAffineSyntomic_isQuasicoherentOnSite_restriction
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := BigAffineSyntomic.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSyntomicRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

/-- **Stacks 0GZV, condition (6).** A sheaf of modules on `(Aff/S)_fppf` whose base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are all isomorphisms is quasi-coherent on the ringed site
`((Aff/S)_fppf, 𝒪_Aff)`. -/
@[stacks 0GZV "(1) ⇒ (6), quasi-coherence conjunct of (6)"]
public theorem bigAffineFppf_isQuasicoherentOnSite_of_canonicalMap_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O))
    (h : ∀ ⦃U V : BigAffineFppf B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineFppfRingedSite B S hS) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

/-- **Stacks 0GZV, condition (6).** The restriction to `(Aff/S)_fppf` of a quasi-coherent module
on the ringed site `((Sch/S)_fppf, 𝒪)` is quasi-coherent on `((Aff/S)_fppf, 𝒪_Aff)`. -/
@[stacks 0GZV "(7) ⇒ (6) at τ = fppf, quasi-coherence conjunct of (6)"]
public theorem bigAffineFppf_isQuasicoherentOnSite_restriction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := BigAffineFppf.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

end AlgebraicGeometry

end
