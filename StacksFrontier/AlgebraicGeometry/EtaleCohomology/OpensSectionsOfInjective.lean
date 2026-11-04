module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpensAcyclicityTransport

/-!
# The degree-zero gluing condition holds for an injective abelian sheaf

Let `X` be a scheme and `F` an abelian sheaf on the one-universe model
`Stacks.EtaleCohomology.MayerVietoris.Site X` of its small étale site. If `F` is an *injective*
object of the category of abelian sheaves then for every pair of open subschemes `U`, `V` of `X`
every section of `F` over `U ⊓ V` is the difference of a section over `U` and a section over `V`
— the degree-zero gluing condition
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.SectionsSub`, equivalently
`Stacks.EtaleCohomology.OpensAcyclicity.SectionsDifference`.

The reason is the Mayer--Vietoris sequence of [Stacks, Tag 0A50]: the degree-zero difference map
`H⁰(U, F) ⊞ H⁰(V, F) ⟶ H⁰(U ⊓ V, F)` is followed in that sequence by the connecting map into
`H¹(U ⊔ V, F)`, so it is surjective as soon as that degree-one group vanishes; and the cohomology
of an injective abelian sheaf *over an object* vanishes in every positive degree, being an
`Ext`-group into an injective object.

## Main results

* `Stacks.Cohomology.subsingleton_H'_succ_of_injective` — **the cohomology of an injective
  abelian sheaf over an object of a site vanishes in positive degrees.** Mathlib has this for
  global cohomology `CategoryTheory.Sheaf.H` as an instance; `CategoryTheory.Sheaf.H'` is the
  `Ext`-group out of the free abelian sheaf on a representable, so the same argument applies to
  it, with no terminal object needed.
* `Stacks.EtaleCohomology.MayerVietoris.sectionsSub_of_subsingleton_cohomologySup` — the
  degree-zero gluing condition for `U`, `V` from the vanishing of `H¹(U ⊔ V, F)`. This is the
  converse direction of
  `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.surjective_fromBiprod_of_sectionsSub`,
  read through exactness of the Mayer--Vietoris sequence at `H⁰(U ⊓ V, F)`.
* `Stacks.EtaleCohomology.MayerVietoris.sectionsSub_of_injective` and
  `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_injective` — the degree-zero
  gluing condition for an injective abelian sheaf, for *every* pair of opens.
* `Stacks.EtaleCohomology.MayerVietoris.injective_mayerVietorisRestrict` — an injective abelian
  sheaf on `AlgebraicGeometry.Scheme.smallEtaleTopology` stays injective when read on the
  one-universe model, restriction along the dense subsite inclusion `CategoryTheory.AsSmall.down`
  being an equivalence of sheaf categories.
* `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_mayerVietorisRestrict_of_injective`
  — the two previous statements combined: the gluing condition, in the shape the hypothesis `hsub`
  of `OpensAcyclicity.subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference` is
  stated in, for an injective abelian sheaf given on Mathlib's small étale site.
* `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective` — **the gluing
  condition passes along a morphism of abelian sheaves surjective on sections over the
  intersection**, and `sectionsDifference_of_surjective_of_injective` with an injective source.
  The degree-zero half of [Stacks, Tag 09YQ] is exactly such a surjectivity statement for the
  legs of the colimit presentation, which are morphisms of abelian sheaves on the limit, so this
  is the step that turns it into `hsub`.
* `Stacks.EtaleCohomology.OpensAcyclicity.opensSectionsMap` and `opensSectionsMap_restrict` — the
  map on sections over an open subscheme induced by a morphism of abelian sheaves, and its
  compatibility with restriction. The degree-zero companion of
  `Stacks.EtaleCohomology.MayerVietoris.opensCohomologyMap`.
* `Stacks.EtaleCohomology.OpensAcyclicity.opensSectionsRestrict_self`,
  `opensSectionsRestrict_restrict` and `opensSectionsRestrict_injective_of_eq` — restriction of
  sections along an inclusion of opens is the identity on an open, is functorial, and is injective
  when the inclusion is an equality.
* `Stacks.EtaleCohomology.OpensAcyclicity.exists_sectionsDifference_preimage_of_leg` — **the image
  of a single section under the leg is a difference**, which is
  `sectionsDifference_preimage_of_surjective` with the quantifier over sections moved outside the
  data, and the form a filtered colimit supplies.

## Why this is wanted

In [Stacks, Tag 09YQ] the sheaf on the limit is `colim_i f_i^{-1}F_i` for a system `(F_i)` of
abelian sheaves on the levels, and the vanishing half of the proof is applied to a system all of
whose `F_i` are **injective**. The gluing condition for the colimit sheaf over a pair of opens of
the limit is to be obtained from the gluing condition for the `F_i` over a pair of opens of a
level; the statements here are that level half, and they hold for every pair of opens of the
level, with no quasi-compactness and no affineness.

What they do not supply, and what the rest of `hsub` is: the descent of a section of the colimit
sheaf over `U ⊓ V` to a level — that is the degree-zero statement of [Stacks, Tag 09YQ], and in
the form `sectionsDifference_of_surjective` consumes it, the surjectivity of the leg on sections
over `U ⊓ V` — together with the descent of the pair of opens `(U, V)` itself to a common level, so
that the splitting is available there. Neither is proved here.

## References

* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed (SectionsSub)
open Stacks.EtaleCohomology.StrictlyHenselian (opensCohomology)

universe w' v u

namespace Stacks.Cohomology

/-- **The cohomology of an injective abelian sheaf over an object vanishes in positive degrees.**
`CategoryTheory.Sheaf.H'` is the `Ext`-group out of the free abelian sheaf on the representable
presheaf of the object, and an `Ext`-group in a positive degree into an injective object
vanishes. No terminal object and no hypothesis on the site are needed. -/
public theorem subsingleton_H'_succ_of_injective {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (n : ℕ) (T : C) :
    Subsingleton (Sheaf.H'.{w'} F (n + 1) T) :=
  subsingleton_of_forall_eq 0 fun x => Ext.eq_zero_of_injective x

end Stacks.Cohomology

namespace Stacks.EtaleCohomology.MayerVietoris

variable {X : Scheme.{u}} (F : Sheaf (topology X) AddCommGrpCat.{u + 1})

/-- **The degree-zero gluing condition from the vanishing of the degree-one cohomology over the
union.** If `H¹(U ⊔ V, F)` vanishes then every section of `F` over `U ⊓ V` is the difference of
the restrictions of a section over `U` and a section over `V`.

The Mayer--Vietoris sequence of [Stacks, Tag 0A50] is exact at its term `H⁰(U ⊓ V, F)`, whose
incoming map is the degree-zero difference map and whose outgoing map is the connecting map into
`H¹(U ⊔ V, F)`; the connecting map kills everything because its target vanishes, so the
difference map is surjective. Writing an element of the biproduct as a pair of sections is
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply`.

This is the converse of
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.surjective_fromBiprod_of_sectionsSub`. -/
public theorem sectionsSub_of_subsingleton_cohomologySup (U V : X.Opens)
    (h : Subsingleton ((opensCohomology F 1).obj (op (U ⊔ V)))) :
    SectionsSub F U V := by
  intro τ
  have hE := (cohomologySequence_exact F U V 0 1 rfl).exact' 1 2 3
  rw [ShortComplex.ab_exact_iff] at hE
  obtain ⟨z, hz⟩ := hE τ (by exact @Subsingleton.elim _ h _ _)
  have hz' : fromBiprod F U V 0 z = τ := hz
  obtain ⟨p, hp⟩ : ∃ p, (AddCommGrpCat.biprodIsoProd (F.H' 0 (square X U V).X₂)
      (F.H' 0 (square X U V).X₃)).inv p = z :=
    ⟨(AddCommGrpCat.biprodIsoProd (F.H' 0 (square X U V).X₂)
        (F.H' 0 (square X U V).X₃)).hom z, by
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
      rfl⟩
  have key : (opensCohomology F 0).map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op p.1 -
      (opensCohomology F 0).map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op p.2 =
        fromBiprod F U V 0 z := by
    rw [← hp]
    exact (GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply
      (square X U V) F p.1 p.2).symm
  exact ⟨p.1, p.2, key.trans hz'⟩

/-- **The degree-zero gluing condition holds for an injective abelian sheaf**, for every pair of
open subschemes: the degree-one cohomology over the union vanishes by
`Stacks.Cohomology.subsingleton_H'_succ_of_injective`. -/
public theorem sectionsSub_of_injective [Injective F] (U V : X.Opens) :
    SectionsSub F U V :=
  sectionsSub_of_subsingleton_cohomologySup F U V
    (Stacks.Cohomology.subsingleton_H'_succ_of_injective (topology X) F 0
      ((opensToSite X).obj (U ⊔ V)))

/-- **An injective abelian sheaf on Mathlib's small étale site stays injective on the
one-universe model.** Restriction along `CategoryTheory.AsSmall.down` is an equivalence of
abelian sheaf categories, that functor exhibiting the model as a dense subsite, and an
equivalence preserves injective objects. -/
public theorem injective_mayerVietorisRestrict
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective G] :
    Injective ((mayerVietorisRestrict X).obj G) :=
  ((AsSmall.down : Site X ⥤ X.Etale).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology X) X.smallEtaleTopology).injective_obj_of_injective inferInstance

end Stacks.EtaleCohomology.MayerVietoris

namespace Stacks.EtaleCohomology.OpensAcyclicity

variable {X : Scheme.{u}}

/-- **The degree-zero gluing condition, as a condition on sections, holds for an injective
abelian sheaf.** This is `Stacks.EtaleCohomology.MayerVietoris.sectionsSub_of_injective` read
through `Stacks.EtaleCohomology.OpensAcyclicity.sectionsSub_iff_sectionsDifference`. -/
public theorem sectionsDifference_of_injective
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) [Injective F] (U V : X.Opens) :
    SectionsDifference F U V :=
  (sectionsSub_iff_sectionsDifference F U V).1 (MayerVietoris.sectionsSub_of_injective F U V)

/-- **The degree-zero gluing condition for an injective abelian sheaf given on Mathlib's small
étale site**, in the shape the hypothesis `hsub` of
`subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference` is stated in: the sheaf is
read on the one-universe model, where it stays injective by
`Stacks.EtaleCohomology.MayerVietoris.injective_mayerVietorisRestrict`. No quasi-compactness of `U`
and no affineness of `V` are needed. -/
public theorem sectionsDifference_mayerVietorisRestrict_of_injective
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective F] (U V : X.Opens) :
    SectionsDifference ((MayerVietoris.mayerVietorisRestrict X).obj F) U V :=
  have := MayerVietoris.injective_mayerVietorisRestrict F
  sectionsDifference_of_injective _ U V

/-! ### Restriction of sections along an inclusion of opens -/

/-- Restriction of sections along the inclusion of an open subscheme into itself is the
identity. -/
public theorem opensSectionsRestrict_self
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) {U : X.Opens} (h : U ≤ U) :
    opensSectionsRestrict F h = 𝟙 _ := by
  show F.obj.map ((MayerVietoris.opensToSite X).map (homOfLE h)).op = 𝟙 _
  rw [show homOfLE h = 𝟙 U from rfl, CategoryTheory.Functor.map_id, op_id,
    CategoryTheory.Functor.map_id]

/-- **Restriction of sections is functorial**: restricting a section from `C` to `B` and then from
`B` to `A` restricts it from `C` to `A`.

This is the functoriality of the presheaf underlying `F` along the inclusion of the opens into the
small étale site, read on an element. Any two proofs of `A ≤ C` give the same restriction map, so
a composite of restrictions may be matched against a single one whose `≤` is spelled
differently. -/
public theorem opensSectionsRestrict_restrict
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) {A B C : X.Opens}
    (h₁ : A ≤ B) (h₂ : B ≤ C) (x : ToType (opensSections F C)) :
    opensSectionsRestrict F h₁ (opensSectionsRestrict F h₂ x) =
      opensSectionsRestrict F (h₁.trans h₂) x := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp,
    ← CategoryTheory.Functor.map_comp, homOfLE_comp]

/-- **Restriction of sections along an inclusion of opens that happens to be an equality is
injective**, being the identity. This is how a section over an open is recovered from its
restriction to a smaller open with the *same* preimage along a morphism of schemes. -/
public theorem opensSectionsRestrict_injective_of_eq
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) {U V : X.Opens} (h : U ≤ V)
    (hUV : U = V) : Function.Injective (ConcreteCategory.hom (opensSectionsRestrict F h)) := by
  subst hUV
  rw [opensSectionsRestrict_self]
  exact fun _ _ hxy => hxy

/-! ### Carrying the gluing condition along a morphism of sheaves -/

/-- **The map on sections over an open subscheme induced by a morphism of abelian sheaves.**
This is the degree-zero companion of
`Stacks.EtaleCohomology.MayerVietoris.opensCohomologyMap`. -/
public abbrev opensSectionsMap {F G : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}}
    (θ : F ⟶ G) (U : X.Opens) : opensSections F U ⟶ opensSections G U :=
  θ.hom.app (op ((MayerVietoris.opensToSite X).obj U))

/-- A morphism of abelian sheaves commutes with restriction of sections along an inclusion of
open subschemes. -/
public theorem opensSectionsMap_restrict
    {F G : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}} (θ : F ⟶ G)
    {U V : X.Opens} (h : U ≤ V) (x : ToType (opensSections F V)) :
    opensSectionsRestrict G h (opensSectionsMap θ V x) =
      opensSectionsMap θ U (opensSectionsRestrict F h x) :=
  (θ.hom.naturality_apply ((MayerVietoris.opensToSite X).map (homOfLE h)).op x).symm

/-- **The degree-zero gluing condition passes along a morphism of abelian sheaves that is
surjective on sections over the intersection.** If every section of `G` over `U ⊓ V` is the image
of a section of `F` there, and the condition holds for `F`, then it holds for `G`: the images
under `θ` of the two sections splitting a preimage split the section itself, `θ` commuting with
restriction.

This is the step by which the gluing condition for the colimit sheaf of [Stacks, Tag 09YQ] is to
be obtained from the gluing condition at a level: the legs of the colimit presentation are
morphisms of abelian sheaves on the limit, and the degree-zero statement of that tag is exactly
the surjectivity hypothesis here, over a quasi-compact quasi-separated object. -/
public theorem sectionsDifference_of_surjective
    {F G : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}} (θ : F ⟶ G) (U V : X.Opens)
    (hF : SectionsDifference F U V)
    (hsurj : Function.Surjective (ConcreteCategory.hom (opensSectionsMap θ (U ⊓ V)))) :
    SectionsDifference G U V := by
  intro τ
  obtain ⟨σ, hσ⟩ := hsurj τ
  obtain ⟨a, b, hab⟩ := hF σ
  refine ⟨opensSectionsMap θ U a, opensSectionsMap θ V b, ?_⟩
  rw [opensSectionsMap_restrict θ (inf_le_left : U ⊓ V ≤ U) a,
    opensSectionsMap_restrict θ (inf_le_right : U ⊓ V ≤ V) b, ← map_sub, hab, hσ]

/-- `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective` for an **injective**
source: the gluing condition holds for every abelian sheaf whose sections over `U ⊓ V` are hit by
an injective one. No quasi-compactness of `U` and no affineness of `V` are needed. -/
public theorem sectionsDifference_of_surjective_of_injective
    {F G : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}} [Injective F] (θ : F ⟶ G)
    (U V : X.Opens)
    (hsurj : Function.Surjective (ConcreteCategory.hom (opensSectionsMap θ (U ⊓ V)))) :
    SectionsDifference G U V :=
  sectionsDifference_of_surjective θ U V (sectionsDifference_of_injective F U V) hsurj

/-! ### Carrying the gluing condition from a pair of opens to their preimages -/

/-- **The image of one section under the leg is a difference, from the gluing condition
upstairs.** Let `f : X ⟶ Y` be a morphism of schemes, `G` an abelian sheaf on the one-universe
model of the small étale site of `Y` and `𝒢` one on that of `X`, and let `leg` be a family of maps
from the sections of `G` over an open of `Y` to the sections of `𝒢` over its preimage, compatible
with restriction. If the gluing condition holds for `G` at `(U, V)` then for *every* section `σ`
of `G` over `U ⊓ V` the image `leg σ` is the difference of the restrictions of a section of `𝒢`
over `f ⁻¹ᵁ U` and one over `f ⁻¹ᵁ V`.

This is `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_preimage_of_surjective` with
the quantifier over the sections of `𝒢` moved *outside* the data: that theorem never uses its
surjectivity hypothesis anywhere but on the single section it is handed, so nothing of the
argument depends on one `f`, one `G` and one `leg` serving every section at once. A filtered
colimit supplies exactly the weaker thing — each section of `𝒢` is hit from *some* level, the
level depending on the section — and this is the form in which it is consumed; see
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective_opensLeg`. -/
public theorem exists_sectionsDifference_preimage_of_leg {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}}
    {𝒢 : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}}
    (leg : ∀ W : Y.Opens, opensSections G W ⟶ opensSections 𝒢 (f ⁻¹ᵁ W))
    (hleg : ∀ {W W' : Y.Opens} (h : W ≤ W') (x : ToType (opensSections G W')),
      opensSectionsRestrict 𝒢 (f.preimage_mono h) (leg W' x) =
        leg W (opensSectionsRestrict G h x))
    (U V : Y.Opens) (hG : SectionsDifference G U V)
    (σ : ToType (opensSections G (U ⊓ V))) :
    ∃ (a : ToType (opensSections 𝒢 (f ⁻¹ᵁ U))) (b : ToType (opensSections 𝒢 (f ⁻¹ᵁ V))),
      opensSectionsRestrict 𝒢 (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) a -
          opensSectionsRestrict 𝒢 (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V) b =
        leg (U ⊓ V) σ := by
  obtain ⟨a, b, hab⟩ := hG σ
  refine ⟨leg U a, leg V b, ?_⟩
  show opensSectionsRestrict 𝒢 (f.preimage_mono (inf_le_left : U ⊓ V ≤ U)) (leg U a) -
      opensSectionsRestrict 𝒢 (f.preimage_mono (inf_le_right : U ⊓ V ≤ V)) (leg V b) = _
  rw [hleg (inf_le_left : U ⊓ V ≤ U) a, hleg (inf_le_right : U ⊓ V ≤ V) b, ← map_sub, hab]

/-- **The degree-zero gluing condition for a pair of preimage opens, from the gluing condition
upstairs.** Let `f : X ⟶ Y` be a morphism of schemes, `G` an abelian sheaf on the one-universe
model of the small étale site of `Y` and `𝒢` one on that of `X`, and let `leg` be a family of maps
from the sections of `G` over an open of `Y` to the sections of `𝒢` over its preimage, compatible
with restriction. If the gluing condition holds for `G` at `(U, V)` and `leg` is surjective on
sections over `U ⊓ V`, then the gluing condition holds for `𝒢` at `(f ⁻¹ᵁ U, f ⁻¹ᵁ V)`.

The preimage of an intersection being the intersection of the preimages, this is
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective` read across a morphism
of schemes rather than for two sheaves on one scheme. -/
public theorem sectionsDifference_preimage_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}}
    {𝒢 : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}}
    (leg : ∀ W : Y.Opens, opensSections G W ⟶ opensSections 𝒢 (f ⁻¹ᵁ W))
    (hleg : ∀ {W W' : Y.Opens} (h : W ≤ W') (x : ToType (opensSections G W')),
      opensSectionsRestrict 𝒢 (f.preimage_mono h) (leg W' x) =
        leg W (opensSectionsRestrict G h x))
    (U V : Y.Opens) (hG : SectionsDifference G U V)
    (hsurj : Function.Surjective (ConcreteCategory.hom (leg (U ⊓ V)))) :
    SectionsDifference 𝒢 (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) := by
  intro τ
  obtain ⟨σ, hσ⟩ := hsurj τ
  obtain ⟨a, b, hab⟩ := exists_sectionsDifference_preimage_of_leg f leg hleg U V hG σ
  exact ⟨a, b, hab.trans hσ⟩

/-- `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_preimage_of_surjective` with the
gluing condition upstairs discharged by injectivity of `G`: **for an injective abelian sheaf `G` on
the model of `Y`, the gluing condition holds for `𝒢` at every pair of preimage opens over which
`leg` is surjective on the intersection.**

This is the level step of the hypothesis `hsub` of
`subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference` for the colimit sheaf of
[Stacks, Tag 09YQ]: with `f` a projection of the limit cone, `G` the sheaf of a level of a
pointwise injective system and `leg` the leg of the colimit presentation read on sections over the
opens, the surjectivity hypothesis is the degree-zero statement of that tag over `U ⊓ V`, and no
quasi-compactness or affineness is used anywhere else. -/
public theorem sectionsDifference_preimage_of_surjective_of_injective {X Y : Scheme.{u}}
    (f : X ⟶ Y) {G : Sheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}} [Injective G]
    {𝒢 : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}}
    (leg : ∀ W : Y.Opens, opensSections G W ⟶ opensSections 𝒢 (f ⁻¹ᵁ W))
    (hleg : ∀ {W W' : Y.Opens} (h : W ≤ W') (x : ToType (opensSections G W')),
      opensSectionsRestrict 𝒢 (f.preimage_mono h) (leg W' x) =
        leg W (opensSectionsRestrict G h x))
    (U V : Y.Opens)
    (hsurj : Function.Surjective (ConcreteCategory.hom (leg (U ⊓ V)))) :
    SectionsDifference 𝒢 (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) :=
  sectionsDifference_preimage_of_surjective f leg hleg U V
    (sectionsDifference_of_injective G U V) hsurj

end Stacks.EtaleCohomology.OpensAcyclicity

end
