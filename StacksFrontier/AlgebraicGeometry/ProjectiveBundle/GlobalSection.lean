module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalQuotientDatum
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TrivializedQuotientRestrict

/-!
# The section of a projective bundle attached to an invertible quotient

Let `ℰ` be a quasi-coherent `𝒪_X`-module and `q : ℰ ↠ ℒ` an epimorphism onto an invertible
module. `Stacks.RelativeProj.localSection` is a section of `π : 𝐏(ℰ) ⟶ X` over an affine open on
which `ℒ` is trivial, and
`Stacks.RelativeProj.homOfLE_comp_localSection_eq` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TrivializedQuotientRestrict.lean` says that those
local sections agree under shrinking the open. **This file glues them**:
`Stacks.RelativeProj.globalSection` is a morphism `X ⟶ 𝐏(ℰ)` with
`globalSection q ≫ π = 𝟙 X`.

## Why shrinking is enough

Agreement under shrinking is weaker than agreement on pairwise intersections — the intersection
of two affine opens is not affine in general, so the local section is not even defined over it —
but it is exactly the hypothesis of Mathlib's
`AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected`, which glues a family of
morphisms over a cover indexed by a preorder whose members form a basis of the topology. The
cover here is `Stacks.RelativeProj.trivCover`, indexed by **all** affine opens on which `ℒ` is
trivial, ordered by inclusion.

That those opens form a basis is `Stacks.RelativeProj.exists_trivAffineOpen_mem_le`, and it is
where the work of the previous file is used a second time: the trivializing affine opens produced
by `Stacks.LineBundle.Situation.exists_trivializing_affineOpen` are not a basis on their own —
one gets *some* trivializing affine at each point, not one inside a prescribed neighbourhood —
and shrinking one needs the trivialization to restrict. On the open subscheme that is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictTrivializationOfLE`, and
`…ProjInvertibleLocus.exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq` carries the result back
to the restricted site, which is where the index set states triviality.

Surjectivity of `q` on sections, the third condition the local section needs, is free on every
affine open once `ℒ` is known to be quasi-coherent, so it does not enter the index set; see
`Stacks.RelativeProj.surjective_app_of_isAffineOpen_of_epi`.

## Main definitions

* `Stacks.RelativeProj.TrivAffineOpens`: the affine opens on which `ℒ` is trivial.
* `Stacks.RelativeProj.trivCover`: **the open cover of `X` by them**, locally directed by
  inclusion.
* `Stacks.RelativeProj.localSectionFamily`: the local sections, one per cover member.
* `Stacks.RelativeProj.globalSection`: **the glued section** `X ⟶ 𝐏(ℰ)`.

## Main results

* `Stacks.RelativeProj.exists_trivAffineOpen_mem_le`: the trivializing affine opens are a basis.
* `Stacks.RelativeProj.trans_comp_localSectionFamily`: the local sections agree under the
  transition maps of the cover.
* `Stacks.RelativeProj.globalSection_comp_projectiveBundleToBase` and
  `Stacks.RelativeProj.exists_section_projectiveBundle`: **the glued morphism is a section of
  `π`.**
* `Stacks.RelativeProj.ι_comp_globalSection` and
  `Stacks.RelativeProj.ι_comp_globalSection_eq_localSection`: **the glued section restricted to a
  member of the cover is the local section there**, the second with the trivialisation supplied by
  the consumer rather than chosen inside `localSectionFamily`. This is what a statement about the
  glued section proved one cover member at a time runs on.

## What this is not

This is **not** a covering part of Tag 0B3V, and no `@[stacks]` attribute is attached. Tag 0B3V
asserts that `sectionsMap` is a *bijection* between the sections of `π` and the invertible
quotients of `ℰ`. What is produced here is a section attached to a quotient; that it *classifies*
that quotient — that `σ^*𝒪(1)` is `ℒ`, pinned on sections and not merely up to an unspecified
isomorphism — is the `Classifies` half of
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies`, and it is untouched.
Registering the mere existence of a section under Tag 0B3V would be a weaker statement wearing
the tag's name.

## Implementation notes

`Scheme.Cover.LocallyDirected.ofIsBasisOpensRange` asks for the index preorder to agree with
inclusion of the images and for those images to be a basis. Both are discharged by
`AlgebraicGeometry.Scheme.Opens.opensRange_ι`, which is not a definitional equality, so the
second is phrased as a rewrite of the indexing function rather than pointwise — `simp` cannot
rewrite under the `Set.range` binder here, the goals being rejected as not type-correct at
`implicit` transparency across the `AlgebraicGeometry.Scheme.Modules` `def`.

The transition maps of the cover are `AlgebraicGeometry.Scheme.homOfLE` on the nose
(`Stacks.RelativeProj.trivCover_trans`, by `rfl`), because
`ofIsBasisOpensRange` builds them as `AlgebraicGeometry.IsOpenImmersion.lift` of the two
inclusions and that is the definition of `homOfLE`. This is what lets
`homOfLE_comp_localSection_eq` be the compatibility hypothesis verbatim.

The trivialization of each cover member is `Nonempty`, as
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalQuotientDatum.lean` produces it, and is
chosen by `Nonempty.some`. The choice does not matter: `Stacks.RelativeProj.localSection_congr`
makes the local section a function of the open and the quotient alone, which is also why the
compatibility above typechecks with two unrelated choices on the two cover members.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u

namespace Stacks.RelativeProj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **An affine open of `X` on which `ℒ` is trivial**: the index type of the cover the local
sections are glued over. Triviality is recorded as `Nonempty` of an isomorphism on the restricted
site, which is the form `Stacks.LineBundle.Situation.exists_trivializing_affineOpen` produces. -/
public def TrivAffineOpens (L : X.Modules) : Type u :=
  {V : X.affineOpens //
    Nonempty (L.over V.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over V.1))}

/-- The trivializing affine opens are ordered by inclusion. -/
public instance : Preorder (TrivAffineOpens L) :=
  inferInstanceAs <| Preorder {V : X.affineOpens //
    Nonempty (L.over V.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over V.1))}

/-- **The affine opens on which `ℒ` is trivial are a basis of the topology of `X`.** At each
point there is *some* trivializing affine open, but to get a basis one must be able to shrink it
inside a prescribed neighbourhood: take an affine open inside the intersection and restrict the
trivialization to it, by
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictTrivializationOfLE` on the open subscheme
and `…ProjInvertibleLocus.exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq` to read the result
back on the restricted site. -/
public theorem exists_trivAffineOpen_mem_le {U : X.Opens} {x : X} (hxU : x ∈ U) :
    ∃ V : TrivAffineOpens L, x ∈ V.1.1 ∧ V.1.1 ≤ U := by
  obtain ⟨V₀, hxV₀, ⟨e₀⟩⟩ := (invertibleSituation L).exists_trivializing_affineOpen x
  obtain ⟨W, hWaff, hxW, hWle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ V₀.1 ⊓ U from ⟨hxV₀, hxU⟩)
  have hWV₀ : W ≤ V₀.1 := fun _ hy => (hWle hy).1
  obtain ⟨e, -⟩ := exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq W L
    (restrictTrivializationOfLE hWV₀ L (restrictIsoUnitOfOverIsoUnit V₀.1 L e₀))
  exact ⟨⟨⟨W, hWaff⟩, ⟨e⟩⟩, hxW, fun _ hy => (hWle hy).2⟩

variable (L) in
/-- **The open cover of `X` by the affine opens on which `ℒ` is trivial.** Joint surjectivity is
the basis property at the top open. -/
@[simps I₀ X f]
public def trivCover : X.OpenCover where
  I₀ := TrivAffineOpens L
  X V := V.1.1
  f V := V.1.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨V, hxV, -⟩ := exists_trivAffineOpen_mem_le (L := L) (U := ⊤) (x := x) trivial
    exact ⟨V, ⟨x, hxV⟩, rfl⟩

/-- The cover's index type is the trivializing affine opens, with their order. -/
public instance : Preorder (trivCover L).I₀ :=
  inferInstanceAs <| Preorder (TrivAffineOpens L)

/-- **The cover is locally directed by inclusion.** Its members form a basis and the order is
inclusion of the images, which is what
`AlgebraicGeometry.Scheme.Cover.LocallyDirected.ofIsBasisOpensRange` asks for. -/
public instance : (trivCover L).LocallyDirected :=
  .ofIsBasisOpensRange
    (fun {i j} => by
      change i.1.1 ≤ j.1.1 ↔
        Scheme.Hom.opensRange i.1.1.ι ≤ Scheme.Hom.opensRange j.1.1.ι
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]) <| by
    have hfun : (fun i : (trivCover L).I₀ => Scheme.Hom.opensRange ((trivCover L).f i)) =
        (fun i : TrivAffineOpens L => i.1.1) :=
      funext fun i => Scheme.Opens.opensRange_ι i.1.1
    rw [hfun, TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hxU
    obtain ⟨V, hxV, hVU⟩ := exists_trivAffineOpen_mem_le (L := L) hxU
    exact ⟨V.1.1, ⟨V, rfl⟩, hxV, hVU⟩

/-- **The transition maps of the cover are `AlgebraicGeometry.Scheme.homOfLE`**, on the nose:
both are `AlgebraicGeometry.IsOpenImmersion.lift` of the two inclusions. -/
@[simp]
public theorem trivCover_trans {V W : TrivAffineOpens L} (hVW : V ≤ W) :
    Scheme.Cover.trans (trivCover L) (homOfLE hVW) = X.homOfLE hVW :=
  rfl

/-- **An epimorphism onto an invertible module is surjective on sections over every affine
open.** The invertible module is quasi-coherent, so
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` applies; no condition on the open beyond
affineness is needed, which is why triviality of `ℒ` is the only condition in the index set of
the cover. -/
public theorem surjective_app_of_isAffineOpen_of_epi (q : F ⟶ L) [Epi q] {V : X.Opens}
    (hV : IsAffineOpen V) : Function.Surjective (q.val.app (op V)) := by
  have : L.IsQuasicoherent :=
    have : Stacks.Ample.IsInvertibleModule X L :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X q V hV

/-- **The local sections, as a family over the cover**: on each member,
`Stacks.RelativeProj.localSection` at a chosen trivialization. The choice is immaterial by
`Stacks.RelativeProj.localSection_congr`. -/
public def localSectionFamily (q : F ⟶ L) [Epi q] (V : TrivAffineOpens L) :
    V.1.1.toScheme ⟶ projectiveBundle X F :=
  localSection V.1.1 q V.2.some V.1.2 (surjective_app_of_isAffineOpen_of_epi q V.1.2)

/-- **The local sections agree under the transition maps of the cover.** This is
`Stacks.RelativeProj.homOfLE_comp_localSection_eq` verbatim, the transition maps being
`AlgebraicGeometry.Scheme.homOfLE`; the two trivializations are the independent choices made on
the two members, which that lemma allows. -/
public theorem trans_comp_localSectionFamily (q : F ⟶ L) [Epi q]
    {V W : TrivAffineOpens L} (hVW : V ⟶ W) :
    Scheme.Cover.trans (trivCover L) hVW ≫ localSectionFamily q W = localSectionFamily q V :=
  homOfLE_comp_localSection_eq q W.2.some V.2.some (leOfHom hVW) V.1.2 W.1.2
    (surjective_app_of_isAffineOpen_of_epi q W.1.2) (surjective_app_of_isAffineOpen_of_epi q V.1.2)

/-- **The section of `π : 𝐏(ℰ) ⟶ X` attached to an invertible quotient `q : ℰ ↠ ℒ`**: the local
sections, glued over the cover of `X` by the affine opens trivializing `ℒ`. -/
public def globalSection (q : F ⟶ L) [Epi q] : X ⟶ projectiveBundle X F :=
  (trivCover L).glueMorphismsOfLocallyDirected (localSectionFamily q)
    (trans_comp_localSectionFamily q)

/-- The glued section restricted to a member of the cover is the local section there. -/
private theorem ι_comp_globalSection_aux (q : F ⟶ L) [Epi q] (V : TrivAffineOpens L) :
    V.1.1.ι ≫ globalSection q = localSectionFamily q V :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (trivCover L) (localSectionFamily q)
    (trans_comp_localSectionFamily q) V

/-- **The glued morphism is a section of `π`.** Checked on the cover, where it is the local
section, and `Stacks.RelativeProj.localSection_comp_projectiveBundleToBase` places that over its
open on the nose. -/
public theorem globalSection_comp_projectiveBundleToBase (q : F ⟶ L) [Epi q] :
    globalSection q ≫ projectiveBundleToBase X F = 𝟙 X := by
  refine (trivCover L).hom_ext _ _ fun V => ?_
  rw [← Category.assoc]
  exact (congrArg (· ≫ projectiveBundleToBase X F) (ι_comp_globalSection_aux q V)).trans
    ((localSection_comp_projectiveBundleToBase V.1.1 q V.2.some V.1.2
      (surjective_app_of_isAffineOpen_of_epi q V.1.2)).trans (Category.comp_id _).symm)

/-- **The glued section restricted to a member of the cover is the local section there.** This is
`AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOfLocallyDirected` at
`Stacks.RelativeProj.localSectionFamily`, the transition maps of `Stacks.RelativeProj.trivCover`
being the inclusions of its members. -/
public theorem ι_comp_globalSection (q : F ⟶ L) [Epi q] (V : TrivAffineOpens L) :
    V.1.1.ι ≫ globalSection q = localSectionFamily q V :=
  ι_comp_globalSection_aux q V

/-- **The glued section restricted to a member of the cover is the local section built there from
*any* trivialisation.** The choice made inside `Stacks.RelativeProj.localSectionFamily` is
absorbed by `Stacks.RelativeProj.localSection_congr`, so a consumer holding its own trivialisation
of `ℒ` over the member reads the restriction of `Stacks.RelativeProj.globalSection` as the local
section of that trivialisation. -/
public theorem ι_comp_globalSection_eq_localSection (q : F ⟶ L) [Epi q] (V : TrivAffineOpens L)
    (e : L.over V.1.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over V.1.1))
    (hq : Function.Surjective (q.val.app (op V.1.1))) :
    V.1.1.ι ≫ globalSection q = localSection V.1.1 q e V.1.2 hq :=
  (ι_comp_globalSection q V).trans
    (localSection_congr V.1.1 q V.1.2 V.2.some e
      (surjective_app_of_isAffineOpen_of_epi q V.1.2) hq)

/-- **Every invertible quotient of `ℰ` gives a section of `π : 𝐏(ℰ) ⟶ X`.**

This is *not* the surjectivity half of Tag 0B3V's bijection: it produces a section, not a section
*classifying the given quotient*. See the `What this is not` section of this file. -/
public theorem exists_section_projectiveBundle (q : F ⟶ L) [Epi q] :
    ∃ τ : X ⟶ projectiveBundle X F, τ ≫ projectiveBundleToBase X F = 𝟙 X :=
  ⟨globalSection q, globalSection_comp_projectiveBundleToBase q⟩

/-- **`exists_classifies` without `Classifies`.** Every invertible quotient of `ℰ`, in the form
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` takes it, has a section of
`π : 𝐏(ℰ) ⟶ X` attached to it. What that field asks beyond this is that the section *classify*
the quotient — `Stacks.RelativeProj.TautologicalDatum.Classifies`, which is untouched; this
statement is exactly the field with that conclusion deleted, so discharging the field is
replacing `True` by `Classifies` here and nothing else. -/
public theorem exists_section_of_invertibleQuotient
    (Q : Stacks.Divisors.InvertibleQuotient X F) :
    ∃ σ : X ⟶ projectiveBundle X F, σ ≫ projectiveBundleToBase X F = 𝟙 X := by
  have :
      AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Q.L :=
    Q.invertible
  have : Epi Q.q := Q.epi
  exact exists_section_projectiveBundle Q.q

end Stacks.RelativeProj

end
