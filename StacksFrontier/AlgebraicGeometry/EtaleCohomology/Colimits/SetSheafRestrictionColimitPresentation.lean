module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcSeparatedObjectColimit

/-!
# A sheaf of sets on a colimit of sites presents itself as the colimit of its restrictions

`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.SheafSystem.IsColimitPresentation`
is the set-valued presentation hypothesis `𝒢 = colim_i f_i^{-1}F_i` of [Stacks, Tag 09YQ], in the
*restriction* vocabulary: a system `F` of sheaves of sets on the levels of an inverse system of
sites, a sheaf `𝒢` of sets on the colimit site, and a family of maps
`ι_i : F_i ⟶ (u_i)^{op} ⋙ 𝒢` compatible with the transitions, through which every compatible
family factors uniquely.

This file proves that every sheaf of sets on the colimit site satisfies it, at the canonical
system: the system of restrictions of the sheaf to the levels, with the identity maps as legs.
Nothing is assumed about the sheaf. The colimit property is
`InverseSystemOfFiniteSites.isColimit_pullback_pushforward_of_colimit` ([Stacks, Tag 09YN]) at
`F_i = f_{i, *}𝒢`; the transition maps are the natural transformations
`InverseSystemOfFiniteSites.restrictionTransition`, and the restriction of a sheaf to a level is a
sheaf by [Stacks, Tag 0A35], which is
`InverseSystemOfFiniteSites.exists_isMorphismOfSites_sections_pullback_of_colimit`.

Here and below `InverseSystemOfFiniteSites` abbreviates
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites` and `AffineLimitCohomology`
abbreviates `Stacks.EtaleCohomology.AffineLimitCohomology`.

## Main results

* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.restrictionTransition` — the
  canonical transition `f_{i, *}𝒢 ⟶ f_{a, *}f_{j, *}𝒢` of the system of restrictions, as a natural
  transformation. It is the transport along the strict cocone identity `D.u a ⋙ u_j = u_i`, which
  is the source's own definition of the comparison, and `restrictionTransition_app` evaluates it.
* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.restrictionSystem` — the system
  of sheaves of sets on the levels obtained by restricting a sheaf on the colimit site, with those
  transitions.
* `InverseSystemOfFiniteSites.isColimitPresentation_restrictionSystem` — that system, with the
  identity maps as legs, is a colimit presentation of the sheaf it came from.
* `Stacks.EtaleCohomology.AffineLimitCohomology.limitRestrictionSystem` and
  `Stacks.EtaleCohomology.AffineLimitCohomology.isColimitPresentation_limitRestrictionSystem` —
  the same at the geometry: the system of sites of [Stacks, Tag 0EYL] for an inverse system of
  schemes with affine transition morphisms, with the legs `toLimitSmall i` and the coverings
  `limitSitePrecoverage`. This is the degree-zero half of [Stacks, Tag 0EYN] in the bundled
  set-valued vocabulary, and it is what lets
  `Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object` be applied
  to an actual sheaf.
* `AffineLimitCohomology.objectSections_surjective_and_separated_limitRestrictionSystem` — the
  two object-level clauses of [Stacks, Tag 09YN] in degree zero, for every sheaf of sets on the
  site of the limit, with no hypothesis on the sheaf.

## Implementation notes

**Why the transitions are built by transport and not by a universal property.** The comparison
`φ_a : f_a^{-1}f_{i, *}𝒢 → f_{j, *}𝒢` of [Stacks, Tag 09YN] is, in adjoint form, a map of
*presheaves* `f_{i, *}𝒢 ⟶ f_{a, *}f_{j, *}𝒢` whose source and target are *equal* functors, the
strict cocone identity `D.u a ⋙ u_j = u_i` of [Stacks, Tag 0A34] being an equality and not an
isomorphism. So the canonical map is `CategoryTheory.eqToHom` of that equality of functors, which
is what `restrictionTransition` is; `restrictionTransition_app` records its value on sections as
the reindexing the machinery's hypothesis `hψ` asks for, so that hypothesis is discharged by
evaluation and not by a comparison of two constructions.

**Why the predicate is reached through the bundled site inputs.** The four descent clauses of
[Stacks, Tag 09YL] are taken as
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.ColimitSiteInputs` rather than
spelled out, for the cost reason recorded on that structure and on
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit`: written out
at a concrete system the telescope mentions `D.I`, `D.C i` and `D.u a` some thirty times and the
elaborator goes through the system's definition at each occurrence. Taking the bundle also makes
the geometric instantiation a single application, `colimitSiteInputs_toLimitSmall` being exactly
that bundle for the system of sites of [Stacks, Tag 0EYL].

**The legs are the identity, which is the source's own cocone.** The second clause of
`isColimit_pullback_pushforward_of_colimit` factors a compatible family through the cocone whose
structure maps are the identity of `f_{i, *}𝒢`; the predicate here records those identities as its
`ι`. Nothing is lost: the first clause of the predicate, compatibility of the legs with the
transitions, is then the composition of a transport with its inverse, which is why its proof is
the cancellation of two `eqToHom`s and not an appeal to the machinery.

**The inverse-image form of the predicate.** The abelian predicate
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` of [Stacks, Tag 09YQ] is
stated with the *constructed* inverse image on Mathlib's small étale site; passing between it and
the restriction predicate here takes the two steps recorded in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCoefficientCrossing.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleColimitVanishingReduction.lean`
(namely an adjunction and a change of coefficients), neither of which is performed in this
file. The abelian half of the adjunction step is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_iff`.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 09YL](https://stacks.math.columbia.edu/tag/09YL)
* [Stacks Project, Tag 0A34](https://stacks.math.columbia.edu/tag/0A34)
* [Stacks Project, Tag 0A35](https://stacks.math.columbia.edu/tag/0A35)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem

universe w v₁ u₁ v u

namespace CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

variable {C : Type w} [SmallCategory C]

/-- **The restriction of a presheaf on the colimit site to a level, read at two levels, is the
same presheaf.** For `a : j ⟶ i` the presheaves `f_{i, *}P = (u_i)^{op} ⋙ P` and
`f_{a, *}f_{j, *}P = (D.u a)^{op} ⋙ (u_j)^{op} ⋙ P` are *equal*, because the strict cocone
identity `D.u a ⋙ u_j = u_i` of [Stacks, Tag 0A34] is an equality of functors. -/
theorem restriction_comp_eq (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) (P : Cᵒᵖ ⥤ Type w) {i j : D.I}
    (a : j ⟶ i) :
    (u i).op ⋙ P = (D.u a).op ⋙ ((u j).op ⋙ P) := by
  rw [show u i = D.u a ⋙ u j from (hu a).symm]
  rfl

/-- **The canonical transition of the system of restrictions**, in the adjoint form of
[Stacks, Tag 09YN]: the comparison `φ_a : f_a^{-1}f_{i, *}P → f_{j, *}P` transposed to a map of
presheaves `f_{i, *}P ⟶ f_{a, *}f_{j, *}P` on the level `i`. The source calls it the identity, and
here it is the transport `CategoryTheory.eqToHom` along `restriction_comp_eq`, the two presheaves
being equal functors. -/
def restrictionTransition (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) (P : Cᵒᵖ ⥤ Type w) {i j : D.I}
    (a : j ⟶ i) :
    (u i).op ⋙ P ⟶ (D.u a).op ⋙ ((u j).op ⋙ P) :=
  eqToHom (restriction_comp_eq D u hu P a)

/-- **The canonical transition on sections** is the reindexing of a section along the
identification `u_j(D.u a(V)) = u_i(V)` of [Stacks, Tag 0A34]. This is the form of the hypothesis
`ψ` of `isColimit_pullback_pushforward_of_colimit`. -/
theorem restrictionTransition_app (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) (P : Cᵒᵖ ⥤ Type w)
    {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : P.obj (op ((u i).obj V))) :
    (restrictionTransition D u hu P a).app (op V) x =
      P.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V).symm)) x := by
  rw [restrictionTransition, eqToHom_app, eqToHom_map]

/-- **The legs of the restriction system are compatible with its transitions.** Reindexing a
section back along the identification `u_j(D.u a(V)) = u_i(V)` after transporting it forward along
`restrictionTransition` returns it: the two transports cancel. This is the compatibility clause of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.SheafSystem.IsColimitPresentation`
at the identity legs, which is why that clause needs no appeal to the descent machinery. -/
theorem restrictionTransition_cancel (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) (P : Cᵒᵖ ⥤ Type w)
    {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : P.obj (op ((u i).obj V))) :
    x = P.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
      ((restrictionTransition D u hu P a).app (op V) x) := by
  rw [restrictionTransition_app D u hu P a V x, ← Functor.map_comp_apply, eqToHom_trans,
    eqToHom_refl, Functor.map_id_apply]

/-- **Every functor from a level to the colimit site defines a morphism of sites**
([Stacks, Tag 0A35]), hence is continuous, so the restriction of a sheaf on the colimit site to a
level is a sheaf. The witness is a proposition, so it is read off the existential statement of
[Stacks, Tag 0A35] directly. -/
theorem isSheaf_restriction (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) (K : Precoverage C)
    (hin : ColimitSiteInputs K D u hu)
    (G : Sheaf K.toGrothendieck (Type w)) (i : D.I) :
    Presheaf.IsSheaf (D.J i) ((u i).op ⋙ G.obj) :=
  have hf : ∀ i, (u i).IsMorphismOfSites (D.J i) K.toGrothendieck :=
    (exists_isMorphismOfSites_sections_pullback_of_colimit D u hu hin.hobj hin.hhom hin.hhom_inj
      K hin.hK).elim fun h _ => h
  have := (hf i).isContinuous
  (u i).op_comp_isSheaf (D.J i) K.toGrothendieck G

/-- **The system of restrictions of a sheaf of sets on a colimit of sites.** The sheaf at the level
`i` is `f_{i, *}𝒢`, the restriction of `𝒢` along `u_i` — a sheaf by `isSheaf_restriction` — and the
transitions are the canonical `restrictionTransition`. The cocycle law is the first clause of
`isColimit_pullback_pushforward_of_colimit`.

This is the system of direct images of [Stacks, Tag 0EZL] for sheaves of sets, bundled as
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.SheafSystem`. -/
def restrictionSystem (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) (K : Precoverage C)
    (hin : ColimitSiteInputs K D u hu)
    (G : Sheaf K.toGrothendieck (Type w)) : InverseSystemOfFiniteSites.SheafSystem D where
  obj i := ⟨(u i).op ⋙ G.obj, isSheaf_restriction D u hu K hin G i⟩
  map a := restrictionTransition D u hu G.obj a
  map_comp a b V x :=
    (isColimit_pullback_pushforward_of_colimit D u hu hin.hobj hin.hhom hin.hhom_inj K hin.hK G
      (fun a => restrictionTransition D u hu G.obj a)
      (fun a V x => restrictionTransition_app D u hu G.obj a V x)).1 a b V x

/-- The restriction system's sheaf at a level has the restriction of `𝒢` as its underlying
presheaf, on the nose. -/
theorem restrictionSystem_obj_obj (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (K : Precoverage C) (hin : ColimitSiteInputs K D u hu)
    (G : Sheaf K.toGrothendieck (Type w)) (i : D.I) :
    ((restrictionSystem D u hu K hin G).obj i).obj = (u i).op ⋙ G.obj :=
  rfl

/-- **A sheaf of sets on a colimit of sites is the colimit of the inverse images of its
restrictions**, in the bundled vocabulary the set-valued degree-zero statements of
[Stacks, Tag 09YQ] consume. In the situation of [Stacks, Tag 0A34], let the functors
`u_i : D.C i ⥤ C` exhibit the small category `C` as the colimit of the levels with `K` the
coverings of [Stacks, Tag 09YL] — that is the bundle `hin` — and let `𝒢` be a sheaf of sets on
`C`. Then `𝒢` together with the identity maps out of its restrictions
`f_{i, *}𝒢 = (u_i)^{op} ⋙ 𝒢` is a colimit presentation of the system `restrictionSystem`:
every family of maps `f_{i, *}𝒢 ⟶ f_{i, *}H` into the restrictions of a sheaf `H` on `C` that is
compatible with the canonical transitions consists of the restrictions of a unique map `𝒢 ⟶ H`.

Nothing is assumed. The factorisation clause is the second clause of
`isColimit_pullback_pushforward_of_colimit`, the half of [Stacks, Tag 0EXJ] that says
`𝒢 = colim_i f_i^{-1}f_{i, *}𝒢`; the compatibility clause of the legs is the cancellation of the
transport of `restrictionTransition` against its inverse, the legs being identities. -/
theorem isColimitPresentation_restrictionSystem (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (K : Precoverage C) (hin : ColimitSiteInputs K D u hu)
    (G : Sheaf K.toGrothendieck (Type w)) :
    (restrictionSystem D u hu K hin G).IsColimitPresentation u hu K G (fun _ => 𝟙 _) :=
  ⟨restrictionTransition_cancel D u hu G.obj,
    (isColimit_pullback_pushforward_of_colimit D u hu hin.hobj hin.hhom hin.hhom_inj K hin.hK G
      (restrictionTransition D u hu G.obj) (restrictionTransition_app D u hu G.obj)).2⟩

end CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

/-! ### The system of sites of a limit of schemes

The instantiation at the system of sites of [Stacks, Tag 0EYL]: an inverse system of schemes with
affine transition morphisms, its small affine étale sites as levels, and the raised small affine
étale site of the limit as the colimit site. -/

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **The system of restrictions of a sheaf of sets on the site of the limit**, for the system of
sites of [Stacks, Tag 0EYL]. The sheaf at the level `n` is the restriction of `𝒢` along
`toLimitSmall n`, whose sections over a level object are the sections of `𝒢` over its base change
to the limit; this is the `p_{n, *}𝒢` of [Stacks, Tag 0EYN] read on the level. The abelian system
of direct images for the same tag, stated on Mathlib's small étale site rather than on these
levels, is `Stacks.EtaleCohomology.directImageSystem`. -/
def limitRestrictionSystem
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1))) :
    InverseSystemOfFiniteSites.SheafSystem (sys D c B hD hX hc) :=
  InverseSystemOfFiniteSites.restrictionSystem (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
    (limitSitePrecoverage D c B hX) (colimitSiteInputs_toLimitSmall D c B hD hX hc) G

/-- **[Stacks, Tag 0EYN] in degree zero for sheaves of sets, in the bundled vocabulary.** Let
`(X_i)` be an inverse system of schemes with affine transition morphisms over a nonempty directed
index, all objects of a big étale site `B`, let `X = lim X_i`, and let `𝒢` be a sheaf of sets on
the raised small affine étale site of `X`. Then `𝒢` with the identity maps out of its restrictions
to the levels of the system of sites of [Stacks, Tag 0EYL] is a colimit presentation of
`limitRestrictionSystem`: `𝒢 = colim_n p_n^{-1}p_{n, *}𝒢`.

Nothing is assumed. The four site inputs of [Stacks, Tag 09YL] for this system are
`colimitSiteInputs_toLimitSmall`, and the abstract statement is
`InverseSystemOfFiniteSites.isColimitPresentation_restrictionSystem`.

This is the hypothesis `hpres` of
`Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object` and of
`Stacks.EtaleCohomology.QcqsEtaleCohomologyColimitGlobal.globalSections_colimit_of_qcqs_level`.
-/
theorem isColimitPresentation_limitRestrictionSystem
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1))) :
    (limitRestrictionSystem D c B hD hX hc G).IsColimitPresentation
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (limitSitePrecoverage D c B hX) G (fun _ => 𝟙 _) :=
  InverseSystemOfFiniteSites.isColimitPresentation_restrictionSystem (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
    (limitSitePrecoverage D c B hX) (colimitSiteInputs_toLimitSmall D c B hD hX hc) G

open Stacks.WeakSites.ColimitGlobalSections in
/-- **The degree-zero sections statement of [Stacks, Tag 09YN] at the geometry, with nothing
assumed.** For every sheaf of sets `𝒢` on the raised small affine étale site of the limit
`X = lim X_i`: every section of `𝒢` over the image of an object `Y` of a level `n` is the image of
a section of `𝒢` over the base change of `Y` to some lower level, and two such sections of a level
with the same image there agree at a further level.

This is `Stacks.EtaleCohomology.QcSeparatedColimit.objectSections_surjective_and_separated` with
its colimit-presentation hypothesis discharged by
`isColimitPresentation_limitRestrictionSystem`, so it carries no hypothesis on the sheaf at all.
Both halves are read at the system of restrictions, whose sheaf at a level is `𝒢` restricted
there, so the content is that the restrictions of `𝒢` to the levels jointly generate it and
separate its sections -- which is the two object-level inputs of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'`. -/
theorem objectSections_surjective_and_separated_limitRestrictionSystem
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1))) :
    ObjectSectionsSurjective (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc)
        (limitRestrictionSystem D c B hD hX hc G).obj G (fun _ => 𝟙 _) ∧
      ObjectSectionsSeparated (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (limitRestrictionSystem D c B hD hX hc G).obj
        (limitRestrictionSystem D c B hD hX hc G).map G (fun _ => 𝟙 _) :=
  QcSeparatedColimit.objectSections_surjective_and_separated D c B hD hX hc
    (limitRestrictionSystem D c B hD hX hc G) G (fun _ => 𝟙 _)
    (isColimitPresentation_limitRestrictionSystem D c B hD hX hc G)

end Stacks.EtaleCohomology.AffineLimitCohomology

end
