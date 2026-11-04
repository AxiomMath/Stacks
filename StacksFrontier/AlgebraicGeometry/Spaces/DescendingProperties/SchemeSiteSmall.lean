module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Scheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspaceCoveringLimitSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspaceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusPreimage

/-!
# Representability on the schematic locus, under the site-containment hypothesis

For a cofiltered inverse system of quasi-compact algebraic spaces over `S` with affine transition
morphisms, if every point of the limit lies in the inverse image of the schematic locus of some
stage, then some stage is representable by a scheme. This is proved here under a smallness
hypothesis on the system and under `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

## Main results

In namespace `AlgebraicGeometry.Space`:

* `exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_isSiteSmall`: some stage is
  representable when the schematic loci of the stages cover the points of the limit.
* `exists_isOpenSubspace_isAffineSpace_limit_restrictDiagram_of_isSiteSmall`: an affine open
  subspace of the limit is the inverse image of a quasi-compact open subspace of some stage, and
  the restricted system has affine limit.
* `exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_siteContainsBaseChangeLimits`: the
  representability criterion under `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- An algebraic space whose schematic locus is everything is representable. -/
private theorem isRepresentable_of_schematicLocus_eq_top
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hi : schematicLocus B S hS F = ⊤) : F.IsRepresentable := by
  have _ : (schematicLocus B S hS F).toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2
  have _ : IsIso (schematicLocus B S hS F).ι := (Subfunctor.eq_top_iff_isIso _).mp hi
  exact isRepresentable_of_natIso (schematicLocus B S hS F).toFunctor
    (asIso (schematicLocus B S hS F).ι)

/-- **A stage of a limit is a scheme as soon as the stages' schematic loci see every point of the
limit.** For a cofiltered inverse system of quasi-compact algebraic spaces over `S` with affine
transition morphisms, if every point of `limit D` lies in the inverse image of the schematic locus
of some stage, then some stage is representable by a scheme. -/
theorem exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_isSiteSmall
    (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (schematicLocus B S hS (D.obj i)).toFunctor
          (schematicLocus B S hS (D.obj i)).ι)) :
    ∃ i, (D.obj i).IsRepresentable := by
  obtain ⟨i, hi⟩ := exists_eq_top_of_covering_limit_of_isSiteSmall B S hS D hb hD hAffine hCompact
    (fun i => schematicLocus B S hS (D.obj i))
    (fun i =>
      (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS (hD i)).1)
    (fun {i j} f => preimage_schematicLocus_le B S hS (D.map f) (hD j) (hD i) (hAffine f))
    hpoint
  exact ⟨i, isRepresentable_of_schematicLocus_eq_top B S hS (hD i) hi⟩

/-! ### Descending an affine open subspace of the limit -/

/-- **An affine open subspace of the limit comes from a stage, with affine restricted system.** An
affine open subspace `W` of `limit D` is the inverse image of a quasi-compact open subspace `V` of
some stage, by Stacks 0827, and the limit of the system obtained by restricting `D` to `V` is then
affine, being `W`. -/
theorem exists_isOpenSubspace_isAffineSpace_limit_restrictDiagram_of_isSiteSmall
    (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (W : Subfunctor (limit D)) (hW : IsOpenSubspace B S hS W)
    (hWaff : IsAffineSpace B S hS W.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
      V.preimage (limit.π D i) = W ∧
      IsAffineSpace B S hS (limit (restrictDiagram B S hS D i V.ι)) := by
  obtain ⟨i, V, hV, hVqc, hpre⟩ :=
    exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_isSiteSmall
      B S hS D hb hD hAffine W hW hWaff.isQuasiCompactSpace
  refine ⟨i, V, hV, hVqc, hpre, ?_⟩
  have hpreaff : IsAffineSpace B S hS (V.preimage (limit.π D i)).toFunctor := by
    rw [hpre]; exact hWaff
  exact hpreaff.of_iso ((restrictConePtIsoPreimage B S hS D i V).symm.trans
    ((isLimitRestrictCone B S hS D i V.ι).conePointUniqueUpToIso (limit.isLimit _)))

/-! ### Under the chapter's standing convention -/

/-- **A stage of a limit is a scheme as soon as the stages' schematic loci see every point of the
limit, under the chapter's standing convention.** For a cofiltered inverse system of quasi-compact
algebraic spaces over `S` with affine transition morphisms whose limit is an algebraic space, if
every point of `limit D` lies in the inverse image of the schematic locus of some stage, then some
stage is representable by a scheme.

This is `exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_isSiteSmall` with its smallness
hypothesis replaced by the convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`; nothing is asked of the index. -/
theorem exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (schematicLocus B S hS (D.obj i)).toFunctor
          (schematicLocus B S hS (D.obj i)).ι)) :
    ∃ i, (D.obj i).IsRepresentable := by
  obtain ⟨i, hi⟩ := exists_eq_top_of_covering_limit_of_siteContainsBaseChangeLimits B S hS D
    hconv hlim hD hAffine hCompact
    (fun i => schematicLocus B S hS (D.obj i))
    (fun i =>
      (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS (hD i)).1)
    (fun {i j} f => preimage_schematicLocus_le B S hS (D.map f) (hD j) (hD i) (hAffine f))
    hpoint
  exact ⟨i, isRepresentable_of_schematicLocus_eq_top B S hS (hD i) hi⟩

end AlgebraicGeometry.Space

end
