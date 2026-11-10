module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Restricting a limit system to a subspace of one stage

Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms, let `i` be a stage, and let `g : T ⟶ D i` be a morphism. Base changing the stages
over `i` along `g` gives an inverse system indexed by the slice `Over i` whose limit is the
base change of `limit.π D i` along `g`, which is Stacks 07SF part (2). This file records that
system and shows that it again satisfies the hypotheses of Situation 084R: its stages are
quasi-compact and quasi-separated algebraic spaces and its transition morphisms are affine,
as soon as `T` is such a space.

The case of interest is `g = V.ι` for a quasi-compact open subspace `V` of the stage `D i`:
the system is then the system of inverse images of `V` in the later stages, and its limit is
the inverse image `V.preimage (limit.π D i)` of `V` in `limit D`.

## Main definitions

* `AlgebraicGeometry.Space.restrictDiagram`, with projections
  `AlgebraicGeometry.Space.restrictFst` and `.restrictSnd`.
* `AlgebraicGeometry.Space.restrictCone` and
  `AlgebraicGeometry.Space.isLimitRestrictCone`: the limiting cone, from Stacks 07SF (2).

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_restrictDiagram_obj`,
  `.isQuasiCompactSpace_restrictDiagram_obj`,
  `.isAbsolutelyQuasiSeparated_restrictDiagram_obj`,
  `.isAffineHom_restrictDiagram_map`: the restricted system satisfies the hypotheses of
  Situation 084R.
* `AlgebraicGeometry.Space.restrictConePtIsoPreimage`: for `g = V.ι` the vertex of the
  limiting cone is the inverse image of `V` in `limit D`.
* `AlgebraicGeometry.Space.cardinal_mk_hom_over_lt`: the morphism types of the index of the
  restricted system are small enough for the site, given that those of the original index
  are.

## Implementation notes

This is the construction to which Stacks 07SQ is applied in the proof of Stacks 07SR: having
descended an affine open of the limit to a quasi-compact open subspace `V` of a stage by
Stacks 0827, one knows that the *limit* of the restricted system is affine, and 07SQ then
makes one of its stages — an inverse image of `V` in a later stage — affine, hence a scheme.

Both quasi-compactness and quasi-separatedness of a restricted stage are read off the same
morphism: `restrictSnd j : D j ×_{D i} T ⟶ T` is a base change of the transition morphism
`D.map j.hom`, hence affine, hence both quasi-compact and quasi-separated, and `T` is
quasi-compact and quasi-separated by hypothesis. Affineness of a transition morphism of the
restricted system is the horizontal pasting of the two squares defining the stages over `T`,
which exhibits it as a base change of `D.map φ.left`.

The diagram and its two projections are given names rather than being written as
`pullback.fst`/`pullback.snd`, for the same reason as in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineChartSystem.lean`, whose
`stageBaseChangeDiagram` is this construction specialised to an affine scheme-valued point:
the vertices are definitionally but not syntactically chosen pullbacks.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : I)
  {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : T ⟶ D.obj i)

/-! ### The index of the restricted system is small enough for the site -/

omit [IsCofiltered I] in
/-- The morphism types of the slice over a stage are no larger than those of the index
category: a morphism of the slice is determined by its underlying morphism.

`AlgebraicGeometry.cardinal_mk_hom_over_op_lt` is the same bound for the slice over a stage
of the opposite of a *preorder*, where it is free because the morphism types are then
subsingletons. That argument is unavailable here — the index category of this section is an
arbitrary cofiltered category, whose morphism types are not subsingletons — so the bound has
to come from `hHomSize` instead. Together with `AlgebraicGeometry.mk_over_lt` for the object
type, this is what lets a result stated for a system over a small enough index, such as
Stacks 07SQ, be applied to the restricted system. -/
theorem cardinal_mk_hom_over_lt
    (hHomSize : ∀ a b : I, #(a ⟶ b) < B.cutoff.ord.cof) (i : I) (j k : Over i) :
    #(j ⟶ k) < B.cutoff.ord.cof :=
  (Cardinal.mk_le_of_injective (f := fun φ : j ⟶ k ↦ φ.left)
    (fun _ _ h ↦ Over.OverMorphism.ext h)).trans_lt (hHomSize j.left k.left)

/-! ### The restricted system -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the limits of presheaves on the big fppf site times out at the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_OpenSubspaceRestriction :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_OpenSubspaceRestriction
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The inverse system, indexed by the stages over `i`, of the base changes along `g` of
those stages. -/
noncomputable abbrev restrictDiagram : Over i ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Over.post (X := i) D ⋙ Over.pullback g) ⋙ Over.forget T

/-- The projection of a restricted stage to its own stage of `D`. -/
noncomputable def restrictFst (j : Over i) :
    (restrictDiagram B S hS D i g).obj j ⟶ D.obj j.left :=
  pullback.fst (D.map j.hom) g

/-- The projection of a restricted stage to `T`. -/
noncomputable def restrictSnd (j : Over i) :
    (restrictDiagram B S hS D i g).obj j ⟶ T :=
  pullback.snd (D.map j.hom) g

omit [IsCofiltered I] in
/-- A restricted stage is the fibre product of its own stage with `T` over the stage `i`. -/
theorem isPullback_restrict (j : Over i) :
    IsPullback (restrictFst B S hS D i g j) (restrictSnd B S hS D i g j) (D.map j.hom) g :=
  IsPullback.of_hasPullback _ _

omit [IsCofiltered I] in
/-- The transition morphisms of the restricted system are compatible with the projections to
the stages of `D`. -/
theorem restrictDiagram_map_comp_fst {j k : Over i} (φ : j ⟶ k) :
    (restrictDiagram B S hS D i g).map φ ≫ restrictFst B S hS D i g k =
      restrictFst B S hS D i g j ≫ D.map φ.left := by
  dsimp [restrictFst, Over.pullback, Over.post]
  exact pullback.lift_fst _ _ _

omit [IsCofiltered I] in
/-- The transition morphisms of the restricted system are compatible with the projections
to `T`. -/
theorem restrictDiagram_map_comp_snd {j k : Over i} (φ : j ⟶ k) :
    (restrictDiagram B S hS D i g).map φ ≫ restrictSnd B S hS D i g k =
      restrictSnd B S hS D i g j := by
  dsimp [restrictSnd, Over.pullback, Over.post]
  exact pullback.lift_snd _ _ _

/-! ### Its limit, by Stacks 07SF (2) -/

/-- The canonical cone on the restricted system, with vertex the base change of
`limit.π D i` along `g`. -/
noncomputable def restrictCone : Cone (restrictDiagram B S hS D i g) :=
  (Over.forget T).mapCone ((Over.pullback g).mapCone ((limit.cone D).overPost i))

/-- **Stacks 07SF (2).** The canonical cone on the restricted system is limiting. -/
noncomputable def isLimitRestrictCone : IsLimit (restrictCone B S hS D i g) :=
  isLimitPullbackLimitOverPost B S hS D i g

omit [IsCofiltered I] in
/-- The vertex of the canonical cone is the fibre product of `limit D` with `T` over the
stage `i`. -/
theorem isPullback_restrictCone :
    IsPullback (pullback.fst (limit.π D i) g) (pullback.snd (limit.π D i) g)
      (limit.π D i) g :=
  IsPullback.of_hasPullback _ _

/-! ### The restricted system satisfies the hypotheses of Situation 084R -/

variable (hD : ∀ a, IsAlgebraicSpace B S hS (D.obj a))
  (hAffine : ∀ {a b : I} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
  (hT : IsAlgebraicSpace B S hS T)

omit [IsCofiltered I] in
include hD hT in
/-- Every stage of the restricted system is an algebraic space over `S`. -/
theorem isAlgebraicSpace_restrictDiagram_obj (j : Over i) :
    IsAlgebraicSpace B S hS ((restrictDiagram B S hS D i g).obj j) :=
  isAlgebraicSpace_pullback B S hS (D.map j.hom) g (hD j.left) hT (hD i)

omit [IsCofiltered I] in
include hAffine in
/-- The projection of a restricted stage to `T` is affine, being a base change of a
transition morphism of `D`. -/
theorem isAffineHom_restrictSnd (j : Over i) :
    IsAffineHom B S hS (restrictSnd B S hS D i g j) :=
  isAffineHom_of_isPullback' B S hS (isPullback_restrict B S hS D i g j) (hAffine j.hom)

omit [IsCofiltered I] in
/-- A transition morphism of the restricted system is a base change of the corresponding
transition morphism of `D`: the horizontal pasting of the two squares cutting out the
stages over `T`. -/
theorem isPullback_restrictDiagram_map {j k : Over i} (φ : j ⟶ k) :
    IsPullback (restrictFst B S hS D i g j) ((restrictDiagram B S hS D i g).map φ)
      (D.map φ.left) (restrictFst B S hS D i g k) := by
  refine (IsPullback.of_right ?_ (restrictDiagram_map_comp_fst B S hS D i g φ)
    (isPullback_restrict B S hS D i g k).flip).flip
  have hmap : D.map φ.left ≫ D.map k.hom = D.map j.hom := by
    rw [← D.map_comp, Over.w φ]
  rw [restrictDiagram_map_comp_snd B S hS D i g φ, hmap]
  exact (isPullback_restrict B S hS D i g j).flip

omit [IsCofiltered I] in
include hAffine in
/-- Every transition morphism of the restricted system is affine. -/
theorem isAffineHom_restrictDiagram_map {j k : Over i} (φ : j ⟶ k) :
    IsAffineHom B S hS ((restrictDiagram B S hS D i g).map φ) :=
  isAffineHom_of_isPullback' B S hS (isPullback_restrictDiagram_map B S hS D i g φ)
    (hAffine φ.left)

omit [IsCofiltered I] in
include hD hAffine hT in
/-- Every stage of the restricted system is quasi-compact, as soon as `T` is: the projection
to `T` is affine, hence quasi-compact. -/
theorem isQuasiCompactSpace_restrictDiagram_obj
    (hTqc : IsQuasiCompactSpace B S hS T) (j : Over i) :
    IsQuasiCompactSpace B S hS ((restrictDiagram B S hS D i g).obj j) :=
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS hT hTqc
    (isQuasiCompact_of_isAffineHom' B S hS (restrictSnd B S hS D i g j)
      (isAlgebraicSpace_restrictDiagram_obj B S hS D i g hD hT j) hT
      (isAffineHom_restrictSnd B S hS D i g hAffine j))

omit [IsCofiltered I] in
include hD hAffine hT in
/-- Every stage of the restricted system is quasi-separated, as soon as `T` is: the
projection to `T` is affine, hence quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_restrictDiagram_obj
    {hZ : B.Contains (⊤_ Scheme.{u})}
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T) (j : Over i) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((restrictDiagram B S hS D i g).obj j) :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    (isAlgebraicSpace_restrictDiagram_obj B S hS D i g hD hT j) hTqs
    (isQuasiSeparated_of_isAffineHom B S hS (restrictSnd B S hS D i g j)
      (isAlgebraicSpace_restrictDiagram_obj B S hS D i g hD hT j) hT
      (isAffineHom_restrictSnd B S hS D i g hAffine j))

/-! ### The case of an open subspace -/

/-- For `g = V.ι` the vertex of the limiting cone of the restricted system is the inverse
image of `V` in `limit D`: both are the fibre product of `limit D` with `V` over `D i`. -/
noncomputable def restrictConePtIsoPreimage (V : Subfunctor (D.obj i)) :
    (restrictCone B S hS D i V.ι).pt ≅ (V.preimage (limit.π D i)).toFunctor :=
  (isPullback_restrictCone B S hS D i V.ι).isoIsPullback _ _
    (Subfunctor.isPullback_preimage (limit.π D i) V).flip

end AlgebraicGeometry.Space

end
