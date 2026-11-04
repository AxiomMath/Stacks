module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismLimitPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Inverse limits of algebraic spaces affine over a base

Let `D` be a cofiltered inverse system of algebraic spaces over a scheme `S`, each carrying an
affine morphism to one fixed algebraic space `T`, compatibly with the transitions. The
transition morphisms of such a system are then affine of their own accord, so the inverse
limit of `D` is an algebraic space and its structure morphism to `T` is affine. When `T` is an
affine object of the site, the limit is moreover represented by an affine object of the site.
Consequently a limiting cone of such a system, taken in the category of algebraic spaces affine
over `T`, is computed in the presheaves over `T`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_map_of_isAffineHom_app`: a transition morphism of a
  system affine over `T` is affine.
* `AlgebraicGeometry.Space.limitπ_comp_app_eq`: the structure morphism of the limit does not
  depend on the stage at which it is read off.
* `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isAffineHom_app`: the limit is an
  algebraic space.
* `AlgebraicGeometry.Space.isAffineHom_limitπ_comp_app`: its structure morphism to `T` is
  affine.
* `AlgebraicGeometry.Space.exists_isAffine_representation_limit`: over an affine base the
  limit is represented by an affine object of the site.
* `AlgebraicGeometry.Space.isLimit_affineOverToOver_of_size`: a limiting cone of a cofiltered
  system in the category of algebraic spaces affine over `T` is computed in the presheaves
  over `T`.

## Implementation notes

Stacks 07SE is a section, not a lemma, so it has no statement of its own; what is assembled
here is the combination the section is cited for, as in the proof of Stacks 08K6. The
section's own numbered results are proved elsewhere: 07SF in
`StacksFrontier/AlgebraicGeometry/Spaces/ApproximationSteps.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/AffineLimitExistence.lean`, 07SG in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/QuotientPresentation.lean`, 07SH in
`StacksFrontier/AlgebraicGeometry/Spaces/ApproximationSteps.lean`, 0CUH in
`StacksFrontier/AlgebraicGeometry/Spaces/LimitClosedImmersion.lean`, 0CUI in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/Reduced.lean`, and 0CP4 in
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentation/QcqsCriterion.lean`.

Affineness of the transition morphisms, which is the hypothesis of 07SF, is not assumed. It
is derived from affineness of the structure morphisms by Stacks 08GB, part (2): a composite
`D i ⟶ D j ⟶ T` which is affine and whose second factor is separated has an affine first
factor, and an affine morphism of algebraic spaces is separated. The source's standing
convention for the section, that base change of an affine morphism is affine (Stacks 03WI),
is used through that lemma.

The last result is the point at which the section combines with Limits, Section 01YV in the
source: over an affine base the limit is not merely affine over the base but represented by
an affine object of the site. It is read off from affineness of the structure morphism at
the test object `Z` and the identity, a base change along an isomorphism.

The two cardinality hypotheses on the index category are those carried by 07SF in this
development: they put the index category below the cofinality of the site's size cutoff,
which is what makes the limit exist inside the site.

`AlgebraicGeometry.Space.isLimit_affineOverToOver_of_size` is a different reading of the same
limit, and the one a limit presentation of an affine morphism needs. The anti-equivalence of
Stacks 081V produces limits of inverse systems of affine morphisms in the *full subcategory*
`AlgebraicGeometry.Space.AffineOver` of the algebraic spaces affine over a base, and a limit in
a full subcategory need not be a limit in the ambient category. It is here: the presheaf limit
of the system is an algebraic space affine over the base by the two results above, hence an
object of that subcategory, and there it is a limiting cone, because the inclusion of the
subcategory into the presheaves over the base is faithful and a presheaf lift of a cone of
spaces affine over the base is again a morphism over the base. Any other limiting cone is then
isomorphic to that one, and the isomorphism transports the presheaf limit property. The two
cardinality hypotheses are the ones that make the presheaf limit an algebraic space, so they are
carried; nothing else is. In particular neither finiteness of the limit over the base nor the
closed-immersion hypothesis on the transition morphisms of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitPresentation` is needed, and that is
what makes the result apply to an integral morphism, whose system has finite surjections as
transitions and a limit which is not finite over the base.

## References

* [Stacks Project, Tag 07SE](https://stacks.math.columbia.edu/tag/07SE)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 01YV](https://stacks.math.columbia.edu/tag/01YV)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section AffineOverBase

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (τ : D ⟶ (Functor.const I).obj T)

omit [IsCofiltered I] in
/-- A transition morphism of an inverse system of algebraic spaces affine over `T` is itself
affine. It composes with the structure morphism of its target to the structure morphism of
its source, so Stacks 08GB, part (2) applies: the composite is affine and the structure
morphism of the target is separated, being affine. -/
theorem isAffineHom_map_of_isAffineHom_app
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) {i j : I} (φ : i ⟶ j) :
    IsAffineHom B S hS (D.map φ) := by
  have hnat : D.map φ ≫ τ.app j = τ.app i := by simp
  refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS (D.map φ) (τ.app j) ?_ ?_
  · rw [hnat]; exact hτ i
  · exact isSeparated_of_isAffineHom B S hS (τ.app j) (hD j) hT (hτ j)

omit [IsCofiltered I] in
/-- The structure morphism of the inverse limit does not depend on the stage at which it is
read off: the projections of the limit cone are compatible with the transitions, and the
transitions are compatible with the structure morphisms. -/
theorem limitπ_comp_app_eq {i j : I} (φ : i ⟶ j) :
    limit.π D i ≫ τ.app i = limit.π D j ≫ τ.app j := by
  have hnat : D.map φ ≫ τ.app j = τ.app i := by simp
  rw [← hnat, ← Category.assoc, limit.w]

/-- **Stacks 07SE.** The inverse limit of a cofiltered inverse system of algebraic spaces
over `S`, each affine over one fixed algebraic space `T`, is an algebraic space over `S`,
provided the index category is small enough for the site.

Affineness of the transition morphisms, which is what Stacks 07SF asks for, is supplied by
`AlgebraicGeometry.Space.isAffineHom_map_of_isAffineHom_app`. -/
@[stacks 07SE "the content the section is cited for: a cofiltered inverse limit of \
algebraic spaces affine over a base is an algebraic space; the section's own numbered \
results 07SF, 07SG, 07SH, 0CUH, 0CUI and 0CP4 are not proved here"]
theorem isAlgebraicSpace_limit_of_isAffineHom_app (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit B S hS D hSize hHomSize hD fun {_ _} φ =>
    isAffineHom_map_of_isAffineHom_app B S hS D τ hD hT hτ φ

/-- **Stacks 07SE.** The structure morphism of the inverse limit of a cofiltered inverse
system of algebraic spaces each affine over one fixed algebraic space `T` is affine over `T`.

It factors as the projection to a stage, which is affine by Stacks 07SF, part (1), followed
by the structure morphism of that stage. -/
@[stacks 07SE "the content the section is cited for: the structure morphism of a cofiltered \
inverse limit of algebraic spaces affine over a base is affine; the section's own numbered \
results 07SF, 07SG, 07SH, 0CUH, 0CUI and 0CP4 are not proved here"]
theorem isAffineHom_limitπ_comp_app (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) (i : I) :
    IsAffineHom B S hS (limit.π D i ≫ τ.app i) :=
  isAffineHom_comp B S hS _ _
    (isAffineHom_limitπ B S hS D hSize hHomSize
      (fun {_ _} φ => isAffineHom_map_of_isAffineHom_app B S hS D τ hD hT hτ φ) i) (hτ i)

end AffineOverBase

section AffineBase

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Z : BigAffineFppf B S hS)
variable (τ : D ⟶ (Functor.const I).obj
  (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)))

/-- **Stacks 07SE, over an affine base.** The inverse limit of a cofiltered inverse system of
algebraic spaces over `S`, each affine over one fixed affine object `Z` of the site, is
represented by an affine object of the site, by an isomorphism carrying the structure
morphism of the limit to a morphism of the site.

The structure morphism of the limit is affine, so its base change along the identity of
`yoneda Z` is represented by an affine object of the site; a base change along an identity is
an isomorphism. -/
@[stacks 07SE "the content the section is cited for, combined with Limits, Section 01YV: a \
cofiltered inverse limit of algebraic spaces affine over an affine base is represented by an \
affine object of the site; the section's own numbered results 07SF, 07SG, 07SH, 0CUH, 0CUI \
and 0CP4 are not proved here"]
theorem exists_isAffine_representation_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) (i₀ : I) :
    ∃ (W : BigAffineFppf B S hS)
      (e : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ≅ limit D)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
        (BigAffineFppf.inclusion B S hS).obj Z),
      e.hom ≫ limit.π D i₀ ≫ τ.app i₀ = yoneda.map q := by
  have hZ : IsAlgebraicSpace B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    isAlgebraicSpace_yoneda B S hS _
  obtain ⟨W, p, q, hpb⟩ :=
    isAffineHom_limitπ_comp_app B S hS D τ hSize hHomSize hD hZ hτ i₀ Z (𝟙 _)
  have hid : IsPullback (𝟙 (limit D)) (limit.π D i₀ ≫ τ.app i₀)
      (limit.π D i₀ ≫ τ.app i₀) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨W, IsPullback.isoIsPullback _ _ hpb hid, q,
    IsPullback.isoIsPullback_hom_snd _ _ hpb hid⟩

end AffineBase

section AffineOverPresheafLimit

variable {Y : AlgebraicSpaces B S hS} {J : Type u} [SmallCategory J] [IsCofiltered J]

/-- The system of presheaves underlying a system of algebraic spaces affine over `Y`. -/
private abbrev affineOverPresheafDiagram (D : J ⥤ AffineOver B S hS Y) :
    J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (D ⋙ affineOverToOver B S hS Y) ⋙ Over.forget Y.obj

/-- The cone of presheaves underlying a cone of algebraic spaces affine over `Y`. -/
private abbrev affineOverPresheafCone (D : J ⥤ AffineOver B S hS Y) (s : Cone D) :
    Cone (affineOverPresheafDiagram B S hS D) :=
  (Over.forget Y.obj).mapCone ((affineOverToOver B S hS Y).mapCone s)

/-- A morphism of spaces affine over `Y` commutes with the structure morphisms to `Y`. -/
private theorem affineOver_hom_left_comp_hom {D E : AffineOver B S hS Y} (f : D ⟶ E) :
    f.hom.left.hom ≫ E.obj.hom.hom = D.obj.hom.hom := by
  have h := congrArg (fun k => k.hom) (Over.w f.hom)
  rwa [ObjectProperty.FullSubcategory.comp_hom] at h

/-- A limiting cone of a cofiltered system of algebraic spaces affine over `Y`, over an index
category small enough for the site, is computed in the presheaves over `Y`.

The presheaf limit of the system is an algebraic space by
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isAffineHom_app` and is affine over `Y` by
`AlgebraicGeometry.Space.isAffineHom_limitπ_comp_app`, so it is itself an object of
`AlgebraicGeometry.Space.AffineOver`, and there the projections of the presheaf limit are a
limiting cone: a presheaf lift of a cone of spaces affine over `Y` is again a morphism over `Y`,
and the inclusion into the presheaves over `Y` is faithful.  The given cone is therefore
isomorphic to that one, and the isomorphism transports the presheaf limit property. -/
theorem isLimit_affineOverToOver_of_size (D : J ⥤ AffineOver B S hS Y) (c : Cone D)
    (hc : IsLimit c) (hSize : #J < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof) :
    Nonempty (IsLimit ((affineOverToOver B S hS Y).mapCone c)) := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := J)
  set Dp := affineOverPresheafDiagram B S hS D
  set τ : Dp ⟶ (Functor.const J).obj Y.obj :=
    { app := fun i => (D.obj i).obj.hom.hom
      naturality := fun i j g => by
        change (D.map g).hom.left.hom ≫ (D.obj j).obj.hom.hom =
          (D.obj i).obj.hom.hom ≫ 𝟙 Y.obj
        rw [Category.comp_id]
        exact affineOver_hom_left_comp_hom B S hS (D.map g) }
  have hDsp : ∀ i, IsAlgebraicSpace B S hS (Dp.obj i) := fun i => (D.obj i).obj.left.property
  have hDaff : ∀ i, IsAffineHom B S hS (τ.app i) := fun i => (D.obj i).property
  have hLsp : IsAlgebraicSpace B S hS (limit Dp) :=
    isAlgebraicSpace_limit_of_isAffineHom_app B S hS Dp τ hSize hHomSize hDsp Y.property hDaff
  have hLaff : IsAffineHom B S hS (limit.π Dp i₀ ≫ τ.app i₀) :=
    isAffineHom_limitπ_comp_app B S hS Dp τ hSize hHomSize hDsp Y.property hDaff i₀
  have hconst : ∀ i : J, limit.π Dp i ≫ τ.app i = limit.π Dp i₀ ≫ τ.app i₀ := fun i =>
    (limitπ_comp_app_eq B S hS Dp τ (IsCofiltered.minToLeft i i₀)).symm.trans
      (limitπ_comp_app_eq B S hS Dp τ (IsCofiltered.minToRight i i₀))
  set W : AffineOver B S hS Y :=
    ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS)
      (X := (⟨limit Dp, hLsp⟩ : AlgebraicSpaces B S hS)) (Y := Y)
      (limit.π Dp i₀ ≫ τ.app i₀)), hLaff⟩
  set cW : Cone D :=
    { pt := W
      π :=
        { app := fun i => ObjectProperty.homMk (Over.homMk
            (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (limit.π Dp i))
            (ObjectProperty.hom_ext _ (hconst i)))
          naturality := fun i j g =>
            ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
              (limit.w Dp g).symm)) } }
  have hcWlim : IsLimit cW :=
    { lift := fun s => ObjectProperty.homMk (Over.homMk
        (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS)
          (limit.lift Dp (affineOverPresheafCone B S hS D s)))
        (by
          apply ObjectProperty.hom_ext
          rw [ObjectProperty.FullSubcategory.comp_hom]
          change limit.lift Dp (affineOverPresheafCone B S hS D s) ≫
            limit.π Dp i₀ ≫ τ.app i₀ = s.pt.obj.hom.hom
          rw [← Category.assoc, limit.lift_π]
          exact affineOver_hom_left_comp_hom B S hS (s.π.app i₀)))
      fac := fun s i =>
        ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
          (limit.lift_π (affineOverPresheafCone B S hS D s) i)))
      uniq := fun s m hm => by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change m.hom.left.hom = limit.lift Dp (affineOverPresheafCone B S hS D s)
        exact limit.hom_ext fun i =>
          (congrArg (fun t : s.pt ⟶ D.obj i => t.hom.left.hom) (hm i)).trans
            (limit.lift_π (affineOverPresheafCone B S hS D s) i).symm }
  have hmapW : IsLimit ((affineOverToOver B S hS Y).mapCone cW) :=
    isLimitOfReflects (Over.forget Y.obj) (limit.isLimit Dp)
  refine ⟨IsLimit.ofIsoLimit hmapW (Cone.ext
    ((affineOverToOver B S hS Y).mapIso (hc.conePointUniqueUpToIso hcWlim)).symm fun i => ?_)⟩
  change (affineOverToOver B S hS Y).map (cW.π.app i) =
    (affineOverToOver B S hS Y).map (hc.conePointUniqueUpToIso hcWlim).inv ≫
      (affineOverToOver B S hS Y).map (c.π.app i)
  rw [← Functor.map_comp, IsLimit.conePointUniqueUpToIso_inv_comp]

end AffineOverPresheafLimit

end AlgebraicGeometry.Space

end
