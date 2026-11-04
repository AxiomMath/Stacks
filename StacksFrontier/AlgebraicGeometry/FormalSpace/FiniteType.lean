module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Finite type morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of formal
algebraic spaces over `S` is *locally of finite type* (Stacks 0AM4, part (1)), resp. *of finite
type* (Stacks 0AM4, part (2)), when it is representable by algebraic spaces and every base change
of `f` along a scheme-valued point of `Y` is a morphism of algebraic spaces which is locally of
finite type, resp. of finite type. Condition (2) of Stacks 0AJJ, representability by algebraic
spaces together with being of finite type in the bootstrap sense of Stacks 03XZ, is the same
test. All three conditions are stated for an arbitrary morphism of fppf sheaves on the big fppf
site of `S`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType`: Stacks 0AM4, part (1).
* `AlgebraicGeometry.FormalSpace.IsFiniteType`: Stacks 0AM4, part (2).
* `AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType`: condition (2) of Stacks 0AJJ.

## Main results

* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isPullback`,
  `AlgebraicGeometry.FormalSpace.IsFiniteType.of_isPullback` and
  `AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType.of_isPullback`: Stacks 0AQ5, stability
  under base change.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.comp`,
  `AlgebraicGeometry.FormalSpace.IsFiniteType.comp` and
  `AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType.comp`: Stacks 0AQ4, stability under
  composition.
* `AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType.isLocallyOfFiniteType`: condition (2)
  of Stacks 0AJJ implies being locally of finite type.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_comp`: Stacks 0AQ6, for `f ≫ g` with
  the source of `g` a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_comp_of_isAffineFormal`: Stacks 0AQ6
  when the source of the second morphism is an affine formal algebraic space.
* `FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace`:
  Stacks 0AQ0 when the source of the second morphism is a formal algebraic space.

## Implementation notes

Representability is the notion of `StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`, since the
sheaves carrying formal algebraic spaces take values in `Type (u + 1)` rather than in `Type u`.
The representability witness is what makes the base changes algebraic spaces, so each definition
is an existential over that witness rather than a conjunction.

## References

* [Stacks Project, Tag 0AJJ](https://stacks.math.columbia.edu/tag/0AJJ)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
* [Stacks Project, Tag 0AQ4](https://stacks.math.columbia.edu/tag/0AQ4)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
* [Stacks Project, Tag 0AQ6](https://stacks.math.columbia.edu/tag/0AQ6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of formal algebraic spaces over `S` is *locally of finite type* when it is
representable by algebraic spaces and every base change of it along a scheme-valued point of its
target is a morphism of algebraic spaces which is locally of finite type. The condition is stated
for an arbitrary morphism of fppf sheaves on the big fppf site of `S`. -/
@[stacks 0AM4 "part (1): locally of finite type"]
abbrev IsLocallyOfFiniteType {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.locallyOfFiniteTypePropertyULift.{u + 1} B S hS) f.hom hrep

/-- A morphism of formal algebraic spaces over `S` is *of finite type* when it is representable
by algebraic spaces and every base change of it along a scheme-valued point of its target is a
morphism of algebraic spaces which is of finite type. The condition is stated for an arbitrary
morphism of fppf sheaves on the big fppf site of `S`. -/
@[stacks 0AM4 "part (2): finite type",
  stacks 0AJJ "representable plus Bootstrap finite type",
  ega "I 10.13.3" "representable morphisms"]
abbrev IsFiniteType {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.finiteTypePropertyULift.{u + 1} B S hS) f.hom hrep

/-- A morphism of formal algebraic spaces over `S` is representable by algebraic spaces and of
finite type in the bootstrap sense of Stacks 03XZ when every base change of it along a
scheme-valued point of its target is a morphism of algebraic spaces which is of finite type. The
condition is stated for an arbitrary morphism of fppf sheaves on the big fppf site of `S`. -/
@[stacks 0AJJ "condition (2): representable by algebraic spaces plus of finite type in the \
Bootstrap sense of Stacks 03XZ"]
abbrev IsBootstrapFiniteType {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.finiteTypePropertyULift.{u + 1} B S hS) f.hom hrep

/-- A morphism of formal algebraic spaces over `S` satisfying condition (2) of Stacks 0AJJ is
locally of finite type. -/
theorem IsBootstrapFiniteType.isLocallyOfFiniteType {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsBootstrapFiniteType B S hS f) : IsLocallyOfFiniteType B S hS f := by
  obtain ⟨hrep, hprop⟩ := hf
  exact ⟨hrep, fun U ξ => (hprop U ξ).1⟩

/-- A cartesian square of fppf sheaves on the big fppf site of `S` is cartesian on the
underlying presheaves. -/
public theorem isPullback_hom_of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f) :
    IsPullback q.hom p.hom f.hom g.hom :=
  sq.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- A base change of a morphism of formal algebraic spaces over `S` which is locally of finite
type is locally of finite type. -/
@[stacks 0AQ5 "locally of finite type"]
theorem IsLocallyOfFiniteType.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS p := by
  obtain ⟨hrep, hprop⟩ := hf
  have sq' := isPullback_hom_of_isPullback B S hS sq
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS q.hom p.hom f.hom
      g.hom sq' hrep,
    Space.hasPropertyULift_of_isPullback B S hS sq' hrep hprop⟩

/-- A base change of a morphism of formal algebraic spaces over `S` which is of finite type is
of finite type. -/
@[stacks 0AQ5 "finite type"]
theorem IsFiniteType.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsFiniteType B S hS f) :
    IsFiniteType B S hS p := by
  obtain ⟨hrep, hprop⟩ := hf
  have sq' := isPullback_hom_of_isPullback B S hS sq
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS q.hom p.hom f.hom
      g.hom sq' hrep,
    Space.hasPropertyULift_of_isPullback B S hS sq' hrep hprop⟩

/-- **Stacks 0AQ5 for condition (2) of Stacks 0AJJ.** A base change of a morphism of formal
algebraic spaces over `S` which is representable by algebraic spaces and of finite type in the
bootstrap sense of Stacks 03XZ is again such. -/
theorem IsBootstrapFiniteType.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsBootstrapFiniteType B S hS f) :
    IsBootstrapFiniteType B S hS p :=
  IsFiniteType.of_isPullback B S hS sq hf

/-- A composition of morphisms of formal algebraic spaces over `S` which are locally of finite
type is locally of finite type. -/
@[stacks 0AQ4 "locally of finite type"]
theorem IsLocallyOfFiniteType.comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) :
    IsLocallyOfFiniteType B S hS (f ≫ g) := by
  obtain ⟨hfr, hfp⟩ := hf
  obtain ⟨hgr, hgp⟩ := hg
  have hcr := Space.isRepresentableByAlgebraicSpacesULift_comp B S hS f.hom g.hom hfr hgr
  refine ⟨hcr, ?_⟩
  intro U ξ
  change Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
    (pullback.fst ξ (f.hom ≫ g.hom))
  have hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ g.hom) := hgr U ξ
  have hA : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd ξ g.hom) f.hom) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (pullbackLeftPullbackSndIso ξ g.hom f.hom).symm (hcr U ξ)
  have hq : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
      (pullback.fst (pullback.snd ξ g.hom) f.hom) :=
    Space.isLocallyOfFiniteTypeULift_of_forall_pullback_fst B S hS hA hX _
      (Space.hasPropertyULift_of_isPullback B S hS
        (IsPullback.of_hasPullback (pullback.snd ξ g.hom) f.hom).flip hfr hfp)
  have hcomp := Space.isLocallyOfFiniteTypeULift_comp B S hS hA hX
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)
    (pullback.fst (pullback.snd ξ g.hom) f.hom) (pullback.fst ξ g.hom) hq (hgp U ξ)
  rw [show pullback.fst (pullback.snd ξ g.hom) f.hom ≫ pullback.fst ξ g.hom =
    (pullbackLeftPullbackSndIso ξ g.hom f.hom).hom ≫
      pullback.fst ξ (f.hom ≫ g.hom) by simp] at hcomp
  have h1 := Space.holdsOnEveryEtaleChartULift_precomp B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u})
    (pullbackLeftPullbackSndIso ξ g.hom f.hom).inv _ hcomp
  rwa [Iso.inv_hom_id_assoc] at h1

/-- A composition of morphisms of formal algebraic spaces over `S` which are of finite type is
of finite type. -/
@[stacks 0AQ4 "finite type"]
theorem IsFiniteType.comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsFiniteType B S hS f) (hg : IsFiniteType B S hS g) :
    IsFiniteType B S hS (f ≫ g) := by
  obtain ⟨hfr, hfp⟩ := hf
  obtain ⟨hgr, hgp⟩ := hg
  have hcr := Space.isRepresentableByAlgebraicSpacesULift_comp B S hS f.hom g.hom hfr hgr
  refine ⟨hcr, ?_⟩
  intro U ξ
  change Space.IsFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ (f.hom ≫ g.hom))
  have hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ g.hom) := hgr U ξ
  have hA : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd ξ g.hom) f.hom) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (pullbackLeftPullbackSndIso ξ g.hom f.hom).symm (hcr U ξ)
  have hq : Space.IsFiniteTypeULift.{u + 1} B S hS
      (pullback.fst (pullback.snd ξ g.hom) f.hom) :=
    Space.isFiniteTypeULift_of_forall_pullback_fst B S hS hA hX _
      (Space.hasPropertyULift_of_isPullback B S hS
        (IsPullback.of_hasPullback (pullback.snd ξ g.hom) f.hom).flip hfr hfp)
  have hcomp := Space.isFiniteTypeULift_comp B S hS hA hX
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)
    (pullback.fst (pullback.snd ξ g.hom) f.hom) (pullback.fst ξ g.hom) hq (hgp U ξ)
  rw [show pullback.fst (pullback.snd ξ g.hom) f.hom ≫ pullback.fst ξ g.hom =
    (pullbackLeftPullbackSndIso ξ g.hom f.hom).hom ≫
      pullback.fst ξ (f.hom ≫ g.hom) by simp] at hcomp
  refine ⟨?_, ?_⟩
  · have h1 := Space.holdsOnEveryEtaleChartULift_precomp B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u})
      (pullbackLeftPullbackSndIso ξ g.hom f.hom).inv _ hcomp.1
    rwa [Iso.inv_hom_id_assoc] at h1
  · have h2 := Space.isQuasiCompactULift_precomp B S hS
      (pullbackLeftPullbackSndIso ξ g.hom f.hom).symm _ hcomp.2
    rwa [Iso.symm_hom, Iso.inv_hom_id_assoc] at h2

/-- A composition of morphisms of formal algebraic spaces over `S` which are representable by
algebraic spaces and of finite type in the bootstrap sense of Stacks 03XZ is again such. -/
@[stacks 0AQ4 "finite type, proved for condition (2) of Stacks 0AJJ — representable by \
algebraic spaces plus of finite type in the Bootstrap sense of Stacks 03XZ — rather than for \
Definition 0AM4, part (2), verbatim, which is defined further up the import order: the two \
are identified unconditionally by Stacks 0AJJ, \
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`"]
theorem IsBootstrapFiniteType.comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsBootstrapFiniteType B S hS f) (hg : IsBootstrapFiniteType B S hS g) :
    IsBootstrapFiniteType B S hS (f ≫ g) :=
  IsFiniteType.comp B S hS f g hf hg

/-! ### Cancelling the second factor -/

/-- Being locally of finite type, read as a property of the morphisms of the big fppf site of
`S`, is invariant under isomorphism. -/
private instance inverseImage_locallyOfFiniteType_respectsIso :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := by
  let _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage _ _

/-- A morphism of fppf sheaves on the big fppf site of `S` every represented base change of
which is a morphism of the site that is locally of finite type has an underlying morphism of
presheaves with the same property against universe-lifted scheme-valued points. -/
private theorem relative_hom_of_relative_sheaf {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) f.hom := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let L := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let e : Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙ L ≅ uliftYoneda.{u + 1} :=
    Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)) L ≪≫
      (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf
  refine MorphismProperty.relative.of_exists fun U ξ => ?_
  let η := (fullyFaithfulSheafToPresheaf (BigFppfOver.topology B S hS)
    (Type (u + 1))).preimage ((e.app U).hom ≫ ξ)
  have hη : L.map η = (e.app U).hom ≫ ξ :=
    (fullyFaithfulSheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).map_preimage _
  obtain ⟨V, s, fst, hpb⟩ := hf.rep η
  have hpb' : IsPullback ((e.app V).inv ≫ L.map fst) ((uliftYoneda.{u + 1}).map s)
      f.hom ξ := by
    apply (hpb.map L).of_iso (e.app V) (Iso.refl _) (e.app U) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · exact e.hom.naturality s
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · exact hη
  exact ⟨V, (e.app V).inv ≫ L.map fst, s, hpb', hf.property η fst s hpb⟩

/-- A morphism of presheaves on the big fppf site of `S` representable by algebraic spaces
every represented base change of which is a morphism of the site that is locally of finite type
is locally of finite type in the bootstrap sense of Stacks 03XZ. -/
private theorem hasPropertyULift_of_relative
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a) :
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.locallyOfFiniteTypePropertyULift.{u + 1} B S hS) a hrep := by
  intro U ξ
  change Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ a)
  obtain ⟨V, s, fst, hpb⟩ := ha.rep ξ
  have h0 : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).map s) :=
    Space.isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS s (ha.property ξ fst s hpb)
  rw [← hpb.flip.isoPullback_hom_fst] at h0
  have h1 := Space.holdsOnEveryEtaleChartULift_precomp B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) hpb.flip.isoPullback.inv _ h0
  rwa [Iso.inv_hom_id_assoc] at h1

/-- Every represented base change of the relative diagonal of the underlying morphism of
presheaves of a morphism of fppf sheaves on the big fppf site of `S` is a morphism of the site
that is locally of finite type, as soon as the same holds for the relative diagonal of the
morphism of sheaves. -/
private theorem relative_diagonal_hom {Y Z : FppfSheaf B S hS} (g : Y ⟶ Z)
    (hdiag : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal g)) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
      (pullback.diagonal g.hom) := by
  have hmap : IsPullback (pullback.fst g g).hom (pullback.snd g g).hom g.hom g.hom :=
    (IsPullback.of_hasPullback g g).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have heq : (pullback.diagonal g).hom ≫ hmap.isoPullback.hom =
      pullback.diagonal g.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmap.isoPullback_hom_fst, pullback.diagonal_fst]
      exact congrArg (fun m : Y ⟶ Y => m.hom) (pullback.diagonal_fst g)
    · rw [Category.assoc, hmap.isoPullback_hom_snd, pullback.diagonal_snd]
      exact congrArg (fun m : Y ⟶ Y => m.hom) (pullback.diagonal_snd g)
  rw [← heq]
  exact MorphismProperty.RespectsIso.postcomp _ hmap.isoPullback.hom _
    (relative_hom_of_relative_sheaf B S hS (pullback.diagonal g) hdiag)

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of fppf sheaves on the big fppf site of `S`
with `Y` a formal algebraic space. If `f ≫ g` is locally of finite type then so is `f`. -/
@[stacks 0AQ6 "stated for arbitrary fppf sheaves, only the source of the second morphism being \
assumed a formal algebraic space"]
theorem IsLocallyOfFiniteType.of_comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hfg : IsLocallyOfFiniteType B S hS (f ≫ g)) :
    IsLocallyOfFiniteType B S hS f := by
  have hdiag := relative_locallyOfFiniteType_pullback_diagonal_of_isFormalAlgebraicSpace
    B S hS g hY
  obtain ⟨hcr, hcp⟩ := hfg
  have hrep := isRepresentableByAlgebraicSpacesULift_of_comp B S hS f g hdiag.rep hcr
  refine ⟨hrep, fun U ξ => ?_⟩
  change Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ f.hom)
  have hΔrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.diagonal g.hom) :=
    isRepresentableByAlgebraicSpacesULift_diagonal_hom B S hS g
      (isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable B S hS _
        hdiag.rep)
  have hΔ := hasPropertyULift_of_relative B S hS (pullback.diagonal g.hom)
    (relative_diagonal_hom B S hS g hdiag) hΔrep
  have hA : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ f.hom) := hrep U ξ
  have hBase : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (ξ ≫ g.hom) (f.hom ≫ g.hom)) := hcr U (ξ ≫ g.hom)
  have hmft := Space.isLocallyOfFiniteTypeULift_of_forall_pullback_fst B S hS hA hBase _
    (Space.hasPropertyULift_of_isPullback B S hS
      (pullback_map_diagonal_isPullback ξ f.hom g.hom) hΔrep hΔ)
  have hcomp := Space.isLocallyOfFiniteTypeULift_comp B S hS hA hBase
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U) _
    (pullback.fst (ξ ≫ g.hom) (f.hom ≫ g.hom)) hmft (hcp U (ξ ≫ g.hom))
  have hfac : pullback.map ξ f.hom (ξ ≫ g.hom) (f.hom ≫ g.hom) (𝟙 _) (𝟙 _) g.hom
      (Category.id_comp _).symm (Category.id_comp _).symm ≫
      pullback.fst (ξ ≫ g.hom) (f.hom ≫ g.hom) = pullback.fst ξ f.hom := by
    simp
  rwa [hfac] at hcomp

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of fppf sheaves on the big fppf site of `S`
with `Y` an affine formal algebraic space. If `f ≫ g` is locally of finite type then so is
`f`. -/
@[stacks 0AQ6 "for a second morphism whose source is an affine formal algebraic space"]
theorem IsLocallyOfFiniteType.of_comp_of_isAffineFormal {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hfg : IsLocallyOfFiniteType B S hS (f ≫ g)) :
    IsLocallyOfFiniteType B S hS f :=
  IsLocallyOfFiniteType.of_comp B S hS f g
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hY) hfg

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of fppf sheaves on the big fppf site of `S`
with `Y` a formal algebraic space. If `f ≫ g` is representable by algebraic spaces then so is
`f`. -/
@[stacks 0AQ0 "for a second morphism whose source is an arbitrary formal algebraic space"]
theorem isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hcomp : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f.hom ≫ g.hom)) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  isRepresentableByAlgebraicSpacesULift_of_comp B S hS f g
    (relativelyRepresentable_pullback_diagonal_of_isFormalAlgebraicSpace B S hS g hY) hcomp

/-- A morphism of fppf sheaves on the big fppf site of `S` between two algebraic spaces which is
locally of finite type in the sense of Definition 0AM4, part (1), is locally of finite type as a
morphism of algebraic spaces. -/
theorem isLocallyOfFiniteTypeULift_of_isLocallyOfFiniteType {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj)
    (hY : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Y.obj)
    (hf : IsLocallyOfFiniteType B S hS f) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS f.hom := by
  obtain ⟨_hrep, hprop⟩ := hf
  exact Space.isLocallyOfFiniteTypeULift_of_forall_pullback_fst B S hS hX hY f.hom hprop

end AlgebraicGeometry.FormalSpace

end
