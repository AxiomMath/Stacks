module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# The open locus over which a module is relatively ample

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`L` be an `𝒪_X`-module. This file builds the open subspace `V ⊆ Y` of Stacks 0D3D — a morphism
`Y' ⟶ Y` factors through `V` exactly when the pullback of `L` to `Y' ×_Y X` is ample over `Y'`
— out of two inputs, which are the two halves of the source's proof that are not formal:

* the Zariski case of Stacks 0D3C, (2) implies (1): relative ampleness may be checked on the
  members of a Zariski covering of the target;
* claim (A) of the proof of Stacks 0D3D: a field-valued point of `Y` over which the pullback of
  `L` is ample lies in an open subspace of `Y` over which `L` is ample.

Neither is assumed about the objects of the conclusion in any other way, and nothing is assumed
of `f`: the construction is formal once these two inputs are available.

## Main definitions

* `AlgebraicGeometry.Space.IsRelativelyAmpleOver`: `L` is ample over a subfunctor `W` of `Y` when
  the pullback of `L` is ample on every base change of `f` along a morphism of algebraic spaces
  factoring through `W`.
* `AlgebraicGeometry.Space.relativelyAmpleLocus`: the set of points of `Y` lying in some open
  subspace over which `L` is ample.

## Main results

* `AlgebraicGeometry.Space.isOpen_relativelyAmpleLocus`: that set is open.
* `AlgebraicGeometry.Space.isRelativelyAmple_of_forall_pointsMap_mem_relativelyAmpleLocus`:
  relative ampleness on a base change all of whose points map into the locus, from the Zariski
  case of Stacks 0D3C.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple`: the open
  subspace of Stacks 0D3D, from the two inputs above.

## Implementation notes

**Ampleness over a subfunctor is quantified over base changes.** The restriction of `f` over an
open subspace `W` is the base change of `f` along the inclusion of `W`; rather than choosing it,
`IsRelativelyAmpleOver` asks for ampleness on every cartesian square over a morphism factoring
through `W`, which is equivalent by Stacks 0D33 and avoids a choice of fibre product.

**The open subspace** is `AlgebraicGeometry.Space.openSubspaceOfPoints` of the locus, whose point
set is the locus by Stacks 03BZ; factoring through it is a condition on points by Stacks 03IE.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D3C](https://stacks.math.columbia.edu/tag/0D3C)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2)

/-- `L` is *ample over* a subfunctor `W` of `Y` when, for every morphism of algebraic spaces
`g : Y' ⟶ Y` factoring through `W` and every cartesian square realising the base change
`f' : X' ⟶ Y'` of `f` along `g`, the pullback of `L` to `X'` is ample relative to `f'`. -/
def IsRelativelyAmpleOver (W : Subfunctor Y.1) : Prop :=
  ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback p f' f g → (∃ l : Y'.1 ⟶ W.toFunctor, l ≫ W.ι = g.hom) →
      IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)

/-- The points of `Y` lying in some open subspace of `Y` over which `L` is ample. -/
def relativelyAmpleLocus : Set (points B S hS Y.1) :=
  {y | ∃ W : Subfunctor Y.1, IsOpenSubspace B S hS W ∧ IsRelativelyAmpleOver f L W ∧
    y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι)}

/-- The locus of points over a neighbourhood of which `L` is ample is open: it is a union of
point sets of open subspaces, which are open by Stacks 03BZ. -/
theorem isOpen_relativelyAmpleLocus : IsOpen (relativelyAmpleLocus f L) := by
  have h : relativelyAmpleLocus f L = ⋃ W : {W : Subfunctor Y.1 //
      IsOpenSubspace B S hS W ∧ IsRelativelyAmpleOver f L W},
        Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := by
    ext y
    simp only [relativelyAmpleLocus, Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists,
      exists_prop]
    exact ⟨fun ⟨W, hW, hamp, hy⟩ => ⟨W, ⟨hW, hamp⟩, hy⟩,
      fun ⟨W, ⟨hW, hamp⟩, hy⟩ => ⟨W, hW, hamp, hy⟩⟩
  rw [h]
  exact isOpen_iUnion fun W => isOpen_range_pointsMap_of_isOpenImmersion B S hS _ W.2.1.2

/-- The fpqc case of Stacks 0D3C, (2) implies (1), in the shape consumed here: relative
ampleness of an invertible module may be checked on the base changes along the members of an
fpqc covering of the target. It holds: `AlgebraicGeometry.Space.relativeAmpleFpqcDescends`. -/
def RelativeAmpleFpqcDescends (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (L' : Modules.{u, u} B S hS X'.1 X'.2),
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X'.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).property
      L' →
    ∀ {I : Type (u + 1)} {Yᵢ Xᵢ : I → AlgebraicSpaces B S hS} {gᵢ : ∀ i, Yᵢ i ⟶ Y'}
    {fᵢ : ∀ i, Xᵢ i ⟶ Yᵢ i} {pᵢ : ∀ i, Xᵢ i ⟶ X'},
    (∀ i, IsPullback (pᵢ i) (fᵢ i) f' (gᵢ i)) →
    IsFpqcCovering B S hS (fun i => (gᵢ i).hom) →
    (∀ i, IsRelativelyAmple B S hS (fᵢ i) ((modulePullback B S hS (pᵢ i)).obj L')) →
    IsRelativelyAmple B S hS f' L'

variable {f L}

/-- Descent of relative ampleness along an fpqc covering of the target, with the pullbacks of `L`
along `pᵢ ≫ p` as hypotheses. -/
private theorem isRelativelyAmple_of_isFpqcCovering_comp
    (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    {X' Y' : AlgebraicSpaces B S hS} (p : X' ⟶ X) (f' : X' ⟶ Y')
    {I : Type (u + 1)} {Yᵢ Xᵢ : I → AlgebraicSpaces B S hS} {gᵢ : ∀ i, Yᵢ i ⟶ Y'}
    {fᵢ : ∀ i, Xᵢ i ⟶ Yᵢ i} {pᵢ : ∀ i, Xᵢ i ⟶ X'}
    (hsqᵢ : ∀ i, IsPullback (pᵢ i) (fᵢ i) f' (gᵢ i))
    (hcov : IsFpqcCovering B S hS (fun i => (gᵢ i).hom))
    (h : ∀ i, IsRelativelyAmple B S hS (fᵢ i) ((modulePullback B S hS (pᵢ i ≫ p)).obj L)) :
    IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L) :=
  hdesc f' _ (Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS p) (L := L) (hL := hL)) hsqᵢ hcov
    fun i => (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS (pᵢ i) p).app L)).mpr (h i)

/-- Ampleness of the pullback of `L` is inherited by the base change along any `a : A ⟶ Y'`. -/
private theorem exists_isPullback_isRelativelyAmple_comp
    {X' Y' A : AlgebraicSpaces B S hS} {g : Y' ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y'}
    (hsq : IsPullback p f' f g) (a : A ⟶ Y')
    (hamp : IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) :
    ∃ (X'' : AlgebraicSpaces B S hS) (p'' : X'' ⟶ X) (f'' : X'' ⟶ A),
      IsPullback p'' f'' f (a ≫ g) ∧
        IsRelativelyAmple B S hS f'' ((modulePullback B S hS p'').obj L) := by
  have hsq₁ := AlgebraicSpaces.isPullback_fiberProduct B S hS f' a
  exact ⟨_, _, _, hsq₁.paste_horiz hsq,
    (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS _ p).app L)).mp
      (isRelativelyAmple_baseChange hsq₁ _ hamp)⟩

/-- **Ampleness on a base change all of whose points map into the ample locus.** Let
`f' : X' ⟶ Y'` be the base change of `f` along `g : Y' ⟶ Y`. If every point of `Y'` maps into
`AlgebraicGeometry.Space.relativelyAmpleLocus`, then the pullback of `L` is ample relative to
`f'`.

The preimages in `Y'` of the open subspaces over which `L` is ample form a Zariski covering of
`Y'`, hence an fpqc covering (Stacks 0DFQ); over each member the composite to `Y` factors
through such an open subspace, so the pullback of `L` is ample there, and the Zariski case of
Stacks 0D3C concludes. -/
theorem isRelativelyAmple_of_forall_pointsMap_mem_relativelyAmpleLocus
    (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    {X' Y' : AlgebraicSpaces B S hS}
    {g : Y' ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y'} (hsq : IsPullback p f' f g)
    (hpts : ∀ y : points B S hS Y'.1, pointsMap B S hS Y'.1 g.hom y ∈ relativelyAmpleLocus f L) :
    IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L) := by
  let I := {W : Subfunctor Y.1 // IsOpenSubspace B S hS W ∧ IsRelativelyAmpleOver f L W}
  let Wₛ : I → AlgebraicSpaces B S hS := fun W => ⟨W.1.toFunctor, W.2.1.1⟩
  let ιₛ : ∀ W : I, Wₛ W ⟶ Y := fun W => ObjectProperty.homMk W.1.ι
  let Yᵢ : I → AlgebraicSpaces B S hS := fun W => AlgebraicSpaces.fiberProduct B S hS g (ιₛ W)
  let gᵢ : ∀ W : I, Yᵢ W ⟶ Y' := fun W => ObjectProperty.homMk (pullback.fst g.hom W.1.ι)
  let Xᵢ : I → AlgebraicSpaces B S hS := fun W => AlgebraicSpaces.fiberProduct B S hS f' (gᵢ W)
  let pᵢ : ∀ W : I, Xᵢ W ⟶ X' := fun W => ObjectProperty.homMk (pullback.fst f'.hom (gᵢ W).hom)
  let fᵢ : ∀ W : I, Xᵢ W ⟶ Yᵢ W := fun W =>
    ObjectProperty.homMk (pullback.snd f'.hom (gᵢ W).hom)
  have hsqᵢ : ∀ W : I, IsPullback (pᵢ W) (fᵢ W) f' (gᵢ W) := fun W =>
    AlgebraicSpaces.isPullback_fiberProduct B S hS f' (gᵢ W)
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hzar : IsZariskiCovering B S hS I (fun W => (Yᵢ W).1) (fun W => (gᵢ W).hom) := by
    refine ⟨fun W => ?_, fun y => ?_⟩
    · exact MorphismProperty.pullback_fst (P := MorphismProperty.presheaf
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g.hom W.1.ι W.2.1.2
    · obtain ⟨W, hW, hamp, w, hw⟩ := hpts y
      obtain ⟨z, hz, -⟩ := exists_points_of_isPullback B S hS
        (IsPullback.of_hasPullback g.hom W.ι) y w hw.symm
      exact ⟨⟨W, hW, hamp⟩, z, hz⟩
  refine isRelativelyAmple_of_isFpqcCovering_comp hdesc hL p f' hsqᵢ
    (isFpqcCovering_of_isZariskiCovering B S hS _ _ Y'.2 (fun W => (Yᵢ W).2) hzar) fun W => ?_
  exact W.2.2 (gᵢ W ≫ g) (pᵢ W ≫ p) (fᵢ W) ((hsqᵢ W).paste_horiz hsq)
    ⟨pullback.snd g.hom W.1.ι, (pullback.condition (f := g.hom) (g := W.1.ι)).symm⟩

/-- **The open subspace of Stacks 0D3D, from its two non-formal inputs.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces and `L` an invertible `𝒪_X`-module. Assume

* `hdesc`: the fpqc case of Stacks 0D3C, (2) implies (1)
  (`AlgebraicGeometry.Space.relativeAmpleFpqcDescends`);
* `hA`: claim (A) of the proof of Stacks 0D3D — every field-valued point of `Y` over which the
  pullback of `L` is ample lies in an open subspace over which `L` is ample.

Then there is an open subspace `V ⊆ Y` such that a morphism of algebraic spaces `g : Y' ⟶ Y`
factors through `V` if and only if the pullback of `L` to the base change `X'` of `f` along
`g` is ample relative to `X' ⟶ Y'`.

`V` is the open subspace whose points are `AlgebraicGeometry.Space.relativelyAmpleLocus`
(Stacks 03BZ). Factoring through it is the condition that every point of `Y'` lands in the
locus (Stacks 03IE); that condition gives ampleness by
`isRelativelyAmple_of_forall_pointsMap_mem_relativelyAmpleLocus`, and conversely ampleness over
`Y'` restricts to ampleness over every field-valued point of `Y'` (Stacks 0D33), which `hA`
places in the locus. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple
    (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (hA : ∀ (t : FieldValuedPoint B S hS Y.1) {X'' : AlgebraicSpaces B S hS} (p'' : X'' ⟶ X)
      (f'' : X'' ⟶ representedAlgebraicSpace B S hS t.siteObject),
      IsPullback p'' f'' f (ObjectProperty.homMk (yonedaEquiv.symm t.value)) →
      IsRelativelyAmple B S hS f'' ((modulePullback B S hS p'').obj L) →
      t.class B S hS Y.1 ∈ relativelyAmpleLocus f L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) := by
  let V := openSubspaceOfPoints B S hS Y.1 (relativelyAmpleLocus f L)
  have hV : IsOpenSubspace B S hS V :=
    isOpenSubspace_openSubspaceOfPoints B S hS Y.2 _ (isOpen_relativelyAmpleLocus f L)
  have hVpts : Set.range (pointsMap B S hS V.toFunctor V.ι) = relativelyAmpleLocus f L :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  refine ⟨V, hV, fun X' Y' g p f' hsq => ⟨?_, fun hamp => ?_⟩⟩
  · rintro ⟨l, hl⟩
    refine isRelativelyAmple_of_forall_pointsMap_mem_relativelyAmpleLocus hdesc hL hsq fun y => ?_
    rw [← hVpts, ← hl, pointsMap_comp_apply]
    exact ⟨_, rfl⟩
  · refine (factorsThrough_openSubspace_iff_points B S hS Y.2 Y'.2 V hV g.hom).mpr ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := Quot.exists_rep y
    rw [hVpts]
    let a : representedAlgebraicSpace B S hS t.siteObject ⟶ Y' :=
      ObjectProperty.homMk (yonedaEquiv.symm t.value)
    obtain ⟨_, p₂, f₂, hsq₂, hamp₂⟩ := exists_isPullback_isRelativelyAmple_comp hsq a hamp
    have ha : a ≫ g = ObjectProperty.homMk
        (yonedaEquiv.symm ((FieldValuedPoint.map B S hS Y'.1 g.hom t).value)) := by
      ext1
      change yonedaEquiv.symm t.value ≫ g.hom = yonedaEquiv.symm (g.hom.app _ t.value)
      exact yonedaEquiv_symm_naturality_right _ g.hom t.value
    rw [ha] at hsq₂
    exact hA (FieldValuedPoint.map B S hS Y'.1 g.hom t) _ _ hsq₂ hamp₂

/-! ### Reduction of claim (A) to affine schemes étale over the target -/

variable (f L) in
/-- `L` is *ample over* a subfunctor `W` of a presheaf `Z` *along* a morphism `a : Z ⟶ Y` when
the pullback of `L` is ample on every base change of `f` along a morphism of algebraic spaces
which factors through `W ⟶ Z ⟶ Y`. For `a` the identity this is
`AlgebraicGeometry.Space.IsRelativelyAmpleOver`. -/
def IsRelativelyAmpleAlong {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Z ⟶ Y.1)
    (W : Subfunctor Z) : Prop :=
  ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback p f' f g → (∃ l : Y'.1 ⟶ W.toFunctor, l ≫ W.ι ≫ a = g.hom) →
      IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)

variable (f L) in
/-- **Claim (A) of the proof of Stacks 0D3D over affine schemes étale over the target.** For
every affine scheme `U` of the site with a morphism `a : h_U ⟶ Y` and every field-valued point
`r` of `U` over which the pullback of `L` is ample, `r` lies in an open subspace of `U` over
which `L` is ample along `a`. -/
def AmpleNearFieldPointsOfAffines : Prop :=
  ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ (a : yoneda.obj U ⟶ Y.1), IsEtale B S hS a →
    ∀ (r : FieldValuedPoint B S hS (yoneda.obj U)) {X'' : AlgebraicSpaces B S hS} (p'' : X'' ⟶ X)
      (f'' : X'' ⟶ representedAlgebraicSpace B S hS r.siteObject),
      IsPullback p'' f'' f (ObjectProperty.homMk (yonedaEquiv.symm r.value ≫ a)) →
      IsRelativelyAmple B S hS f'' ((modulePullback B S hS p'').obj L) →
      ∃ W : Subfunctor (yoneda.obj U), IsOpenSubspace B S hS W ∧
        r.class B S hS _ ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        IsRelativelyAmpleAlong f L a W

/-- **Ampleness over the étale image of an open subspace.** Let `b : Z ⟶ Y` be an étale morphism
from an algebraic space and `W ⊆ Z` an open subspace over which `L` is ample along `b`. Then `L`
is ample over the image of `W` in `Y`, an open subspace of `Y` by Stacks 03BZ and 03IR.

A morphism `Y' ⟶ Y` factoring through the image is covered, in the étale topology, by its base
change along `W ⟶ Y`: that base change is étale, and surjective on points because the image has
the points of `W` as its points (Stacks 03H4). Over it the pullback of `L` is ample by
hypothesis, and the fpqc case of Stacks 0D3C descends ampleness to `Y'`. -/
theorem isRelativelyAmpleOver_image_of_isRelativelyAmpleAlong
    (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) {b : Z ⟶ Y.1} (hb : IsEtale B S hS b)
    {W : Subfunctor Z} (hW : IsOpenSubspace B S hS W) (h : IsRelativelyAmpleAlong f L b W) :
    IsRelativelyAmpleOver f L (openSubspaceOfPoints B S hS Y.1
      (Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ b)))) := by
  intro X' Y' g p f' hsq hfac
  let Wₛ : AlgebraicSpaces B S hS := ⟨W.toFunctor, hW.1⟩
  let c : Wₛ ⟶ Y := ObjectProperty.homMk (W.ι ≫ b)
  let Y'' : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS g c
  let q : Y'' ⟶ Y' := ObjectProperty.homMk (pullback.fst g.hom c.hom)
  let X'' : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS f' q
  let p'' : X'' ⟶ X' := ObjectProperty.homMk (pullback.fst f'.hom q.hom)
  let f'' : X'' ⟶ Y'' := ObjectProperty.homMk (pullback.snd f'.hom q.hom)
  have hsq'' : IsPullback p'' f'' f' q := AlgebraicSpaces.isPullback_fiberProduct B S hS f' q
  have hc : IsEtale B S hS c.hom := isEtale_comp B S hS (isEtale_ι_of_isOpenSubspace hW) hb
  have hcov : IsEtaleCovering B S hS (fun _ : PUnit.{u + 2} => Y''.1) (fun _ => q.hom) := by
    refine ⟨Y'.2, fun _ => Y''.2, fun _ => ?_, ?_⟩
    · exact isEtale_of_isPullback B S hS _ _ _ _
        (AlgebraicSpaces.isPullback_fiberProduct B S hS g c).flip hc
    · refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ⟨PUnit.unit, ?_⟩
      obtain ⟨l, hl⟩ := hfac
      obtain ⟨w, hw⟩ : pointsMap B S hS Y'.1 g.hom y ∈
          Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ b)) := by
        rw [← range_pointsMap_ι_openSubspaceOfPoints B S hS
          (Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ b))), ← hl, pointsMap_comp_apply]
        exact ⟨_, rfl⟩
      obtain ⟨z, hz, -⟩ := exists_points_of_isPullback B S hS
        (IsPullback.of_hasPullback g.hom c.hom) y w hw.symm
      exact ⟨z, hz⟩
  refine isRelativelyAmple_of_isFpqcCovering_comp hdesc hL p f' (fun _ : PUnit.{u + 2} => hsq'')
    (isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov) fun _ => ?_
  exact h (q ≫ g) (p'' ≫ p) f'' (hsq''.paste_horiz hsq)
    ⟨pullback.snd g.hom c.hom, (pullback.condition (f := g.hom) (g := c.hom)).symm⟩

/-- A field-valued point of `Y` which comes from a field-valued point of an étale chart, read on
that chart: if a field-valued point `t` of `Y` and the image of a field-valued point `w` of `Z`
under `b : Z ⟶ Y` have a common extension `r`, then `r` is the image of a field-valued point of
`Z`, namely the restriction of `w`. -/
theorem exists_fieldValuedPoint_map_eq {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : Z ⟶ Y.1)
    (r : FieldValuedPoint B S hS Y.1) (w : FieldValuedPoint B S hS Z)
    (hr : FieldValuedPoint.Dominates B S hS Y.1 r (FieldValuedPoint.map B S hS Z b w)) :
    ∃ r' : FieldValuedPoint B S hS Z, FieldValuedPoint.map B S hS Z b r' = r := by
  obtain ⟨β, hβ⟩ := hr
  let β' : r.siteObject ⟶ w.siteObject := β
  refine ⟨⟨r.carrier, r.contained, r.toBase, Z.map β'.op w.value⟩, ?_⟩
  obtain ⟨K, hK, tb, v⟩ := r
  simp only [FieldValuedPoint.map, FieldValuedPoint.mk.injEq, heq_eq_eq, true_and]
  exact (NatTrans.naturality_apply b β'.op w.value).trans hβ

/-- **Claim (A) of the proof of Stacks 0D3D, reduced to affine schemes étale over the target.**
Every field-valued point of `Y` over which the pullback of `L` is ample lies in
`AlgebraicGeometry.Space.relativelyAmpleLocus`, granted claim (A) over affine schemes étale over
`Y` and the fpqc case of Stacks 0D3C.

The point is the image of a point of an affine étale chart (Stacks 03BU); a common field-valued
extension `r` of the two lifts to the chart, ampleness over `r` follows by base change
(Stacks 0D33), the open subspace of the chart around `r` is pushed down to `Y` by
`isRelativelyAmpleOver_image_of_isRelativelyAmpleAlong`. -/
theorem mem_relativelyAmpleLocus_of_ampleNearFieldPointsOfAffines
    (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (hA : AmpleNearFieldPointsOfAffines f L)
    (t : FieldValuedPoint B S hS Y.1) {X'' : AlgebraicSpaces B S hS} (p'' : X'' ⟶ X)
    (f'' : X'' ⟶ representedAlgebraicSpace B S hS t.siteObject)
    (hsq : IsPullback p'' f'' f (ObjectProperty.homMk (yonedaEquiv.symm t.value)))
    (hamp : IsRelativelyAmple B S hS f'' ((modulePullback B S hS p'').obj L)) :
    t.class B S hS Y.1 ∈ relativelyAmpleLocus f L := by
  obtain ⟨U, b, hU, hbet, w, hw⟩ :=
    exists_affine_etale_chart_at_point B S hS Y.1 Y.2 (t.class _ _ _ _)
  have hb := (isEtale_iff_presheaf_of_yoneda B S hS b).mpr hbet
  obtain ⟨w₀, rfl⟩ := Quot.exists_rep w
  rw [pointsMap_class, FieldValuedPoint.class_eq_class_iff] at hw
  obtain ⟨r, hrw, ⟨α, hα⟩⟩ := hw
  obtain ⟨r', rfl⟩ := exists_fieldValuedPoint_map_eq b r w₀ hrw
  -- ampleness over `r`, by base change from `t`
  let e : representedAlgebraicSpace B S hS r'.siteObject ⟶
      representedAlgebraicSpace B S hS t.siteObject := ObjectProperty.homMk (yoneda.map α)
  obtain ⟨_, p₂, f₂, hsq₂, hamp₂⟩ := exists_isPullback_isRelativelyAmple_comp hsq e hamp
  have he : e ≫ ObjectProperty.homMk (yonedaEquiv.symm t.value) =
      (ObjectProperty.homMk (yonedaEquiv.symm r'.value ≫ b) :
        representedAlgebraicSpace B S hS r'.siteObject ⟶ Y) := by
    ext1
    change yoneda.map α ≫ yonedaEquiv.symm t.value = yonedaEquiv.symm r'.value ≫ b
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_left]
    exact congrArg yonedaEquiv.symm hα
  rw [he] at hsq₂
  obtain ⟨W, hW, hrW, hWamp⟩ := hA U hU b hb r' _ _ hsq₂ hamp₂
  refine ⟨_, isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale
      (isAlgebraicSpace_yoneda B S hS U) Y.2 hb hW,
    isRelativelyAmpleOver_image_of_isRelativelyAmpleAlong hdesc hL
      (isAlgebraicSpace_yoneda B S hS U) hb hW hWamp, ?_⟩
  rw [range_pointsMap_ι_openSubspaceOfPoints]
  obtain ⟨w', hw'⟩ := hrW
  refine ⟨w', ?_⟩
  rw [pointsMap_comp_apply, hw', pointsMap_class]
  exact (FieldValuedPoint.class_eq_class_iff B S hS Y.1 _ t).mpr
    ⟨_, FieldValuedPoint.dominates_refl B S hS Y.1 _, α, hα⟩

/-- **The open subspace of Stacks 0D3D, from claim (A) over affine schemes.** Granted the fpqc
case of Stacks 0D3C and claim (A) over affine schemes étale over `Y`, there is an open subspace
`V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of algebraic spaces factors through `V` if and only if
the pullback of `L` to the base change of `f` along `g` is ample. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleNearFieldPointsOfAffines
    (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (hA : AmpleNearFieldPointsOfAffines f L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) :=
  exists_isOpenSubspace_factors_iff_isRelativelyAmple hdesc hL fun t _ p'' f'' hsq hamp =>
    mem_relativelyAmpleLocus_of_ampleNearFieldPointsOfAffines hdesc hL hA t p'' f'' hsq hamp

end AlgebraicGeometry.Space

end
