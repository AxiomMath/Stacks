module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Flatness of morphisms of algebraic spaces is fpqc local on the source and on the target

Let `S` be a scheme contained in a big fppf site `B`. Flatness of a morphism of algebraic
spaces over `S` is the chart condition `AlgebraicGeometry.Space.IsFlat` of **Stacks 03ML**,
part (1). It is local on the source for the fpqc topology of **Stacks 03YH** (**Stacks 06ET**)
and local on the target for it (**Stacks 041W**).

Source locality is the fpqc case of **Stacks 06ER** applied to flatness of morphisms of
schemes, which is étale local on the source and target (**Stacks 04R3**, flat case) and fpqc
local on the source (**Stacks 036K**).

Target locality is the source's argument for Stacks 041W, transposed to the covering families
of algebraic spaces rather than to Stacks 041J's affine criterion. In one direction, flatness
is stable under base change (**Stacks 03MO**). In the other, the base changes of the given
morphism along the members of the covering form an fpqc covering of its source, so by source
locality it suffices that each composite `X ×_Y Yᵢ ⟶ X ⟶ Y` be flat; that composite is the
other projection followed by `Yᵢ ⟶ Y`, and both of those are flat, so **Stacks 03MN** applies.
The fpqc covering property of the base-changed family is proved here directly from the
refinement clause of **Stacks 03MQ**: a finite affine fpqc refinement of an affine
scheme-valued point of `X` factoring through the original family lifts to one factoring through
the base-changed family, by the universal property of the fibre product.

## Main results

* `AlgebraicGeometry.Space.isFlat_isLocalAtSource_fpqc`: **Stacks 06ET**.
* `AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fpqc`: **Stacks 041W**.

## Implementation notes

Both are registered as instances, which is the form the relative properties of Chapters 100
and 101 consume them in: `AlgebraicGeometry.Stack.HasRelativeProperty` and the smooth-locality
criterion of **Stacks 06FB** take exactly these two as instance arguments.

These are **Chapter 74 results** (Descent on Spaces).

## References

* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 06ET](https://stacks.math.columbia.edu/tag/06ET)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

/-- **Stacks 06ET.** Flatness of morphisms of algebraic spaces over `S` is local on the source
for the fpqc topology. -/
@[stacks 06ET]
instance isFlat_isLocalAtSource_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFlat B S hS f.hom)
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  isLocalAtSource_fpqc_of_schemes B S hS
    (@Flat.{u} : MorphismProperty Scheme.{u}) Flat.isEtaleLocalOnSourceAndTarget

/-- The base change of an fpqc covering family of algebraic spaces over `S` along a morphism of
algebraic spaces, taken as the family of *first* projections out of the fibre products, is an
fpqc covering of the new base.

Flatness of each projection is base-change stability of flatness (Stacks 03MO). For the
refinement clause, an affine scheme-valued point `h` of the new base is composed with the
morphism to get an affine scheme-valued point of the old base, refined there by a finite affine
fpqc family factoring through the original covering; each member of that refinement then
factors through the corresponding fibre product by the universal property. -/
theorem isFpqcCovering_pullback_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {Y : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
    (g : ∀ i, Yi i ⟶ Y) (hcover : IsFpqcCovering B S hS (fun i => (g i).hom))
    (X : AlgebraicSpaces B S hS) (f : X ⟶ Y) :
    IsFpqcCovering B S hS (fun i => (pullback.fst f (g i)).hom) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃A C⦄ (q : A ⟶ C) => IsFlat B S hS q.hom
  let : ∀ i, HasPullback f (g i) := fun i =>
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f (g i)).hasPullback
  let : P.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange B S hS
  refine ⟨fun i => MorphismProperty.pullback_fst (P := P) f (g i) (hcover.1 i), fun T h => ?_⟩
  obtain ⟨U, hfinite, hU, hfactor⟩ := hcover.2 T (h ≫ f.hom)
  refine ⟨U, hfinite, hU, fun j => ?_⟩
  obtain ⟨i, a, ha⟩ := hfactor j
  let Z := schemeSpace ((BigAffineFppf.inclusion B S hS).obj (U.X j))
  let k : Z ⟶ X := ObjectProperty.homMk
    (yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)) ≫ h)
  let aj : Z ⟶ Yi i := ObjectProperty.homMk a
  have hcomm : k ≫ f = aj ≫ g i := by
    apply ObjectProperty.hom_ext
    change (yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)) ≫ h) ≫
      f.hom = a ≫ (g i).hom
    simpa only [Category.assoc] using ha.symm
  refine ⟨i, (pullback.lift k aj hcomm).hom, ?_⟩
  change ((pullback.lift k aj hcomm) ≫ pullback.fst f (g i)).hom = _
  rw [pullback.lift_fst]
  rfl

/-- **Stacks 041W.** Flatness of a morphism of algebraic spaces over `S` is local on the target
for the fpqc topology. -/
@[stacks 041W]
instance isFlat_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFlat B S hS f.hom)
      (Topology.fpqc.precoverage.{u, v} B S hS) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃X Y⦄ (f : X ⟶ Y) => IsFlat B S hS f.hom
  let : P.IsLocalAtSource (Topology.fpqc.precoverage.{u, v} B S hS) :=
    isFlat_isLocalAtSource_fpqc B S hS
  let : P.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange B S hS
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff (P := P) ?_
  rintro X Y f _ ⟨I, Yi, g, rfl, hcover⟩
  refine ⟨fun hf Z k _ hmem => ?_, fun hflat => ?_⟩
  · obtain ⟨i, hZ, hk⟩ := Presieve.ofArrows_surj g k hmem
    cases hZ
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst k
    exact MorphismProperty.pullback_snd (P := P) f (g i) hf
  let Pᵢ : I → AlgebraicSpaces B S hS := fun i => pullback f (g i)
  let p : ∀ i, Pᵢ i ⟶ X := fun i => pullback.fst f (g i)
  have hmem : Presieve.ofArrows Pᵢ p ∈ (Topology.fpqc.precoverage.{u, v} B S hS) X :=
    ⟨I, Pᵢ, p, rfl, X.property, fun i => (Pᵢ i).property,
      isFpqcCovering_pullback_fst B S hS Yi g hcover.2.2 X f⟩
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hmem fun Z q hq => ?_
  obtain ⟨i, hZ, hq⟩ := Presieve.ofArrows_surj p q hq
  cases hZ
  simp only [eqToHom_refl, Category.id_comp] at hq
  subst q
  have hcomp : (p i).hom ≫ f.hom = (pullback.snd f (g i)).hom ≫ (g i).hom := by
    have hcond : p i ≫ f = pullback.snd f (g i) ≫ g i := pullback.condition
    exact congrArg (·.hom) hcond
  change IsFlat B S hS ((p i).hom ≫ f.hom)
  rw [hcomp]
  exact isFlat_comp B S hS (Pᵢ i).property (Yi i).property Y.property
    (pullback.snd f (g i)).hom (g i).hom
    (hflat (g i) (Presieve.ofArrows.mk i)) (hcover.2.2.1 i)

end AlgebraicGeometry.Space

end
