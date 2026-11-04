module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStandardCoverings

/-!
# Cofinality of the standard coverings in the size-bounded small étale site

Let `S` be a scheme contained in a big étale site `B`.  The small étale category of
[Stacks, Tag 021B], `AlgebraicGeometry.SmallEtale B S hS`, consists of the schemes étale over
`S` whose size is below the cutoff of `B`; it sits inside Mathlib's choice-free small étale site
`AlgebraicGeometry.Scheme.Etale` through `AlgebraicGeometry.SmallEtale.toEtaleSite`.

This file proves that the *standard* étale coverings of [Stacks, Tag 03X9] are cofinal among the
covering sieves of an object with affine total space, **on the size-bounded site**: a covering
sieve of such an object contains a family of the size-bounded site whose image under
`toEtaleSite` is a small-étale-standard covering in the sense of
`AlgebraicGeometry.IsSmallEtaleStandardCovering`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.objOfEtale`: a scheme below the size cutoff, étale over `S`, as
  an object of the size-bounded small étale site.
* `AlgebraicGeometry.SmallEtale.homMk` and `AlgebraicGeometry.SmallEtale.homOfEtale`: a morphism
  of such objects, from a morphism of the underlying schemes commuting with the structure
  morphisms.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isSmallEtaleStandardCovering_map_sieve₀_le`:
  **cofinality of the standard coverings on the size-bounded small étale site.**

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme below the size cutoff of `B`, étale over `S`, as an object of the size-bounded
small étale site of `S`. -/
@[implicit_reducible]
public def objOfEtale {V : Scheme.{u}} (hV : B.Contains V) (p : V ⟶ S) (hp : Etale p) :
    SmallEtale B S hS :=
  ⟨Over.mk (ObjectProperty.homMk (X := B.obj V hV) (Y := B.obj S hS) p), hp⟩

/-- A morphism of the size-bounded small étale site of `S`, from a morphism of the underlying
schemes commuting with the structure morphisms. -/
@[implicit_reducible]
public def homMk {X Y : SmallEtale B S hS} (g : X.obj.left.obj ⟶ Y.obj.left.obj)
    (hg : g ≫ Y.obj.hom.hom = X.obj.hom.hom) : X ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk g)
    (by apply ObjectProperty.hom_ext; exact hg))

/-- A morphism of the size-bounded small étale site out of
`AlgebraicGeometry.SmallEtale.objOfEtale`, from a morphism of the underlying schemes commuting
with the structure morphisms. -/
@[implicit_reducible]
public def homOfEtale (T : SmallEtale B S hS) {V : Scheme.{u}} (hV : B.Contains V) {p : V ⟶ S}
    (hp : Etale p) (g : V ⟶ T.obj.left.obj) (hg : g ≫ T.obj.hom.hom = p) :
    objOfEtale B S hS hV p hp ⟶ T :=
  homMk B S hS (X := objOfEtale B S hS hV p hp) g hg

/-- **Cofinality of the standard coverings on the size-bounded small étale site.**  Every
covering sieve of an object of `AlgebraicGeometry.SmallEtale B S hS` whose total space is affine
contains a family of that site whose image in Mathlib's small étale site is a
small-étale-standard covering.

This is [Stacks, Tag 03XA] on the site of [Stacks, Tag 021B]. -/
public theorem exists_isSmallEtaleStandardCovering_map_sieve₀_le (T : SmallEtale B S hS)
    (hT : _root_.AlgebraicGeometry.IsAffine T.obj.left.obj) {R : Sieve T}
    (hR : R ∈ topology B S hS T) :
    ∃ 𝒱 : PreZeroHypercover.{u} T,
      IsSmallEtaleStandardCovering S (𝒱.map (toEtaleSite B S hS)) ∧ 𝒱.sieve₀ ≤ R := by
  classical
  have _ := hT
  have hTet : Etale T.obj.hom.hom := T.property
  choose W g hgR hgx using fun x ↦ exists_mem_arrows_mem_range B S hS hR x
  have h𝒰 : (PreZeroHypercover.mk (I₀ := T.obj.left.obj.carrier)
      (fun x ↦ (toScheme B S hS).obj (W x))
      (fun x ↦ (toScheme B S hS).map (g x))).presieve₀ ∈
        Scheme.precoverage (coveringMorphismProperty .etale) T.obj.left.obj :=
    (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨x, hgx x⟩, fun x ↦ inferInstanceAs (Etale ((toScheme B S hS).map (g x)))⟩
  obtain ⟨𝒲, r, h𝒲⟩ := exists_standardCovering_refinement .etale _ h𝒰
  have hsize : ∀ j, B.Contains (𝒲.X j) := fun j ↦
    size_lt_cutoff_of_isStandardCovering .etale B h𝒲 T.obj.left.property j
  have hpet : ∀ j, Etale (𝒲.f j ≫ T.obj.hom.hom) := fun j ↦
    have : Etale (𝒲.f j) := h𝒲.standard j
    inferInstance
  refine ⟨{ I₀ := 𝒲.I₀
            X := fun j ↦ objOfEtale B S hS (hsize j) (𝒲.f j ≫ T.obj.hom.hom) (hpet j)
            f := fun j ↦ homOfEtale B S hS T (hsize j) (hpet j) (𝒲.f j) rfl }, ⟨hT, h𝒲⟩, ?_⟩
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
    Presieve.ofArrows_le_iff]
  intro j
  have hw : r.h₀ j ≫ (W (r.s₀ j)).obj.hom.hom = 𝒲.f j ≫ T.obj.hom.hom := by
    have hover : (toScheme B S hS).map (g (r.s₀ j)) ≫ T.obj.hom.hom =
        (W (r.s₀ j)).obj.hom.hom :=
      congrArg (fun k ↦ k.hom) (CategoryTheory.Over.w ((inclusion B S hS).map (g (r.s₀ j))))
    rw [← hover, ← Category.assoc, r.w₀ j]
  have heq : homOfEtale B S hS (W (r.s₀ j)) (hsize j) (hpet j) (r.h₀ j) hw ≫ g (r.s₀ j) =
      homOfEtale B S hS T (hsize j) (hpet j) (𝒲.f j) rfl :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ (r.w₀ j)))
  have hmem := R.downward_closed (hgR (r.s₀ j))
    (homOfEtale B S hS (W (r.s₀ j)) (hsize j) (hpet j) (r.h₀ j) hw)
  rwa [heq] at hmem

end AlgebraicGeometry.SmallEtale

end
