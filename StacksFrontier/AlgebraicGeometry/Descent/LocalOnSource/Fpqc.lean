module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Injective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Defs
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion

/-!
# Flatness and stalkwise injectivity are fpqc-local on the source

A morphism of schemes is flat if and only if its composites with the members of an fpqc
covering family of its source are flat, and likewise it induces injective maps on all local
rings if and only if the composites do. In both cases the covering members are themselves flat
and jointly surjective, so the local rings of the source are flat over the local rings upstairs
by faithful flatness of a flat local homomorphism.

## Main results

* `AlgebraicGeometry.flat_isLocalAtSource_fpqc` says that flatness is local on the source for
  the fpqc precoverage.
* `AlgebraicGeometry.stalkwiseInjective_isLocalAtSource_fpqc` says the same for injectivity of
  all the maps of local rings.

## Implementation notes

Flatness is Mathlib's morphism property `AlgebraicGeometry.Flat`, injectivity on local rings is
`AlgebraicGeometry.stalkwise` applied to injectivity of ring homomorphisms, and fpqc coverings
are those of `AlgebraicGeometry.Scheme.fpqcPrecoverage`. Both locality classes also record the
isomorphism invariance of the property.

## References

* [Stacks Project, Tag 036K](https://stacks.math.columbia.edu/tag/036K)
* [Stacks Project, Tag 036L](https://stacks.math.columbia.edu/tag/036L)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For a tower of flat local homomorphisms of local rings, flatness of the first map is
equivalent to flatness of the composite: compositions of flat maps are flat, and conversely a
flat composite descends along the second map, which is faithfully flat because it is a flat
local homomorphism. -/
@[ega "0 6.6.4" "special case"]
private theorem flat_iff_flat_comp_of_local_homs
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (f : A →+* B) (g : B →+* C) [IsLocalHom f] [IsLocalHom g]
    (hg : g.Flat) : f.Flat ↔ (g.comp f).Flat := by
  refine ⟨fun hf ↦ RingHom.Flat.comp hf hg, fun hcomp ↦ ?_⟩
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat A C := hcomp
  have : Module.Flat B C := hg
  have : IsLocalHom (algebraMap B C) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat (R := A) (S := B) C

/-- Flatness of scheme morphisms is fpqc-local on the source. -/
@[stacks 036K]
public instance flat_isLocalAtSource_fpqc :
    MorphismProperty.IsLocalAtSource (@Flat : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)).toRespects
  refine MorphismProperty.IsLocalAtSource.mk_of_iff fun {X Y} f R hR ↦ ?_
  change R ∈ (Scheme.qcPrecoverage ⊓
    Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})) X at hR
  constructor
  · intro hf U g hg
    exact MorphismProperty.comp_mem (@Flat : MorphismProperty Scheme.{u}) g f
      (hR.2.2 hg) hf
  · intro h
    refine Flat.of_stalkMap f fun x ↦ ?_
    obtain ⟨U, g, hg, ⟨y, hy⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hR.2.1 x
    obtain rfl : g y = x := by simpa only [Scheme.forget_map'] using hy
    have : Flat (g ≫ f) := h hg
    have hgf' := Flat.stalkMap (g ≫ f) y
    rw [Scheme.Hom.stalkMap_comp] at hgf'
    change ((g.stalkMap y).hom.comp (f.stalkMap (g y)).hom).Flat at hgf'
    have : Flat g := hR.2.2 hg
    exact (flat_iff_flat_comp_of_local_homs
      (f.stalkMap (g y)).hom (g.stalkMap y).hom (Flat.stalkMap g y)).2 hgf'

/-- Injectivity of all the local-ring maps of a scheme morphism is fpqc-local on its source. -/
@[stacks 036L]
public instance stalkwiseInjective_isLocalAtSource_fpqc :
    MorphismProperty.IsLocalAtSource
      (stalkwise (fun f => Function.Injective f) : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  have : (stalkwise (fun f => Function.Injective f) : MorphismProperty Scheme.{u}).RespectsIso :=
    stalkwise_respectsIso RingHom.injective_respectsIso
  refine MorphismProperty.IsLocalAtSource.mk_of_iff fun {X Y} f R hR ↦ ?_
  change R ∈ (Scheme.qcPrecoverage ⊓ Scheme.precoverage
    (@Flat : MorphismProperty Scheme.{u})) X at hR
  constructor
  · intro hf U g hg y
    have : Flat g := hR.2.2 hg
    rw [Scheme.Hom.stalkMap_comp]
    change Function.Injective ((g.stalkMap y).hom.comp (f.stalkMap (g y)).hom)
    have hinj : Function.Injective (g.stalkMap y).hom := by
      have hgy : (g.stalkMap y).hom.Flat := Flat.stalkMap g y
      let := (g.stalkMap y).hom.toAlgebra
      have : IsLocalHom
          (algebraMap ↑(X.presheaf.stalk (g.base y)) ↑(U.presheaf.stalk y)) := by
        rw [RingHom.algebraMap_toAlgebra]
        infer_instance
      have : Module.Flat ↑(X.presheaf.stalk (g.base y)) ↑(U.presheaf.stalk y) := hgy
      exact RingHom.FaithfullyFlat.injective Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact fun a b hab ↦ hf (g y) (hinj hab)
  · intro h x
    obtain ⟨U, g, hg, ⟨y, hy⟩⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
        (F := Scheme.forget)).mp hR.2.1 x
    obtain rfl : g y = x := by simpa only [Scheme.forget_map'] using hy
    have hcomp := h hg y
    rw [Scheme.Hom.stalkMap_comp] at hcomp
    exact fun a b hab ↦ hcomp (congrArg (g.stalkMap y).hom hab)

end AlgebraicGeometry
