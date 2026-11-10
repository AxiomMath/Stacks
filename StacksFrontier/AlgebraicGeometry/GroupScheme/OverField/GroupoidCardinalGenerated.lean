module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGeneratedSmall

/-!
# Cardinally generated modules on a groupoid scheme form a set

For a groupoid scheme and a cardinal `κ`, the `κ`-generated quasi-coherent modules equipped
with groupoid descent data have only a set of isomorphism classes.  The underlying modules
already do, and the descent morphisms over a fixed underlying module form a subtype of a single
morphism set, so the forgetful functor has essentially small fibres.

## Main results

* `AlgebraicGeometry.essentiallySmall_isCardinalGenerated`: cardinally generated quasi-coherent
  modules on a groupoid scheme form an essentially small class.

## Implementation notes

The source's set of representatives is expressed as essential smallness of the object property
on the category of quasi-coherent modules with groupoid descent data.  The property is imposed
on the underlying module.  The result is stated for every cardinal, since the source's proof
does not use infinitude.

## References

* [Stacks Project, Tag 077T](https://stacks.math.columbia.edu/tag/077T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Stacks.Groupoids
open Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry

universe u

/-- Over a fixed module on the object scheme, the quasi-coherent modules with descent data whose
underlying module is isomorphic to it form an essentially small class. -/
private theorem essentiallySmall_fiber {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (Y : G.objects.left.Modules) :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : QuasicoherentModule G =>
        Nonempty ((QuasicoherentModule.forget G).obj M ≅ Y)) := by
  classical
  let C := QuasicoherentModule G
  let αAt := fun (M : C) (e : M.module ≅ Y) =>
    (Scheme.Modules.pullback G.target.left).map e.inv ≫ M.alpha ≫
      (Scheme.Modules.pullback G.source.left).map e.hom
  let A := {a : (Scheme.Modules.pullback G.target.left).obj Y ⟶
        (Scheme.Modules.pullback G.source.left).obj Y //
      ∃ (M : C) (e : M.module ≅ Y), αAt M e = a}
  refine ⟨ObjectProperty.ofObj (fun a : A => Classical.choose a.2), inferInstance, ?_⟩
  rintro M ⟨e⟩
  let a : A := ⟨αAt M e, ⟨M, e, rfl⟩⟩
  let M₀ : C := Classical.choose a.2
  obtain ⟨e₀, hα⟩ := Classical.choose_spec a.2
  change αAt M₀ e₀ = αAt M e at hα
  have compat (N N' : C) (d : N.module ≅ Y) (d' : N'.module ≅ Y)
      (h : αAt N' d' = αAt N d) :
      N.alpha ≫ (Scheme.Modules.pullback G.source.left).map (d.hom ≫ d'.inv) =
        (Scheme.Modules.pullback G.target.left).map (d.hom ≫ d'.inv) ≫ N'.alpha := by
    simpa [αAt, Functor.map_comp, Category.assoc] using
      (congrArg (fun z => (Scheme.Modules.pullback G.target.left).map d.hom ≫ z ≫
        (Scheme.Modules.pullback G.source.left).map d'.inv) h).symm
  let f : M.module ≅ M₀.module := e.trans e₀.symm
  let i : M ≅ M₀ :=
    { hom := ⟨f.hom, compat M M₀ e e₀ hα⟩
      inv := ⟨f.inv, compat M₀ M e₀ e hα.symm⟩
      hom_inv_id := by
        apply QuasicoherentModule.Hom.ext
        change f.hom ≫ f.inv = 𝟙 _
        simp [f]
      inv_hom_id := by
        apply QuasicoherentModule.Hom.ext
        change f.inv ≫ f.hom = 𝟙 _
        simp [f] }
  exact ⟨M₀, ⟨a⟩, ⟨i⟩⟩

/-- The `κ`-generated quasi-coherent modules on a groupoid scheme have only a set of
isomorphism classes. -/
@[stacks 077T]
theorem essentiallySmall_isCardinalGenerated {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : QuasicoherentModule G ↦
        Stacks.AlgebraicGeometry.CardinalGeneration.IsCardinalGenerated M.module κ) := by
  classical
  let F := QuasicoherentModule.forget G
  let P : ObjectProperty (QuasicoherentModule G) :=
    fun M => Stacks.AlgebraicGeometry.CardinalGeneration.IsCardinalGenerated M.module κ
  let Q : ObjectProperty G.objects.left.Modules :=
    fun M => Stacks.AlgebraicGeometry.CardinalGeneration.IsCardinalGenerated M κ
  let _ : ObjectProperty.EssentiallySmall.{u} Q :=
    AlgebraicGeometry.CardinalGenerated.essentiallySmall_isCardinalGenerated
      (X := G.objects.left.toRingedSpace) κ
  apply ObjectProperty.EssentiallySmall.of_functor P F
  · apply ObjectProperty.EssentiallySmall.of_le (Q := Q.isoClosure)
    rintro M ⟨N, hN, ⟨e⟩⟩
    exact ⟨F.obj N, hN, ⟨e.symm⟩⟩
  · intro Y
    let _ : ObjectProperty.EssentiallySmall.{u}
        (fun M : QuasicoherentModule G => Nonempty (F.obj M ≅ Y)) :=
      essentiallySmall_fiber G Y
    exact ObjectProperty.EssentiallySmall.of_le (P := _ ⊓ _) (Q := _)
      (fun _ h => h.2)

end AlgebraicGeometry

end
