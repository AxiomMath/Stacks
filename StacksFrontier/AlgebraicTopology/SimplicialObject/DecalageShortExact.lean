module

public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit
public import StacksFrontier.RingTheory.Flat.ShortExact

/-!
# The reduced décalage as a flat covering, and its short exact sequence

Let `B` be a commutative ring and `Y` a simplicial `B`-module whose Moore complex has vanishing
homology in degree zero. The reduced décalage `decRed Y` then covers `Y`, and the covering is a
short exact sequence of simplicial modules

`0 ⟶ decRedKer Y ⟶ decRed Y ⟶ Y ⟶ 0`

whose middle term is acyclic and whose first two terms are degreewise flat when `Y` is.

## Main definitions

* `StacksDraft.SimplicialTensor.decRedKer`: the degreewise kernel of the covering
  `decRed Y ⟶ Y`.
* `StacksDraft.SimplicialTensor.decRedShortComplex`: the short complex
  `decRedKer Y ⟶ decRed Y ⟶ Y`.

## Main results

* `StacksDraft.SimplicialTensor.flat_decRed`: the reduced décalage of a degreewise flat
  simplicial module is degreewise flat.
* `StacksDraft.SimplicialTensor.flat_decRedKer`: so is the kernel of the covering.
* `StacksDraft.SimplicialTensor.decRedShortComplex_shortExact`: the short complex is short exact.
* `StacksDraft.SimplicialTensor.isZero_homology_decRed'`: the Moore complex of the middle term is
  acyclic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject
open Opposite AlgebraicTopology

open scoped Simplicial

universe u

namespace StacksDraft.SimplicialTensor

variable {B : Type u} [CommRing B] (Y : SimplicialObject (ModuleCat.{u} B))

/-- The reduced décalage of a degreewise flat simplicial module is degreewise flat. -/
public lemma flat_decRed (hY : ∀ n, Module.Flat B (Y.obj n)) (n : SimplexCategoryᵒᵖ) :
    Module.Flat B ((decRed Y).obj n) := by
  have : Module.Flat B ((dec Y).obj n) := hY (op (SimplexCategory.shift.obj n.unop))
  have h := congrArg ModuleCat.Hom.hom (NatTrans.congr_app (decRedι_comp_decRedπ Y) n)
  rw [NatTrans.comp_app, ModuleCat.hom_comp, NatTrans.id_app, ModuleCat.hom_id] at h
  exact Module.Flat.of_retract ((decRedι Y).app n).hom ((decRedπ Y).app n).hom h

/-- The kernel of the covering of `Y` by its reduced décalage: the degreewise kernel of
`decRedδ₀ Y : decRed Y ⟶ Y`. -/
public def decRedKer : SimplicialObject (ModuleCat.{u} B) :=
  simpKer (decRedδ₀ Y)

/-- If `Y` is degreewise flat and its Moore complex has vanishing homology in degree zero, the
kernel `decRedKer Y` of the covering `decRed Y ⟶ Y` is degreewise flat. -/
public lemma flat_decRedKer (hY : ∀ n, Module.Flat B (Y.obj n))
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj Y).homology 0))
    (n : SimplexCategoryᵒᵖ) :
    Module.Flat B ((decRedKer Y).obj n) := by
  have : Module.Flat B ((decRed Y).obj n) := flat_decRed Y hY n
  have : Module.Flat B (Y.obj n) := hY n
  exact _root_.flat_of_flat_of_flat_quotient
    (LinearMap.ker ((decRedδ₀ Y).app n).hom).subtype ((decRedδ₀ Y).app n).hom
    (LinearMap.ker ((decRedδ₀ Y).app n).hom).injective_subtype
    (LinearMap.exact_subtype_ker_map ((decRedδ₀ Y).app n).hom)
    (decRedδ₀_app_surjective Y h₀ n.unop.len)

/-- The short complex of simplicial modules `decRedKer Y ⟶ decRed Y ⟶ Y` given by the covering of
`Y` by its reduced décalage and the degreewise kernel of that covering. -/
public def decRedShortComplex : ShortComplex (SimplicialObject (ModuleCat.{u} B)) where
  X₁ := decRedKer Y
  X₂ := decRed Y
  X₃ := Y
  f := simpKerι (decRedδ₀ Y)
  g := decRedδ₀ Y
  zero := simpKerι_comp (decRedδ₀ Y)

/-- If the Moore complex of `Y` has vanishing homology in degree zero, the short complex
`decRedKer Y ⟶ decRed Y ⟶ Y` is short exact. -/
public lemma decRedShortComplex_shortExact
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj Y).homology 0)) :
    (decRedShortComplex Y).ShortExact :=
  ShortComplex.shortExact_of_app _ fun n =>
    ModuleCat.shortComplex_shortExact _
      (LinearMap.exact_subtype_ker_map ((decRedδ₀ Y).app n).hom)
      (LinearMap.ker ((decRedδ₀ Y).app n).hom).injective_subtype
      (decRedδ₀_app_surjective Y h₀ n.unop.len)

/-- The Moore complex of the reduced décalage `decRed Y` has vanishing homology in every
degree. -/
public lemma isZero_homology_decRed' (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (decRed Y)).homology n) :=
  isZero_homology_decRed Y n

end StacksDraft.SimplicialTensor

end
