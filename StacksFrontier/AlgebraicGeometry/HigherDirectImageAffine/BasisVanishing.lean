module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheafification of a presheaf that vanishes on a basis

A presheaf on a topological space whose sections over the members of a *basis* of opens vanish
need not vanish; but its sheafification does. This file proves that, in the two forms needed to
read off the vanishing of a cohomology sheaf from the vanishing of the underlying cohomology
presheaf on a basis — which is how [Stacks, Tag 01XC] is deduced from [Stacks, Tag 01XB].

The argument is the separatedness half of the sheaf axiom and nothing else. If `φ : P ⟶ Q` is a
morphism of presheaves of abelian groups with `Q` a sheaf and with `P` vanishing on a basis `B`,
then `φ = 0`: a section `x` of `P` over an open `W` maps to a section of `Q` over `W` whose
restriction to each member of a covering of `W` by elements of `B` factors through a zero group,
and a section of a sheaf vanishing locally vanishes. Applying this to the unit of the
sheafification adjunction makes the unit zero, and a left adjoint sends an object with zero unit
to a zero object.

## Main results

* `Stacks.Topology.BasisVanishing.isZero_leftAdjoint_obj_of_unit_eq_zero`: if the unit of an
  adjunction `L ⊣ G` between preadditive categories vanishes at `P`, then `L.obj P` is a zero
  object.
* `Stacks.Topology.BasisVanishing.eq_zero_of_isZero_on_basis`: a morphism from a presheaf
  vanishing on a basis into a sheaf is zero.
* `Stacks.Topology.BasisVanishing.isZero_sheafification_of_isZero_on_basis`: the sheafification
  of a presheaf of modules whose underlying presheaf of abelian groups vanishes on a basis is a
  zero object.

## Implementation notes

The statements are given for presheaves spelled as functors `(Opens X)ᵒᵖ ⥤ AddCommGrpCat` rather
than as `TopCat.Presheaf AddCommGrpCat X`: the two are definitionally equal, but
`CategoryTheory.Preadditive` is found by instance search only for the former, so the zero
morphism cannot even be written with the latter spelling.

The covering of an arbitrary open by basis elements is the one supplied by
`TopologicalSpace.Opens.isBasis_iff_cover`, whose index type is the covering family itself as a
subtype; `TopCat.Sheaf.eq_of_locally_eq'` then takes the inclusions directly, so no `eqToHom`
transport along `W = sSup Us` is needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.BasisVanishing

/-- **An object with vanishing adjunction unit is sent to a zero object by the left adjoint.**
If `L ⊣ G` is an adjunction of preadditive categories, `G` preserves zero morphisms and the unit
of the adjunction vanishes at `P`, then `L.obj P` is a zero object.

Indeed `Hom(L.obj P, L.obj P) ≃ Hom(P, G.obj (L.obj P))` sends both the identity and the zero
morphism to the unit at `P`, which is zero. -/
theorem isZero_leftAdjoint_obj_of_unit_eq_zero {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
    [G.PreservesZeroMorphisms] (P : C) (h : adj.unit.app P = 0) : IsZero (L.obj P) := by
  rw [IsZero.iff_id_eq_zero]
  apply (adj.homEquiv P (L.obj P)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp [h]

variable {X : TopCat.{u}}

/-- **A morphism from a presheaf vanishing on a basis into a sheaf is zero.** Let `B` be a basis
of opens of `X`, let `P` be a presheaf of abelian groups with `P(V) = 0` for every `V ∈ B`, and
let `Q` be a sheaf. Then every morphism `P ⟶ Q` is zero.

A section of `P` over `W` is carried to a section of `Q` over `W` all of whose restrictions to
the members of a covering of `W` by elements of `B` vanish, because they factor through the zero
groups `P(V)`; separatedness of `Q` concludes. -/
theorem eq_zero_of_isZero_on_basis {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hQ : TopCat.Presheaf.IsSheaf Q) (φ : P ⟶ Q) {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hP : ∀ V ∈ B, IsZero (P.obj (op V))) : φ = 0 := by
  apply NatTrans.ext
  funext W
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  obtain ⟨Us, hUs, hW⟩ := Opens.isBasis_iff_cover.mp hB W.unop
  have hle : ∀ i : Us, (i : Opens X) ≤ W.unop := fun i => hW ▸ le_sSup i.2
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨Q, hQ⟩)
      (fun i : Us => (i : Opens X)) W.unop (fun i => homOfLE (hle i))
      (by rw [hW, sSup_eq_iSup']) _ _ fun i => ?_
  have h0 : P.map (homOfLE (hle i)).op = 0 := (hP _ (hUs i.2)).eq_zero_of_tgt _
  rw [← NatTrans.naturality_apply (F := P) φ (homOfLE (hle i)).op x, h0]
  simp

variable {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The sheafification of a presheaf of modules vanishing on a basis is a zero object.** If the
underlying presheaf of abelian groups of `P` has vanishing sections over every member of a basis
`B` of opens of `X`, then the associated sheaf of modules is zero.

The unit of the sheafification adjunction at `P` is zero, because on underlying presheaves of
abelian groups it is the canonical map to the sheafification, which `eq_zero_of_isZero_on_basis`
makes zero; and `isZero_leftAdjoint_obj_of_unit_eq_zero` turns that into the vanishing of the
sheafification. -/
theorem isZero_sheafification_of_isZero_on_basis (P : PresheafOfModules.{u} R.obj)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hP : ∀ V ∈ B, IsZero (P.presheaf.obj (op V))) :
    IsZero ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) := by
  refine isZero_leftAdjoint_obj_of_unit_eq_zero
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) P ?_
  refine (PresheafOfModules.toPresheaf R.obj).map_injective ?_
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app, Functor.map_zero]
  exact eq_zero_of_isZero_on_basis
    ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj P.presheaf).2 _ hB hP

end Stacks.Topology.BasisVanishing

end
