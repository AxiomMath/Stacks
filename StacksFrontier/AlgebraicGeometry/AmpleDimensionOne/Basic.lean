module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.GloballyGenerated
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksCore.Tactic.StacksAttribute

/-!
# Ample invertible sheaves on one-dimensional integral schemes

A Noetherian integral separated scheme of topological Krull dimension one has an ample invertible
sheaf ([Stacks, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)). The source's proof is four
sentences: cover `X` by affine opens `U_i`, observe that each `X \ U_i` is finite, apply
[Tag 09NB](https://stacks.math.columbia.edu/tag/09NB) to get a globally generated invertible sheaf
`L_i` with a global section `s_i` satisfying `U_i = X_{s_i}`, and conclude by
[Tag 09NC](https://stacks.math.columbia.edu/tag/09NC).

Tag 09NB is available
  (`AlgebraicGeometry.exists_isInvertible_generatingSections_nonvanishingOpen_eq`);
Tag 09NC is not. So Tag 09NC is carried here as the explicit hypothesis `h09NC` of
`Stacks.AlgebraicGeometry.AmpleDimensionOne.exists_ample_invertible_of_09NC`, stated verbatim in
  the library's names for the
notions it mentions. Everything else the source's proof needs is proved here outright, and no
`@[stacks 09ND]` attribute is attached while the hypothesis is there.

The three geometric facts the reduction rests on are stated separately, because they are about a
one-dimensional integral scheme and nothing about ampleness, and two of them had been recorded as
missing from the library.

## Main results

* `Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint`: every point
  of a one-dimensional
  integral scheme other than the generic point is closed.
* `Stacks.AlgebraicGeometry.AmpleDimensionOne.finite_compl_of_ne_bot`: the complement of a nonempty
  open in a Noetherian
  integral scheme of dimension one is finite.
* `Stacks.AlgebraicGeometry.AmpleDimensionOne.ringKrullDim_stalk_eq_one_of_ne_genericPoint`: the
  local ring at a non-generic
  point of such a scheme has Krull dimension one.
* `Stacks.AlgebraicGeometry.AmpleDimensionOne.exists_ample_invertible_of_09NC`: **Tag 09ND given
  Tag 09NC.**

## Implementation notes

The three geometric facts come from the purely topological
`StacksFrontier/Topology/Dimension/DimensionLEOne.lean`, whose hypothesis is that a closed set
contains no irreducible component. On an integral scheme there is exactly one irreducible
component, the whole space (`irreducibleComponents_eq_singleton`), so that hypothesis becomes
"does not contain the generic point", which for `closure {x}` is `x ≠ genericPoint X` and for the
complement of an open is nonemptiness of the open.

The dimension of the local ring is read off the coheight of the point in the specialization order
through Mathlib's `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`. The order is a `local
instance` here, as it is in Mathlib's `Mathlib/Topology/Sober.lean`; the generic point is its top
element, so a non-generic point lies strictly below it and has coheight at least one, while the
dimension hypothesis bounds every coheight by one.

**Two invertibility classes.** Tag 01CS is developed twice in this repository, and the two
predicates are distinct constants bridged by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. The statements here cannot pick one:
`Stacks.SheafOfModules.nonvanishingOpen` is defined only for `Stacks.SheafOfModules.IsInvertible`
and `AlgebraicGeometry.Scheme.Modules.IsAmple` only for
`AlgebraicGeometry.SheafOfModules.IsInvertible`, so the hypothesis of Tag 09NC is spelled with the
first and its conclusion with the second. Both are `Prop`s, so the choice of witness does not
affect what either statement says. The spelling of the first matches
`AlgebraicGeometry.exists_isInvertible_generatingSections_nonvanishingOpen_eq`
  exactly, so its output
feeds the hypothesis with no conversion.

## References

* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 09NB](https://stacks.math.columbia.edu/tag/09NB)
* [Stacks Project, Tag 09NC](https://stacks.math.columbia.edu/tag/09NC)
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AmpleDimensionOne

attribute [local instance] specializationOrder

/-- On an integral scheme the order-theoretic Krull dimension of the specialization order is the
topological Krull dimension. -/
public theorem krullDim_eq_topologicalKrullDim (X : Scheme.{u}) [IsIntegral X] :
    Order.krullDim X = topologicalKrullDim X := by
  rw [topologicalKrullDim]
  exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)).symm

/-- On an integral scheme of topological Krull dimension one every point has coheight at most
one in the specialization order. -/
public theorem coheight_le_one (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (x : X) :
    (Order.coheight x : WithBot ℕ∞) ≤ 1 :=
  calc (Order.coheight x : WithBot ℕ∞) ≤ Order.krullDim X := Order.coheight_le_krullDim x
    _ = 1 := krullDim_eq_topologicalKrullDim X ▸ hdim

/-- On an integral scheme, a point whose closure is everything is the generic point. -/
public theorem eq_genericPoint_of_closure_eq_univ (X : Scheme.{u}) [IsIntegral X] {x : X}
    (hx : closure ({x} : Set X) = Set.univ) : x = genericPoint X :=
  IsGenericPoint.eq hx (genericPoint_spec X)

/-- On an integral scheme the only irreducible component is the whole space. -/
private theorem eq_univ_of_mem_irreducibleComponents (X : Scheme.{u}) [IsIntegral X]
    {C : Set X} (hC : C ∈ irreducibleComponents X) : C = Set.univ := by
  rwa [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hC

/-- **Every non-generic point of a one-dimensional integral scheme is closed.** A nontrivial
specialization into such a point would, together with the whole space above it, give a chain of
three irreducible closed subsets. -/
public theorem isClosed_singleton_of_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) {x : X} (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  refine Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
    (T := closure ({x} : Set X)) hdim.le isClosed_closure ?_ (subset_closure rfl)
  intro C hC hCsub
  obtain rfl := eq_univ_of_mem_irreducibleComponents X hC
  exact hx (eq_genericPoint_of_closure_eq_univ X (Set.univ_subset_iff.mp hCsub))

/-- **The complement of a nonempty open in a Noetherian integral scheme of dimension one is
finite.** It is a closed set not containing the generic point, hence not containing the unique
irreducible component. -/
public theorem finite_compl_of_ne_bot (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (U : X.Opens) (hU : U ≠ ⊥) :
    ((U : Set X)ᶜ).Finite := by
  obtain ⟨x, hxU⟩ := (Opens.ne_bot_iff_nonempty U).mp hU
  have hgen : genericPoint X ∈ U :=
    (genericPoint_specializes x).mem_open U.2 hxU
  refine Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim.le
    U.2.isClosed_compl ?_
  intro C hC hCsub
  obtain rfl := eq_univ_of_mem_irreducibleComponents X hC
  exact hCsub (Set.mem_univ (genericPoint X)) hgen

/-- **The local ring at a non-generic point of a one-dimensional integral scheme has Krull
dimension one.** Its coheight in the specialization order is at least one because it is strictly
below the generic point, and at most one by the dimension hypothesis. -/
public theorem ringKrullDim_stalk_eq_one_of_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) {x : X} (hx : x ≠ genericPoint X) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  have hlow : (1 : ℕ∞) ≤ Order.coheight x := by
    simpa [show genericPoint X = (⊤ : X) from rfl, Order.coheight_top] using
      Order.coheight_add_one_le (lt_of_le_of_ne le_top hx)
  exact le_antisymm (coheight_le_one X hdim x) (by exact_mod_cast hlow)

/-- **Stacks Project, Tag 09ND**, reduced to Tag 09NC. A one-dimensional Noetherian integral
separated scheme has an ample invertible sheaf, given Tag 09NC as the hypothesis `h09NC`. -/
public theorem exists_ample_invertible_of_09NC
    (h09NC : ∀ (Y : Scheme.{u}), CompactSpace Y →
      (∀ y : Y, ∃ (M : Y.Modules)
        (hM : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.sheaf.obj
          (structureSheaf Y.toRingedSpace.sheaf).property M),
        Nonempty M.GeneratingSections ∧
          ∃ t : M.sections,
            y ∈ @Stacks.SheafOfModules.nonvanishingOpen
                Y.toLocallyRingedSpace.toRingedSpace _ M hM t ∧
              IsAffineOpen (@Stacks.SheafOfModules.nonvanishingOpen
                Y.toLocallyRingedSpace.toRingedSpace _ M hM t)) →
      ∃ (M : Y.Modules)
        (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
          (structureSheafRing Y.toRingedSpace).property
            M),
        @AlgebraicGeometry.Scheme.Modules.IsAmple Y M hM)
    (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X] [X.IsSeparated]
    (hdim : topologicalKrullDim X = 1) :
    ∃ (L : X.Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
          L),
      @AlgebraicGeometry.Scheme.Modules.IsAmple X L hL := by
  refine h09NC X inferInstance (fun x => ?_)
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (show x ∈ (⊤ : X.Opens) from trivial)
  have hUne : U ≠ ⊥ := (Opens.ne_bot_iff_nonempty U).mpr ⟨x, hxU⟩
  have hgen : genericPoint X ∈ U :=
    (genericPoint_specializes x).mem_open U.2 hxU
  obtain ⟨L, hL, s, hgenerated, hnonvanishing⟩ :=
    AlgebraicGeometry.exists_isInvertible_generatingSections_nonvanishingOpen_eq X U hU hUne
      (finite_compl_of_ne_bot X hdim U hUne) (fun y _ => inferInstance)
      (fun y hy => ringKrullDim_stalk_eq_one_of_ne_genericPoint X hdim
        (fun heq => hy (heq ▸ hgen)))
  exact ⟨L, hL, hgenerated, s, hnonvanishing ▸ hxU, hnonvanishing ▸ hU⟩

end Stacks.AlgebraicGeometry.AmpleDimensionOne

end
