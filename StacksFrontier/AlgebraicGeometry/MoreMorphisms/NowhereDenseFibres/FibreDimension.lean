module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# Local dimension of a fibre at a generic point

For a scheme of finite type over a field the local dimension at a generic point of an
irreducible component is the dimension of that component, and a closed immersion which
matches up generic points preserves it. For a flat morphism locally of finite presentation
the local dimension of a fibre at a generic point of one of its irreducible components is
finite.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_closure_of_mem_genericPoints` identifies the
  local dimension at a generic point with the dimension of its component.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_of_isClosedImmersion_genericPoints` compares
  local dimensions across a closed immersion of schemes of finite type over a field.
* `AlgebraicGeometry.exists_nat_topologicalKrullDimAt_fiber_of_mem_genericPoints` gives
  finiteness of the local fibre dimension at a generic point.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For a scheme of finite type over a field, the local dimension at a generic point of an
irreducible component is the dimension of that component. -/
theorem topologicalKrullDimAt_eq_closure_of_mem_genericPoints {X : Scheme.{u}} (k : Type u)
    [Field k] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (x : X)
    (hx : x ∈ genericPoints X) :
    topologicalKrullDimAt X x = topologicalKrullDim (closure ({x} : Set X)) := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X q x]
  refine le_antisymm (iSup₂_le fun C hC => ?_) (le_iSup_of_le (closure ({x} : Set X))
    (le_iSup_of_le ⟨hx, subset_closure (Set.mem_singleton x)⟩ le_rfl))
  obtain ⟨hC, hxC⟩ := hC
  have hsub : closure ({x} : Set X) ⊆ C :=
    (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hxC)
  rw [Set.Subset.antisymm (hx.2 hC.1 hsub) hsub]

/-- A closed immersion of schemes of finite type over a field preserves the local dimension
at a point which is generic in an irreducible component of both source and target. -/
theorem topologicalKrullDimAt_eq_of_isClosedImmersion_genericPoints {A B : Scheme.{u}}
    (j : A ⟶ B) [IsClosedImmersion j] (k : Type u) [Field k] (qA : A ⟶ Spec (.of k))
    (qB : B ⟶ Spec (.of k)) [LocallyOfFiniteType qA] [LocallyOfFiniteType qB] {a : A}
    (ha : a ∈ genericPoints A) (hb : j a ∈ genericPoints B) :
    topologicalKrullDimAt A a = topologicalKrullDimAt B (j a) := by
  have hclosure : j '' closure ({a} : Set A) = closure ({j a} : Set B) := by
    simpa only [Set.image_singleton] using
      (j.isClosedEmbedding.closure_image_eq ({a} : Set A)).symm
  rw [topologicalKrullDimAt_eq_closure_of_mem_genericPoints k qA a ha,
    topologicalKrullDimAt_eq_closure_of_mem_genericPoints k qB (j a) hb, ← hclosure]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (j.isEmbedding.homeomorphImage (closure ({a} : Set A))).isHomeomorph

/-- For a flat morphism locally of finite presentation, the local dimension of a fibre at a
generic point of one of its irreducible components is a natural number. -/
theorem exists_nat_topologicalKrullDimAt_fiber_of_mem_genericPoints {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] {x : X}
    (hx : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    ∃ d : ℕ, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨U, hdense, hrel⟩ := exists_open_relativeDimension_fiberwise_dense f
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd f
      (S.fromSpecResidueField (f x)))
    infer_instance
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have hopen : IsOpen ((f.fiberι (f x)) ⁻¹' (((iSup U : X.Opens) : Set X))) :=
    (iSup U).2.preimage (f.fiberι (f x)).continuous
  have hxUnion : x ∈ (((iSup U : X.Opens) : Set X)) := by
    simpa only [Set.mem_preimage, f.fiberι_asFiber] using
      scheme_genericPoints_mem_dense_open (f.fiber (f x)) hopen (hdense (f x)) hx
  obtain ⟨d, hxd⟩ : ∃ d, x ∈ U d := Opens.mem_iSup.mp hxUnion
  exact ⟨d, topologicalKrullDimAt_fiber_eq_of_relativeDimension f (U d) d (hrel d) x hxd⟩

end AlgebraicGeometry

end
