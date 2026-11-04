module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedExtOnAnOpen

/-!
# An upper bound on the derived internal Hom from local vanishing of `Ext`

Let `(X, 𝒪_X)` be a ringed space and `K`, `L` objects of `D(𝒪_X)`. If on a family of opens
which is a basis near every point of `X` there are no degree-`n` morphisms `K|_U ⟶ L|_U` for
`n > c`, then `R𝓗om(K, L)` lies in `D^{≤ c}(𝒪_X)`. Indeed `R𝓗om(K, L)` is the class of an
internal Hom complex whose complex of sections over `U` has degree-`n` cohomology
`Ext^n(K|_U, L|_U)` ([Stacks, Tag 08DK] in every degree), and exactness of a complex of sheaves
is local.

## Main results

* `Stacks.SheafOfModules.isLE_of_locally_exactAt_sections`: a complex of sheaves of modules has no
  cohomology above `c` once its complexes of sections are exact above `c` on a basis.
* `Stacks.SheafOfModules.isLE_derivedSheafHom_of_locally_subsingleton`: the bound on
  `R𝓗om(K, L)`.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- A complex of sheaves of modules has no cohomology above `c` as soon as its complexes of
sections are exact above `c` on a family of opens which is a basis near every point. -/
theorem isLE_of_locally_exactAt_sections
    {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} O) ℤ) (c : ℤ)
    (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hK : ∀ U, P U → ∀ n, c < n →
      ((((_root_.SheafOfModules.evaluation O (op U)) ⋙
        forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).ExactAt n) :
    K.IsLE c := by
  rw [CochainComplex.isLE_iff]
  exact fun n hn => moduleExact_of_locally_surjective_sections (K.sc n) P hP
    fun U hU => (ShortComplex.ab_exact_iff _).mp (hK U hU n hn)

attribute [local instance] HasDerivedCategory.standard
  LocalCokernel.overFunctor_preservesFiniteLimits LocalCokernel.overFunctor_preservesFiniteColimits

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The derived internal Hom is bounded above by a local bound.** If on a family of opens which
is a basis near every point there is no degree-`n` morphism `K|_U ⟶ L|_U` in the derived category
of the slice site, for every `n > c`, then `R𝓗om(K, L)` lies in `D^{≤ c}`. -/
theorem isLE_derivedSheafHom_of_locally_subsingleton
    (K L : DerivedCategory (StructureSheafModules Rc)) (c : ℤ) (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (h : ∀ U, P U → ∀ n, c < n → Subsingleton (ShiftedHom
      ((_root_.SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory.obj K)
      ((_root_.SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).mapDerivedCategory.obj L)
      n)) :
    (((derivedSheafHom Rc).obj (op K)).obj L).IsLE c := by
  have hC : (homSheafComplex Rc K L).IsLE c := by
    refine isLE_of_locally_exactAt_sections _ c P hP fun U hU n hn => ?_
    refine ((sectionComplex Rc (homSheafComplex Rc K L) U).exactAt_iff_isZero_homology n).mpr ?_
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr
      ((Equiv.subsingleton_congr (homSheafComplexSectionHomologyEquiv Rc K L U n).toEquiv).mpr
        (h U hU n hn))
  have hQ : (homSheafObject Rc K L).IsLE c := (DerivedCategory.isLE_Q_obj_iff _ c).mpr hC
  exact DerivedCategory.TStructure.t.isLE_of_iso (homSheafObjectIso Rc K L).symm c

end Stacks.SheafOfModules

end
