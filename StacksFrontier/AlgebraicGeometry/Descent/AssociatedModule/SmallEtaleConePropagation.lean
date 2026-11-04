module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentForward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.ConePropagationAlongAnExactFunctor

/-!
# The standing hypothesis of the induction travels to the cone along `ε^*`

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the comparison of Stacks 08H7.
The induction of Stacks 08HE (2) ⇒ (1),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep`, carries a predicate `P` on
objects of `D(𝒪_S)` from `E` to the third vertex of the triangle its step produces; in that
application `P E` is the conjunction of clause (2) of Stacks 08HE, "`ε^*E` is
`m`-pseudo-coherent", and quasi-coherence of the cohomology sheaves of `E`.  This module
discharges the **first** conjunct on the cone, which is item 4 of the measurement in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentObligation`.

It is the general statements of
`StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.ConePropagationAlongAnExactFunctor`
read at `ε`.  Nothing mathematical happens here: what the specialization has to supply is the
unit comparison of `ε^*`, and the three functor-level typeclass hypotheses of the general
statements explicitly, instance search not crossing between the spelling of the structure sheaves
`ε^*` was built with and the spelling
`AlgebraicGeometry.RingedSite.ringSheaf` of the two ringed sites.

## Main results

* `AlgebraicGeometry.SmallEtale.pullbackUnitIso` and
  `AlgebraicGeometry.SmallEtale.associatedModuleRingSheafUnitIso`: `ε^*𝒪_S ≅ 𝒪`, and the same at
  the `AlgebraicGeometry.RingedSite.ringSheaf` spelling.
* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFromSmallEtale_obj₃_of_distinguished`: clause (2)
  of Stacks 08HE propagates along a distinguished triangle of `D(𝒪_S)` by Stacks 08FV part (1).
* `AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale`: **the triangle datum
  of the induction step with clause (2) carried to its third vertex.**

## Implementation notes

The unit comparison is Mathlib's: the associated-module functor of Stacks 03DU (4) is the
pullback of sheaves of modules along `AlgebraicGeometry.SmallEtale.structureMap`, whose
`SheafOfModules.pullbackObjUnitToUnit` is an isomorphism because the underlying functor of sites
is final.  This is the same comparison the forward implication uses at the slices, there as
`asIso (SheafOfModules.pullbackObjUnitToUnit (sliceStructureMap B S hS V))`, taken here at the
whole site; Stacks 08H3 `AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules` is
not used, since it asks its morphism to be a `AlgebraicGeometry.RingedToposHom` and `ε^*` appears
here as a bare functor.

What is **not** proved here, and is the other half of `P`: that the cohomology sheaves of the cone
are quasi-coherent.  That is a statement about `D(𝒪_S)` alone, with no `ε` in it, and nothing in
this module bears on it.

## References

* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`ε^*𝒪_S ≅ 𝒪`.**  The pullback of the unit `𝒪_S`-module along `ε` is the unit module of the
small étale site.  This is `SheafOfModules.pullbackObjUnitToUnit` of
`AlgebraicGeometry.SmallEtale.structureMap`, which is an isomorphism because the underlying
functor of sites is final. -/
public def pullbackUnitIso :
    (SheafOfModules.pullback.{u} (structureMap B S hS)).obj
        (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit (structureSheaf B S hS) :=
  asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS))

/-- `AlgebraicGeometry.SmallEtale.pullbackUnitIso` at the spelling
`AlgebraicGeometry.RingedSite.ringSheaf` of the two structure sheaves, which is the spelling the
general statements are stated at.  The retyping is a definitional one; it is written out because
`AlgebraicGeometry.SmallEtale.associatedModule` and
`AlgebraicGeometry.RingedSite.ringSheaf` are `def`s, so instance search for the `IsIso` of
`SheafOfModules.pullbackObjUnitToUnit` does not see through them. -/
public def associatedModuleRingSheafUnitIso :
    (associatedModuleOfSheaf B S hS).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) :=
  pullbackUnitIso B S hS

variable [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **Clause (2) of Stacks 08HE propagates along a distinguished triangle.**  Let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle of `D(𝒪_S)`.  If `ε^*K` is
`(m + 1)`-pseudo-coherent and `ε^*L` is `m`-pseudo-coherent, then `ε^*M` is `m`-pseudo-coherent.

`ε^*` is exact, so it acts on the derived categories as a triangulated functor and carries the
triangle to a distinguished triangle of `D(𝒪)`; Stacks 08FV part (1) finishes.  This is
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished` at
`ε`. -/
public theorem isPseudoCoherentFromSmallEtale_obj₃_of_distinguished (m : ℤ)
    (T : Triangle (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))))
    (h₁ : IsPseudoCoherentFromSmallEtale B S hS T.obj₁ (m + 1))
    (h₂ : IsPseudoCoherentFromSmallEtale B S hS T.obj₂ m) :
    IsPseudoCoherentFromSmallEtale B S hS T.obj₃ m :=
  RingedSite.isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished_of_hypotheses
    (X := smallEtaleRingedSite B S hS) (Y := S.zariskiRingedSite)
    (associatedModuleOfSheaf B S hS)
    (additive_associatedModuleOfSheaf B S hS)
    (preservesFiniteLimits_associatedModuleOfSheaf B S hS)
    (preservesFiniteColimits_associatedModuleOfSheaf B S hS)
    m T hT h₁ h₂

/-- **The triangle datum of the induction step of Stacks 08HE (2) ⇒ (1), with clause (2) carried
to the third vertex.**

For `E` in `D^{≤n}(𝒪_S)` with `ε^*E` `m`-pseudo-coherent, an epimorphism
`φ : 𝒪_S^{⊕t} ⟶ Hⁿ(E)` with `t` finite, and a lift `f` of
`DerivedCategory.singleMapTruncGEZeroShift E n φ` along `E⟦n⟧ ⟶ τ^{≥0}(E⟦n⟧)`, there is a
distinguished triangle of `D(𝒪_S)` whose second vertex is `E`, whose first vertex is
`m`-pseudo-coherent, whose third vertex has no cohomology in any degree `≥ n`, **and whose third
vertex has `m`-pseudo-coherent pullback along `ε`**.

That is everything `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks of its
step, except the quasi-coherence conjunct of `P` on the third vertex, which is not a statement
about `ε` and is not addressed here. -/
public theorem exists_distTriang_free_of_lift_smallEtale (m n : ℤ)
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    [DerivedCategory.IsLE E n] (ι : Type u) [Finite ι]
    (φ : SheafOfModules.free
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ι ⟶
      (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) n).obj E)
    (hφ : Epi φ)
    (f : (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) 0).obj
        (SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ι) ⟶ E⟦n⟧)
    (hf : f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app (E⟦n⟧) =
      DerivedCategory.singleMapTruncGEZeroShift E n φ)
    (hE : IsPseudoCoherentFromSmallEtale B S hS E m) :
    ∃ T : Triangle (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))),
      T ∈ distTriang (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) ∧
        Nonempty (T.obj₂ ≅ E) ∧ S.zariskiRingedSite.IsPseudoCoherentFrom T.obj₁ m ∧
          IsPseudoCoherentFromSmallEtale B S hS T.obj₃ m ∧
            ∀ j : ℤ, n ≤ j →
              IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
                  T.obj₃) :=
  RingedSite.exists_distTriang_free_of_lift_mapDerivedCategory_of_hypotheses
    (X := smallEtaleRingedSite B S hS) (Y := S.zariskiRingedSite)
    (associatedModuleOfSheaf B S hS)
    (additive_associatedModuleOfSheaf B S hS)
    (preservesFiniteLimits_associatedModuleOfSheaf B S hS)
    (preservesFiniteColimits_associatedModuleOfSheaf B S hS)
    (associatedModuleRingSheafUnitIso B S hS) m n E ι φ hφ f hf hE

end AlgebraicGeometry.SmallEtale

end
