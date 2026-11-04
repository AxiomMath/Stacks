module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleConePropagation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentConePropagation

/-!
# Both conjuncts of the induction's standing hypothesis on one cone

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the comparison of Stacks 08H7.
The recursion `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` carries a
predicate `P` on objects of `D(𝒪_S)` from `E` to the third vertex of the triangle its step
produces; in the application of Stacks 0DII,
`P E` is "`ε^*E` is `m`-pseudo-coherent **and** the cohomology sheaves of `E` are quasi-coherent".

The two conjuncts are propagated separately, by
`AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale` and by
`AlgebraicGeometry.exists_distTriang_free_of_lift_isQuasicoherent`.  Each of those **binds its
triangle existentially**, so neither conclusion can be read on the triangle of the other and their
conjunction is not a consequence of the two: the recursion needs one triangle carrying both.  This
module states that triangle.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale_quasicoherent`:
  **the triangle datum of the induction step with the whole of `P` carried to its third vertex.**

## Implementation notes

The triangle is *not* rebuilt a third time.  `exists_distTriang_free_of_lift_isQuasicoherent`
exports the identity of its first vertex — `Nonempty (T.obj₁ ≅ 𝒪_S^{⊕t}[n])` — precisely so that
further standing hypotheses can be read on the triangle it produces; the `ε` conjunct is then
`AlgebraicGeometry.SmallEtale.isPseudoCoherentFromSmallEtale_obj₃_of_distinguished`, which is
stated at an explicit triangle, with its two inputs transported along that isomorphism and along
`Nonempty (T.obj₂ ≅ E)` by `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_iso`.

For the first vertex the `ε`-clause is read off **clause (1) ⇒ (2) of Stacks 08HE** itself,
`AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`, which is proved
unconditionally in this development: `𝒪_S^{⊕t}[n]` is `m'`-pseudo-coherent on the Zariski site for
every `m'`, so its pullback along `ε` is too.  There is no circularity — the implication being
proved here is (2) ⇒ (1).  This is shorter than the direct route, which would be
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_shift_singleFunctor_obj_free`
and whose three functor-level typeclass hypotheses cannot be synthesized at `ε` — the obstruction
recorded at `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`,
which that statement has no `_of_hypotheses` form for.

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
variable [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **The triangle datum of the induction step of Stacks 08HE (2) ⇒ (1), with both conjuncts of
the standing hypothesis carried to the third vertex.**

For `E` in `D^{≤n}(𝒪_S)` with `ε^*E` `m`-pseudo-coherent and with quasi-coherent cohomology
sheaves, an epimorphism `φ : 𝒪_S^{⊕t} ⟶ Hⁿ(E)` with `t` finite, and a lift `f` of
`DerivedCategory.singleMapTruncGEZeroShift E n φ` along `E⟦n⟧ ⟶ τ^{≥0}(E⟦n⟧)`, there is a
distinguished triangle of `D(𝒪_S)` whose second vertex is `E`, whose first vertex is
`m`-pseudo-coherent, whose third vertex has no cohomology in any degree `≥ n`, **and whose third
vertex has `m`-pseudo-coherent pullback along `ε` and quasi-coherent cohomology sheaves**.

That is the whole of what `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks
of its step, for the predicate `P` of Stacks 0DII. -/
public theorem exists_distTriang_free_of_lift_smallEtale_quasicoherent (m n : ℤ)
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    [DerivedCategory.IsLE E n] (ι : Type u) [Finite ι]
    (φ : SheafOfModules.free
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ι ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
        n).obj E)
    (hφ : Epi φ)
    (f : (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) 0).obj
        (SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ι) ⟶ E⟦n⟧)
    (hf : f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app (E⟦n⟧) =
      DerivedCategory.singleMapTruncGEZeroShift E n φ)
    (hE : IsPseudoCoherentFromSmallEtale B S hS E m)
    (hEq : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) j).obj
        E).IsQuasicoherent) :
    ∃ T : Triangle (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))),
      T ∈ distTriang (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) ∧
        Nonempty (T.obj₂ ≅ E) ∧ S.zariskiRingedSite.IsPseudoCoherentFrom T.obj₁ m ∧
          IsPseudoCoherentFromSmallEtale B S hS T.obj₃ m ∧
            (∀ j : ℤ, ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
                j).obj T.obj₃).IsQuasicoherent) ∧
              ∀ j : ℤ, n ≤ j →
                IsZero ((DerivedCategory.homologyFunctor
                  (SheafOfModules.{u}
                    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
                  j).obj T.obj₃) := by
  obtain ⟨T, hT, ⟨e₂⟩, hone, ⟨e₁⟩, hqcoh, hzero⟩ :=
    exists_distTriang_free_of_lift_isQuasicoherent S m n E ι φ hφ f hf hEq
  refine ⟨T, hT, ⟨e₂⟩, hone, ?_, hqcoh, hzero⟩
  refine isPseudoCoherentFromSmallEtale_obj₃_of_distinguished B S hS m T hT ?_ ?_
  · exact pseudoCoherentToAssociatedModule_of_slice_exact B S hS T.obj₁ (m + 1)
      (RingedSite.isPseudoCoherentFrom_of_iso S.zariskiRingedSite (m + 1)
        (S.zariskiRingedSite.isPseudoCoherentFrom_singleFunctor_obj_free n (m + 1) ι) e₁)
  · exact RingedSite.isPseudoCoherentFrom_of_iso (smallEtaleRingedSite B S hS) m hE
      ((@Functor.mapDerivedCategory.{d, d'}
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
        _ _ inferInstance (SheafOfModules.{u} (structureSheaf B S hS)) _ _ inferInstance
        (associatedModuleOfSheaf B S hS)
        (inferInstance : (associatedModuleOfSheaf B S hS).Additive)
        (inferInstance : PreservesFiniteLimits (associatedModuleOfSheaf B S hS))
        (inferInstance : PreservesFiniteColimits (associatedModuleOfSheaf B S hS))).mapIso e₂)

end AlgebraicGeometry.SmallEtale

end
