module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomReflectorExists
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaShift

/-!
# The differential graded Yoneda functor is exact, and 09LK with no exactness hypothesis

Let `C` be a differential graded category over a commutative ring `R` satisfying axioms (A),
(B) and (C), that is, carrying a `DGCategory.ConeSituation`, and suppose that its shift is
strict on representables in the sense of
`DGCategory.ShiftAxiomB.IsStrictRepresentable`. Then Tag 0FQF applies to the differential
graded Yoneda functor `X ↦ h_X`, so the induced functor

`K(h) : K(C) ⥤ K(Mod^dg(C))`

is an exact functor of triangulated categories. Feeding this to
`DGCategory.exists_isTriangulated_derivedHomReflector` removes the last hypothesis that steps 1
to 3 of [Stacks, Tag 09LK] were assembled under: the source functor `Φ` is no longer abstract
and exact by assumption, it is `K(h)`.

## Main results

* `DGCategory.isTriangulated_yonedaOnK`: `K(h)` is exact.
* `DGCategory.exists_isTriangulated_derivedHomReflector_yoneda`: steps 1 and 2 of
  [Stacks, Tag 09LK] with `Φ = K(h)`, and so with no exactness hypothesis left.

## Implementation notes

The triangulated structure on `K(C)` is the one attached to the strictification
`DGCategory.ConeSituation.strictify` of the given cone situation, which changes neither the
differential graded shifts nor the cones nor the distinguished triangles, only the coherence
isomorphisms of the translation of `K(C)`; this is what Tag 0FQF in the form
`DGCategory.DGFunctor.CommShiftB.isTriangulated` asks for on the source side. On the target
side nothing has to be strictified: the translation that axiom (B) for `Mod^dg(C)` puts on
`K(Mod^dg(C))` is already strict, by
`DGCategory.isStrictKShift_rightModuleShiftAxiomB`, and the structures used are the registered
instances of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Triangulated`.

Nothing is asked of the Yoneda functor about cones. Tag 0FQF carries a distinguished triangle
to a distinguished triangle by transporting the *admissible short exact sequence* it comes
from, and a functor of differential graded categories transports one of those automatically,
its defining identities being equations between composites. The compatibility `h_{c(f)} =
c(h_f)` is therefore never needed.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace DGCategory

universe v₂ u₂ v₁ u₁ v u r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- Strictifying axiom (B) changes neither its shift functors nor its identifications, so it
preserves strictness on representables. -/
theorem ShiftAxiomB.IsStrictRepresentable.strictify {S : ShiftAxiomB C}
    (hS : S.IsStrictRepresentable) : S.strictify.IsStrictRepresentable where
  toShift_heq := hS.toShift_heq
  yonedaRightModule_shift := hS.yonedaRightModule_shift

/-- The commutation of the differential graded Yoneda functor with the shift, together with the
two coherences of the comparison isomorphisms with the `ℤ`-action data of the translations; the
latter are supplied by the strictness of those translations. -/
theorem commShiftK_yonedaDGFunctor (CC : ConeSituation C)
    (hS : CC.shift.IsStrictRepresentable) :
    (yonedaDGFunctor C).CommShiftK CC.strictify.shift (rightModuleShiftAxiomB.{v} C) :=
  DGFunctor.CommShiftK.ofCommShiftB (commShiftB_yonedaDGFunctor hS.strictify)
    CC.isStrictKShift_strictify (isStrictKShift_rightModuleShiftAxiomB.{v} C)

/-- **The differential graded Yoneda functor is exact.** If `C` satisfies axioms (A), (B) and
(C) and its shift is strict on representables, then the functor `K(C) ⥤ K(Mod^dg(C))` induced
by `X ↦ h_X` on homotopy categories is an exact functor of triangulated categories.

This is Tag 0FQF; its hypothesis `F(x⟦1⟧) = F(x)⟦1⟧` is
`DGCategory.commShiftB_yonedaDGFunctor`, and the strictness of the translation of
`K(Mod^dg(C))` is `DGCategory.isStrictKShift_rightModuleShiftAxiomB`. -/
theorem isTriangulated_yonedaOnK (CC : ConeSituation C)
    (hS : CC.shift.IsStrictRepresentable) :
    letI : Preadditive C.K := homotopyPreadditive C
    letI : HasZeroObject C.K := homotopyHasZeroObject C CC.strictify
    letI : HasShift C.K ℤ := CC.strictify.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor C.K n).Additive := fun n =>
      homotopyShiftAdditive C CC.strictify n
    letI : Pretriangulated C.K := homotopyPretriangulated C CC.strictify
    letI : (yonedaDGFunctor C).onK.CommShift ℤ :=
      (commShiftK_yonedaDGFunctor CC hS).commShift
    (yonedaDGFunctor C).onK.IsTriangulated :=
  (commShiftK_yonedaDGFunctor CC hS).isTriangulated CC.strictify
    (rightModuleConeSituation.{v} C)

/-- **Steps 1 and 2 of [Stacks, Tag 09LK] for the differential graded Yoneda functor.** Let `C`
be a differential graded category whose objects and whose morphism modules live in one
universe, satisfying axioms (A), (B) and (C) and with its shift strict on representables, let
`K` be an object of `C` and let `G` be a family of objects of `C`. Let `Z` be a triangulated
subcategory of `K(C)` and `q : K(C) ⥤ D(A)` a localization at the morphisms whose cone lies in
`Z`, and suppose that `h_X` lies in the localizing subcategory generated by the `h_{G i}`
whenever `X` lies in `Z`. Then there are an exact reflector `L` with unit `η`, an exact functor

`R̃ : D(A) ⥤ D(E)`

with values in the derived category of right differential graded modules over the
endomorphism complex `E = C(K, K)`, and a natural transformation
`K(h) ⋙ ev_K ⋙ Q_E ⟶ q ⋙ R̃`; and the restriction of `R̃` along `q` is the reflected
evaluation.

This is `DGCategory.exists_isTriangulated_derivedHomReflector` with its exactness hypothesis on
the source functor discharged: the source functor is `K(h)`, which
`DGCategory.isTriangulated_yonedaOnK` makes exact. -/
theorem exists_isTriangulated_derivedHomReflector_yoneda (C : DGCategory.{v, v} R) (K : C.Obj)
    {ι : Type v} (G : ι → C.Obj) (CC : ConeSituation C)
    (hS : CC.shift.IsStrictRepresentable) :
    letI : Preadditive C.K := homotopyPreadditive C
    letI : HasZeroObject C.K := homotopyHasZeroObject C CC.strictify
    letI : HasShift C.K ℤ := CC.strictify.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor C.K n).Additive := fun n =>
      homotopyShiftAdditive C CC.strictify n
    letI : Pretriangulated C.K := homotopyPretriangulated C CC.strictify
    letI : IsTriangulated C.K := homotopyCategory_isTriangulated C CC.strictify
    letI : (yonedaDGFunctor C).onK.CommShift ℤ :=
      (commShiftK_yonedaDGFunctor CC hS).commShift
    letI : (yonedaDGFunctor C).onK.IsTriangulated := isTriangulated_yonedaOnK CC hS
    ∀ (Z : ObjectProperty C.K) [Z.IsTriangulated] {DA : Type u₂} [Category.{v₂} DA]
      [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA]
      [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA] (q : C.K ⥤ DA)
      [q.IsLocalization Z.trW] [q.CommShift ℤ] [q.IsTriangulated],
      (∀ X, Z X → RightModule.yonedaLocalizing C G (((yonedaDGFunctor C).onK).obj X)) →
      ∃ (L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K)
        (_ : L.CommShift ℤ) (_ : L.IsTriangulated) (_ : 𝟭 _ ⟶ L)
        (Rt : DA ⥤ RightModule.derivedCategory (endDGCategory C K))
        (_ : Rt.CommShift ℤ) (_ : Rt.IsTriangulated)
        (_ : (yonedaDGFunctor C).onK ⋙ evaluationOnK.{v} C K ⋙
          RightModule.derivedQ (endDGCategory C K) ⟶ q ⋙ Rt),
        Nonempty (q ⋙ Rt ≅ (yonedaDGFunctor C).onK ⋙ L ⋙ evaluationOnK.{v} C K ⋙
          RightModule.derivedQ (endDGCategory C K)) := by
  let : Preadditive C.K := homotopyPreadditive C
  let : HasZeroObject C.K := homotopyHasZeroObject C CC.strictify
  let : HasShift C.K ℤ := CC.strictify.shift.kShift
  let : ∀ n : ℤ, (shiftFunctor C.K n).Additive := fun n =>
    homotopyShiftAdditive C CC.strictify n
  let : Pretriangulated C.K := homotopyPretriangulated C CC.strictify
  let : IsTriangulated C.K := homotopyCategory_isTriangulated C CC.strictify
  let : (yonedaDGFunctor C).onK.CommShift ℤ := (commShiftK_yonedaDGFunctor CC hS).commShift
  let : (yonedaDGFunctor C).onK.IsTriangulated := isTriangulated_yonedaOnK CC hS
  intro Z _ DA _ _ _ _ _ _ q _ _ _ hZ
  exact exists_isTriangulated_derivedHomReflector C K G ((yonedaDGFunctor C).onK) Z q hZ

end DGCategory

end
