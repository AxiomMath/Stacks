module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDiagonalImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorIsomAffine

/-!
# The diagonal of the Picard functor is a quasi-compact immersion (Stacks 0DMF)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` which is flat, proper and of
finite presentation, such that `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every scheme `T`
over `B` (the standing assumptions of Section 0DMD). Then `Pic_{X/B}` is an algebraic space over
`B` (Stacks 0D2C, `AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor`), and Stacks 0DMF
asserts that its diagonal `Pic_{X/B} ⟶ Pic_{X/B} ×_B Pic_{X/B}` is a quasi-compact immersion.

The diagonal is an immersion by Stacks 0D2D
(`AlgebraicGeometry.Space.PicardSituation.isImmersion_picardEqualizer_and_isLocallySeparated`).
It is quasi-compact by
`AlgebraicGeometry.Space.PicardSituation.isQuasiSeparated_of_represents_picardFunctor`: read at a
point of `Pic_{X/B} ×_B Pic_{X/B}` over a scheme `T`, the diagonal is the equalizer of two points
of `Pic_{X/B}(T)`, which fppf locally on `T` are the classes of invertible modules `L`, `N` on
`X_T` (Stacks 0DME), and there the equalizer is covered by `Isom(L, N)`, affine over `T`. This
is the argument of Stacks 0DQL for the gerbe `Picardstack_{X/B} ⟶ Pic_{X/B}`, the
quasi-compactness of the diagonal of the Picard stack (Stacks 0DMA) being read at the point
`(L, N)`, where it is Stacks 08K9 for `X_T ⟶ T`.

## Main results

* `PicardSituation.isImmersion_and_isQuasiCompact_diagonal_of_iso_picardFunctor`: the diagonal
  of `Pic_{X/B}` over `B` is a quasi-compact immersion.

## References

* [Stacks Project, Tag 0DMF](https://stacks.math.columbia.edu/tag/0DMF)
* [Stacks Project, Tag 0D2D](https://stacks.math.columbia.edu/tag/0D2D)
* [Stacks Project, Tag 0DMA](https://stacks.math.columbia.edu/tag/0DMA)
* [Stacks Project, Tag 0DME](https://stacks.math.columbia.edu/tag/0DME)
* [Stacks Project, Tag 0DQL](https://stacks.math.columbia.edu/tag/0DQL)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.PicardSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, proper and of
finite presentation, such that `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every scheme `T`
over `B`, and let `p : H ⟶ B` be an algebraic space over `B` whose functor of points over `B` is
identified (`c`) with the relative Picard functor `Pic_{X/B}` (such an `H` exists by Stacks 0D2C,
`AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor`). Then the diagonal `H ⟶ H ×_B H` of
`Pic_{X/B}` over `B` is a quasi-compact immersion. -/
@[stacks 0DMF]
theorem isImmersion_and_isQuasiCompact_diagonal_of_iso_picardFunctor
    {s : PicardSituation B S hS} (hflat : IsFlat B S hS s.f.hom)
    (hfp : IsFinitePresentation B S hS s.f.hom) (hproper : IsProper B S hS s.f.hom)
    (h : s.StructureSheafMapIso) {H : AlgebraicSpaces B S hS} {p : H ⟶ s.base}
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor) :
    IsImmersion B S hS (pullback.diagonal p.hom) ∧
      IsQuasiCompact B S hS (pullback.diagonal p.hom) := by
  let e : ∀ T : s.SchemesOver, s.picardFunctor.obj (op T) ≃
      {x : H.1.obj (op T.left) //
        p.hom.app (op T.left) x =
          yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)} := fun T =>
    { toFun := fun ξ => (c.inv.app (op T) ξ).down
      invFun := fun x => c.hom.app (op T) (ULift.up x)
      left_inv := fun ξ => (c.app (op T)).inv_hom_id_apply ξ
      right_inv := fun x => by
        have hx := (c.app (op T)).hom_inv_id_apply
          (show (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).obj (op T) from ULift.up x)
        exact congrArg ULift.down hx }
  have he : ∀ (T U : s.SchemesOver) (g : T ⟶ U) (ξ : s.picardFunctor.obj (op U)),
      (e T (s.picardFunctor.map g.op ξ)).val = H.1.map g.left.op (e U ξ).val := by
    intro T U g ξ
    show (c.inv.app (op T) (s.picardFunctor.map g.op ξ)).down.1 = _
    rw [NatTrans.naturality_apply]
    rfl
  exact ⟨(s.isImmersion_picardEqualizer_and_isLocallySeparated hflat hfp hproper h).2 H.1 p.hom e
      he, isQuasiSeparated_of_represents_picardFunctor c hflat hfp hproper⟩

end AlgebraicGeometry.Space.PicardSituation

end
