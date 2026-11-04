module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactZariskiLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType

/-!
# Quasi-compactness of isomorphism spaces through a surjection

Two formal facts used to bound the isomorphism spaces of one stack by those of another.

* A morphism of algebraic spaces `b : B' ⟶ G` is quasi-compact as soon as `r ≫ b` is for a
  morphism `r : A ⟶ B'` which is surjective on the sections over every object of the site: every
  base change of `b` along a morphism from a quasi-compact algebraic space is the image, on points,
  of the corresponding base change of `r ≫ b` (Stacks 03MH, 040W).
* For a fibred 1-morphism `F` of fibred categories, the map of morphism presheaves
  `Mor(a, b) ⟶ Mor(F a, F b)` of Stacks 042V is surjective on the sections over `V ⟶ U` as soon
  as `F` is surjective on the morphisms between the chosen pullbacks of `a` and `b` to `V`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_surjective_app_comp`: the first fact.
* `AlgebraicGeometry.Stack.surjective_liftedMorPresheafMap_app`: the second.

## References

* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Quasi-compactness descends along a sectionwise surjection.** Let `r : A ⟶ B'` and
`b : B' ⟶ G` be morphisms of algebraic spaces over `S` with `r` surjective on the sections over
every object of the site. If `r ≫ b` is quasi-compact, so is `b`: a base change of `b` along a
morphism from a quasi-compact algebraic space receives the corresponding base change of `r ≫ b`,
which is quasi-compact, by a base change of `r`, which is surjective on points (Stacks 03MH), and
an algebraic space covered on points by a quasi-compact one is quasi-compact (Stacks 040W). -/
theorem isQuasiCompact_of_surjective_app_comp {A B' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hB : IsAlgebraicSpace B S hS B')
    (hG : IsAlgebraicSpace B S hS G) (r : A ⟶ B') (b : B' ⟶ G)
    (hr : ∀ T, Function.Surjective (r.app T)) (h : IsQuasiCompact B S hS (r ≫ b)) :
    IsQuasiCompact B S hS b := by
  intro Z hZ hZqc g
  let k : pullback g (r ≫ b) ⟶ pullback g b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by simp [pullback.condition])
  have hsq : IsPullback (pullback.snd g (r ≫ b)) k r (pullback.snd g b) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst g b) (v₂₂ := b) (h₃₁ := g) ?_ ?_
      (IsPullback.of_hasPullback g b).flip
    · rw [show k ≫ pullback.fst g b = pullback.fst g (r ≫ b) from pullback.lift_fst _ _ _]
      exact (IsPullback.of_hasPullback g (r ≫ b)).flip
    · exact (pullback.lift_snd _ _ _).symm
  have hsurj : Function.Surjective (pointsMap B S hS _ k) :=
    surjective_pointsMap_of_isPullback B S hS hsq
      (surjective_pointsMap_of_surjective_app B S hS r hr)
  exact isQuasiCompactSpace_of_finite_jointly_surjective' B S hS
    (isAlgebraicSpace_pullback B S hS g b hZ hB hG) (J := Unit)
    (fun _ => isAlgebraicSpace_pullback B S hS g (r ≫ b) hZ hA hG) (fun _ => k)
    (fun _ => h Z hZ hZqc g) fun w => ⟨(), hsurj w⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u₁ u₂ u₃ vb v v'

variable {𝒞 : Type u₁} [Category.{vb} 𝒞]
  {𝒳 : Type u₂} [Category.{v} 𝒳] {𝒮 : Type u₃} [Category.{max v v'} 𝒮]
  {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} [p.IsFibered] [r.IsFibered]

/-- **The map of morphism presheaves of a 1-morphism is surjective where the 1-morphism is full.**
Let `F` be a fibred 1-morphism, `a`, `b` objects of the fibre over `U` and `g : V ⟶ U`. If every
morphism between the images under `F` of the chosen pullbacks of `a` and `b` along `g` is the
image of a morphism, the map `Mor(a, b) ⟶ Mor(F a, F b)` of Stacks 042V is surjective on the
sections over `g`. -/
theorem surjective_liftedMorPresheafMap_app (hF : p.IsFibredOneMorphism r F) {U : 𝒞}
    (a b : p.Fiber U) (g : (Over U)ᵒᵖ)
    (hfull : ∀ t : F.obj (Functor.pullbackFiber p a g.unop.hom).1 ⟶
        F.obj (Functor.pullbackFiber p b g.unop.hom).1,
      ∃ m : (Functor.pullbackFiber p a g.unop.hom).1 ⟶ (Functor.pullbackFiber p b g.unop.hom).1,
        F.map m = t) :
    Function.Surjective ((liftedMorPresheafMap.{_, _, _, _, _, v'} hF a b).app g) := by
  intro n
  let t := (hF.mapPullbackFiberIso a g.unop.hom).inv ≫ n ≫
    (hF.mapPullbackFiberIso b g.unop.hom).hom
  obtain ⟨m, hm⟩ := hfull (Functor.Fiber.fiberInclusion.map t)
  have hmv : p.IsHomLift (𝟙 g.unop.left) m :=
    Functor.isHomLift_of_isHomLift_map_of_comp_eq hF.comp_eq _ m (by rw [hm]; exact t.2)
  let m' : Functor.pullbackFiber p a g.unop.hom ⟶ Functor.pullbackFiber p b g.unop.hom :=
    Functor.Fiber.homMk p _ m
  have ht : (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).map m' = t := by
    apply Functor.Fiber.fiberInclusion.map_injective
    rwa [Functor.fiberInclusion_map_fiberFunctorOfCompEq_map]
  have key : (hF.mapPullbackFiberIso a g.unop.hom).hom ≫
      (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).map m' ≫
      (hF.mapPullbackFiberIso b g.unop.hom).inv = n := by
    rw [ht]
    simp [t]
  exact ⟨ULift.up m', key⟩

end AlgebraicGeometry.Stack

end
