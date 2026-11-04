module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.CoordinateImmersion
public import StacksFrontier.AlgebraicGeometry.VeryAmpleProjectiveSpace.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Very ampleness is preserved by base change, over an affine base

Let `f : X ⟶ S` be a morphism of schemes, `ℒ` an invertible `𝒪_X`-module which is very ample
relative to `f`, and `g : S' ⟶ S` a morphism of schemes. [Stacks, Tag 0B3F] asserts that the
inverse image of `ℒ` on `X ×_S S'` is very ample relative to the projection `X ×_S S' ⟶ S'`.
It is proved here **when `S` and `S'` are affine and `f` is of finite type**.

## Main results

* `AlgebraicGeometry.hasImmersionTwistOver_baseChange`: an immersion into `ℙⁿ_S` over `S`
  carrying the hyperplane sheaf to `ℳ` base changes to one into `ℙⁿ_{S'}` over `S'` carrying it
  to the inverse image of `ℳ`. No hypothesis on `S`, `S'` or `f`.
* `AlgebraicGeometry.isRelativelyVeryAmple_baseChange`: **[Stacks, Tag 0B3F] for a finite-type
  morphism to an affine base, base changed along a morphism of affine schemes.**
* `AlgebraicGeometry.isRelativelyVeryAmple_baseChange_fst`: the same at the chosen categorical
  pullback.

## Implementation notes

The source's proof of [Stacks, Tag 0B3F] runs through the projective bundle `𝐏(ℰ)` and the
comparison of degree-one twists of [Stacks, Tag 01O3]. Over an affine base the projective bundle
can be left out of the argument altogether: very ampleness is equivalent to an immersion into a
*finite-dimensional projective space* `ℙⁿ_S` ([Stacks, Tag 02NP],
`Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple`, and back
`Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion`), and `ℙⁿ_S` is a fibre
product over the **terminal** scheme. So:

* the base change `i' : X' ⟶ ℙⁿ_{S'}` of the immersion `i : X ⟶ ℙⁿ_S` needs no universal
  property of a projective bundle: it is `Stacks.AmpleProjectiveImmersion.liftOver` of `f'` and
  of the composite `X' ⟶ X ⟶ ℙⁿ_S ⟶ ℙⁿ_ℤ`, and the compatibility a `pullback.lift` has to
  discharge is an equality of two morphisms into a terminal object, so there is nothing to check;
* it is an immersion because the square it forms with `i` over
  `AlgebraicGeometry.projectiveSpaceOverMap n g` is cartesian —
  `AlgebraicGeometry.isPullback_projectiveSpaceOverMap` pasted under the given base-change
  square — and immersions are stable under base change ([Stacks, Tag 01JY]);
* and the hyperplane sheaf is carried across by pure pseudofunctoriality, because
  `𝒪_{ℙⁿ_S}(1)` is *by definition* the integral `𝒪_{ℙⁿ_ℤ}(1)` pulled back along the projection
  to the integral model, and `i'` and `i` have the *same* such projection up to `p`. That is
  `Stacks.AmpleProjectiveImmersion.liftOverTwistIso`.

None of these three steps mentions a graded algebra, so nothing of [Stacks, Tag 01O3] is needed.

## References

* [Stacks Project, Tag 0B3F](https://stacks.math.columbia.edu/tag/0B3F)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01JY](https://stacks.math.columbia.edu/tag/01JY)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X X' S S' : Scheme.{u}} (n : ℕ)

/-- **The base change of an immersion into `ℙⁿ_S` over `S`.** Given a cartesian square with
`p : X' ⟶ X` over `g : S' ⟶ S` and an immersion `i : X ⟶ ℙⁿ_S` over `S`, the morphism
`i' : X' ⟶ ℙⁿ_{S'}` with structure morphism `f'` and the same projection to the integral model as
`p ≫ i` makes the square `(p, i', i, ℙⁿ(g))` cartesian. -/
theorem isPullback_liftOver_baseChange {p : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hbc : IsPullback p f' f g) (i : X ⟶ projectiveSpaceOver.{u} n S)
    (hover : i ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f) :
    IsPullback p
      (Stacks.AmpleProjectiveImmersion.liftOver f'
        (p ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S))
      i (projectiveSpaceOverMap n g) := by
  set i' := Stacks.AmpleProjectiveImmersion.liftOver f'
    (p ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S) with hi'
  have hsq : p ≫ i = i' ≫ projectiveSpaceOverMap n g := by
    refine (pullback.hom_ext ?_ ?_).symm
    · rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc, hi',
        Stacks.AmpleProjectiveImmersion.liftOver_fst, Category.assoc, hover]
      exact hbc.w.symm
    · rw [Category.assoc]
      show i' ≫ projectiveSpaceOverMap n g ≫
        projectiveSpaceOver.toIntegralAtUniverse n S = _
      rw [projectiveSpaceOverMap_snd, hi',
        Stacks.AmpleProjectiveImmersion.liftOver_snd, Category.assoc]
  refine IsPullback.of_bot ?_ hsq (isPullback_projectiveSpaceOverMap n g)
  rw [hi', Stacks.AmpleProjectiveImmersion.liftOver_fst, hover]
  exact hbc

/-- **[Stacks, Tag 01VS]'s conclusion is stable under base change.** If `ℳ` is the hyperplane
sheaf of a finite-dimensional projective space over `S` pulled back along an immersion over `S`,
then its inverse image on a base change `X' = X ×_S S'` is the same for `S'`. -/
theorem hasImmersionTwistOver_baseChange {p : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hbc : IsPullback p f' f g) (M : X.Modules)
    (hM : Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver f M) :
    Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver f'
      ((Scheme.Modules.pullback p).obj M) := by
  obtain ⟨n, i, hi, hover, ⟨e⟩⟩ := hM
  set i' := Stacks.AmpleProjectiveImmersion.liftOver f'
    (p ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
  refine ⟨n, i', ?_, ?_, ⟨?_⟩⟩
  · exact MorphismProperty.of_isPullback (P := @IsImmersion)
      (isPullback_liftOver_baseChange n hbc i hover) hi
  · exact Stacks.AmpleProjectiveImmersion.liftOver_fst _ _
  · refine (Scheme.Modules.pullback p).mapIso e ≪≫ ?_
    refine (Scheme.Modules.pullback p).mapIso
        ((Scheme.Modules.pullbackComp i
          (projectiveSpaceOver.toIntegralAtUniverse n S)).app _) ≪≫ ?_
    refine (Scheme.Modules.pullbackComp p
        (i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).app _ ≪≫ ?_
    exact (Stacks.AmpleProjectiveImmersion.liftOverTwistIso f'
      (p ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).symm

/-- **[Stacks, Tag 0B3F] for a finite-type morphism to an affine base, base changed along a
morphism of affine schemes.** Let `S` and `S'` be affine, `f : X ⟶ S` of finite type, `ℒ` an
invertible `𝒪_X`-module very ample relative to `f`, and let `X' = X ×_S S'` be a base change of
`f` along `g : S' ⟶ S`. Then the inverse image of `ℒ` on `X'` is very ample relative to
`f' : X' ⟶ S'`. -/
@[ega "II 4.4.10" "(iii)"]
theorem isRelativelyVeryAmple_baseChange [IsAffine S] [IsAffine S'] {p : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hbc : IsPullback p f' f g) [LocallyOfFiniteType f] [QuasiCompact f]
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hva : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    @Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S' X' f'
      ((Scheme.Modules.pullback p).obj L)
      (Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
        p.toLRSHom.toShHom L hL) := by
  let : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback p).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry p.toLRSHom.toShHom L hL
  obtain ⟨m, i', hi', hover', ⟨e'⟩⟩ := hasImmersionTwistOver_baseChange hbc L
    (Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple f L hva)
  exact Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion m f'
    ((Scheme.Modules.pullback p).obj L) i' hi' hover' e'

/-- [Stacks, Tag 0B3F] over an affine base at the chosen categorical pullback: the inverse image
of a very ample `ℒ` along `AlgebraicGeometry.pullback.snd` is very ample relative to
`AlgebraicGeometry.pullback.fst`. -/
@[ega "II 4.4.10" "(iii)"]
theorem isRelativelyVeryAmple_baseChange_fst [IsAffine S] [IsAffine S'] (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hva : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    @Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S' (pullback g f) (pullback.fst g f)
      ((Scheme.Modules.pullback (pullback.snd g f)).obj L)
      (Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
        (pullback.snd g f).toLRSHom.toShHom L hL) :=
  isRelativelyVeryAmple_baseChange (IsPullback.of_hasPullback g f).flip L hva

end AlgebraicGeometry

end
