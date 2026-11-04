module

public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.BaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.VeryAmpleFiniteTypeCover.Basic

/-!
# Immersions into projective space and relative very ampleness

An immersion `i : X ⟶ ℙⁿ_S` over `S` with `L ≅ i^* 𝒪(1)` exhibits `L` as very ample relative to
`X ⟶ S` in the sense of [Stacks, Tag 01VM]: the implication (5) ⟹ (3) of [Stacks, Tag 01VT],
over an arbitrary base `S`.

## Main results

* `Stacks.VeryAmpleGlue.isRelativelyVeryAmple_projectiveSpaceTwistingSheaf`: `𝒪(1)` on `ℙⁿ_S` is
  very ample relative to `ℙⁿ_S ⟶ S`.
* `Stacks.VeryAmpleGlue.isRelativelyVeryAmple_comp_of_isImmersion`: very ampleness relative to
  `Y ⟶ S` pulls back along an immersion `X ⟶ Y`.
* `Stacks.VeryAmpleGlue.veryAmpleOfProjectiveImmersion`: an immersion `i : X ⟶ ℙⁿ_S` over `S`
  with `L ≅ i^* 𝒪(1)` exhibits `L` as very ample relative to `X ⟶ S`, stated as
  `Stacks.VeryAmpleFiniteTypeCover.VeryAmpleOfProjectiveImmersion`.

## References

* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 0B3F](https://stacks.math.columbia.edu/tag/0B3F)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.VeryAmpleGlue

/-- **`𝒪(1)` is very ample on the integral model of projective space**, relative to its morphism to
the terminal scheme. -/
theorem isRelativelyVeryAmple_twistingSheafAtUniverse (n : ℕ) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) (twistingSheafAtUniverse.{u} n) := by
  let P := projectiveSpaceAtUniverse.{u} n
  let snd := pullback.snd (terminal.from (⊤_ Scheme.{u})) (terminal.from P)
  let i : P ⟶ projectiveSpaceOver n (⊤_ Scheme.{u}) :=
    pullback.lift (terminal.from P) (𝟙 P) (terminal.hom_ext _ _)
  have hi : i ≫ snd = 𝟙 P := pullback.lift_snd _ _ _
  have : IsIso (terminal.from (⊤_ Scheme.{u})) :=
    ⟨⟨𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩⟩
  have : IsIso i := IsIso.of_isIso_fac_right hi
  exact Stacks.AmpleRelativeFiniteType.isRelativelyVeryAmple_of_hasImmersionTwistOver
    (fun m => Stacks.SymGraded.hasFreeBundleTwistOne (⊤_ Scheme.{u}) m) _ _
    ⟨n, i, inferInstance, terminal.hom_ext _ _, ⟨((Scheme.Modules.pullbackId P).app _).symm ≪≫
      ((Scheme.Modules.pullbackCongr hi).app _).symm ≪≫
      ((Scheme.Modules.pullbackComp i snd).app _).symm⟩⟩

/-- **`𝒪(1)` on `ℙⁿ_S` is very ample relative to `ℙⁿ_S ⟶ S`**, for every scheme `S`. -/
theorem isRelativelyVeryAmple_projectiveSpaceTwistingSheaf (n : ℕ) (S : Scheme.{u}) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple
      (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (projectiveSpaceTwistingSheaf n S) :=
  Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_pullback_fst _ (terminal.from S) _
    (isRelativelyVeryAmple_twistingSheafAtUniverse n)

/-- **Relative very ampleness is carried back along an immersion over the base.** If `M` is very
ample relative to `h : Y ⟶ B`, `i : A ⟶ Y` is an immersion and `N ≅ i^* M`, then `N` is very
ample relative to `i ≫ h`. -/
theorem isRelativelyVeryAmple_comp_of_isImmersion {A Y B : Scheme.{u}} (i : A ⟶ Y) (h : Y ⟶ B)
    [IsImmersion i] (M : Y.Modules) [IsInvertibleModule Y M] (N : A.Modules)
    [IsInvertibleModule A N] (e : N ≅ (Scheme.Modules.pullback i).obj M)
    (hM : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple h M) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (i ≫ h) N := by
  obtain ⟨E, _, j, _, hover, ⟨eM⟩⟩ := hM
  exact Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_immersion _ N E (i ≫ j)
    inferInstance (by rw [Category.assoc, hover]) (e ≪≫ (Scheme.Modules.pullback i).mapIso eM ≪≫
      (Scheme.Modules.pullbackComp i j).app (Stacks.Tag01VMVeryAmple.twistOne E))

/-- An immersion `i : A ⟶ ℙⁿ_B` over `B` with `N ≅ i^* 𝒪(1)` exhibits `N` as very ample relative
to `A ⟶ B`. -/
theorem veryAmpleOfProjectiveImmersion :
    Stacks.VeryAmpleFiniteTypeCover.VeryAmpleOfProjectiveImmersion.{u} := by
  rintro A B g N _ ⟨n, i, _, rfl, ⟨e⟩⟩
  exact isRelativelyVeryAmple_comp_of_isImmersion i _ _ N e
    (isRelativelyVeryAmple_projectiveSpaceTwistingSheaf n B)

end Stacks.VeryAmpleGlue

end
