module

public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleBaseChangeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleBaseChangeCriteriaComplete

/-!
# The ampleness clause of Stacks 0D36 descends along fpqc families of test schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`L` be an invertible `𝒪_X`-module. For a scheme `T` of the site and a morphism
`g : yoneda.obj T ⟶ Y`, the clause `AlgebraicGeometry.Space.IsAmpleOnBaseChange` of Stacks
0D36 asks that the base change of `f` along `g` be a scheme carrying a relatively ample pullback
of `L`. This file proves that the *ampleness half* of the clause at `T` follows from the whole
clause on the members of any fpqc covering family of `T` by schemes of the site, and that
relative ampleness may be tested on the affine schemes of the site.

## Main results

* `AlgebraicGeometry.Space.exists_isRelativelyAmple_of_fpqcFamily`: for a cartesian square
  presenting the base change of `f` along `g` by a scheme `U`, the pullback of `L` to `U` is
  invertible and ample relative to `U ⟶ T`, provided the clause of Stacks 0D36 holds on the
  members of an fpqc covering family of `T`. This is scheme-level fpqc descent of relative
  ampleness, [Stacks, Tag 0D2P] (`Stacks.Descent.isRelativelyAmple_of_forall_of_fpqcCover`),
  carried to the cartesian squares of algebraic spaces.
* `AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_affine_isAmpleOnBaseChange`: relative
  ampleness of an invertible module may be tested on the affine schemes of the site. The
  implication (3) ⇒ (2) of Stacks 0D36 it uses is the base's
  `AlgebraicGeometry.Space.isAmpleOnBaseChange_of_forall_affine`.

## Implementation notes

**Fibre products of test schemes are taken in the site.** For the covering family
`uᵢ : Tᵢ ⟶ T` and the given square with corner `U`, the fibre product `U ×_T Tᵢ` is formed in
the big fppf category over `S`, which has pullbacks, and the passage to schemes preserves them.
The Yoneda image of its cartesian square, pasted with the given square, presents the base
change of `f` along `Tᵢ ⟶ Y`, so the clause at `Tᵢ` applies to it; and the reading of `L` on
`U ×_T Tᵢ` is the pullback of its reading on `U` by
`AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`.

**Invertibility of the pullback of `L` to `U`** is not part of any hypothesis on `U` itself; it
is `AlgebraicGeometry.Space.isInvertibleModule_baseChangeModule`.

## References

* [Stacks Project, Tag 0D36](https://stacks.math.columbia.edu/tag/0D36)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The ampleness clause of Stacks 0D36 descends along an fpqc covering family of the test
scheme.** Let `f : X ⟶ Y` be a morphism of algebraic spaces, `L` an invertible `𝒪_X`-module,
`T` a scheme of the site with a morphism `g : yoneda.obj T ⟶ Y`, and `uᵢ : Tᵢ ⟶ T` a family of
morphisms of the site whose underlying family of schemes is an fpqc covering of `T`. If the
clause of Stacks 0D36 holds at every `Tᵢ`, then for every cartesian square presenting the base
change of `f` along `g` by a scheme `U`, the pullback of `L` to `U` is invertible and ample
relative to `U ⟶ T`. -/
theorem exists_isRelativelyAmple_of_fpqcFamily {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    {T : BigFppfOver B S hS} (g : yoneda.obj T ⟶ Y.1) {ι : Type v}
    {T' : ι → BigFppfOver B S hS} (u : ∀ i, T' i ⟶ T)
    (hu : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (T' i))
      (fun i => (BigFppfOver.toScheme B S hS).map (u i)) ∈
        Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj T))
    (h : ∀ i, IsAmpleOnBaseChange B S hS f L (T' i) (yoneda.map (u i) ≫ g))
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ T)
    (hsq : IsPullback p (yoneda.map q) f.hom g) :
    ∃ hL' : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B S hS).map q)
        (baseChangeModule B S hS L U p) hL' := by
  have hinv := isInvertibleModule_baseChangeModule L hL U p
  refine ⟨hinv, ?_⟩
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hsqS : ∀ i, IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst q (u i)))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd q (u i)))
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map (u i)) :=
    fun i => (IsPullback.of_hasPullback q (u i)).map (BigFppfOver.toScheme B S hS)
  refine Stacks.Descent.isRelativelyAmple_of_forall_of_fpqcCover hu
    ((BigFppfOver.toScheme B S hS).map q) (baseChangeModule B S hS L U p) hsqS fun i => ?_
  have hsqY : IsPullback (yoneda.map (pullback.fst q (u i)) ≫ p)
      (yoneda.map (pullback.snd q (u i))) f.hom (yoneda.map (u i) ≫ g) :=
    ((IsPullback.of_hasPullback q (u i)).map yoneda).paste_horiz hsq
  obtain ⟨hinv', hamp⟩ := (h i).2 _ _ _ hsqY
  obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hL U (pullback q (u i)) p
    (pullback.fst q (u i))
  have := hinv'
  exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp hamp

/-- **Relative ampleness may be tested on the affine schemes of the site.** For an invertible
`𝒪_X`-module, `L` is ample on `X / Y` exactly when the clause of Stacks 0D36 holds at every
affine scheme of the site over `Y`: this is the equivalence of parts (1) and (3) of Stacks 0D36,
with nothing carried. -/
theorem isRelativelyAmple_iff_forall_affine_isAmpleOnBaseChange {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
          L) :
    IsRelativelyAmple B S hS f L ↔
      ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ g : yoneda.obj T ⟶ Y.1, IsAmpleOnBaseChange B S hS f L T g :=
  ⟨fun hamp T _ g => isAmpleOnBaseChange_of_isRelativelyAmple hamp T g,
    fun h => (isRelativelyAmple_iff_forall_isAmpleOnBaseChange f L).mpr
      (isAmpleOnBaseChange_of_forall_affine hL h)⟩

end AlgebraicGeometry.Space

end
