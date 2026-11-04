module

public import StacksFrontier.AlgebraicGeometry.Flatness.FibreFlatnessSpecialization
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative flatness passes to an arbitrary generalization

Let `f : X → S` be a morphism of schemes, let `F` be a quasi-coherent `𝒪_X`-module and let
`x' ⤳ x` be points of `X`. Then flatness of `F` over `S` at `x` implies flatness of `F` over
`S` at `x'`: the stalk `F_{x'}` is a localization of `F_x` over `𝒪_{X, x}`, and the base ring
`𝒪_{S, f(x')}` is a localization of `𝒪_{S, f(x)}`, over which flatness is the same condition.

The same-fibre case is `AlgebraicGeometry.isFlatOverAt_of_specializes`, the implication
(1) ⟹ (2) of Stacks 05UA, in
`StacksFrontier/AlgebraicGeometry/Flatness/FibreFlatnessSpecialization.lean`.

## Main results

* `AlgebraicGeometry.isFlatOverAt_of_specializes_acrossFibres`: relative flatness at `x` implies
  relative flatness at an arbitrary generalization `x'` of `x`, with no condition relating the
  images of `x'` and `x` in `S`.

## Implementation notes

The stalk `F_{x'}` is a localization of `F_x` by
`AlgebraicGeometry.exists_isLocalizedModule_stalkSpecializes`. The two base stalks
`𝒪_{S, f(x')}` and `𝒪_{S, f(x)}` are different rings, the first a localization of the second at
the contraction of its maximal ideal
(`Stacks.StalkSpecialization.isLocalization_atPrime_stalk_of_specializes`). Flatness is moved
across by `Module.flat_iff_of_isLocalization`, the identification of the two actions on `F_{x'}`
being the naturality `AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap`.

## References

* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Relative flatness at a point passes to every generalization of that point.** If a
quasi-coherent `𝒪_X`-module is flat over `S` at `x`, then it is flat over `S` at every point `w`
generalizing `x` — with no condition relating the images of `w` and `x` in `S`.

The stalk `F_w` is a localization of `F_x` over `𝒪_{X, x}`, so it is flat over `𝒪_{S, f x}`;
and `𝒪_{S, f w}` is itself a localization of `𝒪_{S, f x}`, namely at the contraction of its
maximal ideal (`Stacks.StalkSpecialization.isLocalization_atPrime_stalk_of_specializes`), over
which flatness of an `𝒪_{S, f w}`-module is the same condition as flatness over `𝒪_{S, f x}` by
`Module.flat_iff_of_isLocalization`. -/
@[ega "IV 19.7.5" "more general"]
theorem isFlatOverAt_of_specializes_acrossFibres {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] {x w : X} (h : w ⤳ x)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsFlatOverAt f.toLRSHom.toShHom F w := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) := Scheme.Modules.moduleStalk F x
  let : Module (X.presheaf.stalk w) (F.presheaf.stalk w) := Scheme.Modules.moduleStalk F w
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk w) :=
    Module.compHom _ (X.presheaf.stalkSpecializes h).hom
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module (S.presheaf.stalk (f.base x)) (F.presheaf.stalk w) :=
    Module.compHom _ ((X.presheaf.stalkSpecializes h).hom.comp (f.stalkMap x).hom)
  let : Module (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w) :=
    Module.compHom _ (f.stalkMap w).hom
  have : IsScalarTower (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
      (F.presheaf.stalk x) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
      (F.presheaf.stalk w) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x) := hflat
  obtain ⟨T, g, hg⟩ := exists_isLocalizedModule_stalkSpecializes F h
  have : Module.Flat (S.presheaf.stalk (f.base x)) (F.presheaf.stalk w) :=
    Module.Flat.of_isLocalizedModule_of_tower T g
  let : Algebra (S.presheaf.stalk (f.base x)) (S.presheaf.stalk (f.base w)) :=
    (S.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom.toAlgebra
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap f w x h
  have : IsScalarTower (S.presheaf.stalk (f.base x)) (S.presheaf.stalk (f.base w))
      (F.presheaf.stalk w) := by
    refine IsScalarTower.of_algebraMap_smul fun r m => ?_
    change (f.stalkMap w).hom
        ((S.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom r) • m =
      (X.presheaf.stalkSpecializes h).hom ((f.stalkMap x).hom r) • m
    congr 1
    exact congrArg (fun φ : S.presheaf.stalk (f.base x) ⟶ X.presheaf.stalk w => φ.hom r) hnat
  have : IsLocalization.AtPrime (S.presheaf.stalk (f.base w))
      ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base w))).under
        (S.presheaf.stalk (f.base x))) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalk_of_specializes
      (f.base.hom.map_specializes h) (RingHom.algebraMap_toAlgebra _)
  change Module.Flat (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w)
  exact (Module.flat_iff_of_isLocalization (S.presheaf.stalk (f.base w))
    ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base w))).under
      (S.presheaf.stalk (f.base x))).primeCompl (F.presheaf.stalk w)).mpr ‹_›

end AlgebraicGeometry

end

end
