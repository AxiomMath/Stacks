module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantGenericNontrivial

/-!
# The kernel of a stalk map of modules of the same generic rank is torsion

`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` of [Stacks, Tag 0B3T] takes two
hypotheses about the determinant comparison map `σ(f, r)` of `f : F ⟶ F'`: that it is nonzero,
and that it is a stalkwise epimorphism at every point off the divisor. Both are supplied by
`StacksFrontier/AlgebraicGeometry/Divisors/DeterminantStalkIso.lean` and
`StacksFrontier/AlgebraicGeometry/Divisors/DeterminantNonzero.lean` from two facts about `f`
itself at the point: that `f_x` is onto, and that `ker f_x` is torsion. The first is the
vanishing of the quotient off the divisor; the second is what this file proves, for `F` and
`F'` of the same generic rank.

The argument is the source's. On an integral scheme every stalk localizes to the stalk at the
generic point, at *all* the nonzerodivisors
(`Stacks.ModuleStalkGenericPoint.isLocalizedModule_nonZeroDivisors_stalkSpecializes_genericPoint`),
so an element of `F_x` dies in `F_η` exactly when it is torsion. The comparison maps commute
with `f`, so `ker f_x` lands in `ker f_η`; and `f_η` is a surjection between vector spaces of
the same finite dimension over the function field, hence injective.

## Main results

* `AlgebraicGeometry.Scheme.Modules.stalkSpecializes_stalkHom`: the specialization comparison
  of stalks is natural in the module.
* `AlgebraicGeometry.Scheme.Modules.stalkSpecializes_genericPoint_eq_zero_iff`: an element of a
  stalk dies at the generic point exactly when it is torsion.
* `AlgebraicGeometry.Scheme.Modules.injective_stalkHom_genericPoint_of_surjective`: at the
  generic point a surjective stalk map between modules of the same generic rank is injective.
* `AlgebraicGeometry.Scheme.Modules.ker_stalkHom_le_torsion` and
  `ker_stalkHom_le_torsion_of_surjective_genericPoint`: **the kernel of the stalk map at every
  point is torsion.**
* `AlgebraicGeometry.surjective_mapFun_detMap_of_surjective_of_genericRank`: the hypothesis
  `hoff` of `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap`.
* `AlgebraicGeometry.Scheme.Modules.detMap_ne_zero_of_surjective_stalkHom_genericPoint`: the
  hypothesis `hf` of the same theorem.

## Implementation notes

**Naturality is proved on germs, not by Mathlib's `stalkSpecializes_stalkFunctor_map`.** That
lemma is about `TopCat.Presheaf.stalkFunctor Ab`, while `stalkHom` is the `𝒪_{X,x}`-linear map
of `StacksFrontier/AlgebraicGeometry/ReflexiveHull/DualStalk.lean`; crossing between the two costs
more than evaluating both sides on a germ, which both files already have lemmas for.

**`rw` is avoided in the naturality proof and in its consumer.** `modStalk F x` asks for
`F : SheafOfModules (structureSheaf X.sheaf)` and `X.Modules` is `SheafOfModules X.ringCatSheaf`;
the two agree at default transparency but not at the transparency `rw` uses to check its
motive, so the rewrites are written as `congrArg` with the function given explicitly.

**No `@[stacks]` attribute.** This is a step of the proof of Tag 0B3T, not one of its
assertions.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ModuleStalkGenericPoint
open Stacks.ModuleStalkSpecialization
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The specialization comparison of stalks is natural in the module.** Both sides send the
germ at `x` of a section over `W` to the germ at `y` of its image under `f`. -/
theorem stalkSpecializes_stalkHom {F G : X.Modules} (f : F ⟶ G) {x y : X} (h : y ⤳ x)
    (m : F.presheaf.stalk x) :
    G.presheaf.stalkSpecializes h (stalkHom f x m)
      = stalkHom f y (F.presheaf.stalkSpecializes h m) := by
  obtain ⟨W, hxW, t, rfl⟩ := Stacks.SheafOfModules.SheafHomStalk.exists_germ_eq F m
  have hy : y ∈ W := h.mem_open W.isOpen hxW
  exact (congrArg (fun z ↦ G.presheaf.stalkSpecializes h z) (stalkHom_germAt f x W hxW t)).trans
    (((germ_stalkSpecializes_apply G hxW h (Scheme.Modules.Hom.app f W t)).trans
      (stalkHom_germAt f y W hy t).symm).trans
      (congrArg (fun z ↦ stalkHom f y z) (germ_stalkSpecializes_apply F hxW h t).symm))

/-- **An element of a stalk dies at the generic point exactly when it is torsion.** The stalk
at the generic point is the localization at all the nonzerodivisors, and an element of a
localization at a submonoid `S` vanishes exactly when some element of `S` kills it. -/
theorem stalkSpecializes_genericPoint_eq_zero_iff [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] (x : X) (m : modStalk F x) :
    F.presheaf.stalkSpecializes (genericPoint_specializes x) m = 0 ↔
      m ∈ Submodule.torsion (ringStalk X.sheaf x) (modStalk F x) := by
  let := stalkSpecializesModule F (genericPoint_specializes x)
  have := isLocalizedModule_nonZeroDivisors_stalkSpecializes_genericPoint F x
  rw [Submodule.mem_torsion_iff]
  exact IsLocalizedModule.eq_zero_iff (nonZeroDivisors (X.presheaf.stalk x))
    (stalkSpecializesₗ F (genericPoint_specializes x))

/-- **The kernel of a stalk map is torsion as soon as the stalk map at the generic point is
injective.** An element of the kernel at `x` has image in `F_η` killed by the injective `f_η`,
so it dies at the generic point, so it is torsion. -/
theorem ker_stalkHom_le_torsion [IsIntegral X] {F G : X.Modules} [F.IsQuasicoherent]
    (f : F ⟶ G) (hinj : Function.Injective (stalkHom f (genericPoint X))) (x : X) :
    LinearMap.ker (stalkHom f x) ≤
      Submodule.torsion (ringStalk X.sheaf x) (modStalk F x) := by
  intro m hm
  rw [LinearMap.mem_ker] at hm
  rw [← stalkSpecializes_genericPoint_eq_zero_iff F x m]
  have h0 : G.presheaf.stalkSpecializes (genericPoint_specializes x) (stalkHom f x m) = 0 :=
    (congrArg (fun z ↦ G.presheaf.stalkSpecializes (genericPoint_specializes x) z) hm).trans
      (map_zero _)
  exact hinj (((stalkSpecializes_stalkHom f (genericPoint_specializes x) m).symm.trans h0).trans
    (map_zero (stalkHom f (genericPoint X))).symm)

/-- **At the generic point a surjective stalk map between modules of the same generic rank is
injective.** Both stalks are vector spaces over the function field of the same finite
dimension. -/
theorem injective_stalkHom_genericPoint_of_surjective [IsIntegral X] {F G : X.Modules}
    (f : F ⟶ G) (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (G.over U) r] (hU : ∃ x : X, x ∈ U)
    (hsurj : Function.Surjective (stalkHom f (genericPoint X))) :
    Function.Injective (stalkHom f (genericPoint X)) := by
  have := finite_stalk_genericPoint_of_isFiniteLocallyFreeOfRank_over F U r hU
  have := finite_stalk_genericPoint_of_isFiniteLocallyFreeOfRank_over G U r hU
  have hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
        (F.presheaf.stalk (genericPoint X))
      = Module.finrank (X.presheaf.stalk (genericPoint X))
        (G.presheaf.stalk (genericPoint X)) :=
    (finrank_stalk_genericPoint_eq_of_isFiniteLocallyFreeOfRank_over F U r hU).trans
      (finrank_stalk_genericPoint_eq_of_isFiniteLocallyFreeOfRank_over G U r hU).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj

/-- **The torsion-kernel hypothesis, at every point of the scheme**, for a morphism of modules
of the same generic rank whose stalk map at the generic point is onto. -/
theorem ker_stalkHom_le_torsion_of_surjective_genericPoint [IsIntegral X] {F G : X.Modules}
    [F.IsQuasicoherent] (f : F ⟶ G) (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (G.over U) r] (hU : ∃ x : X, x ∈ U)
    (hsurj : Function.Surjective (stalkHom f (genericPoint X))) (x : X) :
    LinearMap.ker (stalkHom f x) ≤
      Submodule.torsion (ringStalk X.sheaf x) (modStalk F x) :=
  ker_stalkHom_le_torsion f (injective_stalkHom_genericPoint_of_surjective f U r hU hsurj) x

/-- **The determinant comparison map of a morphism of modules of the same generic rank whose
stalk map at the generic point is onto is nonzero.** This is the hypothesis `hf` of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap`. -/
theorem detMap_ne_zero_of_surjective_stalkHom_genericPoint [IsIntegral X] {F F' : X.Modules}
    [F.IsQuasicoherent] (f : F ⟶ F') (r : ℕ) (U : X.Opens)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F'.over U) r] (hU : ∃ x : X, x ∈ U)
    [(exteriorPower F (r : ℤ)).IsFinitePresentation]
    [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
    [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
    [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]
    (hsurj : Function.Surjective (stalkHom f (genericPoint X))) :
    detMap f (r : ℤ) ≠ 0 :=
  have := nontrivial_modStalk_det_genericPoint F U r hU
  detMap_ne_zero_of_surjective_of_ker_le_torsion f r (genericPoint X) hsurj
    (ker_stalkHom_le_torsion_of_surjective_genericPoint f U r hU hsurj (genericPoint X))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

/-- **The stalkwise epimorphism hypothesis `hoff` of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap`**, at every point where the stalk map of
`f` is onto, for a morphism of modules of the same generic rank whose stalk map at the generic
point is onto. -/
theorem surjective_mapFun_detMap_of_surjective_of_genericRank [IsIntegral X]
    {F F' : X.Modules} [F.IsQuasicoherent] (f : F ⟶ F') (r : ℕ) (U : X.Opens)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F'.over U) r] (hU : ∃ x : X, x ∈ U)
    [(exteriorPower F (r : ℤ)).IsFinitePresentation]
    [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
    [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
    [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]
    (hsurj : Function.Surjective (stalkHom f (genericPoint X))) (x : X)
    (hx : Function.Surjective (stalkHom f x)) :
    Function.Surjective (Stacks.ModuleStalk.mapFun (detMap f (r : ℤ)) x) :=
  surjective_mapFun_detMap_of_surjective_of_ker_le_torsion f r x hx
    (ker_stalkHom_le_torsion_of_surjective_genericPoint f U r hU hsurj x)

end AlgebraicGeometry

end
