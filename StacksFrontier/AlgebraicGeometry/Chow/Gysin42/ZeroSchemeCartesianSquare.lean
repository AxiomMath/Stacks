module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# The square of Remark 0B6Y is cartesian

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `s ∈ Γ(X, L)` and `f : X' ⟶ X`. Writing
`i : D = Z(s) ⟶ X` and `i' : D' = Z(f^*s) ⟶ X'`, Remark 0B6Y of the Stacks Project produces the
square

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

and asserts that it is cartesian. `Stacks.Chow.zeroSchemePullbackHom` is the comparison morphism
`g`, obtained in `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible` as the
factorization of `i' ≫ f` through the zero scheme of `s` and unique as such. This file proves
that the square it fills is a pullback square, and reads off from that the two properties of `g`
that Stacks 0B71 needs: `g` is flat of relative dimension `r` whenever `f` is.

`Stacks.Divisors.zeroScheme_pullback` in
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic` states the same content as the
equality of ideal sheaves `Z(f^*s) = f^{-1}(Z(s))`, which combined with Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` identifies `D'` with the fibre product. The
cartesian square at the *canonical* morphism `g` is what a consumer of Stacks 0B71 or 02TA needs,
and it is established inside that proof but not exported; here it is a theorem, so that a
downstream statement need not take `g`, its flatness and its relative dimension as parameters.

## Main results

* `Stacks.Chow.isPullback_zeroSchemePullbackHom` — **Stacks 0B6Y**: the square is cartesian.
* `Stacks.Chow.locallyOfFiniteType_zeroSchemePullbackHom`,
  `Stacks.Chow.flat_zeroSchemePullbackHom`,
  `Stacks.Chow.relativeDimension_zeroSchemePullbackHom` — `g` is locally of finite type, flat, and
  of relative dimension `r`, whenever `f` is.
* `Stacks.Chow.comap_zeroSchemePullbackHom` — a closed subscheme of `X` pulled back to `D` and then
  along `g` is its pullback to `X'` intersected with `D'`.

## Implementation notes

The proof of the pullback property is the universal property of the zero scheme,
[Stacks, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR) (2), in the form
`Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme`: for a cone
`(c.fst, c.snd)` over `f` and `i`, the section `f^*s` pulled back to `c.pt` vanishes, because
`(c.fst ≫ f)^*s` does and the comparison `c.fst^*f^*L ≅ (c.fst ≫ f)^*L` is injective on global
sections (`AlgebraicGeometry.pullbackGlobalSections_injective_pullbackComp`). That produces the
lift, and uniqueness is the monicity of the closed immersions `i` and `i'`.

Flatness and the relative dimension of `g` are then
`CategoryTheory.MorphismProperty.of_isPullback` and
`AlgebraicGeometry.RelativeDimension.of_isPullback`, which is Stacks 02NK.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Stacks 0B6Y.** The square

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

of Remark 0B6Y is cartesian, at the canonical comparison morphism
`g = Stacks.Chow.zeroSchemePullbackHom` of the zero schemes. -/
theorem isPullback_zeroSchemePullbackHom :
    IsPullback (pullbackZeroScheme f L s).subschemeι (zeroSchemePullbackHom f L s) f
      (zeroScheme X L s).subschemeι := by
  let D' := pullbackZeroScheme f L s
  let D := zeroScheme X L s
  let i' : D'.subscheme ⟶ X' := D'.subschemeι
  let i : D.subscheme ⟶ X := D.subschemeι
  let g := zeroSchemePullbackHom f L s
  have hg : g ≫ i = i' ≫ f := zeroSchemePullbackHom_subschemeι f L s
  refine IsPullback.of_isLimit (c := PullbackCone.mk i' g hg.symm) ?_
  have hsection (c : PullbackCone f i) :
      pullbackGlobalSections c.fst ((Scheme.Modules.pullback f).obj L)
        (pullbackGlobalSections f L s) = 0 := by
    have hcomposite : pullbackGlobalSections (c.fst ≫ f) L s = 0 := by
      rw [c.condition,
        ← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp c.snd i L s,
        (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s i).2 ⟨𝟙 _, by simp [i, D]⟩]
      simp
    refine pullbackGlobalSections_injective_pullbackComp c.fst f L ?_
    simpa [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp c.fst f L s]
      using hcomposite
  have hfac (c : PullbackCone f i) := (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X'
    ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s) c.fst).mp (hsection c)
  let lift : ∀ c : PullbackCone f i, c.pt ⟶ D'.subscheme := fun c => (hfac c).choose
  have lift_fst (c : PullbackCone f i) : lift c ≫ i' = c.fst := (hfac c).choose_spec
  have lift_snd (c : PullbackCone f i) : lift c ≫ g = c.snd := by
    refine (cancel_mono i).1 ?_
    rw [Category.assoc, hg, ← Category.assoc, lift_fst, c.condition]
  exact PullbackCone.IsLimit.mk hg.symm lift lift_fst lift_snd
    fun c m hleft _ => (cancel_mono i').1 (hleft.trans (lift_fst c).symm)

/-- The comparison morphism of Remark 0B6Y is locally of finite type when `f` is: it is a base
change of `f` along the closed immersion of the zero scheme. -/
instance locallyOfFiniteType_zeroSchemePullbackHom [LocallyOfFiniteType f] :
    LocallyOfFiniteType (zeroSchemePullbackHom f L s) :=
  MorphismProperty.of_isPullback (isPullback_zeroSchemePullbackHom f L s)
    (P := @LocallyOfFiniteType) inferInstance

/-- The comparison morphism of Remark 0B6Y is flat when `f` is: it is a base change of `f` along
the closed immersion of the zero scheme. -/
instance flat_zeroSchemePullbackHom [Flat f] : Flat (zeroSchemePullbackHom f L s) :=
  MorphismProperty.of_isPullback (isPullback_zeroSchemePullbackHom f L s)
    (P := @Flat) inferInstance

/-- **Stacks 02NK for the square of Remark 0B6Y.** The comparison morphism has the same relative
dimension as `f`. -/
theorem relativeDimension_zeroSchemePullbackHom [LocallyOfFiniteType f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) :
    AlgebraicGeometry.RelativeDimension (zeroSchemePullbackHom f L s) r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_zeroSchemePullbackHom f L s) hf

/-- Pulling a closed subscheme `Z ⊆ X` back to `D = Z(s)` and then along `g` to `D' = Z(f^*s)` is
the same as pulling it back to `X'` and intersecting with `D'`: both are the pullback of `Z` along
the diagonal `g ≫ i = i' ≫ f` of the square of Remark 0B6Y. -/
theorem comap_zeroSchemePullbackHom (Z : X.IdealSheafData) :
    (Z.comap (zeroScheme X L s).subschemeι).comap (zeroSchemePullbackHom f L s) =
      (Z.comap f).comap (pullbackZeroScheme f L s).subschemeι := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    zeroSchemePullbackHom_subschemeι]

end Stacks.Chow

end
