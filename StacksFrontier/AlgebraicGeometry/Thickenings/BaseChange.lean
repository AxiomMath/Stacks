module

public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Thickenings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Thickenings are stable under base change

Let `i : Z ⟶ Z'` be a thickening of schemes and let `f : X ⟶ Z'` be any morphism. The base change
of `i` along `f` is again a thickening, of the same order: the closed immersion and the
surjectivity are both stable under base change, and the kernel ideal sheaf of the base change is
the inverse image of the kernel ideal sheaf of `i`, which sends a vanishing power to a vanishing
power. This is [Stacks Project, Tag 09ZU].

## Main results

* `Stacks.IdealSheaf.comap_pow_eq_bot`: if a power of an ideal sheaf vanishes, the same power of
  its inverse image along an arbitrary morphism vanishes.
* `Stacks.Thickenings.ker_pow_eq_bot_of_isPullback`: the corresponding statement for the kernel
  ideal sheaf of the base change of a closed immersion.
* `Stacks.Thickenings.isThickening_of_isPullback`,
  `Stacks.Thickenings.isNthOrderThickening_of_isPullback`,
  `Stacks.Thickenings.isFirstOrderThickening_of_isPullback` and
  `Stacks.Thickenings.isFiniteOrderThickening_of_isPullback`: a base change of a thickening, of an
  `n`th-order thickening, of a first-order thickening or of a finite-order thickening is again one
  of the same kind.
* `Stacks.Thickenings.isFirstOrderThickening_pullback_fst` and
  `Stacks.Thickenings.isFiniteOrderThickening_pullback_fst`: the first-order and finite-order cases
  for the projection out of the chosen fibre product.

## Implementation notes

A base change square, as a morphism of thickenings, is the morphism of `CategoryTheory.Arrow` given
by the commuting square of the pullback, so the content of Tag 09ZU is the four stability
statements. These reduce to `Stacks.IdealSheaf.comap_pow_eq_bot`, which is checked on the affine
opens of the source lying over affine opens of the target.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.IdealSheaf

variable {X Y : Scheme.{u}}

/-- **The inverse image of an ideal sheaf with a vanishing power, on one affine open.** If the
`n`th power of an ideal sheaf `I` on `Y` vanishes, then the `n`th power of the ideal of `I.comap f`
vanishes on every affine open `U` of `X` which lies over an affine open `V` of `Y`. -/
theorem ideal_comap_pow_eq_bot_of_isAffineOpen (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ)
    (hI : I ^ n = ⊥) {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    ((I.comap f).ideal ⟨U, hU⟩) ^ n = ⊥ := by
  have hUa : IsAffine U.toScheme := hU
  have hVa : IsAffine V.toScheme := hV
  set g : U.toScheme ⟶ V.toScheme := f.resLE V U hUV with hg
  have hcomp : U.ι ≫ f = g ≫ V.ι := (Scheme.Hom.resLE_comp_ι f hUV).symm
  have hcomap : (I.comap f).comap U.ι = (I.comap V.ι).comap g := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]
  have e1 : ((I.comap f).comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩ =
      Ideal.map U.topIso.inv.hom ((I.comap f).ideal ⟨U, hU⟩) :=
    ideal_comap_ι_top (I.comap f) hU _
  have e2 : ((I.comap V.ι).comap g).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩ =
      Ideal.map g.appTop.hom ((I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) :=
    ideal_comap_top_of_isAffine (I.comap V.ι) g
  have e3 : (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ =
      Ideal.map V.topIso.inv.hom (I.ideal ⟨V, hV⟩) :=
    ideal_comap_ι_top I hV _
  have hIV : (I.ideal ⟨V, hV⟩) ^ n = ⊥ := by
    have hpow := congrArg (fun K : Y.IdealSheafData => K.ideal ⟨V, hV⟩) hI
    simpa [Scheme.IdealSheafData.ideal_pow] using hpow
  have key : Ideal.map U.topIso.inv.hom (((I.comap f).ideal ⟨U, hU⟩) ^ n) =
      Ideal.map U.topIso.inv.hom ⊥ := by
    rw [Ideal.map_pow, ← e1, hcomap, e2, e3, ← Ideal.map_pow, ← Ideal.map_pow, hIV,
      Ideal.map_bot, Ideal.map_bot, Ideal.map_bot]
  exact ideal_map_hom_injective U.topIso.symm key

/-- **A vanishing power of an ideal sheaf is inherited by the inverse image.** If `I ^ n = ⊥` for
an ideal sheaf `I` on `Y`, then `(I.comap f) ^ n = ⊥` for every morphism `f : X ⟶ Y`. -/
theorem comap_pow_eq_bot (I : Y.IdealSheafData) (f : X ⟶ Y) {n : ℕ} (hI : I ^ n = ⊥) :
    (I.comap f) ^ n = ⊥ := by
  have hbasis : ∀ x : X, ∃ (U : X.affineOpens) (V : Y.Opens),
      IsAffineOpen V ∧ x ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV)
        (f ⁻¹ᵁ V).isOpen
    exact ⟨⟨U, hU⟩, V, hV, hxU, hUV⟩
  choose U V hV hmem hle using hbasis
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ fun x => ?_
  · refine top_le_iff.mp fun x _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩
  · simpa [Scheme.IdealSheafData.ideal_pow] using
      ideal_comap_pow_eq_bot_of_isAffineOpen I f n hI (U x).2 (hV x) (hle x)

end Stacks.IdealSheaf

namespace Stacks.Thickenings

variable {P X Y Z : Scheme.{u}}

/-- **The kernel ideal sheaf of a base change of a closed immersion inherits a vanishing power.**
If `i : Z ⟶ Y` is a closed immersion with `i.ker ^ n = ⊥` and the square with sides `f' : P ⟶ X`,
`g' : P ⟶ Z`, `f : X ⟶ Y` and `i` is a pullback square, then `f'.ker ^ n = ⊥`. -/
theorem ker_pow_eq_bot_of_isPullback {f' : P ⟶ X} {g' : P ⟶ Z} {f : X ⟶ Y} {i : Z ⟶ Y}
    (h : IsPullback f' g' f i) (hi : IsClosedImmersion i) {n : ℕ} (hn : i.ker ^ n = ⊥) :
    f'.ker ^ n = ⊥ := by
  have := hi
  have hker : f'.ker = (pullback.fst f i).ker := by
    rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  rw [hker, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact Stacks.IdealSheaf.comap_pow_eq_bot i.ker f hn

/-- A base change of a closed immersion with a vanishing kernel power has the same property. -/
private theorem isClosedImmersion_and_ker_pow_eq_bot_of_isPullback {f' : P ⟶ X} {g' : P ⟶ Z}
    {f : X ⟶ Y} {i : Z ⟶ Y} {n : ℕ} (h : IsPullback f' g' f i)
    (hi : IsClosedImmersion i ∧ i.ker ^ n = ⊥) : IsClosedImmersion f' ∧ f'.ker ^ n = ⊥ :=
  ⟨MorphismProperty.of_isPullback h.flip hi.1, ker_pow_eq_bot_of_isPullback h hi.1 hi.2⟩

/-- **A base change of a thickening is a thickening.** If `i : Z ⟶ Y` is a thickening and the
square with sides `f' : P ⟶ X`, `g' : P ⟶ Z`, `f : X ⟶ Y` and `i` is a pullback square, then `f'`
is a thickening. -/
@[stacks 09ZU "a base change of a thickening is a thickening", ega "I 4.3.2" "thickenings"]
theorem isThickening_of_isPullback {f' : P ⟶ X} {g' : P ⟶ Z} {f : X ⟶ Y} {i : Z ⟶ Y}
    (h : IsPullback f' g' f i) (hi : IsThickening i) : IsThickening f' := by
  exact ⟨MorphismProperty.of_isPullback h.flip hi.1,
    (MorphismProperty.of_isPullback (P := @Surjective.{u}) h.flip ⟨hi.2⟩).1⟩

/-- **A base change of an `n`th-order thickening is an `n`th-order thickening.** If `i` is an
`n`th-order thickening and the square with sides `f'`, `g'`, `f` and `i` is a pullback square, then
`f'` is an `n`th-order thickening. -/
@[stacks 09ZU "a base change of an nth-order thickening is an nth-order thickening"]
theorem isNthOrderThickening_of_isPullback {f' : P ⟶ X} {g' : P ⟶ Z} {f : X ⟶ Y} {i : Z ⟶ Y}
    {n : ℕ} (h : IsPullback f' g' f i) (hi : IsNthOrderThickening n i) :
    IsNthOrderThickening n f' :=
  isClosedImmersion_and_ker_pow_eq_bot_of_isPullback h hi

/-- **A base change of a first-order thickening is a first-order thickening.** If `i` is a
first-order thickening and the square with sides `f'`, `g'`, `f` and `i` is a pullback square, then
`f'` is a first-order thickening. -/
@[stacks 09ZU "a base change of a first-order thickening is a first-order thickening"]
theorem isFirstOrderThickening_of_isPullback {f' : P ⟶ X} {g' : P ⟶ Z} {f : X ⟶ Y} {i : Z ⟶ Y}
    (h : IsPullback f' g' f i) (hi : IsFirstOrderThickening i) :
    IsFirstOrderThickening f' :=
  isClosedImmersion_and_ker_pow_eq_bot_of_isPullback h hi

/-- **A base change of a finite-order thickening is a finite-order thickening.** If `i` is a
finite-order thickening and the square with sides `f'`, `g'`, `f` and `i` is a pullback square,
then `f'` is a finite-order thickening. -/
@[stacks 09ZU "a base change of a finite-order thickening is a finite-order thickening"]
theorem isFiniteOrderThickening_of_isPullback {f' : P ⟶ X} {g' : P ⟶ Z} {f : X ⟶ Y} {i : Z ⟶ Y}
    (h : IsPullback f' g' f i) (hi : IsFiniteOrderThickening i) :
    IsFiniteOrderThickening f' :=
  have := isClosedImmersion_and_ker_pow_eq_bot_of_isPullback h ⟨hi.1, hi.2.choose_spec⟩
  ⟨this.1, _, this.2⟩

/-- **The projection out of a fibre product with a first-order thickening.** If `i : Z ⟶ Y` is a
first-order thickening then so is `CategoryTheory.Limits.pullback.fst f i`. -/
theorem isFirstOrderThickening_pullback_fst (f : X ⟶ Y) {i : Z ⟶ Y}
    (hi : IsFirstOrderThickening i) : IsFirstOrderThickening (pullback.fst f i) :=
  isFirstOrderThickening_of_isPullback (IsPullback.of_hasPullback f i) hi

/-- **The projection out of a fibre product with a finite-order thickening.** If `i : Z ⟶ Y` is a
finite-order thickening then so is `CategoryTheory.Limits.pullback.fst f i`. -/
theorem isFiniteOrderThickening_pullback_fst (f : X ⟶ Y) {i : Z ⟶ Y}
    (hi : IsFiniteOrderThickening i) : IsFiniteOrderThickening (pullback.fst f i) :=
  isFiniteOrderThickening_of_isPullback (IsPullback.of_hasPullback f i) hi

end Stacks.Thickenings

end
