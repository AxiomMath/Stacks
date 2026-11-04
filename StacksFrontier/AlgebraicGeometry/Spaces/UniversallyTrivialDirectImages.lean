module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveStructureMapRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Morphisms with universally trivial direct images of the structure sheaf

A morphism `c : X ⟶ Y` of algebraic spaces has *trivial direct images* when
`𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`: the canonical map `𝒪_Y ⟶ c_*𝒪_X` is an isomorphism and the
first higher direct image of the structure sheaf vanishes. Given a morphism `q : Y ⟶ Z` to a
further algebraic space, `c` has *universally trivial direct images over `Z`* when this remains
true after base change along every morphism from a scheme to `Z`: for every scheme `T`, every
morphism `t : T ⟶ Z`, and the base changes `Y_T = Y ×_Z T` and `X_T = X ×_Y Y_T`, the induced
morphism `c_T : X_T ⟶ Y_T` has trivial direct images.

These are the conditions on a contraction `c : X ⟶ Y` of families of curves over a scheme `S`
in the construction of the stable model of a prestable family of curves, where `Z = S` and the
condition after base change is the clause "and this remains true after base change by any
morphism `S' ⟶ S`". Since the condition is required along all base changes, it is itself stable
under base change: pasting cartesian squares shows that a base change of `c_T` along a morphism
`T' ⟶ T` is a base change of `c` along the composite `T' ⟶ T ⟶ Z`.

## Main definitions

* `AlgebraicGeometry.Space.HasTrivialDirectImages`: `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`.
* `AlgebraicGeometry.Space.HasUniversallyTrivialDirectImages`: the same after every base change
  along a morphism from a scheme to `Z`.

## Main results

* `AlgebraicGeometry.Space.HasTrivialDirectImages.hom_ext` and
  `AlgebraicGeometry.Space.HasTrivialDirectImages.iso_ext`: **rigidity**. Since `𝒪_Y = c_*𝒪_X`,
  morphisms out of `Y` into an algebraic space separated over a base are determined by their
  composites with `c`; in particular an isomorphism `Y ≅ Y'` under `X` over a separated base is
  unique.
* `AlgebraicGeometry.Space.HasUniversallyTrivialDirectImages.hasTrivialDirectImages`: over a
  scheme `Z`, the universal condition contains the condition for `c` itself.
* `AlgebraicGeometry.Space.HasUniversallyTrivialDirectImages.of_isPullback`: the universal
  condition is stable under base change along a morphism from a scheme to `Z`.
* `AlgebraicGeometry.Space.HasUniversallyTrivialDirectImages.of_isPullback_of_isPullback`: the
  same for a contraction `c : X ⟶ Y` over `Z`, with `X ⟶ Z` and `Y ⟶ Z` base changed separately
  and `c_T` any morphism over `T` compatible with `c`; this is the form in which the base change
  of a morphism of families of curves over `S` occurs.

## Implementation notes

The base changes in the universal condition are quantified over all cartesian squares rather
than over chosen fibre products. The two formulations are equivalent, since any two cartesian
squares on the same cospan are isomorphic; quantifying over squares makes the stability under
base change a matter of pasting cartesian squares alone, with no transport of direct images
along isomorphisms of algebraic spaces.

The test objects of the universal condition are schemes, as in the source, read as algebraic
spaces through `AlgebraicGeometry.schemeSpace`.

The direct image is `AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU between the small
étale sites, the canonical map `𝒪_Y ⟶ c_*𝒪_X` is
`AlgebraicGeometry.Space.pushforwardStructureProjection`, and `R¹c_*` is the first right derived
functor of the direct image, which exists because modules on the small étale site of an algebraic
space have injective resolutions (`AlgebraicGeometry.Space.hasInjectiveResolutions_modules`).

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E8B](https://stacks.math.columbia.edu/tag/0E8B)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- A morphism `c : X ⟶ Y` of algebraic spaces has *trivial direct images* when
`𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`: the canonical map `𝒪_Y ⟶ c_*𝒪_X` is an isomorphism and the
first higher direct image of the structure sheaf of `X` vanishes. -/
def HasTrivialDirectImages {X Y : AlgebraicSpaces B S hS} (c : X ⟶ Y) : Prop :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  IsIso (pushforwardStructureProjection B S hS c) ∧
    IsZero (((modulePushforward B S hS c).rightDerived 1).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)))

variable (B S hS) in
/-- A morphism `c : X ⟶ Y` of algebraic spaces has *universally trivial direct images over*
`q : Y ⟶ Z` when `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0` remain true after every base change along a
morphism from a scheme to `Z`: for every scheme `T`, every `t : T ⟶ Z`, every cartesian square
presenting `Y_T = Y ×_Z T` and every cartesian square presenting `X_T = X ×_Y Y_T`, the induced
morphism `c_T : X_T ⟶ Y_T` has trivial direct images. -/
def HasUniversallyTrivialDirectImages {X Y Z : AlgebraicSpaces B S hS} (c : X ⟶ Y)
    (q : Y ⟶ Z) : Prop :=
  ∀ ⦃T : BigFppfOver B S hS⦄ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (t : schemeSpace T ⟶ Z)
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c' : X' ⟶ Y') (q' : Y' ⟶ schemeSpace T),
    IsPullback b q' q t → IsPullback a c' c b → HasTrivialDirectImages B S hS c'

namespace HasTrivialDirectImages

/-- **Rigidity of a morphism with trivial direct images.** If `𝒪_Y = c_*𝒪_X`, then morphisms
`a, b : Y ⟶ W` into an algebraic space separated over `Z`, agreeing over `Z` and after
composition with `c`, are equal: the scheme-theoretic image of `c` is `Y`. -/
theorem hom_ext {X Y W Z : AlgebraicSpaces B S hS} {c : X ⟶ Y}
    (h : HasTrivialDirectImages B S hS c) (q : W ⟶ Z) (hq : IsSeparated B S hS q.hom)
    {a b : Y ⟶ W} (hab : a ≫ q = b ≫ q) (hcab : c ≫ a = c ≫ b) : a = b :=
  have : IsIso (pushforwardStructureProjection B S hS c) := h.1
  hom_ext_of_injective_structureSharp B S hS c
    (@injective_structureSharp_app_of_mono B S hS _ _ c (IsIso.mono_of_iso _)) q hq hab hcab

/-- **An isomorphism of targets under the source is unique.** If `𝒪_Y = c_*𝒪_X` and `Y'` is
separated over `Z`, two isomorphisms `e, e' : Y ≅ Y'` agreeing over `Z` with
`c ≫ e = c ≫ e'` are equal. -/
theorem iso_ext {X Y Y' Z : AlgebraicSpaces B S hS} {c : X ⟶ Y}
    (h : HasTrivialDirectImages B S hS c) (q' : Y' ⟶ Z) (hq' : IsSeparated B S hS q'.hom)
    {e e' : Y ≅ Y'} (he : e.hom ≫ q' = e'.hom ≫ q') (hce : c ≫ e.hom = c ≫ e'.hom) : e = e' :=
  Iso.ext (h.hom_ext q' hq' he hce)

end HasTrivialDirectImages

namespace HasUniversallyTrivialDirectImages

/-- **The universal condition contains the condition itself**: over a scheme `Z`, a morphism with
universally trivial direct images has trivial direct images, by the base change along the
identity of `Z`. -/
theorem hasTrivialDirectImages {X Y : AlgebraicSpaces B S hS} {Z : BigFppfOver B S hS}
    {c : X ⟶ Y} {q : Y ⟶ schemeSpace Z}
    (h : HasUniversallyTrivialDirectImages B S hS c q) : HasTrivialDirectImages B S hS c :=
  h (𝟙 _) (𝟙 X) (𝟙 Y) c q (IsPullback.of_id_fst) (IsPullback.of_id_fst)

/-- **Universally trivial direct images are stable under base change.** If `c : X ⟶ Y` has
universally trivial direct images over `q : Y ⟶ Z`, then so has every base change
`c' : X' ⟶ Y'` of it along a morphism `t : T ⟶ Z` from a scheme, over `q' : Y' ⟶ T`: a further
base change of `c'` along `T' ⟶ T` is, by pasting cartesian squares, the base change of `c` along
the composite `T' ⟶ T ⟶ Z`. -/
theorem of_isPullback {X Y Z X' Y' : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    {c : X ⟶ Y} {q : Y ⟶ Z} (h : HasUniversallyTrivialDirectImages B S hS c q)
    {t : schemeSpace T ⟶ Z} {a : X' ⟶ X} {b : Y' ⟶ Y} {c' : X' ⟶ Y'}
    {q' : Y' ⟶ schemeSpace T} (hY : IsPullback b q' q t) (hX : IsPullback a c' c b) :
    HasUniversallyTrivialDirectImages B S hS c' q' :=
  fun _ _ _ t₂ a₂ b₂ c₂ q₂ hY₂ hX₂ =>
    h (t₂ ≫ t) (a₂ ≫ a) (b₂ ≫ b) c₂ q₂ (hY₂.paste_horiz hY) (hX₂.paste_horiz hX)

/-- **Base change of a contraction over a base.** Let `c : X ⟶ Y` be a morphism over `Z`, with
structure morphisms `f : X ⟶ Z` and `q : Y ⟶ Z`, having universally trivial direct images over
`q`. Let `t : T ⟶ Z` be a morphism from a scheme, let `X'` and `Y'` be base changes of `X` and
`Y` along `t`, and let `c' : X' ⟶ Y'` be a morphism over `T` compatible with `c`. Then `c'` has
universally trivial direct images over `T`: the square formed by `c` and `c'` is cartesian, by
cancellation of the cartesian square of `Y'` from that of `X'`. -/
theorem of_isPullback_of_isPullback {X Y Z X' Y' : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} {c : X ⟶ Y} {f : X ⟶ Z} {q : Y ⟶ Z} (hcq : c ≫ q = f)
    (h : HasUniversallyTrivialDirectImages B S hS c q) {t : schemeSpace T ⟶ Z}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c' : X' ⟶ Y'} {f' : X' ⟶ schemeSpace T}
    {q' : Y' ⟶ schemeSpace T} (hc'q' : c' ≫ q' = f') (hc : c' ≫ b = a ≫ c)
    (hY : IsPullback b q' q t) (hX : IsPullback a f' f t) :
    HasUniversallyTrivialDirectImages B S hS c' q' := by
  subst hcq hc'q'
  exact h.of_isPullback hY (IsPullback.of_bot hX hc.symm hY)

end HasUniversallyTrivialDirectImages

end AlgebraicGeometry.Space

end
