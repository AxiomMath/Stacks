module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteType
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# Local finite type from a cartesian thickening of the target

Let `S` be a scheme contained in a big fppf site `B`, let `a : F ⟶ T` be a morphism of
presheaves on the big fppf site of `S` with representable target, and let `m : b ⟶ T` be a
thickening of `T` by an object of the site which factors through `a` in such a way that the
square it makes with `a` is cartesian. If the thickening is of *finite order* then `a` is
locally of finite type.

This is used in the Noetherian case of Stacks 0GHZ. Stacks proves that case by making the
source of `a` an affine scheme through Stacks 07VT and reading the finiteness off the rings;
here the finiteness is obtained directly, without Stacks 07VT. In both arguments the defining
ideal of the thickening has to be nilpotent and not merely nil, which is what a Noetherian
target supplies and what fails in general by the counterexample of Stacks 06RH.

## Main results

* `Stacks.Thickenings.isFiniteOrderThickening_of_isThickening_of_isNoetherianRing`: a
  thickening of an affine scheme with Noetherian ring of global sections is of finite order.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isPullback_of_isFiniteOrderThickening`:
  a morphism to a representable presheaf which a finite-order thickening of the target
  factors through cartesianly is locally of finite type.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_mono_of_thickening_factors_of_isNoetherianRing`
  states the same for a monomorphism to a Noetherian affine scheme of the site through which a
  thickening of that scheme factors, where the cartesian square comes for free.

## Implementation notes

Finite order at the level of schemes is a vanishing power of the defining ideal sheaf, so the
first statement is the ideal-sheaf form of "a nil finitely generated ideal is nilpotent": the
defining ideal sheaf of a thickening has full support by
`Stacks.Thickenings.IsThickening.support_ker_eq_top`, an affine scheme is quasi-compact, and
on a Noetherian affine scheme every ideal of every affine open is finitely generated, which
is what `Stacks.Thickenings.exists_pow_eq_bot_of_fg_of_support_eq_top` asks for.

The second statement is proved one étale chart at a time, which is what local finite type for
a morphism of algebraic spaces means. Over a square of étale charts `U ⟶ F` and `V ⟶ T` of
`a` the thickening is pulled back twice: to `U₀ = U ×_F b` using that the chart of the source
is relatively representable, and to `V₀ = V ×_T b` using the same for the chart of the target.
Pasting the cartesian square of the thickening onto the first of these identifies `U₀` with
`U ×_T b` as well, so `U₀` is also the fibre product of `U` and `V₀` over `V`; the resulting
square of schemes is a cartesian morphism of thickenings whose lower row is the chart morphism
`U ⟶ V` and whose base thickening `V₀ ⟶ V` is of finite order, being a base change of
`b ⟶ T`. Its upper row `U₀ ⟶ V₀` is locally of finite type because both `U₀` and `V₀` are
étale over `b` — they are base changes of the two charts — so
`Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening`, the scheme-level
Stacks 09ZW, transports the finiteness to the chart morphism.

No algebraicity hypothesis on `F` is needed: the charts are quantified over, and the only
representability used is that of the two charts and of the thickening, each of which is part
of the hypothesis that makes it a chart or a closed immersion.

## References

* [Stacks Project, Tag 06RH](https://stacks.math.columbia.edu/tag/06RH)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 0GHZ](https://stacks.math.columbia.edu/tag/0GHZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- A thickening of an affine scheme whose ring of global sections is Noetherian is of finite
order: the defining ideal sheaf has full support, hence consists of nilpotents, and on a
Noetherian affine scheme it is finitely generated on each affine open, so a single power of
it vanishes. -/
theorem isFiniteOrderThickening_of_isThickening_of_isNoetherianRing {W Z : Scheme.{u}}
    [IsAffine Z] {i : W ⟶ Z} (hi : IsThickening i) (hZ : IsNoetherianRing Γ(Z, ⊤)) :
    IsFiniteOrderThickening i := by
  have _ : IsLocallyNoetherian Z :=
    isLocallyNoetherian_of_affine_cover (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top Z⟩)
      (by simp) fun _ ↦ hZ
  have hfg : ∀ U : Z.affineOpens, (i.ker.ideal U).FG := by
    intro U
    have _ : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian U
    exact IsNoetherian.noetherian _
  exact ⟨hi.1, exists_pow_eq_bot_of_fg_of_support_eq_top hfg hi.support_ker_eq_top⟩

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism to a representable presheaf on the big fppf site of `S` through which a
finite-order thickening of the target factors, cartesianly, is locally of finite type.

Both charts of a square of étale charts of `a` are pulled back along the thickening; the two
results are étale over its source, and the square they form with the chart morphism is a
cartesian morphism of thickenings whose base thickening is of finite order. The scheme-level
Stacks 09ZW therefore carries local finite type from the upper row to the chart morphism. -/
theorem isLocallyOfFiniteType_of_isPullback_of_isFiniteOrderThickening
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T b : BigFppfOver B S hS}
    (a : F ⟶ yoneda.obj T) (m : b ⟶ T)
    (hm : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map m))
    (c : yoneda.obj b ⟶ F) (hcart : IsPullback c (𝟙 (yoneda.obj b)) a (yoneda.map m)) :
    IsLocallyOfFiniteType B S hS a := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  intro U V α β w hα hβ hcomm
  obtain ⟨v, rfl⟩ := yoneda.map_surjective β
  -- The thickening pulled back along the chart of the source.
  obtain ⟨U₀, sU, fU, hpbU⟩ := hα.rep c
  obtain ⟨p, rfl⟩ := yoneda.map_surjective fU
  have hsU : MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) sU := hα.property c _ sU hpbU
  have _ : Etale ((BigFppfOver.toScheme B S hS).map sU) := hsU
  -- The thickening pulled back along the chart of the target.
  obtain ⟨V₀, sV, fV, hpbV⟩ := hβ.rep (yoneda.map m)
  obtain ⟨q, rfl⟩ := yoneda.map_surjective fV
  have hpbVsite : IsPullback q sV v m := hpbV.of_map_of_faithful yoneda
  have hqFO : Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B S hS).map q) :=
    Stacks.Thickenings.isFiniteOrderThickening_of_isPullback
      (IsPullback.map (BigFppfOver.toScheme B S hS) hpbVsite) hm
  -- The morphism between the two pulled-back thickenings.
  have hca : c ≫ a = yoneda.map m := by simpa using hcart.w
  have hlift : (p ≫ w) ≫ v = sU ≫ m := by
    refine yoneda.map_injective ?_
    simp only [Functor.map_comp]
    rw [Category.assoc, hcomm, ← Category.assoc, hpbU.w, Category.assoc, hca]
  have hk1 : hpbVsite.lift (p ≫ w) sU hlift ≫ q = p ≫ w := hpbVsite.lift_fst _ _ _
  have hk2 : hpbVsite.lift (p ≫ w) sU hlift ≫ sV = sU := hpbVsite.lift_snd _ _ _
  set k : U₀ ⟶ V₀ := hpbVsite.lift (p ≫ w) sU hlift with hk
  -- Pasting the cartesian square of the thickening makes `U₀` the fibre product over `T`.
  have hbig : IsPullback (yoneda.map sU) (yoneda.map p) (yoneda.map m) (α ≫ a) := by
    simpa using IsPullback.paste_horiz hpbU.flip hcart.flip
  have hsq : IsPullback (yoneda.map k) (yoneda.map p) (yoneda.map q) (yoneda.map w) := by
    have e1 : yoneda.map k ≫ yoneda.map sV = yoneda.map sU := by
      rw [← Functor.map_comp, hk2]
    have hs : IsPullback (yoneda.map k ≫ yoneda.map sV) (yoneda.map p) (yoneda.map m)
        (yoneda.map w ≫ yoneda.map v) := by
      rw [e1, hcomm]
      exact hbig
    refine IsPullback.of_right hs ?_ hpbV.flip
    rw [← Functor.map_comp, ← Functor.map_comp, hk1]
  have hsqsch := IsPullback.map (BigFppfOver.toScheme B S hS)
    (hsq.of_map_of_faithful yoneda : IsPullback k p q w)
  -- The upper row is étale over the source of the thickening, hence of finite type.
  have hkLFT : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k) := by
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k ≫
        (BigFppfOver.toScheme B S hS).map sV) := by
      rw [← Functor.map_comp, hk2]
      infer_instance
    exact locallyOfFiniteType_of_comp ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map sV)
  exact (Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening _ _ _ _ hqFO
    hsqsch.flip).mp hkLFT

/-- A monomorphism of presheaves on the big fppf site of `S` to a Noetherian affine scheme of
the site through which a thickening of that scheme factors is locally of finite type.

Monomorphy makes the factorisation square cartesian, and a thickening of a Noetherian affine
scheme is of finite order, so
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isPullback_of_isFiniteOrderThickening`
applies. -/
theorem isLocallyOfFiniteType_of_mono_of_thickening_factors_of_isNoetherianRing
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T b : BigFppfOver B S hS}
    (a : F ⟶ yoneda.obj T) (hmono : Mono a)
    (hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hTN : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (m : b ⟶ T)
    (hm : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map m))
    (c : yoneda.obj b ⟶ F) (hc : c ≫ a = yoneda.map m) :
    IsLocallyOfFiniteType B S hS a := by
  have _ : Mono a := hmono
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
  exact isLocallyOfFiniteType_of_isPullback_of_isFiniteOrderThickening B S hS a m
    (Stacks.Thickenings.isFiniteOrderThickening_of_isThickening_of_isNoetherianRing hm hTN) c
    (isPullback_id_of_comp_mono c a hc).flip

end AlgebraicGeometry.Space

end
