module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback of a zero scheme

Let `L` be an invertible module on a scheme `X`, let `s ∈ Γ(X, L)` and let `f : X' ⟶ X`. The zero
scheme of the pulled-back section `f^* s` is the scheme-theoretic inverse image of the zero scheme
of `s`:

`Z(f^* s) = f⁻¹(Z(s))`,

an equality of quasi-coherent ideal sheaves on `X'`. Combined with Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`, which identifies the inverse-image closed
subscheme with the fibre product `X' ×_X Z(s)`, this is the cartesian square

`Z(f^* s) ⟶ Z(s)`, `Z(f^* s) ⟶ X'`, `Z(s) ⟶ X`, `X' ⟶ X`

of [Stacks, Tag 0B6Y]. The square is what makes the Gysin map of a zero scheme compatible with
base change: it supplies the comparison morphism `Z(f^* s) ⟶ Z(s)` and its properness, rather
than requiring them as hypotheses.

## Main results

* `Stacks.Divisors.pullback_isInvertible` — the pullback of an invertible module is invertible,
  as an instance (Stacks 0B8L in the `AlgebraicGeometry` spelling).
* `Stacks.Divisors.zeroScheme_pullback` — the zero scheme of the pulled-back section is the
  inverse image of the zero scheme.

## Implementation notes

The proof is the universal property of the zero scheme, Stacks 02OR, applied twice. That `f^* s`
vanishes on `Z(f^* s)` gives, via 02OR over `X`, a morphism `g : Z(f^* s) ⟶ Z(s)` with
`i' ≫ f = g ≫ i`; and for any cone `(c.fst, c.snd)` over `f` and `i`, the section `f^* s` pulled
back to `c.pt` vanishes, so 02OR over `X'` produces the lift. Injectivity of the comparison
`c.fst^* f^* L ≅ (c.fst ≫ f)^* L` on global sections —
`AlgebraicGeometry.pullbackGlobalSections_injective_pullbackComp` — is what turns the vanishing of
`(c.fst ≫ f)^* s` into the vanishing of `c.fst^* (f^* s)`.

With the square in hand, the ideal-sheaf equality is a kernel computation: `Z(f^* s)` is the
kernel of `i'`, the square identifies `i'` with `pullback.fst f i` up to an isomorphism, and
kernels are unchanged by precomposition with an isomorphism.

The vanishing statements are never re-derived through the definition of the pullback map on
global sections: the three functoriality lemmas used here
(`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp`,
`pullbackGlobalSections_injective_pullbackComp`, `pullbackGlobalSections_subschemeι_eq_zero`)
are stated once and reused, so no step normalizes a pullback comparison more than once.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **Stacks 0B8L** for schemes. The pullback of an invertible module along a morphism of schemes
is invertible. This is `Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry`
specialised to the ringed space underlying a scheme, registered as an instance so that the zero
scheme of a pulled-back section can be formed without an explicit invertibility argument. -/
instance pullback_isInvertible {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L h

/-- The pulled-back section vanishes on the zero scheme of a section: the closed immersion of the
zero scheme factors through itself by the identity. -/
private theorem pullbackGlobalSections_subschemeι_eq_zero (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    pullbackGlobalSections (zeroScheme X L s).subschemeι L s = 0 :=
  (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s
    (zeroScheme X L s).subschemeι).2 ⟨𝟙 _, by simp⟩

/-- Vanishing of a pulled-back section along a composite is vanishing of the twice-pulled-back
section. -/
private theorem pullbackGlobalSections_comp_eq_zero_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (L : Z.Modules) (s : Γ(L, ⊤)) :
    pullbackGlobalSections (f ≫ g) L s = 0 ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback g).obj L)
        (pullbackGlobalSections g L s) = 0 := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  refine ⟨fun h => pullbackGlobalSections_injective_pullbackComp f g L ?_, fun h => ?_⟩
  · simpa using h
  · simp [h]

/-- **Stacks 0B6Y.** The zero scheme of the pulled-back section is the scheme-theoretic inverse
image of the zero scheme: `Z(f^* s) = f⁻¹(Z(s))` as quasi-coherent ideal sheaves on `X'`.

Together with `AlgebraicGeometry.Scheme.IdealSheafData.comapIso` and its two projection
identities this is the cartesian square `Z(f^* s) ≅ X' ×_X Z(s)` of the tag. -/
@[stacks 0B6Y "the pulled-back zero scheme"]
theorem zeroScheme_pullback {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    zeroScheme X' ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s) =
      (zeroScheme X L s).comap f := by
  let D' := zeroScheme X' ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s)
  let D := zeroScheme X L s
  let i' := D'.subschemeι
  let i := D.subschemeι
  have hi' : pullbackGlobalSections i' ((Scheme.Modules.pullback f).obj L)
      (pullbackGlobalSections f L s) = 0 :=
    pullbackGlobalSections_subschemeι_eq_zero X' ((Scheme.Modules.pullback f).obj L)
      (pullbackGlobalSections f L s)
  have hcompzero : pullbackGlobalSections (i' ≫ f) L s = 0 :=
    (pullbackGlobalSections_comp_eq_zero_iff i' f L s).2 hi'
  obtain ⟨g, hg⟩ :=
    (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s (i' ≫ f)).mp hcompzero
  have hpb : IsPullback i' g f i := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk i' g hg.symm) ?_
    have hsection (c : PullbackCone f i) :
        pullbackGlobalSections c.fst ((Scheme.Modules.pullback f).obj L)
          (pullbackGlobalSections f L s) = 0 := by
      refine (pullbackGlobalSections_comp_eq_zero_iff c.fst f L s).1 ?_
      rw [c.condition, pullbackGlobalSections_comp_eq_zero_iff,
        pullbackGlobalSections_subschemeι_eq_zero X L s]
      simp
    choose lift lift_fst using fun c : PullbackCone f i =>
      (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X'
        ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s) c.fst).mp (hsection c)
    have lift_snd (c : PullbackCone f i) : lift c ≫ g = c.snd :=
      (cancel_mono i).1 <| by rw [Category.assoc, hg, ← Category.assoc, lift_fst, c.condition]
    exact PullbackCone.IsLimit.mk hg.symm lift lift_fst lift_snd
      fun c m hleft _ => (cancel_mono i').1 (hleft.trans (lift_fst c).symm)
  calc
    D' = Scheme.Hom.ker i' := (Scheme.IdealSheafData.ker_subschemeι D').symm
    _ = Scheme.Hom.ker (pullback.fst f i) :=
        (congrArg Scheme.Hom.ker hpb.isoPullback_hom_fst).symm.trans
          (Scheme.Hom.ker_comp_of_isIso _ _)
    _ = D.comap f := rfl

end Stacks.Divisors

/-! ### The cartesian square

The remaining three clauses of Tag 0B6Y are Mathlib's: `Scheme.IdealSheafData.comapIso` identifies
the inverse-image closed subscheme with the fibre product, and `comapIso_hom_fst`,
`comapIso_hom_snd` identify its two projections with the closed immersion of `Z(f^* s)` and with
the induced map to `Z(s)`. Together with `Stacks.Divisors.zeroScheme_pullback` above they give the
cartesian square of the tag. -/

add_to_stacks 0B6Y "the cartesian square" AlgebraicGeometry.Scheme.IdealSheafData.comapIso
add_to_ega "IV 19.4.1" "more general" AlgebraicGeometry.Scheme.IdealSheafData.comapIso
add_to_stacks 0B6Y "the pulled-back inclusion"
  AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst
add_to_ega "I 4.4.1" "closed case" AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst
add_to_stacks 0B6Y "the map to the original zero scheme"
  AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_snd

end

end
