module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesFibered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative ampleness under an arbitrary cartesian base change

If `L` is ample relative to `f : X ⟶ S` and the square with sides `p : X' ⟶ X`, `f' : X' ⟶ S'`,
`f` and `g : S' ⟶ S` is cartesian, then the pullback of `L` along `p` is ample relative to `f'`.
For the chosen fibre product `X ×_S S'` this is
`Stacks.RelativeAmpleBaseChange.isRelativelyAmple_modulePullback_unconditional`.

## Main results

* `Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso`: the pullback of an ample invertible
  module along an isomorphism of schemes is ample.
* `Stacks.AmpleBridge.isRelativelyAmple_comp_of_isIso`: relative ampleness is unchanged when the
  source of the morphism is replaced by an isomorphic scheme and the module is pulled back.
* `Stacks.AmpleBridge.relativelyAmpleBaseChange`: relative ampleness is preserved by base change
  along an arbitrary cartesian square, in the form
  `AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`.
* `Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback`: the same statement for
  `Stacks.RelativeAmple.IsRelativelyAmple`.

## References

* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.AmpleLocallyClosed (pullbackModule)

namespace Stacks.AmpleBridge

/-- The pullback of an ample invertible module along an isomorphism of schemes is ample, in the
sense of `Stacks.Ample.IsAmple`. -/
theorem isAmple_pullbackModule_of_isIso {A B : Scheme.{u}} (i : A ⟶ B) [IsIso i] (N : B.Modules)
    [Stacks.Ample.IsInvertibleModule B N] (h : Stacks.Ample.IsAmple B N) :
    Stacks.Ample.IsAmple A (pullbackModule i N) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible A.toRingedSpace.presheaf
      (structureSheafRing A.toRingedSpace).property
      ((Scheme.Modules.pullback i).obj N) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback i.toLRSHom.toShHom N
  exact (isAmple_iff_isAmple A (pullbackModule i N)).mpr
    (AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isIso i N
      ((isAmple_iff_isAmple B N).mp h))

/-- If `M` is ample relative to `q : Y ⟶ S` and `e : X ⟶ Y` is an isomorphism, then the pullback
of `M` is ample relative to `e ≫ q`. -/
theorem isRelativelyAmple_comp_of_isIso {X Y S : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (q : Y ⟶ S)
    (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (h : Stacks.RelativeAmple.IsRelativelyAmple q M) :
    Stacks.RelativeAmple.IsRelativelyAmple (e ≫ q) (pullbackModule e M) := by
  have : QuasiCompact q := h.quasiCompact
  refine ⟨inferInstance, fun V hV => ?_⟩
  have key := isAmple_pullbackModule_of_isIso (e ∣_ (q ⁻¹ᵁ V)) (pullbackModule (q ⁻¹ᵁ V).ι M)
    (h.2 V hV)
  change Stacks.Ample.IsAmple (e ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme
    (pullbackModule (e ⁻¹ᵁ (q ⁻¹ᵁ V)).ι (pullbackModule e M))
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mp key
  exact (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (e ∣_ (q ⁻¹ᵁ V)) (q ⁻¹ᵁ V).ι M).symm
    ≪≫ Stacks.RelativeAmpleBaseChange.pullbackModuleCongr (morphismRestrict_ι e (q ⁻¹ᵁ V)) M
    ≪≫ Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (e ⁻¹ᵁ (q ⁻¹ᵁ V)).ι e M

/-- The pullback of a relatively ample module along the projection of a cartesian square is
relatively ample. -/
private theorem isRelativelyAmple_pullbackModule_aux {X S X' S' : Scheme.{u}} {p : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback p f' f g) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f' (pullbackModule p L) := by
  have h0893 :=
    Stacks.RelativeAmpleBaseChange.isRelativelyAmple_modulePullback_unconditional f g L hL
  have htr := isRelativelyAmple_comp_of_isIso hsq.isoPullback.hom (pullback.snd f g)
    (pullbackModule (pullback.fst f g) L) h0893
  rw [hsq.isoPullback_hom_snd] at htr
  refine (Stacks.RelativeVeryAmple.isRelativelyAmple_congr f' _ _ ?_).mp htr
  exact (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso hsq.isoPullback.hom
      (pullback.fst f g) L).symm
    ≪≫ Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hsq.isoPullback_hom_fst L

/-- If `L` is ample relative to `f : X ⟶ S` and `X' ⟶ S'` is the base change of `f` along
`S' ⟶ S` in an arbitrary cartesian square, then the pullback of `L` to `X'` is ample relative to
it: `AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange` holds. -/
@[ega "II 4.6.13"]
theorem relativelyAmpleBaseChange :
    AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange.{u} := by
  intro X S X' S' p f' f g hsq L _ _ hL
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  have hLA : Stacks.RelativeAmple.IsRelativelyAmple f L :=
    (isRelativelyAmple_iff_isRelativelyAmple f L).mpr hL
  exact (isRelativelyAmple_iff_isRelativelyAmple f' (pullbackModule p L)).mp
    (isRelativelyAmple_pullbackModule_aux hsq L hLA)

/-- If `L` is ample relative to `f : X ⟶ S` and the square with sides `p : X' ⟶ X`,
`f' : X' ⟶ S'`, `f` and `g : S' ⟶ S` is cartesian, then the pullback of `L` along `p` is ample
relative to `f'`. -/
@[stacks 0893
 "for an arbitrary cartesian square"]
theorem isRelativelyAmple_pullbackModule_of_isPullback {X S X' S' : Scheme.{u}} {p : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback p f' f g) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f' (pullbackModule p L) := by
  exact isRelativelyAmple_pullbackModule_aux hsq L hL

end Stacks.AmpleBridge

end
