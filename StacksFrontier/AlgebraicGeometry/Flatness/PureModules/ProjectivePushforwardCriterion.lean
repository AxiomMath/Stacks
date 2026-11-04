module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocallyProjectivePurity
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.InternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# How purity is used: local projectivity of the direct image implies relative purity

Let `f : X ⟶ S` be an affine morphism of finite type and let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module. Stacks Tag 05MD asserts, for `f` of finite presentation and `ℱ` of
finite presentation and flat over `S`, that the direct image `f_*ℱ` is locally projective on `S`
if and only if `ℱ` is pure relative to `S`, and specializes this to a ring map `A → B` of finite
presentation and a finitely presented `B`-module `N` flat over `A`.

This file proves the implication from local projectivity of the direct image to relative purity,
in both the scheme and the ring form. That implication needs neither flatness nor finite
presentation: it is Tag 05K6 together with the observation that universal purity along a fibre
is by definition stronger than purity along it.

## Main results

* `AlgebraicGeometry.isPureRelative_of_isLocallyProjective_pushforward`: the scheme form.
* `AlgebraicGeometry.isPureRelative_tilde_of_projective`: the ring form.

## Implementation notes

The converse implication of Tag 05MD — that relative purity of a finitely presented, flat `ℱ`
makes `f_*ℱ` locally projective — is not proved here, because its proof consumes this file, which
it runs at an étale chart: it is `isLocallyProjective_pushforward_of_isPureRelative` in
`StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectivePushforwardConverse`, where the two
biconditionals of Tag 05MD are stated. Its argument runs through Tags 05KW, 05L4, 05KR, 05LW,
05DH, 059N and 059X, and descends the conclusion with Tag 05JZ.

## References

* [Stacks Project, Tag 05MD](https://stacks.math.columbia.edu/tag/05MD)
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05MD**, the implication from (1) to (2). For an affine morphism of
finite type, a finite type quasi-coherent module whose direct image is locally projective on the
base is pure relative to the base.

This implication of Tag 05MD assumes neither flatness over the base nor finite presentation,
which the statement of that tag assumes for the converse: it is Tag 05K6, whose conclusion is
universal purity relative to the base, followed by the fact that universal purity along a fibre
is purity along it with the étale and elementary hypotheses on the base change dropped. -/
@[stacks 05MD "the implication from local projectivity of the direct image to relative purity,
in the scheme form", sga "3 VIB 6.9" "6.9 a)"]
theorem isPureRelative_of_isLocallyProjective_pushforward
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward f).obj F)) :
    IsPureRelative f F :=
  fun s D _ _ => isUniversallyPureRelative_of_pushforward_isLocallyProjective f F hF s D

/-- The spectrum of a ring map of finite type is locally of finite type. This is the
`HasRingHomProperty` characterization of `LocallyOfFiniteType`, which is not itself registered as
an instance for a `Spec.map`, which the statement of the ring form below needs. -/
public instance specMap_algebraMap_locallyOfFiniteType (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **Stacks Project, Tag 05MD**, the ring specialization of the implication from (1) to (2).
Let `A → B` be a ring map of finite presentation and let `N` be a finitely presented
`B`-module. If `N` is projective as an `A`-module, then the sheaf `Ñ` on `Spec B` is pure
relative to `Spec A`.

As in the scheme form, flatness of `N` over `A` — which the statement of Tag 05MD assumes for
the converse — is not needed for this implication. The direct image of `Ñ` along
`Spec B ⟶ Spec A` is the sheaf associated to `N` viewed as an `A`-module, by Tag 01I9, so local
projectivity of the direct image is projectivity of that `A`-module by Tag 05JQ. -/
@[stacks 05MD "the implication from projectivity to relative purity, in the ring form of the
final assertion"]
theorem isPureRelative_tilde_of_projective
    (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Algebra.FinitePresentation A B] [Module.FinitePresentation B N]
    (hproj : Module.Projective A N) :
    IsPureRelative (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (tilde (ModuleCat.of (CommRingCat.of B) N)) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let M : ModuleCat.{u} (CommRingCat.of B) := ModuleCat.of (CommRingCat.of B) N
  let NA : ModuleCat.{u} (CommRingCat.of A) := (ModuleCat.restrictScalars φ.hom).obj M
  -- `N` with its `A`-action is `N` with the action restricted along `A → B`.
  have e : N ≃ₗ[A] NA :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r n =>
        (IsScalarTower.algebraMap_smul (A := B) (M := N) r n).symm }
  have hprojNA : Module.Projective (CommRingCat.of A) NA := Module.Projective.of_equiv e
  have hNA : Scheme.Modules.IsLocallyProjective (tilde NA) :=
    (isLocallyProjective_tilde_iff_projective (CommRingCat.of A) NA).2 hprojNA
  have hpush : Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) :=
    Scheme.Modules.isLocallyProjective_of_iso
      ((pushforwardTildeIso (CommRingCat.of A) (CommRingCat.of B) φ).app M).symm hNA
  exact isPureRelative_of_isLocallyProjective_pushforward (Spec.map φ) (tilde M) hpush

end AlgebraicGeometry

end
