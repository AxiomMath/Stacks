module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.OneDimensionalLocal
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Flat pullback detects vanishing of stalks

Let `g : S' ⟶ S` be a flat morphism of schemes and let `M` be a sheaf of `𝒪_S`-modules. Then
`g^* M` vanishes exactly when every stalk of `M` at a point of the image of `g` vanishes.

The forward implication is the only one that needs flatness, and it is [Stacks, Tag 0098]
together with faithful flatness of a flat local homomorphism: by Tag 0098 the stalk of `g^* M`
at `z` is `𝒪_{S', z} ⊗_{𝒪_{S, g z}} M_{g z}`, the stalk map
`𝒪_{S, g z} ⟶ 𝒪_{S', z}` is a flat local homomorphism of local rings, hence faithfully flat,
and a faithfully flat extension of scalars reflects triviality.

This generalizes `Stacks.AlgebraicGeometry.OneDimensionalLocal.pullbackFromSpecStalkDetectsStalk`
(`StacksFrontier/AlgebraicGeometry/OneDimensionalLocal/PullbackStalk.lean`), which is the case
`g = X.fromSpecStalk x` at the closed point: there the stalk map is an *isomorphism* and the
tensor product collapses, whereas here flatness alone suffices.

`Stacks.AlgebraicGeometry.OneDimensionalLocal.FlatBaseChangeVanishing` — the vanishing half of
[Stacks, Tag 02KH] part (1) — asks, for a cartesian square with `g` flat and `f` quasi-compact
and quasi-separated, that vanishing of `R ⁿ f'_* (g')^* 𝓖` force vanishing of `g^* R ⁿ f_* 𝓖`.
By `isZero_pullback_iff_forall_isZero_stalk` its conclusion is equivalent to vanishing of the
stalks of `R ⁿ f_* 𝓖` along the image of `g`. When `f` is affine that conclusion holds in
positive degrees with no hypothesis, because `R ⁿ f_* 𝓖` already vanishes by
[Stacks, Tag 01XC].

## Main results

* `Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_stalk_of_isZero_pullback`: if `g` is flat
  and `g^* M` vanishes, then `M` has vanishing stalk at every point of the image of `g`.
* `Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_pullback_of_forall_isZero_stalk`: the
  converse, which needs no flatness.
* `Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_pullback_iff_forall_isZero_stalk`: the two
  together.
* `Stacks.AlgebraicGeometry.FlatPullbackStalk`'s
  `isZero_pullback_rightDerived_pushforward_of_isAffineHom`: for an affine morphism `f` and a
  quasi-coherent `𝓖`, every pullback of `R ⁿ f_* 𝓖` vanishes in positive degrees.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.FlatPullbackStalk

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (M : S.Modules)

/-! ### Flat pullback detects stalks -/

/-- The stalk of `g^* M` at `z` vanishes iff the extension of scalars `𝒪_{S', z} ⊗ M_{g z}`
does, by [Stacks, Tag 0098]. -/
private theorem isZero_stalk_pullback_iff_subsingleton_tensorProduct (z : S') :
    letI : Algebra (S.presheaf.stalk (g.base z)) (S'.presheaf.stalk z) :=
      (g.stalkMap z).hom.toAlgebra
    letI : Module (S.presheaf.stalk (g.base z))
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (g.base z)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S.presheaf) M.val (g.base z)
    IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} z).obj
      ((Scheme.Modules.toPresheaf S').obj ((Scheme.Modules.pullback g).obj M))) ↔
      Subsingleton (TensorProduct (S.presheaf.stalk (g.base z)) (S'.presheaf.stalk z)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (g.base z))) := by
  obtain ⟨e, -⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      g.toLRSHom.toShHom M z
  exact AddCommGrpCat.isZero_iff_subsingleton.trans e.toEquiv.subsingleton_congr

/-- **Flat pullback reflects vanishing of stalks.** If `g : S' ⟶ S` is flat and `g^* M`
vanishes, then the stalk of `M` at `g z` vanishes for every `z : S'`.

By [Stacks, Tag 0098] the stalk of `g^* M` at `z` is `𝒪_{S', z} ⊗_{𝒪_{S, g z}} M_{g z}`. The
stalk map `𝒪_{S, g z} ⟶ 𝒪_{S', z}` is a local homomorphism of local rings and is flat because
`g` is, so it is faithfully flat, and therefore triviality of the tensor product forces
triviality of `M_{g z}`. -/
theorem isZero_stalk_of_isZero_pullback [Flat g] (z : S')
    (hM : IsZero ((Scheme.Modules.pullback g).obj M)) :
    IsZero (M.presheaf.stalk (g.base z)) := by
  let A := S.presheaf.stalk (g.base z)
  let B := S'.presheaf.stalk z
  let : Algebra A B := (g.stalkMap z).hom.toAlgebra
  let Mstalk := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (g.base z)
  let : Module A Mstalk :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.presheaf) M.val (g.base z)
  have hflat : Module.Flat A B := Flat.stalkMap g z
  have hloc : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (g.stalkMap z).hom)
  have hff : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Subsingleton Mstalk :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B).mp
      ((isZero_stalk_pullback_iff_subsingleton_tensorProduct g M z).mp
        ((TopCat.Presheaf.stalkFunctor Ab.{u} z).map_isZero
          ((Scheme.Modules.toPresheaf S').map_isZero hM)))
  exact AddCommGrpCat.isZero_of_subsingleton Mstalk

/-- **A pullback vanishes as soon as the stalks along the image vanish.** No flatness is
needed: by [Stacks, Tag 0098] the stalk of `g^* M` at `z` is an extension of scalars of
`M_{g z}`, which is trivial as soon as `M_{g z}` is. -/
theorem isZero_pullback_of_forall_isZero_stalk
    (h : ∀ z : S', IsZero (M.presheaf.stalk (g.base z))) :
    IsZero ((Scheme.Modules.pullback g).obj M) := by
  refine isZero_of_forall_isZero_stalk _ fun z ↦ ?_
  let A := S.presheaf.stalk (g.base z)
  let B := S'.presheaf.stalk z
  let : Algebra A B := (g.stalkMap z).hom.toAlgebra
  let Mstalk := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (g.base z)
  let : Module A Mstalk :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.presheaf) M.val (g.base z)
  have : Subsingleton Mstalk := AddCommGrpCat.isZero_iff_subsingleton.mp (h z)
  exact (isZero_stalk_pullback_iff_subsingleton_tensorProduct g M z).mpr
    (inferInstanceAs (Subsingleton (TensorProduct A B Mstalk)))

/-- **Vanishing of a flat pullback is vanishing of the stalks along the image.** This is the
stalk-level form of the conclusion of the vanishing half of [Stacks, Tag 02KH] part (1). -/
theorem isZero_pullback_iff_forall_isZero_stalk [Flat g] :
    IsZero ((Scheme.Modules.pullback g).obj M) ↔
      ∀ z : S', IsZero (M.presheaf.stalk (g.base z)) :=
  ⟨fun hM z ↦ isZero_stalk_of_isZero_pullback g M z hM,
    isZero_pullback_of_forall_isZero_stalk g M⟩

/-! ### The affine case of flat base change in positive degrees -/

/-- **The affine case of the vanishing half of [Stacks, Tag 02KH] part (1) in positive
degrees, with no base-change hypothesis at all.** If `f : T ⟶ S` is an affine morphism and `𝓖`
is a quasi-coherent `𝒪_T`-module, then `R ⁿ f_* 𝓖` already vanishes for `n > 0` by
[Stacks, Tag 01XC], so every pullback of it vanishes. -/
theorem isZero_pullback_rightDerived_pushforward_of_isAffineHom
    {T : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f] (G : T.Modules) (hG : G.IsQuasicoherent)
    (n : ℕ) (hn : 0 < n) :
    IsZero ((Scheme.Modules.pullback g).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj G)) :=
  (Scheme.Modules.pullback g).map_isZero
    (OneDimensionalLocal.higherDirectImageVanishingAffine f G inferInstance hG n hn)

end Stacks.AlgebraicGeometry.FlatPullbackStalk

end
