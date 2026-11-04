module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleTwistExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseObjectNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyOverBaseFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCohomologyUniformVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerDevissage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additivity of the Euler characteristic on a proper algebraic space over a field

Let `k` be a field and `X` a proper algebraic space over `k`.  For a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of coherent `𝒪_X`-modules,

`χ(X, F₂) = χ(X, F₁) + χ(X, F₃)`.

This is Stacks 0DN2, proved as
`AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_outer`: the long exact sequence
of cohomology followed by rank-nullity, with the two facts that make `χ` a finite alternating sum
of finite dimensions, namely that the cohomology of a coherent module is finite dimensional
(Stacks 08AS, `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent`)
and vanishes beyond a degree independent of the module (Stacks 072C,
`AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBase_of_isCoherent_of_qcqs`).

Twisting by integer powers of invertible modules is exact
(`AlgebraicGeometry.Space.shortExact_map_twistedModuleUliftExactFunctor`), so the twisted Euler
characteristics are additive too; that is the form in which the proof of Stacks 0DN4 uses the
tag.

## Main results

* `AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_isProper`: **Stacks 0DN2**,
  under the name used by the twisted form below; it is
  `AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_outer`.
* `AlgebraicGeometry.Space.hasAdditiveTwistedEulerOnCoherent_of_isProper`: the twisted Euler
  characteristics are additive along short exact sequences of coherent modules.

## References

* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- **Stacks 0DN2.**  Let `k` be a field, `X` a proper algebraic space over `k` and
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact sequence of coherent `𝒪_X`-modules.  Then
`χ(X, F₂) = χ(X, F₁) + χ(X, F₃)`.

This is `AlgebraicGeometry.Space.eulerCharacteristic_add_of_shortExact_of_outer`: the long exact
sequence of cohomology and rank-nullity, with the finiteness of Stacks 08AS and the uniform
vanishing of Stacks 072C, for `X` quasi-compact and quasi-separated, being proper over
`Spec k`. -/
@[stacks 0DN2]
theorem eulerCharacteristic_add_of_shortExact_of_isProper
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    {S : ShortComplex (Modules.{u, max (u + 1) w} B (Spec (.of k)) hk X hX)} (hS : S.ShortExact)
    [IsCoherent B (Spec (.of k)) hk X hX S.X₁] [IsCoherent B (Spec (.of k)) hk X hX S.X₂]
    [IsCoherent B (Spec (.of k)) hk X hX S.X₃] :
    eulerCharacteristic.{u, w} k B hk X hX f hf S.X₂ =
      eulerCharacteristic.{u, w} k B hk X hX f hf S.X₁ +
        eulerCharacteristic.{u, w} k B hk X hX f hf S.X₃ :=
  eulerCharacteristic_add_of_shortExact_of_outer.{u, w} k B hk X hX f hf hS

/-- **The twisted Euler characteristics are additive along short exact sequences of coherent
modules.**  For `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` short exact with coherent terms on a proper algebraic
space over a field and invertible `L₁, …, L_r`,
`χ(X, F₂ ⊗ L^{⊗ n}) = χ(X, F₁ ⊗ L^{⊗ n}) + χ(X, F₃ ⊗ L^{⊗ n})` for every integral tuple `n`:
twisting followed by the universe lift is exact
(`AlgebraicGeometry.Space.shortExact_map_twistedModuleUliftExactFunctor`), and Stacks 0DN2
applies to the twisted sequence. -/
@[ega "III 2.5.2" "special case"]
theorem hasAdditiveTwistedEulerOnCoherent_of_isProper (X : AlgebraicSpaces B (Spec (.of k)) hk)
    {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)] :
    HasAdditiveTwistedEulerOnCoherent.{u, w} k B hk X f hf L := by
  intro E hE h₁ h₂ h₃ n
  let T := twistedModuleUliftExactFunctor.{u, w} B (Spec (.of k)) hk X.1 X.2 L n
  have hE' := shortExact_map_twistedModuleUliftExactFunctor.{u, w} B (Spec (.of k)) hk X.1 X.2 L n
    hE
  have e : ∀ M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2,
      T.obj M ≅ twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n := fun M =>
    eqToIso (twistedModuleUliftExactFunctor_obj.{u, w} B (Spec (.of k)) hk X.1 X.2 L n M)
  have c : ∀ (M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
      [IsCoherent B (Spec (.of k)) hk X.1 X.2 M],
      IsCoherent B (Spec (.of k)) hk X.1 X.2 (T.obj M) :=
    fun M hM => isCoherent_of_iso B (Spec (.of k)) hk X.2 (e M).symm
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L M hM n)
  have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L E.X₁ h₁ n
  have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L E.X₂ h₂ n
  have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L E.X₃ h₃ n
  dsimp only [ShortComplex.map] at hE'
  have key := eulerCharacteristic_add_of_shortExact_of_isProper.{u, w} k B hk X.1 X.2 f hf hE'
  rw [eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf (e E.X₁),
    eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf (e E.X₂),
    eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf (e E.X₃)] at key
  exact key

end AlgebraicGeometry.Space

end
