module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalSelfMapIso
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftTorsor

/-!
# The translation action on the global lifts of a morphism of schemes, named

Let `f : X ⟶ Y` be a morphism of schemes over the residue field `k`, let `P` be a deformation of
`X` and `Q` a deformation of `Y`, and let `ℓ₀ : P.scheme ⟶ Q.scheme` be a lift of `f` over the
base in the sense of `Deformation.Examples.globalLiftsOverBase`. [Stacks Project, Tag 0CK2]
makes the derivations act simply transitively on those lifts.

The library already has that statement, as
`Deformation.Examples.exists_simplyTransitive_addAction_globalLiftsOverBase`, but **as an
existential over the acting function**: it produces a function with the torsor axioms rather
than naming one. This file names the action. The point is that "the derivation carrying `ℓ₀`
where something else carries it" is then a *term*, which is what the arrow `b` of
[Stacks Project, Tag 0E3V] and the exactness statements at the interior spots of the source's
sequence need.

Naming it costs nothing, because the thickening level already has an honest bijection:
`Stacks.Thickenings.derivationActionGlobalEquivOfBase` identifies the derivations with the
morphisms `P.scheme ⟶ Q.scheme` over the base restricting to `f` along the special-fibre
immersion, and **that subtype is `Deformation.Examples.globalLiftsOverBase` itself** — the two
conditions are the same two, in the same order. So the bijection, read at the data of the
dictionary in `StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftTorsor.lean`, is
already a bijection onto the global lifts; the translation action is the addition of the
derivations transported along it.

## Main definitions

* `Deformation.Examples.globalLiftsOverBaseDerivationEquiv`: **the derivations are the global
  lifts**, based at `ℓ₀`.
* `Deformation.Examples.globalLiftsOverBaseVAdd`: **the named translation action** of the
  derivations on the global lifts.

## Main results

* `Deformation.Examples.globalLiftsOverBaseDerivationEquiv_zero`: the bijection takes the zero
  derivation to the base lift, so it is based at `ℓ₀`.
* `Deformation.Examples.globalLiftsOverBaseVAdd_zero` and
  `Deformation.Examples.globalLiftsOverBaseVAdd_add`: the two action laws.
* `Deformation.Examples.globalLiftsOverBaseVAdd_base`: the action of a derivation on the base
  lift is its image under the bijection.
* `Deformation.Examples.existsUnique_globalLiftsOverBaseVAdd`: **simple transitivity based at
  `ℓ₀`**, which is the hypothesis `htrans` of
  `Deformation.exact_triple_of_simplyTransitive`.

## Implementation notes

That the bijection is based at `ℓ₀` is `Stacks.Thickenings.derivationActionGlobal_zero`, the
statement that the zero derivation does not move the lift. It is the one fact that makes the
transported addition an action *with `ℓ₀` in the orbit of `0`*, and so the one fact that makes
the simple transitivity statement here the one the torsor lemmas consume.

The action is `θ ⬝ ℓ = E (θ + E⁻¹ ℓ)` rather than a construction on lifts. Nothing is lost: the
existential statement
`Deformation.Examples.exists_simplyTransitive_addAction_globalLiftsOverBase` pins its action
only up to the torsor axioms, and that is genuinely weaker than determining it. Composing a
simply transitive action with any automorphism `σ` of the acting group gives another simply
transitive action, and the two still agree at the basing lift, because `σ 0 = 0`; so agreeing at
one point does *not* force two simply transitive actions to agree. They differ by a group
automorphism, not by nothing. What ties this definition to the action of
[Stacks Project, Tag 0CK2] is therefore not a uniqueness argument but that it is *supplied as
the witness* of the existential: see
`Deformation.Examples.exists_simplyTransitive_addAction_derivations_globalLiftsOverBase`, which
is proved from `Deformation.Examples.schemeMorphismLiftsVAdd`.

The acting group is left as the group `Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/P.scheme})` of maps of sheaves
of modules, not carried onto the derivations `Der_k(𝒪_Y, f_*N)`: the identification
`Deformation.Examples.schemeMorphismDerivationsEquivHom` needs a trivialisation of the conormal
sheaf, which nothing here does, and it is an isomorphism of additive groups, so a caller that
wants the third term of the source's sequence as the acting group may transport along it.

## References

* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

section NamedTorsor

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)

/-! ### The derivations are the global lifts -/

/-- **[Stacks Project, Tag 0CK2] for the global lifts of `f`, as an honest bijection based at a
lift.** The group `Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/P.scheme})` is in bijection with the morphisms
`P.scheme ⟶ Q.scheme` over `baseSpec Q.base` restricting to `f` on the special fibre, by
`θ ↦ θ ⬝ ℓ₀`.

This is `Stacks.Thickenings.derivationActionGlobalEquivOfBase` at the data of the dictionary of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftTorsor.lean`; its codomain is
`Deformation.Examples.globalLiftsOverBase` with no transport, the two conditions on a lift being
literally the same two. -/
def globalLiftsOverBaseDerivationEquiv (ℓ₀ : globalLiftsOverBase f P Q e) :
    (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules P.specialMap) ≃ globalLiftsOverBase f P Q e :=
  Stacks.Thickenings.derivationActionGlobalEquivOfBase (ker_specialMap_pow_two_eq_bot P hm)
    Q.specialCartesian (specialMap_comp_deformationAmbientToBase (X := Over.mk pX)
      (Y := Over.mk pY) f hf P e) ℓ₀.2.2 ℓ₀.2.1

/-- The bijection is the modified-lift construction of [Stacks Project, Tag 0CK1], read through
the comparison of the differentials relative to `Spec k` and relative to `baseSpec Q.base`. -/
theorem globalLiftsOverBaseDerivationEquiv_val (ℓ₀ : globalLiftsOverBase f P Q e)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P.specialMap) :
    (globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀ θ).1 =
      Stacks.Thickenings.derivationActionGlobal (ker_specialMap_pow_two_eq_bot P hm)
        ((Stacks.Thickenings.pullbackCotangentSheafIsoOfBase Q.specialCartesian f).hom ≫ θ)
        ℓ₀.2.2 :=
  Stacks.Thickenings.derivationActionGlobalEquivOfBase_apply _ _ _ _ _ θ

/-- **The bijection is based at the lift it is built from**: the zero derivation goes to `ℓ₀`.
This is `Stacks.Thickenings.derivationActionGlobal_zero`, and it is what makes the transported
addition an action whose orbit of `0` is `ℓ₀`. -/
theorem globalLiftsOverBaseDerivationEquiv_zero (ℓ₀ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀ 0 = ℓ₀ := by
  refine Subtype.ext ?_
  rw [globalLiftsOverBaseDerivationEquiv_val, comp_zero]
  exact Stacks.Thickenings.derivationActionGlobal_zero (ker_specialMap_pow_two_eq_bot P hm)
    ℓ₀.1 ℓ₀.2.2

/-- The inverse bijection takes the base lift to the zero derivation. -/
theorem globalLiftsOverBaseDerivationEquiv_symm_base (ℓ₀ : globalLiftsOverBase f P Q e) :
    (globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).symm ℓ₀ = 0 :=
  (globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).injective
    ((globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).apply_symm_apply ℓ₀|>.trans
      (globalLiftsOverBaseDerivationEquiv_zero f pX pY hf hm ℓ₀).symm)

/-! ### The named action -/

/-- **The named translation action of [Stacks Project, Tag 0CK2] on the global lifts of `f`**:
the addition of the acting group, transported along
`Deformation.Examples.globalLiftsOverBaseDerivationEquiv`.

`Deformation.Examples.exists_simplyTransitive_addAction_globalLiftsOverBase` produces an action
with the torsor axioms but names none; this is a name for it. The two laws are
`Deformation.Examples.globalLiftsOverBaseVAdd_zero` and
`Deformation.Examples.globalLiftsOverBaseVAdd_add`, and simple transitivity based at `ℓ₀` is
`Deformation.Examples.existsUnique_globalLiftsOverBaseVAdd`. -/
def globalLiftsOverBaseVAdd (ℓ₀ : globalLiftsOverBase f P Q e)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P.specialMap)
    (ℓ : globalLiftsOverBase f P Q e) : globalLiftsOverBase f P Q e :=
  globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀
    (θ + (globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).symm ℓ)

/-- **The zero derivation acts trivially.** -/
theorem globalLiftsOverBaseVAdd_zero (ℓ₀ ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ 0 ℓ = ℓ := by
  rw [globalLiftsOverBaseVAdd, zero_add]
  exact (globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).apply_symm_apply ℓ

/-- **The action law**: translating by `θ + η` is translating by `η` and then by `θ`. -/
theorem globalLiftsOverBaseVAdd_add (ℓ₀ : globalLiftsOverBase f P Q e)
    (θ η : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P.specialMap)
    (ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ (θ + η) ℓ =
      globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ
        (globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ η ℓ) := by
  rw [globalLiftsOverBaseVAdd, globalLiftsOverBaseVAdd, globalLiftsOverBaseVAdd,
    Equiv.symm_apply_apply, add_assoc]

/-- **The action on the base lift is the bijection.** This is what makes the named action the
torsor structure based at `ℓ₀`. -/
theorem globalLiftsOverBaseVAdd_base (ℓ₀ : globalLiftsOverBase f P Q e)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P.specialMap) :
    globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ₀ =
      globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀ θ := by
  rw [globalLiftsOverBaseVAdd, globalLiftsOverBaseDerivationEquiv_symm_base, add_zero]

/-- **Simple transitivity of the named action, based at `ℓ₀`.** Every global lift of `f` is the
translate of `ℓ₀` by exactly one derivation. This is the hypothesis `htrans` of
`Deformation.exact_triple_of_simplyTransitive`. -/
theorem existsUnique_globalLiftsOverBaseVAdd (ℓ₀ ℓ : globalLiftsOverBase f P Q e) :
    ∃! θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules P.specialMap,
      globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ₀ = ℓ := by
  refine ⟨(globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).symm ℓ, ?_, fun η hη => ?_⟩
  · simp only [globalLiftsOverBaseVAdd_base]
    exact (globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).apply_symm_apply ℓ
  · simp only [globalLiftsOverBaseVAdd_base] at hη
    rw [← hη, Equiv.symm_apply_apply]

end NamedTorsor

end Deformation.Examples

end
