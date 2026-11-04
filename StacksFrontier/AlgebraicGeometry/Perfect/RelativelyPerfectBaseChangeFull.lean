module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.InverseImageTorAmplitudeStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionNestedRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTorDimensionLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# Base change of relative perfectness

Let `f : X ⟶ S` be flat and locally of finite presentation, let `g : S' ⟶ S` be arbitrary, and
let `X'` with `g' : X' ⟶ X` and `f' : X' ⟶ S'` be the base change. If `K` in `D(𝒪_X)` is
`S`-perfect, then `L(g')^*K` is `S'`-perfect (Stacks 0DI5).

Pseudo-coherence is preserved by any derived pullback. For the Tor clause, let `U ⊆ X` be an
affine open. On `U` the complex `K` has Tor amplitude in some `[a, b]` over `S`, read stalkwise.
The square formed by `g'⁻¹(U) ⟶ U` and `S' ⟶ S` is cartesian, and `f` is flat, so the two maps to
`S` are Tor independent. Stacks 0C0V then bounds the Tor amplitude of `L(g'|_U)^*(K|_U)` over
`S'` by the same `[a, b]`. The opens `g'⁻¹(U)` cover `X'`, which gives locally finite Tor dimension
of `L(g')^*K` over `f'⁻¹𝒪_{S'}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_derivedPullback`: Stacks 0DI5.

## Implementation notes

Relative perfectness is read at the canonical family of derived tensor products of Stacks 06YU
on the open subspaces of the inverse-image ringed space. At an arbitrary family of certificates
the statement is false; see `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange`.

## References

* [Stacks Project, Lemma 36.35.6 (Tag 0DI5)](https://stacks.math.columbia.edu/tag/0DI5)
* [Stacks Project, Lemma 36.22.8 (Tag 0C0V)](https://stacks.math.columbia.edu/tag/0C0V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')

variable {f g g' f'}

/-- **The Tor clause of Stacks 0DI5 over an open of the source.** If `K|_U` has Tor amplitude in
`[a, b]` over `S`, then `L(g')^*K` restricted to `g'⁻¹(U)` has Tor amplitude in `[a, b]` over
`S'`. -/
theorem hasTorAmplitudeOver_restrict_derivedPullback [Flat f] (hpb : IsPullback g' f' f g)
    (U : X.Opens) (K : DerivedCategory X.Modules) (a b : ℤ)
    (hK : HasTorAmplitudeOver (U.ι ≫ f)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) a b) :
    HasTorAmplitudeOver ((g' ⁻¹ᵁ U).ι ≫ f')
      ((Scheme.Modules.restrictFunctor (g' ⁻¹ᵁ U).ι).mapDerivedCategory.obj
        ((derivedPullback g'.toLRSHom.toShHom).obj K)) a b := by
  have hsq : IsPullback (g' ∣_ U) ((g' ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) g :=
    (isPullback_morphismRestrict g' U).paste_vert hpb
  have htor : TorIndependent (U.ι ≫ f) g := torIndependent_of_flat _ _
  exact hasTorAmplitudeOver_of_iso
    (Scheme.Modules.openRestrictionDerivedPullbackIso (g' ⁻¹ᵁ U).ι g' U.ι (g' ∣_ U)
      (morphismRestrict_ι g' U).symm K).symm a b
    (derivedPullback_hasTorAmplitudeOver _ _ _ _ hsq htor _ a b hK)

/-- **Stacks 0DI5.** Let `f : X ⟶ S` be flat and locally of finite presentation, `g : S' ⟶ S` a
morphism of schemes, and `X'` with `g' : X' ⟶ X`, `f' : X' ⟶ S'` the base change of `f` along `g`.
If `K` in `D(𝒪_X)` is `S`-perfect, then `L(g')^*K` is `S'`-perfect.

Relative perfectness is read at the derived tensor product of Stacks 06YU on the open subspaces
of the inverse-image ringed spaces. -/
@[stacks 0DI5]
theorem isPerfectRelativeTo_derivedPullback [Flat f] [LocallyOfFinitePresentation f]
    (hpb : IsPullback g' f' f g) (K : DerivedCategory X.Modules)
    (hK : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) K) :
    haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb (inferInstance : Flat f)
    haveI : LocallyOfFinitePresentation f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb
        (inferInstance : LocallyOfFinitePresentation f)
    f'.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S'.toRingedSpace f'.base))
      ((derivedPullback g'.toLRSHom.toShHom).obj K) := by
  have : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
  refine ⟨isPseudoCoherent_derivedPullback_of_isPerfectRelativeTo f g g' f' hpb _ K hK, ?_⟩
  refine locallyHasFiniteTorDimension_of_isOpenCover f' _ _ X.affineOpens
    (fun U => g' ⁻¹ᵁ (U : X.Opens)) ?_ fun U => ?_
  · refine top_unique fun x _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g'.base x)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · have hU := chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension f K hK.2
      (U : X.Opens) U.2
    have e₁ : (U : X.Opens) ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have e₂ : g' ⁻¹ᵁ (U : X.Opens) ≤ f' ⁻¹ᵁ ⊤ := fun _ _ => trivial
    obtain ⟨a, b, hab⟩ := (chartTorSpellingsAgree f K ⊤ U e₁).1 hU
    have hab' := (hasTorAmplitudeOver_comp_iff_of_isOpenImmersion _ (⊤ : S.Opens).ι _ a b).2 hab
    rw [Scheme.Hom.resLE_comp_ι] at hab'
    refine (chartTorSpellingsAgree f' _ ⊤ (g' ⁻¹ᵁ (U : X.Opens)) e₂).2 ⟨a, b, ?_⟩
    refine (hasTorAmplitudeOver_comp_iff_of_isOpenImmersion _ (⊤ : S'.Opens).ι _ a b).1 ?_
    rw [Scheme.Hom.resLE_comp_ι]
    exact hasTorAmplitudeOver_restrict_derivedPullback hpb _ K a b hab'

end AlgebraicGeometry.Scheme.Hom

end
