module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Pieces
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback

/-!
# The pullback map on sections is bijective when the chart ideal annihilates

`Stacks.Conormal.pullbackSection_surjective` says that over a pair of affine opens on which the
map on functions surjects, every section of `f^*F` is a pullback, and
`Stacks.Conormal.pullbackSection_eq_zero_iff` identifies which sections pull back to zero: those
in `ker (f.appLE U V) · Γ(F, U)`. Putting the two together, if that submodule is zero — that is,
if the kernel **annihilates** `Γ(F, U)` — then

  `Γ(F, U) ⟶ Γ(f^*F, V)`,  `a ↦ pullbackSection f F U V a`

is a bijection, packaged here as an `AddEquiv`.

This is the situation of a closed immersion `i : Z ⟶ X` and a module killed by its ideal sheaf,
such as a graded piece `ℐⁿ/ℐⁿ⁺¹` of the `ℐ`-adic filtration, which is killed by `ℐ`. Over an
affine chart `V` of `X` the preimage `i⁻¹V` is affine, `Γ(X, V) ⟶ Γ(Z, i⁻¹V)` surjects with
kernel the chart ideal `Stacks.Conormal.chartIdeal i V`, and that ideal annihilates
`Γ(ℐⁿ/ℐⁿ⁺¹, V)`. So the sections of `i^*(ℐⁿ/ℐⁿ⁺¹)` over `i⁻¹V` are the sections of `ℐⁿ/ℐⁿ⁺¹`
over `V`.

## Main definitions

* `Stacks.Conormal.annihilatedPullbackSectionsEquiv`: the additive equivalence
  `Γ(F, U) ≃+ Γ(f^*F, f⁻¹U)`, **given by `Stacks.Conormal.pullbackSectionAddHom`**.

## Main results

* `Stacks.Conormal.bijective_pullbackSectionAddHom_of_smul_top_eq_bot`: **the pullback map on
  sections is bijective.**

## Implementation notes

The hypothesis is stated as `ker • ⊤ = ⊥`, the right-hand side of
`Stacks.Conormal.pullbackSection_eq_zero_iff`, rather than as a pointwise annihilation statement.

The equivalence is `Stacks.Conormal.pullbackSectionAddHom`, that is `pullbackSection` over the full
preimage as an additive map, rather than an abstract isomorphism of the two section modules, so
the `AlgebraicGeometry.Scheme.Modules.pullbackSection` API (`pullbackSection_naturality`,
`pullbackSection_comp`) applies to it.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.Conormal

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)

/-- **The pullback map on sections over the preimage of an affine open is bijective when the map
on functions surjects with annihilating kernel.** -/
theorem bijective_pullbackSectionAddHom_of_smul_top_eq_bot
    (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (hsurj : Function.Surjective (f.app U).hom)
    (hann : RingHom.ker (f.app U).hom • (⊤ : Submodule Γ(X, U) Γ(F, U)) = ⊥) :
    Function.Bijective (pullbackSectionAddHom f F U) := by
  have happ : f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U := Scheme.Hom.appLE_preimage_self f U
  have hsurj' : Function.Surjective (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom := by
    rwa [happ]
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_,
    pullbackSection_surjective f F le_rfl hU hV hsurj'⟩
  have hmem := (pullbackSection_eq_zero_iff f F le_rfl hU hV hsurj' a).1 ha
  rw [happ] at hmem
  exact (Submodule.eq_bot_iff _).1 hann a hmem

/-- **The sections of `f^*F` over the preimage of an affine open are the sections of `F`**, when
the map on functions surjects with annihilating kernel. The equivalence is
`Stacks.Conormal.pullbackSectionAddHom`. -/
noncomputable def annihilatedPullbackSectionsEquiv
    (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (hsurj : Function.Surjective (f.app U).hom)
    (hann : RingHom.ker (f.app U).hom • (⊤ : Submodule Γ(X, U) Γ(F, U)) = ⊥) :
    Γ(F, U) ≃+ Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U) :=
  AddEquiv.ofBijective (pullbackSectionAddHom f F U)
    (bijective_pullbackSectionAddHom_of_smul_top_eq_bot f F U hU hV hsurj hann)

/-- The equivalence `annihilatedPullbackSectionsEquiv` sends a section of `F` over `U` to its
pullback section of `f^*F` over `f ⁻¹ᵁ U`. -/
@[simp]
theorem annihilatedPullbackSectionsEquiv_apply
    (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (hsurj : Function.Surjective (f.app U).hom)
    (hann : RingHom.ker (f.app U).hom • (⊤ : Submodule Γ(X, U) Γ(F, U)) = ⊥)
    (a : Γ(F, U)) :
    annihilatedPullbackSectionsEquiv f F U hU hV hsurj hann a =
      Scheme.Modules.pullbackSection f F U (f ⁻¹ᵁ U) le_rfl a :=
  rfl

end Stacks.Conormal

end
