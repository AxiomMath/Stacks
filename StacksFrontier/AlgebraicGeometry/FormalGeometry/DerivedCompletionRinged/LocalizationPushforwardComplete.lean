module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Localization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.Relocalization

/-!
# Derived pushforward along a localization morphism preserves derived completeness

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals, `U` an object of `𝒞` and
`j : (Sh(𝒞/U), 𝒪_U) ⟶ (Sh(𝒞), 𝒪)` the localization morphism. If `E ∈ D(𝒪_U)` is derived
complete along the restriction `ℐ|_U`, then `Rj_* E` is derived complete along `ℐ`. This is
[Stacks, Tag 099J] for `j`, the step of the Remark [Stacks, Tag 0A0F] that produces the map
`b : K^∧ ⟶ Rj_*((K|_U)^∧)`.

## Main results

* `AlgebraicGeometry.RingedSite.localization_fSharp_ideal`: the structure map of `j` carries
  `j⁻¹ℐ` into `ℐ|_U`.
* `AlgebraicGeometry.RingedSite.localizationDerivedPushforward_isDerivedComplete`: `Rj_*` sends
  `D_comp(𝒪_U, ℐ|_U)` into `D_comp(𝒪, ℐ)`.

## Implementation notes

The inverse image of `j` is restriction along `𝒞/U ⥤ 𝒞`, and its structure map is the identity
on underlying sheaves of sets (`forgetRing_localizationRingedToposHom_fSharpInverseImage`). The
restriction `ℐ|_U` (`overIdeal`) has, over `V ⟶ U`, the sections of `ℐ` over `V`; so `j⁻¹ℐ` and
`ℐ|_U` have the same underlying sheaf of sets and the inclusions agree, which is the hypothesis
of `AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete`.

## References

* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (U : X.C)

/-- The structure map of the localization morphism `j` at `U` carries `j⁻¹ℐ` into the
restriction `ℐ|_U`: the composite of the inverse image of `ℐ ⊂ 𝒪` with the inverse-image form
of `j^♯` factors through `ℐ|_U ⊂ 𝒪_U`. -/
theorem localization_fSharp_ideal :
    ∃ φ : (X.localizationRingedToposHom U).toToposHom.inverseImage.obj
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).toRingedSite.O))).obj
          I.toSheafOfModules) ⟶
        (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (X.over U)).toRingedSite.O))).obj
          (overIdeal I U).toSheafOfModules,
      (X.localizationRingedToposHom U).toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).toRingedSite.O))).map
            I.ι) ≫
        (ringedTopos (X.over U)).forgetRing.map
          (X.localizationRingedToposHom U).fSharpInverseImage =
      φ ≫ (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (X.over U)).toRingedSite.O))).map
          (overIdeal I U).ι := by
  refine ⟨𝟙 _, ?_⟩
  rw [X.forgetRing_localizationRingedToposHom_fSharpInverseImage U]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **[Stacks, Tag 099J] for the localization morphism.** Let `(𝒞, 𝒪)` be a ringed site,
`ℐ ⊂ 𝒪` a sheaf of ideals, `U` an object of `𝒞` and `j : (Sh(𝒞/U), 𝒪_U) ⟶ (Sh(𝒞), 𝒪)` the
localization morphism. If `E ∈ D(𝒪_U)` is derived complete along `ℐ|_U`, then `Rj_* E` is
derived complete along `ℐ`. -/
theorem localizationDerivedPushforward_isDerivedComplete
    (K : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))))
    (hK : IsDerivedComplete.{u, u, u, u} (X.over U) (overIdeal I U) K) :
    IsDerivedComplete.{u, u, u, u} X I
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u}
        (X.localizationRingedToposHom U)).obj K) :=
  RingedToposHom.derivedPushforward_isDerivedComplete (X.localizationRingedToposHom U) I
    (overIdeal I U) (localization_fSharp_ideal X I U) K hK

end AlgebraicGeometry.RingedSite

end
