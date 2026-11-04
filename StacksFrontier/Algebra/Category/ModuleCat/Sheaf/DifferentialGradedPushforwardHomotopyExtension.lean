module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction

/-!
# The direct image of a homotopy, for the constructed direct image

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforwardHom.lean` carries the
direct image of a homotopy as the datum
`SheafOfModules.DifferentialGradedModule.PushforwardData.HomotopyExtension`, because the
universal property of a direct image speaks only of morphisms of differential graded modules,
that is of maps of degree zero, and says nothing about the degree `-1` maps a homotopy is made
of.

For the *constructed* direct image it is a theorem. The direct image of right differential
graded modules is restriction of sections along the functor of sites with scalars restricted
along the structure map, so it is additive and degreewise, and
`SheafOfModules.DifferentialGradedModule.pushforwardHomotopy` already produces the direct image
of a homotopy. All that is added here is that the direct image of a morphism in the sense of the
universal property is the constructed one, which turns that homotopy into the missing datum.

## Main results

* `SheafOfModules.DifferentialGradedModule.pushforwardData_map`: the direct image of a morphism
  given by the universal property is the constructed direct image of that morphism.
* `SheafOfModules.DifferentialGradedModule.pushforwardHomotopyExtension`: **the direct image of
  a homotopy**, that is the `PushforwardData.HomotopyExtension` of the constructed direct image.
* `SheafOfModules.DifferentialGradedModule.exists_homotopyPushforwardSheafHom`: a
  homotopy-preserving functor of modules followed by the constructed direct image descends
  uniquely to the homotopy categories. The functor of
  [Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS) itself, with its exactness, is
  `SheafOfModules.DifferentialGradedModule.exists_isTriangulated_homotopyPushforwardSheafHom`
  in `DifferentialGradedPushforwardSheafHomExact.lean`.

## References

* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
* [Stacks Project, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS)
-/

@[expose] public section

open CategoryTheory

universe t a a' m s z v u v' u'

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}

/-- **The direct image of a morphism given by the universal property is the constructed direct
image of that morphism.** -/
theorem pushforwardData_map (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A)
    {M M₂ : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ M₂) :
    (pushforwardData.{t, a, a', m} φ).map g = pushforwardMap φ g :=
  rfl

/-- **The direct image of a homotopy along a morphism of ringed sites.** This is the extra datum
that `DifferentialGradedPushforwardHom.lean` carries as
`SheafOfModules.DifferentialGradedModule.PushforwardData.HomotopyExtension`; for the constructed
direct image it is a theorem, the direct image being additive and degreewise. -/
noncomputable def pushforwardHomotopyExtension
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A) :
    (pushforwardData.{t, a, a', m} φ).HomotopyExtension where
  mapHomotopy {_M _M₂ ψ χ} h :=
    (pushforwardHomotopy φ h).ofDiffEq fun _ => by
      rw [pushforwardData_map φ ψ, pushforwardData_map φ χ]

/-- **The constructed direct image carries homotopic morphisms to homotopic morphisms**, as a
direct image datum. -/
theorem preservesHomotopic_pushforwardData
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A) :
    PreservesHomotopic (pushforwardData.{t, a, a', m} φ).functor :=
  (pushforwardHomotopyExtension φ).preservesHomotopic

/-! ### Descending a composite with the direct image -/

section PushforwardSheafHom

variable {A' : DifferentialGradedAlgebra.{t, a} R}

/-- For a morphism of ringed sites `f`, a sheaf of differential graded algebras `𝒜` on its
source, a sheaf of differential graded algebras `ℬ` on its target, a homomorphism
`φ : ℬ ⟶ f_*𝒜` and a functor `S` of right differential graded modules from a second sheaf of
differential graded algebras `𝒜'` on the source to `𝒜` which carries homotopic morphisms to
homotopic morphisms, there is a unique functor

`K(Mod(𝒜', d)) ⟶ K(Mod(ℬ, d))`

on the homotopy categories factoring `S` followed by the direct image through the two quotient
functors. At `S` the internal hom of a differential graded `(𝒜, 𝒜')`-bimodule this is the
functor of [Stacks, Tag 0FTS], whose exactness is
`SheafOfModules.DifferentialGradedModule.exists_isTriangulated_homotopyPushforwardSheafHom`. -/
theorem exists_homotopyPushforwardSheafHom
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A)
    (S : DifferentialGradedModule.{t, a, s} A' ⥤ DifferentialGradedModule.{t, a, m} A)
    (hS : PreservesHomotopic S) :
    ∃! Φ : HomotopyCategory.{t, a, s} A' ⥤ HomotopyCategory.{t, a', m} B,
      HomotopyCategory.quotient A' ⋙ Φ =
        (S ⋙ pushforwardFunctor φ) ⋙ HomotopyCategory.quotient B :=
  ⟨HomotopyCategory.descend (S ⋙ pushforwardFunctor φ)
      (hS.comp (preservesHomotopic_pushforwardFunctor φ)),
    HomotopyCategory.quotient_comp_descend _ _,
    fun _ hΨ => HomotopyCategory.eq_descend _ _ _ hΨ⟩

/-- **The functor of Tag 0FTS at the internal hom.** Wherever the internal hom of the
differential graded `(𝒜, 𝒜')`-bimodule `𝒩` does exist as a functor with a differential graded
extension, `SheafOfModules.DifferentialGradedModule.exists_homotopyPushforwardSheafHom` gives
the functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of the tag on the homotopy categories. -/
theorem exists_homotopyPushforwardSheafHom_of_sheafHomFunctorData
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A)
    {N : DifferentialGradedBimodule.{t, a, z} A A'}
    (S : SheafHomFunctorData.{t, a, m, s, z} N) (ES : S.HomotopyExtension) :
    ∃! Φ : HomotopyCategory.{t, a, s} A' ⥤ HomotopyCategory.{t, a', m} B,
      HomotopyCategory.quotient A' ⋙ Φ =
        (S.functor ⋙ pushforwardFunctor φ) ⋙ HomotopyCategory.quotient B :=
  exists_homotopyPushforwardSheafHom φ S.functor ES.preservesHomotopic

end PushforwardSheafHom

end SheafOfModules.DifferentialGradedModule

end
