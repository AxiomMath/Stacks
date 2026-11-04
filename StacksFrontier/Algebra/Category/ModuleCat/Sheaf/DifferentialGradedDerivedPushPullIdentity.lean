module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushPullLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorPullbackFunctors

/-!
# The derived pushforward and the derived pullback along the identity

Along the identity morphism of ringed sites — the identity functor of a site, the identity
structure map of its sheaf of rings and the identity homomorphism of a sheaf of differential
graded algebras — both the direct image and the pullback of right differential graded modules
are the identity, so both are exact and
`SheafOfModules.DifferentialGradedModule.derivedPushPullDataOfInverts` applies with no
hypotheses at all. This records the resulting term.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.idDerivedPushPullData` is the resulting
  `SheafOfModules.DifferentialGradedModule.DerivedPushPullData`, for the differential graded
  extension `SheafOfModules.DifferentialGradedModule.idPullbackDataHomotopyExtension` of
  `SheafOfModules.DifferentialGradedModule.idPullbackData`, and
  `SheafOfModules.DifferentialGradedModule.idAdjunction` is its adjunction `Lf^* ⊣ Rf_*`.
* `SheafOfModules.DifferentialGradedModule.idDerivedPushforwardIso` and
  `...idDerivedPullbackIso`: the computation. Both derived functors along the identity are
  isomorphic to the identity functor of the derived category.

## Main results

* `SheafOfModules.DifferentialGradedModule.pushforwardFunctor_idSemilinearHom` and
  `...idPullbackData_functor`: on right differential graded modules both functors are the
  identity functor on the nose, and
  `...homotopyPushforwardFunctor_idSemilinearHom`, `...homotopyPullbackFunctor_idPullbackData`
  say the same of the induced functors of homotopy categories.
* `SheafOfModules.DifferentialGradedModule.preservesHomology_sitePushforward_id`: the direct
  image of sheaves of modules along the identity preserves homology, being the identity functor.

## Implementation notes

The point of recording this is the same as for
`SheafOfModules.DifferentialGradedModule.idPullbackData`: it shows that the hypotheses of
`derivedPushPullDataOfInverts` can be met with nothing assumed, and that `DerivedPushPullData` —
seven of whose consumers take it as an explicit parameter — is not an empty structure, whatever
the universes are. It carries no hypotheses beyond the sheafification hypotheses that make the
category of sheaves of modules abelian, which `quasiIsomorphisms` needs in order to be defined
at all.

Both identifications are definitional. `SheafOfModules.sitePushforward (𝟭 C)` with the identity
structure map is *reducibly* the identity functor, because `Mathlib.SheafOfModules.pushforwardId`
is `Iso.refl`, so exactness transports by `inferInstanceAs`. On the pullback side
`idPullbackData.obj` is the identity by construction and `idPullbackData.map` reduces to the
identity as well, since the universal property of the identity unit is inhabited by the
descending morphism itself; both functors are therefore `rfl`-equal to `𝟭`. The derived
statements are nevertheless not definitional, because the derived functors are obtained from the
universal property of the localization, so they are proved by uniqueness of the factorisation.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
-/

@[expose] public section

open CategoryTheory

universe t a b m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The direct image of sheaves of modules along the identity morphism of ringed sites preserves
homology, being the identity functor. -/
noncomputable instance preservesHomology_sitePushforward_id :
    (sitePushforward (𝟭 C) (𝟙 R.obj) :
      SheafOfModules.{m} R ⥤ SheafOfModules.{m} R).PreservesHomology :=
  inferInstanceAs ((𝟭 (SheafOfModules.{m} R)).PreservesHomology)

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The direct image of right differential graded modules along the identity morphism of ringed
sites is the identity functor. -/
theorem pushforwardFunctor_idSemilinearHom :
    pushforwardFunctor (DifferentialGradedAlgebra.idSemilinearHom A) =
      𝟭 (DifferentialGradedModule.{t, a, m} A) :=
  rfl

/-- The pullback of right differential graded modules along the identity morphism of ringed sites
is the identity functor. -/
theorem idPullbackData_functor :
    (idPullbackData.{t, a, m, v, u} (A := A)).functor =
      𝟭 (DifferentialGradedModule.{t, a, m} A) :=
  rfl

/-- `K(f_*)` for the identity morphism of ringed sites is the identity functor of the homotopy
category. -/
theorem homotopyPushforwardFunctor_idSemilinearHom :
    homotopyPushforwardFunctor (DifferentialGradedAlgebra.idSemilinearHom A) =
      𝟭 (HomotopyCategory.{t, a, m} A) :=
  HomotopyCategory.descend_id

/-- `K(f^*)` for the pullback along the identity morphism of ringed sites is the identity functor
of the homotopy category. -/
theorem homotopyPullbackFunctor_idPullbackData :
    homotopyPullbackFunctor (idPullbackData.{t, a, m, v, u} (A := A))
        idPullbackDataHomotopyExtension =
      𝟭 (HomotopyCategory.{t, a, m} A) :=
  HomotopyCategory.descend_id

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- `K(f_*)` for the identity morphism of ringed sites, followed by the localization, inverts the
quasi-isomorphisms: along the identity the direct image is restriction of scalars along a
homomorphism `ι : Z ⟶ A` of sheaves of differential graded algebras, which leaves the underlying
complex of sheaves of modules unchanged and is therefore exact. -/
theorem idIsInvertedBy_homotopyPushforwardFunctor_comp
    {Z : DifferentialGradedAlgebra.{t, b} R}
    (ι : DifferentialGradedAlgebra.SemilinearHom (𝟭 C) (𝟙 R.obj) Z A) :
    (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
      (homotopyPushforwardFunctor ι ⋙ toDerivedCategory.{t, b, m} Z) :=
  isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology
    preservesHomology_sitePushforward_id

/-- `K(f^*)` for the pullback along the identity morphism of ringed sites, followed by the
localization, inverts the quasi-isomorphisms: the pullback along the identity is the identity. -/
theorem idIsInvertedBy_homotopyPullbackFunctor_comp :
    (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
      (homotopyPullbackFunctor (idPullbackData.{t, a, m, v, u} (A := A))
          idPullbackDataHomotopyExtension ⋙
        toDerivedCategory.{t, a, m} A) :=
  isInvertedBy_homotopyPullbackFunctor_comp _ _ fun g hg => by
    rw [idPullbackData_map]
    exact hg

/-- **A term of `DerivedPushPullData`**, along the identity morphism of ringed sites: the derived
pushforward and the derived pullback are both the functor induced on the derived category by the
identity, with their comparison maps and the derived-value conditions of Stacks 05S9. It carries
no hypothesis on the site, the sheaf of rings or the algebra. -/
noncomputable def idDerivedPushPullData :
    DerivedPushPullData (idPullbackData.{t, a, m, v, u} (A := A)) idPullbackDataHomotopyExtension :=
  derivedPushPullDataOfInverts
    (idIsInvertedBy_homotopyPushforwardFunctor_comp (DifferentialGradedAlgebra.idSemilinearHom A))
    idIsInvertedBy_homotopyPullbackFunctor_comp

/-- **The derived pushforward along the identity is the identity**: `R(id)_*` is isomorphic to
the identity functor of the derived category. Both lift the identity of the homotopy category
followed by the localization. -/
noncomputable def idDerivedPushforwardIso :
    derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp.{t, a, a, m, v, u}
        (DifferentialGradedAlgebra.idSemilinearHom A)) ≅
      𝟭 (derivedCategory.{t, a, m} A) := by
  letI : Localization.Lifting (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
      (homotopyPushforwardFunctor (DifferentialGradedAlgebra.idSemilinearHom A) ⋙
        toDerivedCategory.{t, a, m} A) (𝟭 (derivedCategory.{t, a, m} A)) :=
    ⟨eqToIso (by rw [homotopyPushforwardFunctor_idSemilinearHom, Functor.comp_id,
      Functor.id_comp])⟩
  exact Localization.liftNatIso (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
    (homotopyPushforwardFunctor (DifferentialGradedAlgebra.idSemilinearHom A) ⋙
      toDerivedCategory.{t, a, m} A)
    (homotopyPushforwardFunctor (DifferentialGradedAlgebra.idSemilinearHom A) ⋙
      toDerivedCategory.{t, a, m} A)
    (derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp
      (DifferentialGradedAlgebra.idSemilinearHom A)))
    (𝟭 (derivedCategory.{t, a, m} A)) (Iso.refl _)

/-- **The derived pullback along the identity is the identity**: `L(id)^*` is isomorphic to the
identity functor of the derived category. -/
noncomputable def idDerivedPullbackIso :
    derivedPullbackOfInverts
        (idIsInvertedBy_homotopyPullbackFunctor_comp.{t, a, m, v, u} (A := A)) ≅
      𝟭 (derivedCategory.{t, a, m} A) := by
  letI : Localization.Lifting (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
      (homotopyPullbackFunctor (idPullbackData.{t, a, m, v, u} (A := A))
          idPullbackDataHomotopyExtension ⋙
        toDerivedCategory.{t, a, m} A) (𝟭 (derivedCategory.{t, a, m} A)) :=
    ⟨eqToIso (by rw [homotopyPullbackFunctor_idPullbackData, Functor.comp_id,
      Functor.id_comp])⟩
  exact Localization.liftNatIso (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
    (homotopyPullbackFunctor (idPullbackData.{t, a, m, v, u} (A := A))
      idPullbackDataHomotopyExtension ⋙ toDerivedCategory.{t, a, m} A)
    (homotopyPullbackFunctor (idPullbackData.{t, a, m, v, u} (A := A))
      idPullbackDataHomotopyExtension ⋙ toDerivedCategory.{t, a, m} A)
    (derivedPullbackOfInverts idIsInvertedBy_homotopyPullbackFunctor_comp)
    (𝟭 (derivedCategory.{t, a, m} A)) (Iso.refl _)

/-- The adjunction `Lf^* ⊣ Rf_*` along the identity morphism of ringed sites, with no calculus of
fractions assumed. -/
noncomputable def idAdjunction :
    derivedPullbackOfInverts
        (idIsInvertedBy_homotopyPullbackFunctor_comp.{t, a, m, v, u} (A := A)) ⊣
      derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp
        (DifferentialGradedAlgebra.idSemilinearHom A)) :=
  adjunctionOfInverts _ _

end DifferentialGradedModule

end SheafOfModules

end
