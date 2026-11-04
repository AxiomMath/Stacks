module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionRestrictionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquarePieceMapCompositionLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMapDegreeOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos

/-!
# Base change of the conormal module of an immersion of algebraic spaces

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a fibre product square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
in which `i` and `i'` are **immersions**.  [Stacks Project, Tag 04CQ] asserts that the canonical
map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is surjective, and that it is an
isomorphism when `g` is flat.  Both clauses are proved here at that generality, for the canonical
map `AlgebraicGeometry.Space.conormalMapOfImmersions` between the conormal modules
`AlgebraicGeometry.Space.immersionConormalModule`, with flatness of `g` read as flatness of a
morphism of algebraic spaces, `AlgebraicGeometry.Space.IsFlat` of Stacks 03ML.

## Main results

* `AlgebraicGeometry.Space.epi_conormalMapOfImmersions_of_isPullback`: **the surjectivity clause
  of [Stacks Project, Tag 04CQ]**.
* `AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isPullback_of_isFlat`: **the flat
  clause of [Stacks Project, Tag 04CQ]**.
* `AlgebraicGeometry.Space.epi_conormalMapOfImmersions_of_isPullback_of_isClosedImmersion`,
  `AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isPullback_of_isClosedImmersion`: the
  two clauses when the lower immersion is closed.

## References

* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- A map conjugated by two `eqToHom`s is an epimorphism when the map is. -/
theorem epi_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {A A' T T' : C} (hA : A = A')
    (m : A' ⟶ T) (hT : T = T') [Epi m] : Epi (eqToHom hA ≫ m ≫ eqToHom hT) := by
  subst hA hT
  simpa using (inferInstance : Epi m)

/-- A map conjugated by two `eqToHom`s is an isomorphism when the map is. -/
theorem isIso_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {A A' T T' : C} (hA : A = A')
    (m : A' ⟶ T) (hT : T = T') [IsIso m] : IsIso (eqToHom hA ≫ m ≫ eqToHom hT) := by
  subst hA hT
  simpa using (inferInstance : IsIso m)

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transfer along stacked squares -/

section Stack

variable {Z₁ Z₂ Z₃ X₁ X₂ X₃ : AlgebraicSpaces B S hS} (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂)
    (i₃ : Z₃ ⟶ X₃) (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃)
    (hi₁ : IsImmersion B S hS i₁.hom) (hi₂ : IsImmersion B S hS i₂.hom)
    (hi₃ : IsImmersion B S hS i₃.hom)
    (hsq₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃)
    (hsq : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃)

include hsq₂ in
/-- If the canonical map of the outer rectangle of two stacked squares is surjective, so is the
one of the upper square. -/
theorem epi_conormalMapOfImmersions_upper
    (h : Epi (conormalMapOfImmersions B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃ hsq)) :
    Epi (conormalMapOfImmersions B S hS i₁ i₂ f₁ g₁ hi₁ hi₂ hsq₁) := by
  rw [conormalMapOfImmersions_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hi₁ hi₂ hi₃ hsq₁ hsq₂ hsq,
    ← Category.assoc] at h
  exact @epi_of_epi _ _ _ _ _ _ _ h

/-- If the canonical maps of the outer rectangle and of the lower square of two stacked squares
are invertible, so is the one of the upper square. -/
theorem isIso_conormalMapOfImmersions_upper
    (h : IsIso (conormalMapOfImmersions B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃ hsq))
    (h₂ : IsIso (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)) :
    IsIso (conormalMapOfImmersions B S hS i₁ i₂ f₁ g₁ hi₁ hi₂ hsq₁) := by
  rw [conormalMapOfImmersions_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hi₁ hi₂ hi₃ hsq₁ hsq₂ hsq,
    ← Category.assoc] at h
  have h₂' := (modulePullback B S hS f₁).map_isIso
    (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)
  have ha := @IsIso.comp_isIso' _ _ _ _ _ _ _
    (Iso.isIso_inv ((modulePullbackCompIso B S hS f₁ f₂).app
      (immersionConormalModule B S hS i₃ hi₃))) h₂'
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ha h

/-- If the canonical maps of the two stacked squares are surjective, so is the one of the outer
rectangle. -/
theorem epi_conormalMapOfImmersions_outer
    (h₁ : Epi (conormalMapOfImmersions B S hS i₁ i₂ f₁ g₁ hi₁ hi₂ hsq₁))
    (h₂ : Epi (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)) :
    Epi (conormalMapOfImmersions B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃ hsq) := by
  rw [conormalMapOfImmersions_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hi₁ hi₂ hi₃ hsq₁ hsq₂ hsq]
  have hP : (modulePullback B S hS f₁).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS f₁)
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv ((modulePullbackCompIso B S hS
      f₁ f₂).app (immersionConormalModule B S hS i₃ hi₃))))
    (epi_comp' (@Functor.map_epi _ _ _ _ _ hP _ _ _ h₂) h₁)

/-- If the canonical maps of the two stacked squares are invertible, so is the one of the outer
rectangle. -/
theorem isIso_conormalMapOfImmersions_outer
    (h₁ : IsIso (conormalMapOfImmersions B S hS i₁ i₂ f₁ g₁ hi₁ hi₂ hsq₁))
    (h₂ : IsIso (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)) :
    IsIso (conormalMapOfImmersions B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃ hsq) := by
  rw [conormalMapOfImmersions_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hi₁ hi₂ hi₃ hsq₁ hsq₂ hsq]
  exact IsIso.comp_isIso' (Iso.isIso_inv ((modulePullbackCompIso B S hS f₁ f₂).app
      (immersionConormalModule B S hS i₃ hi₃)))
    (IsIso.comp_isIso' ((modulePullback B S hS f₁).map_isIso
      (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)) h₁)

/-- If the canonical map of the outer rectangle of two stacked squares is surjective and the
upper square, whose left vertical morphism is an identity, has invertible canonical map, then the
canonical map of the lower square is surjective. -/
theorem epi_conormalMapOfImmersions_lower {Z X₁ X₂ Z₃ X₃ : AlgebraicSpaces B S hS}
    (i₁ : Z ⟶ X₁) (i₂ : Z ⟶ X₂) (i₃ : Z₃ ⟶ X₃) (g₁ : X₁ ⟶ X₂) (f₂ : Z ⟶ Z₃) (g₂ : X₂ ⟶ X₃)
    (hi₁ : IsImmersion B S hS i₁.hom) (hi₂ : IsImmersion B S hS i₂.hom)
    (hi₃ : IsImmersion B S hS i₃.hom)
    (hsq₁ : i₁ ≫ g₁ = 𝟙 Z ≫ i₂) (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃)
    (hsq : i₁ ≫ g₁ ≫ g₂ = (𝟙 Z ≫ f₂) ≫ i₃)
    (h : Epi (conormalMapOfImmersions B S hS i₁ i₃ (𝟙 Z ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃ hsq))
    (h₁ : IsIso (conormalMapOfImmersions B S hS i₁ i₂ (𝟙 Z) g₁ hi₁ hi₂ hsq₁)) :
    Epi (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂) := by
  rw [conormalMapOfImmersions_comp B S hS i₁ i₂ i₃ (𝟙 Z) g₁ f₂ g₂ hi₁ hi₂ hi₃ hsq₁ hsq₂ hsq]
    at h
  have h' := @epi_of_epi _ _ _ _ _ _ _ h
  have h'' : Epi ((modulePullback B S hS (𝟙 Z)).map
      (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)) := by
    have := epi_comp' h' (@IsIso.epi_of_iso _ _ _ _ _ (IsIso.inv_isIso (f := conormalMapOfImmersions
      B S hS i₁ i₂ (𝟙 Z) g₁ hi₁ hi₂ hsq₁)))
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using this
  have hnat := (modulePullbackIdIso B S hS Z).hom.naturality
    (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)
  have h3 := epi_comp' h'' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom
    ((modulePullbackIdIso B S hS Z).app (immersionConormalModule B S hS i₂ hi₂))))
  rw [Iso.app_hom, hnat, Functor.id_map] at h3
  exact @epi_of_epi _ _ _ _ _ _ _ h3

/-- The invertibility counterpart of `AlgebraicGeometry.Space.epi_conormalMapOfImmersions_lower`.
-/
theorem isIso_conormalMapOfImmersions_lower {Z X₁ X₂ Z₃ X₃ : AlgebraicSpaces B S hS}
    (i₁ : Z ⟶ X₁) (i₂ : Z ⟶ X₂) (i₃ : Z₃ ⟶ X₃) (g₁ : X₁ ⟶ X₂) (f₂ : Z ⟶ Z₃) (g₂ : X₂ ⟶ X₃)
    (hi₁ : IsImmersion B S hS i₁.hom) (hi₂ : IsImmersion B S hS i₂.hom)
    (hi₃ : IsImmersion B S hS i₃.hom)
    (hsq₁ : i₁ ≫ g₁ = 𝟙 Z ≫ i₂) (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃)
    (hsq : i₁ ≫ g₁ ≫ g₂ = (𝟙 Z ≫ f₂) ≫ i₃)
    (h : IsIso (conormalMapOfImmersions B S hS i₁ i₃ (𝟙 Z ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃ hsq))
    (h₁ : IsIso (conormalMapOfImmersions B S hS i₁ i₂ (𝟙 Z) g₁ hi₁ hi₂ hsq₁)) :
    IsIso (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂) := by
  rw [conormalMapOfImmersions_comp B S hS i₁ i₂ i₃ (𝟙 Z) g₁ f₂ g₂ hi₁ hi₂ hi₃ hsq₁ hsq₂ hsq,
    ← Category.assoc] at h
  have h' := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₁ h
  have h'' := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_inv ((modulePullbackCompIso B S
    hS (𝟙 Z) f₂).app (immersionConormalModule B S hS i₃ hi₃))) h'
  have hnat := (modulePullbackIdIso B S hS Z).hom.naturality
    (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂)
  have h3 := @IsIso.comp_isIso' _ _ _ _ _ _ _ h'' (Iso.isIso_hom
    ((modulePullbackIdIso B S hS Z).app (immersionConormalModule B S hS i₂ hi₂)))
  rw [Iso.app_hom, hnat, Functor.id_map] at h3
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom
    ((modulePullbackIdIso B S hS Z).app
      ((modulePullback B S hS f₂).obj (immersionConormalModule B S hS i₃ hi₃)))) h3

end Stack

section Congr

variable {Z X Z' X' : AlgebraicSpaces B S hS} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)

/-- The canonical map only depends on the vertical morphisms through their values. -/
theorem epi_conormalMapOfImmersions_congr {f f' : Z ⟶ Z'} {g g' : X ⟶ X'} (hf : f = f')
    (hg : g = g') (hsq : i ≫ g = f ≫ i') (hsq' : i ≫ g' = f' ≫ i')
    (h : Epi (conormalMapOfImmersions B S hS i i' f g hi hi' hsq)) :
    Epi (conormalMapOfImmersions B S hS i i' f' g' hi hi' hsq') := by
  subst hf hg
  exact h

/-- The canonical map only depends on the vertical morphisms through their values. -/
theorem isIso_conormalMapOfImmersions_congr {f f' : Z ⟶ Z'} {g g' : X ⟶ X'} (hf : f = f')
    (hg : g = g') (hsq : i ≫ g = f ≫ i') (hsq' : i ≫ g' = f' ≫ i')
    (h : IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' hsq)) :
    IsIso (conormalMapOfImmersions B S hS i i' f' g' hi hi' hsq') := by
  subst hf hg
  exact h

/-- **Stacks 04CO, as invertibility of the canonical map.**  At a fibre product square whose
transverse morphism is étale the canonical map of Stacks 04CP is an isomorphism. -/
theorem isIso_conormalMapOfImmersions_of_isPullback_of_isEtale (f : Z ⟶ Z') (g : X ⟶ X')
    (sq : IsPullback f i i' g) (hg : IsEtale B S hS g.hom) :
    IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' sq.w.symm) := by
  rw [← conormalModuleOfImmersionEtaleRestrictionIso_hom B S hS f i i' g sq hi' hg]
  exact Iso.isIso_hom _

end Congr

/-! ### The closed case -/

section Closed

variable {Z V Z' V' : AlgebraicSpaces B S hS}

/-- The range of a closed immersion, as a closed subspace of the target. -/
noncomputable abbrev closedImmersionRange (j : Z ⟶ V) (hj : IsClosedImmersion B S hS j.hom) :
    ClosedSubspaces B S hS V.1 :=
  ⟨Subfunctor.range j.hom, isClosedSubspace_range_of_isClosedImmersion B S hS j.hom Z.2 hj⟩

/-- **The surjectivity clause at the canonical fibre product square of a closed subspace**, for
the canonical map of immersions.  For a closed subspace `Z' ⊆ X'` and its inverse image
`g⁻¹(Z') ⊆ X`, the canonical map of Stacks 04CP of the square of the two inclusions is
surjective. -/
theorem epi_conormalMapOfImmersions_preimageSubspace {X X' : AlgebraicSpaces B S hS}
    (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1) :
    Epi (conormalMapOfImmersions B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'))
      (subspaceInclusion B S hS X' Z') (preimageProjection B S hS g Z') g
      (isImmersion_subspaceInclusion B S hS X _) (isImmersion_subspaceInclusion B S hS X' Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) := by
  rw [conormalMapOfImmersions_eq_kernelIdealZPowSquareMap, kernelIdealZPowSquareMap_eq,
    kernelIdealSquareMap_one_eq_idealSheafMap]
  have hP : (modulePullback B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'))).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS _)
  have hsqIso := Iso.isIso_hom ((squarePullbackCompIso B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'))
      (subspaceInclusion B S hS X' Z') (preimageProjection B S hS g Z') g
      (conormalEtaleRestrictionSquare B S hS g Z')).app
    (kernelIdealSheafZPow B S hS (subspaceInclusion B S hS X' Z') 1).toSheafOfModules)
  have hideal := @epi_eqToHom_comp_comp_eqToHom _ _ _ _ _ _
    (congrArg (modulePullback B S hS g).obj
      (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X' Z'))
    (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z'))
    (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X (preimageSubspace B S hS g Z')).symm
    (epi_idealSheafMap B S hS g Z')
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullback B S hS _).mapIso
      (conormalModuleOfImmersionZPowIso B S hS _ _).symm)))
    (epi_comp' (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ hsqIso)
      (@Functor.map_epi _ _ _ _ _ hP _ _ _ hideal))
      (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom (conormalModuleOfImmersionZPowIso B S hS _ _))))

/-- **The flat clause at the canonical fibre product square of a closed subspace**, for the
canonical map of immersions: if the morphism of small étale ringed topoi of `g` is flat, the
canonical map of the square of the two inclusions is an isomorphism. -/
theorem isIso_conormalMapOfImmersions_preimageSubspace {X X' : AlgebraicSpaces B S hS}
    (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    IsIso (conormalMapOfImmersions B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'))
      (subspaceInclusion B S hS X' Z') (preimageProjection B S hS g Z') g
      (isImmersion_subspaceInclusion B S hS X _) (isImmersion_subspaceInclusion B S hS X' Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) := by
  rw [conormalMapOfImmersions_eq_kernelIdealZPowSquareMap, kernelIdealZPowSquareMap_eq,
    kernelIdealSquareMap_one_eq_idealSheafMap]
  have h := isIso_idealSheafMap_of_isFlat B S hS g Z' hg
  have hsqIso := Iso.isIso_hom ((squarePullbackCompIso B S hS
      (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'))
      (subspaceInclusion B S hS X' Z') (preimageProjection B S hS g Z') g
      (conormalEtaleRestrictionSquare B S hS g Z')).app
    (kernelIdealSheafZPow B S hS (subspaceInclusion B S hS X' Z') 1).toSheafOfModules)
  have hideal := @isIso_eqToHom_comp_comp_eqToHom _ _ _ _ _ _
    (congrArg (modulePullback B S hS g).obj
      (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X' Z'))
    (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z'))
    (kernelIdealSheafZPow_one_toSheafOfModules_eq B S hS X (preimageSubspace B S hS g Z')).symm h
  exact IsIso.comp_isIso' (Iso.isIso_hom ((modulePullback B S hS _).mapIso
      (conormalModuleOfImmersionZPowIso B S hS _ _).symm)) (IsIso.comp_isIso'
    (@IsIso.comp_isIso' _ _ _ _ _ _ _ hsqIso (@Functor.map_isIso _ _ _ _ _ _ _ _ hideal))
    (Iso.isIso_hom (conormalModuleOfImmersionZPowIso B S hS _ _)))

/-- The lower comparison square of the reduction of a closed immersion to the inclusion of its
range: the closed immersion over the inclusion of its range, with the identification of the
source with the range and the identity of the target as vertical morphisms. -/
theorem isPullback_closedImmersionRange (j : Z ⟶ V) (hj : IsClosedImmersion B S hS j.hom) :
    IsPullback j ((ObjectProperty.fullyFaithfulι _).preimageIso
        (by haveI := mono_of_isClosedImmersion B S hS j.hom hj
            exact asIso (Subfunctor.toRange j.hom)) :
          Z ≅ ⟨(closedImmersionRange B S hS j hj).1.toFunctor,
            (closedImmersionRange B S hS j hj).2.1⟩).hom
      (𝟙 V) (subspaceInclusion B S hS V (closedImmersionRange B S hS j hj)) :=
  IsPullback.of_vert_isIso ⟨ObjectProperty.hom_ext _ (by
    simp only [Category.comp_id]
    exact (Subfunctor.toRange_ι j.hom).symm)⟩

end Closed

section ClosedCartesian

variable {Z X Z' X' : AlgebraicSpaces B S hS}

/-- A fibre product square over a closed immersion `i'` is the base change of the square of the
inclusion of its range: the source of `i` is the inverse image of the range, with `e'` and `e` the
identifications of the sources with the two subspaces. -/
private theorem exists_closedImmersionRange_preimage_iso
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'} {g : X ⟶ X'}
    (hi'c : IsClosedImmersion B S hS i'.hom) (hcart : IsPullback i f g i') :
    ∃ (Zc : ClosedSubspaces B S hS X'.1) (e' : Z' ⟶ ⟨Zc.1.toFunctor, Zc.2.1⟩)
      (e : Z ⟶ ⟨(preimageSubspace B S hS g Zc).1.toFunctor,
        (preimageSubspace B S hS g Zc).2.1⟩),
      IsPullback i' e' (𝟙 X') (subspaceInclusion B S hS X' Zc) ∧
      IsPullback e i (subspaceInclusion B S hS X (preimageSubspace B S hS g Zc)) (𝟙 X) ∧
      e ≫ preimageProjection B S hS g Zc = f ≫ e' := by
  have L := isPullback_closedImmersionRange B S hS i' hi'c
  set Zc := closedImmersionRange B S hS i' hi'c
  set e' := ((ObjectProperty.fullyFaithfulι _).preimageIso
        (by have := mono_of_isClosedImmersion B S hS i'.hom hi'c
            exact asIso (Subfunctor.toRange i'.hom)) :
          Z' ≅ ⟨Zc.1.toFunctor, Zc.2.1⟩).hom
  have O : IsPullback i (f ≫ e') g (subspaceInclusion B S hS X' Zc) := by
    simpa only [Category.comp_id] using hcart.paste_vert L
  have C := (isPullback_fromPreimage B S hS g Zc.1 Zc.2.1
    (isClosedSubspace_preimage B S hS g.hom Zc.1 X'.2 X.2 Zc.2).1).flip
  have he₁ := O.isoIsPullback_hom_fst _ _ C
  exact ⟨Zc, e', _, L, IsPullback.of_horiz_isIso ⟨by rw [he₁, Category.comp_id]⟩,
    O.isoIsPullback_hom_snd _ _ C⟩

/-- **The surjectivity clause of Stacks 04CQ when the lower immersion is closed.** -/
theorem epi_conormalMapOfImmersions_of_isPullback_of_isClosedImmersion
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hi'c : IsClosedImmersion B S hS i'.hom) (hcart : IsPullback i f g i') :
    Epi (conormalMapOfImmersions B S hS i i' f g hi hi' hcart.w) := by
  obtain ⟨Zc, e', e, L, U, he₂⟩ := exists_closedImmersionRange_preimage_iso B S hS hi'c hcart
  have hU := isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS i
    (subspaceInclusion B S hS X (preimageSubspace B S hS g Zc)) hi
    (isImmersion_subspaceInclusion B S hS X _) e (𝟙 X) U (fun _ _ hφ ↦ by simpa using hφ)
  have hC := epi_conormalMapOfImmersions_preimageSubspace B S hS g Zc
  have hR := epi_conormalMapOfImmersions_outer B S hS i _ _ e (𝟙 X) _ g hi
    (isImmersion_subspaceInclusion B S hS X _) (isImmersion_subspaceInclusion B S hS X' Zc)
    U.w.symm (conormalEtaleRestrictionSquare B S hS g Zc) (by
      rw [Category.id_comp, Category.assoc, ← conormalEtaleRestrictionSquare B S hS g Zc,
        ← Category.assoc, U.w, Category.comp_id])
    (@IsIso.epi_of_iso _ _ _ _ _ hU) hC
  have hR' := epi_conormalMapOfImmersions_congr B S hS i (subspaceInclusion B S hS X' Zc) hi
    (isImmersion_subspaceInclusion B S hS X' Zc) he₂
    (show 𝟙 X ≫ g = g ≫ 𝟙 X' by simp) _
    (stackedSquare_comm B S hS i i' _ f g e' (𝟙 X') hcart.w L.w) hR
  exact epi_conormalMapOfImmersions_upper B S hS i i' _ f g e' (𝟙 X') hi hi'
    (isImmersion_subspaceInclusion B S hS X' Zc) hcart.w L.w _ hR'

/-- **The flat clause of Stacks 04CQ when the lower immersion is closed**, with flatness of the
morphism of small étale ringed topoi of `g`. -/
theorem isIso_conormalMapOfImmersions_of_isPullback_of_isClosedImmersion
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hi'c : IsClosedImmersion B S hS i'.hom) (hcart : IsPullback i f g i')
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' hcart.w) := by
  obtain ⟨Zc, e', e, L, U, he₂⟩ := exists_closedImmersionRange_preimage_iso B S hS hi'c hcart
  have hU := isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS i
    (subspaceInclusion B S hS X (preimageSubspace B S hS g Zc)) hi
    (isImmersion_subspaceInclusion B S hS X _) e (𝟙 X) U (fun _ _ hφ ↦ by simpa using hφ)
  have hC := isIso_conormalMapOfImmersions_preimageSubspace B S hS g Zc hg
  have hR := isIso_conormalMapOfImmersions_outer B S hS i _ _ e (𝟙 X) _ g hi
    (isImmersion_subspaceInclusion B S hS X _) (isImmersion_subspaceInclusion B S hS X' Zc)
    U.w.symm (conormalEtaleRestrictionSquare B S hS g Zc) (by
      rw [Category.id_comp, Category.assoc, ← conormalEtaleRestrictionSquare B S hS g Zc,
        ← Category.assoc, U.w, Category.comp_id])
    hU hC
  have hR' := isIso_conormalMapOfImmersions_congr B S hS i (subspaceInclusion B S hS X' Zc) hi
    (isImmersion_subspaceInclusion B S hS X' Zc) he₂
    (show 𝟙 X ≫ g = g ≫ 𝟙 X' by simp) _
    (stackedSquare_comm B S hS i i' _ f g e' (𝟙 X') hcart.w L.w) hR
  have hL := isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS i'
    (subspaceInclusion B S hS X' Zc) hi' (isImmersion_subspaceInclusion B S hS X' Zc) e' (𝟙 X')
    L.flip (fun _ _ hφ ↦ by simpa using hφ)
  exact isIso_conormalMapOfImmersions_upper B S hS i i' _ f g e' (𝟙 X') hi hi'
    (isImmersion_subspaceInclusion B S hS X' Zc) hcart.w L.w _ hR' hL

end ClosedCartesian

/-! ### The ambient open subspace of the upper row -/

section Ambient

variable {Z X Z' X' : AlgebraicSpaces B S hS} (i' : Z' ⟶ X') (hi' : IsImmersion B S hS i'.hom)
    (g : X ⟶ X')

/-- The open subspace `X' ∖ ∂Z'` of `X'` in which the immersion `i'` is closed, as a subfunctor. -/
noncomputable abbrev immersionAmbientSubfunctor : Subfunctor X'.1 :=
  boundaryComplement B S hS X'.1 (Set.range (pointsMap B S hS Z'.1 i'.hom))

include hi' in
/-- `X' ∖ ∂Z'` is an open subspace of `X'`. -/
theorem isOpenSubspace_immersionAmbientSubfunctor :
    IsOpenSubspace B S hS (immersionAmbientSubfunctor B S hS i') :=
  isOpenSubspace_boundaryComplement B S hS X'.2
    (isLocallyClosed_range_pointsMap_of_isImmersion B S hS X'.2 i'.hom hi')

include hi' in
/-- The inverse image of `X' ∖ ∂Z'` along `g` is an algebraic space. -/
theorem isAlgebraicSpace_preimage_immersionAmbientSubfunctor :
    IsAlgebraicSpace B S hS ((immersionAmbientSubfunctor B S hS i').preimage g.hom).toFunctor :=
  isAlgebraicSpace_of_iso B S hS
    (Subfunctor.isPullback_preimage g.hom (immersionAmbientSubfunctor B S hS i')).isoPullback.symm
    (isAlgebraicSpace_pullback B S hS _ g.hom
      (isOpenSubspace_immersionAmbientSubfunctor B S hS i' hi').1 X.2 X'.2)

/-- The inverse image `g⁻¹(X' ∖ ∂Z')`, an open subspace of `X`, as an algebraic space. -/
noncomputable def preimageAmbient : AlgebraicSpaces B S hS :=
  ⟨((immersionAmbientSubfunctor B S hS i').preimage g.hom).toFunctor,
    isAlgebraicSpace_preimage_immersionAmbientSubfunctor B S hS i' hi' g⟩

/-- The inclusion of `g⁻¹(X' ∖ ∂Z')` into `X`. -/
noncomputable def preimageAmbientInclusion : preimageAmbient B S hS i' hi' g ⟶ X :=
  ObjectProperty.homMk ((immersionAmbientSubfunctor B S hS i').preimage g.hom).ι

/-- The restriction `g⁻¹(X' ∖ ∂Z') ⟶ X' ∖ ∂Z'` of `g`. -/
noncomputable def preimageAmbientMap :
    preimageAmbient B S hS i' hi' g ⟶ immersionAmbient B S hS X'.2 Z'.2 i'.hom hi' :=
  ObjectProperty.homMk ((immersionAmbientSubfunctor B S hS i').fromPreimage g.hom)

/-- The square of the restriction of `g` over the two inclusions is cartesian. -/
theorem isPullback_preimageAmbient :
    IsPullback (preimageAmbientMap B S hS i' hi' g) (preimageAmbientInclusion B S hS i' hi' g)
      (immersionAmbientInclusion B S hS i' hi') g :=
  isPullback_fromPreimage B S hS g (immersionAmbientSubfunctor B S hS i')
    (isOpenSubspace_immersionAmbientSubfunctor B S hS i' hi').1
    (isAlgebraicSpace_preimage_immersionAmbientSubfunctor B S hS i' hi' g)

/-- The inclusion of `g⁻¹(X' ∖ ∂Z')` is a monomorphism. -/
theorem mono_preimageAmbientInclusion : Mono (preimageAmbientInclusion B S hS i' hi' g) :=
  ⟨fun _ _ hab ↦ ObjectProperty.hom_ext _
    ((cancel_mono ((immersionAmbientSubfunctor B S hS i').preimage g.hom).ι).mp
      (congrArg (fun k ↦ k.hom) hab))⟩

/-- The inclusion of `g⁻¹(X' ∖ ∂Z')` is étale. -/
theorem isEtale_preimageAmbientInclusion :
    IsEtale B S hS (preimageAmbientInclusion B S hS i' hi' g).hom :=
  isEtale_of_isPullback B S hS _ _ _ _ (isPullback_preimageAmbient B S hS i' hi' g)
    (isEtale_immersionAmbientInclusion B S hS i' hi')

/-- **The restriction of a flat morphism to the inverse image of an open subspace is flat**: the
restriction `g⁻¹(X' ∖ ∂Z') ⟶ X' ∖ ∂Z'` of a flat `g` is flat. -/
theorem isFlat_preimageAmbientMap (hg : IsFlat B S hS g.hom) :
    IsFlat B S hS (preimageAmbientMap B S hS i' hi' g).hom :=
  isFlat_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_preimageAmbient B S hS i' hi' g))
    (presheaf_etale_of_isOpenImmersion B S hS
      (isOpenSubspace_immersionAmbientSubfunctor B S hS i' hi').2) hg

variable (i : Z ⟶ X) (f : Z ⟶ Z') (hsq : i ≫ g = f ≫ i')

include hi' hsq in
/-- If `g ∘ i = i' ∘ f`, the image of `i` lies in `g⁻¹(X' ∖ ∂Z')`. -/
theorem range_le_preimage_immersionAmbientSubfunctor :
    Subfunctor.range i.hom ≤ (immersionAmbientSubfunctor B S hS i').preimage g.hom := by
  rintro T _ ⟨z, rfl⟩
  have hsq' : i.hom ≫ g.hom = f.hom ≫ i'.hom := congrArg (fun k ↦ k.hom) hsq
  have hmem : (i.hom ≫ g.hom).app T z ∈ (Subfunctor.range (f.hom ≫ i'.hom)).obj T :=
    hsq' ▸ ⟨z, rfl⟩
  exact range_le_boundaryComplement B S hS X'.2 Z'.2 i'.hom hi' T
    (Subfunctor.range_comp_le _ _ T hmem)

/-- The factorisation of `i` through `g⁻¹(X' ∖ ∂Z')`. -/
noncomputable def preimageAmbientLift : Z ⟶ preimageAmbient B S hS i' hi' g :=
  ObjectProperty.homMk (Subfunctor.lift i.hom
    (range_le_preimage_immersionAmbientSubfunctor B S hS i' hi' g i f hsq))

/-- The factorisation of `i` through `g⁻¹(X' ∖ ∂Z')`, followed by the inclusion, is `i`. -/
theorem preimageAmbientLift_comp :
    preimageAmbientLift B S hS i' hi' g i f hsq ≫ preimageAmbientInclusion B S hS i' hi' g = i :=
  ObjectProperty.hom_ext _ (Subfunctor.lift_ι i.hom
    (range_le_preimage_immersionAmbientSubfunctor B S hS i' hi' g i f hsq))

/-- The square of the factorisation of `i` over the closed factorisation of `i'` commutes. -/
theorem preimageAmbientLift_comp_map :
    preimageAmbientLift B S hS i' hi' g i f hsq ≫ preimageAmbientMap B S hS i' hi' g =
      f ≫ immersionClosedFactorization B S hS X'.2 Z'.2 i'.hom hi' := by
  have := mono_immersionAmbientInclusion B S hS i' hi'
  refine (cancel_mono (immersionAmbientInclusion B S hS i' hi')).mp ?_
  rw [Category.assoc, (isPullback_preimageAmbient B S hS i' hi' g).w, ← Category.assoc,
    preimageAmbientLift_comp, hsq, Category.assoc,
    immersionClosedFactorization_comp_immersionAmbientInclusion]

/-- The square of `i` over its factorisation through `g⁻¹(X' ∖ ∂Z')` is cartesian. -/
theorem isPullback_preimageAmbientLift :
    IsPullback (𝟙 Z) (preimageAmbientLift B S hS i' hi' g i f hsq) i
      (preimageAmbientInclusion B S hS i' hi' g) :=
  have := mono_preimageAmbientInclusion B S hS i' hi' g
  IsPullback.of_horiz_isIso_mono
    ⟨by rw [Category.id_comp, preimageAmbientLift_comp]⟩

/-- **A fibre product square of immersions restricts to a fibre product square over the ambient
open subspaces**, whose lower immersion is closed. -/
theorem isPullback_preimageAmbientLift_closed (hcart : IsPullback i f g i') :
    IsPullback (preimageAmbientLift B S hS i' hi' g i f hcart.w) f
      (preimageAmbientMap B S hS i' hi' g)
      (immersionClosedFactorization B S hS X'.2 Z'.2 i'.hom hi') := by
  refine IsPullback.of_right ?_ (preimageAmbientLift_comp_map B S hS i' hi' g i f hcart.w)
    (isPullback_preimageAmbient B S hS i' hi' g).flip
  rw [preimageAmbientLift_comp, immersionClosedFactorization_comp_immersionAmbientInclusion]
  exact hcart

end Ambient

/-! ### Stacks 04CQ -/

section Main

variable {Z X Z' X' : AlgebraicSpaces B S hS}

/-- The reduction of Stacks 04CQ to the closed case: for a fibre product square `i, i'` and its
restriction `j, j'` over the ambient open subspaces `ι, ι'` of `i'`, the canonical map of `i, i'` is
surjective, resp. invertible, once the one of `j, j'` is. -/
private theorem epi_and_isIso_conormalMapOfImmersions_of_ambient {A V : AlgebraicSpaces B S hS}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'} {g : X ⟶ X'} {j : Z ⟶ A} {j' : Z' ⟶ V}
    {ι : A ⟶ X} {ι' : V ⟶ X'} {gV : A ⟶ V} (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) (hji : IsImmersion B S hS j.hom)
    (hj'i : IsImmersion B S hS j'.hom) (hcart : IsPullback i f g i')
    (hC : IsPullback j f gV j') (hQ : IsPullback gV ι ι' g) (hZ : IsPullback (𝟙 Z) j i ι)
    (hL : IsPullback (𝟙 Z') j' i' ι') (hι : IsEtale B S hS ι.hom) (hι' : IsEtale B S hS ι'.hom) :
    (Epi (conormalMapOfImmersions B S hS j j' f gV hji hj'i hC.w) →
      Epi (conormalMapOfImmersions B S hS i i' f g hi hi' hcart.w)) ∧
    (IsIso (conormalMapOfImmersions B S hS j j' f gV hji hj'i hC.w) →
      IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' hcart.w)) := by
  have hlower := isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS j' i' hj'i hi'
    (𝟙 Z') ι' hL hι'
  have hZiso := isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS j i hji hi (𝟙 Z) ι
    hZ hι
  have hst := stackedSquare_comm B S hS j j' i' f gV (𝟙 Z') ι' hC.w hL.w.symm
  have hst' := stackedSquare_comm B S hS j i i' (𝟙 Z) ι f g hZ.w.symm hcart.w
  have hfg : f ≫ 𝟙 Z' = 𝟙 Z ≫ f := by simp
  constructor
  · intro hupper
    have houter := epi_conormalMapOfImmersions_outer B S hS j j' i' f gV (𝟙 Z') ι' hji hj'i hi'
      hC.w hL.w.symm hst hupper (@IsIso.epi_of_iso _ _ _ _ _ hlower)
    exact epi_conormalMapOfImmersions_lower B S hS j i i' ι f g hji hi hi' hZ.w.symm hcart.w _
      (epi_conormalMapOfImmersions_congr B S hS j i' hji hi' hfg hQ.w _ hst' houter) hZiso
  · intro hupper
    have houter := isIso_conormalMapOfImmersions_outer B S hS j j' i' f gV (𝟙 Z') ι' hji hj'i hi'
      hC.w hL.w.symm hst hupper hlower
    exact isIso_conormalMapOfImmersions_lower B S hS j i i' ι f g hji hi hi' hZ.w.symm hcart.w _
      (isIso_conormalMapOfImmersions_congr B S hS j i' hji hi' hfg hQ.w _ hst' houter) hZiso

/-- **The surjectivity clause of [Stacks Project, Tag 04CQ].**  Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a fibre product square of algebraic spaces over `S` in which `i` and `i'` are immersions.  Then
the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] between the conormal
modules of the two immersions is an epimorphism of `𝒪_Z`-modules. -/
@[stacks 04CQ "surjectivity, for a fibre product square of immersions"]
theorem epi_conormalMapOfImmersions_of_isPullback
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hcart : IsPullback i f g i') :
    Epi (conormalMapOfImmersions B S hS i i' f g hi hi' hcart.w) := by
  set j := preimageAmbientLift B S hS i' hi' g i f hcart.w
  set ι := preimageAmbientInclusion B S hS i' hi' g
  set gV := preimageAmbientMap B S hS i' hi' g
  set j' := immersionClosedFactorization B S hS X'.2 Z'.2 i'.hom hi'
  set ι' := immersionAmbientInclusion B S hS i' hi'
  have hj'c : IsClosedImmersion B S hS j'.hom :=
    isClosedImmersion_boundaryComplementLift B S hS X'.2 Z'.2 i'.hom hi'
  have hj'i : IsImmersion B S hS j'.hom := isImmersion_of_isClosedImmersion B S hS hj'c
  have hC := isPullback_preimageAmbientLift_closed B S hS i' hi' g i f hcart
  have hji : IsImmersion B S hS j.hom := isImmersion_of_isPullback B S hS hC.flip hj'i
  have hupper := epi_conormalMapOfImmersions_of_isPullback_of_isClosedImmersion B S hS j j' f gV
    hji hj'i hj'c hC
  exact (epi_and_isIso_conormalMapOfImmersions_of_ambient B S hS hi hi' hji hj'i hcart hC
    (isPullback_preimageAmbient B S hS i' hi' g)
    (isPullback_preimageAmbientLift B S hS i' hi' g i f hcart.w)
    (isPullback_closedFactorization_ambientInclusion B S hS i' hi')
    (isEtale_preimageAmbientInclusion B S hS i' hi' g)
    (isEtale_immersionAmbientInclusion B S hS i' hi')).1 hupper

/-- **The flat clause of [Stacks Project, Tag 04CQ].**  For a fibre product square as in
`AlgebraicGeometry.Space.epi_conormalMapOfImmersions_of_isPullback`, if `g` is flat as a
morphism of algebraic spaces (Stacks 03ML), then the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of
[Stacks Project, Tag 04CP] is an isomorphism. -/
@[stacks 04CQ "isomorphism when g is flat, for a fibre product square of immersions"]
theorem isIso_conormalMapOfImmersions_of_isPullback_of_isFlat
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hcart : IsPullback i f g i') (hg : IsFlat B S hS g.hom) :
    IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' hcart.w) := by
  set j := preimageAmbientLift B S hS i' hi' g i f hcart.w
  set ι := preimageAmbientInclusion B S hS i' hi' g
  set gV := preimageAmbientMap B S hS i' hi' g
  set j' := immersionClosedFactorization B S hS X'.2 Z'.2 i'.hom hi'
  set ι' := immersionAmbientInclusion B S hS i' hi'
  have hj'c : IsClosedImmersion B S hS j'.hom :=
    isClosedImmersion_boundaryComplementLift B S hS X'.2 Z'.2 i'.hom hi'
  have hj'i : IsImmersion B S hS j'.hom := isImmersion_of_isClosedImmersion B S hS hj'c
  have hC := isPullback_preimageAmbientLift_closed B S hS i' hi' g i f hcart
  have hji : IsImmersion B S hS j.hom := isImmersion_of_isPullback B S hS hC.flip hj'i
  have hupper := isIso_conormalMapOfImmersions_of_isPullback_of_isClosedImmersion B S hS j j' f gV
    hji hj'i hj'c hC ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS gV).mp
      (isFlat_preimageAmbientMap B S hS i' hi' g hg))
  exact (epi_and_isIso_conormalMapOfImmersions_of_ambient B S hS hi hi' hji hj'i hcart hC
    (isPullback_preimageAmbient B S hS i' hi' g)
    (isPullback_preimageAmbientLift B S hS i' hi' g i f hcart.w)
    (isPullback_closedFactorization_ambientInclusion B S hS i' hi')
    (isEtale_preimageAmbientInclusion B S hS i' hi' g)
    (isEtale_immersionAmbientInclusion B S hS i' hi')).2 hupper

end Main

end AlgebraicGeometry.Space

end
