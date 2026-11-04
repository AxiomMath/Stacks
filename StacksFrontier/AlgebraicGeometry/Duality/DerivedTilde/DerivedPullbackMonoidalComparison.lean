module

public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalComparison

/-!
# The two canonical monoidal structures on derived pullback along a morphism of schemes agree

For a morphism of schemes `f : X ⟶ Y`, the derived pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` carries
two strong monoidal structures for the re-seated structures
`AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`, whose tensor product is the derived
tensor product of [Stacks, Tag 06YU] on the nose:

* `Stacks.Duality.derivedPullbackCanonicalMonoidal`, re-seated by
  `CategoryTheory.MonoidalCategory.Functor.monoidalReseat`;
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal`, re-seated by
  `CategoryTheory.MonoidalCategory.reseatFunctorMonoidal`.

Both re-seatings conjugate the tensorator by the re-seating isomorphisms, and the structures
re-seated have the same tensorator
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal_δ_eq`), so the two tensorators
of [Stacks, Tag 079U] agree; the lax tensorators, their inverses, agree as well.

## Main results

* `CategoryTheory.MonoidalCategory.Functor.monoidalReseat_δ`,
  `CategoryTheory.MonoidalCategory.Functor.monoidalReseat_μ` — the tensorators of
  `Functor.monoidalReseat`.
* `Stacks.Duality.derivedPullbackCanonicalMonoidal_δ_eq`,
  `Stacks.Duality.derivedPullbackCanonicalMonoidal_μ_eq` — the two structures have the same
  tensorators.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MC : MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- The lax tensorator of `reseatMonoidalInverse`, the identity functor from the given structure
to the re-seated one, is the inverse of `reseatIso`. -/
lemma reseatMonoidalInverse_μ (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y : C) :
    @Functor.LaxMonoidal.μ C _ MC C _ (reseat e ε) (𝟭 C)
      (reseatMonoidalInverse e ε).toLaxMonoidal X Y = (reseatIso e X Y).inv := by
  show 𝟙 _ ≫ ((reseatIso e X Y).inv ≫ (𝟙 X ⊗ₘ 𝟙 Y)) = _
  exact (Category.id_comp _).trans ((congrArg _ (id_tensorHom_id X Y)).trans (Category.comp_id _))

/-- The oplax tensorator of `reseatMonoidalInverse` is `reseatIso`. -/
lemma reseatMonoidalInverse_δ (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y : C) :
    @Functor.OplaxMonoidal.δ C _ MC C _ (reseat e ε) (𝟭 C)
      (reseatMonoidalInverse e ε).toOplaxMonoidal X Y = (reseatIso e X Y).hom := by
  have h := @Functor.Monoidal.μ_δ C _ MC C _ (reseat e ε) (𝟭 C) (reseatMonoidalInverse e ε) X Y
  rw [reseatMonoidalInverse_μ] at h
  simpa using (Iso.inv_comp_eq _).1 h

variable {D : Type u₂} [Category.{v₂} D] [MD : MonoidalCategory D] {T' : D ⥤ D ⥤ D} {U' : D}

/-- The oplax tensorator of `Functor.monoidalReseat` is that of `F` conjugated by the two
re-seating isomorphisms. -/
lemma Functor.monoidalReseat_δ (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') (X Y : C) :
    @Functor.OplaxMonoidal.δ C _ (reseat e ε) D _ (reseat e' ε') F
        (Functor.monoidalReseat F e ε e' ε').toOplaxMonoidal X Y =
      F.map (reseatIso e X Y).inv ≫ Functor.OplaxMonoidal.δ F X Y ≫
        (reseatIso e' (F.obj X) (F.obj Y)).hom := by
  rw [← reseatMonoidalInverse_δ e' ε']
  rfl

/-- The lax tensorator of `Functor.monoidalReseat` is that of `F` conjugated by the two
re-seating isomorphisms. -/
lemma Functor.monoidalReseat_μ (F : C ⥤ D) [F.Monoidal] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) (e' : curriedTensor D ≅ T') (ε' : 𝟙_ D ≅ U') (X Y : C) :
    @Functor.LaxMonoidal.μ C _ (reseat e ε) D _ (reseat e' ε') F
        (Functor.monoidalReseat F e ε e' ε').toLaxMonoidal X Y =
      (reseatIso e' (F.obj X) (F.obj Y)).inv ≫ Functor.LaxMonoidal.μ F X Y ≫
        F.map (reseatIso e X Y).hom := by
  show (@Functor.LaxMonoidal.μ D _ MD D _ (reseat e' ε') (𝟭 D)
      (reseatMonoidalInverse e' ε').toLaxMonoidal (F.obj X) (F.obj Y) ≫
    Functor.LaxMonoidal.μ F X Y) ≫ F.map (reseatIso e X Y).hom = _
  rw [reseatMonoidalInverse_μ, Category.assoc]

end CategoryTheory.MonoidalCategory

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The two canonical monoidal structures on `Lf^*` have the same oplax tensorator**
`Lf^*(K ⊗ᴸ L) ⟶ Lf^*K ⊗ᴸ Lf^*L` ([Stacks, Tag 079U]): `derivedPullbackCanonicalMonoidal` and
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal`, at the locally small
model. -/
theorem derivedPullbackCanonicalMonoidal_δ_eq (K L : DerivedCategory Y.Modules) :
    @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
        (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K L =
      @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.toRingedSpace.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.toRingedSpace.sheaf)
        (derivedPullback f)
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
          f.toLRSHom.toShHom).toOplaxMonoidal K L := by
  refine (@Functor.monoidalReseat_δ _ _ (Scheme.Modules.derivedMonoidal Y) _ _ _ _
    (Scheme.Modules.derivedMonoidal X) _ _ (derivedPullback f) (derivedPullbackDerivedMonoidal f)
    _ _ _ _ K L).trans ?_
  refine Eq.trans ?_ (@reseatFunctorMonoidal_δ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.toRingedSpace.sheaf) _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.toRingedSpace.sheaf) _ _
    (derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackKFlatMonoidal f.toLRSHom.toShHom)
    _ _ _ _ K L).symm
  exact congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal_δ_eq f.toLRSHom.toShHom K L)
    rfl)

/-- The two canonical monoidal structures on `Lf^*` have the same lax tensorator
`Lf^*K ⊗ᴸ Lf^*L ⟶ Lf^*(K ⊗ᴸ L)`, at the locally small model. -/
theorem derivedPullbackCanonicalMonoidal_μ_eq (K L : DerivedCategory Y.Modules) :
    @Functor.LaxMonoidal.μ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
        (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toLaxMonoidal K L =
      @Functor.LaxMonoidal.μ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.toRingedSpace.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.toRingedSpace.sheaf)
        (derivedPullback f)
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
          f.toLRSHom.toShHom).toLaxMonoidal K L := by
  have h₁ := @Functor.Monoidal.μ_δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
    (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
    (derivedPullbackCanonicalMonoidal f) K L
  have h₂ := @Functor.Monoidal.δ_μ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.toRingedSpace.sheaf) _ _
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.toRingedSpace.sheaf)
    (derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f.toLRSHom.toShHom)
    K L
  rw [derivedPullbackCanonicalMonoidal_δ_eq] at h₁
  exact (Category.comp_id _).symm.trans ((congrArg _ h₂).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans (Category.id_comp _))))

end Stacks.Duality

end
