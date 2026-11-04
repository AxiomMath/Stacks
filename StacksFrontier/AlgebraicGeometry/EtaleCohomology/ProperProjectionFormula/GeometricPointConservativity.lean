module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Inverse images to geometric points detect isomorphisms of `D(X_étale, Λ)`

Let `Y` be a scheme and `Λ` a commutative ring. A morphism `φ` of the unbounded derived category
of sheaves of `Λ`-modules on the small étale site of `Y` is an isomorphism as soon as its inverse
image `ȳ^{-1}φ` along every geometric point `ȳ : Spec Ω ⟶ Y` is one. This is [Stacks, Tag 03PU]
(stalks at geometric points detect isomorphisms of étale sheaves) read through inverse images:
the stalk of a sheaf at `ȳ` is the stalk at the tautological point of `Spec Ω` of its inverse
image (`Stacks.EtaleCohomology.smallEtalePullbackStalkAbIso`), so a sheaf map whose inverse
images to all geometric points are isomorphisms is an isomorphism on all stalks. The derived
statement follows because inverse image is exact, hence commutes with the cohomology sheaves.

The statement is given in the two readings of `D(Y_étale, Λ)` of this development: on
`DerivedCategory (EtaleModules Λ Y)` with the degreewise inverse image, and on the derived
category of modules over the constant ringed site `(Y_étale, Λ̲)` with the derived pullback along
the morphism of ringed topoi `Stacks.EtaleCohomology.etaleRingedToposHom`.

## Main results

* `Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleInverseImage_map`: sheaves of
  `Λ`-modules.
* `Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleDerivedInverseImage_map`:
  `D(Y_étale, Λ)`.
* `Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleRingedDerivedPullback_map`:
  `D(Y_étale, Λ̲)` on the constant ringed site, with derived pullbacks.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ] {Y : Scheme.{u}}

/-- **Inverse images to geometric points detect isomorphisms of étale sheaves of modules.** A
morphism `φ` of sheaves of `Λ`-modules on `Y_étale` whose inverse image along every geometric
point of `Y` is an isomorphism is an isomorphism: on underlying abelian sheaves the stalk at `ȳ`
is the stalk of the inverse image to `Spec Ω` at its tautological point, and stalks detect
isomorphisms ([Stacks, Tag 03PU]). -/
theorem isIso_of_forall_isIso_etaleModuleInverseImage_map {F G : EtaleModules.{u, 0} Λ Y}
    (φ : F ⟶ G)
    (h : ∀ y : GeometricPoint Y, IsIso ((etaleModuleInverseImage.{u, 0} Λ y.hom).map φ)) :
    IsIso φ := by
  rw [← isIso_iff_of_reflects_iso φ (etaleModuleForgetAb.{u, 0} Λ Y),
    isIso_iff_forall_isIso_smallEtaleStalkAb]
  intro y
  have e₁ : etaleAbelianInverseImage.{u, 0} y.hom ≅ smallEtalePullbackAb y.hom :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange y.hom)
        AddCommGrpCat.{u + 1} Y.smallEtaleTopology (y.source).smallEtaleTopology).leftAdjointUniq
      ((smallEtaleBaseChange y.hom).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology (y.source).smallEtaleTopology)
  have h₁ : IsIso ((etaleAbelianInverseImage.{u, 0} y.hom).map
      ((etaleModuleForgetAb.{u, 0} Λ Y).map φ)) := by
    have := h y
    exact (NatIso.isIso_map_iff (etaleModuleForgetInverseImageIso.{u, 0} Λ y.hom) φ).2
      (inferInstanceAs (IsIso ((etaleModuleForgetAb.{u, 0} Λ y.source).map
        ((etaleModuleInverseImage.{u, 0} Λ y.hom).map φ))))
  have h₂ : IsIso ((smallEtalePullbackAb y.hom).map ((etaleModuleForgetAb.{u, 0} Λ Y).map φ)) :=
    (NatIso.isIso_map_iff e₁ _).1 h₁
  have e₂ := smallEtalePullbackStalkAbIso y.hom (𝟙 y.source)
  rw [Category.id_comp] at e₂
  exact (NatIso.isIso_map_iff e₂ _).1
    (inferInstanceAs (IsIso ((smallEtaleStalkAb (𝟙 y.source)).map
      ((smallEtalePullbackAb y.hom).map ((etaleModuleForgetAb.{u, 0} Λ Y).map φ)))))

attribute [local instance] HasDerivedCategory.standard

/-- **Inverse images to geometric points detect isomorphisms of `D(Y_étale, Λ)`.** A morphism `φ`
of the unbounded derived category of sheaves of `Λ`-modules on `Y_étale` whose derived inverse
image along every geometric point of `Y` is an isomorphism is an isomorphism: inverse image is
exact, so it commutes with the cohomology sheaves, and those are detected by
`Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleInverseImage_map`. -/
theorem isIso_of_forall_isIso_etaleModuleDerivedInverseImage_map
    {M N : DerivedCategory (EtaleModules.{u, 0} Λ Y)} (φ : M ⟶ N)
    (h : ∀ y : GeometricPoint Y, IsIso ((etaleModuleDerivedInverseImage.{u, 0} Λ y.hom).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_forall_isIso_etaleModuleInverseImage_map Λ _ fun y => ?_
  have := h y
  exact ((etaleModuleInverseImage.{u, 0} Λ
      y.hom).isIso_homologyFunctor_map_mapDerivedCategory_map_iff
    φ n).1 inferInstance

/-- **Derived pullbacks to geometric points detect isomorphisms of `D(Y_étale, Λ̲)`**, on the
derived category of modules over the constant ringed site: the derived pullback along the
morphism of constant ringed topoi of a geometric point is the étale derived inverse image read
through `Stacks.EtaleCohomology.etaleDerivedEquivalence`. -/
theorem isIso_of_forall_isIso_etaleRingedDerivedPullback_map
    {M N : @DerivedCategory (EtaleRingedModules.{u, 0} Λ Y) _ _
      (HasDerivedCategory.standard _)} (φ : M ⟶ N)
    (h : ∀ y : GeometricPoint Y, IsIso ((etaleRingedDerivedPullback.{u, 0} Λ y.hom).map φ)) :
    IsIso φ := by
  let Φ := etaleDerivedEquivalence.{u, 0} Λ Y
  suffices IsIso (Φ.inverse.map φ) from isIso_of_fully_faithful Φ.inverse φ
  refine isIso_of_forall_isIso_etaleModuleDerivedInverseImage_map Λ _ fun y => ?_
  have h₁ : IsIso ((Φ.inverse ⋙ Φ.functor ⋙ etaleRingedDerivedPullback.{u, 0} Λ y.hom).map φ) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight Φ.counitIso
        (etaleRingedDerivedPullback.{u, 0} Λ y.hom) ≪≫ Functor.leftUnitor _).symm φ).1 (h y)
  have h₂ : IsIso ((etaleDerivedEquivalence.{u, 0} Λ y.source).functor.map
      ((etaleModuleDerivedInverseImage.{u, 0} Λ y.hom).map (Φ.inverse.map φ))) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerLeft Φ.inverse
      (etaleRingedDerivedPullbackIso.{u, 0} Λ y.hom)) φ).1 h₁
  exact isIso_of_fully_faithful (etaleDerivedEquivalence.{u, 0} Λ y.source).functor _

end Stacks.EtaleCohomology

end
