module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalKFlat

/-!
# The unit of the monoidal structure of `Lf^*`

For a morphism of ringed spaces `f : X ⟶ Y`, at the locally small model, the lax unit
`𝒪_X[0] ⟶ Lf^*(𝒪_Y[0])` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal` is the inverse of the
comparison `Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIsoLocallySmall`, through
which `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` is computed degreewise ([Stacks, Tag 06YJ]).

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open CochainComplex.KFlatBifunctor RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory
  abelianStructureSheafRing

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The bookkeeping behind `ε_pullbackComplex_comp`, in an arbitrary category. -/
private lemma comp_eq_id_aux {C : Type*} [Category C] {P Q S A B : C} {e : P ⟶ Q} {a : Q ⟶ A}
    {b : A ⟶ S} {s : S ⟶ A} {n : A ⟶ B} {ni : B ⟶ A} {s₀ : P ⟶ B} {si : B ⟶ P}
    (h : e ≫ a = s₀ ≫ ni) (hb : b ≫ s = 𝟙 A) (hn : ni ≫ n = 𝟙 B) (hs : s₀ ≫ si = 𝟙 P) :
    e ≫ (a ≫ b) ≫ s ≫ n ≫ si = 𝟙 P := by
  rw [Category.assoc, reassoc_of% hb, reassoc_of% h, reassoc_of% hn, hs]

/-- **The unit of `f^*` on complexes is `ν⁻¹` in degree zero**: followed by the identification of
`f^*` with `f^*` degreewise on single complexes and by `ν : f^*𝒪_Y ≅ 𝒪_X`, it is the identity. -/
theorem ε_pullbackComplex_comp :
    Functor.LaxMonoidal.ε (pullbackComplex f) ≫
        (HomologicalComplex.singleMapHomologicalComplex (StacksDraft.KFlat.modulePullback f)
          (ComplexShape.up ℤ) 0).hom.app
            (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (modulePullbackObjUnitIso f).hom = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  have h := epsilon_pullbackComplex_zero f
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  refine (congrArg (fun x => _ ≫ (_ ≫ _) ≫ x)
    (HomologicalComplex.single_map_f_self (c := ComplexShape.up ℤ) 0
      (modulePullbackObjUnitIso f).hom)).trans ?_
  exact comp_eq_id_aux h (Iso.inv_hom_id _) (Iso.inv_hom_id _) (Iso.hom_inv_id _)

/-- The bookkeeping behind `derivedPullbackCanonicalMonoidal_ε_eq`, in an arbitrary category. -/
private lemma comp_eq_id_aux' {C : Type*} [Category C] {S T T' U V W Z : C} {ε : S ⟶ T}
    {a a' : T ⟶ T'} {b : T' ⟶ U} {c : U ⟶ V} {d : V ⟶ W} {q : S ⟶ W} {e : W ⟶ Z}
    {g : Z ⟶ Z} {h : Z ⟶ S}
    (ha : a = a') (hε : ε ≫ a' ≫ b ≫ c ≫ d = q) (hg : g = 𝟙 Z) (hq : q ≫ e ≫ h = 𝟙 S) :
    ε ≫ a ≫ b ≫ c ≫ d ≫ e ≫ g ≫ h = 𝟙 S := by
  subst ha hg
  rw [Category.id_comp, reassoc_of% hε, hq]

/-- **The unit of `Lf^*` is `Lf^*𝒪_Y ≅ 𝒪_X`**: at the locally small model, the lax unit of
`derivedPullbackCanonicalMonoidal` is the inverse of
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIsoLocallySmall`. -/
theorem derivedPullbackCanonicalMonoidal_ε_eq :
    @Functor.LaxMonoidal.ε _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toLaxMonoidal =
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIsoLocallySmall f).inv := by
  refine (Iso.comp_hom_eq_id _).1 ?_
  exact comp_eq_id_aux'
    (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app _ _ |>.trans rfl |> congrArg
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map)
    (derivedPullbackCanonicalMonoidal_ε_comp f) rfl
    ((congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _).symm).trans
      ((DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
        (ε_pullbackComplex_comp f)).trans (DerivedCategory.Q.map_id _))))

end Stacks.Cohomology.DerivedPullbackTensor
