module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexCompactGeneratorEquivalence

/-!
# K-injective representatives of the shape the derived tensor product consumes

Let `(C, O)` be a ringed site whose objects, morphisms and structure sheaf live in one universe
`u`, and take the complexes of `O`-modules with sections in that same universe. Then the ambient
category of `O`-modules in which the derived tensor product of Tag 09LX is formed is the category
of `O`-modules itself, and the universe-raising embedding `liftComplex` is isomorphic to the
identity. Every object of `D(O)` is therefore isomorphic to `liftComplex K` for a complex `K`
with `liftComplex K` K-injective: take a K-injective resolution (Tag 079P).

## Main definitions

* `AlgebraicGeometry.RingedSite.moduleULiftSelfIso`: at equal universes, raising the universe of
  sections is isomorphic to the identity.
* `AlgebraicGeometry.RingedSite.liftComplexSelfIso`: hence `liftComplex K ≅ K`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_isKInjective_liftComplex_iso`: every object of `D(O)` is
  isomorphic to `liftComplex K` for some `K` with `liftComplex K` K-injective.

## References

* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})

/-- At equal universes, raising the universe of the sections of an `O`-module is isomorphic to
the identity: sectionwise it is `ULift`. -/
def moduleULiftSelfIso :
    Stacks.SheafOfModules.moduleULift.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      𝟭 (ModO.{u, u, u, u} X) :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U => by
          change ModuleCat.of _ (ULift.{u} (M.val.obj U)) ≅ M.val.obj U
          exact ULift.moduleEquiv.toModuleIso)
        (fun {_ _} _ => by ext ⟨x⟩; rfl)))
    (fun {_ _} _ => by ext; rfl)

/-- At equal universes, the universe-raising embedding of complexes is isomorphic to the
identity. -/
def liftComplexSelfIso (K : CochainComplex (ModO.{u, u, u, u} X) ℤ) :
    liftComplex.{u, u, u, u, u} X K ≅ K :=
  (NatIso.mapHomologicalComplex (moduleULiftSelfIso X) (ComplexShape.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ _).app K

/-- **Every object of `D(O)` has a K-injective representative of the shape the derived tensor
product of Tag 09LX consumes**: an object `G` of `D(O)`, at the standard model
`CategoryTheory.HasDerivedCategory.standard` on which Tag 09LX is built, is isomorphic to
`liftComplex K` for a complex `K` of `O`-modules such that `liftComplex K` is K-injective.

The model is explicit in the statement: at equal universes the locally small global instance
`SheafOfModules.hasDerivedCategory` would otherwise be found instead. -/
theorem exists_isKInjective_liftComplex_iso
    (G : @DerivedCategory (TensorModO.{u, u, u, u, u} X) _ _ (HasDerivedCategory.standard _)) :
    ∃ K : CochainComplex (ModO.{u, u, u, u} X) ℤ,
      (liftComplex.{u, u, u, u, u} X K).IsKInjective ∧
        Nonempty ((@DerivedCategory.Q (TensorModO.{u, u, u, u, u} X) _ _
          (HasDerivedCategory.standard _)).obj (liftComplex.{u, u, u, u, u} X K) ≅ G) := by
  let : HasDerivedCategory (TensorModO.{u, u, u, u, u} X) := HasDerivedCategory.standard _
  let _ : IsGrothendieckAbelian.{u} (TensorModO.{u, u, u, u, u} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, u, u, u} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let M := DerivedCategory.Q.objPreimage G
  let I : CochainComplex (ModO.{u, u, u, u} X) ℤ :=
    (Stacks.Injectives.kInjectiveResolutionFunctor (TensorModO.{u, u, u, u, u} X)).obj M
  have hI : I.IsKInjective :=
    inferInstanceAs ((Stacks.Injectives.kInjectiveResolutionFunctor
      (TensorModO.{u, u, u, u, u} X)).obj M).IsKInjective
  refine ⟨I, CochainComplex.isKInjective_of_iso (liftComplexSelfIso X I).symm, ⟨?_⟩⟩
  have : IsIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion
        (TensorModO.{u, u, u, u, u} X)).app M)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact DerivedCategory.Q.mapIso (liftComplexSelfIso X I) ≪≫
    (asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion
      (TensorModO.{u, u, u, u, u} X)).app M))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso G

end AlgebraicGeometry.RingedSite

end
