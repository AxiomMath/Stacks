module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.StalkTorsionOfSupportedComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Stacks 0AET at the stalk ring of the point of the site

Stacks 0AET
(`AlgebraicGeometry.Space.isIPowerTorsion_geometricModuleStalk_homology_of_cohomologySupportedOn`)
says that for `Q ∈ D_QCoh(𝒪_X)` supported on a finitely presented closed subspace `Z`, the
geometric stalk `Hⁿ(Q)_x̄` is `I_x̄`-power torsion, as a module over the étale local ring
`𝒪_{X,x̄}` of Stacks 04KG. The derived geometric stalk
`AlgebraicGeometry.Space.geometricDerivedStalk` used in the stalkwise proof of Stacks 0AEU, and in
the stalk formula for derived pullbacks, is formed over the stalk ring of the point of the site,
`AlgebraicGeometry.Space.geometricStalkRing`, which `AlgebraicGeometry.Space.pointStalkRingEquiv`
identifies with `𝒪_{X,x̄}`. This file moves the torsion statement across that identification.

## Main results

* `AlgebraicGeometry.Space.isIPowerTorsion_moduleStalk_of_geometricModuleStalk`: a module over
  the étale local ring which is `I`-power torsion gives an `I'`-power torsion module over the
  stalk ring of the point, `I'` the pullback of `I` along `pointStalkRingEquiv`.
* `AlgebraicGeometry.Space.isIPowerTorsion_homology_geometricDerivedStalk`: **Stacks 0AET for the
  cohomology of the derived geometric stalk.** For `Q` as above, every `Hⁿ(Q_x̄)` is `I'`-power
  torsion over the stalk ring of the point.
* `AlgebraicGeometry.Space.isIso_iff_forall_isIso_geometricDerivedStalk_map`: a morphism of
  `D(𝒪_X)` is invertible exactly when all its derived geometric stalks are.

## Main definitions

* `AlgebraicGeometry.Space.DerivedPullbackCohomologySupportedOnStatement`: the proposition that
  `Lg^*` carries complexes supported on `T` to complexes supported on `|g|⁻¹T`, which
  `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback` proves.

## Implementation notes

The two stalks of a module are compared by the additive isomorphism
`AlgebraicGeometry.Space.geometricModuleStalkAddEquiv` (semilinear along `pointStalkRingEquiv`)
and the linear isomorphism `Stacks.moduleStalkLargeLinearEquiv`. The cohomology of the derived
stalk is the stalk of the cohomology sheaf by
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`, the stalk functor being exact.

## References

* [Stacks Project, Tag 0AET](https://stacks.math.columbia.edu/tag/0AET)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ideal of the stalk ring of the point of the site corresponding to an ideal of the étale
local ring, along `AlgebraicGeometry.Space.pointStalkRingEquiv`. -/
abbrev pointStalkIdeal (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (I : Ideal (etaleLocalRing B S hS X.1 x)) :
    Ideal (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O.obj) :=
  I.comap (pointStalkRingEquiv B S hS X x).toRingHom

/-- Power torsion pulls back along an injective map that is semilinear over a ring map `σ`. -/
private theorem isIPowerTorsion_of_injective_smul {R R' M N : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] {σ : R →+* R'} (f : M → N)
    (hf : Function.Injective f) (h0 : f 0 = 0) (hs : ∀ (a : R) (m : M), f (a • m) = σ a • f m)
    {I : Ideal R} {I' : Ideal R'} (h : IsIPowerTorsion R' N I') (hI : I ≤ I'.comap σ) :
    IsIPowerTorsion R M I := by
  intro m
  obtain ⟨n, hn, hm⟩ := h (f m)
  refine ⟨n, hn, fun a ha ↦ hf ?_⟩
  rw [hs, h0]
  exact hm _ (Ideal.le_comap_pow _ n ((Ideal.pow_right_mono hI n) ha))

/-- **Power torsion moves from the geometric module stalk to the stalk at the point of the
site.** If the stalk of `F` at `x̄`, as a module over the étale local ring, is `I`-power torsion,
then the stalk of `F` at the point of the small étale site attached to `x̄`, as a module over the
stalk ring of that point, is power torsion for the corresponding ideal. -/
theorem isIPowerTorsion_moduleStalk_of_geometricModuleStalk (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (I : Ideal (etaleLocalRing B S hS X.1 x))
    (h : IsIPowerTorsion (etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x F) I) :
    IsIPowerTorsion (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj)
      (Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O F)
      (pointStalkIdeal B S hS X x I) := by
  let e₁ := (Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O F).symm
  let e₂ := geometricModuleStalkAddEquiv B S hS X x F
  refine isIPowerTorsion_of_injective_smul (σ := (pointStalkRingEquiv B S hS X x).toRingHom)
    (fun m ↦ e₂ (e₁ m)) (e₂.injective.comp e₁.injective) ?_ ?_ h le_rfl
  · exact (congrArg e₂ (map_zero e₁)).trans (map_zero e₂)
  · intro a m
    exact (congrArg e₂ (e₁.map_smul a m)).trans
      (geometricModuleStalkAddEquiv_smul B S hS X x F a (e₁ m))

/-- **Stacks 0AET for the cohomology of the derived geometric stalk.** Let `Q ∈ D_QCoh(𝒪_X)`
have its cohomology sheaves supported on a closed subspace `Z` of finite presentation. At every
geometric point `x̄` of `X` and in every degree `n`, the cohomology `Hⁿ(Q_x̄)` of the derived
geometric stalk (`AlgebraicGeometry.Space.geometricDerivedStalk`, which is
`Stacks.derivedModuleFiber` at the point of the site) is power torsion for the stalk of the ideal
of `Z`, as a module over the stalk ring of the point of the site. -/
theorem isIPowerTorsion_homology_geometricDerivedStalk (X : AlgebraicSpaces B S hS)
    [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (Z : ClosedSubspaces B S hS X.1) (hZ : IsFinitePresentation B S hS Z.1.ι)
    (Q : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hQ : CohomologySupportedOn B S hS X.1 X.2
      (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι)) Q.1)
    (x : GeometricPoint B S hS X.1) (n : ℤ) :
    IsIPowerTorsion (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u}
          (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
            (smallEtaleRingedTopos B S hS X).O.obj)) n).obj
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O).obj Q.1))
      (pointStalkIdeal B S hS X x (closedSubspaceStalkIdeal B S hS X Z x)) := by
  have h := isIPowerTorsion_moduleStalk_of_geometricModuleStalk B S hS X x _ _
    (isIPowerTorsion_geometricModuleStalk_homology_of_cohomologySupportedOn B S hS X Z hZ Q hQ
      x n)
  let e := ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryHomologyFunctorIso n).app Q.1
  exact isIPowerTorsion_of_injective_smul (σ := RingHom.id _) e.hom.hom
    ((ModuleCat.mono_iff_injective e.hom).1 inferInstance) (map_zero e.hom.hom)
    (e.hom.hom.map_smul) h le_rfl

/-! ### Isomorphisms are detected on derived geometric stalks -/

/-- **A morphism of `D(𝒪_X)` is invertible exactly when all its derived geometric stalks are.**
The derived geometric stalk (`AlgebraicGeometry.Space.geometricDerivedStalk`, which is
`Stacks.derivedModuleFiber` at the point of the site) commutes with cohomology, the stalk functor
being exact, and the geometric stalks of modules detect isomorphisms (Stacks 04K5). -/
theorem isIso_iff_forall_isIso_geometricDerivedStalk_map (X : AlgebraicSpaces B S hS)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (φ : K ⟶ L) :
    IsIso φ ↔ ∀ x : GeometricPoint B S hS X.1, IsIso ((geometricDerivedStalk B S hS x).map φ) := by
  refine ⟨fun _ x ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2
    (ringedToposStructureRingSheaf B S hS X) _ fun x ↦ ?_
  have h₀ : IsIso ((geometricDerivedStalk B S hS x ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} (geometricStalkRing B S hS x)) n).map φ) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((geometricDerivedStalk B S hS x).map φ)))
  have h₁ : IsIso ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O).map
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) n).map φ)) :=
    (NatIso.isIso_map_iff ((Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryHomologyFunctorIso n) φ).1 h₀
  have h₂ : IsIso ((forget₂ _ AddCommGrpCat.{u}).map
      ((geometricModuleStalkFunctor B S hS X.1 X.2 (ringedToposStructureRingSheaf B S hS X) x).map
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) n).map φ))) :=
    Functor.map_isIso (forget₂ _ AddCommGrpCat.{u}) ((Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O).map
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) n).map φ))
  exact (isIso_iff_of_reflects_iso _ (forget₂ _ AddCommGrpCat.{u})).1 h₂

/-! ### The shape of the support step for derived pullbacks -/

/-- **The statement that derived pullback preserves supports**: for a morphism `g : X' ⟶ X` of
algebraic spaces and `E ∈ D(𝒪_X)` with cohomology supported on `T ⊆ |X|`, the cohomology of
`Lg^*E` is supported on `|g|⁻¹ T`. It is proved by
`AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback`. -/
def DerivedPullbackCohomologySupportedOnStatement : Prop :=
  ∀ {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) {T : Set (points B S hS X.1)}
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
    CohomologySupportedOn B S hS X.1 X.2 T E →
      CohomologySupportedOn B S hS X'.1 X'.2 (pointsMap B S hS X'.1 g.hom ⁻¹' T)
        ((smallEtaleDerivedModulePullback B S hS g).obj E)

end AlgebraicGeometry.Space

end
