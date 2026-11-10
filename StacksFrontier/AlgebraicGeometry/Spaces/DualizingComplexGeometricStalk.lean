module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionAtLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange

/-!
# The geometric stalks of a dualizing complex on an algebraic space

Let `X` be a locally Noetherian algebraic space and `K` an object of `D(𝒪_X)` whose restriction to
an étale chart `h_U ⟶ X` is `ε^*ω_U` for a dualizing complex `ω_U` on the scheme `U` (Stacks
0E4X). This file computes the normalizing shift of the geometric stalks of `K` over the points of
`U`, which is the input of the proof of Stacks 0E53.

## Main results

* `AlgebraicGeometry.Space.nonempty_geometricDerivedStalk_etaleModulePullback_iso`: the stalk of
  an étale pullback at a geometric point is the stalk at the image point base changed along the
  homomorphism of geometric stalk rings (Stacks 05V5 with the matched pair of Stacks 04K2), which
  is bijective (`AlgebraicGeometry.Space.bijective_smallEtaleStalkPullbackRingMap`).
* `AlgebraicGeometry.Space.isNormalizedDualizingComplex_geometricDerivedStalk_restriction`:
  normalized geometric stalks ascend along an étale chart.
* `AlgebraicGeometry.Space.nonempty_geometricDerivedStalk_representedTilde_iso`: **the derived
  stalk comparison** — the geometric stalk of `ε^*(M~)` on an affine chart `Spec A` is
  `M ⊗_A 𝒪_{X, x̄}`, from the abelian comparison
  `AlgebraicGeometry.Space.representedAffineAssociatedModuleStalkIso`.
* `AlgebraicGeometry.Space.isNormalizedDualizingComplex_extendScalars_geometricStalkRing`: the
  base change of a dualizing complex `M` over `A` to the geometric stalk ring is normalized after
  the shift by the dualizing dimension of `M` at the prime of the point (Stacks 04KF and 0AWD).
* `AlgebraicGeometry.Space.exists_geometricPoint_isNormalizedDualizingComplex`: over every point
  `y` of `U` there is a geometric point of `X` at which the normalizing shift of `K` is the value
  at `y` of the dimension function of Stacks 0AWF for `ω_U`.

## Implementation notes

The geometric stalk is `AlgebraicGeometry.Space.geometricDerivedStalk`, over the stalk
`AlgebraicGeometry.Space.geometricStalkRing` of the structure sheaf at the point of the small
étale site of Stacks 04K0; it is local and, on a locally Noetherian space, Noetherian
(`AlgebraicGeometry.Space.isNoetherianRing_geometricStalkRing`).

Several functors here have two definitionally equal spellings of their source or target category
— the modules of the small étale ringed site and the modules over the structure ring sheaf of the
small étale ringed topos — whose instances are not found across the spellings; the functors are
therefore retyped (`AlgebraicGeometry.Space.representedAssociatedModuleTopos`) and their exactness
instances supplied with `haveI` where instance search does not reach them.

## References

* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0E53](https://stacks.math.columbia.edu/tag/0E53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Dualizing

/-- A normalized dualizing complex stays normalized under extension of scalars along a bijective
homomorphism of Noetherian local rings: such a homomorphism is flat and local and carries the
maximal ideal onto the maximal ideal, so Stacks 0AWD applies. -/
theorem isNormalizedDualizingComplex_extendScalars_of_bijective {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (g : A →+* B) (hg : Function.Bijective g) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (RingHom.Flat.of_bijective hg)
    IsNormalizedDualizingComplex.{u, u}
      ((ModuleCat.extendScalars.{u, u, u} g).mapDerivedCategory.obj K) := by
  let : Algebra A B := g.toAlgebra
  let : Module.Flat A B := RingHom.Flat.of_bijective hg
  let : IsLocalHom (algebraMap A B) := IsLocalHom.of_surjective g hg.2
  exact isNormalizedDualizingComplex_extendScalars_of_flat.{u, u, u}
    (IsLocalRing.map_maximalIdeal_of_surjective g hg.2) K hK

end Dualizing

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The geometric stalk ring `𝒪_{X, x̄}` is local, being isomorphic to the étale local ring
(Stacks 04KG, 04KH). -/
instance isLocalRing_geometricStalkRing (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) : IsLocalRing (geometricStalkRing B S hS x) :=
  haveI := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  (pointStalkRingEquiv B S hS X x).symm.isLocalRing

/-- The geometric stalk ring of a locally Noetherian algebraic space is Noetherian, being
isomorphic to the étale local ring, which is the strict henselization of a Noetherian local
ring. -/
theorem isNoetherianRing_geometricStalkRing (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : GeometricPoint B S hS X.1) : IsNoetherianRing (geometricStalkRing B S hS x) :=
  have := isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS X.1 X.2 hN x
  isNoetherianRing_of_ringEquiv _ (pointStalkRingEquiv B S hS X x).symm

/-- Along an étale morphism of algebraic spaces the homomorphism of geometric stalk rings of
Stacks 05V5 is bijective: read on the étale local rings it is the homomorphism of Stacks 04NG,
which along an étale morphism is the inverse of the comparison of the two étale local rings
(`AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale`). -/
theorem bijective_smallEtaleStalkPullbackRingMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (x : GeometricPoint B S hS X.1) :
    Function.Bijective (smallEtaleStalkPullbackRingMap B S hS f x) := by
  have h := pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS f x
  have he : etaleLocalRingMap X.2 f.hom x = (etaleLocalRingIsoOfIsEtale B S hS f hf x).inv.hom :=
    (eq_etaleLocalRingMap X.2 f.hom x
      (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS f hf x)).symm
  rw [he] at h
  have hb : Function.Bijective ((pointStalkRingEquiv B S hS X x).toRingHom.comp
      (smallEtaleStalkPullbackRingMap B S hS f x)) := by
    rw [h]
    exact ((ConcreteCategory.bijective_of_isIso
      (etaleLocalRingIsoOfIsEtale B S hS f hf x).inv)).comp
      (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).bijective
  exact (Function.Bijective.of_comp_iff' (pointStalkRingEquiv B S hS X x).bijective _).mp hb

/-- The stalk functor at a geometric point of an algebraic space, on modules over the structure ring
sheaf of the small étale ringed topos. -/
private abbrev geometricStalkFunctor (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
      ModuleCat.{u} (((etaleSitePoint B S hS X.1 x X.2).presheafFiber
        (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :=
  Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O

/-- The stalk functor at a geometric point is additive and preserves finite limits and finite
colimits. -/
private theorem geometricStalkFunctor_exact (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) :
    (geometricStalkFunctor B S hS X x).Additive ∧
      PreservesFiniteLimits (geometricStalkFunctor B S hS X x) ∧
      PreservesFiniteColimits (geometricStalkFunctor B S hS X x) :=
  ⟨Stacks.additive_sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O,
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O,
    Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O⟩

/-- Extension of scalars along a bijective ring homomorphism preserves finite limits. -/
private theorem preservesFiniteLimits_extendScalars_of_bijective {A C : Type u} [CommRing A]
    [CommRing C] (g : A →+* C) (hg : Function.Bijective g) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (RingHom.Flat.of_bijective hg)

/-- **The geometric stalk of an étale pullback.** For an étale morphism `f : X ⟶ Y` of algebraic
spaces, a geometric point `x̄` of `X` and `K ∈ D(𝒪_Y)`, the stalk of `f^*K` at `x̄` is the stalk
of `K` at `f(x̄)` with its scalars extended along the homomorphism of geometric stalk rings: this
is Stacks 05V5 at the matched pair of points of Stacks 04K2, read on derived categories, with the
pullback of modules identified with étale restriction by Stacks 03LW. -/
theorem nonempty_geometricDerivedStalk_etaleModulePullback_iso {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    letI := etaleModulePullback_additive.{u, u} B S hS f hf
    letI := preservesFiniteLimits_etaleModulePullback B S hS f hf
    letI := preservesFiniteColimits_etaleModulePullback B S hS f hf
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
        (smallEtaleStalkPullbackRingMap B S hS f x)) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
        (RingHom.Flat.of_bijective (bijective_smallEtaleStalkPullbackRingMap B S hS f hf x))
    Nonempty ((geometricDerivedStalk B S hS x).obj
        ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj K) ≅
      (ModuleCat.extendScalars.{u, u, u}
          (smallEtaleStalkPullbackRingMap B S hS f x)).mapDerivedCategory.obj
        ((geometricDerivedStalk B S hS (geometricPointMap f.hom x)).obj K)) := by
  let := etaleModulePullback_additive.{u, u} B S hS f hf
  let := preservesFiniteLimits_etaleModulePullback B S hS f hf
  let := preservesFiniteColimits_etaleModulePullback B S hS f hf
  let := preservesFiniteLimits_extendScalars_of_bijective _
    (bijective_smallEtaleStalkPullbackRingMap B S hS f hf x)
  let T : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) :=
    etaleModulePullback.{u, u} B S hS f hf
  have : T.Additive := etaleModulePullback_additive.{u, u} B S hS f hf
  have : PreservesFiniteLimits T := preservesFiniteLimits_etaleModulePullback B S hS f hf
  have : PreservesFiniteColimits T := preservesFiniteColimits_etaleModulePullback B S hS f hf
  obtain ⟨_, _, _⟩ := geometricStalkFunctor_exact B S hS X x
  obtain ⟨_, _, _⟩ := geometricStalkFunctor_exact B S hS Y (geometricPointMap f.hom x)
  let e : T ⋙ geometricStalkFunctor B S hS X x ≅
      geometricStalkFunctor B S hS Y (geometricPointMap f.hom x) ⋙
        ModuleCat.extendScalars.{u, u, u} (smallEtaleStalkPullbackRingMap B S hS f x) :=
    Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS f hf).symm _ ≪≫
      Stacks.Sheaves.StalkPullback.stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
        (etaleSitePoint B S hS X.1 x X.2)
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleInverseImageFiberIso B S hS f x)
  exact ⟨(Functor.mapDerivedCategorySquareIso e).app K⟩

/-- The geometric stalk ring of the source of an étale chart is Noetherian when that of the
target point is: the homomorphism of geometric stalk rings is bijective. -/
theorem isNoetherianRing_geometricStalkRing_of_etale (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X.1) (hψ : IsEtale B S hS ψ)
    (p : GeometricPoint B S hS (yoneda.obj V)) :
    IsNoetherianRing (geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p) := by
  let f : (⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk ψ
  have : IsNoetherianRing (Stacks.ringFiber
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom p) X.2)
      (smallEtaleRingedTopos B S hS X).O.obj) :=
    isNoetherianRing_geometricStalkRing B S hS X hN (geometricPointMap ψ p)
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective _
    (bijective_smallEtaleStalkPullbackRingMap B S hS f hψ p))

/-- The local ring at a point `z` of an affine open `W` of a scheme, read on the open subscheme
`W`, is the localization of `Γ(Z, W)` at the prime of `z`, along the germ at `z` of the global
section of `W` attached to an element of `Γ(Z, W)`. -/
theorem isLocalization_stalk_toScheme {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)
    (z : W) :
    letI : Algebra Γ(Z, W) ((W : Scheme.{u}).presheaf.stalk z) :=
      ((W : Scheme.{u}).presheaf.germ ⊤ z trivial).hom.comp W.topIso.inv.hom |>.toAlgebra
    IsLocalization.AtPrime ((W : Scheme.{u}).presheaf.stalk z) (hW.primeIdealOf z).asIdeal := by
  let : Algebra Γ(Z, W) ((W : Scheme.{u}).presheaf.stalk z) :=
    ((W : Scheme.{u}).presheaf.germ ⊤ z trivial).hom.comp W.topIso.inv.hom |>.toAlgebra
  have := hW.isLocalization_stalk z
  let e := (W.stalkIso z).symm.commRingCatIsoToRingEquiv
  refine IsLocalization.isLocalization_of_algEquiv (hW.primeIdealOf z).asIdeal.primeCompl
    { e with commutes' := fun a => ?_ }
  change (W.stalkIso z).inv.hom (Z.presheaf.germ W z.1 z.2 a) =
    ((W : Scheme.{u}).presheaf.germ ⊤ z trivial).hom (W.topIso.inv.hom a)
  rw [← Scheme.Opens.germ_stalkIso_inv W ⊤ z trivial]
  refine congrArg (W.stalkIso z).inv.hom ?_
  simp only [Scheme.Opens.topIso_inv]
  exact (Z.presheaf.germ_res_apply (homOfLE (by simp)) z.1 _ a).symm

/-- The geometric stalk ring of a represented algebraic space whose scheme is locally Noetherian
is Noetherian: by Stacks 04KF it is the strict henselization of a Noetherian local ring. -/
theorem isNoetherianRing_geometricStalkRing_yoneda (V : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (p : GeometricPoint B S hS (yoneda.obj V)) :
    IsNoetherianRing (geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p) := by
  let N := selfNeighborhood B S hS V p
  let R := chartLocalRing B S hS (yoneda.obj V) N
  let κ := separableClosure (IsLocalRing.ResidueField R) (chartGeometricPoint N).residueField
  let Tw := chartHenselizationTower B S hS (yoneda.obj V) N
  have : IsLocallyNoetherian (chartScheme N.chart) :=
    inferInstanceAs (IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
  have : IsNoetherianRing R := inferInstanceAs
    (IsNoetherianRing ((chartScheme N.chart).presheaf.stalk (chartPoint B S hS (yoneda.obj V) N)))
  have : IsNoetherianRing Tw.strictHenselization :=
    ((isNoetherianRing_iff_henselizations R Tw.henselization Tw.strictHenselization κ).2).mp
      inferInstance
  exact isNoetherianRing_of_ringEquiv _ ((chartStrictHenselizationEquiv B S hS (yoneda.obj V)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) N).trans
      (pointStalkRingEquiv B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p).symm)

/-- **The geometric stalk of a model, normalized.** Let `V` be an object of the big fppf site over
`S` with locally Noetherian scheme, `p` a geometric point of `h_V` and `N` its canonical
neighbourhood. Let `A` be a Noetherian ring with a homomorphism `α` into the local ring `𝒪_{V, v}`
of the chart at the point under `p` presenting it as the localization of `A` at a prime `P`, and
let `γ : A → 𝒪_{h_V, p}` be the homomorphism to the geometric stalk ring which, read on the étale
local ring, is `α` followed by the comparison of Stacks 05VP. Then for a dualizing complex `M` over
`A`, the base change of `M` to the geometric stalk ring, shifted by the dualizing dimension of `M`
at `P`, is a normalized dualizing complex: `γ` is the localization at `P` followed by the strict
henselization of Stacks 04KF, and Stacks 0AWD applies to the second step. -/
theorem isNormalizedDualizingComplex_extendScalars_geometricStalkRing (V : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (p : GeometricPoint B S hS (yoneda.obj V)) (A : CommRingCat.{u}) [IsNoetherianRing A]
    (P : PrimeSpectrum A)
    (α : A →+* chartLocalRing B S hS (yoneda.obj V) (selfNeighborhood B S hS V p))
    (hα : letI := α.toAlgebra
      IsLocalization.AtPrime (chartLocalRing B S hS (yoneda.obj V) (selfNeighborhood B S hS V p))
        P.asIdeal)
    (γ : A →+* geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p)
    (hγ : ∀ a : A, pointStalkRingEquiv B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p (γ a) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj V)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) (selfNeighborhood B S hS V p) (α a))
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : Dualizing.IsDualizingComplex M)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} γ)] :
    letI := isNoetherianRing_geometricStalkRing_yoneda B S hS V p
    letI := isLocalRing_geometricStalkRing B S hS
      ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((ModuleCat.extendScalars.{u, u, u} γ).mapDerivedCategory.obj
        M⟦-Dualizing.dualizingDimension.{u, u} M P⟧) := by
  let Xp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩
  let N := selfNeighborhood B S hS V p
  let R := chartLocalRing B S hS (yoneda.obj V) N
  let κ := separableClosure (IsLocalRing.ResidueField R) (chartGeometricPoint N).residueField
  let Tw := chartHenselizationTower B S hS (yoneda.obj V) N
  let E : Tw.strictHenselization ≃+* geometricStalkRing B S hS (X := Xp) p :=
    (chartStrictHenselizationEquiv B S hS (yoneda.obj V)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) N).trans
      (pointStalkRingEquiv B S hS Xp p).symm
  let : Algebra A R := α.toAlgebra
  have := hα
  have : IsLocallyNoetherian (chartScheme N.chart) :=
    inferInstanceAs (IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
  have : IsNoetherianRing R := inferInstanceAs
    (IsNoetherianRing ((chartScheme N.chart).presheaf.stalk (chartPoint B S hS (yoneda.obj V) N)))
  have : IsNoetherianRing Tw.strictHenselization :=
    ((isNoetherianRing_iff_henselizations R Tw.henselization Tw.strictHenselization κ).2).mp
      inferInstance
  let := isNoetherianRing_geometricStalkRing_yoneda B S hS V p
  let := isLocalRing_geometricStalkRing B S hS Xp p
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R P.asIdeal
  have : Module.Flat R Tw.strictHenselization := IsLocalRing.IsHenselization.flat (L := κ)
  have : IsLocalHom (algebraMap R Tw.strictHenselization) :=
    IsLocalRing.IsHenselization.isLocalHom (L := κ)
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R Tw.strictHenselization) =
      IsLocalRing.maximalIdeal Tw.strictHenselization :=
    IsLocalRing.IsHenselization.map_maximalIdeal (R := R) (Rh := Tw.strictHenselization) (L := κ)
  have hγeq : γ = E.toRingHom.comp ((algebraMap R Tw.strictHenselization).comp α) := by
    ext a
    apply (pointStalkRingEquiv B S hS Xp p).injective
    rw [hγ a]
    change _ = (pointStalkRingEquiv B S hS Xp p) ((pointStalkRingEquiv B S hS Xp p).symm _)
    rw [RingEquiv.apply_symm_apply]
    rfl
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A R)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat R P.asIdeal.primeCompl))
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (algebraMap R Tw.strictHenselization)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let := preservesFiniteLimits_extendScalars_of_bijective E.toRingHom E.bijective
  set n := Dualizing.dualizingDimension.{u, u} M P
  have h0 := Dualizing.isNormalizedDualizingComplex_extendScalars_dualizingDimension M hM P R
  have h1 := Dualizing.isNormalizedDualizingComplex_extendScalars_of_flat.{u, u, u} hmax _ h0
  have h2 := Dualizing.isNormalizedDualizingComplex_extendScalars_of_bijective E.toRingHom
    E.bijective _ h1
  refine (Dualizing.isNormalizedDualizingComplex_congr.{u, u} ?_).mp h2
  let Fα := ModuleCat.extendScalars.{u, u, u} (algebraMap A R)
  let Fh := ModuleCat.extendScalars.{u, u, u} (algebraMap R Tw.strictHenselization)
  let FE := ModuleCat.extendScalars.{u, u, u} E.toRingHom
  let c : (Fα ⋙ Fh) ⋙ FE ≅ ModuleCat.extendScalars.{u, u, u} γ :=
    (Functor.isoWhiskerRight (ModuleCat.extendScalarsComp (algebraMap A R)
        (algebraMap R Tw.strictHenselization)).symm FE) ≪≫
      (ModuleCat.extendScalarsComp _ E.toRingHom).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars hγeq.symm)
  exact FE.mapDerivedCategory.mapIso (((Fh.mapDerivedCategory.commShiftIso (-n)).app _)) ≪≫
    ((FE.mapDerivedCategory.commShiftIso (-n)).app _) ≪≫
    (shiftFunctor _ (-n)).mapIso
      (FE.mapDerivedCategory.mapIso
          ((Stacks.DerivedGlueing.mapDerivedCategoryCompIso Fα Fh).app M) ≪≫
        (Stacks.DerivedGlueing.mapDerivedCategoryCompIso (Fα ⋙ Fh) FE).app M ≪≫
        (Stacks.DerivedGlueing.mapDerivedCategoryCongr c).app M)

/-- **Normalized geometric stalks ascend along an étale chart.** If the stalk of `K` at the image
`ψ(p)` of a geometric point `p` of `h_V` is, shifted by `-m`, a normalized dualizing complex, then
so is the stalk of `K|_V` at `p`. -/
theorem isNormalizedDualizingComplex_geometricDerivedStalk_restriction (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X.1) (hψ : IsEtale B S hS ψ)
    (p : GeometricPoint B S hS (yoneda.obj V)) (m : ℤ)
    (hm : letI := isNoetherianRing_geometricStalkRing B S hS X hN (geometricPointMap ψ p)
      Dualizing.IsNormalizedDualizingComplex.{u, u}
        ((geometricDerivedStalk B S hS (geometricPointMap ψ p)).obj K⟦-m⟧)) :
    letI := isNoetherianRing_geometricStalkRing_of_etale B S hS X hN V ψ hψ p
    letI := isLocalRing_geometricStalkRing B S hS
      ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((geometricDerivedStalk B S hS
          (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p).obj
        ((representedChartDerivedRestriction B S hS X.2 V ψ hψ).obj K)⟦-m⟧) := by
  let f : (⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk ψ
  obtain ⟨eC1⟩ := nonempty_geometricDerivedStalk_etaleModulePullback_iso B S hS f hψ p K
  have hg := bijective_smallEtaleStalkPullbackRingMap B S hS f hψ p
  let : IsNoetherianRing
      (Stacks.ringFiber (etaleSitePoint B S hS X.1 (geometricPointMap f.hom p) X.2)
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    isNoetherianRing_geometricStalkRing B S hS X hN (geometricPointMap ψ p)
  let : IsLocalRing (Stacks.ringFiber (etaleSitePoint B S hS X.1 (geometricPointMap f.hom p) X.2)
      (smallEtaleRingedTopos B S hS X).O.obj) :=
    isLocalRing_geometricStalkRing B S hS X (geometricPointMap ψ p)
  let : IsNoetherianRing (Stacks.ringFiber (etaleSitePoint B S hS (yoneda.obj V) p
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
      (smallEtaleRingedTopos B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O.obj) :=
    isNoetherianRing_geometricStalkRing_of_etale B S hS X hN V ψ hψ p
  let : IsLocalRing (Stacks.ringFiber (etaleSitePoint B S hS (yoneda.obj V) p
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
      (smallEtaleRingedTopos B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O.obj) :=
    isLocalRing_geometricStalkRing B S hS
      ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
  let := preservesFiniteLimits_extendScalars_of_bijective _ hg
  let : IsNoetherianRing (geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p) :=
    isNoetherianRing_geometricStalkRing_of_etale B S hS X hN V ψ hψ p
  let : IsLocalRing (geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p) :=
    isLocalRing_geometricStalkRing B S hS
      ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
  have h1 := Dualizing.isNormalizedDualizingComplex_extendScalars_of_bijective _ hg _ hm
  refine (Dualizing.isNormalizedDualizingComplex_congr.{u, u} ?_).mp h1
  exact ((ModuleCat.extendScalars.{u, u, u}
      (smallEtaleStalkPullbackRingMap B S hS f p)).mapDerivedCategory.commShiftIso (-m)).app _ ≪≫
    (shiftFunctor _ (-m)).mapIso eC1.symm

/-- The geometric stalk of `ε^*` of the sheaf associated to a module on an affine chart is its
base change, packaged: the homomorphism `γ` of
`AlgebraicGeometry.Space.representedAffineStalkRingHom`, its value on the étale local ring
(`AlgebraicGeometry.Space.pointStalkRingEquiv_representedAffineStalkRingHom`), and the
isomorphism `AlgebraicGeometry.Space.representedAffineAssociatedModuleStalkIso`. -/
theorem exists_representedAffineStalkRingHom_iso (V : BigFppfOver B S hS) (A : CommRingCat.{u})
    (i : (BigFppfOver.toScheme B S hS).obj V ≅ Spec A) (p : GeometricPoint B S hS (yoneda.obj V)) :
    ∃ γ : A →+* geometricStalkRing B S hS
        (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p,
      (∀ a : A, pointStalkRingEquiv B S hS
          ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p (γ a) =
        etaleLocalRingGerm B S hS (yoneda.obj V) p (Opposite.op (selfNeighborhood B S hS V p))
          (i.hom.appTop ((Scheme.ΓSpecIso A).inv a))) ∧
      Nonempty (tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom ⋙
          representedAssociatedModule B S hS V
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) ⋙
          Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS (yoneda.obj V) p
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O ≅
        ModuleCat.extendScalars.{u, u, u} γ) :=
  ⟨representedAffineStalkRingHom B S hS V p A i,
    pointStalkRingEquiv_representedAffineStalkRingHom B S hS V p A i,
    ⟨representedAffineAssociatedModuleStalkIso B S hS V p A i⟩⟩

/-- `ε^*` on a represented space, read with its target spelled as the modules over the structure
ring sheaf of the small étale ringed topos, which is the spelling of the geometric stalk
functor. -/
abbrev representedAssociatedModuleTopos (V : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj V).Modules ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) :=
  representedAssociatedModule B S hS V (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)

/-- `ε^*` on a represented space is additive, in the ringed-topos spelling of its target. -/
instance (V : BigFppfOver B S hS) : (representedAssociatedModuleTopos B S hS V).Additive :=
  additive_representedAssociatedModule B S hS V _

/-- `ε^*` on a represented space is left exact, in the ringed-topos spelling of its target. -/
instance (V : BigFppfOver B S hS) :
    PreservesFiniteLimits (representedAssociatedModuleTopos B S hS V) :=
  preservesFiniteLimits_representedAssociatedModule B S hS V _

/-- `ε^*` on a represented space is right exact, in the ringed-topos spelling of its target. -/
instance (V : BigFppfOver B S hS) :
    PreservesFiniteColimits (representedAssociatedModuleTopos B S hS V) :=
  preservesFiniteColimits_representedAssociatedModule B S hS V _

/-- The functor `M ↦ (ε^*(M~)|_V)_p` is exact, so an isomorphism with an extension of scalars makes
that extension of scalars exact. -/
theorem preservesFiniteLimits_extendScalars_of_iso (V : BigFppfOver B S hS) (A : CommRingCat.{u})
    (i : (BigFppfOver.toScheme B S hS).obj V ≅ Spec A) (p : GeometricPoint B S hS (yoneda.obj V))
    (γ : A →+* geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p)
    (eF : tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom ⋙
        representedAssociatedModule B S hS V (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) ⋙
        Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS (yoneda.obj V) p
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O ≅
      ModuleCat.extendScalars.{u, u, u} γ) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} γ) := by
  obtain ⟨_, _, _⟩ := geometricStalkFunctor_exact B S hS
    ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
  exact preservesFiniteLimits_of_natIso
    (F := tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom ⋙
      representedAssociatedModuleTopos B S hS V ⋙ geometricStalkFunctor B S hS
        ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p) eF

/-- **The derived geometric stalk of `ε^*` of a model.** For an object `M` of `D(A)`, an
isomorphism `T_V ≅ Spec A` and a geometric point `p` of `h_V`, an identification of the functor
`M ↦ (ε^*(M~)|_V)_p` with the extension of scalars along `γ` identifies the derived geometric
stalk of `ε^*(M~)` with `M ⊗_A 𝒪_{h_V, p}`. -/
theorem nonempty_geometricDerivedStalk_representedTilde_iso (V : BigFppfOver B S hS)
    (A : CommRingCat.{u}) (i : (BigFppfOver.toScheme B S hS).obj V ≅ Spec A)
    (p : GeometricPoint B S hS (yoneda.obj V))
    (γ : A →+* geometricStalkRing B S hS
      (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p)
    (eF : tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom ⋙
        representedAssociatedModule B S hS V (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) ⋙
        Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS (yoneda.obj V) p
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V))
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O ≅
      ModuleCat.extendScalars.{u, u, u} γ)
    (M : DerivedCategory (ModuleCat.{u} A)) :
    letI := preservesFiniteLimits_extendScalars_of_iso B S hS V A i p γ eF
    Nonempty ((geometricDerivedStalk B S hS
        (X := ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩) p).obj
        ((representedDerivedAssociatedModule B S hS V).obj
          ((tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom).mapDerivedCategory.obj M)) ≅
      (ModuleCat.extendScalars.{u, u, u} γ).mapDerivedCategory.obj M) := by
  let := preservesFiniteLimits_extendScalars_of_iso B S hS V A i p γ eF
  have : (show ModuleCat.{u} A ⥤ ModuleCat.{u}
      (((etaleSitePoint B S hS (yoneda.obj V) p
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)).presheafFiber
          (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O.obj) from
      ModuleCat.extendScalars.{u, u, u} γ).Additive := extendScalars_additive γ
  have : PreservesFiniteLimits (show ModuleCat.{u} A ⥤ ModuleCat.{u}
      (((etaleSitePoint B S hS (yoneda.obj V) p
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)).presheafFiber
          (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O.obj) from
      ModuleCat.extendScalars.{u, u, u} γ) :=
    preservesFiniteLimits_extendScalars_of_iso B S hS V A i p γ eF
  have : PreservesFiniteColimits (show ModuleCat.{u} A ⥤ ModuleCat.{u}
      (((etaleSitePoint B S hS (yoneda.obj V) p
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)).presheafFiber
          (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩).O.obj) from
      ModuleCat.extendScalars.{u, u, u} γ) := by
    have h : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u} γ) :=
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} γ).leftAdjoint_preservesColimits
    exact @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _ h
  obtain ⟨_, _, _⟩ := geometricStalkFunctor_exact B S hS
    ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
  let G₃ := geometricStalkFunctor B S hS
    ⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ p
  exact ⟨(Stacks.DerivedGlueing.mapDerivedCategoryCompIso
      (representedAssociatedModuleTopos B S hS V) G₃).app
        ((tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom).mapDerivedCategory.obj M) ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
      (tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom)
      (representedAssociatedModuleTopos B S hS V ⋙ G₃)).app M ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCongr
      ((Functor.associator (tilde.functor A ⋙ Scheme.Modules.restrictFunctor i.hom)
        (representedAssociatedModuleTopos B S hS V) G₃) ≪≫ eF)).app M⟩

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback) in
/-- **The normalizing shift of a stalk of a dualizing complex, read on a chart (proof of Stacks
0E53).** Let `K` be an object of `D(𝒪_X)` on a locally Noetherian algebraic space `X`, let
`φ : h_U ⟶ X` be an étale chart and `ω_U` a dualizing complex on `U` with `K|_U ≅ ε^*ω_U`
(Stacks 0E4X). Then over every point `y` of `U` there is a geometric point `x̄` of `X`, lying over
`φ(y)`, such that the only integer `m` for which `K_x̄[-m]` is a normalized dualizing complex over
`𝒪_{X, x̄}` is the value at `y` of the dimension function of Stacks 0AWF for `ω_U`.

On an affine neighbourhood `W` of `y`, `ω_U` is the sheaf associated to a dualizing complex `M`
over `Γ(U, W)`. The geometric point is a geometric point `p` of `h_W` over `y`, pushed to `X`. Its
stalk is read in three steps: the stalk of `K` at `x̄` base changes to the stalk of `K|_W` at `p`
along a bijection of geometric stalk rings (Stacks 05V5, `ε` being étale); `K|_W ≅ ε^*(M~)`
because `ε^*` commutes with étale pullback; and the stalk of `ε^*(M~)` is `M` base changed to
the geometric stalk ring, which by Stacks 04KF is the strict henselization of `Γ(U, W)` at the
prime of `y`. By Stacks 0AWD the normalizing shift of that base change is the dualizing dimension
of `M` at that prime, which is the value at `y` of the dimension function of Stacks 0AWF. -/
theorem exists_geometricPoint_isNormalizedDualizingComplex
    (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X.1)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (ωU : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hωU : Stacks.Duality.IsDualizingComplex ωU)
    (e : (representedChartDerivedRestriction B S hS X.2 U φ
        (isEtale_of_presheaf_etale B S hS hφ)).obj K ≅
      (representedDerivedAssociatedModule B S hS U).obj ωU)
    (y : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ x : GeometricPoint B S hS X.1,
      x.image = pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm y) ∧
      ∀ m : ℤ,
        letI := isNoetherianRing_geometricStalkRing B S hS X hN x
        Dualizing.IsNormalizedDualizingComplex.{u, u}
          ((geometricDerivedStalk B S hS x).obj K⟦-m⟧) →
        m = Stacks.Duality.associatedShiftFunction ωU y := by
  -- an affine open neighbourhood `W` of `y` and a dualizing model `M` of `ωU` on it
  obtain ⟨-, ⟨W, hW₀, rfl⟩, hyW, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ y) isOpen_univ
  have hW : IsAffineOpen W := hW₀
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj U, W) :=
    IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hωU W hW
  have hshift : Stacks.Duality.associatedShiftFunction ωU y =
      Dualizing.dualizingDimension.{u, u} M (hW.primeIdealOf ⟨y, hyW⟩) :=
    Stacks.Duality.associatedShiftFunction_eq_dualizingDimension hW M ⟨hM, ⟨eM⟩⟩ y hyW
  -- the open `W`, read as an étale chart `h_{W'} ⟶ X` through `φ`
  let Ac : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk φ, hφ⟩
  let W' : BigFppfOver B S hS := chartOpenOver B S hS Ac W
  let q : W' ⟶ U := chartOpenOverι B S hS Ac W
  have hTq : (BigFppfOver.toScheme B S hS).map q = Scheme.Opens.ι W := rfl
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map q) :=
    hTq ▸ Scheme.Opens.instIsOpenImmersionι (U := W)
  have hqEt : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) := inferInstance
  have hqφ : IsEtale B S hS (representedSpaceMap B S hS q).hom :=
    isEtale_schemeSpaceMap B S hS _ q hqEt
  have hψE := isEtale_of_presheaf_etale B S hS (etale_comp_of_scheme B S hS q φ hqEt hφ)
  -- a geometric point of `h_{W'}` over `y`
  let y' : (BigFppfOver.toScheme B S hS).obj W' := ⟨y, hyW⟩
  obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS (yoneda.obj W')
    ((pointsEquivScheme B S hS W').symm y')
  let f : (⟨yoneda.obj W', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩ :
      AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk (yoneda.map q ≫ φ)
  refine ⟨geometricPointMap f.hom p, ?_, ?_⟩
  · rw [geometricPointMap_image, hp]
    change pointsMap B S hS (yoneda.obj W') (yoneda.map q ≫ φ) _ = _
    rw [pointsMap_comp]
    refine congrArg (pointsMap B S hS (yoneda.obj U) φ) ?_
    apply (pointsEquivScheme B S hS U).injective
    rw [Equiv.apply_symm_apply]
    change pointsToScheme B S hS U (pointsMap B S hS _ (yoneda.map q) _) = y
    rw [pointsToScheme_pointsMap_yoneda]
    change (BigFppfOver.toScheme B S hS).map q
      ((pointsEquivScheme B S hS W') ((pointsEquivScheme B S hS W').symm y')) = y
    rw [Equiv.apply_symm_apply]
    rfl
  intro m hm
  -- `K|_{W'} ≅ ε^*` of the model `M`
  let eW : (representedChartDerivedRestriction B S hS X.2 W' (yoneda.map q ≫ φ) hψE).obj K ≅
      (representedDerivedAssociatedModule B S hS W').obj
        ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, W) ⋙
          Scheme.Modules.restrictFunctor hW.isoSpec.hom).mapDerivedCategory.obj M) :=
    (representedChartDerivedRestrictionCompIso B S hS X.2 φ (isEtale_of_presheaf_etale B S hS hφ)
        q hqφ hψE).app K ≪≫
      (representedDerivedPullback B S hS q hqφ).mapIso e ≪≫
      (representedDerivedAssociatedModulePullbackIso B S hS q hqφ).app ωU ≪≫
      (representedDerivedAssociatedModule B S hS W').mapIso
        ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory
            ((BigFppfOver.toScheme B S hS).map q)).app ωU ≪≫
          (Stacks.DerivedGlueing.mapDerivedCategoryCongr
            (Scheme.Modules.restrictFunctorIsoPullback
              ((BigFppfOver.toScheme B S hS).map q)).symm).app ωU ≪≫ eM)
  -- the stalk at `p` of `K|_{W'}` is normalized at `-m`
  have hmp := isNormalizedDualizingComplex_geometricDerivedStalk_restriction B S hS X hN K W'
    (yoneda.map q ≫ φ) hψE p m hm
  -- the base change of the model to the geometric stalk ring
  obtain ⟨γ, hγ, ⟨eF⟩⟩ := exists_representedAffineStalkRingHom_iso B S hS W'
    Γ((BigFppfOver.toScheme B S hS).obj U, W) hW.isoSpec p
  let N := selfNeighborhood B S hS W' p
  have hz : chartPoint B S hS (yoneda.obj W') N = y' := by
    change pointsToScheme B S hS W' p.image = y'
    rw [hp]
    exact (pointsEquivScheme B S hS W').apply_symm_apply y'
  let α : Γ((BigFppfOver.toScheme B S hS).obj U, W) →+*
      chartLocalRing B S hS (yoneda.obj W') N :=
    ((W : Scheme.{u}).presheaf.germ ⊤ (chartPoint B S hS (yoneda.obj W') N) trivial).hom.comp
      (Scheme.Opens.topIso W).inv.hom
  have hγα : ∀ a, pointStalkRingEquiv B S hS
      ⟨yoneda.obj W', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩ p (γ a) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj W')
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W') N (α a) := by
    intro a
    rw [hγ a, IsAffineOpen.isoSpec_hom_appTop]
    exact (congrArg (etaleLocalRingGerm B S hS (yoneda.obj W') p (Opposite.op N))
      (congrArg (fun t => (Scheme.Opens.topIso W).inv.hom t)
        (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, W))
          a))).trans
      (chartLocalRingToEtaleLocalRing_germ B S hS (yoneda.obj W')
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W') N
        ((Scheme.Opens.topIso W).inv.hom a)).symm
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W') :=
    inferInstanceAs (IsLocallyNoetherian (W : Scheme.{u}))
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} γ) :=
    preservesFiniteLimits_extendScalars_of_iso B S hS W' _ hW.isoSpec p γ eF
  have hn := isNormalizedDualizingComplex_extendScalars_geometricStalkRing B S hS W' p
    Γ((BigFppfOver.toScheme B S hS).obj U, W)
    (hW.primeIdealOf (chartPoint B S hS (yoneda.obj W') N)) α
    (isLocalization_stalk_toScheme hW (chartPoint B S hS (yoneda.obj W') N)) γ hγα M hM
  obtain ⟨e₃⟩ := nonempty_geometricDerivedStalk_representedTilde_iso B S hS W' _ hW.isoSpec p γ eF M
  have := isNoetherianRing_geometricStalkRing_yoneda B S hS W' p
  have := isLocalRing_geometricStalkRing B S hS
    ⟨yoneda.obj W', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩ p
  have hk : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((ModuleCat.extendScalars.{u, u, u} γ).mapDerivedCategory.obj M⟦-m⟧) :=
    (Dualizing.isNormalizedDualizingComplex_congr.{u, u}
      ((shiftFunctor _ (-m)).mapIso ((geometricDerivedStalk B S hS
        (X := ⟨yoneda.obj W', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩) p).mapIso eW ≪≫
          e₃))).mp hmp
  rw [(Dualizing.isNormalizedDualizingComplex_shift_iff_eq.{u, u} _ _ hn m).mp hk, hshift]
  exact congrArg (fun z => Dualizing.dualizingDimension.{u, u} M (hW.primeIdealOf z)) hz

end AlgebraicGeometry.Space

end
