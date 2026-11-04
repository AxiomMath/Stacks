module

public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsValue
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.PullbackOfApproximations

/-!
# The degree-zero sections functor of a K-flat complex computes `H⁰(T, H⁰(Lg^*E))`

Let `P` be a K-flat complex of `𝒪_X`-modules with flat terms on an algebraic space `X`.  By the
computation clause of Stacks 06YY the degreewise inverse image `g^*P` along any `g : T ⟶ X`
computes the derived pullback `Lg^*P`.  This file records the consequences for the degree-zero
sections functor of `P`:

* its value at a test scheme `g : T ⟶ X` is `H⁰(T, H⁰(Lg^*E))` for `E ≅ P` in `D(𝒪_X)`, which is
  the value of the functor of Stacks 08JX, part (1),
  `AlgebraicGeometry.Space.degreeZeroPullbackSections`;
* a morphism `φ : P ⟶ P'` of such complexes which is an approximation in degrees `> m`, `m < 0`
  — an isomorphism on cohomology in every degree `> m` and an epimorphism in degree `m` — induces
  isomorphisms on `H⁰` after every inverse image, hence an isomorphism of the degree-zero
  sections functors: the derived pullback is triangulated and right t-exact, so it carries
  approximations in degrees `> m` to approximations in degrees `> m`.

## Main definitions

* `AlgebraicGeometry.Space.pullbackQComparison`: the comparison `Lf^*(Q K) ⟶ Q(f^*K)`, natural in
  the complex `K`, invertible at K-flat complexes with flat terms.
* `AlgebraicGeometry.Space.degreeZeroSectionsEquiv`: the value identification.

## Main results

* `AlgebraicGeometry.Space.quasiIsoAt_pullback_of_approximation` and
  `AlgebraicGeometry.Space.epi_homologyMap_pullback_of_approximation`: approximations in degrees
  `> m` stay approximations after degreewise pullback, between K-flat complexes with flat terms.
* `AlgebraicGeometry.Space.isIso_degreeZeroSectionsMap_of_approximation`.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

namespace CategoryTheory.NatIso

/-- A morphism is sent to an epimorphism by one of two isomorphic functors exactly when it is by
the other. -/
theorem epi_map_iff_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    {X Y : C} (f : X ⟶ Y) : Epi (F.map f) ↔ Epi (G.map f) := by
  constructor <;> intro
  · rw [show G.map f = e.inv.app X ≫ F.map f ≫ e.hom.app Y by simp]
    infer_instance
  · rw [show F.map f = e.hom.app X ≫ G.map f ≫ e.inv.app Y by simp]
    infer_instance

end CategoryTheory.NatIso

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

-- The inverse images are never unfolded here; keeping them opaque stops the unifier from
-- unfolding them when two inverse images along equal morphisms are compared.
attribute [local irreducible] modulePullback smallEtaleRingedToposHom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Invertibility of `Hⁱ(Qh (quotient χ))` is invertibility of the `i`-th homology map of `χ`. -/
theorem isIso_homologyFunctor_map_Qh_quotient_map_iff {Z : AlgebraicSpaces B S hS}
    {K L : CochainComplex (toposModules B S hS Z) ℤ} (χ : K ⟶ L) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS Z) i).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map χ))) ↔
      IsIso (HomologicalComplex.homologyMap χ i) :=
  NatIso.isIso_map_iff
    (Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactorsh (toposModules B S hS Z) i) ≪≫
      HomotopyCategory.homologyFunctorFactors _ _ i) χ

/-- **The pullback on homotopy categories of an approximation between K-flat complexes is an
approximation.**  If `ψ : M ⟶ M'` is a morphism of K-flat complexes with flat terms whose image in
the derived category induces isomorphisms on cohomology in degrees `> m` and an epimorphism in
degree `m`, so does its degreewise pullback: the derived pullback carries approximations to
approximations, and on K-flat complexes it is the degreewise pullback (Stacks 06YY). -/
theorem pullbackOnHomotopy_map_approximation {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M M' : HomotopyCategory (toposModules B S hS Y) (ComplexShape.up ℤ)}
    (hM : IsKFlat (Y := smallEtaleRingedTopos B S hS Y) M)
    (hM' : IsKFlat (Y := smallEtaleRingedTopos B S hS Y) M') (ψ : M ⟶ M') (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS Y) i).map
      (DerivedCategory.Qh.map ψ)))
    (hepi : Epi ((DerivedCategory.homologyFunctor (toposModules B S hS Y) m).map
      (DerivedCategory.Qh.map ψ))) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS X) i).map
        ((smallEtaleModulePullbackOnHomotopy B S hS f).map ψ))) ∧
      Epi ((DerivedCategory.homologyFunctor (toposModules B S hS X) m).map
        ((smallEtaleModulePullbackOnHomotopy B S hS f).map ψ)) := by
  have hL := smallEtaleDerivedModulePullback_map_approximation f (DerivedCategory.Qh.map ψ) m
    hiso hepi
  let c := @asIso _ _ _ _ ((smallEtaleDerivedModulePullbackComparison B S hS f).app M)
    (isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat f M hM)
  let c' := @asIso _ _ _ _ ((smallEtaleDerivedModulePullbackComparison B S hS f).app M')
    (isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat f M' hM')
  have h3 : (smallEtaleModulePullbackOnHomotopy B S hS f).map ψ =
      c.inv ≫ (smallEtaleDerivedModulePullback B S hS f).map (DerivedCategory.Qh.map ψ) ≫
        c'.hom := by
    rw [← cancel_epi c.hom, Iso.hom_inv_id_assoc]
    exact ((smallEtaleDerivedModulePullbackComparison B S hS f).naturality ψ).symm
  have hA := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.iso_comp_approximation c.symm _ m
    hL.1 hL.2
  have hB := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_comp_iso _ c' m
    hA.1 hA.2
  rwa [Iso.symm_hom, Category.assoc, ← h3] at hB

/-- Surjectivity of `Hⁱ(Qh (quotient χ))` is surjectivity of the `i`-th homology map of `χ`. -/
theorem epi_homologyFunctor_map_Qh_quotient_map_iff {Z : AlgebraicSpaces B S hS}
    {K L : CochainComplex (toposModules B S hS Z) ℤ} (χ : K ⟶ L) (i : ℤ) :
    Epi ((DerivedCategory.homologyFunctor (toposModules B S hS Z) i).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map χ))) ↔
      Epi (HomologicalComplex.homologyMap χ i) :=
  NatIso.epi_map_iff_of_iso
    (Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactorsh (toposModules B S hS Z) i) ≪≫
      HomotopyCategory.homologyFunctorFactors _ _ i) χ

/-- The degreewise pullback of an approximation between K-flat complexes is an approximation, on
the level of homology maps. -/
private theorem homologyMap_pullback_approximation {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {K K' : CochainComplex (toposModules B S hS Y) ℤ}
    (hK : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (hK' : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K'))
    (φ : K ⟶ K') (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap φ i))
    (hepi : Epi (HomologicalComplex.homologyMap φ m)) :
    (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap
      ((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) i)) ∧
      Epi (HomologicalComplex.homologyMap
        ((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) m) := by
  let ψ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ
  have hP := pullbackOnHomotopy_map_approximation f hK hK' ψ m
    (fun j hj => (isIso_homologyFunctor_map_Qh_quotient_map_iff φ j).2 (hiso j hj))
    ((epi_homologyFunctor_map_Qh_quotient_map_iff φ m).2 hepi)
  have h4 : (smallEtaleModulePullbackOnHomotopy B S hS f).map ψ =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ)) :=
    congrArg DerivedCategory.Qh.map (Functor.mapHomotopyCategory_map _ φ)
  rw [h4] at hP
  let e := NatIso.mapHomologicalComplex (toposPullbackModulesIso f) (ComplexShape.up ℤ)
  have : (((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ =
      e.inv.app K ≫
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) ≫ e.hom.app K' := by
    rw [e.hom.naturality φ, Iso.inv_hom_id_app_assoc]
  simp only [this, HomologicalComplex.homologyMap_comp]
  refine ⟨fun i hi => ?_, ?_⟩
  · have := (isIso_homologyFunctor_map_Qh_quotient_map_iff (Z := X) _ i).1 (hP.1 i hi)
    infer_instance
  · have := (epi_homologyFunctor_map_Qh_quotient_map_iff (Z := X) _ m).1 hP.2
    infer_instance

/-- **The degreewise pullback of an approximation between K-flat complexes is an approximation**,
for the inverse image of `𝒪`-modules of Stacks 03LU: if `φ : K ⟶ K'` is a morphism of K-flat
complexes with flat terms inducing isomorphisms on cohomology in every degree `> m` and an
epimorphism in degree `m`, then `f^*φ` induces isomorphisms on cohomology in every degree
`> m`. -/
theorem quasiIsoAt_pullback_of_approximation {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {K K' : CochainComplex (toposModules B S hS Y) ℤ}
    (hK : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (hK' : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K'))
    (φ : K ⟶ K') (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap φ i))
    (hepi : Epi (HomologicalComplex.homologyMap φ m)) (i : ℤ) (hi : m < i) :
    QuasiIsoAt ((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) i := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (homologyMap_pullback_approximation f hK hK' φ m hiso hepi).1 i hi

/-- **The degreewise pullback of an approximation between K-flat complexes is surjective on
cohomology in the bottom degree**, the companion of
`AlgebraicGeometry.Space.quasiIsoAt_pullback_of_approximation`. -/
theorem epi_homologyMap_pullback_of_approximation {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {K K' : CochainComplex (toposModules B S hS Y) ℤ}
    (hK : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (hK' : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K'))
    (φ : K ⟶ K') (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap φ i))
    (hepi : Epi (HomologicalComplex.homologyMap φ m)) :
    Epi (HomologicalComplex.homologyMap
      ((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) m) :=
  (homologyMap_pullback_approximation f hK hK' φ m hiso hepi).2

/-- **An approximation in degrees `> m`, `m < 0`, between K-flat complexes with flat terms induces
an isomorphism of the degree-zero sections functors.** -/
theorem isIso_degreeZeroSectionsMap_of_approximation {X : AlgebraicSpaces B S hS} {I : Type*}
    [Category* I] {π : I ⥤ AlgebraicSpaces B S hS} (κ : PullbackData.ConeTo π X)
    {K K' : CochainComplex (toposModules B S hS X) ℤ}
    (hK : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (hK' : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K'))
    (φ : K ⟶ K') (m : ℤ) (hm : m < 0)
    (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap φ i))
    (hepi : Epi (HomologicalComplex.homologyMap φ m)) :
    IsIso (degreeZeroSectionsMap κ φ) :=
  isIso_degreeZeroSectionsMap κ φ fun i =>
    quasiIsoAt_pullback_of_approximation (κ.leg i) hK hK' φ m hiso hepi 0 hm

/-- **The derived pullback of a K-flat complex with flat terms is its degreewise pullback.** -/
def derivedPullbackQIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (K : CochainComplex (toposModules B S hS Y) ℤ)
    (hK : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    (smallEtaleDerivedModulePullback B S hS f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        ((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.quotientCompQhIso (toposModules B S hS Y)).app K).symm ≪≫
    @asIso _ _ _ _ ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((HomotopyCategory.quotient _ _).obj K))
      (isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat f _ hK) ≪≫
    DerivedCategory.Qh.mapIso
      (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso (toposModules B S hS X)).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (toposPullbackModulesIso f) (ComplexShape.up ℤ)).app K)

/-- **The value of the degree-zero sections functor of a K-flat complex `P` representing `E` is
`H⁰(T, H⁰(Lg^*E))`**, the value of the functor of Stacks 08JX, part (1). -/
def degreeZeroSectionsEquiv {X : AlgebraicSpaces B S hS}
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    (P : CochainComplex (toposModules B S hS X) ℤ)
    (hP : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (E : derivedModules B S hS X) (e : DerivedCategory.Q.obj P ≅ E) (T : SchemesOver X) :
    (degreeZeroSectionsFunctor (schemesOverCone X) P).obj (Opposite.op T) ≃
      degreeZeroPullbackSections hL E T :=
  let c : ((((toposModulePullbackData B S hS).pull
        ((schemesOverCone X).leg T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology 0 ≅
      BottomRankStratum.pullbackHomology hL E 0 T.hom :=
    ((DerivedCategory.homologyFunctorFactors (toposModules B S hS _) 0).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (toposModules B S hS _) 0).mapIso
        ((derivedPullbackQIso T.hom P hP).symm ≪≫
          (smallEtaleDerivedModulePullback B S hS T.hom).mapIso e)
  (degreeZeroSectionsEquivHom (schemesOverCone X) P T).trans <|
    (Iso.homCongr (Iso.refl _) c).trans (SheafOfModules.unitHomEquiv _)

end AlgebraicGeometry.Space

end
