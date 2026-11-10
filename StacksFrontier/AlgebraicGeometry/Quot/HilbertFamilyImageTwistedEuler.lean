/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyTwistedEuler
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomial

/-!
# The image of a Hilbert family along a monomorphism keeps its Hilbert polynomial

Let `π : X ⟶ Y` be a morphism over `A` whose base changes are monomorphisms (an open or a closed
immersion), `L'` an invertible `𝒪_Y`-module and `L ≅ π^*L'`.  The image `π_T(W) ⊆ Y_T` of a family
`W ⊆ X_T` classified by the Hilbert functor of `X/A` (Stacks 0DPE, 0DPF) is isomorphic to `W` over
`T`, and the restriction of `L'` to it is the restriction of `L`; so the two families have the
same twisted Euler characteristics, hence the same Hilbert polynomials.

## Main results

* `AlgebraicGeometry.Space.twistedEuler_hilbertCohObject_image`: the general statement.
* `AlgebraicGeometry.Space.twistedEuler_hilbertFamilyOverImage` (open immersions) and
  `AlgebraicGeometry.Space.twistedEuler_hilbertFamilyOverImageOfClosed` (closed immersions).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y A : AlgebraicSpaces B S hS} {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A}
  (hπ : π ≫ bY = bX) (hfX : IsFinitePresentation B S hS bX.hom)
  (hfY : IsFinitePresentation B S hS bY.hom)

include hπ in
/-- **A family and its image along a monomorphism have the same twisted Euler characteristics.**
-/
theorem twistedEuler_hilbertCohObject_image {T : BigFppfOver B S hS}
    (x : HilbertFamilyOver bX T) (yfam : HilbertFamily bY (CostructuredArrow.mk x.toBase))
    [Mono (schemeBaseChangeOfMap hπ (CostructuredArrow.mk x.toBase))]
    (hyZ : yfam.Z = x.family.Z.image (schemeBaseChangeOfMap hπ (CostructuredArrow.mk x.toBase)))
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
    (L' : Modules.{u, u} B S hS Y.1 Y.2)
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property L']
    (eπ : (modulePullback B S hS π).obj L' ≅ L)
    (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℤ) :
    @CoherentObject.twistedEuler B S hS (structureSheafQuotSituation bX hfX).toCoherentSituation
        L hL (hilbertCohObject bX hfX x) t n =
      @CoherentObject.twistedEuler B S hS (structureSheafQuotSituation bY hfY).toCoherentSituation
        L' hL' (hilbertCohObject bY hfY ⟨x.toBase, yfam⟩) t n := by
  obtain ⟨Z', hc, hfp, hfl, hpr⟩ := yfam
  dsimp only at hyZ
  subst hyZ
  let m := schemeBaseChangeOfMap hπ (CostructuredArrow.mk x.toBase)
  let y : HilbertFamilyOver bY T := ⟨x.toBase, ⟨_, hc, hfp, hfl, hpr⟩⟩
  let φ : x.subspace ≅ y.subspace := ObjectProperty.isoMk _ (asIso (x.family.Z.toImage m))
  have hφ : φ.hom ≫ y.subspaceInclusion ≫ schemeBaseChangeProjectionHom B S hS bY
      (CostructuredArrow.mk y.toBase) =
      x.subspaceInclusion ≫ schemeBaseChangeProjectionHom B S hS bX
        (CostructuredArrow.mk x.toBase) := by
    apply ObjectProperty.hom_ext
    change x.family.Z.toImage m ≫ (x.family.Z.image m).ι ≫ pullback.snd bY.hom x.toBase =
      x.family.Z.ι ≫ pullback.snd bX.hom x.toBase
    rw [← Category.assoc, Subfunctor.toImage_ι, Category.assoc]
    exact congrArg (x.family.Z.ι ≫ ·) (schemeBaseChangeOfMap_snd hπ (CostructuredArrow.mk x.toBase))
  let p := x.subspaceInclusion ≫ (ObjectProperty.homMk (pullback.fst bX.hom x.toBase) :
    schemeBaseChangeSpace bX (CostructuredArrow.mk x.toBase) ⟶ X)
  let p' := φ.hom ≫ y.subspaceInclusion ≫ (ObjectProperty.homMk (pullback.fst bY.hom y.toBase) :
    schemeBaseChangeSpace bY (CostructuredArrow.mk y.toBase) ⟶ Y)
  have hp : p ≫ π = p' := by
    apply ObjectProperty.hom_ext
    change (x.family.Z.ι ≫ pullback.fst bX.hom x.toBase) ≫ π.hom =
      x.family.Z.toImage m ≫ (x.family.Z.image m).ι ≫ pullback.fst bY.hom x.toBase
    rw [← Category.assoc (x.family.Z.toImage m), Subfunctor.toImage_ι, Category.assoc,
      Category.assoc]
    exact (congrArg (x.family.Z.ι ≫ ·)
      (schemeBaseChangeOfMap_fst hπ (CostructuredArrow.mk x.toBase))).symm
  let e : (modulePullback B S hS p).obj L ≅ (modulePullback B S hS p').obj L' :=
    (modulePullback B S hS p).mapIso eπ.symm ≪≫ ((modulePullbackTriangle B S hS hp).app L').symm
  exact twistedEuler_hilbertCohObject_eq_of_iso bX hfX bY hfY x y φ hφ L L'
    (fun n => modulePullbackInvertibleTensorPowerCongr p p' L L' e n) t n

/-- **`Hilb^{P, π^*L'}_{X/A}` lands in `Hilb^{P, L'}_{Y/A}` under an open immersion**
(Stacks 0DPE): the image of a family has the twisted Euler characteristics of the family. -/
theorem hilbertFamilyOverImage_mem_hilbertPolynomialSubfunctor
    (hopen : IsOpenImmersion B S hS π.hom) (hsep : IsSeparated B S hS bY.hom)
    {T : BigFppfOver B S hS} (x : HilbertFamilyOver bX T) (L' : Modules.{u, u} B S hS Y.1 Y.2)
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property L'] (P : ℤ → ℤ)
    (hx : x ∈ (hilbertPolynomialSubfunctor bX hfX ((modulePullback B S hS π).obj L')
      (hL := stacksIsInvertible_modulePullback_obj B S hS π L') P).obj (Opposite.op T)) :
    hilbertFamilyOverImage hπ hopen hsep T x ∈
      (hilbertPolynomialSubfunctor bY hfY L' P).obj (Opposite.op T) := by
  have := mono_schemeBaseChangeOfMap hπ hopen (CostructuredArrow.mk x.toBase)
  have := stacksIsInvertible_modulePullback_obj B S hS π L'
  intro t n
  exact (hx t n).trans (twistedEuler_hilbertCohObject_image hπ hfX hfY x
    (hilbertFamilyImage hπ hopen hsep (CostructuredArrow.mk x.toBase) x.family) rfl
    ((modulePullback B S hS π).obj L') L' (Iso.refl _) t n)

/-- **`Hilb^{P, π^*L'}_{X/A}` lands in `Hilb^{P, L'}_{Y/A}` under a closed immersion**
(Stacks 0DPF). -/
theorem hilbertFamilyOverImageOfClosed_mem_hilbertPolynomialSubfunctor
    (hclosed : IsClosedImmersion B S hS π.hom)
    {T : BigFppfOver B S hS} (x : HilbertFamilyOver bX T) (L' : Modules.{u, u} B S hS Y.1 Y.2)
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property L'] (P : ℤ → ℤ)
    (hx : x ∈ (hilbertPolynomialSubfunctor bX hfX ((modulePullback B S hS π).obj L')
      (hL := stacksIsInvertible_modulePullback_obj B S hS π L') P).obj (Opposite.op T)) :
    hilbertFamilyOverImageOfClosed hπ hclosed T x ∈
      (hilbertPolynomialSubfunctor bY hfY L' P).obj (Opposite.op T) := by
  have := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed
    (CostructuredArrow.mk x.toBase)
  have := stacksIsInvertible_modulePullback_obj B S hS π L'
  intro t n
  exact (hx t n).trans (twistedEuler_hilbertCohObject_image hπ hfX hfY x
    (hilbertFamilyImageOfClosed hπ hclosed (CostructuredArrow.mk x.toBase) x.family) rfl
    ((modulePullback B S hS π).obj L') L' (Iso.refl _) t n)

end AlgebraicGeometry.Space

end
