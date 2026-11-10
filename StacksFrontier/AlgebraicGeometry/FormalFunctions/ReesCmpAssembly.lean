module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesBaseChangeCoherent
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyCoproductDirectSum
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Natural
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSpecStructureSections

/-!
# Assembling the `B`-linear comparison `cmp` of [Stacks, Tag 0897]

[Stacks, Tag 02O8]'s hypothesis `h0897` is down to the comparison
`cmp : ⨁ₙ Hᵖ(X, Mₙ) ≃ₗ[B] Hᵖ(X', F')` (see
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_cmp`). This file
assembles the comparison out of the three identifications that make it up:

* `Hᵖ(X, ∐ₙ Mₙ) ≅ ⨁ₙ Hᵖ(X, Mₙ)`
  (`Stacks.Cohomology.CoproductDirectSum.cohomologyCoprodDirectSumIso`);
* `Hᵖ(X, ε)` for an identification `ε : ∐ₙ Mₙ ≅ π_* F'`;
* [Stacks, Tag 089W] for the affine `π : X' ⟶ X`
  (`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`).

## Main definitions

* `Stacks.Cohomology.FormalFunctions.addEquivOfModuleIso`: a module isomorphism read as an
  additive equivalence of the underlying groups.
* `Stacks.Cohomology.FormalFunctions.reesSpecStructure`: the structure morphism
  `f' : X' ⟶ Spec B` of the base change.
* `Stacks.Cohomology.FormalFunctions.reesCmpAddEquiv`: **the additive comparison
  `⨁_{n : ℕ} Hᵖ(X, Mₙ) ≃+ Hᵖ(X', F')`.**

## Main results

* `Stacks.Cohomology.FormalFunctions.compactSpace_of_isProper` and
  `Stacks.Cohomology.FormalFunctions.quasiSeparatedSpace_of_isProper`: a scheme proper over an
  affine base is quasi-compact and quasi-separated, which is what the direct-sum comparison of
  [Stacks, Tag 01FF] needs.
* `Stacks.Cohomology.FormalFunctions.reesCmpAddEquiv_of`: **the comparison on a generator** is
  `Hᵖ(X, −)` of the `n`-th coproduct injection followed by `ε`, read through [Stacks, Tag 089W].
  This is what reduces the `B`-linearity of the comparison to one identity of morphisms of
  sheaves in each degree.
* `Stacks.Cohomology.FormalFunctions.ReesSmulCompatible`: **that identity**, for all degrees:
  the direct image of multiplication by a homogeneous `b ∈ Iᵏ` on `F'` is, through `ε`, the
  degreewise action `Stacks.Cohomology.FormalFunctions.actHom` of `b` on `∐ₙ Mₙ`. It is proved,
  at the identification `Stacks.Cohomology.FormalFunctions.reesCoprodPushforwardIso` built at
  the end of this file, in
  `StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSmulCompatible`.
* `Stacks.Cohomology.FormalFunctions.smul_cohomologyIsoPushforward_inv`: multiplication by a
  scalar of `B` on `Hᵖ(X', F')`, read through [Stacks, Tag 089W].

The semilinearity of the comparison, the `B`-linear comparison `cmp` itself and
[Stacks, Tag 02O8]'s hypothesis `h0897` are all deduced from that identity in
`StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSmulCompatible`, where the identity is
proved; nothing here needs them.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology
open Stacks.Cohomology.AffineBase Stacks.Blowup
open scoped DirectSum

universe u

namespace Stacks.Cohomology.FormalFunctions

noncomputable section

/-- A module isomorphism, read as an additive equivalence of the underlying groups. -/
public def addEquivOfModuleIso {R : Type u} [Ring R] {N P : ModuleCat.{u} R} (e : N ≅ P) :
    (N : Type u) ≃+ (P : Type u) where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv x := congrArg (fun φ : N ⟶ N => φ.hom x) e.hom_inv_id
  right_inv y := congrArg (fun φ : P ⟶ P => φ.hom y) e.inv_hom_id
  map_add' := map_add _

/-- A module isomorphism undoes itself, read on elements. -/
public theorem moduleIso_inv_hom_apply {R : Type u} [Ring R] {N P : ModuleCat.{u} R} (e : N ≅ P)
    (x : (N : Type u)) : e.inv.hom (e.hom.hom x) = x :=
  congrArg (fun φ : N ⟶ N => φ.hom x) e.hom_inv_id

/-- A module isomorphism undoes itself, read on elements, the other way round. -/
public theorem moduleIso_hom_inv_apply {R : Type u} [Ring R] {N P : ModuleCat.{u} R} (e : N ≅ P)
    (y : (P : Type u)) : e.hom.hom (e.inv.hom y) = y :=
  congrArg (fun φ : P ⟶ P => φ.hom y) e.inv_hom_id

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- A scheme proper over an affine base is quasi-compact. -/
public theorem compactSpace_of_isProper (hX : AlgebraicGeometry.IsProper X.hom) :
    CompactSpace (X.left : Type u) :=
  let := hX
  QuasiCompact.compactSpace_of_compactSpace X.hom

/-- A scheme separated over an affine base is quasi-separated. -/
public theorem quasiSeparatedSpace_of_isProper (hX : AlgebraicGeometry.IsProper X.hom) :
    QuasiSeparatedSpace (X.left : Type u) :=
  let := hX
  quasiSeparatedSpace_of_quasiSeparated X.hom

variable (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X)) (p : ℕ)

section Assembly

/-- **`f' : X' ⟶ Spec B`**, the structure morphism of [Stacks, Tag 0897]'s base change: the
closed immersion of `X' = Spec_X(⨁ₙ ℐⁿ)` into `Spec(B) ×_{Spec A} X` followed by the
projection. -/
public abbrev reesSpecStructure : (reesRelativeSpec I X).left ⟶ Spec (.of ↥(reesAlgebra I)) :=
  reesClosedImmersion I X ≫ pullback.fst (Over.mk (reesSpecToBase I)).hom X.hom

variable (F' : (reesRelativeSpec I X).left.Modules) [F'.IsQuasicoherent]
  (hX : AlgebraicGeometry.IsProper X.hom)
  (ε : (∐ fun n : ℕ => M.piece (n : ℤ)) ≅
    (AlgebraicGeometry.Scheme.Modules.pushforward (reesRelativeSpec I X).hom).obj F')

/-- **The additive comparison `⨁_{n : ℕ} Hᵖ(X, Mₙ) ≃+ Hᵖ(X', F')`**, from an identification `ε`
of `∐ₙ Mₙ` with `π_* F'`: the direct sum comparison of
`Stacks.Cohomology.CoproductDirectSum.cohomologyCoprodDirectSumIso`, then `Hᵖ(X, ε)`, then
[Stacks, Tag 089W]. -/
public def reesCmpAddEquiv :
    (⨁ n : ℕ, gradedCohomologyPiece I X M p n) ≃+
      (cohomologyOf (reesRelativeSpec I X).left p F' : Type u) :=
  haveI := compactSpace_of_isProper X hX
  haveI := quasiSeparatedSpace_of_isProper X hX
  (addEquivOfModuleIso
      (Stacks.Cohomology.CoproductDirectSum.cohomologyCoprodDirectSumIso X.left p
        (fun n : ℕ => M.piece (n : ℤ))).symm).trans
    ((addEquivOfModuleIso (((moduleGlobalSections X.left).rightDerived p).mapIso ε)).trans
      (addEquivOfModuleIso
        (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (reesRelativeSpec I X).hom F' p).symm))

/-- The value of the comparison on a generator: `Hᵖ(X, −)` of the `n`-th coproduct injection,
then of `ε`. -/
public theorem reesCmpAddEquiv_of (n : ℕ) (x : gradedCohomologyPiece I X M p n) :
    reesCmpAddEquiv I X M p F' hX ε (DirectSum.of (gradedCohomologyPiece I X M p) n x) =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (reesRelativeSpec I X).hom F' p).inv.hom
        ((((moduleGlobalSections X.left).rightDerived p).map ε.hom).hom
          ((((moduleGlobalSections X.left).rightDerived p).map
            (Sigma.ι (fun m : ℕ => M.piece (m : ℤ)) n)).hom x)) := by
  have := compactSpace_of_isProper X hX
  have := quasiSeparatedSpace_of_isProper X hX
  have h2 := Stacks.Cohomology.CoproductDirectSum.map_sigmaι_comp_cohomologyCoprodDirectSumIso_hom
    X.left p (fun m : ℕ => M.piece (m : ℤ)) n
  have h3 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h2) x
  refine congrArg (fun w =>
    (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
        (reesRelativeSpec I X).hom F' p).inv.hom
      ((((moduleGlobalSections X.left).rightDerived p).map ε.hom).hom w)) ?_
  exact Eq.trans (congrArg (fun w =>
    (Stacks.Cohomology.CoproductDirectSum.cohomologyCoprodDirectSumIso X.left p
      (fun m : ℕ => M.piece (m : ℤ))).inv.hom w) h3.symm) (moduleIso_inv_hom_apply _ _)

/-- **The one sheaf-level identity the `B`-linearity of the comparison reduces to**: for `b`
homogeneous of degree `k`, the direct image of multiplication by `b` on `F'` is, through `ε`,
the degreewise action `actHom` of `b` on `∐ₙ Mₙ`. -/
public def ReesSmulCompatible : Prop :=
  ∀ (k n : ℕ) (b : ↥(reesGrading I k)),
    actHom I X M b (n : ℤ) (degree_add_eq k n) ≫
        Limits.Sigma.ι (fun m : ℕ => M.piece (m : ℤ)) (k + n) ≫ ε.hom =
      Limits.Sigma.ι (fun m : ℕ => M.piece (m : ℤ)) n ≫ ε.hom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (reesRelativeSpec I X).hom).map
          (letI : Linear ↥(reesAlgebra I) (reesRelativeSpec I X).left.Modules :=
             AlgebraicGeometry.modulesLinear ↥(reesAlgebra I) (Over.mk (reesSpecStructure I X))
           (b : ↥(reesAlgebra I)) • 𝟙 F')

attribute [local irreducible] Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
  reesClosedImmersion reesClosedImmersionOver

/-- Multiplication by a scalar of `B` on `Hᵖ(X', F')`, read through [Stacks, Tag 089W]: it is
`Hᵖ(X, −)` of the direct image of multiplication by that scalar. -/
public theorem smul_cohomologyIsoPushforward_inv (r : ↥(reesAlgebra I))
    (v : ((((moduleGlobalSections X.left).rightDerived p).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (reesRelativeSpec I X).hom).obj F')) : Type u)) :
    specAlgebraRingHom ↥(reesAlgebra I) (reesSpecStructure I X) r •
        (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (reesRelativeSpec I X).hom F' p).inv.hom v =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (reesRelativeSpec I X).hom F' p).inv.hom
        ((((moduleGlobalSections X.left).rightDerived p).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward (reesRelativeSpec I X).hom).map
            (letI : Linear ↥(reesAlgebra I) (reesRelativeSpec I X).left.Modules :=
               AlgebraicGeometry.modulesLinear ↥(reesAlgebra I)
                 (Over.mk (reesSpecStructure I X))
             r • 𝟙 F'))).hom v) := by
  have h := Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_baseSmul
    (Over.mk (reesSpecStructure I X)) (reesRelativeSpec I X).hom F' p r
    ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
      (reesRelativeSpec I X).hom F' p).inv.hom v)
  rw [moduleIso_hom_inv_apply] at h
  exact (moduleIso_inv_hom_apply
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
        (reesRelativeSpec I X).hom F' p) _).symm.trans
    (congrArg (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
      (reesRelativeSpec I X).hom F' p).inv.hom h)

/-- Three composable maps under `Hᵖ(X, −)`, read on elements. -/
public theorem map_three {N₁ N₂ N₃ N₄ : X.left.Modules} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃)
    (h : N₃ ⟶ N₄) (x : (cohomologyFunctor X p).obj N₁) :
    ((cohomologyFunctor X p).map h).hom (((cohomologyFunctor X p).map g).hom
        (((cohomologyFunctor X p).map f).hom x)) =
      ((cohomologyFunctor X p).map ((f ≫ g) ≫ h)).hom x := by
  rw [cohomologyFunctor_map_comp_apply, cohomologyFunctor_map_comp_apply]
  exact congrArg (fun φ : N₁ ⟶ N₄ => ((cohomologyFunctor X p).map φ).hom x)
    (Category.assoc f g h).symm

end Assembly

/-- **The functor of [Stacks, Tag 01SB] is the direct image**, after restriction of scalars
along the structure map of the algebra sheaf. The equality holds because
`Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence_functor_obj_obj` and
`Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules` are both
`rfl`, and the two restrictions of scalars compose to the one along `π^♯` by
`Stacks.AffineAlgebraEquivalence.structureMap_comp_pushforwardRingIso`. -/
public theorem restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj
    {S : Scheme.{u}} (𝒜 : AlgebraSheaf S) [AlgebraSheaf.IsQuasicoherent 𝒜]
    (G : (SheafOfModules.isQuasicoherent (relativeSpec 𝒜).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap 𝒜)).obj
        ((relativeSpecQcohEquivalence 𝒜).functor.obj G).obj =
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeSpecToBase 𝒜)).obj G.obj := by
  have hmap : AlgebraSheaf.structureMap 𝒜 ≫ (pushforwardRingIso 𝒜).inv =
      (relativeSpecToBase 𝒜).toRingCatSheafHom :=
    (Iso.comp_inv_eq _).2 (structureMap_comp_pushforwardRingIso 𝒜).symm
  change (SheafOfModules.restrictScalars
      (AlgebraSheaf.structureMap 𝒜 ≫ (pushforwardRingIso 𝒜).inv)).obj
    ((Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules
      (relativeSpecToBase 𝒜).base (relativeSpec 𝒜).ringCatSheaf).obj G.obj) = _
  exact congrArg (fun α => (SheafOfModules.restrictScalars α).obj
    ((Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules
      (relativeSpecToBase 𝒜).base (relativeSpec 𝒜).ringCatSheaf).obj G.obj)) hmap

/-- **`∐ₙ Mₙ ≅ π_* F'`**: the coproduct comparison
`SheafOfModules.GradedModule.coprodIsoUngradedSheaf` followed by the defining property
`Stacks.Cohomology.FormalFunctions.reesBaseChangeModuleIso` of `F'`, read as a statement about
the direct image by `restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj`. -/
public def reesCoprodPushforwardIso
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (∐ fun n : ℕ => M.piece (n : ℤ)) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (reesRelativeSpec I X).hom).obj
        (reesBaseChangeModule I X M hqc hneg) :=
  SheafOfModules.GradedModule.coprodIsoUngradedSheaf M hneg ≪≫
    ((SheafOfModules.restrictScalars
        (AlgebraSheaf.structureMap
          (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom)))).mapIso
      ((ObjectProperty.ι _).mapIso (reesBaseChangeModuleIso I X M hqc hneg))).symm ≪≫
    eqToIso (restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj
      (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom)) _)

end

end Stacks.Cohomology.FormalFunctions

end
