module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.SmulIdentityHelpers
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedComparison
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedRingAction
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSmulCompatible

/-!
# The `B`-linearity of [Stacks, Tag 0897]'s comparison

`Stacks.AlgebraicGeometry.GradedProperCohomology.GradedQcohAlgebra.cmpAddEquiv` compares the
graded cohomology `⨁ₙ Hᵖ(X, Fₙ)` with `Hᵖ(X', F')` as abelian groups, and
`HomogeneousSections.gradedCohomologyModule` makes the source a `B`-module. **This file proves
that the comparison is `B`-linear**, given the one scalar identity that ties the graded sections
of `𝓑` to the structure morphism `f' : X' ⟶ Spec B`, and deduces the finiteness conclusion of
[Stacks, Tag 0897] part (1) from [Stacks, Tag 02O6].

## The shape of the argument

The comparison is determined on the generators of the direct sum by
`GradedQcohAlgebra.cmpAddEquiv_of`, so its linearity reduces to one identity of morphisms of
sheaves in each degree: for `b` homogeneous of degree `k`, the direct image along `π : X' ⟶ X` of
multiplication by `b` on `F'` is, through `ε : ∐ₙ Fₙ ≅ π_* F'`, the degreewise action
`HomogeneousSections.actHom` of `b`. That is `SmulCompatible`, and it splits into three:

* the identification of [Stacks, Tag 01SB]'s functor with the direct image is an equality of
  *objects*, so the direct image of a morphism and the `𝓑`-module morphism it comes from differ
  by an `eqToHom` on either side — that is
  `Stacks.Cohomology.FormalFunctions.restrictScalars_relativeSpecQcohEquivalence_functor_map`;
* multiplication by `b` is multiplication by a section of `𝓑`, so the `𝓑`-linear isomorphism
  `GradedQcohAlgebra.baseChangeModuleIso` commutes with it, and on the coproduct side
  `SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf_hom_sigma_ι_smul` says that
  multiplication by a homogeneous section is degreewise — that is `smul_key`;
* which section of `𝓑` it is, is `IsScalarIdentity`, the one datum tying `f'` to the graded
  sections.

## Main definitions

* `IsScalarIdentity`: the scalar identity. Through [Stacks, Tag 01LX] part (3), the degree-`k`
  inclusion of the section named by a homogeneous `b ∈ 𝒜ₖ` is the function on `X'` by which `b`
  acts on every `𝒪_{X'}`-module.
* `SmulCompatible`: the sheaf-level identity the linearity reduces to.
* `GradedQcohAlgebra.cmp`: **the `B`-linear comparison
  `⨁ₙ Hᵖ(X, Fₙ) ≃ₗ[B] Hᵖ(X', F')`.**

## Main results

* `smulCompatible`: **the sheaf-level identity**, from `IsScalarIdentity`.
* `cmpAddEquiv_smul`: **the comparison is `B`-linear.**
* `moduleFinite_gradedCohomologySum_of_scalarIdentity`: **[Stacks, Tag 0897] part (1)** for an
  arbitrary sheaf of graded algebras, with the base change supplied: `f' : X' ⟶ Spec B` proper
  and the scalar identity. Local Noetherianness of `X'` — which is what makes `F'` coherent — is
  not a hypothesis: it follows from properness of `f'` over the Noetherian `Spec B`, exactly as
  in the source.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.Cohomology.AffineBase Stacks.Cohomology.FormalFunctions
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

variable {X : Scheme.{u}} (D : GradedQcohAlgebra X)
  {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {𝒜 : ℕ → Submodule A B} [_root_.GradedAlgebra 𝒜] (S : HomogeneousSections D.alg 𝒜)
  (M : _root_.SheafOfModules.GradedModule.{u, u, u} D.alg)

/-- **The scalar identity.** Through [Stacks, Tag 01LX] part (3), the degree-`k` inclusion of the
section of `𝓑ₖ` named by a homogeneous `b ∈ 𝒜ₖ` is the function on `X'` by which `b` acts on
every `𝒪_{X'}`-module. This is the one datum tying the structure morphism `f' : X' ⟶ Spec B` to
the graded sections of `𝓑`. -/
def IsScalarIdentity (f' : D.relSpec.left ⟶ Spec (.of B)) : Prop :=
  ∀ (k : ℕ) (b : ↥(𝒜 k)) (U : (Opens ↥X)ᵒᵖ),
    ((pushforwardRingIso D.sheaf).inv.hom.app U).hom
        (D.alg.ungradedIncl (k : ℤ) ((S.sec b).eval U)) =
      _root_.AlgebraicGeometry.baseRingToSections B (Over.mk f')
        (op (D.relSpec.hom ⁻¹ᵁ U.unop)) (b : B)

variable (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)

/-- **The sheaf-level identity the `B`-linearity of the comparison reduces to**: for `b`
homogeneous of degree `k`, the direct image of multiplication by `b` on `F'` is, through `ε`, the
degreewise action `HomogeneousSections.actHom` of `b` on `∐ₙ Fₙ`. -/
def SmulCompatible (f' : D.relSpec.left ⟶ Spec (.of B)) (F' : D.relSpec.left.Modules)
    (ε : (∐ fun n : ℤ => M.piece n) ≅
      (_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj F') : Prop :=
  ∀ (k : ℕ) (n : ℤ) (b : ↥(𝒜 k)),
    S.actHom M b n rfl ≫ Sigma.ι (fun m : ℤ => M.piece m) (n + (k : ℤ)) ≫ ε.hom =
      Sigma.ι (fun m : ℤ => M.piece m) n ≫ ε.hom ≫
        (_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).map
          (letI : Linear B D.relSpec.left.Modules :=
             _root_.AlgebraicGeometry.modulesLinear B (Over.mk f')
           (b : B) • 𝟙 F')

/-- **`ε` on the nose**: the coproduct comparison, then the defining isomorphism of `F'`, then
the identification of [Stacks, Tag 01SB]'s functor with the direct image. -/
theorem coprodPushforwardIso_hom :
    (D.coprodPushforwardIso M hqc).hom =
      M.coprodIntIsoUngradedSheaf.hom ≫
        (_root_.SheafOfModules.restrictScalars (AlgebraSheaf.structureMap D.sheaf)).map
          ((ObjectProperty.ι _).map (D.baseChangeModuleIso M hqc).inv) ≫
        eqToHom (restrictScalars_relativeSpecQcohEquivalence_functor_obj_obj D.sheaf
          ((relativeSpecQcohEquivalence D.sheaf).inverse.obj (D.totalQcoh M hqc))) := rfl

/-- **The identity before the object identification**, for an arbitrary `𝓑`-linear `φ` out of the
total module and an arbitrary endomorphism `T` of its target which is multiplication by the
degree-`k` section named by `b`. -/
private theorem smul_key (k : ℕ) (n : ℤ) (b : ↥(𝒜 k))
    {N : _root_.SheafOfModules.{u} D.alg.ungradedSheaf}
    (φ : _root_.SheafOfModules.GradedModule.ungradedSheaf M ⟶ N) (T : N ⟶ N)
    (hT : ∀ (U : (Opens ↥X)ᵒᵖ) (w : (N.val.obj U : Type u)),
      T.val.app U w = D.alg.ungradedIncl (k : ℤ) ((S.sec b).eval U) • w) :
    S.actHom M b n rfl ≫
        Sigma.ι (fun m : ℤ => M.piece m) (n + (k : ℤ)) ≫
          M.coprodIntIsoUngradedSheaf.hom ≫
          (_root_.SheafOfModules.restrictScalars (AlgebraSheaf.structureMap D.sheaf)).map φ =
      (Sigma.ι (fun m : ℤ => M.piece m) n ≫ M.coprodIntIsoUngradedSheaf.hom ≫
          (_root_.SheafOfModules.restrictScalars (AlgebraSheaf.structureMap D.sheaf)).map φ) ≫
        (_root_.SheafOfModules.restrictScalars (AlgebraSheaf.structureMap D.sheaf)).map T := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  have hA := (M.coprodIntIsoUngradedSheaf_hom_sigma_ι_smul U (k : ℤ) n (n + (k : ℤ)) rfl
    ((S.sec b).eval U) x).symm
  refine Eq.trans (congrArg (fun z => φ.val.app U z) hA) ?_
  refine ((φ.val.app U).hom.map_smul _ _).trans ?_
  refine Eq.trans ?_ (hT U _).symm
  exact congrArg (fun z => D.alg.ungradedIncl (k : ℤ) ((S.sec b).eval U) • z)
    (congrArg (fun y => φ.val.app U y)
      (M.coprodIntIsoUngradedSheaf_hom_sigma_ι U n x).symm)

/-- **The sheaf-level identity**, at the identification `GradedQcohAlgebra.coprodPushforwardIso`,
from the scalar identity. -/
theorem smulCompatible (f' : D.relSpec.left ⟶ Spec (.of B))
    (hsc : IsScalarIdentity D S f') :
    SmulCompatible D S M f' (D.baseChangeModule M hqc) (D.coprodPushforwardIso M hqc) := by
  intro k n b
  let : Linear B D.relSpec.left.Modules :=
    _root_.AlgebraicGeometry.modulesLinear B (Over.mk f')
  rw [coprodPushforwardIso_hom D M hqc]
  exact Stacks.Cohomology.FormalFunctions.rees_assemble
    (smul_key D S M k n b ((ObjectProperty.ι _).map (D.baseChangeModuleIso M hqc).inv)
      ((ObjectProperty.ι _).map ((relativeSpecQcohEquivalence D.sheaf).functor.map
        (ObjectProperty.homMk ((b : B) • 𝟙 (D.baseChangeModule M hqc)))))
      (by
        intro U w
        exact congrArg (fun t : D.relSpec.left.ringCatSheaf.obj.obj
            (op (D.relSpec.hom ⁻¹ᵁ U.unop)) =>
          t • id (α := ((D.baseChangeModule M hqc).val.obj
            (op (D.relSpec.hom ⁻¹ᵁ U.unop)) : Type u)) w)
          (hsc k b U).symm))
    (restrictScalars_relativeSpecQcohEquivalence_functor_map D.sheaf
      (ObjectProperty.homMk ((b : B) • 𝟙 (D.baseChangeModule M hqc))))

/-! ### The comparison is `B`-linear -/

variable (p : ℕ) [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]

attribute [local irreducible] Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward

omit [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] in
/-- Multiplication by a scalar of `B` on `Hᵖ(X', F')`, read through [Stacks, Tag 089W]: it is
`Hᵖ(X, −)` of the direct image of multiplication by that scalar. -/
theorem smul_cohomologyIsoPushforward_inv (f' : D.relSpec.left ⟶ Spec (.of B))
    (F' : D.relSpec.left.Modules) [F'.IsQuasicoherent] (r : B)
    (v : ((((moduleGlobalSections X).rightDerived p).obj
      ((_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj F')) :
        Type u)) :
    specAlgebraRingHom B f' r •
        (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom F' p).inv.hom
          v =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom F' p).inv.hom
        ((((moduleGlobalSections X).rightDerived p).map
          ((_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).map
            (letI : Linear B D.relSpec.left.Modules :=
               _root_.AlgebraicGeometry.modulesLinear B (Over.mk f')
             r • 𝟙 F'))).hom v) := by
  have h := Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_baseSmul
    (Over.mk f') D.relSpec.hom F' p r
    ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom F' p).inv.hom v)
  rw [moduleIso_hom_inv_apply] at h
  exact (moduleIso_inv_hom_apply
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom F' p) _).symm.trans
    (congrArg (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
      D.relSpec.hom F' p).inv.hom h)

omit [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] in
/-- Three composable maps under `Hᵖ(X, −)`, read on elements. -/
theorem cohAddHom_three {N₁ N₂ N₃ N₄ : X.Modules} (φ : N₁ ⟶ N₂) (ψ : N₂ ⟶ N₃) (χ : N₃ ⟶ N₄)
    (x : (cohomologyOf X p N₁ : Type u)) :
    HomogeneousSections.cohAddHom p χ
        (HomogeneousSections.cohAddHom p ψ (HomogeneousSections.cohAddHom p φ x)) =
      HomogeneousSections.cohAddHom p ((φ ≫ ψ) ≫ χ) x :=
  ((HomogeneousSections.cohAddHom_comp p (φ ≫ ψ) χ x).trans
    (congrArg (HomogeneousSections.cohAddHom p χ)
      (HomogeneousSections.cohAddHom_comp p φ ψ x))).symm

/-- **The comparison is semilinear on the generators.** -/
theorem cmpAddEquiv_smul_of (f' : D.relSpec.left ⟶ Spec (.of B))
    (hsc : IsScalarIdentity D S f') (k : ℕ) (n : ℤ) (b : ↥(𝒜 k))
    (x : HomogeneousSections.cohPiece M p n) :
    letI := S.gradedCohomologyModule M p
    D.cmpAddEquiv M hqc p
        ((b : B) • DirectSum.of (fun j : ℤ => HomogeneousSections.cohPiece M p j) n x) =
      specAlgebraRingHom B f' (b : B) •
        D.cmpAddEquiv M hqc p
          (DirectSum.of (fun j : ℤ => HomogeneousSections.cohPiece M p j) n x) := by
  have e2 := congrArg (fun φ : M.piece n ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj
        (D.baseChangeModule M hqc) =>
    HomogeneousSections.cohAddHom p φ x)
    (smulCompatible D S M hqc f' hsc k n b)
  have hL := cohAddHom_three p (S.actHom M b n rfl)
    (Sigma.ι (fun m : ℤ => M.piece m) (n + (k : ℤ)))
    (D.coprodPushforwardIso M hqc).hom x
  have hR := cohAddHom_three p (Sigma.ι (fun m : ℤ => M.piece m) n)
    (D.coprodPushforwardIso M hqc).hom
    ((_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).map
      (let : Linear B D.relSpec.left.Modules :=
         _root_.AlgebraicGeometry.modulesLinear B (Over.mk f')
       (b : B) • 𝟙 (D.baseChangeModule M hqc))) x
  rw [S.smul_of M p b n x]
  refine (D.cmpAddEquiv_of M hqc p (n + (k : ℤ)) _).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => specAlgebraRingHom B f' (b : B) • z)
    (D.cmpAddEquiv_of M hqc p n x)).symm
  refine Eq.trans ?_ (smul_cohomologyIsoPushforward_inv D p f'
    (D.baseChangeModule M hqc) (b : B) _).symm
  refine congrArg (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
    D.relSpec.hom (D.baseChangeModule M hqc) p).inv.hom ?_
  refine hL.trans ?_
  refine Eq.trans ?_ hR.symm
  refine Eq.trans (congrArg (fun φ : M.piece n ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj
        (D.baseChangeModule M hqc) =>
    HomogeneousSections.cohAddHom p φ x) (Category.assoc _ _ _)) ?_
  refine e2.trans ?_
  exact congrArg (fun φ : M.piece n ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj
        (D.baseChangeModule M hqc) =>
    HomogeneousSections.cohAddHom p φ x) (Category.assoc _ _ _).symm

/-- **The comparison is `B`-semilinear**: both sides are additive in the scalar and in the
argument, so the homogeneous generators suffice. -/
theorem cmpAddEquiv_smul (f' : D.relSpec.left ⟶ Spec (.of B)) (hsc : IsScalarIdentity D S f')
    (c : ⨁ k : ℕ, ↥(𝒜 k)) (y : gradedCohomologySum M p) :
    letI := S.gradedCohomologyModule M p
    D.cmpAddEquiv M hqc p ((DirectSum.decomposeRingEquiv 𝒜).symm c • y) =
      specAlgebraRingHom B f' ((DirectSum.decomposeRingEquiv 𝒜).symm c) •
        D.cmpAddEquiv M hqc p y := by
  let := S.gradedCohomologyModule M p
  induction c using DirectSum.induction_on with
  | zero => simp only [map_zero, zero_smul]
  | of k b =>
      have hb : (DirectSum.decomposeRingEquiv 𝒜).symm
          (DirectSum.of (fun j : ℕ => ↥(𝒜 j)) k b) = (b : B) :=
        DirectSum.decompose_symm_of (ℳ := 𝒜) b
      rw [hb]
      induction y using DirectSum.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | of n x => exact cmpAddEquiv_smul_of D S M hqc p f' hsc k n b x
      | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, smul_add]
  | add c c' hc hc' => rw [map_add, add_smul, map_add, hc, hc', map_add, add_smul]

/-- **The `B`-linear comparison `⨁ₙ Hᵖ(X, Fₙ) ≃ₗ[B] Hᵖ(X', F')`** of [Stacks, Tag 0897], with
nothing assumed beyond the scalar identity. -/
def GradedQcohAlgebra.cmp (f' : D.relSpec.left ⟶ Spec (.of B)) (hsc : IsScalarIdentity D S f') :
    letI := S.gradedCohomologyModule M p
    gradedCohomologySum M p ≃ₗ[B]
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom B f')).obj
        (cohomologyOf D.relSpec.left p (D.baseChangeModule M hqc))) :=
  letI := S.gradedCohomologyModule M p
  AddEquiv.toLinearEquiv (D.cmpAddEquiv M hqc p) fun r z => by
    have hr : (DirectSum.decomposeRingEquiv 𝒜).symm (DirectSum.decompose 𝒜 r) = r :=
      (DirectSum.decompose 𝒜).symm_apply_apply r
    have h := cmpAddEquiv_smul D S M hqc p f' hsc (DirectSum.decompose 𝒜 r) z
    rwa [hr] at h

include hqc

/-- **[Stacks, Tag 0897] part (1) for an arbitrary sheaf of graded algebras**, with the base
change supplied: the structure morphism `f' : X' ⟶ Spec B` of the relative spectrum, proper, and
the scalar identity tying it to the graded sections of `𝓑`.

This is `Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedCohomologySum` with
its three remaining binders discharged: `F'` is `GradedQcohAlgebra.baseChangeModule`, coherent by
`GradedQcohAlgebra.isCoherent_baseChangeModule`; the `B`-module structure on the graded
cohomology is `HomogeneousSections.gradedCohomologyModule`; and the `B`-linear comparison is
`GradedQcohAlgebra.cmp`. -/
theorem moduleFinite_gradedCohomologySum_of_scalarIdentity [IsNoetherianRing A]
    [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hft : M.IsFiniteType)
    (f' : D.relSpec.left ⟶ Spec (.of B)) [IsProper f'] (hsc : IsScalarIdentity D S f') :
    letI := S.gradedCohomologyModule M p
    Module.Finite B (gradedCohomologySum M p) :=
  let := S.gradedCohomologyModule M p
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of B)) :=
    _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.mpr hBN
  have hXN : _root_.AlgebraicGeometry.IsLocallyNoetherian D.relSpec.left :=
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f'
  have := D.isCoherent_baseChangeModule M hqc hXN hft
  moduleFinite_gradedCohomologySum A 𝒜 f M hqc hft p f' (D.baseChangeModule M hqc)
    (D.cmp S M hqc p f' hsc)

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
