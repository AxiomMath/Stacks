module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenness
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Perfect.FiniteTorDimension
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# Openness of versality for a dual deformation situation

Let `x` be an object of a category fibred in groupoids over the big fppf site of a locally
Noetherian scheme `S`, lying over `U = Spec A` with `A` of finite type over the ring `Λ` of an
affine open `Spec Λ ⊆ S`, and suppose the deformation theory of `x` is presented by a complex
`K` of `A`-modules as in a dual deformation situation: `T_x(-) = H¹(K ⊗ᴸ_A -)` and every
square-zero thickening `A' → A` with kernel `I` carries an obstruction element in
`H²(K ⊗ᴸ_A I)`. If `K` is a perfect object of `D(A)` and the obstruction elements satisfy the
boundary condition on short exact sequences of deformation situations, then versality of `x` at
a closed point `u₀ ∈ U` propagates to every finite type point of an open neighbourhood of `u₀`.

## Main definitions

* `Deformation.Artin.DualNotion.ObstructionBoundaryCondition` — the boundary condition on short
  exact sequences of deformation situations.
* `Deformation.Artin.DualNotion.OpennessInput` — the two assumptions on a morphism
  `ξ : E ⟶ NL_{A/Λ}` of `D(A)` which the dual notion is turned into: the lifting criterion
  across every deformation situation, and an isomorphism `T_x(-) ⟶ Ext⁰_A(E, -)` carrying the
  canonical element to `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`.

## Main results

* `Deformation.Artin.DualNotion.versalityBase` — the object `x` of a dual deformation situation
  lies over `Spec A`, viewed as a scheme over `S`.
* `Deformation.Artin.DualNotion.minus_of_isPerfect` and
  `Deformation.Artin.DualNotion.isNoetherianRing_of_dualDeformationSituation` — a perfect object
  is bounded above, and the ring of a dual deformation situation is Noetherian.

## Implementation notes

The boundary condition is the source's condition (iv), which is a hypothesis of the lemma; it
is written out here with the same data as `Deformation.Artin.DualDeformationSituation`, namely
square-zero thickenings of `Spec A` inside the chosen big fppf site and their morphisms, so
that the canonical identification `A₁' = A[I₁]` of a short exact sequence of deformation
situations is recorded by the splitting `s` and the ring map `ψ` rather than assumed.

The source's assumptions (i) and (ii) of openness of versality are collected in
`Deformation.Artin.DualNotion.OpennessInput`, at a morphism `ξ : E ⟶ NL_{A/Λ}` out of an
arbitrary object of `D(A)`; the lifting criterion is phrased on the square-zero thickenings of
the dual situation, and the `Λ`-algebra structure of a thickening is pinned to its surjection
and to the affine open of the base by equations rather than imposed. Assumption (iii), that the
cohomology of `E` is finite over `A`, is not part of that data.

## References

* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin.DualNotion

attribute [local instance] HasDerivedCategory.standard

/-! ### Cohomology of a perfect complex -/

/-- A perfect object of `D(A)` is bounded above. -/
public lemma minus_of_isPerfect {A : Type u} [CommRing A]
    (E : DerivedCategory (ModuleCat.{u} A)) (hE : StacksDraft.Perfect.IsPerfect E) :
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E := by
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := hE
  refine (DerivedCategory.minus_iff E).2 ⟨b + 1, fun n hn => ?_⟩
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso e)
  exact DerivedCategory.isZero_of_isLE _ b n (by lia)

/-! ### The boundary condition and the input of openness of versality -/

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)

/-- For a short exact sequence of deformation situations and a lift of `x` over the middle
one, the obstruction element of the smallest one is the boundary of the tangent class of the
restriction of that lift along the canonical identification `A₁' = A[I₁]`. -/
public def ObstructionBoundaryCondition : Prop :=
  ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
    (D₁ : SquareZeroThickening A B S hS toS hA A₁)
    (D₂ : SquareZeroThickening A B S hS toS hA A₂)
    (D₃ : SquareZeroThickening A B S hS toS hA A₃)
    (g₂₁ : SquareZeroThickening.Hom D₂ D₁) (g₃₂ : SquareZeroThickening.Hom D₃ D₂),
    IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom →
    ∀ lift₂ : (Under.post p).Fiber (Under.mk (eqToHom sit.hx ≫ D₂.arrow)),
    ∃ (hzero : g₃₂.kernelMap ≫ g₂₁.kernelMap = 0)
      (hSq : (ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap hzero).ShortExact)
      (hmem : B.Contains (Spec (squareZeroRing A D₁.kernel)))
      (s : A →+* A₁) (ψ : A₂ →+* (squareZeroRing A D₁.kernel : Type u))
      (_hs : g₂₁.ringHom.comp g₃₂.ringHom = s.comp D₃.q)
      (_hψfst : ∀ y : A₂, (ψ y).fst = D₂.q y)
      (_hψsnd : ∀ y : A₂, ((ψ y).snd).1 = g₂₁.ringHom y - s (D₂.q y)),
      letI M₁ : SiteModule A B := ⟨D₁.kernel, hmem⟩
      ∃ (dMap : squareZeroOver A B S hS toS M₁ ⟶ (Over.mk D₂.toS' : BigFppfOver B S hS))
        (lift₁ : (Under.post p).Fiber
          (Under.mk (eqToHom sit.hx ≫ squareZeroArrow A B S hS toS hA M₁)))
        (φ : lift₁.1.right ⟶ lift₂.1.right),
        B.inclusion.map dMap.left = Spec.map (CommRingCat.ofHom ψ) ∧
        squareZeroArrow A B S hS toS hA M₁ ≫ dMap = D₂.arrow ∧
        p.IsStronglyCartesian dMap φ ∧ lift₁.1.hom ≫ φ = lift₂.1.hom ∧
          sit.obstruction A₃ D₃ =
            boundaryMap A sit.K hSq
              (sit.tangentMap M₁
                (((tangentFunctor A B S hS toS hA p sit.x sit.hx sit.fibered
                    sit.rsStar).liftEquiv M₁).symm (Quotient.mk _ lift₁)))

/-- Assumptions (i) and (ii) of openness of versality for a morphism
`ξ : E ⟶ NL_{A/Λ}` of `D(A)` at the object `x` of a dual deformation situation: for every
deformation situation `(x, A' → A)` the object `x` lifts to `Spec A'` exactly when the
composition `E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` vanishes, and there is an isomorphism of functors
`T_x(-) ⟶ Ext⁰_A(E, -)` under which `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}` is the image of the canonical
element of `T_x(Ω_{A/Λ})`. -/
public structure OpennessInput
    (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
    (E : DerivedCategory (ModuleCat.{u} A)) (ξ : E ⟶ derivedNaiveCotangentComplex Λ A) where
  /-- Assumption (i): the lifting criterion across a deformation situation. -/
  hasLift_iff_xi_comp_eq_zero : ∀ (A' : Type u) [CommRing A']
      (D : SquareZeroThickening A B S hS toS hA A') [Algebra Λ A'] [Algebra A' A]
      [IsScalarTower Λ A' A] (_hmap : algebraMap A' A = D.q)
      (_hchart : Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ sit.affineOpen =
        B.inclusion.map D.toS'),
    Nonempty ((Under.post p).Fiber (Under.mk (eqToHom sit.hx ≫ D.arrow))) ↔
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0
  /-- Assumption (ii): the transformation `T_x(M) ⟶ Ext⁰_A(E, M)`. -/
  tangentMap : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar).functor.obj M :
        Type (max (u + 1) v w)) →
      DerivedCategory.Ext E
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj) 0
  /-- Assumption (ii): the transformation is additive. -/
  tangentMap_add : ∀ (M : SiteModule A B)
      (a a' : ((tangentFunctor A B S hS toS hA p sit.x sit.hx sit.fibered
        sit.rsStar).functor.obj M : Type (max (u + 1) v w))),
    tangentMap M (a + a') = tangentMap M a + tangentMap M a'
  /-- Assumption (ii): the transformation is natural in the coefficient module. -/
  tangentMap_natural : ∀ (M N : SiteModule A B) (f : M ⟶ N)
      (a : ((tangentFunctor A B S hS toS hA p sit.x sit.hx sit.fibered
        sit.rsStar).functor.obj M : Type (max (u + 1) v w))),
    tangentMap N ((tangentFunctor A B S hS toS hA p sit.x sit.hx sit.fibered
        sit.rsStar).functor.map f a) =
      extPushforward E f.hom 0 (tangentMap M a)
  /-- Assumption (ii): the transformation is an isomorphism. -/
  tangentMap_bijective : ∀ M : SiteModule A B, Function.Bijective (tangentMap M)
  /-- Assumption (ii): the canonical element of `T_x(Ω_{A/Λ})` goes to the composition
  `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`. -/
  tangentMap_canonicalElement :
    tangentMap (differentialsSiteModule Λ A B hΩ)
        (canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar hΩ
          sit.affineOpen sit.factorization).element =
      ShiftedHom.mk₀ (0 : ℤ) rfl (ξ ≫ naiveCotangentToDifferentials Λ A)

/-! ### Openness of versality -/

/-- The object `x` of a dual deformation situation lies over `Spec A`, viewed as a scheme over
`S`. -/
public theorem versalityBase :
    (p ⋙ Over.post B.inclusion).obj sit.x = Over.mk toS :=
  congrArg ((Over.post B.inclusion).obj) sit.hx

include sit in
/-- The ring of a dual deformation situation is Noetherian: it is of finite type over the ring
of an affine open of a locally Noetherian base. -/
public lemma isNoetherianRing_of_dualDeformationSituation : IsNoetherianRing A := by
  have := sit.openImmersion
  have : IsNoetherianRing Λ := (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp
    (isLocallyNoetherian_of_isOpenImmersion sit.affineOpen)
  have := sit.finiteType
  exact Algebra.FiniteType.isNoetherianRing Λ A

end Deformation.Artin.DualNotion

end
