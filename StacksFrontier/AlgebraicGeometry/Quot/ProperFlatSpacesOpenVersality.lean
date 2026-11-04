module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblem
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesRSStar
public import StacksFrontier.Deformation.Artin.Obstruction.DualNotionOpenVersality

/-!
# Openness of versality for `Spaces'_{fp, flat, proper}` by the `07YZ` route

[Stacks, Remark 0D1P] observes that [Stacks, Lemma 0D3X] — openness of versality for the stack
`Spaces'_{fp, flat, proper}` over `Spec(ℤ)`, and after base change over any Noetherian base —
can be shown with [Stacks, Tag 07YZ]: at an object `x = (X → Spec A)` over an affine chart, the
deformation theory of [Stacks, Section 08V3] presents tangent vectors as
`T¹(M) = Ext¹_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A M)` and obstructions in
`T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)`, and [Stacks, Tag 08JR] makes these `H^i(K ⊗ᴸ_A −)`
for a perfect `K`.

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.chartFunctorDeformationTheory` — the deformation theory
  of `x` valued in `(T¹, T²)` (`Deformation.Artin.FunctorDeformationTheory`), built from a tangent
  isomorphism `T_x(−) ≅ T¹`, the naturality of the obstruction class
  `AlgebraicGeometry.Space.ProperFlatLift.chartObstruction` (the class of [Stacks, Tag 08V5] of
  the extension problem of [Stacks, Section 08V3] posed over `Spec A`), and condition (iv) of
  [Stacks, Tag 07YY]. Its lifting criterion is not an input: it is
  `AlgebraicGeometry.Space.ProperFlatLift.nonempty_lift_iff_chartObstruction_eq_zero`.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.isOpenVersality_cartesianProperFlatProjection` — the
  conclusion of [Stacks, Lemma 0D3X] for `Spaces'_{fp, flat, proper}` over any locally Noetherian
  base ((RS*) being Stacks 0D1J) from, at every chart, the data above together with a perfect
  `K` presenting `(T¹, T²)` compatibly with connecting maps.

## References

* [Stacks Project, Tag 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 07YZ](https://stacks.math.columbia.edu/tag/07YZ)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  (fibered : (cartesianProperFlatProjection B S hS).IsFiberedInGroupoids)
  (rsStar : SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS) fibered)
  [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The deformation theory of `x` valued in `Ext¹`, `Ext²` of the cotangent complex.** With
`T^i = cotangentExtOne/Two (chartStructureMap x hx) (chartBaseRingHom x hx)`, the connecting map
`chartExtConnecting x hx` and the obstruction classes `o(D) = chartObstruction x hx D ∈ T²(I)`
(the class of [Stacks, Tag 08V5] of the extension problem of `X → Spec A ⊂ Spec A'`, posed over
`Spec A`), a tangent isomorphism `τ : T_x(−) ≅ T¹`, the naturality of `o` in the thickening
(07YX (ii)) and condition (iv) of [Stacks, Tag 07YY] for `τ`, `o` and the connecting map form a
deformation theory of `x` in the sense of `Deformation.Artin.FunctorDeformationTheory`. That
`o(D)` vanishes exactly when `x` lifts is
`AlgebraicGeometry.Space.ProperFlatLift.nonempty_lift_iff_chartObstruction_eq_zero`. -/
def chartFunctorDeformationTheory
    (τ : ∀ M : SiteModule A B,
      ((tangentFunctor A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx fibered
          rsStar).functor.obj M : Type _) →ₗ[A]
        ((cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj M.obj : Type _))
    (hτb : ∀ M, Function.Bijective (τ M))
    (hτn : ∀ {M N : SiteModule A B} (f : M ⟶ N)
      (z : (tangentFunctor A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx fibered
        rsStar).functor.obj M),
      τ N ((tangentFunctor A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx fibered
          rsStar).functor.map f z) =
        (cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).map f.hom (τ M z))
    (hon : ∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
      (D₁ : SquareZeroThickening A B S hS toS hA A₁)
      (D₂ : SquareZeroThickening A B S hS toS hA A₂) (f : SquareZeroThickening.Hom D₁ D₂),
      ((cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)).map f.kernelMap)
        (chartObstruction x hx D₁) = chartObstruction x hx D₂)
    (hbd : ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
      (D₁ : SquareZeroThickening A B S hS toS hA A₁)
      (D₂ : SquareZeroThickening A B S hS toS hA A₂)
      (D₃ : SquareZeroThickening A B S hS toS hA A₃)
      (g₂₁ : SquareZeroThickening.Hom D₂ D₁) (g₃₂ : SquareZeroThickening.Hom D₃ D₂),
      IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom →
      ∀ lift₂ : (Under.post (cartesianProperFlatProjection B S hS)).Fiber
        (Under.mk (eqToHom hx ≫ D₂.arrow)),
      ∃ (hzero : g₃₂.kernelMap ≫ g₂₁.kernelMap = 0)
        (hSq : (ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap hzero).ShortExact)
        (hmem : B.Contains (Spec (squareZeroRing A D₁.kernel)))
        (s : A →+* A₁) (ψ : A₂ →+* (squareZeroRing A D₁.kernel : Type u))
        (_hs : g₂₁.ringHom.comp g₃₂.ringHom = s.comp D₃.q)
        (_hψfst : ∀ y : A₂, (ψ y).fst = D₂.q y)
        (_hψsnd : ∀ y : A₂, ((ψ y).snd).1 = g₂₁.ringHom y - s (D₂.q y)),
        letI M₁ : SiteModule A B := ⟨D₁.kernel, hmem⟩
        ∃ (dMap : squareZeroOver A B S hS toS M₁ ⟶ (Over.mk D₂.toS' : BigFppfOver B S hS))
          (lift₁ : (Under.post (cartesianProperFlatProjection B S hS)).Fiber
            (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M₁)))
          (φ : lift₁.1.right ⟶ lift₂.1.right),
          B.inclusion.map dMap.left = Spec.map (CommRingCat.ofHom ψ) ∧
          squareZeroArrow A B S hS toS hA M₁ ≫ dMap = D₂.arrow ∧
          (cartesianProperFlatProjection B S hS).IsStronglyCartesian dMap φ ∧
          lift₁.1.hom ≫ φ = lift₂.1.hom ∧
            chartObstruction x hx D₃ =
              chartExtConnecting x hx hSq (τ M₁
                (((tangentFunctor A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx
                    fibered rsStar).liftEquiv M₁).symm (Quotient.mk _ lift₁)))) :
    FunctorDeformationTheory A B S hS toS hA (CartesianProperFlatSpaces B S hS)
      (cartesianProperFlatProjection B S hS) x hx fibered rsStar where
  T₁ := cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)
  T₂ := cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)
  δ hSq := chartExtConnecting x hx hSq
  tangentMap := τ
  tangentBijective := hτb
  tangentNatural := hτn
  obstruction _ _ D := chartObstruction x hx D
  obstructionNatural := hon
  obstruction_iff_lift _ _ D := nonempty_lift_iff_chartObstruction_eq_zero x hx D
  boundary := hbd

section OpenVersality

variable (B S hS) in
-- `Deformation.Artin.derivedCohomology` and `Deformation.Artin.boundaryMap`, in the hypothesis
-- below, are stated in the standard model of `D(A)`.
attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Openness of versality for `Spaces'_{fp, flat, proper}` by the `07YZ` route** (the
conclusion of [Stacks, Lemma 0D3X], over any locally Noetherian base `S`, as in
[Stacks, Remark 0D1P]). The stack satisfies (RS*) ([Stacks, Lemma 0D1J],
`AlgebraicGeometry.satisfiesRSStar_cartesianProperFlatProjection`). Assume that every
object `x = (X → Spec A)` with `A` of finite type over an affine chart `Spec Λ ⊆ S` carries a
deformation theory valued in a pair of functors (`Deformation.Artin.FunctorDeformationTheory`,
condition (iv) of [Stacks, Tag 07YY] included) presented by a perfect `K ∈ D(A)` compatibly with
connecting maps (`chartTheory`). Then for every scheme `U`
locally of finite type over `S`, every object `x` over `U` and every finite type point `u₀` of `U`
at which `x` is versal, `x` is versal at every finite type point of an open neighbourhood
of `u₀`. -/
theorem isOpenVersality_cartesianProperFlatProjection
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (chartTheory : ∀ (c : AffineChart S)
      (P : ChartedObject B S hS (cartesianProperFlatProjection B S hS) c),
      Algebra.FiniteType c.ring P.ring →
      ∃ (T : FunctorDeformationTheory P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem
          (CartesianProperFlatSpaces B S hS) (cartesianProperFlatProjection B S hS) P.point
          P.obj.obj.2 (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)
          (satisfiesRSStar_cartesianProperFlatProjection B S hS))
        (K : DerivedCategory (ModuleCat.{u} P.ring))
        (e₁ : derivedCohomology P.ring K 1 ≅ T.T₁) (e₂ : derivedCohomology P.ring K 2 ≅ T.T₂),
        StacksDraft.Perfect.IsPerfect K ∧
          ∀ {Sq : ShortComplex (ModuleCat.{u} P.ring)} (hSq : Sq.ShortExact),
            boundaryMap P.ring K hSq ≫ e₂.hom.app Sq.X₁ = e₁.hom.app Sq.X₃ ≫ T.δ hSq)
    (U : Over S) (hUft : LocallyOfFiniteType U.hom) (x : CartesianProperFlatSpaces B S hS)
    (hx : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : IsVersalAt U (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) u₀ x
      hx) :
    ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
      ∀ u ∈ V.1, AlgebraicGeometry.IsFiniteTypePoint u →
        IsVersalAt U (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) u x hx :=
  DualNotion.isOpenVersality_of_functorDeformationTheory
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)
    (satisfiesRSStar_cartesianProperFlatProjection B S hS) chartTheory U hUft x hx u₀
    hu₀ hversal

end OpenVersality

end AlgebraicGeometry.Space.ProperFlatLift

end
