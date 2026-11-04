module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy
public import StacksFrontier.RingTheory.Koszul.Cone

/-!
# The stalk of the restriction of relative differential forms to a subscheme

Let `i : Z ⟶ X` be a morphism of schemes and let `π : X ⟶ S`. The restriction of relative
differential forms `AlgebraicGeometry.Scheme.Hom.formRestriction`,

`Ω^p_{X/S} ⟶ i_*Ω^p_{Z/S}`,

is the adjoint transpose of the canonical map of [Stacks, Tag 01UV] in degree `p`. This file
identifies its stalk at a point `i z` of `X` with `KaehlerDifferential.mapExteriorPower`, the
`p`-th exterior power of the comparison of Kähler differentials of the local rings, through the
identification of the stalk of `Ω^p_{X/S}` with `⋀^p_{𝒪_{X,x}} Ω[𝒪_{X,x}⁄𝒪_{S,π x}]`.

## Main definitions

* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkEquiv`: the stalk of
  `Ω^p_{X/S}` is the `p`-th exterior power of the stalk of `Ω_{X/S}`, Tag 01CH in degree `p`.
* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv`: **the stalk
  of `Ω^p_{X/S}` at `x` is `⋀^p_{𝒪_{X,x}} Ω[𝒪_{X,x}⁄𝒪_{S,π x}]`**, the previous identification
  followed by the `p`-th exterior power of
  `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`.

## Main results

* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv_germ`: **the
  identification on the germ of an exact wedge.** The germ at `x` of the local section
  `d b₁ ∧ ⋯ ∧ d b_p` goes to `D(germ b₁) ∧ ⋯ ∧ D(germ b_p)`. Such germs generate the stalk, so
  this formula determines the identification.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_homogeneousProd`: pulling back
  a differential form along a commutative square carries the ordered product of degree-one local
  sections to the ordered product of their pullbacks.
* `KaehlerDifferential.ext_of_wedge_gens`: two additive maps out of `⋀^p_R Ω[R⁄A]` which are
  semilinear over a ring map `R → R'` and agree on the wedges `D c₁ ∧ ⋯ ∧ D c_p` are equal.
* `Stacks.GysinStalk.formsStalkMapEquation_germ`: the stalk square on the germ of an exact
  wedge, the generator case of the result below.
* `Stacks.GysinStalk.formsStalkMapEquation`: **the stalk of
  `AlgebraicGeometry.Scheme.Hom.formRestriction` is `KaehlerDifferential.mapExteriorPower`.**

## What this does not do

Nothing here is about log poles or about effective Cartier divisors. The consumer of
`Stacks.GysinStalk.formsStalkMapEquation` is the identification of the stalk of the subsheaf
`AlgebraicGeometry.Scheme.Hom.formRestrictionKernel` of forms vanishing on a divisor with
`Stacks.LogPoles.logSubmodule`, which this file does not carry out: that needs the kernel-stalk
comparison `Stacks.SheafOfModules.TensorStalkRingedSpace.kernelStalkLinearEquiv` on top of the
square proved here.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.RelativeDifferentialStalkMap

universe u

/-! ### The stalk of the sheaf of relative differential forms -/

namespace Stacks.RelativeDifferentialStalkMap

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (p : ℕ)

/-- The `𝒪_{X,x}`-module structure on the stalk at `x` of `Ω^p_{X/S}`. -/
abbrev moduleStalkRelativeDifferentialForms : Module (ToType (X.presheaf.stalk x))
    (ToType ((relativeDifferentialForms f (p : ℤ)).presheaf.stalk x)) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) (relativeDifferentialForms f (p : ℤ)).val x

/-- The `𝒪_{X,x}`-module structure on the stalk at `x` of `Ω_{X/S}`. -/
abbrev moduleStalkRelativeDifferentials : Module (ToType (X.presheaf.stalk x))
    (ToType ((relativeDifferentials f).presheaf.stalk x)) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) (relativeDifferentials f).val x

/-- **Stacks Project, Tag 01CH in degree `p` for the relative differentials of a morphism of
schemes.** The stalk at `x` of `Ω^p_{X/S}` is the `p`-th exterior power of the stalk of
`Ω_{X/S}`. -/
def relativeDifferentialFormsStalkEquiv :
    letI := moduleStalkRelativeDifferentialForms f x p
    letI := moduleStalkRelativeDifferentials f x
    ToType ((relativeDifferentialForms f (p : ℤ)).presheaf.stalk x)
      ≃ₗ[ToType (X.presheaf.stalk x)]
      ⋀[ToType (X.presheaf.stalk x)]^p
        (ToType ((relativeDifferentials f).presheaf.stalk x)) :=
  SheafOfModules.exteriorPowerStalkEquiv
    (Scheme.Modules.exteriorAlgebra (relativeDifferentials f))
    (Scheme.Modules.exteriorGenerator _)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) p x

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- **The stalk at `x` of the sheaf `Ω^p_{X/S}` of relative differential `p`-forms is
`⋀^p_{𝒪_{X,x}} Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`**: Tag 01CH in degree `p` followed by the `p`-th exterior
power of Tag 01V0 at `x`. -/
def relativeDifferentialFormsStalkKaehlerEquiv :
    letI := moduleStalkRelativeDifferentialForms f x p
    letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    ToType ((relativeDifferentialForms f (p : ℤ)).presheaf.stalk x)
      ≃ₗ[ToType (X.presheaf.stalk x)]
      ⋀[ToType (X.presheaf.stalk x)]^p
        (KaehlerDifferential (ToType (S.presheaf.stalk (f x)))
          (ToType (X.presheaf.stalk x))) :=
  letI := moduleStalkRelativeDifferentialForms f x p
  letI := moduleStalkRelativeDifferentials f x
  letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  (relativeDifferentialFormsStalkEquiv f x p).trans
    (Koszul.exteriorPowerLinearEquiv p (relativeDifferentialsStalkKaehlerEquiv f x))

/-- **The identification of the stalk of `Ω^p_{X/S}` on the germ of an exact wedge.** The germ at
`x` of the local section `d b₁ ∧ ⋯ ∧ d b_p` of `Ω^p_{X/S}` goes to the wedge
`D(germ b₁) ∧ ⋯ ∧ D(germ b_p)` of the universal `𝒪_{S,f x}`-differentials of the germs.

Such wedges span `⋀^p_{𝒪_{X,x}} Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`, so this formula determines the
identification. -/
theorem relativeDifferentialFormsStalkKaehlerEquiv_germ (U : X.Opens) (hx : x ∈ U)
    (b : Fin p → Γ(X, U)) :
    letI := moduleStalkRelativeDifferentialForms f x p
    letI : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
      (f.stalkMap x).hom.toAlgebra
    relativeDifferentialFormsStalkKaehlerEquiv f x p (TopCat.Presheaf.germ
        (relativeDifferentialForms f (p : ℤ)).val.presheaf U x hx
        ((relativeDifferentialFormsAlgebra f).toPresheafGradedAlgebra.homogeneousProd (op U) p
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app (op U)
            ((universalRelativeDerivation f).d (b j)))) =
      exteriorPower.ιMulti (ToType (X.presheaf.stalk x)) p
        fun j => KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
          (ToType (X.presheaf.stalk x)) ((X.presheaf.germ U x hx).hom (b j)) := by
  let := moduleStalkRelativeDifferentialForms f x p
  let := moduleStalkRelativeDifferentials f x
  let : Algebra (ToType (S.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  refine Eq.trans (congrArg
    (Koszul.exteriorPowerLinearEquiv p (relativeDifferentialsStalkKaehlerEquiv f x))
    (SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd
      (Scheme.Modules.exteriorAlgebra (relativeDifferentials f))
      (Scheme.Modules.exteriorGenerator _)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) p x U hx
      (fun j => (universalRelativeDerivation f).d (b j)))) ?_
  refine Eq.trans (exteriorPower.map_apply_ιMulti _ _) ?_
  refine congrArg _ (funext fun j => ?_)
  exact relativeDifferentialsStalkKaehlerEquiv_germ_d f x
    (OrderDual.toDual (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) (b j)

/-- **Finitely many germs at a point come from one open neighbourhood.** -/
theorem exists_germ_eq_of_fin {Y : Scheme.{u}} (y : Y) {n : ℕ}
    (c : Fin n → ToType (Y.presheaf.stalk y)) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (b : Fin n → Γ(Y, U)),
      ∀ j, (Y.presheaf.germ U y hy).hom (b j) = c j := by
  choose W hW t ht using fun j : Fin n => Y.presheaf.exists_germ_eq (c j)
  have hy : y ∈ (⨅ j, W j : TopologicalSpace.Opens Y) := by
    have h : y ∈ (↑(⨅ j, W j) : Set Y) := by
      rw [TopologicalSpace.Opens.coe_iInf]; exact Set.mem_iInter.2 hW
    exact h
  refine ⟨⨅ j, W j, hy,
    fun j => (Y.presheaf.map (homOfLE (iInf_le W j)).op).hom (t j), fun j => ?_⟩
  exact Eq.trans (Y.presheaf.germ_res_apply (homOfLE (iInf_le W j)) y _ (t j)) (ht j)

end Stacks.RelativeDifferentialStalkMap

/-! ### Pulling back an ordered product of exact differentials -/

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (a : X ⟶ S) (a' : X' ⟶ S') (g : S' ⟶ S)
  (hcomm : f ≫ a = a' ≫ g)

/-- **Pulling back a differential form carries an ordered product of degree-one local sections to
the ordered product of their pullbacks.** The ordered product of
`Stacks.GradedAlgebra.homogeneousProd` multiplies on the right, in degree `(p : ℤ) + 1`, which is
the degree the multiplicativity of the pullback produces, so no degree transport appears. -/
theorem relativeDifferentialFormsPullback_homogeneousProd (q : ℕ) (U : X.Opens)
    (zz : Fin q → Γ(relativeDifferentialForms a 1, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm ((q : ℕ) : ℤ) U
        ((relativeDifferentialFormsAlgebra a).toPresheafGradedAlgebra.homogeneousProd
          (op U) q zz) =
      (relativeDifferentialFormsAlgebra a').toPresheafGradedAlgebra.homogeneousProd
        (op (f ⁻¹ᵁ U)) q fun j =>
          relativeDifferentialFormsPullback f a a' g hcomm 1 U (zz j) := by
  induction q with
  | zero => exact relativeDifferentialFormsPullback_one f a a' g hcomm U
  | succ q ih =>
      refine Eq.trans (relativeDifferentialFormsPullback_mul f a a' g hcomm (q : ℤ) 1 U
        ((relativeDifferentialFormsAlgebra a).toPresheafGradedAlgebra.homogeneousProd (op U) q
          (fun j => zz j.castSucc)) (zz (Fin.last q))) ?_
      exact congrArg (fun w => ((relativeDifferentialFormsAlgebra a').mul (q : ℤ) 1).app
          (op (f ⁻¹ᵁ U)) w
          (relativeDifferentialFormsPullback f a a' g hcomm 1 U (zz (Fin.last q))))
        (ih fun j => zz j.castSucc)

end AlgebraicGeometry.Scheme.Hom

/-! ### An extensionality principle for maps out of `⋀^p Ω` -/

namespace KaehlerDifferential

/-- **Two additive maps out of `⋀^p_R Ω[R⁄A]`, semilinear over a map of `A`-algebras `R → R'`,
which agree on the wedges `D c₁ ∧ ⋯ ∧ D c_p`, are equal.** Those wedges and their `R`-multiples
span `⋀^p_R Ω[R⁄A]` by `Crystalline.span_range_smul_ιMulti_eq_top`. -/
theorem ext_of_wedge_gens (A R R' : Type*) [CommRing A] [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R'] (q : ℕ)
    {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N]
    (Φ Ψ : (⋀[R]^q (Ω[R⁄A])) → N)
    (hΦ0 : Φ 0 = 0) (hΨ0 : Ψ 0 = 0)
    (hΦadd : ∀ w w', Φ (w + w') = Φ w + Φ w')
    (hΨadd : ∀ w w', Ψ (w + w') = Ψ w + Ψ w')
    (hΦsmul : ∀ (r : R) w, Φ (r • w) = algebraMap R R' r • Φ w)
    (hΨsmul : ∀ (r : R) w, Ψ (r • w) = algebraMap R R' r • Ψ w)
    (hgen : ∀ c : Fin q → R,
      Φ (exteriorPower.ιMulti R q fun j => KaehlerDifferential.D A R (c j)) =
        Ψ (exteriorPower.ιMulti R q fun j => KaehlerDifferential.D A R (c j)))
    (ξ : ⋀[R]^q (Ω[R⁄A])) : Φ ξ = Ψ ξ := by
  let : IsScalarTower R R (Ω[R⁄A]) := ⟨fun x y w => mul_smul x y w⟩
  have htop := Crystalline.span_range_smul_ιMulti_eq_top (R := R)
    (KaehlerDifferential.D A R) (KaehlerDifferential.span_range_derivation A R) q
  have hmem : ξ ∈ Submodule.span R (Set.range fun c : Fin (q + 1) → R =>
      c 0 • (exteriorPower.ιMulti R q) fun j => KaehlerDifferential.D A R (c j.succ)) := by
    rw [htop]; exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | zero => rw [hΦ0, hΨ0]
  | add w w' _ _ hw hw' => rw [hΦadd, hΨadd, hw, hw']
  | smul r w _ hw => rw [hΦsmul, hΨsmul, hw]
  | mem w hw =>
      obtain ⟨c, rfl⟩ := hw
      rw [hΦsmul, hΨsmul, hgen fun j => c j.succ]

end KaehlerDifferential

/-! ### The stalk of the restriction of forms to a subscheme -/

namespace Stacks.GysinStalk

variable {X S Z : Scheme.{u}} (i : Z ⟶ X) (π : X ⟶ S) (z : Z) (p : ℕ)

/-- `𝒪_{X, i z}` as an algebra over `𝒪_{S, (i ≫ π) z}`. -/
abbrev algebraAmbient : Algebra (ToType (S.presheaf.stalk ((i ≫ π) z)))
    (ToType (X.presheaf.stalk (i.base z))) := (π.stalkMap (i.base z)).hom.toAlgebra

/-- `𝒪_{Z, z}` as an algebra over `𝒪_{S, (i ≫ π) z}`. -/
abbrev algebraSub : Algebra (ToType (S.presheaf.stalk ((i ≫ π) z)))
    (ToType (Z.presheaf.stalk z)) := ((i ≫ π).stalkMap z).hom.toAlgebra

/-- `𝒪_{Z, z}` as an algebra over `𝒪_{X, i z}`. -/
abbrev algebraRestriction {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    Algebra (ToType (X.presheaf.stalk (i.base z))) (ToType (Z.presheaf.stalk z)) :=
  (i.stalkMap z).hom.toAlgebra

/-- The three algebra structures on the local rings form a scalar tower: the stalk map of a
composite is the composite of the stalk maps. -/
theorem isScalarTower_stalk_comp :
    letI := algebraAmbient i π z
    letI := algebraSub i π z
    letI := algebraRestriction i z
    IsScalarTower (ToType (S.presheaf.stalk ((i ≫ π) z)))
      (ToType (X.presheaf.stalk (i.base z))) (ToType (Z.presheaf.stalk z)) := by
  let := algebraAmbient i π z
  let := algebraSub i π z
  let := algebraRestriction i z
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show ((i ≫ π).stalkMap z).hom a = (i.stalkMap z).hom ((π.stalkMap (i.base z)).hom a)
  rw [Scheme.Hom.stalkMap_comp]
  rfl

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (i.base z)))]
  [DecidableEq (OrderDual (TopologicalSpace.OpenNhds z))]

/-- The identification of the stalk of `Ω^p_{X/S}` at `i z` with an exterior power of Kähler
differentials, read over the local ring of `S` at `(i ≫ π) z` rather than at `π (i z)`. The two
points are equal by `rfl`; this is the one place the two spellings are crossed. -/
def formsStalkKaehlerEquivAt :
    letI := Stacks.GysinStalk.algebraAmbient i π z
    letI := Stacks.RelativeDifferentialStalkMap.moduleStalkRelativeDifferentialForms π
      (i.base z) p
    ToType ((relativeDifferentialForms π (p : ℤ)).presheaf.stalk (i.base z))
      ≃ₗ[ToType (X.presheaf.stalk (i.base z))]
      ⋀[ToType (X.presheaf.stalk (i.base z))]^p
        (KaehlerDifferential (ToType (S.presheaf.stalk ((i ≫ π) z)))
          (ToType (X.presheaf.stalk (i.base z)))) :=
  Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv π
    (i.base z) p

omit [DecidableEq (OrderDual (TopologicalSpace.OpenNhds z))] in
/-- `Stacks.GysinStalk.formsStalkKaehlerEquivAt` on the germ of an exact wedge. -/
theorem formsStalkKaehlerEquivAt_germ (U : X.Opens) (hxU : i.base z ∈ U)
    (b : Fin p → Γ(X, U)) :
    letI := Stacks.GysinStalk.algebraAmbient i π z
    letI := Stacks.RelativeDifferentialStalkMap.moduleStalkRelativeDifferentialForms π
      (i.base z) p
    formsStalkKaehlerEquivAt i π z p (TopCat.Presheaf.germ
        (relativeDifferentialForms π (p : ℤ)).val.presheaf U (i.base z) hxU
        ((relativeDifferentialFormsAlgebra π).toPresheafGradedAlgebra.homogeneousProd (op U) p
          fun j => (Scheme.Modules.exteriorGenerator (relativeDifferentials π)).val.app (op U)
            ((universalRelativeDerivation π).d (b j)))) =
      exteriorPower.ιMulti (ToType (X.presheaf.stalk (i.base z))) p
        fun j => KaehlerDifferential.D (ToType (S.presheaf.stalk ((i ≫ π) z)))
          (ToType (X.presheaf.stalk (i.base z)))
          ((X.presheaf.germ U (i.base z) hxU).hom (b j)) :=
  Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv_germ π
    (i.base z) p U hxU b

omit [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (i.base z)))] in
/-- **The stalk square on the germ of an exact wedge.** The stalk at `i z` of
`AlgebraicGeometry.Scheme.Hom.formRestriction`, read on the germ of `d b₁ ∧ ⋯ ∧ d b_p` and
transported to the stalk of `Ω^p_{Z/S}` at `z`, is the wedge of the universal differentials of
the images of the germs of the `b_j` under the stalk map of `i`. -/
theorem formsStalkMapEquation_germ (U : X.Opens) (hxU : i.base z ∈ U) (b : Fin p → Γ(X, U)) :
    letI := Stacks.GysinStalk.algebraSub i π z
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
        (i ≫ π) z p (Stacks.Chow.stalkPushforwardComparison i
        (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
        (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
          (TopCat.Presheaf.germ (relativeDifferentialForms π (p : ℤ)).val.presheaf U
            (i.base z) hxU
            ((relativeDifferentialFormsAlgebra π).toPresheafGradedAlgebra.homogeneousProd
              (op U) p fun j => (Scheme.Modules.exteriorGenerator
                (relativeDifferentials π)).val.app (op U)
                ((universalRelativeDerivation π).d (b j)))))) =
      exteriorPower.ιMulti (ToType (Z.presheaf.stalk z)) p
        fun j => KaehlerDifferential.D (ToType (S.presheaf.stalk ((i ≫ π) z)))
          (ToType (Z.presheaf.stalk z))
          ((i.stalkMap z).hom ((X.presheaf.germ U (i.base z) hxU).hom (b j))) := by
  let := Stacks.GysinStalk.algebraSub i π z
  have hcomm : i ≫ π = (i ≫ π) ≫ 𝟙 S := by simp
  have hinner :
      PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
          (TopCat.Presheaf.germ (relativeDifferentialForms π (p : ℤ)).val.presheaf U
            (i.base z) hxU
            ((relativeDifferentialFormsAlgebra π).toPresheafGradedAlgebra.homogeneousProd
              (op U) p fun j => (Scheme.Modules.exteriorGenerator
                (relativeDifferentials π)).val.app (op U)
                ((universalRelativeDerivation π).d (b j)))) =
        TopCat.Presheaf.germ ((Scheme.Modules.pushforward i).obj
            (relativeDifferentialForms (i ≫ π) (p : ℤ))).val.presheaf U (i.base z) hxU
          ((relativeDifferentialFormsAlgebra (i ≫ π)).toPresheafGradedAlgebra.homogeneousProd
            (op (i ⁻¹ᵁ U)) p fun j => (Scheme.Modules.exteriorGenerator
              (relativeDifferentials (i ≫ π))).val.app (op (i ⁻¹ᵁ U))
              ((universalRelativeDerivation (i ≫ π)).d ((i.app U).hom (b j)))) := by
    refine Eq.trans (PresheafOfModules.stalkMapL_germ (R := X.sheaf.presheaf) (i.base z)
      (formRestriction i π (p : ℤ)).val U hxU _) ?_
    refine congrArg _ ?_
    refine Eq.trans (relativeDifferentialFormsPullback_homogeneousProd i π (i ≫ π) (𝟙 S)
      hcomm p U (fun j => (Scheme.Modules.exteriorGenerator
        (relativeDifferentials π)).val.app (op U)
        ((universalRelativeDerivation π).d (b j)))) ?_
    exact congrArg _ (funext fun j =>
      relativeDifferentialFormsPullback_exteriorGenerator_d i π (i ≫ π) (𝟙 S) hcomm U (b j))
  refine Eq.trans (congrArg (fun w =>
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv (i ≫ π) z p
      (Stacks.Chow.stalkPushforwardComparison i
        (relativeDifferentialForms (i ≫ π) (p : ℤ)) z w)) hinner) ?_
  refine Eq.trans (congrArg
    (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv (i ≫ π) z p)
    (Stacks.Chow.stalkPushforwardComparison_germ i
      (relativeDifferentialForms (i ≫ π) (p : ℤ)) z U hxU _)) ?_
  refine Eq.trans
    (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv_germ
      (i ≫ π) z p (i ⁻¹ᵁ U) hxU (fun j => (i.app U).hom (b j))) ?_
  exact congrArg _ (funext fun j =>
    congrArg _ (Scheme.Hom.germ_stalkMap_apply i U z hxU (b j)).symm)

omit [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (i.base z)))]
  [DecidableEq (OrderDual (TopologicalSpace.OpenNhds z))] in
/-- The transport to the stalk at `z` kills zero. -/
theorem stalkPushforwardComparison_zero :
    Stacks.Chow.stalkPushforwardComparison i
      (relativeDifferentialForms (i ≫ π) (p : ℤ)) z 0 = 0 := by
  have h := Stacks.Chow.stalkPushforwardComparison_smul i
    (relativeDifferentialForms (i ≫ π) (p : ℤ)) z 0 0
  rw [zero_smul, map_zero, zero_smul] at h
  exact h

/-! #### The composite of the stalk square's upper and right edges -/

/-- The composite in the stalk square sends zero to zero. -/
theorem formsStalkRestriction_zero :
    letI := Stacks.GysinStalk.algebraAmbient i π z
    letI := Stacks.GysinStalk.algebraSub i π z
    letI := Stacks.GysinStalk.algebraRestriction i z
    letI := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
        (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm 0))) = 0 := by
  let := Stacks.GysinStalk.algebraAmbient i π z
  let := Stacks.GysinStalk.algebraSub i π z
  let := Stacks.GysinStalk.algebraRestriction i z
  let := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
      (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
  exact Eq.trans (congrArg (fun v =>
      Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z v))
      (Eq.trans (congrArg (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val)
        (formsStalkKaehlerEquivAt i π z p).symm.map_zero)
        (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val).map_zero))
    (Eq.trans (congrArg
      (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
        (i ≫ π) z p)
        (stalkPushforwardComparison_zero i π z p))
      (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p).map_zero)

/-- The composite in the stalk square is additive. -/
theorem formsStalkRestriction_add :
    letI := Stacks.GysinStalk.algebraAmbient i π z
    letI := Stacks.GysinStalk.algebraSub i π z
    letI := Stacks.GysinStalk.algebraRestriction i z
    letI := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
        (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
    ∀ w w' : ⋀[ToType (X.presheaf.stalk (i.base z))]^p
      (KaehlerDifferential (ToType (S.presheaf.stalk ((i ≫ π) z)))
        (ToType (X.presheaf.stalk (i.base z)))),
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm (w + w')))) =
      Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm w))) +
        Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm w'))) := by
  let := Stacks.GysinStalk.algebraAmbient i π z
  let := Stacks.GysinStalk.algebraSub i π z
  let := Stacks.GysinStalk.algebraRestriction i z
  let := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
      (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
  intro w w'
  exact Eq.trans (congrArg (fun v =>
      Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z v))
      (Eq.trans (congrArg (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val)
        ((formsStalkKaehlerEquivAt i π z p).symm.map_add w w'))
        ((PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val).map_add _ _)))
    (Eq.trans (congrArg
      (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
        (i ≫ π) z p)
        (Stacks.Chow.stalkPushforwardComparison_add i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z _ _))
      ((Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
        (i ≫ π) z p).map_add _ _))

/-- The composite in the stalk square is semilinear over the stalk map of `i`. -/
theorem formsStalkRestriction_smul :
    letI := Stacks.GysinStalk.algebraAmbient i π z
    letI := Stacks.GysinStalk.algebraSub i π z
    letI := Stacks.GysinStalk.algebraRestriction i z
    letI := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
        (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
    ∀ (r : ToType (X.presheaf.stalk (i.base z)))
      (w : ⋀[ToType (X.presheaf.stalk (i.base z))]^p
        (KaehlerDifferential (ToType (S.presheaf.stalk ((i ≫ π) z)))
          (ToType (X.presheaf.stalk (i.base z))))),
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm (r • w)))) =
      (i.stalkMap z).hom r •
        Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
          (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm w))) := by
  let := Stacks.GysinStalk.algebraAmbient i π z
  let := Stacks.GysinStalk.algebraSub i π z
  let := Stacks.GysinStalk.algebraRestriction i z
  let := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
      (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
  intro r w
  exact Eq.trans (congrArg (fun v =>
      Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z v))
      (Eq.trans (congrArg (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val)
        ((formsStalkKaehlerEquivAt i π z p).symm.map_smul r w))
        ((PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val).map_smul r _)))
    (Eq.trans (congrArg
      (Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
        (i ≫ π) z p)
        (Stacks.Chow.stalkPushforwardComparison_smul i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z r _))
      ((Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
        (i ≫ π) z p).map_smul _ _))

/-- The composite in the stalk square agrees with `KaehlerDifferential.mapExteriorPower`
on a wedge of universal differentials. -/
theorem formsStalkRestriction_wedge
    (c : Fin p → ToType (X.presheaf.stalk (i.base z))) :
    letI := Stacks.GysinStalk.algebraAmbient i π z
    letI := Stacks.GysinStalk.algebraSub i π z
    letI := Stacks.GysinStalk.algebraRestriction i z
    letI := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
        (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm
              (exteriorPower.ιMulti (ToType (X.presheaf.stalk (i.base z))) p
                fun j => KaehlerDifferential.D _ _ (c j))))) =
      KaehlerDifferential.mapExteriorPower (ToType (S.presheaf.stalk ((i ≫ π) z)))
        (ToType (X.presheaf.stalk (i.base z))) (ToType (Z.presheaf.stalk z)) p
        (exteriorPower.ιMulti (ToType (X.presheaf.stalk (i.base z))) p
          fun j => KaehlerDifferential.D _ _ (c j)) := by
  let := Stacks.GysinStalk.algebraAmbient i π z
  let := Stacks.GysinStalk.algebraSub i π z
  let := Stacks.GysinStalk.algebraRestriction i z
  let := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
      (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
  obtain ⟨U, hxU, b, hb⟩ :=
    Stacks.RelativeDifferentialStalkMap.exists_germ_eq_of_fin (i.base z) c
  have hsymm : (formsStalkKaehlerEquivAt i π z p).symm
        ((exteriorPower.ιMulti (ToType (X.presheaf.stalk (i.base z))) p)
          fun j => KaehlerDifferential.D _ _ (c j)) =
      TopCat.Presheaf.germ (relativeDifferentialForms π (p : ℤ)).val.presheaf U
        (i.base z) hxU
        ((relativeDifferentialFormsAlgebra π).toPresheafGradedAlgebra.homogeneousProd
          (op U) p fun j => (Scheme.Modules.exteriorGenerator
            (relativeDifferentials π)).val.app (op U)
            ((universalRelativeDerivation π).d (b j))) := by
    refine (formsStalkKaehlerEquivAt i π z p).symm_apply_eq.2 ?_
    refine Eq.trans ?_ (formsStalkKaehlerEquivAt_germ i π z p U hxU b).symm
    exact congrArg _ (funext fun j => congrArg _ (hb j).symm)
  rw [hsymm]
  refine Eq.trans (formsStalkMapEquation_germ i π z p U hxU b) ?_
  refine Eq.trans ?_ (KaehlerDifferential.mapExteriorPower_ιMulti _ _ _ p _).symm
  refine congrArg _ (funext fun j => ?_)
  refine Eq.trans ?_ (KaehlerDifferential.map_D _ _ _ _ _).symm
  exact congrArg _ (congrArg (CommRingCat.Hom.hom (i.stalkMap z)) (hb j))

/-- **The stalk of the restriction of relative differential forms to a subscheme is
`KaehlerDifferential.mapExteriorPower`.**

Let `i : Z ⟶ X` be a morphism of schemes, `π : X ⟶ S`, and `z` a point of `Z`. Write `A` for the
local ring of `S` at the image of `z`, `R` for the local ring of `X` at `i z` and `R'` for the
local ring of `Z` at `z`. Under the identification of the stalk at `i z` of `Ω^p_{X/S}` with
`⋀^p_R Ω[R⁄A]`, the transport of the stalk at `i z` of `i_*Ω^p_{Z/S}` to the stalk at `z` of
`Ω^p_{Z/S}`, and the identification of the latter with `⋀^p_{R'} Ω[R'⁄A]`, **the stalk of
`AlgebraicGeometry.Scheme.Hom.formRestriction` is
`KaehlerDifferential.mapExteriorPower A R R' p`.**

Both sides are additive and semilinear over `R → R'`, and the wedges of universal differentials
span the source, so the identity reduces to `Stacks.GysinStalk.formsStalkRestriction_wedge`. -/
theorem formsStalkMapEquation
    (m : ToType ((relativeDifferentialForms π (p : ℤ)).presheaf.stalk (i.base z))) :
    letI := Stacks.GysinStalk.algebraAmbient i π z
    letI := Stacks.GysinStalk.algebraSub i π z
    letI := Stacks.GysinStalk.algebraRestriction i z
    letI := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
        (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val m)) =
      KaehlerDifferential.mapExteriorPower (ToType (S.presheaf.stalk ((i ≫ π) z)))
        (ToType (X.presheaf.stalk (i.base z))) (ToType (Z.presheaf.stalk z)) p
        (formsStalkKaehlerEquivAt i π z p m) := by
  let := Stacks.GysinStalk.algebraAmbient i π z
  let := Stacks.GysinStalk.algebraSub i π z
  let := Stacks.GysinStalk.algebraRestriction i z
  let := Stacks.GysinStalk.isScalarTower_stalk_comp i π z
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) (relativeDifferentialForms π (p : ℤ)).val (i.base z)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.sheaf.presheaf) ((Scheme.Modules.pushforward i).obj
      (relativeDifferentialForms (i ≫ π) (p : ℤ))).val (i.base z)
  refine Eq.trans (congrArg (fun w =>
    Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p (Stacks.Chow.stalkPushforwardComparison i
        (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
        (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val w)))
    ((formsStalkKaehlerEquivAt i π z p).symm_apply_apply m).symm) ?_
  exact KaehlerDifferential.ext_of_wedge_gens
    (ToType (S.presheaf.stalk ((i ≫ π) z))) (ToType (X.presheaf.stalk (i.base z)))
    (ToType (Z.presheaf.stalk z)) p
    (fun ξ => Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv
      (i ≫ π) z p
        (Stacks.Chow.stalkPushforwardComparison i
          (relativeDifferentialForms (i ≫ π) (p : ℤ)) z
          (PresheafOfModules.stalkMapL (R := X.sheaf.presheaf) (i.base z)
          (formRestriction i π (p : ℤ)).val
            ((formsStalkKaehlerEquivAt i π z p).symm ξ))))
    (fun ξ => KaehlerDifferential.mapExteriorPower _ _ _ p ξ)
    (formsStalkRestriction_zero i π z p) (map_zero _)
    (formsStalkRestriction_add i π z p) (fun w w' => map_add _ _ _)
    (formsStalkRestriction_smul i π z p)
    (fun r w => by rw [map_smul, algebraMap_smul])
    (formsStalkRestriction_wedge i π z p)
    (formsStalkKaehlerEquivAt i π z p m)

end Stacks.GysinStalk

end
