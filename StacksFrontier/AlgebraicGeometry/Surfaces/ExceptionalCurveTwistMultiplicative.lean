module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RestrictedIdealTensor
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionDegreeOneLine
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistInjectivity
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twists an exceptional curve cuts out on itself multiply

Let `E ⊆ X` be an exceptional curve of the first kind, cut out by an ideal sheaf `D` and
presented as the projective line by an isomorphism `e : 𝐏¹_k ≅ E`, and write
`L_m = 𝒪_X(-D ^ m)|_E` for the restriction to `E` of the `m`-th negative twist. This file proves
that **every global section of `L_{1 + (p+1)}` is a finite sum of products**

`Stacks.Divisors.restrictedIdealMulSections a b`,  `a ∈ Γ(E, L_1)`, `b ∈ Γ(E, L_{p+1})`,

the degree-one generation of the graded ring of twisted sections that the Stacks proof of
[Stacks, Tag 0C2K] uses when it says that `x^d, x^{d-1}y, …, y^d` map to a basis of
`H⁰(𝐏¹_k, 𝒪(d))`.

## Why this needed no multiplicative family of comparisons

The identifications `e^*L_m ≅ 𝒪_{𝐏¹_k}(m)` of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` are a *choice in each degree*: they
come from an equality of Picard classes and relate no two degrees. The obstruction that
`StacksFrontier/AlgebraicGeometry/Surfaces/ThickeningKernelFiltration.lean` records is that nothing
makes that family compatible with the two multiplications.

It does not have to be made compatible. Only one identification in the degree of the *product*
is needed, and it may be *built* from the two chosen ones in the degrees of the factors:

`e^*L_{1+n} ≅ e^*(L_1 ⊗ L_n) ≅ e^*L_1 ⊗ e^*L_n ≅ 𝒪(1) ⊗ 𝒪(n) ≅ 𝒪(1 + n)`,

whose four steps are `Stacks.Divisors.restrictedIdealTensorMulIso` (the multiplication of the
ideal sheaves, Tag 01CD on the nose), `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso`
(the pullback–tensor comparison of Tag 01CD), the chosen identifications in degrees `1` and `n`,
and `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso` (Equation 01MO,
invertible because `k[T₀, T₁]` is generated in degree one). Multiplicativity then holds *by
construction*: the first two steps are exactly the morphisms whose action on a pure tensor of
sections is computed by `Stacks.Tag01VSPullbackTensor`, and the last is the one
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` is defined by.

The comparison in the degree of the product is then a *different* identification from the chosen
one in that degree, which is why no compatibility of the chosen family is needed and none is
proved: both are isomorphisms, and degree-one generation is a statement about the whole space of
sections, invariant under replacing one identification by another.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.twistSection_restrictedIdealMulSections` — **the comparison of the graded pieces with the
  twists of `𝐏¹_k` is multiplicative**: the section of `𝒪(1 + n)` attached to a restricted
  product is the product of the sections of `𝒪(1)` and `𝒪(n)` attached to the factors.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.mem_closure_restrictedIdealMulSections` — **degree-one generation of the twisted sections on
  an exceptional curve of the first kind.**

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Divisors
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open Stacks.Tag01VSPullbackTensor
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover twistMultiplicationIso)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistSectionRing (mul mul_apply)
open Stacks.AlgebraicGeometry.RelativeProjTwists (absoluteTwistProduct)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistSectionRing

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Equation [Stacks, Tag 01MO] on global sections is the pointwise product.** The canonical
product `Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` of two global sections
of the twists, which is the multiplication map `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` applied to their pure
tensor, is `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul`: both have the product of the two
local values at every point, and a section of a twist is its family of values. -/
theorem absoluteTwistProduct_eq_mul (n m : ℕ) (s : twistGlobalSections 𝒮 n)
    (t : twistGlobalSections 𝒮 m) :
    absoluteTwistProduct 𝒮 (n : ℤ) (m : ℤ) ⊤ s t = mul 𝒮 n m s t :=
  Subtype.ext (funext fun x =>
    (Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply 𝒮 (n : ℤ) (m : ℤ)
      ⊤ s t x).trans (mul_apply 𝒮 n m s t x).symm)

end Stacks.AlgebraicGeometry.ProjTwistSectionRing

namespace Stacks.Tag01VSPullbackTensor

variable {X Y : _root_.AlgebraicGeometry.Scheme.{u}}

/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. -/
private theorem homApp_inv_homApp_aux {M N : X.Modules} (ε : M ≅ N) (U : X.Opens)
    (x : Γ(M, U)) :
    Scheme.Modules.Hom.app ε.inv U (Scheme.Modules.Hom.app ε.hom U x) = x := by
  have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ U x) ε.hom_inv_id
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using h

/-- **An isomorphism of sheaves of modules is bijective on sections over any open.** The inverse
is the action of the inverse isomorphism. -/
theorem bijective_homApp {M N : X.Modules} (ε : M ≅ N) (U : X.Opens) :
    Function.Bijective fun x : Γ(M, U) => Scheme.Modules.Hom.app ε.hom U x :=
  Function.bijective_iff_has_inverse.2
    ⟨fun y => Scheme.Modules.Hom.app ε.inv U y, homApp_inv_homApp_aux ε U,
      homApp_inv_homApp_aux ε.symm U⟩

/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. -/
theorem homApp_inv_homApp {M N : X.Modules} (ε : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    Scheme.Modules.Hom.app ε.inv U (Scheme.Modules.Hom.app ε.hom U x) = x :=
  homApp_inv_homApp_aux ε U x

/-- **The unit of the module pullback is natural in the sheaf**: the unit image of the image of a
section under a morphism is the image of its unit image under the pullback of the morphism. -/
theorem modulesPullbackUnit_homApp (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens)
    (s : Γ(M, U)) :
    modulesPullbackUnit f N U (Scheme.Modules.Hom.app φ U s) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map φ) (f ⁻¹ᵁ U)
        (modulesPullbackUnit f M U s) := by
  have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ U s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.id_map,
    Functor.comp_map, Scheme.Modules.pushforward_map_app] at h
  exact h

/-- **The unit of the module pullback along an isomorphism of schemes is an isomorphism**: the
direct image along an isomorphism is fully faithful, and every sheaf is in its essential
image. -/
theorem isIso_modulesPullbackUnit_app (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) :=
  Adjunction.isIso_unit_app_of_iso _
    (((Scheme.Modules.pushforwardComp (inv f) f ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id f) ≪≫
      Scheme.Modules.pushforwardId Y).app M).symm)

/-- **The unit of the module pullback along an isomorphism of schemes is bijective on
sections.** -/
theorem bijective_modulesPullbackUnit (f : X ⟶ Y) [IsIso f] (M : Y.Modules) (U : Y.Opens) :
    Function.Bijective fun s : Γ(M, U) => modulesPullbackUnit f M U s :=
  have := isIso_modulesPullbackUnit_app f M
  bijective_homApp (asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) U

/-- Reading the unit of the module pullback along an isomorphism of schemes through an
isomorphism is bijective on sections. -/
private theorem bijective_homApp_modulesPullbackUnit (f : X ⟶ Y) [IsIso f] {M : Y.Modules}
    {N : X.Modules} (ε : (Scheme.Modules.pullback f).obj M ≅ N) :
    Function.Bijective fun s : Γ(M, (⊤ : Y.Opens)) =>
      Scheme.Modules.Hom.app ε.hom ⊤ (modulesPullbackUnit f M ⊤ s) :=
  (bijective_homApp ε ⊤).comp (bijective_modulesPullbackUnit f M ⊤)

end Stacks.Tag01VSPullbackTensor

namespace AlgebraicGeometry.Scheme.IdealSheafData

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

namespace IsExceptionalCurveOfFirstKind

/-! ### The chosen identification of one graded piece with a twist -/

/-- The chosen identification `e^*(𝒪_X(-D ^ m)|_E) ≅ 𝒪_{𝐏¹_k}(m)` of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf`, named so that it may be used twice in
one statement. It carries no information relating two degrees, and none is asked of it. -/
def twistIso (hE : IsExceptionalCurveOfFirstKind D k e) (m : ℕ) :
    (Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m : ℤ) :=
  (nonempty_pullback_negativeTwist_pow_iso_twistingSheaf hE m).some

/-- The global section of `𝒪_{𝐏¹_k}(m)` attached to a global section of `𝒪_X(-D ^ m)|_E`: pull
back along `e` and read through the chosen identification. -/
def twistSection (hE : IsExceptionalCurveOfFirstKind D k e) (m : ℕ)
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)),
      (⊤ : D.subscheme.Opens))) :
    twistGlobalSections (MvPolynomial.homogeneousSubmodule (Fin 2) k) m :=
  Scheme.Modules.Hom.app (hE.twistIso m).hom ⊤
    (modulesPullbackUnit e.hom
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))) ⊤ a)

/-- **The comparison of one graded piece with the sections of a twist is bijective.** -/
theorem bijective_twistSection (hE : IsExceptionalCurveOfFirstKind D k e) (m : ℕ) :
    Function.Bijective (twistSection hE m) :=
  bijective_homApp_modulesPullbackUnit e.hom (hE.twistIso m)

/-! ### The identification in the degree of a product, built from the two factors -/

/-- **The identification of the graded piece in the degree of a product with the twist of that
degree, built from the chosen identifications in the degrees of the two factors.**

The four steps are the multiplication of the ideal sheaves restricted to `E`, the
pullback–tensor comparison of [Stacks, Tag 01CD] along `e`, the chosen identifications of the
two factors, and Equation [Stacks, Tag 01MO]. -/
@[sga "7 X 2.14" "more general"]
def prodTwistIso [IsEffectiveCartierDivisor D] (hE : IsExceptionalCurveOfFirstKind D k e)
    (m n : ℕ) :
    (Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m * D ^ n))) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) ((m : ℤ) + (n : ℤ)) :=
  ((Scheme.Modules.pullback e.hom).mapIso
      (restrictedIdealTensorMulIso D (D ^ m) (D ^ n) inferInstance)).symm ≪≫
    schemePullbackTensorIso e.hom ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ m)))
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))) ≪≫
    tensorSheafMapIso (hE.twistIso m) (hE.twistIso n) ≪≫
    twistMultiplicationIso (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (Stacks.Surfaces.degreeOneCover_homogeneousSubmodule k 1) (m : ℤ) (n : ℤ)

/-- The global section of `𝒪_{𝐏¹_k}(m + n)` attached to a global section of
`𝒪_X(-(D ^ m · D ^ n))|_E`, read through
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.prodTwistIso`. -/
def prodTwistSection [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (m n : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m * D ^ n)),
      (⊤ : D.subscheme.Opens))) :
    twistGlobalSections (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m + n) :=
  Scheme.Modules.Hom.app (hE.prodTwistIso m n).hom ⊤
    (modulesPullbackUnit e.hom
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m * D ^ n))) ⊤ x)

/-- **The comparison in the degree of a product is bijective.** -/
theorem bijective_prodTwistSection [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (m n : ℕ) :
    Function.Bijective (hE.prodTwistSection m n) :=
  bijective_homApp_modulesPullbackUnit e.hom (hE.prodTwistIso m n)

/-! ### Multiplicativity -/

/-- **The comparison of the graded pieces with the twists of `𝐏¹_k` is multiplicative.** The
section of `𝒪(m + n)` attached to the restricted product of a section of `𝒪_X(-D ^ m)|_E` with a
section of `𝒪_X(-D ^ n)|_E` is the pointwise product of the sections of `𝒪(m)` and `𝒪(n)`
attached to the two factors.

This is the compatibility that [Stacks, Tag 0C2K] needs and that the per-degree choices of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` do not have: it holds here because the
identification in the degree of the product is not a further choice but is assembled out of the
two factors' choices, through exactly the three morphisms whose action on a pure tensor of
sections is known —
`Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit`,
`Stacks.Tag01VSPullbackTensor.tensorSheafMapIso_hom_toTensorSheafSection`, and the definition of
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct`. -/
theorem prodTwistSection_restrictedIdealMulSections [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (m n : ℕ)
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)),
      (⊤ : D.subscheme.Opens)))
    (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n)),
      (⊤ : D.subscheme.Opens))) :
    hE.prodTwistSection m n
        (restrictedIdealMulSections D (D ^ m) (D ^ n) inferInstance a b) =
      mul (MvPolynomial.homogeneousSubmodule (Fin 2) k) m n
        (hE.twistSection m a) (hE.twistSection n b) := by
  have hmul : restrictedIdealMulSections D (D ^ m) (D ^ n) inferInstance a b =
      Scheme.Modules.Hom.app (restrictedIdealTensorMulIso D (D ^ m) (D ^ n) inferInstance).hom ⊤
        (toTensorSheafSection D.subscheme.toRingedSpace
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n)))
          (op (⊤ : D.subscheme.Opens)) (a ⊗ₜ b)) := rfl
  have key : hE.prodTwistSection m n
        (restrictedIdealMulSections D (D ^ m) (D ^ n) inferInstance a b) =
      Scheme.Modules.Hom.app (twistMultiplicationIso
            (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (Stacks.Surfaces.degreeOneCover_homogeneousSubmodule k 1) (m : ℤ) (n : ℤ)).hom ⊤
        (Scheme.Modules.Hom.app
          (tensorSheafMapIso (hE.twistIso m) (hE.twistIso n)).hom ⊤
          (Scheme.Modules.Hom.app (schemePullbackTensorIso e.hom
              ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))
              ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n)))).hom ⊤
            (Scheme.Modules.Hom.app ((Scheme.Modules.pullback e.hom).mapIso
                (restrictedIdealTensorMulIso D (D ^ m) (D ^ n) inferInstance)).inv ⊤
              (modulesPullbackUnit e.hom
                ((Scheme.Modules.pullback D.subschemeι).obj
                  (negativeTwist (D ^ m * D ^ n))) ⊤
                (restrictedIdealMulSections D (D ^ m) (D ^ n) inferInstance a b))))) := rfl
  have h1 : modulesPullbackUnit e.hom
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m * D ^ n))) ⊤
        (restrictedIdealMulSections D (D ^ m) (D ^ n) inferInstance a b) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback e.hom).mapIso
          (restrictedIdealTensorMulIso D (D ^ m) (D ^ n) inferInstance)).hom ⊤
        (modulesPullbackUnit e.hom
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨D.subscheme.toRingedSpace.presheaf, D.subscheme.toRingedSpace.IsSheaf⟩).obj
              ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))).obj
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))))) ⊤
          (toTensorSheafSection D.subscheme.toRingedSpace
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n)))
            (op (⊤ : D.subscheme.Opens)) (a ⊗ₜ b))) := by
    rw [hmul]
    exact modulesPullbackUnit_homApp e.hom
      (restrictedIdealTensorMulIso D (D ^ m) (D ^ n) inferInstance).hom ⊤ _
  have h12 : Scheme.Modules.Hom.app ((Scheme.Modules.pullback e.hom).mapIso
          (restrictedIdealTensorMulIso D (D ^ m) (D ^ n) inferInstance)).inv ⊤
        (modulesPullbackUnit e.hom
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m * D ^ n))) ⊤
          (restrictedIdealMulSections D (D ^ m) (D ^ n) inferInstance a b)) =
      modulesPullbackUnit e.hom
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨D.subscheme.toRingedSpace.presheaf, D.subscheme.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))))) ⊤
        (toTensorSheafSection D.subscheme.toRingedSpace
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n)))
          (op (⊤ : D.subscheme.Opens)) (a ⊗ₜ b)) := by
    rw [h1]
    exact homApp_inv_homApp ((Scheme.Modules.pullback e.hom).mapIso
      (restrictedIdealTensorMulIso D (D ^ m) (D ^ n) inferInstance)) ⊤ _
  have h2 : Scheme.Modules.Hom.app (schemePullbackTensorIso e.hom
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n)))).hom ⊤
        (modulesPullbackUnit e.hom
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨D.subscheme.toRingedSpace.presheaf, D.subscheme.toRingedSpace.IsSheaf⟩).obj
              ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))).obj
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))))) ⊤
          (toTensorSheafSection D.subscheme.toRingedSpace
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m)))
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n)))
            (op (⊤ : D.subscheme.Opens)) (a ⊗ₜ b))) =
      toTensorSheafSection (projectiveLineProj k).toRingedSpace
        ((Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))))
        ((Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))))
        (op (⊤ : (projectiveLineProj k).Opens))
        (modulesPullbackUnit e.hom
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))) ⊤ a ⊗ₜ
          modulesPullbackUnit e.hom
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))) ⊤ b) :=
    schemePullbackTensorIso_hom_modulesPullbackUnit e.hom _ _ ⊤ a b
  have h3 : Scheme.Modules.Hom.app (tensorSheafMapIso (hE.twistIso m) (hE.twistIso n)).hom ⊤
        (toTensorSheafSection (projectiveLineProj k).toRingedSpace
          ((Scheme.Modules.pullback e.hom).obj
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))))
          ((Scheme.Modules.pullback e.hom).obj
            ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))))
          (op (⊤ : (projectiveLineProj k).Opens))
          (modulesPullbackUnit e.hom
              ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m))) ⊤ a ⊗ₜ
            modulesPullbackUnit e.hom
              ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ n))) ⊤ b)) =
      toTensorSheafSection (projectiveLineProj k).toRingedSpace
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m : ℤ))
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n : ℤ))
        (op (⊤ : (projectiveLineProj k).Opens))
        (hE.twistSection m a ⊗ₜ hE.twistSection n b) :=
    tensorSheafMapIso_hom_toTensorSheafSection (hE.twistIso m) (hE.twistIso n) ⊤ _ _
  rw [key, h12, h2]
  exact (congrArg (Scheme.Modules.Hom.app (twistMultiplicationIso
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (Stacks.Surfaces.degreeOneCover_homogeneousSubmodule k 1) (m : ℤ) (n : ℤ)).hom ⊤) h3).trans
    (Stacks.AlgebraicGeometry.ProjTwistSectionRing.absoluteTwistProduct_eq_mul
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) m n (hE.twistSection m a)
      (hE.twistSection n b))

/-! ### Degree-one generation -/

/-- `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.prodTwistSection` as an
additive map: both the pullback unit and the action of an isomorphism on sections are additive. -/
def prodTwistSectionHom [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (m n : ℕ) :
    Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m * D ^ n)),
        (⊤ : D.subscheme.Opens)) →+
      twistGlobalSections (MvPolynomial.homogeneousSubmodule (Fin 2) k) (m + n) :=
  AddMonoidHom.mk' (hE.prodTwistSection m n) fun x y => by
    have hx : ∀ z, hE.prodTwistSection m n z =
        Scheme.Modules.Hom.app (hE.prodTwistIso m n).hom ⊤
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app
              ((Scheme.Modules.pullback D.subschemeι).obj
                (negativeTwist (D ^ m * D ^ n)))) ⊤ z) := fun _ => rfl
    simp only [hx, map_add]
    exact map_add _ _ _

/-- The additive map `prodTwistSectionHom` agrees pointwise with `prodTwistSection`. -/
@[simp]
theorem prodTwistSectionHom_apply [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (m n : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ m * D ^ n)),
      (⊤ : D.subscheme.Opens))) :
    hE.prodTwistSectionHom m n x = hE.prodTwistSection m n x := rfl

/-- **Degree-one generation of the twisted sections on an exceptional curve of the first kind.**

Every global section of `𝒪_X(-(D · D ^ n))|_E` is a finite sum of restricted products
`Stacks.Divisors.restrictedIdealMulSections a b` of a global section `a` of `𝒪_X(-D)|_E` with a
global section `b` of `𝒪_X(-D ^ n)|_E`.

This is the geometric half of the step the Stacks proof of [Stacks, Tag 0C2K] takes when it says
that the degree-`d` monomials in two lifts of a basis of `H⁰(𝐏¹_k, 𝒪(1))` map to a basis of
`H⁰(𝐏¹_k, 𝒪(d))`. The `k`-side is
`Stacks.ProjectiveSpace.Cohomology.mem_closure_degreeOneProducts`, and the two are joined by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.prodTwistSection_restrictedIdealMulSections`: the comparison in the degree of the product
carries a restricted product to a pointwise product, and it is bijective, so it carries the
products onto the products and the sums of products onto the sums of products. -/
theorem mem_closure_restrictedIdealMulSections [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ 1 * D ^ n)),
      (⊤ : D.subscheme.Opens))) :
    x ∈ AddSubgroup.closure
      ({y : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ 1 * D ^ n)),
          (⊤ : D.subscheme.Opens)) |
        ∃ a b, restrictedIdealMulSections D (D ^ 1) (D ^ n) inferInstance a b = y}) := by
  have hsub : Stacks.ProjectiveSpace.Cohomology.degreeOneProducts k n ⊆
      ((AddSubgroup.closure
        ({y : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ 1 * D ^ n)),
            (⊤ : D.subscheme.Opens)) |
          ∃ a b, restrictedIdealMulSections D (D ^ 1) (D ^ n) inferInstance a b = y})).map
          (hE.prodTwistSectionHom 1 n) : Set _) := by
    rintro t ⟨a', b', rfl⟩
    obtain ⟨a, ha⟩ := (hE.bijective_twistSection 1).surjective a'
    obtain ⟨b, hb⟩ := (hE.bijective_twistSection n).surjective b'
    refine AddSubgroup.mem_map.2
      ⟨restrictedIdealMulSections D (D ^ 1) (D ^ n) inferInstance a b,
        AddSubgroup.subset_closure ⟨a, b, rfl⟩, ?_⟩
    exact (hE.prodTwistSection_restrictedIdealMulSections 1 n a b).trans (by rw [ha, hb])
  have hmem := (AddSubgroup.closure_le _).2 hsub
    (Stacks.ProjectiveSpace.Cohomology.mem_closure_degreeOneProducts k n
      (hE.prodTwistSectionHom 1 n x))
  obtain ⟨y, hy, hyx⟩ := AddSubgroup.mem_map.1 hmem
  exact (hE.bijective_prodTwistSection 1 n).injective hyx ▸ hy

end IsExceptionalCurveOfFirstKind

end AlgebraicGeometry.Scheme.IdealSheafData

end
