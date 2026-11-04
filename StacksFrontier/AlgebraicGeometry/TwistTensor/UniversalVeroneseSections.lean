module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpenRepresents
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackSectionRing
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaSectionMul

/-!
# The graded map of the universal family on `U_d`, on the tensor powers

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, let `d ≥ 1` and let
`U_d = ⋃_{f ∈ 𝒜 d} D₊(f) ⊆ X` be the open of Equation 27.12.0.1. The universal family of
[Stacks, Tag 01N9] on `U_d` is the invertible module `𝒪_{U_d}(d)` together with the graded map
`ψ^d : A^{(d)} ⟶ Γ_*(U_d, 𝒪_{U_d}(d))`.

This file assembles that graded map as a
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`, indexed by the iterated tensor
powers `𝒪_{U_d}(d)^{⊗ n}`, through the comparison isomorphisms
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat : 𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(nd)`,
and shows that its degree-one values generate `𝒪_{U_d}(d)`.

## Main definitions

* `universalVeroneseSections`: the graded map `ψ^d` of the universal family of
  [Stacks, Tag 01N9], as a degreewise family `A_{nd} →+ Γ(𝒪_{U_d}(d)^{⊗ n}, ⊤)` multiplicative
  across degrees for `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`.

## Main results

* `iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top`: the nonvanishing opens of
  the degree-one values of `ψ^d` cover `U_d`, so `(d, 𝒪_{U_d}(d), ψ^d)` is a triple over `U_d`.
* `veroneseMulHom_eq`: the multiplication of the Veronese family of the twists pulled back along
  `U_d ⟶ X` is the canonical multiplication isomorphism of the twists of `U_d`.
* `thetaNat_inv_mul`: the inverses of the comparison isomorphisms carry the canonical
  multiplication of the twists to the multiplication of the tensor powers.
* `mulSections_thetaNat_inv`: the product under `mulSections` of two global sections of twists,
  carried to the tensor powers, is the image of their canonical product.
* `twistMulIsoVeronese_hom_tmul_restrictedDegreeSection`: the global sections of the twists of
  `U_d` attached to homogeneous elements multiply as those elements do.

## Implementation notes

Two monoidal structures on the modules of a scheme are in play and they do not unify at the
transparency the rewriting tactics use: `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`, whose
tensor product is the tensor product sheaf of [Stacks, Tag 01CA], and
`Stacks.SheafInternalHom.schemeMonoidalCategory`, the localized one. The multiplicativity squares
here live in the first, so their proofs are `Eq.trans`/`congrArg` composites rather than rewrites,
and the two transports they need, `mul_congr_degrees` and `conj_inv_mul`, are stated in a bare
monoidal category, where rewriting works.

`Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.universalTwist` and
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twist 𝒮 d d` are the same term, so no
transport between them is needed.

## References

* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AlgebraicGeometry.CommonDegreeTwist (restrictedTwist restrictedDegreeSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections VeroneseSections)
open Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents (universalTwist)
open Stacks.AlgebraicGeometry.ProjTwistSections (degreeSection_apply)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection degreeSectionHom)
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen (twist thetaNat)
open Stacks.AlgebraicGeometry.ThetaMul (thetaStepNat twistMulIsoVeronese thetaNat_mul
  mulSections_eq_tensorPowModuleAddIso)
open Stacks.AlgebraicGeometry.TwistTensor (degreeOpenHom pullbackTwist pullbackTwistMul
  twistMulHom twistMulHom_eq_pullbackTwistMul veroneseMulHom veroneseSectionMul
  veroneseSectionMul_pullbackUnit)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection nonvanishingOpen_psiSection)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (degreeOpen_le_whereInvertible)
open Stacks.NonvanishingOpen (nonvanishingOpen coe_nonvanishingOpen)
open Stacks.PullbackTensorCoherence (tmul tensorHom_tmul)
open Stacks.RingedSpace (pullbackUnit)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.PullbackGradedAlgebra.monoidalCategory

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-! ### Two transports, in a bare monoidal category -/

/-- For a family of objects indexed by the integers with a multiplication `F a ⊗ F b ⟶ F (a + b)`,
transporting the two factors along equalities of their indices and multiplying there is the same as
multiplying and transporting the product. -/
private theorem mul_congr_degrees {C : Type*} [Category C] [MonoidalCategory C] (F : ℤ → C)
    (μ : ∀ a b : ℤ, F a ⊗ F b ⟶ F (a + b))
    {a b a' b' c : ℤ} (h₁ : a = a') (h₂ : b = b') (hc : a + b = c) (hc' : a' + b' = c) :
    μ a b ≫ eqToHom (congrArg F hc) =
      (eqToHom (congrArg F h₁) ⊗ₘ eqToHom (congrArg F h₂)) ≫
        μ a' b' ≫ eqToHom (congrArg F hc') := by
  subst h₁ h₂
  simp

/-- If two isomorphisms carry a multiplication `st` to a
multiplication `μ` up to an isomorphism `ec` of the targets, then their inverses carry `μ` back to
`st`. -/
private theorem conj_inv_mul {C : Type*} [Category C] [MonoidalCategory C]
    {A A' B B' P Q : C} (ea : A ≅ A') (eb : B ≅ B') (st : A ⊗ B ⟶ P) (ec : P ≅ Q)
    (μ : A' ⊗ B' ⟶ Q) (h : st ≫ ec.hom = (ea.hom ⊗ₘ eb.hom) ≫ μ) :
    (ea.inv ⊗ₘ eb.inv) ≫ st = μ ≫ ec.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, h, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id]
  simp

/-! ### Cast identities for the degrees -/

/-- The integer cast of `n * d` is `d * n`. -/
private theorem cast_mul_comm_eq (n d : ℕ) : ((n * d : ℕ) : ℤ) = (d : ℤ) * (n : ℤ) := by
  push_cast; ring

/-- The degrees `n * d` and `m * d` add up to `(n + m) * d`, as integers. -/
private theorem cast_mul_add_cast_mul (n m d : ℕ) :
    ((n * d : ℕ) : ℤ) + ((m * d : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) := by
  push_cast; ring

/-- The degrees `d * n` and `d * m` add up to `(n + m) * d`, as integers. -/
private theorem mul_cast_add_mul_cast (n m d : ℕ) :
    (d : ℤ) * (n : ℤ) + (d : ℤ) * (m : ℤ) = (((n + m) * d : ℕ) : ℤ) := by
  push_cast; ring

/-! ### The Veronese multiplication of `U_d` is the canonical twist multiplication -/

/-- The canonical multiplication of the twists of `U_d` at the degrees `dn` and `dm`, with its
transport to the Veronese degree `(n + m)d` split off. -/
private theorem twistMulHom_eq_pullbackTwistMul_veronese (n m : ℕ) :
    pullbackTwistMul 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * (n : ℤ)) ((d : ℤ) * (m : ℤ)) ≫
        eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
          (mul_cast_add_mul_cast n m d)) =
      twistMulHom 𝒮 d (n : ℤ) (m : ℤ) ≫
        eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
          (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
            push_cast; ring)) := by
  rw [twistMulHom_eq_pullbackTwistMul, Category.assoc, eqToHom_trans]

/-- The multiplication of the Veronese family of the twists pulled back along `U_d ⟶ Proj(A)` is
the canonical multiplication isomorphism of the twists of `U_d`, in the Veronese degree spelling
`𝒪_{U_d}(nd) ⊗ 𝒪_{U_d}(md) ≅ 𝒪_{U_d}((n + m)d)`. -/
theorem veroneseMulHom_eq (n m : ℕ) :
    veroneseMulHom 𝒮 (degreeOpenHom 𝒮 d) d n m = (twistMulIsoVeronese 𝒮 d n m).hom :=
  Eq.trans
    (mul_congr_degrees (fun a => pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) a)
      (fun a b => pullbackTwistMul 𝒮 (degreeOpenHom 𝒮 d) a b)
      (cast_mul_comm_eq n d)
      (cast_mul_comm_eq m d)
      (cast_mul_add_cast_mul n m d)
      (mul_cast_add_mul_cast n m d))
    (congrArg
      (fun z => (eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
            (cast_mul_comm_eq n d)) ⊗ₘ
          eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
            (cast_mul_comm_eq m d))) ≫ z)
      (twistMulHom_eq_pullbackTwistMul_veronese 𝒮 d n m))

/-! ### The comparison family is multiplicative, read backwards -/

/-- The multiplicativity square of `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(nd)`, inverted: the inverses
in degrees `n` and `m` carry the canonical multiplication of the twists to the addition law of the
tensor powers, followed by the inverse in degree `n + m`. -/
theorem thetaNat_inv_mul (n m : ℕ) :
    ((thetaNat 𝒮 d n).inv ⊗ₘ (thetaNat 𝒮 d m).inv) ≫ (thetaStepNat 𝒮 d n m).hom =
      (twistMulIsoVeronese 𝒮 d n m).hom ≫ (thetaNat 𝒮 d (n + m)).inv :=
  conj_inv_mul (thetaNat 𝒮 d n) (thetaNat 𝒮 d m) (thetaStepNat 𝒮 d n m).hom
    (thetaNat 𝒮 d (n + m)) (twistMulIsoVeronese 𝒮 d n m).hom (thetaNat_mul 𝒮 d n m)

/-- The product `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of the images of two
global sections of `𝒪_{U_d}(nd)` and `𝒪_{U_d}(md)` under the inverted comparison family is the
image of their canonical product. -/
theorem mulSections_thetaNat_inv (n m : ℕ)
    (s : Γ(twist 𝒮 d ((n * d : ℕ) : ℤ), ⊤)) (t : Γ(twist 𝒮 d ((m * d : ℕ) : ℤ), ⊤)) :
    mulSections (twist 𝒮 d (d : ℤ))
        ((thetaNat 𝒮 d n).inv.val.app (op ⊤) s) ((thetaNat 𝒮 d m).inv.val.app (op ⊤) t) =
      (thetaNat 𝒮 d (n + m)).inv.val.app (op ⊤)
        ((twistMulIsoVeronese 𝒮 d n m).hom.val.app (op ⊤)
          (tmul (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.toRingedSpace
            (twist 𝒮 d ((n * d : ℕ) : ℤ)) (twist 𝒮 d ((m * d : ℕ) : ℤ)) (op ⊤) s t)) :=
  Eq.trans
    (mulSections_eq_tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) n m _ _)
    (Eq.trans
      (congrArg ((thetaStepNat 𝒮 d n m).hom.val.app (op ⊤))
        (tensorHom_tmul (thetaNat 𝒮 d n).inv (thetaNat 𝒮 d m).inv (op ⊤) s t).symm)
      (congrArg
        (fun φ => SheafOfModules.Hom.val φ |>.app (op ⊤)
          (tmul (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.toRingedSpace
            (twist 𝒮 d ((n * d : ℕ) : ℤ)) (twist 𝒮 d ((m * d : ℕ) : ℤ)) (op ⊤) s t))
        (thetaNat_inv_mul 𝒮 d n m)))

/-! ### The sections attached to homogeneous elements multiply -/

/-- The product of the global sections of `𝒪(nd)` and `𝒪(md)` attached to two homogeneous
elements is the one attached to their product, after the transport along `nd + md = (n + m)d`. -/
private theorem eqToHom_mulSection_degreeSection (n m : ℕ) (a : 𝒮 (n * d)) (b : 𝒮 (m * d))
    (ab : 𝒮 ((n + m) * d)) (hab : (ab : S) = (a : S) * (b : S)) :
    (eqToHom (congrArg (Stacks.AlgebraicGeometry.TwistTensor.twist 𝒮)
          (cast_mul_add_cast_mul n m d))).val.app (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
        (Stacks.AlgebraicGeometry.TwistTensor.mulSection 𝒮 ((n * d : ℕ) : ℤ) ((m * d : ℕ) : ℤ)
          (op ⊤) (degreeSection 𝒮 (n * d) a) (degreeSection 𝒮 (m * d) b)) =
      degreeSection 𝒮 ((n + m) * d) ab := by
  refine Stacks.AlgebraicGeometry.TwistTensor.twist_section_ext 𝒮 (op ⊤) _ _ fun z => ?_
  refine Eq.trans (Stacks.AlgebraicGeometry.TwistTensor.eqToHom_twist_val_app_apply 𝒮
    (cast_mul_add_cast_mul n m d) (op ⊤) _ z) ?_
  refine Eq.trans (Stacks.AlgebraicGeometry.TwistTensor.mulSection_apply 𝒮
    ((n * d : ℕ) : ℤ) ((m * d : ℕ) : ℤ) (op ⊤)
    (degreeSection 𝒮 (n * d) a) (degreeSection 𝒮 (m * d) b) z) ?_
  rw [degreeSection_apply, degreeSection_apply, degreeSection_apply, hab]
  exact Eq.trans LocalizedModule.mk_mul_mk
    (congrArg (LocalizedModule.mk ((a : S) * (b : S))) (mul_one 1))

/-- The global sections of the twists of `U_d` attached to homogeneous elements multiply, for the
multiplication of the Veronese family of the pulled-back twists. -/
theorem veroneseSectionMul_restrictedDegreeSection (n m : ℕ) (a : 𝒮 (n * d)) (b : 𝒮 (m * d))
    (ab : 𝒮 ((n + m) * d)) (hab : (ab : S) = (a : S) * (b : S)) :
    veroneseSectionMul 𝒮 (degreeOpenHom 𝒮 d) d (op ⊤) n m
        (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (n * d) a)
        (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (m * d) b) =
      restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) ((n + m) * d) ab :=
  Eq.trans
    (veroneseSectionMul_pullbackUnit 𝒮 (degreeOpenHom 𝒮 d) d n m (op ⊤)
      (degreeSection 𝒮 (n * d) a) (degreeSection 𝒮 (m * d) b))
    (congrArg
      (pullbackUnit (degreeOpenHom 𝒮 d)
        (Stacks.AlgebraicGeometry.TwistTensor.twist 𝒮 (((n + m) * d : ℕ) : ℤ)) (op ⊤))
      (eqToHom_mulSection_degreeSection 𝒮 d n m a b ab hab))

/-- The global sections of the twists of `U_d` attached to homogeneous elements multiply, for the
canonical multiplication isomorphism of the twists of `U_d`. -/
theorem twistMulIsoVeronese_hom_tmul_restrictedDegreeSection (n m : ℕ) (a : 𝒮 (n * d))
    (b : 𝒮 (m * d)) (ab : 𝒮 ((n + m) * d)) (hab : (ab : S) = (a : S) * (b : S)) :
    (twistMulIsoVeronese 𝒮 d n m).hom.val.app (op ⊤)
        (tmul (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.toRingedSpace
          (twist 𝒮 d ((n * d : ℕ) : ℤ)) (twist 𝒮 d ((m * d : ℕ) : ℤ)) (op ⊤)
          (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (n * d) a)
          (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (m * d) b)) =
      restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) ((n + m) * d) ab :=
  Eq.trans
    (congrArg
      (fun φ => SheafOfModules.Hom.val φ |>.app (op ⊤)
        (tmul (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.toRingedSpace
          (twist 𝒮 d ((n * d : ℕ) : ℤ)) (twist 𝒮 d ((m * d : ℕ) : ℤ)) (op ⊤)
          (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (n * d) a)
          (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (m * d) b)))
      (veroneseMulHom_eq 𝒮 d n m).symm)
    (veroneseSectionMul_restrictedDegreeSection 𝒮 d n m a b ab hab)

/-! ### The universal family's graded map, as the datum of a triple -/

/-- The global section of `𝒪_{U_d}(k)` attached to a homogeneous element of degree `k` is additive
in that element. -/
theorem restrictedDegreeSection_add (k : ℕ) (a b : 𝒮 k) :
    restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) k (a + b) =
      restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) k a +
        restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) k b := by
  show pullbackUnit (degreeOpenHom 𝒮 d)
      (Stacks.AlgebraicGeometry.TwistTensor.twist 𝒮 (k : ℤ)) (op ⊤)
      (degreeSection 𝒮 k (a + b)) = _
  rw [show degreeSection 𝒮 k (a + b) = degreeSection 𝒮 k a + degreeSection 𝒮 k b from
    map_add (degreeSectionHom 𝒮 k) a b]
  exact map_add _ _ _

/-- The graded map `ψ^d` of the universal family of [Stacks, Tag 01N9], as the datum `ψ` of a
triple of Section 27.12. In degree `n` it sends a homogeneous element `a` of `A` of degree `nd` to
the global section of `𝒪_{U_d}(nd)` it defines, read as a global section of the `n`-th iterated
tensor power `𝒪_{U_d}(d)^{⊗ n}` through the comparison family
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat`. No assumption `d > 0` is needed.
-/
def universalVeroneseSections : VeroneseSections 𝒮 d (universalTwist 𝒮 d) where
  toFun n := AddMonoidHom.mk'
    (fun a => (thetaNat 𝒮 d n).inv.val.app (op ⊤)
      (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (n * d) a))
    (fun a b =>
      (congrArg ((thetaNat 𝒮 d n).inv.val.app (op ⊤))
        (restrictedDegreeSection_add 𝒮 d (n * d) a b)).trans (map_add _ _ _))
  map_mul n m a b ab hab :=
    (congrArg ((thetaNat 𝒮 d (n + m)).inv.val.app (op ⊤))
        (twistMulIsoVeronese_hom_tmul_restrictedDegreeSection 𝒮 d n m a b ab hab).symm).trans
      (mulSections_thetaNat_inv 𝒮 d n m _ _).symm

/-- The degreewise value of the universal family's graded map: the restricted global section of
`𝒪_{U_d}(nd)` attached to a homogeneous element, read on the `n`-th tensor power. -/
theorem universalVeroneseSections_toFun (n : ℕ) (a : 𝒮 (n * d)) :
    (universalVeroneseSections 𝒮 d).toFun n a =
      (thetaNat 𝒮 d n).inv.val.app (op ⊤)
        (restrictedDegreeSection 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d) (n * d) a) :=
  rfl

/-! ### Generation in degree one: the universal family is a triple -/

/-- The nonvanishing locus on `U_d` of the restricted global section of `𝒪(nd)` attached to a
homogeneous element `f` of degree `nd` is `D₊(f) ∩ U_d`. -/
theorem nonvanishingLocus_restrictedDegreeSection (n : ℕ) (f : 𝒮 (n * d)) :
    Stacks.Ample.nonvanishingLocus (restrictedTwist 𝒮 (degreeOpen 𝒮 d) ((n * d : ℕ) : ℤ))
        (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) (n * d) f) =
      (((degreeOpen 𝒮 d).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) :
          (degreeOpen 𝒮 d).toScheme.Opens) : Set (degreeOpen 𝒮 d).toScheme) := by
  refine Eq.trans (Stacks.NonvanishingPullback.preimage_nonvanishingLocus
    (degreeOpen 𝒮 d).ι (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ))
    (degreeSection 𝒮 (n * d) f)).symm ?_
  exact Set.ext fun z =>
    Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
      𝒮 d n f (degreeOpen_le_whereInvertible 𝒮 d z.2)

/-- The nonvanishing open of the degree-one value `ψ^d(f)` of the universal family's graded map is
the preimage of `D₊(f)`. -/
theorem nonvanishingOpen_psiSection_universalVeroneseSections (f : 𝒮 d) :
    nonvanishingOpen (degreeOpen 𝒮 d).toScheme (universalTwist 𝒮 d)
        (psiSection 𝒮 (universalVeroneseSections 𝒮 d) f) =
      (degreeOpen 𝒮 d).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) := by
  have hf1 : ((f : S) ^ 1) ∈ 𝒮 (1 * d) :=
    Stacks.MorphismToProj.HomogeneousRatios.pow_mem f.2 1
  refine Opens.ext ?_
  rw [nonvanishingOpen_psiSection, coe_nonvanishingOpen]
  refine Eq.trans (Stacks.Ample.nonvanishingLocus_congr (thetaNat 𝒮 d 1).symm
    (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) (1 * d) ⟨(f : S) ^ 1, hf1⟩)) ?_
  refine Eq.trans (nonvanishingLocus_restrictedDegreeSection 𝒮 d 1 ⟨(f : S) ^ 1, hf1⟩) ?_
  exact congrArg
    (fun U : (AlgebraicGeometry.Proj 𝒮).Opens =>
      ((((degreeOpen 𝒮 d).ι ⁻¹ᵁ U : (degreeOpen 𝒮 d).toScheme.Opens)) :
        Set (degreeOpen 𝒮 d).toScheme))
    (congrArg (AlgebraicGeometry.Proj.basicOpen 𝒮) (pow_one (f : S)))

/-- The universal family's graded map generates `𝒪_{U_d}(d)` in degree one: the nonvanishing
opens of the global sections `ψ^d(f)`, `f ∈ A_d`, cover `U_d`. -/
theorem iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top :
    (⨆ f : 𝒮 d, nonvanishingOpen (degreeOpen 𝒮 d).toScheme (universalTwist 𝒮 d)
      (psiSection 𝒮 (universalVeroneseSections 𝒮 d) f)) = ⊤ := by
  calc (⨆ f : 𝒮 d, nonvanishingOpen (degreeOpen 𝒮 d).toScheme (universalTwist 𝒮 d)
          (psiSection 𝒮 (universalVeroneseSections 𝒮 d) f))
      = ⨆ f : 𝒮 d, (degreeOpen 𝒮 d).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) :=
        iSup_congr fun f => nonvanishingOpen_psiSection_universalVeroneseSections 𝒮 d f
    _ = (degreeOpen 𝒮 d).ι ⁻¹ᵁ degreeOpen 𝒮 d := by
        rw [← Scheme.Hom.preimage_iSup]
        rfl
    _ = ⊤ := Scheme.Opens.ι_preimage_self _

end Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple

end
