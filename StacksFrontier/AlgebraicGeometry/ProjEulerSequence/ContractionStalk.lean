module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwistStalk
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Contraction
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.TwistTrivialization
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The Euler contraction at a stalk is multiplication by a ratio of coordinates

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = Proj R[T]`
for projective `n`-space over `R`. Fix a point `x` of `X` and a coordinate `Tᵢ` not lying in
the homogeneous prime of `x`. Then `Tᵢ` trivializes `𝒪_X(-1)` at `x`: the stalk of `𝒪_X(-1)`
at `x` is the local ring `𝒪_{X,x}`, and the germ of the section `1 / Tᵢ` corresponds to `1`.

Read through that trivialization, the stalk at `x` of contraction with `Tⱼ` is multiplication
by the ratio `Tⱼ / Tᵢ` of the local ring, the stalk of `𝒪_X(0)` being identified with `𝒪_{X,x}`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.invCoordGerm`: the germ at `x` of the section
  `1 / Tᵢ` of `𝒪_X(-1)` over `D₊(Tᵢ)`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.coordRatio`: the ratio `Tⱼ / Tᵢ` in the local
  ring at `x`, obtained as the image of `1 / Tᵢ` under contraction with `Tⱼ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.tw_invCoordGerm` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.tw_symm_one`: the trivialization of `𝒪_X(-1)`
  by `Tᵢ` sends the germ of `1 / Tᵢ` to `1`, and back.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.val_coordRatio`: the ratio is the fraction
  `Tⱼ / Tᵢ` of the local ring at `x`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.coordRatio_self`: contracting with `Tᵢ` itself
  gives `1`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.tw0_stalkMap_contraction`: **the stalk at `x` of
  contraction with `Tⱼ`, read through the trivialization of `𝒪_X(-1)` by `Tᵢ`, is
  multiplication by `Tⱼ / Tᵢ`.**

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

local instance (x : ProjectiveSpectrum.top (polyGrading R n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

variable (x : ProjectiveSpectrum.top (polyGrading R n))

/-- The stalk at `x` of a morphism of twisting sheaves sends the germ of a section to the germ
of its image. -/
theorem stalkMap_associatedModuleSheafGerm {c d : ℤ}
    (φ : twistingSheaf (polyGrading R n) c ⟶ twistingSheaf (polyGrading R n) d)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n))) (hxU : x ∈ U)
    (a : (twistingSheaf (polyGrading R n) c).val.obj (op U)) :
    (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x φ).hom
        (associatedModuleSheafGerm (polyGrading R n)
          (twistGrading (polyGrading R n) c) x U hxU a) =
      associatedModuleSheafGerm (polyGrading R n) (twistGrading (polyGrading R n) d) x U hxU
        (φ.val.app (op U) a) :=
  _root_.AlgebraicGeometry.SheafOfModules.stalkMap_germ (projRingSheaf (polyGrading R n)) x φ
    U hxU a

variable (i : Fin (n + 1))

/-- A point whose homogeneous prime omits the coordinate `Tᵢ` lies on the standard chart
`D₊(Tᵢ)`. -/
theorem mem_basicOpen_X_of_notMem
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal) :
    x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i) :=
  (ProjectiveSpectrum.mem_basicOpen (polyGrading R n) (MvPolynomial.X i) x).2 hx

/-- The germ at `x` of the section `1 / Tᵢ` of `𝒪_X(-1)` over the standard chart `D₊(Tᵢ)`. -/
def invCoordGerm (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal) :
    associatedModuleSheafStalk (polyGrading R n)
      (twistGrading (polyGrading R n) (-1)) x :=
  associatedModuleSheafGerm (polyGrading R n) (twistGrading (polyGrading R n) (-1)) x
    (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (mem_basicOpen_X_of_notMem R n x i hx) (invCoordSection R n i le_rfl)

/-- An element of the stalk at `x` whose fraction is `Tᵢ / Tᵢ` is `1`. -/
private theorem eq_one_of_val_stalkIso'_eq_mk_X
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal)
    {z : ToType ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).presheaf.stalk x)}
    (h : HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x z) =
      Localization.mk (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ⟨MvPolynomial.X i, hx⟩) :
    z = 1 := by
  refine (Proj.stalkIso' (polyGrading R n) x).injective
    (HomogeneousLocalization.val_injective _ ?_)
  rw [h, map_one, HomogeneousLocalization.val_one]
  exact Localization.mk_self (⟨MvPolynomial.X i, hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

/-- The trivialization of `𝒪_X(-1)` at `x` by `Tᵢ` sends the germ of `1 / Tᵢ` to `1`. -/
theorem tw_invCoordGerm
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal) :
    twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx
        (invCoordGerm R n x i hx) = 1 := by
  refine eq_one_of_val_stalkIso'_eq_mk_X R n x i hx ?_
  have key : HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x
      (twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx
        (invCoordGerm R n x i hx))) =
      Localization.mk ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * 1)
        (⟨MvPolynomial.X i, hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl) :=
    val_twistingSheafMinusOneStalkEquiv_germ (polyGrading R n) (X_mem_one R n i) hx
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
      (mem_basicOpen_X_of_notMem R n x i hx) (invCoordSection R n i le_rfl) rfl
  rw [key, mul_one]

/-- The germ of `1 / Tᵢ` is what `1` corresponds to under the trivialization of `𝒪_X(-1)` by
`Tᵢ`. -/
theorem tw_symm_one
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal) :
    (twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx).symm 1 =
      invCoordGerm R n x i hx := by
  rw [← tw_invCoordGerm R n x i hx, LinearEquiv.symm_apply_apply]

/-- **The ratio `Tⱼ / Tᵢ` in the local ring at `x`**: the image of the germ of `1 / Tᵢ` under
contraction with `Tⱼ`, read in the stalk of `𝒪_X` through the identification of that stalk
with the stalk of `𝒪_X(0)`. -/
def coordRatio (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal)
    (j : Fin (n + 1)) :
    ToType ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).presheaf.stalk x) :=
  twistingSheafZeroStalkEquiv (polyGrading R n) x
    ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
      (contraction R n j)).hom
      ((twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx).symm 1))

/-- The ratio `Tⱼ / Tᵢ` is the germ of the image of the section `1 / Tᵢ` under contraction
with `Tⱼ`. -/
theorem coordRatio_eq_germ
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal)
    (j : Fin (n + 1)) :
    coordRatio R n x i hx j =
      twistingSheafZeroStalkEquiv (polyGrading R n) x
        (associatedModuleSheafGerm (polyGrading R n) (twistGrading (polyGrading R n) 0) x
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
          (mem_basicOpen_X_of_notMem R n x i hx)
          ((contraction R n j).val.app
            (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)))
            (invCoordSection R n i le_rfl))) :=
  (congrArg (fun z => twistingSheafZeroStalkEquiv (polyGrading R n) x
      ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
        (contraction R n j)).hom z)) (tw_symm_one R n x i hx)).trans
    (congrArg (twistingSheafZeroStalkEquiv (polyGrading R n) x)
      (stalkMap_associatedModuleSheafGerm R n x (contraction R n j)
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
        (mem_basicOpen_X_of_notMem R n x i hx) (invCoordSection R n i le_rfl)))

/-- The ratio `Tⱼ / Tᵢ` is the fraction `Tⱼ / Tᵢ` of the local ring at `x`. -/
theorem val_coordRatio
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal)
    (j : Fin (n + 1)) :
    HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x
        (coordRatio R n x i hx j)) =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)
        ⟨MvPolynomial.X i, hx⟩ := by
  have hval : ((contraction R n j).val.app
        (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)))
        (invCoordSection R n i le_rfl)).1 ⟨x, mem_basicOpen_X_of_notMem R n x i hx⟩ =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)
        ⟨MvPolynomial.X i, hx⟩ := by
    rw [contraction_apply]
    show Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) 1 *
      Localization.mk (1 : MvPolynomial (Fin (n + 1)) R)
        (⟨MvPolynomial.X i, hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl) = _
    rw [Localization.mk_mul]
    exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))
  rw [coordRatio_eq_germ]
  exact val_twistingSheafZeroStalkEquiv_germ (polyGrading R n) x _ _ _ hval

/-- The ratio `Tᵢ / Tᵢ` is `1`. -/
theorem coordRatio_self
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal) :
    coordRatio R n x i hx i = 1 := by
  exact eq_one_of_val_stalkIso'_eq_mk_X R n x i hx (val_coordRatio R n x i hx i)

/-- **The stalk at `x` of contraction with `Tⱼ` is multiplication by `Tⱼ / Tᵢ`**, once the
stalk of `𝒪_X(-1)` is identified with the local ring at `x` by the trivializing coordinate
`Tᵢ` and the stalk of `𝒪_X(0)` with it tautologically. -/
theorem tw0_stalkMap_contraction
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal)
    (j : Fin (n + 1))
    (d : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading R n)) x (twistingSheaf (polyGrading R n) (-1)))) :
    twistingSheafZeroStalkEquiv (polyGrading R n) x
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading R n)) x (contraction R n j)).hom d) =
      coordRatio R n x i hx j *
        twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx d := by
  obtain ⟨U, hxU, a, ha⟩ := associatedModuleSheafStalk_exists_germ (polyGrading R n)
    (twistGrading (polyGrading R n) (-1)) x d
  subst ha
  obtain ⟨V, hxV, iV, k, m, s, hm, hs, hn, hfrac⟩ := a.2 ⟨x, hxU⟩
  have hsx : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hn ⟨x, hxV⟩
  have hax : a.1 ⟨x, hxU⟩ = LocalizedModule.mk m ⟨s, hsx⟩ := by
    simpa using hfrac ⟨x, hxV⟩
  have hax' : a.1 ⟨x, hxU⟩ = Localization.mk m ⟨s, hsx⟩ := hax
  have hvalL : ((contraction R n j).val.app (op U) a).1 ⟨x, hxU⟩ =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) 1 *
        Localization.mk m ⟨s, hsx⟩ :=
    (contraction_apply R n j U a ⟨x, hxU⟩).trans
      (congrArg
        (fun z => Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) 1 * z) hax')
  have hleft : HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x
      (twistingSheafZeroStalkEquiv (polyGrading R n) x
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading R n)) x (contraction R n j)).hom
          (associatedModuleSheafGerm (polyGrading R n)
            (twistGrading (polyGrading R n) (-1)) x U hxU a)))) =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) 1 *
        Localization.mk m ⟨s, hsx⟩ :=
    (congrArg (fun z => HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x z))
      (congrArg (twistingSheafZeroStalkEquiv (polyGrading R n) x)
        (stalkMap_associatedModuleSheafGerm R n x (contraction R n j) U hxU a))).trans
      (val_twistingSheafZeroStalkEquiv_germ (polyGrading R n) x U hxU
        ((contraction R n j).val.app (op U) a) hvalL)
  have hright : HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x
      (coordRatio R n x i hx j *
        twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx
          (associatedModuleSheafGerm (polyGrading R n)
            (twistGrading (polyGrading R n) (-1)) x U hxU a))) =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)
          ⟨MvPolynomial.X i, hx⟩ *
        Localization.mk ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * m) ⟨s, hsx⟩ := by
    rw [map_mul, HomogeneousLocalization.val_mul, val_coordRatio,
      val_twistingSheafMinusOneStalkEquiv_germ (polyGrading R n) (X_mem_one R n i) hx U hxU a
        hax]
  refine (Proj.stalkIso' (polyGrading R n) x).injective
    (HomogeneousLocalization.val_injective _ ?_)
  rw [hleft, hright, Localization.mk_mul, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [Submonoid.coe_mul, one_mul]
  ring

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
