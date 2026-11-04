module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ExteriorPowerMono
public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul

/-!
# The exterior-power filtration of the Euler sequence, on stalks

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = ℙⁿ_R`. The
Euler sequence

`0 ⟶ Ω_{X/R} ⟶ 𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X ⟶ 0`

exhibits `E = 𝒪_X(-1)^{⊕ (n+1)}` as a two-step filtered sheaf of modules, with `Ω_{X/R}` the
first step and the invertible sheaf `𝒪_X` the quotient. A filtration of a module by a submodule
with invertible quotient induces a two-step filtration of each exterior power: the first step of
`⋀^{p+1} E` is the image of `⋀^{p+1} Ω_{X/R}` and the quotient is `⋀^p Ω_{X/R} ⊗ 𝒪_X`, which is
`⋀^p Ω_{X/R}`. So the induced filtration of `⋀^{p+1} E` ought to be a short exact sequence

`0 ⟶ ⋀^{p+1} Ω_{X/R} ⟶ ⋀^{p+1} E ⟶ ⋀^p Ω_{X/R} ⟶ 0`

whose first arrow is `⋀^{p+1}` of the first arrow of the Euler sequence. This file proves that
this sequence is split exact at every stalk: a splitting of the stalk of the Euler sequence
identifies `E_x` with `Ω_x × 𝒪_x`, and for a module with a free rank-one summand
`⋀^{p+1}(M × S) ≃ ⋀^{p+1} M × ⋀^p M`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.wedgeStalkProdEquiv`: for a pointwise
  identification `N_x ≅ M_x × 𝒪_x`, the splitting `(⋀^{p+1} N)_x ≅ ⋀^{p+1}(M_x) × ⋀^p(M_x)` of
  the stalk of the degree-`p+1` exterior power.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkProdRingEquiv`: the stalk of
  `𝒪_X(-1)^{⊕ (n+1)}` as the product of the stalk of `Ω_{X/R}` with the local ring.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.projFormsStalkEquiv`: the stalk of `Ω^p_{X/R}` is
  `⋀^p` of the stalk of `Ω_{X/R}`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkEquiv`: the stalk of
  `⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)})` is `⋀^{p+1}(Ω_x) × ⋀^p(Ω_x)`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkProj`: the second arrow of the
  filtration at a stalk, the second component of that identification.

## Main results

* `exteriorPower.prodRightEquiv_map_inl`: the splitting of `⋀^{p+1}(M × S)` carries the image of
  `⋀^{p+1} M` onto the first factor.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.prodEquivOfStalkSplitting_stalkMapL`: the product
  decomposition of a split stalk complex carries the stalk of the first arrow to the inclusion
  of the first factor.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.wedgeStalkProdEquiv_stalkMapL` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkEquiv_stalkMapL`: the splitting
  carries the stalk of `⋀^{p+1}` of the first arrow to the inclusion of the first factor.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.injective_stalkMapL_eulerWedgeFirstArrow`,
  `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkProj_stalkMapL`,
  `Stacks.AlgebraicGeometry.ProjEulerSequence.exists_stalkMapL_eq_of_eulerWedgeStalkProj_eq_zero`
  and `Stacks.AlgebraicGeometry.ProjEulerSequence.surjective_eulerWedgeStalkProj`:
  `0 ⟶ ⋀^{p+1}(Ω_x) ⟶ (⋀^{p+1} E)_x ⟶ ⋀^p(Ω_x) ⟶ 0` is a short exact sequence of modules over
  the local ring, for every point and every `p`.

## Implementation notes

The degree is `((p + 1 : ℕ) : ℤ)`, since homogeneous pieces of a sheaf of graded algebras are
indexed by `ℤ`. Stalks of exterior powers are taken with the sheaf of rings in the
`CategoryTheory.Sheaf.toRingCat` spelling (`projWedgeGerm`, `eulerWedgeGerm`), so that their module
structure over `projStalkRing` is found by instance search. Exactness in the middle is stated as
two implications rather than an equality of submodules, the kernel and range being submodules
over different stalk rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite
open AlgebraicGeometry

universe u

/-! ### The exterior power of a module with a free rank-one summand, on the first factor -/

namespace exteriorPower

variable {S : Type u} [CommRing S] {M : Type u} [AddCommGroup M] [Module S M]

/-- The splitting of `⋀^{p+1}(M × S)` carries the image of `⋀^{p+1} M` onto the first
factor. -/
theorem prodRightEquiv_map_inl (p : ℕ) (u : ⋀[S]^(p + 1) M) :
    prodRightEquiv S M p (map (p + 1) (LinearMap.inl S M S) u) = (u, 0) := by
  refine Prod.ext ?_ ?_
  · show map (p + 1) (LinearMap.fst S M S) (map (p + 1) (LinearMap.inl S M S) u) = u
    rw [← LinearMap.comp_apply, ← map_comp, LinearMap.fst_comp_inl, map_id, LinearMap.id_apply]
  · have h : contraction (LinearMap.snd S M S) p (map (p + 1) (LinearMap.inl S M S) u) = 0 := by
      rw [← LinearMap.comp_apply, contraction_comp_map _ _ (LinearMap.snd_comp_inl S M S) p,
        LinearMap.zero_apply]
    show map p (LinearMap.fst S M S)
      (contraction (LinearMap.snd S M S) p (map (p + 1) (LinearMap.inl S M S) u)) = 0
    rw [h, map_zero]

end exteriorPower

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### The product decomposition of a split stalk complex, on the first arrow -/

section Split

variable {X : TopCat.{u}} (Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u})

/-- The product decomposition of a split stalk complex carries the stalk of the first arrow to
the inclusion of the first factor. -/
theorem prodEquivOfStalkSplitting_stalkMapL
    {F H G : SheafOfModules.{u} (ringSheafOfComm Oc)} {f : F ⟶ H} {g : H ⟶ G}
    (hfg : f ≫ g = 0) (y : ↥X)
    (sp : ((ShortComplex.mk f g hfg).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).Splitting)
    (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y)) :
    prodEquivOfStalkSplitting Oc hfg y sp (PresheafOfModules.stalkMapL y f.val z) = (z, 0) :=
  Prod.ext (congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ z) sp.f_r)
    (congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ z)
      ((ShortComplex.mk f g hfg).map
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).zero)

end Split

/-! ### The exterior power of a stalkwise split inclusion -/

section Wedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A B : SheafOfModules.GradedAlgebra.{u, u}
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (gen : M ⟶ A.piece 1) (gen' : N ⟶ B.piece 1)
  (hA : SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)
  (hB : SheafOfModules.GradedAlgebra.IsExteriorAlgebra B gen')
  (f : M ⟶ N) (p : ℕ) (x : ↥X)

/-- Given `e : N_x ≅ M_x × 𝒪_x`, the stalk of `⋀^{p+1} N` is `⋀^{p+1}(M_x) × ⋀^p(M_x)`: the
comparison `(⋀^{p+1} N)_x ≅ ⋀^{p+1}(N_x)` transported along `e`, followed by
`exteriorPower.prodRightEquiv`. -/
def wedgeStalkProdEquiv
    (e : ↑(TopCat.Presheaf.stalk N.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (↑(TopCat.Presheaf.stalk M.val.presheaf x) ×
          ↑(TopCat.Presheaf.stalk Osharp.obj x))) :
    ↑(TopCat.Presheaf.stalk (B.piece ((p + 1 : ℕ) : ℤ)).val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(p + 1)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x) ×
          ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^p
            ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :=
  SheafOfModules.exteriorPowerStalkEquiv B gen' hB (p + 1) x ≪≫ₗ
    exteriorPowerCongr (p + 1) e ≪≫ₗ exteriorPower.prodRightEquiv _ _ p

/-- When `e` carries the stalk of `f` to the inclusion of the first factor, the splitting
`wedgeStalkProdEquiv` carries the stalk of `⋀^{p+1} f` to the inclusion of the first factor. -/
theorem wedgeStalkProdEquiv_stalkMapL
    (e : ↑(TopCat.Presheaf.stalk N.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (↑(TopCat.Presheaf.stalk M.val.presheaf x) ×
          ↑(TopCat.Presheaf.stalk Osharp.obj x)))
    (he : ∀ z, e (PresheafOfModules.stalkMapL x f.val z) = (z, 0))
    (z : ↑(TopCat.Presheaf.stalk (A.piece ((p + 1 : ℕ) : ℤ)).val.presheaf x)) :
    wedgeStalkProdEquiv gen' hB p x e
        (PresheafOfModules.stalkMapL x (hA.pieceMap hB f ((p + 1 : ℕ) : ℤ)).val z)
      = (SheafOfModules.exteriorPowerStalkEquiv A gen hA (p + 1) x z, 0) := by
  have hcomp : exteriorPower.map (p + 1) (e : _ →ₗ[_] _) ∘ₗ
      exteriorPower.map (p + 1) (PresheafOfModules.stalkMapL x f.val) =
      exteriorPower.map (p + 1)
        (LinearMap.inl ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x)
          ↑(TopCat.Presheaf.stalk Osharp.obj x)) := by
    rw [← exteriorPower.map_comp]
    exact congrArg (exteriorPower.map (p + 1)) (LinearMap.ext he)
  refine Eq.trans (congrArg (fun y => exteriorPower.prodRightEquiv _ _ p
      (exteriorPowerCongr (p + 1) e y))
    (SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap gen gen' hA hB f (p + 1) x z)) ?_
  exact (congrArg (exteriorPower.prodRightEquiv _ _ p)
    (DFunLike.congr_fun hcomp (SheafOfModules.exteriorPowerStalkEquiv A gen hA (p + 1) x z))).trans
    (exteriorPower.prodRightEquiv_map_inl p _)

end Wedge

/-! ### The induced filtration of the exterior powers of the Euler sequence, at a stalk -/

section Euler

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The stalk of `𝒪_X(-1)^{⊕ (n+1)}` is the product of the stalk of `Ω_{X/R}` with the local
ring: `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkProdEquiv` with the stalk of the unit
sheaf of modules read as the stalk of the sheaf of rings. -/
def eulerStalkProdRingEquiv (x : ProjectiveSpectrum.top (polyGrading R n)) :
    ↑(TopCat.Presheaf.stalk (twistMinusOneSum R n).val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk
          (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj x)]
        (↑(TopCat.Presheaf.stalk (projDifferentials R n).val.presheaf x) ×
          ↑(TopCat.Presheaf.stalk
            (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj x)) :=
  eulerStalkProdEquiv R n x ≪≫ₗ LinearEquiv.prodCongr (LinearEquiv.refl _ _)
    (unitStalkCommEquiv (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) x)

/-- The identification of the stalk of `𝒪_X(-1)^{⊕ (n+1)}` carries the stalk of the first arrow
of the Euler sequence to the inclusion of the first factor. -/
theorem eulerStalkProdRingEquiv_stalkMapL (x : ProjectiveSpectrum.top (polyGrading R n))
    (z : ↑(TopCat.Presheaf.stalk (projDifferentials R n).val.presheaf x)) :
    eulerStalkProdRingEquiv R n x
        (PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val z) = (z, 0) := by
  refine Eq.trans (congrArg (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
      (unitStalkCommEquiv (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) x))
    (prodEquivOfStalkSplitting_stalkMapL
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
      (eulerFirstArrow_comp_eulerSurjection R n) x (eulerStalkSplitting R n x) z)) ?_
  have h0 : unitStalkCommEquiv (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) x 0
      = 0 := map_zero _
  exact congrArg (fun y => (z, y)) h0

/-- The local ring of `ℙⁿ_R` at `x`, as the stalk of the sheaf of commutative rings. -/
abbrev projStalkRing (x : ProjectiveSpectrum.top (polyGrading R n)) : Type u :=
  ↑(TopCat.Presheaf.stalk (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj x)

/-- The germ at `x` of the relative differentials `Ω_{X/R}` of `ℙⁿ_R`. -/
abbrev projDiffGerm (x : ProjectiveSpectrum.top (polyGrading R n)) : Type u :=
  ↑(TopCat.Presheaf.stalk (projDifferentials R n).val.presheaf x)

/-- The germ at `x` of `⋀^q Ω_{X/R}`, the degree-`q` exterior power of the relative
differentials of `ℙⁿ_R`, over the sheaf of rings in the `CategoryTheory.Sheaf.toRingCat`
spelling. -/
abbrev projWedgeGerm (x : ProjectiveSpectrum.top (polyGrading R n)) (q : ℤ) : Type u :=
  ↑(TopCat.Presheaf.stalk (SheafOfModules.val
    (R := toRingCat (Opens.grothendieckTopology (ProjectiveSpectrum.top (polyGrading R n)))
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)))
    (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) q)).presheaf x)

/-- The germ at `x` of `⋀^q (𝒪_X(-1)^{⊕ (n+1)})`, the degree-`q` exterior power of the middle
term of the Euler sequence of `ℙⁿ_R`, over the sheaf of rings in the
`CategoryTheory.Sheaf.toRingCat` spelling. -/
abbrev eulerWedgeGerm (x : ProjectiveSpectrum.top (polyGrading R n)) (q : ℤ) : Type u :=
  ↑(TopCat.Presheaf.stalk (SheafOfModules.val
    (R := toRingCat (Opens.grothendieckTopology (ProjectiveSpectrum.top (polyGrading R n)))
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)))
    (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n) q)).presheaf x)

variable (p : ℕ) (x : ProjectiveSpectrum.top (polyGrading R n))

/-- The stalk of `Ω^p_{X/R}` is `⋀^p` of the stalk of `Ω_{X/R}`, for the relative differentials
of `ℙⁿ_R`. -/
def projFormsStalkEquiv :
    projWedgeGerm R n x (p : ℤ) ≃ₗ[projStalkRing R n x]
      ⋀[projStalkRing R n x]^p (projDiffGerm R n x) :=
  SheafOfModules.exteriorPowerStalkEquiv
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (projDifferentials R n))
    p x

/-- The stalk of `⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)})` is `⋀^{p+1}(Ω_x) × ⋀^p(Ω_x)`, the split form of
the filtration of `⋀^{p+1}` induced by the Euler sequence. -/
def eulerWedgeStalkEquiv :
    eulerWedgeGerm R n x ((p + 1 : ℕ) : ℤ) ≃ₗ[projStalkRing R n x]
      (⋀[projStalkRing R n x]^(p + 1) (projDiffGerm R n x) ×
        ⋀[projStalkRing R n x]^p (projDiffGerm R n x)) :=
  wedgeStalkProdEquiv (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n))
    p x (eulerStalkProdRingEquiv R n x)

/-- The second arrow of the induced filtration at a stalk: the second component of
`Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkEquiv`. -/
def eulerWedgeStalkProj :
    eulerWedgeGerm R n x ((p + 1 : ℕ) : ℤ) →ₗ[projStalkRing R n x]
      ⋀[projStalkRing R n x]^p (projDiffGerm R n x) :=
  LinearMap.snd _ _ _ ∘ₗ (eulerWedgeStalkEquiv R n p x).toLinearMap

/-- The identification `eulerWedgeStalkEquiv` carries the stalk of `⋀^{p+1}` of the first arrow
of the Euler sequence to the inclusion of the first factor, through `projFormsStalkEquiv`. -/
theorem eulerWedgeStalkEquiv_stalkMapL (z : projWedgeGerm R n x ((p + 1 : ℕ) : ℤ)) :
    eulerWedgeStalkEquiv R n p x (PresheafOfModules.stalkMapL x
          (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
            (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)).val z)
      = (projFormsStalkEquiv R n (p + 1) x z, 0) :=
  wedgeStalkProdEquiv_stalkMapL
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (projDifferentials R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n))
    (eulerFirstArrow R n) p x (eulerStalkProdRingEquiv R n x)
    (eulerStalkProdRingEquiv_stalkMapL R n x) z

/-- The stalk of `⋀^{p+1}` of the first arrow of the Euler sequence is injective. -/
theorem injective_stalkMapL_eulerWedgeFirstArrow :
    Function.Injective (PresheafOfModules.stalkMapL x
      (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)).val) := by
  intro z z' hzz'
  have h : (projFormsStalkEquiv R n (p + 1) x z,
        (0 : ⋀[projStalkRing R n x]^p (projDiffGerm R n x))) =
      (projFormsStalkEquiv R n (p + 1) x z', 0) :=
    ((eulerWedgeStalkEquiv_stalkMapL R n p x z).symm.trans
      (congrArg (eulerWedgeStalkEquiv R n p x) hzz')).trans
      (eulerWedgeStalkEquiv_stalkMapL R n p x z')
  exact (projFormsStalkEquiv R n (p + 1) x).injective (congrArg Prod.fst h)

/-- The stalk sequence is a complex: the second arrow kills the image of the stalk of `⋀^{p+1}`
of the first arrow of the Euler sequence. -/
theorem eulerWedgeStalkProj_stalkMapL (z : projWedgeGerm R n x ((p + 1 : ℕ) : ℤ)) :
    eulerWedgeStalkProj R n p x (PresheafOfModules.stalkMapL x
        (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
          (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)).val z) = 0 :=
  congrArg Prod.snd (eulerWedgeStalkEquiv_stalkMapL R n p x z)

/-- Exactness of the stalk sequence in the middle: a germ of `⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)})`
killed by the second arrow is a value of the stalk of `⋀^{p+1}` of the first arrow of the Euler
sequence. -/
theorem exists_stalkMapL_eq_of_eulerWedgeStalkProj_eq_zero
    (w : eulerWedgeGerm R n x ((p + 1 : ℕ) : ℤ))
    (hw : eulerWedgeStalkProj R n p x w = 0) :
    ∃ z, PresheafOfModules.stalkMapL x
      (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)).val z = w := by
  refine ⟨(projFormsStalkEquiv R n (p + 1) x).symm (eulerWedgeStalkEquiv R n p x w).1,
    (eulerWedgeStalkEquiv R n p x).injective ?_⟩
  refine Eq.trans (eulerWedgeStalkEquiv_stalkMapL R n p x _) ?_
  refine Eq.trans (congrArg (fun y => (y, (0 : ⋀[projStalkRing R n x]^p (projDiffGerm R n x))))
    ((projFormsStalkEquiv R n (p + 1) x).apply_symm_apply _)) ?_
  exact congrArg (fun y => ((eulerWedgeStalkEquiv R n p x w).1, y)) hw.symm

/-- The second arrow of the induced filtration is surjective at every stalk. -/
theorem surjective_eulerWedgeStalkProj :
    Function.Surjective (eulerWedgeStalkProj R n p x) := fun v =>
  ⟨(eulerWedgeStalkEquiv R n p x).symm (0, v),
    congrArg Prod.snd ((eulerWedgeStalkEquiv R n p x).apply_symm_apply (0, v))⟩

end Euler

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
