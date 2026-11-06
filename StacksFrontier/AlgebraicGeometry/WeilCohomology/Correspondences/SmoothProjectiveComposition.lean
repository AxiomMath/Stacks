module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionAssoc
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GradedStructure
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.SmoothProjectiveScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The composition of correspondences between smooth projective schemes

`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GradedStructure` assembles a
graded category over `ℚ` (Definition 09L2) out of any family `Corr X Y r` of `ℚ`-vector spaces
with a degree-additive composition which is `ℚ`-bilinear, associative and unital
(`Stacks.WeilCohomology.GradedCompositionData`). This file supplies that input for the smooth
projective schemes over a field `k`, from the composition of correspondences of Section 0FFZ.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveCorr`: the correspondences of degree `r` between smooth
  projective schemes over `k` (`Stacks.WeilCohomology.SmoothProjectiveScheme`).
* `Stacks.WeilCohomology.correspondenceCompositionData`: the composition of Section 0FFZ and the
  diagonal correspondences, as a `GradedCompositionData`, with every law proved.

## Implementation notes

Composition is the real composition of Section 0FFZ, `Stacks.WeilCohomology.comp`
(`c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`, piece by piece on the equidimensional parts), and the
identity is the diagonal correspondence `Stacks.WeilCohomology.diagonalCorr`. Every law is
proved, from two properties of the family `Δ` of Gysin classes of diagonals with which the
intersection products are formed: associativity
(`Stacks.WeilCohomology.DiagonalClassFamily.CompositionAssoc`, Stacks 0FG0 (1), proved from
0FC1/0FFB/0FFC in `...Correspondences.Associativity`) and the proper-intersection formula
(`Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`, Stacks 0FFD), which gives
the unit laws `[Δ] ∘ c = c = c ∘ [Δ]` by the source's computation on `X × X × Y`
(`...Correspondences.DiagonalUnit`). For the canonical family of Gysin classes of diagonals
(Stacks 0FBR) both are theorems, and the `@[stacks 0FG2]` registration is on the instance at that
family, `Stacks.WeilCohomology.canonicalCorrespondences_gradedCategory`
(`...Correspondences.CanonicalGradedCategory`).

## References

* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.WeilCohomology

/-! ### Smooth projective schemes and their correspondences -/

section SmoothProjective

open _root_.AlgebraicGeometry _root_.Stacks.Chow

variable {k : Type u} [Field k]

namespace SmoothProjectiveScheme

/-- The structure morphism of a smooth projective scheme over `k` is proper. -/
instance (P : (SmoothProjectiveScheme k).FullSubcategory) : IsProper P.obj.hom :=
  (isProjective P).isProper

/-- The structure morphism of a smooth projective scheme over `k` is separated. -/
instance (P : (SmoothProjectiveScheme k).FullSubcategory) : IsSeparated P.obj.hom :=
  inferInstance

/-- The structure morphism of a smooth projective scheme over `k` is quasi-compact. -/
instance (P : (SmoothProjectiveScheme k).FullSubcategory) : QuasiCompact P.obj.hom :=
  inferInstance

/-- The structure morphism of a smooth projective scheme over `k` is locally of finite type. -/
instance (P : (SmoothProjectiveScheme k).FullSubcategory) : LocallyOfFiniteType P.obj.hom :=
  inferInstance

end SmoothProjectiveScheme

/-- Transport along the reflexive equality of degrees is the identity on correspondences of
mixed dimension. -/
theorem corrCongr_rfl {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY]
    [IsSeparated sY] {r : ℤ} (c : Stacks.WeilCohomology.Corr k sX sY r) :
    corrCongr k sX sY (rfl : r = r) c = c := by
  induction c using Stacks.WeilCohomology.Corr.induction_on with
  | zero => exact LinearEquiv.map_zero _
  | add a b ha hb => rw [LinearEquiv.map_add, ha, hb]
  | lof d e x =>
      rw [corrCongr_lof_lof]
      congr 2
      induction x using TensorProduct.inductionOn with
      | add a b ha hb => rw [LinearEquiv.map_add, ha, hb]
      | tmul q α => rw [correspondenceCongr_tmul]; rfl

namespace SmoothProjectiveScheme

/-- **Correspondences of degree `r`** from `P` to `Q`, Section 0FFZ:
`Corrʳ(P, Q) = ⊕_d CH^{d+r}(P_d × Q) ⊗ ℚ`, the degree-`r` morphisms of the category of
correspondences. A type synonym for `Stacks.WeilCohomology.Corr`, so that its additive and
`ℚ`-linear structures are fixed once and found without unfolding the direct sums. -/
def _root_.Stacks.WeilCohomology.SmoothProjectiveCorr
    (P Q : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) : Type u :=
  Stacks.WeilCohomology.Corr k P.obj.hom Q.obj.hom r

/-- The additive group structure on correspondences of degree `r`. -/
noncomputable instance (P Q : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    AddCommGroup (SmoothProjectiveCorr P Q r) :=
  inferInstanceAs (AddCommGroup (Stacks.WeilCohomology.Corr k P.obj.hom Q.obj.hom r))

/-- The `ℚ`-vector space structure on correspondences of degree `r`. -/
noncomputable instance (P Q : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    Module ℚ (SmoothProjectiveCorr P Q r) :=
  inferInstanceAs (Module ℚ (Stacks.WeilCohomology.Corr k P.obj.hom Q.obj.hom r))

/-- The scalar actions of `ℚ` on correspondences of degree `r` commute with each other. -/
instance (P Q : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    SMulCommClass ℚ ℚ (SmoothProjectiveCorr P Q r) :=
  smulCommClass_self ℚ _

/-- The identification of `Stacks.WeilCohomology.SmoothProjectiveCorr` with the
correspondences of Section 0FFZ. -/
noncomputable def _root_.Stacks.WeilCohomology.SmoothProjectiveCorr.toCorr
    (P Q : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    SmoothProjectiveCorr P Q r ≃ₗ[ℚ] Stacks.WeilCohomology.Corr k P.obj.hom Q.obj.hom r :=
  LinearEquiv.refl ℚ _

end SmoothProjectiveScheme

open SmoothProjectiveCorr

variable (k)

/-- Composition of correspondences between smooth projective schemes over `k`,
`Corrʳ(P, Q) × Corrˢ(Q, R) ⟶ Corr^{r+s}(P, R)`, formed with the family `Δ` of diagonal classes:
the composition `Stacks.WeilCohomology.comp` of Section 0FFZ. -/
noncomputable def correspondenceComp (Δ : DiagonalClassFamily k)
    {P Q R : (SmoothProjectiveScheme k).FullSubcategory} {r s : ℤ} :
    SmoothProjectiveCorr P Q r →ₗ[ℚ] SmoothProjectiveCorr Q R s →ₗ[ℚ]
      SmoothProjectiveCorr P R (r + s) :=
  ((comp k P.obj.hom Q.obj.hom R.obj.hom Δ r s).compl₁₂ (toCorr P Q r).toLinearMap
    (toCorr Q R s).toLinearMap).compr₂ (toCorr P R (r + s)).symm.toLinearMap

/-- Under `Stacks.WeilCohomology.SmoothProjectiveCorr.toCorr`, the composition
`Stacks.WeilCohomology.correspondenceComp` is the composition `Stacks.WeilCohomology.comp` of
correspondences. -/
theorem toCorr_correspondenceComp (Δ : DiagonalClassFamily k)
    {P Q R : (SmoothProjectiveScheme k).FullSubcategory} {r s : ℤ} (a : SmoothProjectiveCorr P Q r)
    (b : SmoothProjectiveCorr Q R s) :
    toCorr P R (r + s) (correspondenceComp k Δ a b) =
      comp k P.obj.hom Q.obj.hom R.obj.hom Δ r s (toCorr P Q r a) (toCorr Q R s b) :=
  rfl

/-- The diagonal correspondence `[Δ_P] ∈ Corr⁰(P, P)` of a smooth projective scheme over `k`. -/
noncomputable def correspondenceDiagonal (P : (SmoothProjectiveScheme k).FullSubcategory) :
    SmoothProjectiveCorr P P 0 :=
  (toCorr P P 0).symm (diagonalCorr k P.obj.hom)

variable {k} in
/-- Transport along an equality of degrees, read in the total module `⨁ᵣ Corrʳ(P, Q)`, is the
identity. -/
theorem of_toCorr_symm_corrCongr {P Q : (SmoothProjectiveScheme k).FullSubcategory} {r r' : ℤ}
    (h : r = r') (c : SmoothProjectiveCorr P Q r) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) r'
        ((toCorr P Q r').symm (corrCongr k P.obj.hom Q.obj.hom h (toCorr P Q r c))) =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) r c := by
  subst h
  exact congrArg (DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) r)
    (corrCongr_rfl P.obj.hom Q.obj.hom c)

/-- **Composition of correspondences between smooth projective schemes over `k`**, assembled
into `Stacks.WeilCohomology.GradedCompositionData`: the degree-`r` piece is
`Corrʳ(X, Y) = ⊕_d CH^{d+r}(X_d × Y) ⊗ ℚ`, composition is the composition
`Stacks.WeilCohomology.comp` of Section 0FFZ formed with the family `Δ` of diagonal classes,
and the identity of `X` is the diagonal correspondence `[Δ_X]`. Associativity is
`Stacks.WeilCohomology.comp_assoc` (Stacks 0FG0 (1)) from `hassoc`, the unit laws are
`Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula.comp_diagonalCorr` and
`...diagonalCorr_comp` from `hΔ`, the proper-intersection formula of Stacks 0FFD.

For the canonical family both properties are theorems (Stacks 0FG0 (1) and Stacks 0FFD), which is
how the category of Stacks 0FG2 is obtained
(`Stacks.WeilCohomology.canonicalCorrespondenceCompositionData`). -/
@[sga "7 XX 4.4" "partial"]
noncomputable def correspondenceCompositionData (Δ : DiagonalClassFamily k)
    (hassoc : Δ.CompositionAssoc) (hΔ : Δ.ProperIntersectionFormula) :
    GradedCompositionData fun (P Q : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) ↦
      SmoothProjectiveCorr P Q r where
  comp := correspondenceComp k Δ
  diagonal := correspondenceDiagonal k
  of_diagonal_comp {P Q} {r} a := by
    have h := congrArg (toCorr P Q (0 + r)).symm
      (hΔ.comp_diagonalCorr k P.obj.hom Q.obj.hom r (toCorr P Q r a))
    exact (congrArg (DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) (0 + r)) h).trans
      (of_toCorr_symm_corrCongr (zero_add r).symm a)
  of_comp_diagonal {P Q} {r} a := by
    have h := congrArg (toCorr P Q (r + 0)).symm
      (hΔ.diagonalCorr_comp k P.obj.hom Q.obj.hom r (toCorr P Q r a))
    exact (congrArg (DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) (r + 0)) h).trans
      (of_toCorr_symm_corrCongr (add_zero r).symm a)
  of_assoc {P Q R T} {r s t} a b c := by
    have h := congrArg (toCorr P T (r + (s + t))).symm
      (comp_assoc k P.obj.hom Q.obj.hom R.obj.hom T.obj.hom Δ hassoc r s t
        (toCorr P Q r a) (toCorr Q R s b) (toCorr R T t c))
    exact (of_toCorr_symm_corrCongr (add_assoc r s t) _).symm.trans
      (congrArg (DirectSum.of (fun i ↦ SmoothProjectiveCorr P T i) (r + (s + t))) h)

/-- Composition in `Stacks.WeilCohomology.correspondenceCompositionData` is composition of
correspondences. -/
theorem toCorr_correspondenceCompositionData_comp (Δ : DiagonalClassFamily k)
    (hassoc : Δ.CompositionAssoc) (hΔ : Δ.ProperIntersectionFormula)
    {P Q R : (SmoothProjectiveScheme k).FullSubcategory} {r s : ℤ} (a : SmoothProjectiveCorr P Q r)
    (b : SmoothProjectiveCorr Q R s) :
    toCorr P R (r + s) ((correspondenceCompositionData k Δ hassoc hΔ).comp a b) =
      comp k P.obj.hom Q.obj.hom R.obj.hom Δ r s (toCorr P Q r a) (toCorr Q R s b) :=
  rfl

/-- The identities of `Stacks.WeilCohomology.correspondenceCompositionData` are the diagonal
correspondences. -/
theorem toCorr_correspondenceCompositionData_diagonal (Δ : DiagonalClassFamily k)
    (hassoc : Δ.CompositionAssoc) (hΔ : Δ.ProperIntersectionFormula)
    (P : (SmoothProjectiveScheme k).FullSubcategory) :
    toCorr P P 0 ((correspondenceCompositionData k Δ hassoc hΔ).diagonal P) =
      diagonalCorr k P.obj.hom :=
  rfl

end SmoothProjective

end Stacks.WeilCohomology

end
