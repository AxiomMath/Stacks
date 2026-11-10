module

public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedPieceQuotientEquiv
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedCongr

/-!
# A degreewise identification with an associated graded ring is a ring isomorphism of sections

Let `Z` be a scheme, `𝓐` a sheaf of graded `𝒪_Z`-algebras with commutative homogeneous
multiplication, `W ⊆ Z` an affine open, `R₀` a commutative ring, `J ⊆ R₀` an ideal and
`φ : R₀ ⟶ Γ(Z, W)` a ring homomorphism. Suppose given, for every `n : ℕ`, an additive bijection

`Jⁿ/Jⁿ⁺¹ ≃+ Γ(𝓐ₙ, W)`

carrying the graded unit to the unit, graded products to the homogeneous multiplication of `𝓐`,
and the action of `R₀` to the action of `Γ(Z, W)` through `φ`. If `𝓐` vanishes in negative
degrees, those bijections assemble into a **ring isomorphism**

`Gr_J(R₀) ≃+* Γ(W, 𝓐_*)`

onto the sections over `W` of the ungraded realization of `𝓐`, carrying the structure map of
`Gr_J(R₀)` to the structural ring map of the algebra sheaf.

## Why this is one module and not two

The degreewise bijections themselves come from
`Stacks.AssociatedGradedSections.pieceEquivOfLocalMap`, in the lighter companion module
`StacksFrontier/AlgebraicGeometry/Constructions/GradedPieceQuotientEquiv.lean`; what is assembled
here is their passage to a ring isomorphism.

The same four-step assembly is what
`StacksFrontier/AlgebraicGeometry/Conormal/ConormalSectionsRing.lean` performs for the conormal
algebra of an immersion, and what
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/GradedPullbackSectionsRing.lean` needs for
the pullback of a Rees algebra along a closed immersion. The steps are: inclusion of the
degree-`n` summand, `DirectSum.toSemiring` to get a ring homomorphism out of the external direct
sum, `Stacks.bijective_directSumNatToIntApp` to see that the nonnegative degrees are all of the
`ℤ`-graded realization, and `Stacks.RelativeSpec.totalSectionsRingEquiv` to pass from the direct
sum of the sections of the pieces to the sections of the sheafification. Nothing in it is about
conormal algebras, so it is stated here once and both consumers call it.

## Main definitions

* `Stacks.AssociatedGradedSections.incl`: the degreewise identification followed by the
  inclusion of the degree-`n` summand of the ungraded realization.
* `Stacks.AssociatedGradedSections.totalHom`: the ring homomorphism
  `Gr_J(R₀) ⟶ ⨁_{n : ℤ} Γ(𝓐ₙ, W)`.
* `Stacks.AssociatedGradedSections.sectionsRingEquiv`: **`Gr_J(R₀) ≃+* Γ(W, 𝓐_*)`.**

## Main results

* `Stacks.AssociatedGradedSections.bijective_totalHom`: the comparison is bijective.
* `Stacks.AssociatedGradedSections.sectionsRingEquiv_gradeZeroRingHom`: **the identification
  carries the structure map of `Gr_J(R₀)` to the structural ring map of the algebra sheaf**,
  composed with `φ`.

## Implementation notes

The source is `ℕ`-graded and the target `ℤ`-graded, so the product of the degree-`n` and
degree-`m` summands is indexed by `((n + m : ℕ) : ℤ)` on one side and `(n : ℤ) + (m : ℤ)` on the
other. `Nat.cast` into `ℤ` is `Int.ofNat` and `Int.add` reduces on constructors, so the two are
definitionally equal and each such step is an `exact`.

The graded unit and the graded product of `fun n => AssociatedGraded.piece J n` are
`AssociatedGraded.mk J 0 ⟨1, _⟩` and `AssociatedGraded.homogeneousSMul J` by `rfl`, which is what
lets the hypotheses `hone` and `hmul` discharge the hypotheses of `DirectSum.toSemiring`
directly. Two subtype proofs of `1 ∈ J⁰` differ, and proof irrelevance makes that free.

Bijectivity is proved by exhibiting the inverse degreewise and never by `rw` under
`DirectSum.of`, whose index family is eta-expanded by the abbreviations; this is the discipline
recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafifiedDirectSum.lean`.

No `@[stacks]` attribute is attached: this is an assembly internal to the development.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec
open scoped DirectSum

universe u

namespace Stacks.AssociatedGradedSections

variable {Z : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (V : (Opens ↥Z)ᵒᵖ) (a : (A.piece i).val.obj V) (b : (A.piece j).val.obj V),
    HEq ((A.mul i j).app V a b) ((A.mul j i).app V b a))
  {W : Z.Opens} {R₀ : Type u} [CommRing R₀] (J : Ideal R₀) (φ : R₀ →+* Γ(Z, W))

/-- The homogeneous pieces of `𝓐`, as a `ℤ`-indexed family of presheaves of modules: the shape
the ungraded realization is formed from. -/
abbrev piecePresheaf (n : ℤ) : PresheafOfModules.{u} Z.ringCatSheaf.obj := (A.piece n).val

/-! ### The ring isomorphism -/

variable (e : (n : ℕ) → AssociatedGraded.piece (M := R₀) J n ≃+ (piecePresheaf A n).obj (op W))

/-- The degreewise identification followed by the inclusion of the degree-`n` summand of the
ungraded realization. -/
def incl (n : ℕ) :
    AssociatedGraded.piece (M := R₀) J n →+ A.toPresheafGradedAlgebra.Total (op W) :=
  (DirectSum.of (fun m : ℤ => ((piecePresheaf A m).obj (op W) : Type u)) (n : ℤ)).comp
    (e n).toAddMonoidHom

/-- `Stacks.AssociatedGradedSections.incl` sends `x` in degree `n` to `e n x` in the degree-`n`
summand. -/
theorem incl_apply (n : ℕ) (x : AssociatedGraded.piece (M := R₀) J n) :
    incl A J e n x =
      DirectSum.of (fun m : ℤ => ((piecePresheaf A m).obj (op W) : Type u)) (n : ℤ) (e n x) :=
  rfl

/-- **The degree-zero summand carries the unit to the unit.** -/
theorem incl_one
    (hone : e 0 (GradedMonoid.GOne.one : AssociatedGraded.piece (M := R₀) J 0) =
      A.one.eval (op W)) :
    incl A J e 0 (GradedMonoid.GOne.one : AssociatedGraded.piece (M := R₀) J 0) = 1 :=
  (congrArg
      (DirectSum.of (fun m : ℤ => ((piecePresheaf A m).obj (op W) : Type u)) 0) hone).trans
    (A.toPresheafGradedAlgebra.one_eq_incl (op W)).symm

/-- **The summands multiply as the associated graded ring does.** -/
theorem incl_mul
    (hmul : ∀ (n m : ℕ) (a : AssociatedGraded.piece (M := R₀) J n)
        (b : AssociatedGraded.piece (M := R₀) J m),
      e (n + m) (AssociatedGraded.homogeneousSMul J a b) =
        (A.mul (n : ℤ) (m : ℤ)).app (op W) (e n a) (e m b))
    (n m : ℕ) (a : AssociatedGraded.piece (M := R₀) J n)
    (b : AssociatedGraded.piece (M := R₀) J m) :
    incl A J e (n + m) (AssociatedGraded.homogeneousSMul J a b) =
      incl A J e n a * incl A J e m b :=
  (congrArg
      (DirectSum.of (fun k : ℤ => ((piecePresheaf A k).obj (op W) : Type u)) ((n + m : ℕ) : ℤ))
      (hmul n m a b)).trans
    (A.toPresheafGradedAlgebra.incl_mul_incl (n : ℤ) (m : ℤ) (e n a) (e m b)).symm

variable
  (hone : e 0 (GradedMonoid.GOne.one : AssociatedGraded.piece (M := R₀) J 0) = A.one.eval (op W))
  (hmul : ∀ (n m : ℕ) (a : AssociatedGraded.piece (M := R₀) J n)
      (b : AssociatedGraded.piece (M := R₀) J m),
    e (n + m) (AssociatedGraded.homogeneousSMul J a b) =
      (A.mul (n : ℤ) (m : ℤ)).app (op W) (e n a) (e m b))

/-- **The degreewise identifications, as a ring homomorphism** out of the associated graded ring
into the direct sum of the sections of the homogeneous pieces. -/
def totalHom :
    AssociatedGraded.gradedRing J →+* A.toPresheafGradedAlgebra.Total (op W) :=
  DirectSum.toSemiring (incl A J e) (incl_one A J e hone)
    fun {_ _} a b => incl_mul A J e hmul _ _ a b

/-- `Stacks.AssociatedGradedSections.totalHom` restricts to
`Stacks.AssociatedGradedSections.incl` on the degree-`n` summand. -/
theorem totalHom_of (n : ℕ) (x : AssociatedGraded.piece (M := R₀) J n) :
    totalHom A J e hone hmul
        (DirectSum.of (fun m => AssociatedGraded.piece (M := R₀) J m) n x) =
      incl A J e n x :=
  DirectSum.toSemiring_of (incl A J e) _ _ n x

/-- The degreewise identifications, assembled over the nonnegative degrees only. -/
def natSum :
    AssociatedGraded.gradedRing J →+
      Stacks.DirectSumType (fun n : ℕ => piecePresheaf A (n : ℤ)) (op W) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of
        (fun m : ℕ => ((piecePresheaf A (m : ℤ)).obj (op W) : Type u)) n).comp
      (e n).toAddMonoidHom

/-- `Stacks.AssociatedGradedSections.natSum` sends `x` in degree `n` to `e n x` in the degree-`n`
summand. -/
theorem natSum_of (n : ℕ) (x : AssociatedGraded.piece (M := R₀) J n) :
    natSum A J e (DirectSum.of (fun m => AssociatedGraded.piece (M := R₀) J m) n x) =
      DirectSum.of (fun m : ℕ => ((piecePresheaf A (m : ℤ)).obj (op W) : Type u)) n (e n x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The inverse of `Stacks.AssociatedGradedSections.natSum`, degree by degree. -/
def natSumInv :
    Stacks.DirectSumType (fun n : ℕ => piecePresheaf A (n : ℤ)) (op W) →+
      AssociatedGraded.gradedRing J :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m => AssociatedGraded.piece (M := R₀) J m) n).comp
      (e n).symm.toAddMonoidHom

/-- `Stacks.AssociatedGradedSections.natSumInv` sends `y` in degree `n` to `(e n).symm y` in the
degree-`n` summand. -/
theorem natSumInv_of (n : ℕ) (y : (piecePresheaf A (n : ℤ)).obj (op W)) :
    natSumInv A J e (DirectSum.of _ n y) =
      DirectSum.of (fun m => AssociatedGraded.piece (M := R₀) J m) n ((e n).symm y) :=
  DirectSum.toAddMonoid_of _ _ _

/-- `Stacks.AssociatedGradedSections.natSum` is bijective. -/
theorem bijective_natSum : Function.Bijective (natSum A J e) := by
  refine Function.bijective_iff_has_inverse.2 ⟨natSumInv A J e, fun z => ?_, fun y => ?_⟩
  · refine DFunLike.congr_fun (x := z) (DirectSum.addHom_ext
      (f := (natSumInv A J e).comp (natSum A J e)) (g := AddMonoidHom.id _) fun n x => ?_)
    rw [AddMonoidHom.comp_apply, natSum_of, natSumInv_of, (e n).symm_apply_apply]
    rfl
  · refine DFunLike.congr_fun (x := y) (DirectSum.addHom_ext
      (f := (natSum A J e).comp (natSumInv A J e)) (g := AddMonoidHom.id _) fun n x => ?_)
    rw [AddMonoidHom.comp_apply, natSumInv_of, natSum_of, (e n).apply_symm_apply]
    rfl

/-- The underlying additive map of `Stacks.AssociatedGradedSections.totalHom` is the degreewise
identification followed by the inclusion of the nonnegative degrees. -/
theorem totalHom_apply_eq (z : AssociatedGraded.gradedRing J) :
    totalHom A J e hone hmul z =
      Stacks.directSumNatToIntApp (piecePresheaf A) (op W) (natSum A J e z) := by
  refine DFunLike.congr_fun (x := z) (DirectSum.addHom_ext
    (f := (totalHom A J e hone hmul).toAddMonoidHom)
    (g := (Stacks.directSumNatToIntApp (piecePresheaf A) (op W)).comp (natSum A J e))
    fun n x => ?_)
  exact ((totalHom_of A J e hone hmul n x).trans (incl_apply A J e n x)).trans
    ((Stacks.directSumNatToIntApp_of (piecePresheaf A) (op W) n (e n x)).symm.trans
      (congrArg (Stacks.directSumNatToIntApp (piecePresheaf A) (op W))
        (natSum_of A J e n x).symm))

/-- **The comparison is bijective**: the degreewise identification is, and the negative degrees
contribute nothing because `𝓐` vanishes there. -/
theorem bijective_totalHom (hneg : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    Function.Bijective (totalHom A J e hone hmul) := by
  have hzero : ∀ n : ℤ, n < 0 → Subsingleton ((piecePresheaf A n).obj (op W)) := fun n hn =>
    Stacks.subsingleton_of_isZero (hneg n hn) (op W)
  have hcomp : Function.Bijective fun z =>
      Stacks.directSumNatToIntApp (piecePresheaf A) (op W) (natSum A J e z) :=
    (Stacks.bijective_directSumNatToIntApp (piecePresheaf A) (op W) hzero).comp
      (bijective_natSum A J e)
  exact (funext fun z => totalHom_apply_eq A J e hone hmul z) ▸ hcomp

/-- **`Gr_J(R₀) ≃+* Γ(W, 𝓐_*)`**: the sections over an affine open `W` of the ungraded
realization of `𝓐` are the associated graded ring of `J`.

The degreewise identification is the hypothesis `e`, and the passage from the direct sum of the
sections of the pieces to the sections of the sheafification is
`Stacks.RelativeSpec.totalSectionsRingEquiv`, `W` being affine. -/
def sectionsRingEquiv (hneg : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) (hW : IsAffineOpen W) :
    AssociatedGraded.gradedRing J ≃+* ↥((gradedAlgebraSheaf Z A hc).sections W) :=
  (RingEquiv.ofBijective (totalHom A J e hone hmul)
      (bijective_totalHom A J e hone hmul hneg)).trans
    (Stacks.RelativeSpec.totalSectionsRingEquiv Z A hc hW)

/-- The degree-zero class of `r : R₀` is `r` acting on the graded unit. -/
theorem gradeZeroMk_eq_smul_one (r : R₀) :
    AssociatedGraded.gradeZeroMk J r =
      r • (GradedMonoid.GOne.one : AssociatedGraded.piece (M := R₀) J 0) := by
  change AssociatedGraded.mk J 0 _ = r • AssociatedGraded.mk J 0 _
  rw [AssociatedGraded.mk, AssociatedGraded.mk, ← Submodule.Quotient.mk_smul]
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (mul_one r).symm)

/-- **The identification carries the structure map of `Gr_J(R₀)` to the structural ring map of
the algebra sheaf**, composed with `φ`. In degree zero the first is `r ↦ [r]₀` and the second
`s ↦ s • 1`, and the hypothesis `hsmul` says that the degreewise identification carries one to
the other. -/
theorem sectionsRingEquiv_gradeZeroRingHom (hneg : ∀ n : ℤ, n < 0 → IsZero (A.piece n))
    (hW : IsAffineOpen W)
    (hsmul : ∀ (n : ℕ) (r : R₀) (a : AssociatedGraded.piece (M := R₀) J n),
      e n (r • a) = (show Z.ringCatSheaf.obj.obj (op W) from φ r) • e n a)
    (r : R₀) :
    sectionsRingEquiv A hc J e hone hmul hneg hW (AssociatedGraded.gradeZeroRingHom J r) =
      ((gradedAlgebraSheaf Z A hc).hom.hom.app (op W)).hom (φ r) := by
  have hsm : e 0 (AssociatedGraded.gradeZeroMk J r) =
      (show Z.ringCatSheaf.obj.obj (op W) from φ r) • A.one.eval (op W) :=
    (congrArg (e 0) (gradeZeroMk_eq_smul_one J r)).trans
      ((hsmul 0 r GradedMonoid.GOne.one).trans
        (congrArg (fun z => (show Z.ringCatSheaf.obj.obj (op W) from φ r) • z) hone))
  have hincl : totalHom A J e hone hmul (AssociatedGraded.gradeZeroRingHom J r) =
      A.toPresheafGradedAlgebra.structureMap (op W) (φ r) :=
    ((totalHom_of A J e hone hmul 0 (AssociatedGraded.gradeZeroMk J r)).trans
        ((incl_apply A J e 0 _).trans
          (congrArg
            (DirectSum.of (fun m : ℤ => ((piecePresheaf A m).obj (op W) : Type u)) (0 : ℤ))
            hsm))).trans
      ((A.toPresheafGradedAlgebra.incl_smul 0 (φ r) (A.one.eval (op W))).trans
        (congrArg (fun z => (show Z.ringCatSheaf.obj.obj (op W) from φ r) • z)
          (A.toPresheafGradedAlgebra.one_eq_incl (op W)).symm))
  exact congrArg (fun z => Stacks.RelativeSpec.totalSectionsRingEquiv Z A hc hW z) hincl

end Stacks.AssociatedGradedSections

end
