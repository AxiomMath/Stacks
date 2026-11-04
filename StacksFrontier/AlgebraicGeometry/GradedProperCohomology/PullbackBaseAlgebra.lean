module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedBaseAlgebraHom
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The base algebra map of [Stacks, Tag 0897] for `𝓑 = f^* B̃`, part one

`Stacks.AlgebraicGeometry.GradedProperCohomology.HomogeneousSections.isProper_structureHom`
produces the proper structure morphism `f' : X' ⟶ Spec B` of [Stacks, Tag 0897]'s base change out
of two data about the homogeneous-sections datum: its compatibility with the structure maps
(`IsStructureCompatible`) and the local surjectivity of the induced `ψ : f^* 𝔅 ⟶ 𝓐`. **This file
reads `𝓑 = f^* B̃` as a `GradedQcohAlgebra` and supplies the compatibility.**

The structure map of the ungraded realization of `𝓑` is `r ↦ r • 1`, and the degree-zero global
section named by `algebraMap A B a = a • 1` is the pullback of the section `a • 1` of `B̃₀`,
because a global section of `B̃ₖ = (𝒜ₖ)~` is the image of a homogeneous element under
`Stacks.AffineBaseChange.toOpenₗ` and that map is `A`-linear.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.pullbackGradedQcoh`: **`𝓑 = f^* B̃` as a
  `GradedQcohAlgebra`**, i.e. as an input to [Stacks, Tag 0897]'s base change.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackSection_preimage_smul`: over the whole preimage of an
  open, pulling a section back is semilinear along `f.app`.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.specSection_eval_top` and
  `exists_specSection_eval_top`: **a global section of `B̃ₖ` is exactly one named by a homogeneous
  element of degree `k`** — the comparison `Stacks.AffineBaseChange.toOpenₗ` is bijective over
  `⊤` (`AlgebraicGeometry.tilde.isIso_toOpen_top`). This is the description of the global
  sections of `B̃` that both the compatibility and the local surjectivity of `ψ` go through.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.isStructureCompatible_pullbackGradedQcoh`:
  **the compatibility.**

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open scoped DirectSum TensorProduct AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Over the whole preimage of an open, pulling a section back is semilinear** along the map of
sections `f.app U`: there the pullback of a section is the image of the section under the unit of
`f^* ⊣ f_*` (`Stacks.Conormal.pullbackSection_self`), and that unit is a morphism of
`𝒪_X`-modules. -/
public theorem pullbackSection_preimage_smul {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    (U : X.Opens) (r : X.ringCatSheaf.obj.obj (op U)) (a : F.val.obj (op U)) :
    pullbackSection f F U (f ⁻¹ᵁ U) le_rfl (r • a) =
      (show Y.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ U)) from
          (f.app U).hom r) •
        pullbackSection f F U (f ⁻¹ᵁ U) le_rfl a := by
  rw [Stacks.Conormal.pullbackSection_self f F U (r • a),
    Stacks.Conormal.pullbackSection_self f F U a]
  exact (((pullbackPushforwardAdjunction f).unit.app F).val.app (op U)).hom.map_smul r a

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.SpecGraded

variable {R : CommRingCat.{u}} {S : Type u} [CommRing S] [Algebra R S]
  (𝒢 : ℤ → Submodule R S) [SetLike.GradedMonoid 𝒢]

/-! ### The global sections of the sheaf of graded algebras on an affine base -/

/-- **The global section of `(𝒢 k)~` named by a homogeneous element of degree `k`** is the image
of that element under `Stacks.AffineBaseChange.toOpenₗ`: the comparison image of `1 ⊗ b`. -/
theorem homogeneousSection_eval_top {k : ℤ} (b : ↥(𝒢 k)) :
    (homogeneousSection 𝒢 b).eval (op (⊤ : (Spec R).Opens)) =
      Stacks.AffineBaseChange.toOpenₗ (pieceModule 𝒢 k) ⊤ b := by
  show Stacks.AffineBaseChange.toTildeₗ (pieceModule 𝒢 k) ⊤
      ((1 : Γ(Spec R, ⊤)) ⊗ₜ[R] b) = _
  refine Eq.trans (Stacks.AffineBaseChange.toTildeₗ_tmul (pieceModule 𝒢 k) ⊤ 1 b) ?_
  exact one_smul _ _

/-- **Every global section of `(𝒢 k)~` is named by a homogeneous element of degree `k`.** The
comparison `Stacks.AffineBaseChange.toOpenₗ` is an isomorphism over `⊤`
(`AlgebraicGeometry.tilde.isIso_toOpen_top`), the degree-`k` piece being the associated sheaf of
`𝒢 k`. -/
theorem exists_homogeneousSection_eval_top (k : ℤ)
    (y : ((specGradedAlgebra 𝒢).piece k).val.obj (op (⊤ : (Spec R).Opens))) :
    ∃ b : ↥(𝒢 k), (homogeneousSection 𝒢 b).eval (op (⊤ : (Spec R).Opens)) = y := by
  have : IsIso (AlgebraicGeometry.tilde.toOpen (pieceModule 𝒢 k) ⊤) :=
    AlgebraicGeometry.tilde.isIso_toOpen_top
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.tilde.toOpen (pieceModule 𝒢 k) ⊤)).2 y
  exact ⟨b, (homogeneousSection_eval_top 𝒢 b).trans hb⟩

/-- The restriction map of the structure sheaf of `Spec R` from `⊤` to `⊤` is the identity. -/
theorem presheaf_map_leTop_top (R : CommRingCat.{u}) :
    ((Spec R).presheaf.map (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op) = 𝟙 _ := by
  rw [show (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _]
  exact (Spec R).presheaf.map_id _

/-- **A scalar acts on the unit global function of `Spec R` as its image under
`Γ(Spec R, ⊤) ≅ R`.** -/
theorem smul_one_eq_ΓSpecIso_inv (R : CommRingCat.{u}) (a : ↥R) :
    a • (1 : Γ(Spec R, ⊤)) = (Scheme.ΓSpecIso R).inv.hom a := by
  have h1 : a • (1 : Γ(Spec R, ⊤)) = algebraMap ↥R Γ(Spec R, ⊤) a := by
    rw [Algebra.smul_def, mul_one]
  refine h1.trans ?_
  show ((Spec R).presheaf.map (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op).hom
      ((Scheme.ΓSpecIso R).inv.hom a) = _
  exact congrArg (fun φ : Γ(Spec R, ⊤) ⟶ Γ(Spec R, ⊤) =>
    φ.hom ((Scheme.ΓSpecIso R).inv.hom a)) (presheaf_map_leTop_top R)

/-- **The global section named by a scalar multiple of the unit is that scalar times the unit of
the algebra sheaf.** -/
theorem homogeneousSection_smul_gOne (a : ↥R) :
    (homogeneousSection 𝒢 (a • gOne 𝒢)).eval (op (⊤ : (Spec R).Opens)) =
      (show (Spec R).ringCatSheaf.obj.obj (op (⊤ : (Spec R).Opens)) from
          (Scheme.ΓSpecIso R).inv.hom a) •
        (specGradedAlgebra 𝒢).one.eval (op (⊤ : (Spec R).Opens)) := by
  have htens : ((1 : Γ(Spec R, ⊤)) ⊗ₜ[R] (a • gOne 𝒢)) =
      ((Scheme.ΓSpecIso R).inv.hom a) • ((1 : Γ(Spec R, ⊤)) ⊗ₜ[R] gOne 𝒢) := by
    refine Eq.trans (TensorProduct.smul_tmul a (1 : Γ(Spec R, ⊤)) (gOne 𝒢)).symm ?_
    refine Eq.trans (congrArg (fun c : Γ(Spec R, ⊤) => c ⊗ₜ[R] gOne 𝒢)
      (smul_one_eq_ΓSpecIso_inv R a)) ?_
    refine Eq.trans (congrArg (fun c : Γ(Spec R, ⊤) => c ⊗ₜ[R] gOne 𝒢)
      (show (Scheme.ΓSpecIso R).inv.hom a =
          (Scheme.ΓSpecIso R).inv.hom a • (1 : Γ(Spec R, ⊤)) from
        ((smul_eq_mul _ (1 : Γ(Spec R, ⊤))).trans (mul_one _)).symm)) ?_
    exact TensorProduct.smul_tmul' ((Scheme.ΓSpecIso R).inv.hom a) (1 : Γ(Spec R, ⊤)) (gOne 𝒢)
  show PresheafOfModules.Hom.app (pieceCmp 𝒢 0) (op (⊤ : (Spec R).Opens))
      ((1 : Γ(Spec R, ⊤)) ⊗ₜ[R] (a • gOne 𝒢)) = _
  refine Eq.trans (congrArg
    (fun z : (piecePresheaf 𝒢 0).obj (op (⊤ : (Spec R).Opens)) =>
      PresheafOfModules.Hom.app (pieceCmp 𝒢 0) (op (⊤ : (Spec R).Opens)) z) htens) ?_
  exact (PresheafOfModules.Hom.app (pieceCmp 𝒢 0) (op (⊤ : (Spec R).Opens))).hom.map_smul _ _

end Stacks.SpecGraded

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`𝓑 = f^* B̃` as a `GradedQcohAlgebra`**, i.e. in the form [Stacks, Tag 0897]'s base change
consumes: its homogeneous multiplication is commutative, it vanishes in negative degrees and its
pieces are quasi-coherent. -/
def pullbackGradedQcoh : GradedQcohAlgebra X where
  alg := pullbackGradedAlg 𝒜 f
  isCommutative := isCommutative_pullbackGradedAlg 𝒜 f
  isZero_of_neg := isZero_pullbackGradedAlg_piece_of_neg 𝒜 f
  isQuasicoherent_piece := isQuasicoherent_pullbackGradedAlg_piece 𝒜 f

/-- **The homogeneous pieces of `B̃` are quasi-coherent**, at the spelling
`Stacks.AlgebraicGeometry.GradedProperCohomology.specGradedAlg`: this is
`Stacks.SpecGraded.isQuasicoherent_specGradedAlgebra_piece`, registered so that instance search
finds it through that definition. -/
instance isQuasicoherent_specGradedAlg_piece (n : ℤ) :
    ((specGradedAlg 𝒜).piece n).IsQuasicoherent :=
  Stacks.SpecGraded.isQuasicoherent_specGradedAlgebra_piece (R := CommRingCat.of A) (S := B)
    (intExtend 𝒜) n

/-! ### The global sections of `B̃ₖ` -/

/-- **Every global section of `B̃ₖ` is named by a homogeneous element of degree `k`.** -/
theorem exists_specSection_eval_top (k : ℕ)
    (y : ((specGradedAlg 𝒜).piece (k : ℤ)).val.obj (op (⊤ : (Spec (.of A)).Opens))) :
    ∃ b : ↥(𝒜 k), (specSection 𝒜 b).eval (op (⊤ : (Spec (.of A)).Opens)) = y :=
  Stacks.SpecGraded.exists_homogeneousSection_eval_top (R := CommRingCat.of A) (S := B)
    (intExtend 𝒜) (k : ℤ) y

/-! ### The compatibility with the structure maps -/

/-- The degree-zero homogeneous element `a · 1` of `B` attached to a scalar `a : A`: the
submodule `𝒜₀` contains `1` and is an `A`-submodule. -/
def degZero (a : A) : ↥(𝒜 0) :=
  a • (GradedMonoid.GOne.one (A := fun n : ℕ => ↥(𝒜 n)))

/-- The element `degZero 𝒜 a`, viewed in `B`, is `algebraMap A B a`. -/
theorem degZero_coe (a : A) : ((degZero 𝒜 a : ↥(𝒜 0)) : B) = algebraMap A B a := by
  show a • ((GradedMonoid.GOne.one (A := fun n : ℕ => ↥(𝒜 n)) : ↥(𝒜 0)) : B) = _
  rw [show ((GradedMonoid.GOne.one (A := fun n : ℕ => ↥(𝒜 n)) : ↥(𝒜 0)) : B) = 1 from rfl,
    Algebra.algebraMap_eq_smul_one]

/-- **The global section of `B̃₀` named by `a · 1` is `a` times the unit of `B̃`.** -/
theorem specSection_degZero (a : A) :
    (specSection 𝒜 (degZero 𝒜 a)).eval (op (⊤ : (Spec (.of A)).Opens)) =
      (show (Spec (.of A)).ringCatSheaf.obj.obj (op (⊤ : (Spec (.of A)).Opens)) from
          (Scheme.ΓSpecIso (.of A)).inv.hom a) •
        (specGradedAlg 𝒜).one.eval (op (⊤ : (Spec (.of A)).Opens)) := by
  refine Eq.trans (congrArg (fun z : ↥(intExtend 𝒜 0) =>
    (Stacks.SpecGraded.homogeneousSection (R := CommRingCat.of A) (S := B) (intExtend 𝒜) z).eval
      (op (⊤ : (Spec (.of A)).Opens)))
    (show degZero 𝒜 a =
        a • Stacks.SpecGraded.gOne (R := CommRingCat.of A) (S := B) (intExtend 𝒜) from
      Subtype.ext rfl)) ?_
  exact Stacks.SpecGraded.homogeneousSection_smul_gOne (R := CommRingCat.of A) (S := B)
    (intExtend 𝒜) a

/-- **The compatibility of the base algebra map with the two structure maps, for `𝓑 = f^* B̃`.**
This is the hypothesis `hsc` of
`Stacks.AlgebraicGeometry.GradedProperCohomology.HomogeneousSections.baseAlgebraHom`. -/
theorem isStructureCompatible_pullbackGradedQcoh :
    HomogeneousSections.IsStructureCompatible (pullbackGradedQcoh 𝒜 f)
      (pullbackHomogeneousSections 𝒜 f) f := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  set a : A := (Scheme.ΓSpecIso (.of A)).hom.hom r with ha
  have hra : (Scheme.ΓSpecIso (.of A)).inv.hom a = r :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of A)) r
  have hB : (Scheme.ΓSpecIso (.of B)).hom.hom
      ((pushforwardAlgebra (algebraSpecToBase A B)).unitTop.hom r) = algebraMap A B a := by
    have hnat := congrArg (fun k : CommRingCat.of A ⟶ Γ(Spec (.of B), ⊤) => k.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
    refine Eq.trans (congrArg (Scheme.ΓSpecIso (.of B)).hom.hom
      (show (pushforwardAlgebra (algebraSpecToBase A B)).unitTop.hom r =
          (algebraSpecToBase A B).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a) from
        congrArg (algebraSpecToBase A B).appTop.hom hra.symm)) ?_
    refine Eq.trans (congrArg (Scheme.ΓSpecIso (.of B)).hom.hom hnat.symm) ?_
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of B)) _
  show HomogeneousSections.secRingHom (pullbackGradedQcoh 𝒜 f)
      (pullbackHomogeneousSections 𝒜 f) (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))
      ((Scheme.ΓSpecIso (.of B)).hom.hom
        ((pushforwardAlgebra (algebraSpecToBase A B)).unitTop.hom r)) = _
  rw [hB, ← degZero_coe 𝒜 a,
    HomogeneousSections.secRingHom_coe (pullbackGradedQcoh 𝒜 f)
      (pullbackHomogeneousSections 𝒜 f) (degZero 𝒜 a) _]
  show (pullbackGradedAlg 𝒜 f).ungradedIncl 0
      (((pullbackHomogeneousSections 𝒜 f).sec (degZero 𝒜 a)).eval
        (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))) = _
  have hsec : ((pullbackHomogeneousSections 𝒜 f).sec (degZero 𝒜 a)).eval
        (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))) =
      (show X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))) from
          (f.app ⊤).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) •
        (pullbackGradedAlg 𝒜 f).one.eval (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))) := by
    refine Eq.trans (pullbackSections_eval f ((specGradedAlg 𝒜).piece 0)
      (specSection 𝒜 (degZero 𝒜 a)) (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))) ?_
    refine Eq.trans (congrArg
      (Scheme.Modules.pullbackSection f ((specGradedAlg 𝒜).piece 0) ⊤
        (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)) le_rfl)
      (specSection_degZero 𝒜 a)) ?_
    refine Eq.trans (Scheme.Modules.pullbackSection_preimage_smul f
      ((specGradedAlg 𝒜).piece 0) ⊤ _ _) ?_
    exact congrArg (fun z => (show X.ringCatSheaf.obj.obj
        (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))) from
        (f.app ⊤).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) • z)
      (Stacks.Conormal.gradedPullback_one_eval f (specGradedAlg 𝒜) ⊤).symm
  rw [hsec, (pullbackGradedAlg 𝒜 f).ungradedIncl_smul_one]
  show (((pullbackGradedAlg 𝒜 f).ungradedStructureMap.hom.app
      (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))))).hom ((f.app ⊤).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom a)) = _
  rw [hra]
  rfl

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
