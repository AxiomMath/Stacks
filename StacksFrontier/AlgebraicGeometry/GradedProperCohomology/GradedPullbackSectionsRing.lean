module

public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSectionsRingSpec
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.AssociatedGradedSectionsRing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.BaseReesPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv

/-!
# `Γ(Spec k, j^*(⨁ₙ ℐⁿ)_*) ≅ Gr_I(R)`, the `ρ` of part (2) of [Stacks, Tag 0897]

Let `S` be an affine scheme, `ℐ` a quasi-coherent sheaf of ideals on it, and
`j : Spec k ⟶ S` the closed immersion cut out by `ℐ`. The pullback
`j^*(⨁ₙ ℐⁿ)` of the Rees algebra of `ℐ` is the associated graded algebra `⨁ₙ ℐⁿ/ℐⁿ⁺¹` read on
`Spec k`, and this file identifies the global sections of its ungraded realization with the
associated graded ring of `I = ℐ(S)`:

`Gr_I(Γ(S, ⊤)) ≃+* Γ(Spec k, j^*(⨁ₙ ℐⁿ)_*)`,

compatibly with the structure maps.

That pair is the `ρ` and `hρ` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections`
and of `exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`, whose graded algebra on
`Spec k` is exactly `Stacks.Conormal.gradedPullback j (Stacks.Blowup.reesGradedAlgebra ℐ)`. At
the fibre of [Stacks, Tag 0D2N] it is used with `S = Spec 𝒪_{Y,y}`, `I = 𝔪`, `k = κ(y)` and
`Gr_I(R) = Gr_𝔪(𝒪_{Y,y})`, Noetherian by `AssociatedGraded.isNoetherianRing_gradedRing`.

## Why this is not the conormal algebra's identification

`StacksFrontier/AlgebraicGeometry/Conormal/ConormalSectionsRingSpec.lean` identifies the same ring
with the sections of `Stacks.Conormal.conormalAlgebraSheaf (quotImmersion R I)`, the ungraded
realization of `Stacks.Conormal.conormalAlgebra`, which is the pullback of the Rees algebra of
`Stacks.Conormal.coborderIdeal` along `Scheme.Hom.liftCoborder` — a graded algebra on the
*coborder* of the immersion's range, not on `S`. Nothing identifies that with
`gradedPullback j (reesGradedAlgebra ℐ)`, and the engine asks for the latter. Both are handled
by the same machinery: the degreewise local presentation feeds
`Stacks.AssociatedGradedSections.pieceEquivOfLocalMap` and the degreewise identifications feed
`Stacks.AssociatedGradedSections.sectionsRingEquiv`. The only difference is which local
presentation is used — `Stacks.Conormal.coborderChartMap` there, `Stacks.Conormal.reesPullbackMap`
here — and `reesPullbackMap` is already stated for an arbitrary morphism and an arbitrary
affine chart, so nothing about it has to be redone.

## Main definitions

* `Stacks.Conormal.gradedPullbackPieceEquiv`: the degreewise identification
  `Iⁿ/Iⁿ⁺¹ ≃+ Γ(Spec k, j^*(ℐⁿ))`.
* `Stacks.Conormal.gradedPullbackSectionsRingEquiv`:
  **`Gr_I(Γ(S, ⊤)) ≃+* Γ(Spec k, j^*(⨁ₙ ℐⁿ)_*)`.**
* `Stacks.Conormal.specGradedPullbackSectionsRingEquiv`: **the same at `S = Spec R` and
  `j = Spec(R ⧸ I) ⟶ Spec R`, with the associated graded ring of `I ⊆ R` itself.** This is `ρ`.

## Main results

* `Stacks.Conormal.gradedPullbackSectionsRingEquiv_gradeZeroRingHom`: the identification carries
  the structure map of `Gr_I(Γ(S, ⊤))` to the structural ring map of the algebra sheaf.
* `Stacks.Conormal.specGradedPullbackSectionsRingEquiv_algebraMap`: **it carries
  `algebraMap (R ⧸ I) (Gr_I(R))` to the structure map of the algebra sheaf.** This is `hρ`.
* `Stacks.Conormal.ker_app_top_quotImmersion_eq_specIdealSheaf`: the hypothesis `hker` holds at
  `Stacks.Cohomology.FormalFunctions.specIdealSheaf`, the ideal sheaf on the base that
  [Stacks, Tag 0D2N] works with.

## Implementation notes

The ideal sheaf is a variable with the hypothesis that its ideal of sections over `⊤` is the
kernel of `Γ(S, ⊤) ⟶ Γ(Spec k, ⊤)`, rather than being taken to be `j.ker`: the consumer's ideal
sheaf at [Stacks, Tag 0D2N] is
`Stacks.Cohomology.FormalFunctions.specIdealSheaf`, a `Scheme.IdealSheafData.ofIdealTop`, and
only its ideal over `⊤` is pinned. That hypothesis is exactly `hker` of
`Stacks.Conormal.reesPullbackMap_eq_zero_iff`, and it is the defining relation between `j` and
`ℐ`, not a missing prerequisite.

`j ⁻¹ᵁ ⊤` is `⊤` by `rfl`, so the affineness of the chart's preimage is
`isAffineOpen_top (Spec (CommRingCat.of k))` and the conclusion may be read at `⊤` with no
transport.

The commutativity datum of the homogeneous multiplication is an argument rather than being
produced here, so that the consumer can pass the spelling the engine's statement uses,
`Stacks.AssociatedGradedFibre.associatedGradedAlgebra_mul_comm`. Definitional proof irrelevance
makes any other proof of it do as well.

No `@[stacks]` attribute is attached: this is one input of part (2) of [Stacks, Tag 0897] at
the fibre and not the assertion of a numbered result.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec
open Stacks.ClosedImmersion.AffineConormal Stacks.ClosedImmersion.IdealSheafAffine
open scoped DirectSum

universe u

namespace Stacks.Conormal

/-! ### The degreewise identification -/

section Affine

variable {S : Scheme.{u}} [IsAffine S] (I : S.IdealSheafData) {k : Type u} [CommRing k]
  (j : Spec (CommRingCat.of k) ⟶ S)
  (hsurj : Function.Surjective ((j.app (⊤ : S.Opens)).hom))
  (hker : RingHom.ker ((j.app (⊤ : S.Opens)).hom) = I.ideal ⟨⊤, isAffineOpen_top S⟩)

include hsurj hker in
/-- **The degreewise identification `Iⁿ/Iⁿ⁺¹ ≃+ Γ(Spec k, j^*(ℐⁿ))`.**

`Stacks.AssociatedGradedSections.pieceEquivOfLocalMap` at the local presentation
`Stacks.Conormal.reesPullbackMap` of the pullback of the Rees algebra: it is surjective and
kills exactly `Iⁿ⁺¹` because `j` surjects on functions with kernel `I`
(`reesPullbackMap_surjective` and `reesPullbackMap_eq_zero_iff`), and it is linear over the map
on functions (`reesPullbackMap_smul`). -/
def gradedPullbackPieceEquiv (n : ℕ) :
    AssociatedGraded.piece (M := Γ(S, ⊤)) (I.ideal ⟨⊤, isAffineOpen_top S⟩) n ≃+
      ((gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)).piece (n : ℤ)).val.obj
        (op (j ⁻¹ᵁ (⊤ : S.Opens))) :=
  Stacks.AssociatedGradedSections.pieceEquivOfLocalMap
    (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
    (I.ideal ⟨⊤, isAffineOpen_top S⟩) (j.app (⊤ : S.Opens)).hom
    (fun m => reesPullbackMap I j m ⟨⊤, isAffineOpen_top S⟩)
    (fun m a => reesPullbackMap_eq_zero_iff I j m ⟨⊤, isAffineOpen_top S⟩
      (isAffineOpen_top (Spec (CommRingCat.of k))) hker hsurj a)
    (fun m => reesPullbackMap_surjective I j m ⟨⊤, isAffineOpen_top S⟩
      (isAffineOpen_top (Spec (CommRingCat.of k))) hsurj)
    (fun m r a b hb => by
      have hba : b = r • a := Subtype.ext (by simpa using hb)
      subst hba
      exact reesPullbackMap_smul I j m ⟨⊤, isAffineOpen_top S⟩ r a) n

include hsurj hker in
/-- The degreewise identification sends the class of a representative to its local section. -/
theorem gradedPullbackPieceEquiv_mk (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(S, ⊤)) (I.ideal ⟨⊤, isAffineOpen_top S⟩) n) :
    gradedPullbackPieceEquiv I j hsurj hker n
        (AssociatedGraded.mk (I.ideal ⟨⊤, isAffineOpen_top S⟩) n a) =
      reesPullbackMap I j n ⟨⊤, isAffineOpen_top S⟩
        ⟨(a : Γ(S, ⊤)), by simpa using a.property⟩ :=
  rfl

include hsurj hker in
/-- The degreewise identification carries the graded unit to the graded unit. -/
theorem gradedPullbackPieceEquiv_one :
    gradedPullbackPieceEquiv I j hsurj hker 0
        (GradedMonoid.GOne.one :
          AssociatedGraded.piece (M := Γ(S, ⊤)) (I.ideal ⟨⊤, isAffineOpen_top S⟩) 0) =
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)).one.eval
        (op (j ⁻¹ᵁ (⊤ : S.Opens))) :=
  (gradedPullbackPieceEquiv_mk I j hsurj hker 0 ⟨1, by simp [AssociatedGraded.power]⟩).trans
    (reesPullbackMap_one I j ⟨⊤, isAffineOpen_top S⟩ ⟨1, by simp⟩ rfl)

include hsurj hker in
/-- The degreewise identification carries graded products to the homogeneous multiplication. -/
theorem gradedPullbackPieceEquiv_mul (n m : ℕ)
    (a : AssociatedGraded.piece (M := Γ(S, ⊤)) (I.ideal ⟨⊤, isAffineOpen_top S⟩) n)
    (b : AssociatedGraded.piece (M := Γ(S, ⊤)) (I.ideal ⟨⊤, isAffineOpen_top S⟩) m) :
    gradedPullbackPieceEquiv I j hsurj hker (n + m)
        (AssociatedGraded.homogeneousSMul (I.ideal ⟨⊤, isAffineOpen_top S⟩) a b) =
      ((gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)).mul (n : ℤ) (m : ℤ)).app
        (op (j ⁻¹ᵁ (⊤ : S.Opens))) (gradedPullbackPieceEquiv I j hsurj hker n a)
        (gradedPullbackPieceEquiv I j hsurj hker m b) := by
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      exact reesPullbackMap_mul I j n m ⟨⊤, isAffineOpen_top S⟩
        ⟨(a : Γ(S, ⊤)), by simpa using a.property⟩
        ⟨(b : Γ(S, ⊤)), by simpa using b.property⟩
        ⟨(a : Γ(S, ⊤)) * (b : Γ(S, ⊤)), by
          rw [pow_add]
          exact Ideal.mul_mem_mul (by simpa using a.property) (by simpa using b.property)⟩ rfl

include hsurj hker in
/-- The degreewise identification is linear over the map on functions. -/
theorem gradedPullbackPieceEquiv_smul (n : ℕ) (r : Γ(S, ⊤))
    (a : AssociatedGraded.piece (M := Γ(S, ⊤)) (I.ideal ⟨⊤, isAffineOpen_top S⟩) n) :
    gradedPullbackPieceEquiv I j hsurj hker n (r • a) =
      (show (Spec (CommRingCat.of k)).ringCatSheaf.obj.obj (op (j ⁻¹ᵁ (⊤ : S.Opens))) from
          (j.app (⊤ : S.Opens)).hom r) •
        gradedPullbackPieceEquiv I j hsurj hker n a := by
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    exact reesPullbackMap_smul I j n ⟨⊤, isAffineOpen_top S⟩ r
      ⟨(a : Γ(S, ⊤)), by simpa using a.property⟩

/-! ### The ring isomorphism -/

variable
  (hc : ∀ (p q : ℤ) (W : (Opens ↥(Spec (CommRingCat.of k)))ᵒᵖ)
    (x : ((gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)).piece p).val.obj W)
    (y : ((gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)).piece q).val.obj W),
    HEq (((gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)).mul p q).app W x y)
      (((gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)).mul q p).app W y x))

include hsurj hker in
/-- **`Gr_I(Γ(S, ⊤)) ≃+* Γ(Spec k, j^*(⨁ₙ ℐⁿ)_*)`.**

`Stacks.AssociatedGradedSections.sectionsRingEquiv` at the degreewise identification
`Stacks.Conormal.gradedPullbackPieceEquiv`; the pullback of the Rees algebra vanishes in
negative degrees by `Stacks.Conormal.gradedPullback_negative_isZero` and
`Stacks.Blowup.reesPiece_negative_isZero`, and `Spec k` is affine. -/
def gradedPullbackSectionsRingEquiv :
    AssociatedGraded.gradedRing (I.ideal ⟨⊤, isAffineOpen_top S⟩) ≃+*
      ↥(AlgebraSheaf.sections
        (gradedAlgebraSheaf (Spec (CommRingCat.of k))
          (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)) hc) ⊤) :=
  Stacks.AssociatedGradedSections.sectionsRingEquiv
    (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)) hc
    (I.ideal ⟨⊤, isAffineOpen_top S⟩) (gradedPullbackPieceEquiv I j hsurj hker)
    (gradedPullbackPieceEquiv_one I j hsurj hker)
    (gradedPullbackPieceEquiv_mul I j hsurj hker)
    (gradedPullback_negative_isZero j (Stacks.Blowup.reesGradedAlgebra I)
      (Stacks.Blowup.reesPiece_negative_isZero I))
    (isAffineOpen_top (Spec (CommRingCat.of k)))

include hsurj hker in
/-- **The identification carries the structure map of `Gr_I(Γ(S, ⊤))` to the structural ring map
of the algebra sheaf**, composed with `Γ(S, ⊤) ⟶ Γ(Spec k, ⊤)`. -/
theorem gradedPullbackSectionsRingEquiv_gradeZeroRingHom (r : Γ(S, ⊤)) :
    gradedPullbackSectionsRingEquiv I j hsurj hker hc
        (AssociatedGraded.gradeZeroRingHom (I.ideal ⟨⊤, isAffineOpen_top S⟩) r) =
      ((gradedAlgebraSheaf (Spec (CommRingCat.of k))
          (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)) hc).hom.hom.app
        (op (j ⁻¹ᵁ (⊤ : S.Opens)))).hom ((j.app (⊤ : S.Opens)).hom r) :=
  Stacks.AssociatedGradedSections.sectionsRingEquiv_gradeZeroRingHom
    (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I)) hc
    (I.ideal ⟨⊤, isAffineOpen_top S⟩) (j.app (⊤ : S.Opens)).hom
    (gradedPullbackPieceEquiv I j hsurj hker)
    (gradedPullbackPieceEquiv_one I j hsurj hker)
    (gradedPullbackPieceEquiv_mul I j hsurj hker)
    (gradedPullback_negative_isZero j (Stacks.Blowup.reesGradedAlgebra I)
      (Stacks.Blowup.reesPiece_negative_isZero I))
    (isAffineOpen_top (Spec (CommRingCat.of k)))
    (gradedPullbackPieceEquiv_smul I j hsurj hker) r

end Affine

/-! ### At `Spec(R ⧸ I) ⟶ Spec R`: the `ρ` and `hρ` the engine takes -/

section Spec

variable (R : CommRingCat.{u}) (I₀ : Ideal ↥R) (I : (Spec R).IdealSheafData)
  (hker : RingHom.ker (((quotImmersion R I₀).app (⊤ : (Spec R).Opens)).hom) =
    I.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩)

/-- The map on global sections of `Spec(R ⧸ I) ⟶ Spec R` is surjective, the quotient map being
so. -/
theorem surjective_app_top_quotImmersion :
    Function.Surjective (((quotImmersion R I₀).app (⊤ : (Spec R).Opens)).hom) :=
  (quotImmersion R I₀).app_surjective ⊤ (isAffineOpen_top (Spec R))

include hker in
/-- The ideal of sections of `ℐ` over `⊤`, transported along `Γ(Spec R, ⊤) ≅ R`, is `I`. -/
theorem map_ideal_top_eq :
    Ideal.map ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv : ↥Γ(Spec R, ⊤) →+* ↥R)
        (I.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩) = I₀ :=
  hker ▸ map_chartIdeal_quotImmersion R I₀

variable
  (hc : ∀ (p q : ℤ) (W : (Opens ↥(Spec (quotRing I₀)))ᵒᵖ)
    (x : ((gradedPullback (quotImmersion R I₀)
      (Stacks.Blowup.reesGradedAlgebra I)).piece p).val.obj W)
    (y : ((gradedPullback (quotImmersion R I₀)
      (Stacks.Blowup.reesGradedAlgebra I)).piece q).val.obj W),
    HEq (((gradedPullback (quotImmersion R I₀)
        (Stacks.Blowup.reesGradedAlgebra I)).mul p q).app W x y)
      (((gradedPullback (quotImmersion R I₀)
        (Stacks.Blowup.reesGradedAlgebra I)).mul q p).app W y x))

include hker in
/-- **`Gr_I(R) ≃+* Γ(Spec(R ⧸ I), (j^*(⨁ₙ ℐⁿ))_*)`** for `j : Spec(R ⧸ I) ⟶ Spec R` the closed
immersion cut out by `ℐ`.

`Stacks.Conormal.gradedPullbackSectionsRingEquiv` with the associated graded ring of the ideal
of sections moved to that of `I` along `Γ(Spec R, ⊤) ≅ R` by
`AssociatedGraded.congrRingEquiv`. **This is the `ρ` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`.** -/
def specGradedPullbackSectionsRingEquiv :
    AssociatedGraded.gradedRing I₀ ≃+*
      ↥(AlgebraSheaf.sections
        (gradedAlgebraSheaf (Spec (quotRing I₀))
          (gradedPullback (quotImmersion R I₀) (Stacks.Blowup.reesGradedAlgebra I)) hc) ⊤) :=
  (AssociatedGraded.congrRingEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
      (map_ideal_top_eq R I₀ I hker)).symm.trans
    (gradedPullbackSectionsRingEquiv I (quotImmersion R I₀)
      (surjective_app_top_quotImmersion R I₀) hker hc)

include hker in
/-- **The identification carries `algebraMap (R ⧸ I) (Gr_I(R))` to the structure map of the
algebra sheaf.** Together with `Stacks.Conormal.specGradedPullbackSectionsRingEquiv` this is the
pair `ρ`, `hρ` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`.

The `R ⧸ I`-algebra structure of `Gr_I(R)` is `AssociatedGraded.algebraQuotient`: on the class of
`a : R` the structure map is the degree-zero class of `a`
(`AssociatedGraded.algebraMap_quotient_mk`), which
`Stacks.Conormal.gradedPullbackSectionsRingEquiv_gradeZeroRingHom` carries to the structural ring
map of the algebra sheaf applied to the image of `a` in `Γ(Spec(R ⧸ I), ⊤)`
(`Stacks.Conormal.appTop_quotImmersion_specTopEquiv`). -/
theorem specGradedPullbackSectionsRingEquiv_algebraMap (c : ↥(quotRing I₀)) :
    specGradedPullbackSectionsRingEquiv R I₀ I hker hc
        (algebraMap (↥R ⧸ I₀) (AssociatedGraded.gradedRing I₀) c) =
      (gradedAlgebraSheaf (Spec (quotRing I₀))
          (gradedPullback (quotImmersion R I₀)
            (Stacks.Blowup.reesGradedAlgebra I)) hc).unitTop.hom
        ((Scheme.ΓSpecIso (quotRing I₀)).symm.commRingCatIsoToRingEquiv c) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I₀) c
  have hsymm : (AssociatedGraded.congrRingEquiv
        (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
        (map_ideal_top_eq R I₀ I hker)).symm
      (AssociatedGraded.gradeZeroRingHom I₀ a) =
      AssociatedGraded.gradeZeroRingHom (I.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩)
        ((Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv a) := by
    have hs : (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv =
        (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm := rfl
    refine (RingEquiv.symm_apply_eq _).2 ?_
    rw [AssociatedGraded.congrRingEquiv_gradeZeroRingHom, hs, RingEquiv.apply_symm_apply]
  change gradedPullbackSectionsRingEquiv I (quotImmersion R I₀)
      (surjective_app_top_quotImmersion R I₀) hker hc
      ((AssociatedGraded.congrRingEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
        (map_ideal_top_eq R I₀ I hker)).symm
          (algebraMap (↥R ⧸ I₀) (AssociatedGraded.gradedRing I₀)
            (Ideal.Quotient.mk I₀ a))) = _
  rw [AssociatedGraded.algebraMap_quotient_mk, hsymm,
    gradedPullbackSectionsRingEquiv_gradeZeroRingHom]
  exact congrArg
    (fun z => ((gradedAlgebraSheaf (Spec (quotRing I₀))
      (gradedPullback (quotImmersion R I₀)
        (Stacks.Blowup.reesGradedAlgebra I)) hc).hom.hom.app (op ⊤)).hom z)
    (appTop_quotImmersion_specTopEquiv R I₀ a)

end Spec

/-! ### The hypothesis at the ideal sheaf [Stacks, Tag 0D2N] uses -/

/-- **The hypothesis `hker` holds at `Stacks.Cohomology.FormalFunctions.specIdealSheaf`**, the
quasi-coherent ideal sheaf on `Spec A` generated by an ideal `𝔪 ⊆ A`, which is the ideal sheaf
on the base that [Stacks, Tag 0D2N] works with: its ideal of sections over `⊤` is the kernel of
the map on global sections of `Spec(A ⧸ 𝔪) ⟶ Spec A`.

`Stacks.Conormal.map_chartIdeal_quotImmersion` computes that kernel, transported along
`Γ(Spec A, ⊤) ≅ A`, to be `𝔪`; transporting back is
`Stacks.Divisors.ideal_ofIdealTop_top` together with `Ideal.map_map` and the fact that
`Γ(Spec A, ⊤) ≅ A` is an isomorphism. -/
theorem ker_app_top_quotImmersion_eq_specIdealSheaf {A : Type u} [CommRing A] (𝔪 : Ideal A) :
    RingHom.ker (((quotImmersion (CommRingCat.of A) 𝔪).app
        (⊤ : (Spec (CommRingCat.of A)).Opens)).hom) =
      (Stacks.Cohomology.FormalFunctions.specIdealSheaf 𝔪).ideal
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ := by
  have h : Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv :
        ↥Γ(Spec (CommRingCat.of A), ⊤) →+* A)
      (chartIdeal (quotImmersion (CommRingCat.of A) 𝔪)
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩) = 𝔪 :=
    map_chartIdeal_quotImmersion (CommRingCat.of A) 𝔪
  have hid : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom.comp
      (((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv :
        ↥Γ(Spec (CommRingCat.of A), ⊤) →+* A)) =
      RingHom.id ↥Γ(Spec (CommRingCat.of A), ⊤) := by
    rw [show (((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv :
        ↥Γ(Spec (CommRingCat.of A), ⊤) →+* A)) =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom from rfl,
      ← CommRingCat.hom_comp, (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id]
    rfl
  rw [Stacks.Divisors.ideal_ofIdealTop_top]
  conv_rhs => rw [← h]
  rw [Ideal.map_map, hid, Ideal.map_id]

end Stacks.Conormal

end
