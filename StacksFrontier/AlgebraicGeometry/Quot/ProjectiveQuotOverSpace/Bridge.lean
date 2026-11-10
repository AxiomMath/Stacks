/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Hilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.IsoReading

/-!
# The quotients of `Quot_{F/X/B}(T)` read on `ℙⁿ_T`

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame `X = B × ℙⁿ_ℤ`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.ProjectiveFrame`), and `T` a test scheme over `B`.
The base change `X_T` is the algebraic space of `ℙⁿ_T`, and the reading
`AlgebraicGeometry.ProjectiveQuotOverSpace.reading` of modules on `X_T` on the scheme `ℙⁿ_T` is an
equivalence on quasi-coherent modules (Stacks 03DX).  So the members of `Quot_{F/X/B}(T)` of
Stacks 09TR — quotients of `F_T` that are quasi-coherent, of finite presentation, flat over `T`
and with support proper over `T` — correspond to the quotients of the reading of `F_T` on `ℙⁿ_T`
that are of finite presentation and flat over `T`; the proper-support condition is automatic,
`X_T ⟶ T` being proper as a base change of `ℙⁿ_ℤ ⟶ Spec ℤ`.  The quotient of the reading is the
reading of the quotient, and the same correspondence matches `Quot^P_{F/X/B}(T)` with the
quotients whose fibres have Hilbert polynomial `P`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.readingSubobject`: the submodule of the reading of
  `F_T` corresponding to a submodule of `F_T`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.properlySupportedQuotientsEquiv`: the
  correspondence for `Quot_{F/X/B}(T)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.hilbertQuotientsEquiv`: the correspondence for
  `Quot^P_{F/X/B}(T)`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.mem_properlySupportedQuotients_iff`: the conditions
  of Stacks 09TR are finite presentation and flatness of the quotient read on `ℙⁿ_T`.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The ambient-universe abelian structure of site modules cannot describe the `𝒪_{X_T}`-modules
-- here, whose sections live in the universe of the schemes; left in place it is selected ahead
-- of `SheafOfModules.instAbelian` and leaves the module universe of every subobject unsolved (as
-- in `StacksFrontier/AlgebraicGeometry/Quot/ProjectiveQuot/SiteBridge.lean`).
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase}
  (E : ProjectiveFrame B n D)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### Proper support is automatic -/

include E in
/-- The projection `X_T ⟶ T` is proper, being a base change of `ℙⁿ_ℤ ⟶ Spec ℤ`. -/
theorem isProper_projection (T : Space.SchemesOver D.Y) :
    Space.IsProper B integerBase B.contains_integerBase (D.projection T).hom := by
  have hf : Space.IsProper B integerBase B.contains_integerBase (quotSituation B n 0).f.hom :=
    (Space.isProper_yoneda_map_iff B integerBase B.contains_integerBase _).2
      (inferInstanceAs (IsProper (projectiveSpaceOver n integerBase ↘ integerBase)))
  exact (Space.isProper_isStableUnderBaseChange B integerBase B.contains_integerBase).of_isPullback
    (isPullback_space E T) hf

include E in
/-- **Every quotient of finite presentation has support proper over the test scheme**: the
support is closed (Stacks 07TZ) and `X_T ⟶ T` is proper. -/
theorem isProperlySupportedOver_of_isFinitePresentationOnSite (T : Space.SchemesOver D.Y)
    (G : Space.Modules.{u, u} B integerBase B.contains_integerBase (D.space T).1 (D.space T).2)
    [G.IsFinitePresentationOnSite] : D.IsProperlySupportedOver T G := by
  have hcl := Space.isClosed_supportOfSheaf_of_isFiniteTypeOnSite B integerBase
    B.contains_integerBase (D.space T).1 (D.space T).2 G
  exact ⟨hcl, Space.isProperOver_of_isProper B integerBase B.contains_integerBase _ _ _ _
    (isProper_projection E T) _ hcl⟩

/-! ### The objectwise correspondence -/

section TestScheme

variable (T : Space.SchemesOver D.Y)

/-- The reading on `ℙⁿ_T` is the reading along `h_{ℙⁿ_T} ≅ X_T`. -/
theorem reading_eq_isoReading : reading E T = isoReading (spaceIso E T) :=
  rfl

omit E in
/-- `F_T` is quasi-coherent. -/
theorem isQuasicoherentOnSite_baseChangeModule :
    (D.baseChangeModule T).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase _ _ D.quasicoherent

/-- **The submodule of the reading of `F_T` corresponding to a submodule `K` of `F_T`**: the
kernel of the reading of `F_T ⟶ F_T / K`. -/
def readingSubobject (K : Subobject (D.baseChangeModule T)) :
    Subobject ((reading E T).obj (D.baseChangeModule T)) :=
  kernelSubobject ((reading E T).map (cokernel.π K.arrow))

/-- The reading of the projection onto a quasi-coherent quotient is an epimorphism. -/
theorem epi_reading_map_cokernel_π (K : Subobject (D.baseChangeModule T))
    (hK : (D.quotientModule T K).IsQuasicoherentOnSite) :
    Epi ((reading E T).map (cokernel.π K.arrow)) := by
  have h := (quotientCorrespondence_isoReadingAdjunction (spaceIso E T)).epi_rightProjection
    (isQuasicoherentOnSite_baseChangeModule T) (Iso.refl _) K hK
  rwa [Adjunction.QuotientCorrespondence.rightProjection, Iso.refl_hom, Category.id_comp] at h

/-- **The quotient of the reading of `F_T` by the corresponding submodule is the reading of the
quotient** `F_T / K`, for a quasi-coherent quotient. -/
def readingSubobjectCokernelIso (K : Subobject (D.baseChangeModule T))
    (hK : (D.quotientModule T K).IsQuasicoherentOnSite) :
    cokernel (readingSubobject E T K).arrow ≅ (reading E T).obj (D.quotientModule T K) :=
  haveI := epi_reading_map_cokernel_π E T K hK
  Abelian.cokernelKernelSubobjectIso ((reading E T).map (cokernel.π K.arrow))

/-- The projection onto the quotient by the corresponding submodule is the reading of the
projection `F_T ⟶ F_T / K`, through `readingSubobjectCokernelIso`. -/
@[reassoc]
theorem cokernel_π_comp_readingSubobjectCokernelIso_hom (K : Subobject (D.baseChangeModule T))
    (hK : (D.quotientModule T K).IsQuasicoherentOnSite) :
    cokernel.π (readingSubobject E T K).arrow ≫ (readingSubobjectCokernelIso E T K hK).hom =
      (reading E T).map (cokernel.π K.arrow) := by
  have := epi_reading_map_cokernel_π E T K hK
  dsimp only [readingSubobjectCokernelIso, readingSubobject]
  rw [← Abelian.cokernelKernelSubobjectIso_inv_comp ((reading E T).map (cokernel.π K.arrow))]
  simp

/-- **The quasi-coherent quotients of `F_T` and of its reading on `ℙⁿ_T` correspond.** -/
def qcohQuotientEquiv :
    {K : Subobject (D.baseChangeModule T) // (cokernel K.arrow).IsQuasicoherentOnSite} ≃
      {K' : Subobject ((reading E T).obj (D.baseChangeModule T)) //
        SheafOfModules.IsQuasicoherent (cokernel K'.arrow)} :=
  haveI := isIso_isoReadingAdjunction_counit_app (spaceIso E T) _
    (isQuasicoherentOnSite_baseChangeModule T)
  (quotientCorrespondence_isoReadingAdjunction (spaceIso E T)).subobjectEquiv
    (isQuasicoherentOnSite_baseChangeModule T) (Iso.refl _)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through the `Subobject` and `cokernel` API on sheaves of modules is deep
/-- The correspondence `qcohQuotientEquiv` sends a submodule `K` of `F_T` to
`readingSubobject E T K`. -/
theorem qcohQuotientEquiv_apply_coe
    (K : {K : Subobject (D.baseChangeModule T) // (cokernel K.arrow).IsQuasicoherentOnSite}) :
    (qcohQuotientEquiv E T K).1 = readingSubobject E T K.1 := by
  change kernelSubobject _ = kernelSubobject _
  congr 1

/-- **The conditions of Stacks 09TR are read on `ℙⁿ_T`.**  For a submodule `K` of `F_T` with
quasi-coherent quotient, the quotient is of finite presentation, flat over `T` and with support
proper over `T` exactly when the corresponding quotient of the reading of `F_T` on `ℙⁿ_T` is of
finite presentation and flat over `T`. -/
theorem mem_properlySupportedQuotients_iff (K : Subobject (D.baseChangeModule T))
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ D.properlySupportedQuotients T ↔
      IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel (readingSubobject E T K).arrow) := by
  let e := readingSubobjectCokernelIso E T K hK
  have hfp : SheafOfModules.IsFinitePresentationOnSite (cokernel K.arrow) ↔
      (cokernel (readingSubobject E T K).arrow).IsFinitePresentation :=
    (isFinitePresentationOnSite_iff_isoReading (spaceIso E T) _ hK).trans
      ⟨fun h => SheafOfModules.IsFinitePresentation.of_iso h e.symm,
        fun h => SheafOfModules.IsFinitePresentation.of_iso h e⟩
  have hfl : Space.IsFlatOver B integerBase B.contains_integerBase (D.space T).2
        (D.projection T).hom (cokernel K.arrow) ↔
      AlgebraicGeometry.IsFlatOver
        (projectiveSpaceOver n ((𝒯).obj T.left) ↘ (𝒯).obj T.left).toLRSHom.toShHom
        (cokernel (readingSubobject E T K).arrow) :=
    (isFlatOver_iff_isoReading (spaceIso E T) (D.projection T) (projectiveSiteStructure B n T.left)
      (spaceIso_hom_projection E T) _ hK).trans
      (forall_congr' fun x => (flatOverAt_iff_of_iso _ e x).symm)
  constructor
  · rintro ⟨⟨⟨_, hflat⟩, hfp'⟩, _⟩
    exact ⟨hfp.1 hfp', hfl.1 hflat⟩
  · rintro ⟨hfp', hflat⟩
    have h := hfp.2 hfp'
    exact ⟨⟨⟨hK, hfl.2 hflat⟩, h⟩, isProperlySupportedOver_of_isFinitePresentationOnSite E T _⟩

/-- **The Hilbert polynomial condition is read on the corresponding quotient.** -/
theorem mem_hilbertQuotients_iff (P : Polynomial ℚ) (K : Subobject (D.baseChangeModule T))
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ hilbertQuotients E P T ↔
      IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel (readingSubobject E T K).arrow) ∧
        HasFibreHilbertPolynomial (n := n) (T := (𝒯).obj T.left) P
          (cokernel (readingSubobject E T K).arrow) := by
  let e := readingSubobjectCokernelIso E T K hK
  constructor
  · rintro ⟨hm, hP⟩
    exact ⟨(mem_properlySupportedQuotients_iff E T K hK).1 hm, hasFibreHilbertPolynomial_of_iso
      (isFinitePresentation_reading E T _ hK hm.1.2) e.symm hP⟩
  · rintro ⟨hfl, hP⟩
    exact ⟨(mem_properlySupportedQuotients_iff E T K hK).2 hfl,
      hasFibreHilbertPolynomial_of_iso hfl.1 e hP⟩

/-- A flat family is quasi-coherent, being of finite presentation. -/
theorem isQuasicoherent_of_isFlatFamily {G : (projectiveSpaceOver n ((𝒯).obj T.left)).Modules}
    (h : IsFlatFamily G) : SheafOfModules.IsQuasicoherent G :=
  have : G.IsFinitePresentation := h.1
  Stacks.Modules.isQuasicoherent_of_isFinitePresentation G

/-- The correspondence `qcohQuotientEquiv`, cut down to two conditions which match along it. -/
def qcohQuotientEquivRestrict (S : Set (Subobject (D.baseChangeModule T)))
    (S' : Set (Subobject ((reading E T).obj (D.baseChangeModule T))))
    (hS : ∀ K ∈ S, (cokernel K.arrow).IsQuasicoherentOnSite)
    (hS' : ∀ K' ∈ S', SheafOfModules.IsQuasicoherent (cokernel K'.arrow))
    (h : ∀ K, (cokernel K.arrow).IsQuasicoherentOnSite →
      (K ∈ S ↔ readingSubobject E T K ∈ S')) : S ≃ S' where
  toFun K := ⟨readingSubobject E T K.1, (h K.1 (hS _ K.2)).1 K.2⟩
  invFun K' := ⟨((qcohQuotientEquiv E T).symm ⟨K'.1, hS' _ K'.2⟩).1, by
    set K := (qcohQuotientEquiv E T).symm ⟨K'.1, hS' _ K'.2⟩
    have hK : readingSubobject E T K.1 = K'.1 :=
      (qcohQuotientEquiv_apply_coe E T K).symm.trans
        (congrArg Subtype.val ((qcohQuotientEquiv E T).apply_symm_apply _))
    exact (h K.1 K.2).2 ((congrArg (· ∈ S') hK).mpr K'.2)⟩
  left_inv K := Subtype.ext (by
    have h1 := congrArg Subtype.val ((qcohQuotientEquiv E T).symm_apply_apply ⟨K.1, hS _ K.2⟩)
    have h2 : qcohQuotientEquiv E T ⟨K.1, hS _ K.2⟩ =
        ⟨readingSubobject E T K.1, hS' _ ((h K.1 (hS _ K.2)).1 K.2)⟩ :=
      Subtype.ext (qcohQuotientEquiv_apply_coe E T _)
    rwa [h2] at h1)
  right_inv K' := Subtype.ext (by
    have h1 := congrArg Subtype.val ((qcohQuotientEquiv E T).apply_symm_apply ⟨K'.1, hS' _ K'.2⟩)
    rwa [qcohQuotientEquiv_apply_coe] at h1)

/-- **`Quot_{F/X/B}(T)` of Stacks 09TR is read on `ℙⁿ_T`**: its members correspond to the
quotients of the reading of `F_T` that are of finite presentation and flat over `T`. -/
def properlySupportedQuotientsEquiv :
    D.properlySupportedQuotients T ≃
      {K : Subobject ((reading E T).obj (D.baseChangeModule T)) //
        IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel K.arrow)} :=
  qcohQuotientEquivRestrict E T _ {K | IsFlatFamily (n := n) (T := (𝒯).obj T.left)
      (cokernel K.arrow)}
    (fun _ hK => hK.1.1.1) (fun _ hK' => isQuasicoherent_of_isFlatFamily T hK')
    (fun K hK => mem_properlySupportedQuotients_iff E T K hK)

/-- The correspondence `properlySupportedQuotientsEquiv` sends a submodule `K` of `F_T` to
`readingSubobject E T K`. -/
theorem properlySupportedQuotientsEquiv_apply_coe (K : D.properlySupportedQuotients T) :
    (properlySupportedQuotientsEquiv E T K).1 = readingSubobject E T K.1 :=
  rfl

/-- **`Quot^P_{F/X/B}(T)` is read on `ℙⁿ_T`**: its members correspond to the quotients of the
reading of `F_T` that are of finite presentation, flat over `T` and whose fibres have Hilbert
polynomial `P`. -/
def hilbertQuotientsEquiv (P : Polynomial ℚ) :
    hilbertQuotients E P T ≃
      {K : Subobject ((reading E T).obj (D.baseChangeModule T)) //
        IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel K.arrow) ∧
          HasFibreHilbertPolynomial (n := n) (T := (𝒯).obj T.left) P (cokernel K.arrow)} :=
  qcohQuotientEquivRestrict E T _ {K | IsFlatFamily (n := n) (T := (𝒯).obj T.left)
      (cokernel K.arrow) ∧ HasFibreHilbertPolynomial (n := n) (T := (𝒯).obj T.left) P
        (cokernel K.arrow)}
    (fun _ hK => hK.1.1.1.1) (fun _ hK' => isQuasicoherent_of_isFlatFamily T hK'.1)
    (fun K hK => mem_hilbertQuotients_iff E T P K hK)

/-- The correspondence `hilbertQuotientsEquiv` sends a submodule `K` of `F_T` to
`readingSubobject E T K`. -/
theorem hilbertQuotientsEquiv_apply_coe (P : Polynomial ℚ) (K : hilbertQuotients E P T) :
    (hilbertQuotientsEquiv E T P K).1 = readingSubobject E T K.1 :=
  rfl

end TestScheme

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
