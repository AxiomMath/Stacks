module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteReadingConditions

/-!
# The quotients of the site Quot functor of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` are the scheme-level ones

For a test scheme `T` of the Quot situation `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` on the big fppf site
(`AlgebraicGeometry.ProjectiveQuot.quotSituation`), the members of `Quot_{F/X/B}(T)` of
Stacks 09TR — quotients of `F_T` that are quasi-coherent, of finite presentation, flat over `T` and
with support proper over `T` — correspond to the members of
`AlgebraicGeometry.ProjectiveQuot.families n r T`: quotients of `𝒪^{⊕ r}` on the scheme `ℙⁿ_T` of
finite presentation and flat over `T`.  The correspondence reads a quotient on `ℙⁿ_T`
(`AlgebraicGeometry.ProjectiveQuot.siteReading`), and the quotient of `𝒪^{⊕ r}` it produces is
the reading of the quotient of `F_T`.  The proper-support condition is automatic, `ℙⁿ_T ⟶ T`
being proper.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.properlySupportedQuotientsEquiv`: the correspondence over a
  test scheme.
* `AlgebraicGeometry.ProjectiveQuot.quotFamilyOverEquiv`: the same over a scheme of the site,
  the morphism to the base being unique.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.mem_properlySupportedQuotients_iff`: the conditions of
  Stacks 09TR are the conditions of `AlgebraicGeometry.ProjectiveQuot.families`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The ambient-universe abelian structure of site modules cannot describe the `𝒪_{X_T}`-modules
-- here, whose sections live in the universe of the schemes; left in place it is selected ahead
-- of `SheafOfModules.instAbelian` and leaves the module universe of every subobject unsolved (as
-- in `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorPullback.lean`).
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n r : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

section TestScheme

variable (T : Space.SchemesOver (quotSituation B n r).Y)

/-- `F_T` is quasi-coherent. -/
theorem isQuasicoherentOnSite_baseChangeModule :
    ((quotSituation B n r).baseChangeModule T).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase _ _ (quotSituation B n r).quasicoherent

/-- The subobject of `𝒪^{⊕ r}` on `ℙⁿ_T` corresponding to a subobject of `F_T`: the kernel of
`𝒪^{⊕ r} ≅ (F_T)_{ℙⁿ_T} ⟶ (F_T/K)_{ℙⁿ_T}`. -/
abbrev schemeSubobject (K : Subobject ((quotSituation B n r).baseChangeModule T)) :
    Subobject (freeModule n r ((𝒯).obj T.left)) :=
  Adjunction.QuotientCorrespondence.rightSubobject (siteReadingFreeIso r T) K

/-- The quotient of `𝒪^{⊕ r}` by the corresponding subobject is the reading on `ℙⁿ_T` of the
quotient of `F_T`. -/
def schemeSubobjectCokernelIso (K : Subobject ((quotSituation B n r).baseChangeModule T))
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    cokernel (schemeSubobject T K).arrow ≅ (siteReading r T).obj (cokernel K.arrow) :=
  (quotientCorrespondence_siteReadingAdjunction T).rightCokernelIso
    (isQuasicoherentOnSite_baseChangeModule T) (siteReadingFreeIso r T) K hK

/-- **The quasi-coherent quotients of `F_T` and of `𝒪^{⊕ r}` on `ℙⁿ_T` correspond.** -/
def qcohQuotientEquiv :
    {K : Subobject ((quotSituation B n r).baseChangeModule T) //
        (cokernel K.arrow).IsQuasicoherentOnSite} ≃
      {K' : Subobject (freeModule n r ((𝒯).obj T.left)) //
        SheafOfModules.IsQuasicoherent (cokernel K'.arrow)} :=
  haveI := isIso_siteReadingAdjunction_counit_app T _ (isQuasicoherentOnSite_baseChangeModule T)
  (quotientCorrespondence_siteReadingAdjunction T).subobjectEquiv
    (isQuasicoherentOnSite_baseChangeModule T) (siteReadingFreeIso r T)

/-- The subobject of `𝒪^{⊕ r}` that `qcohQuotientEquiv` assigns to `K` is `schemeSubobject T K`. -/
theorem qcohQuotientEquiv_apply_coe
    (K : {K : Subobject ((quotSituation B n r).baseChangeModule T) //
      (cokernel K.arrow).IsQuasicoherentOnSite}) :
    (qcohQuotientEquiv T K).1 = schemeSubobject T K.1 :=
  rfl

/-- **The conditions of Stacks 09TR are the conditions of `families`.**  For a subobject `K` of
`F_T` with quasi-coherent quotient, the quotient is of finite presentation, flat over `T` and with
support proper over `T` exactly when the corresponding quotient of `𝒪^{⊕ r}` on `ℙⁿ_T` is of
finite presentation and flat over `T`. -/
theorem mem_properlySupportedQuotients_iff
    (K : Subobject ((quotSituation B n r).baseChangeModule T))
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ (quotSituation B n r).properlySupportedQuotients T ↔
      schemeSubobject T K ∈ families n r ((𝒯).obj T.left) := by
  let e := schemeSubobjectCokernelIso T K hK
  have hfp : SheafOfModules.IsFinitePresentationOnSite (cokernel K.arrow) ↔
      (cokernel (schemeSubobject T K).arrow).IsFinitePresentation :=
    (isFinitePresentationOnSite_iff_siteReading T _ hK).trans
      ⟨fun h => SheafOfModules.IsFinitePresentation.of_iso h e.symm,
        fun h => SheafOfModules.IsFinitePresentation.of_iso h e⟩
  have hfl : Space.IsFlatOver B integerBase B.contains_integerBase
        ((quotSituation B n r).space T).2 ((quotSituation B n r).projection T).hom
        (cokernel K.arrow) ↔
      AlgebraicGeometry.IsFlatOver
        (projectiveSpaceOver n ((𝒯).obj T.left) ↘ (𝒯).obj T.left).toLRSHom.toShHom
        (cokernel (schemeSubobject T K).arrow) :=
    (isFlatOver_iff_siteReading T _ hK).trans
      (forall_congr' fun x => (flatOverAt_iff_of_iso _ e x).symm)
  constructor
  · rintro ⟨⟨⟨_, hflat⟩, hfp'⟩, _⟩
    exact ⟨hfp.1 hfp', hfl.1 hflat⟩
  · rintro ⟨hfp', hflat⟩
    have := hfp.2 hfp'
    exact ⟨⟨⟨hK, hfl.2 hflat⟩, this⟩, isProperlySupportedOver_of_isFinitePresentationOnSite T _⟩

/-- The quotient of a member of `families` is quasi-coherent, being of finite presentation. -/
theorem isQuasicoherent_of_mem_families {K' : Subobject (freeModule n r ((𝒯).obj T.left))}
    (h : K' ∈ families n r ((𝒯).obj T.left)) :
    SheafOfModules.IsQuasicoherent (cokernel K'.arrow) :=
  have : (quotient K').IsFinitePresentation := h.1
  Stacks.Modules.isQuasicoherent_of_isFinitePresentation (quotient K')

/-- **`Quot_{F/X/B}(T)` of Stacks 09TR is `families n r T`** for the Quot situation of
`𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ`, through the reading on `ℙⁿ_T`. -/
def properlySupportedQuotientsEquiv :
    (quotSituation B n r).properlySupportedQuotients T ≃ families n r ((𝒯).obj T.left) where
  toFun K := ⟨schemeSubobject T K.1,
    (mem_properlySupportedQuotients_iff T K.1 K.2.1.1.1).1 K.2⟩
  invFun K' := ⟨((qcohQuotientEquiv T).symm ⟨K'.1, isQuasicoherent_of_mem_families T K'.2⟩).1, by
    set K := (qcohQuotientEquiv T).symm ⟨K'.1, isQuasicoherent_of_mem_families T K'.2⟩
    have hK : schemeSubobject T K.1 = K'.1 :=
      congrArg Subtype.val ((qcohQuotientEquiv T).apply_symm_apply _)
    exact (mem_properlySupportedQuotients_iff T K.1 K.2).2 (hK ▸ K'.2)⟩
  left_inv K := Subtype.ext (by
    have h := congrArg Subtype.val ((qcohQuotientEquiv T).symm_apply_apply ⟨K.1, K.2.1.1.1⟩)
    exact h)
  right_inv K' := Subtype.ext (by
    have h := congrArg Subtype.val
      ((qcohQuotientEquiv T).apply_symm_apply ⟨K'.1, isQuasicoherent_of_mem_families T K'.2⟩)
    exact h)

/-- The member of `families` that `properlySupportedQuotientsEquiv` assigns to `K` is
`schemeSubobject T K`. -/
theorem properlySupportedQuotientsEquiv_apply_coe
    (K : (quotSituation B n r).properlySupportedQuotients T) :
    (properlySupportedQuotientsEquiv T K).1 = schemeSubobject T K.1 :=
  rfl

end TestScheme

/-! ### Over a scheme of the site -/

/-- A scheme of the site, read as a test scheme of the Quot situation through its unique morphism
to the base. -/
abbrev siteTestScheme (T : BigFppfOver B integerBase B.contains_integerBase) :
    Space.SchemesOver (quotSituation B n r).Y :=
  CostructuredArrow.mk (schemeSpaceMap (toSiteBase B T))

/-- Over a scheme of the site, a section of the Quot presheaf is a member of `Quot_{F/X/B}` of the
canonical test scheme: the morphism to the base it lies over is unique. -/
def quotFamilyOverEquivProperlySupported (T : BigFppfOver B integerBase B.contains_integerBase) :
    Space.QuotFamilyOver (quotSituation B n r) T ≃
      (quotSituation B n r).properlySupportedQuotients (siteTestScheme T) :=
  (Equiv.ofBijective (fun K => (⟨schemeSpaceMap (toSiteBase B T), K.1, K.2⟩ :
      Space.QuotFamilyOver (quotSituation B n r) T)) ⟨fun a b h => by
        injection h with h1 h2
        exact Subtype.ext h2, by
        rintro ⟨b, K, hK⟩
        obtain rfl : b = schemeSpaceMap (toSiteBase B T) :=
          (subsingleton_hom_schemeSpace_siteBase B _).elim _ _
        exact ⟨⟨K, hK⟩, rfl⟩⟩).symm

/-- **Over a scheme `T` of the site, the Quot presheaf of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` is
`families n r T`.** -/
def quotFamilyOverEquiv (T : BigFppfOver B integerBase B.contains_integerBase) :
    Space.QuotFamilyOver (quotSituation B n r) T ≃ families n r ((𝒯).obj T) :=
  (quotFamilyOverEquivProperlySupported T).trans
    (properlySupportedQuotientsEquiv (siteTestScheme T))

end AlgebraicGeometry.ProjectiveQuot

end
