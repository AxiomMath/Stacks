module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SubobjectRigidity
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Bridge
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.BridgeNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistQuotients
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteBridgeNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback

/-!
# Quotients of `F_T` read as quotients of `𝒪` on `ℙⁿ_T`, naturally in `T`

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame `X = B × ℙⁿ_ℤ`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.ProjectiveFrame`), and suppose that for every test
scheme `T` the reading of `F_T` on `ℙⁿ_T` is isomorphic to `𝒪_{ℙⁿ_T}`
(`AlgebraicGeometry.C1590Private.HasUnitReading`; this holds for `F = 𝒪_X`). Reading a quotient
of `F_T` on `ℙⁿ_T` (`AlgebraicGeometry.ProjectiveQuotOverSpace.readingSubobject`) and
transporting it along a chosen isomorphism with `𝒪_{ℙⁿ_T} = 𝒪^{⊕ 1}` gives a submodule of
`𝒪^{⊕ 1}` (`AlgebraicGeometry.C1590Private.quotKernel`).

The chosen isomorphisms are not compatible with base change in any controlled way, but they do
not have to be: every automorphism of `𝒪` fixes every submodule
(`AlgebraicGeometry.C1590Private.isSubobjectRigid_freeModule_one`), so the transported submodule
does not depend on the choice. Hence the construction commutes with base change
(`AlgebraicGeometry.C1590Private.quotKernel_quotientPullback`): the only coherence needed is the
naturality in the module of the comparison of readings along `ℙⁿ_{T'} ⟶ ℙⁿ_T`
(`AlgebraicGeometry.C1590Private.readingPullbackIso_naturality`).

## Main definitions

* `AlgebraicGeometry.C1590Private.HasUnitReading`.
* `AlgebraicGeometry.C1590Private.quotKernel`.
* `AlgebraicGeometry.C1590Private.properlySupportedQuotientsFamiliesEquiv`: the members of
  `Quot_{F/X/B}(T)` correspond to the members of `Quot_{𝒪/ℙⁿ/ℤ}(T)`.

## Main results

* `AlgebraicGeometry.C1590Private.quotKernel_quotientPullback`: the correspondence commutes with
  base change.
* `AlgebraicGeometry.C1590Private.mem_hilbertQuotients_iff_quotKernel_mem`: it matches `Quot^P`
  on both sides.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

-- As in `StacksFrontier/AlgebraicGeometry/Quot/ProjectiveQuot/SiteBridgeNaturality.lean`: the
-- represented and the `schemeSpace` spellings of the reading are compared through this unfolding.
attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite


namespace AlgebraicGeometry.C1590Private

open ProjectiveQuot ProjectiveQuotOverSpace

universe u

/-! ### Transport of subobjects along an isomorphism -/

section Transport

variable {C : Type*} [Category* C]

/-- Transporting the kernel of `p` along an isomorphism `ρ` of its source gives the kernel of
`ρ⁻¹ ≫ p`. -/
theorem map_hom_kernelSubobject [Preadditive C] [HasKernels C] {G G' Q : C} (ρ : G ≅ G')
    (p : G ⟶ Q) :
    (Subobject.map ρ.hom).obj (kernelSubobject p) = kernelSubobject (ρ.inv ≫ p) := by
  conv_lhs => rw [← Subobject.mk_arrow (kernelSubobject p)]
  rw [Subobject.map_mk]
  refine (Subobject.mk_eq_mk_of_comm _ _ (kernelSubobjectIsoComp ρ.inv p).symm ?_).trans
    (Subobject.mk_arrow _)
  rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, kernelSubobjectIsoComp_hom_arrow,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Equal subobjects have isomorphic quotients. -/
def cokernelArrowIsoOfEq [HasZeroMorphisms C] [HasCokernels C] {G : C} {S₁ S₂ : Subobject G}
    (h : S₁ = S₂) : cokernel S₁.arrow ≅ cokernel S₂.arrow :=
  eqToIso (congrArg (fun S : Subobject G => cokernel S.arrow) h)

/-- Transporting a subobject along an isomorphism does not change its quotient. -/
theorem nonempty_cokernel_map_hom_iso [Abelian C] {G G' : C} (ρ : G ≅ G') (K : Subobject G) :
    Nonempty (cokernel ((Subobject.map ρ.hom).obj K).arrow ≅ cokernel K.arrow) := by
  have h : (Subobject.map ρ.hom).obj K = Subobject.mk (K.arrow ≫ ρ.hom) := by
    conv_lhs => rw [← Subobject.mk_arrow K]
    rfl
  refine ⟨cokernelArrowIsoOfEq h ≪≫ ?_⟩
  exact cokernelIsoOfEq ((Iso.inv_comp_eq _).1 (Subobject.underlyingIso_arrow (K.arrow ≫ ρ.hom))) ≪≫
    cokernelEpiComp (Subobject.underlyingIso (K.arrow ≫ ρ.hom)).hom _ ≪≫
    cokernelCompIsIso K.arrow ρ.hom

end Transport

/-! ### The reading, through the represented presheaf -/

section Abstract

/-- Two parallel epimorphisms related by isomorphisms of sources and targets have kernels which
correspond along the isomorphism of sources. -/
theorem kernelSubobject_comp_eq_of_comm {C : Type*} [Category* C] [Abelian C]
    {Z A₁ A₂ B₁ B₂ : C} (x : A₁ ⟶ B₁) (y : A₂ ⟶ B₂) (e₁ : A₁ ⟶ A₂) (e₂ : B₁ ⟶ B₂) [IsIso e₁]
    [IsIso e₂] (h : x ≫ e₂ = e₁ ≫ y) (v : Z ⟶ A₂) :
    kernelSubobject (v ≫ y) = kernelSubobject ((v ≫ inv e₁) ≫ x) := by
  have hy : v ≫ y = ((v ≫ inv e₁) ≫ x) ≫ e₂ := by
    rw [Category.assoc, Category.assoc, h, IsIso.inv_hom_id_assoc]
  rw [hy, kernelSubobject_comp_mono]

/-- **The base change of a quotient, read through comparisons, in arbitrary abelian
categories.** This is the shape of `AlgebraicGeometry.C1590Private.quotKernel_quotientPullback`:
every datum is a variable, and every place where two spellings of the same morphism meet is an
equation (`hx`, `hy`), so that the instantiation compares no two spellings. -/
theorem kernelSubobject_baseChange_of_comm {𝒳 𝒳' 𝒮 𝒮' : Type*} [Category* 𝒳] [Category* 𝒳']
    [Category* 𝒮] [Category* 𝒮'] [Abelian 𝒮] [Abelian 𝒮'] (R : 𝒳 ⥤ 𝒮) (R' : 𝒳' ⥤ 𝒮')
    (m : 𝒳 ⥤ 𝒳') (G : 𝒮 ⥤ 𝒮') {F Q : 𝒳} {F' Q' : 𝒳'} (πK : F ⟶ Q) [Epi (R.map πK)]
    (π' : F' ⟶ Q') (c : F' ⟶ m.obj F) [IsIso c] (ι : Q' ≅ m.obj Q) (hπ' : π' ≫ ι.hom = c ≫ m.map πK)
    {O : 𝒮} {O' : 𝒮'} (ρ : R.obj F ≅ O) (ρ' : R'.obj F' ≅ O') (hO' : IsSubobjectRigid O')
    (fPI : G.obj O ≅ O')
    {A₁ B₁ A₂ B₂ : 𝒮'} (x : A₁ ⟶ B₁) (y : A₂ ⟶ B₂) (e₁ : A₁ ⟶ A₂) (e₂ : B₁ ⟶ B₂)
    (h : x ≫ e₂ = e₁ ≫ y) (he₁ : IsIso e₁) (he₂ : IsIso e₂)
    (hA₁ : A₁ = G.obj (R.obj F)) (hB₁ : B₁ = G.obj (R.obj Q))
    (hA₂ : A₂ = R'.obj (m.obj F)) (hB₂ : B₂ = R'.obj (m.obj Q))
    (hx : x ≍ G.map (R.map πK)) (hy : y ≍ R'.map (m.map πK))
    (Φ : Subobject O) (hΦ : Φ = kernelSubobject (ρ.inv ≫ R.map πK))
    (Φ' : Subobject O') (hΦ' : Φ' = kernelSubobject (ρ'.inv ≫ R'.map π')) :
    Φ' = kernelSubobject (fPI.inv ≫ G.map (cokernel.π Φ.arrow)) := by
  subst hA₁ hB₁ hA₂ hB₂
  subst hΦ hΦ'
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  have := he₁
  have := he₂
  have hL : kernelSubobject (ρ'.inv ≫ R'.map π') =
      kernelSubobject ((ρ'.inv ≫ R'.map c) ≫ R'.map (m.map πK)) := by
    refine (kernelSubobject_eq_of_comp_mono _ _ (R'.map ι.hom) ?_).symm
    rw [Category.assoc, Category.assoc, ← R'.map_comp, hπ', R'.map_comp]
  have : Epi (ρ.inv ≫ R.map πK) := epi_comp _ _
  rw [hL, kernelSubobject_comp_eq_of_comm _ _ _ _ h,
    ProjectiveQuot.kernelSubobject_comp_map_cokernel_π, G.map_comp, ← Category.assoc]
  exact kernelSubobject_comp_eq_of_isSubobjectRigid hO' _ _ _

end Abstract

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase} (E : ProjectiveFrame B n D)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **The reading on `ℙⁿ_T`, written through the represented presheaf `⟨yoneda.obj ℙⁿ_T, _⟩`**
rather than `AlgebraicGeometry.schemeSpace`: the spelling of
`AlgebraicGeometry.ProjectiveQuot.readingPullback_naturality`. It is the functor
`AlgebraicGeometry.ProjectiveQuotOverSpace.reading`
(`AlgebraicGeometry.C1590Private.reading_eq_yReading`); the two spellings are compared only as
whole functors, since compared on morphisms the unifier unfolds the structure sheaves. -/
abbrev yReading (T : Space.SchemesOver D.Y) :=
  Space.modulePullback B integerBase B.contains_integerBase
      (X := (⟨yoneda.obj (projectiveSite B n T.left), isAlgebraicSpace_yoneda B integerBase
        B.contains_integerBase (projectiveSite B n T.left)⟩ :
          AlgebraicSpaces B integerBase B.contains_integerBase))
      (@Iso.hom _ _ (⟨yoneda.obj (projectiveSite B n T.left), isAlgebraicSpace_yoneda B
        integerBase B.contains_integerBase (projectiveSite B n T.left)⟩ :
          AlgebraicSpaces B integerBase B.contains_integerBase) _ (spaceIso E T)) ⋙
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property

/-- The reading `AlgebraicGeometry.ProjectiveQuotOverSpace.reading` on `ℙⁿ_T` is the functor
`AlgebraicGeometry.C1590Private.yReading`. -/
theorem reading_eq_yReading (T : Space.SchemesOver D.Y) : reading E T = yReading E T :=
  rfl

/-- `AlgebraicGeometry.C1590Private.yReading` on a morphism, written out factor by factor. -/
theorem yReading_map_eq (T : Space.SchemesOver D.Y)
    {M M' : Space.Modules.{u, u} B integerBase B.contains_integerBase (D.space T).1 (D.space T).2}
    (f : M ⟶ M') :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).map
        ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.map
          ((Space.modulePullback B integerBase B.contains_integerBase
            (X := (⟨yoneda.obj (projectiveSite B n T.left), isAlgebraicSpace_yoneda B integerBase
              B.contains_integerBase (projectiveSite B n T.left)⟩ :
                AlgebraicSpaces B integerBase B.contains_integerBase))
            (@Iso.hom _ _ (⟨yoneda.obj (projectiveSite B n T.left), isAlgebraicSpace_yoneda B
              integerBase B.contains_integerBase (projectiveSite B n T.left)⟩ :
                AlgebraicSpaces B integerBase B.contains_integerBase) _
              (spaceIso E T))).map f)) =
      (yReading E T).map f := by
  simp only [yReading, Functor.comp_map]

/-- The submodule of the reading of `F_T` corresponding to a submodule of `F_T`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.readingSubobject`, in the spelling of
`AlgebraicGeometry.C1590Private.yReading`). -/
def ySubobject (T : Space.SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    Subobject ((yReading E T).obj (D.baseChangeModule T)) :=
  kernelSubobject ((yReading E T).map (cokernel.π K.arrow))

/-- For a quasicoherent quotient `F_T ⟶ F_T / K`, the reading of the quotient map on `ℙⁿ_T` is an
epimorphism. -/
theorem epi_yReading_map (T : Space.SchemesOver D.Y) (K : Subobject (D.baseChangeModule T))
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    Epi ((yReading E T).map (cokernel.π K.arrow)) := by
  simpa only [reading_eq_yReading] using epi_reading_map_cokernel_π E T K hK

/-- A quasicoherent quotient `F_T / K` is a member of `Quot_{F/X/B}(T)` exactly when the quotient
of the reading by `ySubobject E T K` is a flat family over `T`. -/
theorem mem_properlySupportedQuotients_iff_yReading (T : Space.SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ D.properlySupportedQuotients T ↔
      IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel (ySubobject E T K).arrow) := by
  simpa only [readingSubobject, ySubobject, reading_eq_yReading] using
    mem_properlySupportedQuotients_iff E T K hK

/-- A quasicoherent quotient `F_T / K` is a member of `Quot^P_{F/X/B}(T)` exactly when the quotient
of the reading by `ySubobject E T K` is a flat family over `T` whose fibres have Hilbert
polynomial `P`. -/
theorem mem_hilbertQuotients_iff_yReading (P : Polynomial ℚ) (T : Space.SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ hilbertQuotients E P T ↔
      IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel (ySubobject E T K).arrow) ∧
        HasFibreHilbertPolynomial (n := n) (T := (𝒯).obj T.left) P
          (cokernel (ySubobject E T K).arrow) := by
  simpa only [readingSubobject, ySubobject, reading_eq_yReading] using
    mem_hilbertQuotients_iff E T P K hK

/-- Two submodules of `F_T` with quasicoherent quotients and the same corresponding submodule of
the reading are equal. -/
theorem ySubobject_injective (T : Space.SchemesOver D.Y) {K₁ K₂ : Subobject (D.baseChangeModule T)}
    (h₁ : (cokernel K₁.arrow).IsQuasicoherentOnSite)
    (h₂ : (cokernel K₂.arrow).IsQuasicoherentOnSite)
    (h : ySubobject E T K₁ = ySubobject E T K₂) : K₁ = K₂ := by
  have hr : readingSubobject E T K₁ = readingSubobject E T K₂ := by
    simpa only [readingSubobject, ySubobject, reading_eq_yReading] using h
  have e₁ := qcohQuotientEquiv_apply_coe E T ⟨K₁, h₁⟩
  have e₂ := qcohQuotientEquiv_apply_coe E T ⟨K₂, h₂⟩
  have := (qcohQuotientEquiv E T).injective (Subtype.ext (e₁.trans (hr.trans e₂.symm)))
  exact congrArg Subtype.val this

/-- Every submodule of the reading of `F_T` whose quotient is a flat family over `T` is
`ySubobject E T K` for a member `K` of `Quot_{F/X/B}(T)`. -/
theorem exists_ySubobject_eq (T : Space.SchemesOver D.Y) :
    ∀ K' : Subobject ((yReading E T).obj (D.baseChangeModule T)),
      IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel K'.arrow) →
        ∃ K ∈ D.properlySupportedQuotients T, ySubobject E T K = K' := by
  have h : ∀ K' : Subobject ((reading E T).obj (D.baseChangeModule T)),
      IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel K'.arrow) →
        ∃ K ∈ D.properlySupportedQuotients T,
          kernelSubobject ((reading E T).map (cokernel.π K.arrow)) = K' := fun K' hK' =>
    ⟨((properlySupportedQuotientsEquiv E T).symm ⟨K', hK'⟩).1,
      ((properlySupportedQuotientsEquiv E T).symm ⟨K', hK'⟩).2,
      congrArg Subtype.val ((properlySupportedQuotientsEquiv E T).apply_symm_apply ⟨K', hK'⟩)⟩
  simp only [reading_eq_yReading] at h
  exact h

/-- `𝒪^{⊕ 1}` on `ℙⁿ_T`, as an object of the category the reading lands in. -/
abbrev freeModuleReading (T : Space.SchemesOver D.Y) :
    ((𝒯).obj (projectiveSite B n T.left)).Modules :=
  freeModule n 1 ((𝒯).obj T.left)

/-- A framed Quot situation has a *unit reading* when for every test scheme `T` the reading of
`F_T` on `ℙⁿ_T` is isomorphic to `𝒪^{⊕ 1}`. -/
def HasUnitReading : Prop :=
  ∀ T : Space.SchemesOver D.Y,
    Nonempty ((yReading E T).obj (D.baseChangeModule T) ≅ freeModuleReading (n := n) (D := D) T)

/-! ### Reading quotients as quotients of `𝒪` -/

variable {E} (hE : HasUnitReading E)

/-- The chosen identification of the reading of `F_T` with `𝒪^{⊕ 1}`. -/
def unitReadingIso (T : Space.SchemesOver D.Y) :
    (yReading E T).obj (D.baseChangeModule T) ≅ freeModuleReading (n := n) (D := D) T :=
  (hE T).some

/-- A quotient of `F_T`, read as a quotient of `𝒪^{⊕ 1}` on `ℙⁿ_T`, in the category the
reading lands in. -/
def quotKernelReading (T : Space.SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    Subobject (freeModuleReading (n := n) (D := D) T) :=
  Subobject.mapIsoToOrderIso (unitReadingIso hE T) (ySubobject E T K)

/-- **A quotient of `F_T`, read as a quotient of `𝒪^{⊕ 1}` on `ℙⁿ_T`.** -/
def quotKernel (T : Space.SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    Subobject (freeModule n 1 ((𝒯).obj T.left)) :=
  quotKernelReading hE T K

/-- `quotKernel hE T K` is the kernel of the composite of the inverse of the chosen
identification `unitReadingIso hE T` with the reading of the quotient map `F_T ⟶ F_T / K`. -/
theorem quotKernel_eq (T : Space.SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    quotKernel hE T K =
      kernelSubobject ((unitReadingIso hE T).inv ≫ (yReading E T).map (cokernel.π K.arrow)) :=
  map_hom_kernelSubobject _ _

/-- The quotient of `𝒪^{⊕ 1}` by `quotKernel` is the quotient by the corresponding submodule of
the reading. -/
theorem nonempty_quotient_quotKernel_iso (T : Space.SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) :
    Nonempty (ProjectiveQuot.quotient (quotKernel hE T K) ≅ cokernel (ySubobject E T K).arrow) :=
  nonempty_cokernel_map_hom_iso (unitReadingIso hE T) (ySubobject E T K)

/-- For a member `K` of `Quot_{F/X/B}(T)`, the submodule `quotKernel hE T K` of `𝒪^{⊕ 1}` is a
member of `Quot_{𝒪/ℙⁿ/ℤ}(T)`. -/
theorem quotKernel_mem_families (T : Space.SchemesOver D.Y) (K : D.properlySupportedQuotients T) :
    quotKernel hE T K.1 ∈ families n 1 ((𝒯).obj T.left) := by
  obtain ⟨e⟩ := nonempty_quotient_quotKernel_iso hE T K.1
  exact ProjectiveQuotOverSpace.isFlatFamily_of_iso e.symm
    ((mem_properlySupportedQuotients_iff_yReading E T K.1 K.2.1.1.1).1 K.2)

/-- **The correspondence matches `Quot^P` on both sides.** -/
theorem mem_hilbertQuotients_iff_quotKernel_mem (P : Polynomial ℚ) (T : Space.SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ hilbertQuotients E P T ↔ quotKernel hE T K ∈ hilbertFamilies n 1 P ((𝒯).obj T.left) := by
  rw [mem_hilbertQuotients_iff_yReading E P T K hK, mem_hilbertFamilies_iff]
  obtain ⟨e⟩ := nonempty_quotient_quotKernel_iso hE T K
  exact ⟨fun ⟨hfl, hP⟩ => ⟨ProjectiveQuotOverSpace.isFlatFamily_of_iso e.symm hfl,
      hasFibreHilbertPolynomial_of_iso hfl.1 e.symm hP⟩,
    fun ⟨hfl, hP⟩ => ⟨ProjectiveQuotOverSpace.isFlatFamily_of_iso e hfl,
      hasFibreHilbertPolynomial_of_iso hfl.1 e hP⟩⟩

/-- **The members of `Quot_{F/X/B}(T)` are the members of `Quot_{𝒪/ℙⁿ/ℤ}(T)`.** -/
def properlySupportedQuotientsFamiliesEquiv (T : Space.SchemesOver D.Y) :
    D.properlySupportedQuotients T ≃ families n 1 ((𝒯).obj T.left) :=
  Equiv.ofBijective (fun K => ⟨quotKernel hE T K.1, quotKernel_mem_families hE T K⟩) ⟨
    fun K₁ K₂ h => Subtype.ext (ySubobject_injective E T K₁.2.1.1.1 K₂.2.1.1.1
      ((Subobject.mapIsoToOrderIso (unitReadingIso hE T)).injective
        (show quotKernelReading hE T K₁.1 = quotKernelReading hE T K₂.1 from
          congrArg Subtype.val h))),
    fun K'' => by
      obtain ⟨K', hK'K⟩ := (Subobject.mapIsoToOrderIso (unitReadingIso hE T)).surjective K''.1
      obtain ⟨e⟩ := nonempty_cokernel_map_hom_iso (unitReadingIso hE T) K'
      have h :
          Subobject.mapIsoToOrderIso (unitReadingIso hE T) K' ∈ families n 1 ((𝒯).obj T.left) :=
        hK'K ▸ K''.2
      have hfl : IsFlatFamily (n := n) (T := (𝒯).obj T.left) (cokernel K'.arrow) :=
        ProjectiveQuotOverSpace.isFlatFamily_of_iso e h
      obtain ⟨K, hK, hKK⟩ := exists_ySubobject_eq E T K' hfl
      exact ⟨⟨K, hK⟩, Subtype.ext ((congrArg _ hKK).trans hK'K)⟩⟩

/-- `properlySupportedQuotientsFamiliesEquiv hE T` sends `K` to `quotKernel hE T K`. -/
theorem properlySupportedQuotientsFamiliesEquiv_apply_coe (T : Space.SchemesOver D.Y)
    (K : D.properlySupportedQuotients T) :
    (properlySupportedQuotientsFamiliesEquiv hE T K).1 = quotKernel hE T K.1 :=
  rfl

/-! ### Naturality -/

section Square

variable {T' T : Space.SchemesOver D.Y} (h : T' ⟶ T)

/-- The square `h_{ℙⁿ_{T'}} ⟶ h_{ℙⁿ_T} ⟶ X_T` against `h_{ℙⁿ_{T'}} ⟶ X_{T'} ⟶ X_T`, in the
spelling of `AlgebraicGeometry.ProjectiveQuot.readingPullback_naturality`. -/
theorem yReading_square :
    Space.representedSpaceMap B integerBase B.contains_integerBase (projectiveSiteMap B n h.left) ≫
        @Iso.hom _ _ (⟨yoneda.obj (projectiveSite B n T.left), isAlgebraicSpace_yoneda B
          integerBase B.contains_integerBase (projectiveSite B n T.left)⟩ :
            AlgebraicSpaces B integerBase B.contains_integerBase) _ (spaceIso E T) =
      @Iso.hom _ _ (⟨yoneda.obj (projectiveSite B n T'.left), isAlgebraicSpace_yoneda B
          integerBase B.contains_integerBase (projectiveSite B n T'.left)⟩ :
            AlgebraicSpaces B integerBase B.contains_integerBase) _ (spaceIso E T') ≫
        D.relativeMap h :=
  (spaceIso_hom_relativeMap E h).symm

end Square

/-- **Reading quotients as quotients of `𝒪` commutes with base change.** -/
theorem quotKernel_quotientPullback {T' T : Space.SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    quotKernel hE T' (D.quotientPullback h K) =
      ProjectiveQuot.baseChange ((𝒯).map h.left) (quotKernel hE T K) := by
  have := epi_yReading_map E T K hK
  have nat := ProjectiveQuot.readingPullback_naturality (W := projectiveSite B n T.left)
    (W' := projectiveSite B n T'.left) (X := D.space T) (X' := D.space T')
    (projectiveSiteMap B n h.left)
    (spaceIso E T) (spaceIso E T') (D.relativeMap h) _ (yReading_square (E := E) h) rfl
    (isQuasicoherentOnSite_baseChangeModule (D := D) T) hK (cokernel.π K.arrow)
  refine kernelSubobject_baseChange_of_comm (yReading E T) (yReading E T')
    (Space.modulePullback B integerBase B.contains_integerBase (D.relativeMap h))
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) (projectiveSiteMap B n h.left).left))
    (cokernel.π K.arrow) (cokernel.π (D.quotientPullback h K).arrow)
    ((D.baseChangeComparison h).hom.app D.F) (D.quotientPullbackCokernelIso h K)
    (D.quotientProjection_comp_quotientPullbackCokernelIso_hom h K)
    (unitReadingIso hE T) (unitReadingIso hE T')
    (isSubobjectRigid_freeModule_one n ((𝒯).obj T'.left)) (freeModulePullbackIso n 1 _)
    _ _ _ _ nat ?_ ?_ rfl rfl rfl rfl
    (heq_of_eq (congrArg _ (yReading_map_eq E T _))) (heq_of_eq (yReading_map_eq E T' _))
    _ (quotKernel_eq hE T K) _ (quotKernel_eq hE T' _)
  all_goals
    refine IsIso.comp_isIso' (Iso.isIso_hom _) ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    exact NatIso.isIso_app_of_isIso _ _

end AlgebraicGeometry.C1590Private

end
