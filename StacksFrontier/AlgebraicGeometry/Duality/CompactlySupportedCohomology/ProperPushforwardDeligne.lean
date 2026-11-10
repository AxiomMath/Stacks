module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProperPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProperPushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemFunctorImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivityClosed
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCovering
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine

/-!
# Proper pushforward of Deligne systems

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, `V ⊆ Y` open and `U = f⁻¹(V)`. For
every object `K` of `D^b_{Coh}(𝒪_U)` the image `(Rf_* K_n)` of a Deligne system of `K` is
pro-isomorphic to a Deligne system along `V ⟶ Y`. This is the main step of the first proof of
[Stacks, Tag 0G4W].

The source's argument: the reduction to a coherent module in one degree is
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemFunctorImage`; the
question is local on `Y` by [Stacks, Tag 0G4T] and compatible with restriction to opens of `Y`
by [Stacks, Tag 08FE]; over an affine base, by [Stacks, Tag 0G4S], it is the statement that the
higher direct images `(R^q f_*(𝓘^n𝓕))_n` are pro-isomorphic to ideal-power systems of coherent
modules, which is [Stacks, Tag 02OA] (5).

## Main results

* `AlgebraicGeometry.proIsoDeligneSystem_properPushforward_single_affine`: the affine case.
* `AlgebraicGeometry.proIsoDeligneSystem_properPushforward_single`: the coherent case.
* `AlgebraicGeometry.proIsoDeligneSystem_properPushforward`: the general case.

## References

* [Stacks Project, Tag 0G4W](https://stacks.math.columbia.edu/tag/0G4W)
* [Stacks Project, Tag 0G4T](https://stacks.math.columbia.edu/tag/0G4T)
* [Stacks Project, Tag 0G4S](https://stacks.math.columbia.edu/tag/0G4S)
* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Over an affine base `Y`, the extension `I · 𝒪_X` of the ideal `I = J(Y)` of global sections of
a quasi-coherent ideal sheaf `J` cuts out the preimage of the support of `J`. -/
public lemma coe_support_baseIdealSheaf_isoSpec [IsAffine Y] (J : Y.IdealSheafData) :
    ((Stacks.Cohomology.FormalFunctions.baseIdealSheaf Γ(Y, ⊤) (J.ideal ⟨⊤, isAffineOpen_top Y⟩)
      (f ≫ Y.isoSpec.hom)).support : Set X) = f.base ⁻¹' (J.support : Set Y) := by
  have hJ : ∀ y : Y, y ∈ J.support ↔
      (J.ideal ⟨⊤, isAffineOpen_top Y⟩ : Set Γ(Y, ⊤)) ⊆ (Y.isoSpec.hom.base y).asIdeal := by
    intro y
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top Y⟩) trivial,
      ← Scheme.toSpecΓ_preimage_zeroLocus]
    rfl
  ext x
  exact ⟨fun hx => (hJ _).mpr (Stacks.Algebraization.support_baseIdealSheaf_le
      (J.ideal ⟨⊤, isAffineOpen_top Y⟩) (f ≫ Y.isoSpec.hom) hx),
    fun hx => Stacks.Algebraization.mem_support_baseIdealSheaf (J.ideal ⟨⊤, isAffineOpen_top Y⟩)
      (f ≫ Y.isoSpec.hom) ((hJ _).mp hx)⟩

/-- Two inverse systems all of whose terms are zero have isomorphic pro-objects. -/
public def ProSeq.isoOfIsZero {C : Type*} [Category C] [HasZeroMorphisms C] {F G : ℕᵒᵖ ⥤ C}
    (hF : ∀ n, IsZero (F.obj n)) (hG : ∀ n, IsZero (G.obj n)) : ProSeq.of F ≅ ProSeq.of G :=
  ProSeq.isoOfProIso (Pro.proIsoOfNatIso
    (NatIso.ofComponents (fun n => (hF n).iso (hG n)) (fun _ => (hF _).eq_of_src _ _)))

/-- The ideal-power submodules of a zero module are zero. -/
public lemma isZero_idealPowerSystem_obj {Z : Scheme.{u}} (J : Z.IdealSheafData) {M : Z.Modules}
    (hM : IsZero M) (n : ℕᵒᵖ) : IsZero ((Stacks.Duality.idealPowerSystem J M).obj n) :=
  @IsZero.of_mono _ _ _ _ _ (Stacks.Algebraization.idealPowerMultiple J n.unop M).ι
    (Scheme.Modules.mono_submodule_ι _) hM

/-- **The first proof of [Stacks, Tag 0G4W] over an affine base.** Let `f : X ⟶ Y` be a proper
morphism of Noetherian schemes with `Y` affine, `V ⊆ Y` open, `𝓕` a coherent `𝒪_X`-module and
`p ∈ ℤ`. For a suitable quasi-coherent ideal `𝓘` cutting out `X ∖ f⁻¹(V)`, the image under `Rf_*`
of the Deligne system `(𝓘^n𝓕[-p])` is pro-isomorphic to a Deligne system along `V ⟶ Y`.

By [Stacks, Tag 0G4S] it suffices that the cohomology systems `(R^{q-p}f_*(𝓘^n𝓕))_n` are
pro-isomorphic to ideal-power systems of coherent modules, which is [Stacks, Tag 02OA] (5)
through `AlgebraicGeometry.nonempty_proIso_rightDerivedPlus_idealPowerSystem`. -/
public theorem proIsoDeligneSystem_properPushforward_single_affine [IsNoetherian X] [IsAffine Y]
    [IsNoetherian Y] [IsProper f] (V : Y.Opens) (F : X.Modules) [F.IsCoherent] (p : ℤ) :
    ∃ (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ),
      ProIsoDeligneSystem V.ι ((singleDeligneSystem (f ⁻¹ᵁ V) I hI F p).system ⋙
        properPushforwardBoundedCoherent f) := by
  let Z : TopologicalSpace.Closeds Y := ⟨(V : Set Y)ᶜ, V.isOpen.isClosed_compl⟩
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  have hJ : (J.support : Set Y) = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
    rfl
  let I := Stacks.Cohomology.FormalFunctions.baseIdealSheaf Γ(Y, ⊤)
    (J.ideal ⟨⊤, isAffineOpen_top Y⟩) (f ≫ Y.isoSpec.hom)
  have hI : (I.support : Set X) = (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ := by
    rw [coe_support_baseIdealSheaf_isoSpec, hJ, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  refine ⟨I, hI, ?_⟩
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  set D := singleDeligneSystem (f ⁻¹ᵁ V) I hI F p
  set K := D.system ⋙ properPushforwardBoundedCoherent f
  let e₁ : K ⋙ (boundedCoherentDerived Y).ι ≅
      Stacks.Duality.idealPowerSystem I F ⋙ DerivedCategory.singleFunctor X.Modules p ⋙
        derivedPushforwardModules f :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft D.system (Iso.refl _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (singleDeligneSystemIso (f ⁻¹ᵁ V) I hI F p) _ ≪≫
      Functor.associator _ _ _
  let e₂ (q : ℤ) :
      (K ⋙ (boundedCoherentDerived Y).ι) ⋙ DerivedCategory.homologyFunctor Y.Modules q ≅
        Stacks.Duality.idealPowerSystem I F ⋙
          (Scheme.Modules.pushforward f).rightDerivedPlus (q - p) :=
    Functor.isoWhiskerRight e₁ _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        homologyDerivedPushforwardSingleIso f p q)
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward f
  have hab : p ≤ p + max N 0 := by omega
  refine DeligneSystem.proIsoDeligneSystem_of_homology J hJ hab K (fun n i hi => ?_) (fun q => ?_)
  · refine IsZero.of_iso ?_ ((e₂ i).app (op n))
    change IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (i - p)).obj
      (Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules)
    rcases hi with hi | hi
    · exact Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f _ _
        (by omega)
    · exact hN _ (by omega) _ inferInstance
  · refine ⟨_, (hasCoherentBoundedDirectImages_of_isProper f F).1 (q - p), ?_⟩
    rcases lt_or_ge (q - p) 0 with hq | hq
    · refine ⟨ProSeq.isoOfIsZero (fun n => ?_) (isZero_idealPowerSystem_obj J
        (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f F _ hq))⟩
      exact IsZero.of_iso
        (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f _ _ hq)
        ((e₂ q).app n)
    · obtain ⟨i, hi⟩ : ∃ i : ℕ, q - p = (i : ℤ) := ⟨(q - p).toNat, (Int.toNat_of_nonneg hq).symm⟩
      obtain ⟨e₃⟩ := nonempty_proIso_rightDerivedPlus_idealPowerSystem f J F i
      exact ⟨ProSeq.isoOfProIso (Pro.proIsoOfNatIso (e₂ q ≪≫ eqToIso (by rw [hi]))) ≪≫ e₃ ≪≫
        eqToIso (by rw [hi])⟩

section Global

/-- **Deligne systems of isomorphic complexes give the same answer.** For two Deligne systems
`(𝓘_1^n𝓕_1^•)`, `(𝓘_2^n𝓕_2^•)` along `j` built from isomorphic complexes (the ideals being
arbitrary), the image of one under a functor `R` is pro-isomorphic to a Deligne system along `j'`
if and only if that of the other is: both have the same value on `U`. -/
public lemma proIsoDeligneSystem_deligneSystemOfComplex_comp_iff {U X Y V : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X] {j' : V ⟶ Y} [IsOpenImmersion j']
    [IsNoetherian Y] (R : BoundedCoherentDerived X ⥤ BoundedCoherentDerived Y)
    (I₁ I₂ : X.IdealSheafData) (hI₁ : (I₁.support : Set X) = (Set.range j.base)ᶜ)
    (hI₂ : (I₂.support : Set X) = (Set.range j.base)ᶜ)
    (C₁ C₂ : CochainComplex X.Modules ℤ) (h₁ : ∃ a : ℤ, C₁.IsStrictlyGE a)
    (h₁' : ∃ b : ℤ, C₁.IsStrictlyLE b) (h₁c : ∀ i : ℤ, (C₁.X i).IsCoherent)
    (h₂ : ∃ a : ℤ, C₂.IsStrictlyGE a) (h₂' : ∃ b : ℤ, C₂.IsStrictlyLE b)
    (h₂c : ∀ i : ℤ, (C₂.X i).IsCoherent) (ψ : C₁ ≅ C₂) :
    ProIsoDeligneSystem j'
        ((DeligneTriangle.deligneSystemOfComplex j I₁ hI₁ C₁ h₁ h₁' h₁c).system ⋙ R) ↔
      ProIsoDeligneSystem j'
        ((DeligneTriangle.deligneSystemOfComplex j I₂ hI₂ C₂ h₂ h₂' h₂c).system ⋙ R) := by
  let D₂ := DeligneTriangle.deligneSystemOfComplex j I₂ hI₂ C₂ h₂ h₂' h₂c
  let W₁ := DeligneSystem.ofComplexValue I₁ hI₁ C₁ h₁ h₁' h₁c D₂.value
    ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso
      (DerivedCategory.Q.mapIso ψ))
  let W₂ := DeligneSystem.ofComplexValue I₂ hI₂ C₂ h₂ h₂' h₂c D₂.value (Iso.refl _)
  exact (proIsoDeligneSystem_values_comp_iff R _ W₁).symm.trans
    (proIsoDeligneSystem_values_comp_iff R _ W₂)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The coherent case of the first proof of [Stacks, Tag 0G4W].** Let `f : X ⟶ Y` be a proper
morphism of Noetherian schemes, `V ⊆ Y` open, `𝓙` the ideal of the reduced complement of `V`, `𝓕`
a coherent `𝒪_X`-module and `p ∈ ℤ`. The image under `Rf_*` of the Deligne system
`(𝓙^n𝓕[-p])` is pro-isomorphic to a Deligne system along `V ⟶ Y`.

By [Stacks, Tag 0G4T] the question is local on `Y`, and over an affine open it is
`AlgebraicGeometry.proIsoDeligneSystem_properPushforward_single_affine` after base change to the
open by [Stacks, Tag 08FE]. -/
public theorem proIsoDeligneSystem_properPushforward_single [IsNoetherian X] [IsNoetherian Y]
    [IsProper f] (V : Y.Opens) (F : X.Modules) [F.IsCoherent] (p : ℤ)
    (hI : (((Scheme.IdealSheafData.vanishingIdeal
      ⟨(V : Set Y)ᶜ, V.isOpen.isClosed_compl⟩).comap f).support : Set X) =
        (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ) :
    ProIsoDeligneSystem V.ι ((singleDeligneSystem (f ⁻¹ᵁ V)
      ((Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set Y)ᶜ, V.isOpen.isClosed_compl⟩).comap f)
        hI F p).system ⋙ properPushforwardBoundedCoherent f) := by
  obtain ⟨ι, hι, W, hWa, hWc⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover Y
  have hW : ⨆ i, W i = ⊤ :=
    eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr (hWc y)
  rw [proIsoDeligneSystem_iff_forall_restrict V.ι _ W hW]
  intro i
  have : IsAffine (W i) := hWa i
  set D := singleDeligneSystem (f ⁻¹ᵁ V)
    ((Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set Y)ᶜ, V.isOpen.isClosed_compl⟩).comap f) hI F p
  set fi := f ∣_ W i
  set Vi : (W i).toScheme.Opens := (W i).ι ⁻¹ᵁ V
  set Ui : (f ⁻¹ᵁ W i).toScheme.Opens := fi ⁻¹ᵁ Vi
  have hj : Set.range Ui.ι.base = (f ⁻¹ᵁ W i).ι.base ⁻¹' Set.range (f ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext x
    change (W i).ι.base (fi.base x) ∈ V ↔ f.base ((f ⁻¹ᵁ W i).ι.base x) ∈ V
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  have hr : Set.range (V.ι ∣_ W i).base = Set.range Vi.ι.base := by
    rw [range_morphismRestrict, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  rw [ProIsoDeligneSystem.congr_range hr]
  have : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W i).ι |>.obj F).IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion _ F
  obtain ⟨Ia, hIa, ha⟩ := proIsoDeligneSystem_properPushforward_single_affine fi Vi
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W i).ι).obj F) p
  have e : (D.system ⋙ properPushforwardBoundedCoherent f) ⋙
        restrictBoundedCoherentLift (W i).ι ≅
      (D.restrict (f ⁻¹ᵁ W i).ι Ui.ι hj).system ⋙ properPushforwardBoundedCoherent fi :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft D.system
      (properPushforwardRestrictIso f (W i)) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (D.restrictSystemIso (f ⁻¹ᵁ W i).ι Ui.ι hj).symm _
  refine ProIsoDeligneSystem.of_natIso e ?_
  refine (proIsoDeligneSystem_deligneSystemOfComplex_comp_iff Ui.ι _ _ _ _ _ _ _ _ _ _ _ _ _
    ?_).mpr ha
  exact (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W i).ι) (ComplexShape.up ℤ) p).app F

/-- **The main step of the first proof of [Stacks, Tag 0G4W].** Let `f : X ⟶ Y` be a proper
morphism of Noetherian schemes, `V ⊆ Y` open and `U = f⁻¹(V)`. For every `K` in
`D^b_{Coh}(𝒪_U)`, the image under `Rf_*` of the Deligne system of `K` is pro-isomorphic to a
Deligne system along `V ⟶ Y`.

Two out of three ([Stacks, Tag 0G4M], [Stacks, Tag 0G4Q]) and the truncation triangles reduce to
a coherent module in one degree, which is
`AlgebraicGeometry.proIsoDeligneSystem_properPushforward_single`. -/
public theorem proIsoDeligneSystem_properPushforward [IsNoetherian X] [IsNoetherian Y]
    [IsProper f] (V : Y.Opens) (K : BoundedCoherentDerived (f ⁻¹ᵁ V)) :
    ProIsoDeligneSystem V.ι
      ((DeligneSystem.values (f ⁻¹ᵁ V).ι).system K ⋙ properPushforwardBoundedCoherent f) := by
  have hI : (((Scheme.IdealSheafData.vanishingIdeal
      ⟨(V : Set Y)ᶜ, V.isOpen.isClosed_compl⟩).comap f).support : Set X) =
        (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
    rfl
  exact proIsoDeligneSystem_values_comp_of_truncGELE _
    (proIsoDeligneSystem_values_comp_of_single (f ⁻¹ᵁ V) _ _ hI
      (fun F _ p => proIsoDeligneSystem_properPushforward_single f V F p hI)) K

end Global

end AlgebraicGeometry

end
