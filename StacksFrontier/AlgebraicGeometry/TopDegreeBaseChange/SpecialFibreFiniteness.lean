module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.Limits.IntegralFamily
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DirectImageStructureSheafCommutesBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.NoetherianModelOfProperFlat
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafSurjectivityBaseChange
public import StacksFrontier.AlgebraicGeometry.ProperFibreDimensionNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FlatNeighbourhoodOfSpecialFibre
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimensionTotal
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.RingBaseCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.EventualFibreDimension

/-!
# Finiteness of `f_* 𝒪_X` for a proper flat family with one-dimensional fibres

The proof of [Stacks, Tag 0E7J] rests on a claim: for `X ⟶ Y ⟶ S` with `Y` and `S` affine,
`f : X ⟶ Y` proper with fibres of dimension at most one and `R¹ f_* 𝒪_X = 0`, and `X ⟶ S` flat
and locally of finite presentation, `f_* 𝒪_X` is an `𝒪_Y`-module of finite type. Nothing is
assumed of `Y ⟶ S`. This file proves the claim.

## The argument

The source embeds `Y` into the spectrum of a polynomial ring and then, after passing to finitely
many variables ([Stacks, Tag 0EX1]), descends to a Noetherian base and uses pseudo-coherence of
`RΓ(X, 𝒪_X)`. Here the descent step is replaced by [Stacks, Tag 0E7K]: over a Noetherian model
of `X ⟶ A^n_S ⟶ S` ([Stacks, Tags 01ZM, 081F, 04AI]) the fibres are still one-dimensional near
the image of `A^n_S` and `R¹` vanishes there ([Stacks, Tag 0E7G]), so formation of the direct
image of the structure sheaf commutes with the base change back to `A^n_S`, and on the model it
is coherent ([Stacks, Tag 02O5]).

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isFiniteType_of_pushforward_isFiniteType_of_isAffineHom`: finite type descends along an
  affine morphism.
* `topologicalKrullDim_fiber_comp_le_of_isAffineHom`: composing with an affine morphism whose
  composite is proper does not enlarge the fibres.
* `exists_isProper_comp_specMap_aeval`: properness over a polynomial ring in finitely many
  variables ([Stacks, Tag 0EX1]).
* `isFiniteType_directImageStructureSheaf_of_isAffine`: the claim.

## References

* [Stacks Project, Tag 0E7J](https://stacks.math.columbia.edu/tag/0E7J)
* [Stacks Project, Tag 0EX1](https://stacks.math.columbia.edu/tag/0EX1)
* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

/-! ### Finite type descends along an affine morphism -/

/-- **A quasi-coherent module whose direct image along an affine morphism is of finite type is of
finite type.** Over an affine open `V` of the target, `Γ(F, p ⁻¹ V)` is a finite `Γ(Y, V)`-module,
hence a finite `Γ(X, p ⁻¹ V)`-module, the action of `Γ(Y, V)` being the restriction of that of
`Γ(X, p ⁻¹ V)`. -/
theorem isFiniteType_of_pushforward_isFiniteType_of_isAffineHom {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsAffineHom p] (F : X.Modules) [F.IsQuasicoherent]
    (h : ((Scheme.Modules.pushforward p).obj F).IsFiniteType) : F.IsFiniteType := by
  have hcov : IsOpenCover fun V : Y.affineOpens ↦ p ⁻¹ᵁ (V : Y.Opens) := by
    refine IsOpenCover.mk ?_
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  refine CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn F
    (fun V : Y.affineOpens ↦ p ⁻¹ᵁ (V : Y.Opens)) hcov
    (fun V ↦ IsAffineHom.isAffine_preimage (V : Y.Opens) V.2) fun V ↦ ?_
  have hW : IsAffineOpen (p ⁻¹ᵁ (V : Y.Opens)) := IsAffineHom.isAffine_preimage _ V.2
  have hsec : Module.Finite Γ(X, p ⁻¹ᵁ (V : Y.Opens)) Γ(F, p ⁻¹ᵁ (V : Y.Opens)) := by
    let _ : Algebra Γ(Y, (V : Y.Opens)) Γ(X, p ⁻¹ᵁ (V : Y.Opens)) := (p.app V).hom.toAlgebra
    let _ : Module Γ(Y, (V : Y.Opens)) Γ(F, p ⁻¹ᵁ (V : Y.Opens)) :=
      inferInstanceAs (Module Γ(Y, (V : Y.Opens)) Γ((Scheme.Modules.pushforward p).obj F, V))
    have : IsScalarTower Γ(Y, (V : Y.Opens)) Γ(X, p ⁻¹ᵁ (V : Y.Opens))
        Γ(F, p ⁻¹ᵁ (V : Y.Opens)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have : Module.Finite Γ(Y, (V : Y.Opens)) Γ(F, p ⁻¹ᵁ (V : Y.Opens)) :=
      CoherentFinite.finite_sections ((Scheme.Modules.pushforward p).obj F) V.2
    exact Module.Finite.of_restrictScalars_finite Γ(Y, (V : Y.Opens)) Γ(X, p ⁻¹ᵁ (V : Y.Opens))
      Γ(F, p ⁻¹ᵁ (V : Y.Opens))
  exact CoherentTFAE.isFiniteTildeOn_of_finite_specModule F _ hW
    (Module.Finite.equiv (CoherentFinite.specSectionsEquiv F hW).symm)

/-! ### Fibre dimension after composing with an affine morphism -/

/-- A fibre is a subspace of the corresponding fibre of a composite. -/
alias topologicalKrullDim_fiber_le_fiber_comp :=
  EventualFibreDimension.topologicalKrullDim_fiber_le_comp

/-- The global sections of a proper scheme over a field `K` form a finite `K`-algebra. -/
private theorem finite_ΓSpecIso_inv_comp_appTop_of_isProper (K : Type u) [Field K] {F : Scheme.{u}}
    (πF : F ⟶ Spec (.of K)) [IsProper πF] :
    ((Scheme.ΓSpecIso (.of K)).inv ≫ πF.appTop).hom.Finite := by
  let ρ : CommRingCat.of K ⟶ Γ(F, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ πF.appTop
  have := TopDegreeFiniteType.moduleFinite_cohomology_ringBase_of_isFiniteType_rightDerived
    K πF (SheafOfModules.unit F.ringCatSheaf) 0
    (TopDegreeFiniteType.isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian πF
      (SheafOfModules.unit F.ringCatSheaf) 0)
  let e := (ModuleCat.restrictScalars ρ.hom).mapIso
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections F).rightDerivedZeroIsoSelf).app
      (SheafOfModules.unit F.ringCatSheaf))
  exact show Module.Finite K ((ModuleCat.restrictScalars ρ.hom).obj
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections F).obj
        (SheafOfModules.unit F.ringCatSheaf))) from Module.Finite.equiv e.toLinearEquiv

/-- The spectrum of a finite algebra over a field has dimension at most zero. -/
private theorem topologicalKrullDim_spec_le_zero_of_finite {K : Type u} [Field K]
    {R : CommRingCat.{u}} (ρ : CommRingCat.of K ⟶ R) (hρ : ρ.hom.Finite) :
    topologicalKrullDim (Spec R) ≤ 0 := by
  let _ : Algebra K R := ρ.hom.toAlgebra
  have : Module.Finite K R := hρ
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  exact topologicalKrullDim_zero_of_discreteTopology (PrimeSpectrum R)

/-- **The fibres of `f ≫ p` for `p` affine and `f ≫ p` proper are no bigger than those of `f`.**
Let `f : X ⟶ Y` have fibres of dimension at most `d` and let `p : Y ⟶ A` be affine with `f ≫ p`
proper. Then every fibre of `f ≫ p` has dimension at most `d`.

The fibre `F` of `f ≫ p` over `a` is proper over `κ(a)`, so `Γ(F, 𝒪_F)` is a finite
`κ(a)`-algebra ([Stacks, Tag 02O6]) and `Spec Γ(F, 𝒪_F)` has dimension zero. The map
`F ⟶ p⁻¹(a)` to the affine fibre of `p` factors through `F ⟶ Spec Γ(F, 𝒪_F)`, whose fibres are
therefore subspaces of fibres of `F ⟶ p⁻¹(a)`, i.e. of fibres of `f` ([Stacks, Tag 02FY]); the
dimension formula over a field ([Stacks, Tag 0B2L]) concludes. -/
theorem topologicalKrullDim_fiber_comp_le_of_isAffineHom {X Y A : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ A) [IsAffineHom p] [IsProper (f ≫ p)] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) (a : A) :
    topologicalKrullDim ((f ≫ p).fiber a) ≤ (d : WithBot ℕ∞) := by
  let K : Type u := A.residueField a
  let F := (f ≫ p).fiber a
  let πF : F ⟶ Spec (.of K) := (f ≫ p).fiberToSpecResidueField a
  have _ : IsProper πF := isProper_fiberToSpecResidueField (f ≫ p) a
  have _ : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  let Ua := p.fiber a
  have _ : IsAffineHom (p.fiberToSpecResidueField a) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback p (A.fromSpecResidueField a)) inferInstance
  have _ : IsAffine Ua := isAffine_of_isAffineHom (p.fiberToSpecResidueField a)
  let fa : F ⟶ Ua := pullback.lift (pullback.fst (f ≫ p) (A.fromSpecResidueField a) ≫ f)
    (pullback.snd (f ≫ p) (A.fromSpecResidueField a))
    ((Category.assoc _ _ _).trans pullback.condition)
  have hfa2 : fa ≫ pullback.snd p (A.fromSpecResidueField a) =
      pullback.snd (f ≫ p) (A.fromSpecResidueField a) := pullback.lift_snd _ _ _
  have hfa1 : fa ≫ pullback.fst p (A.fromSpecResidueField a) =
      pullback.fst (f ≫ p) (A.fromSpecResidueField a) ≫ f := pullback.lift_fst _ _ _
  have hsq : IsPullback (pullback.fst (f ≫ p) (A.fromSpecResidueField a)) fa f
      (pullback.fst p (A.fromSpecResidueField a)) :=
    IsPullback.of_bot (by
        have h := IsPullback.of_hasPullback (f ≫ p) (A.fromSpecResidueField a)
        rwa [← hfa2] at h) hfa1.symm
      (IsPullback.of_hasPullback p (A.fromSpecResidueField a))
  let ρ : CommRingCat.of K ⟶ Γ(F, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ πF.appTop
  have hfinΓ : ρ.hom.Finite := finite_ΓSpecIso_inv_comp_appTop_of_isProper K πF
  let P := Spec Γ(F, ⊤)
  let t : F ⟶ P := F.toSpecΓ
  let pP : P ⟶ Spec (.of K) := Spec.map ρ
  have hpP : LocallyOfFiniteType pP :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hfinΓ.to_finiteType
  have htp : t ≫ pP = πF := by
    simp only [t, pP, ρ, Spec.map_comp]
    rw [← Scheme.toSpecΓ_naturality_assoc, AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  let m : P ⟶ Ua := Spec.map fa.appTop ≫ Ua.isoSpec.inv
  have htm : t ≫ m = fa := by
    simp only [t, m]
    rw [← Scheme.toSpecΓ_naturality_assoc]
    exact (congrArg (fa ≫ ·) Ua.isoSpec.hom_inv_id).trans (Category.comp_id _)
  have hfib : ∀ x : F, topologicalKrullDimAt (t.fiber (t x)) (t.asFiber x) ≤
      (d : WithBot ℕ∞) := fun x =>
    (topologicalKrullDimAt_le_topologicalKrullDim _).trans
      ((topologicalKrullDim_fiber_le_fiber_comp t m (t x)).trans (by
        rw [htm]
        exact topologicalKrullDim_fiber_le_of_isPullback hsq d _ (hdim _)))
  simpa using topologicalKrullDim_le_add_of_topologicalKrullDimAt_fiber_le K πF pP t htp hfib
    (topologicalKrullDim_spec_le_zero_of_finite ρ hfinΓ)

/-! ### Properness over a polynomial ring in finitely many variables -/

/-- **Properness descends to a finitely generated subalgebra** ([Stacks, Tag 0EX1]). A proper
morphism to `Spec A` whose source is of finite type over `R` is already proper over the spectrum
of a finitely generated `R`-subalgebra of `A`: `Spec A` is the cofiltered limit of the spectra of
those subalgebras (`Algebra.isColimitAdjoinFinsetCocone`). -/
theorem exists_isProper_comp_specMap_adjoin (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    [LocallyOfFiniteType (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    ∃ s : Finset A, IsProper (f ≫ Spec.map (CommRingCat.ofHom
      (Algebra.adjoin R (s : Set A)).val.toRingHom)) := by
  let Dg := (Algebra.adjoinFinsetDiagram R A).op ⋙ Scheme.Spec
  let c := Scheme.Spec.mapCone (Algebra.adjoinFinsetCocone R A).op
  let t : Dg ⟶ (Functor.const (Finset A)ᵒᵖ).obj (Spec (.of R)) :=
    { app := fun s ↦ Spec.map (CommRingCat.ofHom
        (algebraMap R (Algebra.adjoin R (s.unop : Set A))))
      naturality := by
        intro i j g
        dsimp [Dg, Algebra.adjoinFinsetDiagram]
        rw [← Spec.map_comp]
        rfl }
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (Algebra.isColimitAdjoinFinsetCocone R A).op
  let p := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hp : c.π ≫ t = (Functor.const (Finset A)ᵒᵖ).map p := by
    ext s
    change Spec.map (CommRingCat.ofHom (Algebra.adjoin R (s.unop : Set A)).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s.unop : Set A)))) = p
    rw [← Spec.map_comp]
    rfl
  have _ : ∀ {i j : (Finset A)ᵒᵖ} (g : i ⟶ j), IsAffineHom (Dg.map g) := by
    intro i j g
    dsimp [Dg]
    infer_instance
  have _ : ∀ i : (Finset A)ᵒᵖ, CompactSpace (Dg.obj i) := by
    intro i
    change CompactSpace (PrimeSpectrum (Algebra.adjoin R (i.unop : Set A)))
    infer_instance
  have _ : ∀ i : (Finset A)ᵒᵖ, QuasiSeparatedSpace (Dg.obj i) := by
    intro i
    change QuasiSeparatedSpace (PrimeSpectrum (Algebra.adjoin R (i.unop : Set A)))
    infer_instance
  have : IsProper (show X ⟶ c.pt from f) := inferInstanceAs (IsProper f)
  obtain ⟨s, hs⟩ :=
    eventually_isProper_comp_π_app_of_isLimit Dg t c hc p hp (f ≫ p) f rfl
  exact ⟨s.unop, hs s (𝟙 s)⟩

/-- **Properness over a polynomial ring in finitely many variables.** A proper morphism to
`Spec A` whose source is of finite type over `R` is proper over `Spec R[x_a : a ∈ s]` for some
finite `s ⊆ A`, through `x_a ↦ a`. The morphism `Spec A ⟶ Spec R[x_a]` factors through the
closed immersion of the spectrum of the subalgebra generated by `s`. -/
theorem exists_isProper_comp_specMap_aeval (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    [LocallyOfFiniteType (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    ∃ s : Finset A, IsProper (f ≫ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
      (MvPolynomial.aeval (fun a : (s : Set A) => (a : A)) :
        MvPolynomial (s : Set A) R →ₐ[R] A)))) := by
  obtain ⟨s, hs⟩ := exists_isProper_comp_specMap_adjoin R A f
  refine ⟨s, ?_⟩
  let ψ : MvPolynomial (s : Set A) R →ₐ[R] Algebra.adjoin R (s : Set A) :=
    MvPolynomial.aeval fun a => ⟨a, Algebra.subset_adjoin a.2⟩
  have hcomp : (MvPolynomial.aeval (fun a : (s : Set A) => (a : A)) :
      MvPolynomial (s : Set A) R →ₐ[R] A) = (Algebra.adjoin R (s : Set A)).val.comp ψ :=
    MvPolynomial.algHom_ext fun a => by simp [ψ]
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    rw [← Subtype.range_coe (s := (s : Set A)), Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨P, rfl⟩ := hx
    exact ⟨P, Subtype.ext (DFunLike.congr_fun hcomp P).symm⟩
  have hfac : AlgHom.toRingHom (MvPolynomial.aeval (fun a : (s : Set A) => (a : A)) :
      MvPolynomial (s : Set A) R →ₐ[R] A) =
      (Algebra.adjoin R (s : Set A)).val.toRingHom.comp ψ.toRingHom := by
    rw [hcomp]
    rfl
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hψ
  rw [hfac, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
  infer_instance

/-! ### Finiteness of `f_* 𝒪_X` over an affine base -/

/-- The direct image of the structure sheaf along a proper morphism to a locally Noetherian
scheme is of finite type. -/
private theorem isFiniteType_directImageStructureSheaf_of_isProper_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] :
    (directImageStructureSheaf f).IsFiniteType := by
  have := TopDegreeFiniteType.isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian
    f (SheafOfModules.unit X.ringCatSheaf) 0
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.app
      (SheafOfModules.unit X.ringCatSheaf))

/-- **Finite type of `f_* 𝒪` is inherited by a base change** along the cartesian squares `hw`
and `hY`, for `f` proper over a locally Noetherian scheme with one-dimensional fibres,
`R¹ f_* 𝒪 = 0` and `f ≫ q` flat ([Stacks, Tag 0E7K]). -/
private theorem isFiniteType_directImageStructureSheaf_of_isPullback {X Y S X' Y' S' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (hw : IsPullback g' f' f g)
    {q' : Y' ⟶ S'} {q : Y ⟶ S} {k : S' ⟶ S} (hY : IsPullback g q' q k)
    [Flat (f ≫ q)] [IsProper f] [IsLocallyNoetherian Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) :
    (directImageStructureSheaf f').IsFiniteType := by
  have h1 : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g).obj
      (Scheme.unitModule X)).IsFiniteType :=
    _root_.Stacks.Modules.isFiniteType_pullback g (directImageStructureSheaf f)
      (isFiniteType_directImageStructureSheaf_of_isProper_of_isLocallyNoetherian f)
  have h2 : ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
      (Scheme.unitModule X))).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (@asIso _ _ _ _ ((AffinePushforward.baseChangeNatTrans hw.w).app
        (Scheme.unitModule X)) (isIso_baseChangeNatTrans_structureSheaf_of_flat hw hY hdim hR))
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.pushforward f').mapIso (Scheme.Modules.pullbackUnitIso g'))

/-- **A neighbourhood of the image of a base change with one-dimensional fibres and vanishing
`R¹`.** If `f` is proper and its base change `f'` along `g` has one-dimensional fibres and
`R¹ f'_* 𝒪 = 0`, then the image of `g` has an open neighbourhood `V` over which `f` has
one-dimensional fibres and `R¹ f_* 𝒪` vanishes. -/
private theorem exists_range_subset_fiberDimension_le_one_isZero {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hdim : ∀ y : Y', topologicalKrullDim (f'.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f')) :
    ∃ V : Y.Opens, Set.range g ⊆ V ∧
      (∀ y ∈ V, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) := by
  choose Wa hWa using fun y : Y' => ProperFibreDimension.exists_affineOpen_fiberDimension_le f
    (g y) 1 (topologicalKrullDim_fiber_le_of_isPullback' sq 1 y (hdim y))
  let W : Y.Opens := ⨆ y, Wa y
  have hdimW : ∀ z ∈ W, topologicalKrullDim (f.fiber z) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro z hz
    obtain ⟨y, hy⟩ := Opens.mem_iSup.mp hz
    exact (hWa y).2.2.2.2.2.2 z hy
  have hrW : Set.range g ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Opens.mem_iSup.mpr ⟨y, (hWa y).1⟩
  obtain ⟨V, hVW, hrV, hres, -⟩ := exists_isOpen_firstDirectImage_vanishes_of_factor f W
    hdimW sq (IsOpenImmersion.lift W.ι g hrW) (IsOpenImmersion.lift_fac _ _ _) hR
  exact ⟨V, hrV, fun z hz => hdimW z (hVW hz), hres⟩

/-- **The claim over a Noetherian model.** Let `h : X ⟶ A` be proper with one-dimensional fibres
and `R¹ h_* 𝒪_X = 0`, over affine `A` and `T`, with `A ⟶ T` locally of finite presentation and
`X ⟶ T` flat and locally of finite presentation. Then `h_* 𝒪_X` is of finite type. -/
private theorem isFiniteType_directImageStructureSheaf_of_flat {X A T : Scheme.{u}} (h : X ⟶ A)
    (qA : A ⟶ T) [IsAffine A] [IsAffine T] [IsProper h] [LocallyOfFinitePresentation qA]
    [LocallyOfFinitePresentation (h ≫ qA)] [Flat (h ≫ qA)]
    (hdimh : ∀ a : A, topologicalKrullDim (h.fiber a) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hRh : IsZero (firstDirectImageStructureSheaf h)) :
    (directImageStructureSheaf h).IsFiniteType := by
  obtain ⟨S₀, Y₀, X₀, q₀, f₀, π, πY, πX, hN, hA0, hq0, hf0, hflat0, hsqY, hsqX⟩ :=
    exists_noetherianModel h qA
  have _ : IsNoetherian S₀ := hN
  have _ : LocallyOfFinitePresentation q₀ := hq0
  have _ : IsProper f₀ := hf0
  have _ : Flat (f₀ ≫ q₀) := hflat0
  have _ : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian q₀
  obtain ⟨V₀, hrV, hdimW, hres⟩ :=
    exists_range_subset_fiberDimension_le_one_isZero f₀ hsqX hdimh hRh
  let f₁ := f₀ ∣_ V₀
  let q₁ := V₀.ι ≫ q₀
  have _ : IsProper f₁ := MorphismProperty.of_isPullback (isPullback_morphismRestrict f₀ V₀).flip
    inferInstance
  have _ : Flat (f₁ ≫ q₁) := by
    simp only [f₁, q₁]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have hdim₁ : ∀ v : V₀.toScheme, topologicalKrullDim (f₁.fiber v) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_morphismRestrict_le f₀ V₀ 1 fun y hy => hdimW y hy
  have hR₁ : IsZero (firstDirectImageStructureSheaf f₁) :=
    IsZero.of_iso hres (firstDirectImageRestrictIso f₀ V₀)
  let πY₁ := IsOpenImmersion.lift V₀.ι πY (by rwa [Scheme.Opens.range_ι])
  have hπY₁ : πY₁ ≫ V₀.ι = πY := IsOpenImmersion.lift_fac _ _ _
  have hrX : Set.range πX ⊆ Set.range (f₀ ⁻¹ᵁ V₀).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f₀ (πX x) ∈ V₀
    rw [← Scheme.Hom.comp_apply, hsqX.w, Scheme.Hom.comp_apply]
    exact hrV ⟨h x, rfl⟩
  let πX₁ := IsOpenImmersion.lift (f₀ ⁻¹ᵁ V₀).ι πX hrX
  have hπX₁ : πX₁ ≫ (f₀ ⁻¹ᵁ V₀).ι = πX := IsOpenImmersion.lift_fac _ _ _
  have hcomm : πX₁ ≫ f₁ = h ≫ πY₁ := by
    rw [← cancel_mono V₀.ι]
    simp only [f₁, Category.assoc, morphismRestrict_ι, hπY₁]
    rw [← Category.assoc, hπX₁]
    exact hsqX.w
  have hX₁ : IsPullback πX₁ h f₁ πY₁ :=
    IsPullback.of_right (by rwa [hπX₁, hπY₁]) hcomm
      (isPullback_morphismRestrict f₀ V₀).flip
  have hY₁ : IsPullback πY₁ qA q₁ π := by
    simpa only [Category.id_comp] using
      ((IsPullback.of_horiz_isIso_mono (fst := 𝟙 A) (snd := πY₁) (f := πY) (g := V₀.ι)
        ⟨by rw [Category.id_comp, hπY₁]⟩).flip).paste_vert hsqY
  exact isFiniteType_directImageStructureSheaf_of_isPullback hX₁ hY₁ hdim₁ hR₁

/-- **[Stacks, Tag 0E7J], the claim of the proof, over an affine target.** Let `X ⟶ U ⟶ T` with
`U` and `T` affine, `f : X ⟶ U` proper with fibres of dimension at most one and
`R¹ f_* 𝒪_X = 0`, and `X ⟶ T` flat and locally of finite presentation. Then `f_* 𝒪_X` is an
`𝒪_U`-module of finite type.

As in the source, `X ⟶ U` is first replaced by a proper morphism `h : X ⟶ A` to the spectrum of
a polynomial ring over `Γ(T, 𝒪_T)` in finitely many variables through which it factors by an
affine morphism (`exists_isProper_comp_specMap_aeval`, [Stacks, Tag 0EX1]); `h` still has
one-dimensional fibres (`topologicalKrullDim_fiber_comp_le_of_isAffineHom`) and vanishing
`R¹ h_* 𝒪_X`. The triangle `X ⟶ A ⟶ T` is the base change of one over a Noetherian affine
scheme (`exists_noetherianModel`, [Stacks, Tags 01ZM, 081F, 04AI]); over a neighbourhood of the
image of `A` the model has one-dimensional fibres and vanishing `R¹`
(`exists_isOpen_firstDirectImage_vanishes_of_factor`), so formation of its `f_* 𝒪` commutes with
the base change to `A` ([Stacks, Tag 0E7K], `isIso_baseChangeNatTrans_structureSheaf_of_flat`),
and there it is coherent ([Stacks, Tag 02O5]). Hence `h_* 𝒪_X` is of finite type, and so is
`f_* 𝒪_X`, whose direct image along the affine `U ⟶ A` it is. -/
theorem isFiniteType_directImageStructureSheaf_of_isAffine {X U T : Scheme.{u}} (f : X ⟶ U)
    (q : U ⟶ T) [IsAffine U] [IsAffine T] [IsProper f] [Flat (f ≫ q)]
    [LocallyOfFinitePresentation (f ≫ q)]
    (hdim : ∀ y : U, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) :
    (directImageStructureSheaf f).IsFiniteType := by
  let _ : Algebra Γ(T, ⊤) Γ(U, ⊤) := q.appTop.hom.toAlgebra
  let f' : X ⟶ Spec (.of Γ(U, ⊤)) := f ≫ U.isoSpec.hom
  have hq : U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) Γ(U, ⊤))) =
      q ≫ T.isoSpec.hom := Scheme.isoSpec_hom_naturality q
  have _ : LocallyOfFiniteType
      (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) Γ(U, ⊤)))) := by
    simp only [f', Category.assoc]
    rw [hq, ← Category.assoc]
    infer_instance
  obtain ⟨s, hs⟩ := exists_isProper_comp_specMap_aeval Γ(T, ⊤) Γ(U, ⊤) f'
  let P := MvPolynomial (s : Set Γ(U, ⊤)) Γ(T, ⊤)
  let e : P →ₐ[Γ(T, ⊤)] Γ(U, ⊤) := MvPolynomial.aeval fun a => (a : Γ(U, ⊤))
  let A := Spec (.of P)
  let p : U ⟶ A := U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
  let qA : A ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) P)) ≫ T.isoSpec.inv
  have hpq : p ≫ qA = q := by
    simp only [p, qA, Category.assoc]
    rw [← Category.assoc (Spec.map _), ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show e.toRingHom.comp (algebraMap Γ(T, ⊤) P) = algebraMap Γ(T, ⊤) Γ(U, ⊤) from
        e.comp_algebraMap, ← Category.assoc, hq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  let h : X ⟶ A := f ≫ p
  have _ : IsProper h := by
    change IsProper (f ≫ U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
    rwa [← Category.assoc]
  have _ : IsAffineHom p := isAffineHom_of_isAffine p
  have hhq : h ≫ qA = f ≫ q := by simp only [h, Category.assoc, hpq]
  have _ : Flat (h ≫ qA) := by
    rw [hhq]
    infer_instance
  have _ : LocallyOfFinitePresentation (h ≫ qA) := by
    rw [hhq]
    infer_instance
  have _ : LocallyOfFinitePresentation qA := by
    have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) P))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
        (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    infer_instance
  have hRh : IsZero (firstDirectImageStructureSheaf h) :=
    isZero_rightDerivedPlus_pushforward_of_isZero_cohomology h 1 _
      (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward f 1 _ hR)
  have hfth : (directImageStructureSheaf h).IsFiniteType :=
    isFiniteType_directImageStructureSheaf_of_flat h qA
      (topologicalKrullDim_fiber_comp_le_of_isAffineHom f p 1 hdim) hRh
  have hqc : (directImageStructureSheaf f).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs f _
  exact isFiniteType_of_pushforward_isFiniteType_of_isAffineHom p _ <|
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.pushforwardComp f p).app (Scheme.unitModule X)).symm

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
