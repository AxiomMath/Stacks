module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupOpenCover
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite

/-!
# The contraction of an exceptional curve is of finite presentation over the base

Let `b : X ⟶ X'` contract an exceptional curve of the first kind in `X`, and let `X` be
at-worst-nodal of relative dimension one over the spectrum of a Noetherian ring `R` through
`X'`. Then `X' ⟶ Spec R` is itself locally of finite presentation. This is the finiteness half
of [Stacks, Tag 0CDF].

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_of_isContractionOfExceptionalCurve`: the
  statement above.

## References

* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
* [Stacks Project, Tag 0EX1](https://stacks.math.columbia.edu/tag/0EX1)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### `A` as the filtered colimit of its finitely generated subalgebras -/

/-- The diagram of finitely generated `R`-subalgebras of an `R`-algebra `A`, indexed by the
finite subsets of `A`. -/
private def finiteSubalgebraDiagram (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Finset A ⥤ CommRingCat.{u} where
  obj s := .of (Algebra.adjoin R (s : Set A))
  map {s t} h := CommRingCat.ofHom (Subalgebra.inclusion
    (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom h)))).toRingHom

/-- The cocone on `AlgebraicGeometry.finiteSubalgebraDiagram` with vertex `A`, whose legs are
the inclusions of the subalgebras. -/
private def finiteSubalgebraCocone (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Cocone (finiteSubalgebraDiagram R A) where
  pt := .of A
  ι := { app := fun s ↦ CommRingCat.ofHom (Algebra.adjoin R (s : Set A)).val.toRingHom }

/-- An algebra is the filtered colimit of its finitely generated subalgebras. -/
private def finiteSubalgebraIsColimit (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    IsColimit (finiteSubalgebraCocone R A) := by
  letI := reflectsColimit_of_reflectsIsomorphisms
    (finiteSubalgebraDiagram R A) (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · exact fun a => ⟨{a}, ⟨a, Algebra.subset_adjoin (Finset.mem_singleton_self a)⟩, rfl⟩
  · exact fun s a b hab => ⟨s, 𝟙 s, Subtype.ext hab⟩

/-- **Properness descends to a finitely generated subalgebra.** A proper morphism to `Spec A`
whose source is locally of finite type over `Spec R` is already proper over the spectrum of a
finitely generated `R`-subalgebra of `A`. This is a case of [Stacks, Tag 0EX1]. -/
private theorem exists_isProper_over_finiteSubalgebra (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    [LocallyOfFiniteType (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    ∃ s : Finset A, IsProper (f ≫ Spec.map (CommRingCat.ofHom
      (Algebra.adjoin R (s : Set A)).val.toRingHom)) := by
  let Dg := (finiteSubalgebraDiagram R A).op ⋙ Scheme.Spec
  let c := Scheme.Spec.mapCone (finiteSubalgebraCocone R A).op
  let t : Dg ⟶ (Functor.const (Finset A)ᵒᵖ).obj (Spec (.of R)) :=
    { app := fun s ↦ Spec.map (CommRingCat.ofHom
        (algebraMap R (Algebra.adjoin R (s.unop : Set A))))
      naturality := by
        intro i j g
        dsimp [Dg, finiteSubalgebraDiagram]
        rw [← Spec.map_comp]
        rfl }
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (finiteSubalgebraIsColimit R A).op
  let p := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hp : c.π ≫ t = (Functor.const (Finset A)ᵒᵖ).map p := by
    ext s
    show Spec.map (CommRingCat.ofHom (Algebra.adjoin R (s.unop : Set A)).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s.unop : Set A)))) = p
    rw [← Spec.map_comp]
    rfl
  let : ∀ {i j : (Finset A)ᵒᵖ} (g : i ⟶ j), IsAffineHom (Dg.map g) := by
    intro i j g
    dsimp [Dg]
    infer_instance
  let : ∀ i : (Finset A)ᵒᵖ, CompactSpace (Dg.obj i) := by
    intro i
    show CompactSpace (PrimeSpectrum (Algebra.adjoin R (i.unop : Set A)))
    infer_instance
  let : ∀ i : (Finset A)ᵒᵖ, QuasiSeparatedSpace (Dg.obj i) := by
    intro i
    show QuasiSeparatedSpace (PrimeSpectrum (Algebra.adjoin R (i.unop : Set A)))
    infer_instance
  have : IsProper (show Y ⟶ c.pt from f) := inferInstanceAs (IsProper f)
  obtain ⟨s, hs⟩ :=
    eventually_isProper_comp_π_app_of_isLimit Dg t c hc p hp (f ≫ p) f rfl
  exact ⟨s.unop, hs s (𝟙 s)⟩

/-! ### The affine case -/

/-- **The affine case.** Let `R` be a Noetherian ring. If `b : X ⟶ X'` contracts an exceptional
curve, `X'` is affine and `X` is locally of finite type over `Spec R` through `b`, then `X'` is
locally of finite type over `Spec R`. -/
private theorem locallyOfFiniteType_of_contraction_of_isAffine
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X X' : Scheme.{u}} [IsAffine X']
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b)
    (f : X' ⟶ Spec (.of R)) [LocallyOfFiniteType (b ≫ f)] :
    LocallyOfFiniteType f := by
  let φ : CommRingCat.of R ⟶ Γ(X', ⊤) := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop
  let : Algebra R Γ(X', ⊤) := φ.hom.toAlgebra
  have hf : X'.toSpecΓ ≫ Spec.map φ = f := by
    apply ext_to_Spec
    show (Scheme.ΓSpecIso (.of R)).inv ≫ (X'.toSpecΓ ≫ Spec.map φ).appTop = φ
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : IsProper b := hb.isProper
  have : IsIso b.appTop := isIso_appTop_of_isContractionOfExceptionalCurve hb
  let : LocallyOfFiniteType ((b ≫ X'.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(X', ⊤)))) := by
    show LocallyOfFiniteType ((b ≫ X'.toSpecΓ) ≫ Spec.map φ)
    simpa only [Category.assoc, hf] using inferInstanceAs (LocallyOfFiniteType (b ≫ f))
  obtain ⟨s, hs⟩ := exists_isProper_over_finiteSubalgebra R Γ(X', ⊤) (b ≫ X'.toSpecΓ)
  set B := Algebra.adjoin R (s : Set Γ(X', ⊤)) with hBdef
  set ψ : CommRingCat.of B ⟶ Γ(X', ⊤) := CommRingCat.ofHom B.val.toRingHom with hψdef
  let : Algebra.FiniteType R B := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hfin := finiteGlobalSectionsOfProper B inferInstance ((b ≫ X'.toSpecΓ) ≫ Spec.map ψ) hs
  have hkey : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      ((b ≫ X'.toSpecΓ) ≫ Spec.map ψ).appTop = ψ ≫ b.appTop := by
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Iso.inv_hom_id_assoc]
  have h1 : (ψ ≫ b.appTop).hom.Finite := by
    rw [← hkey]
    exact hfin.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2)
  have h2 : ψ.hom.Finite := by
    rw [show ψ = (ψ ≫ b.appTop) ≫ CategoryTheory.inv b.appTop by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    exact (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (CategoryTheory.inv b.appTop)).2).comp h1
  have hft : (algebraMap R Γ(X', ⊤)).FiniteType := by
    have h3 := h2.finiteType.comp
      ((RingHom.finiteType_algebraMap (A := R) (B := ↥B)).mpr inferInstance)
    rwa [show ψ.hom.comp (algebraMap R B) = algebraMap R Γ(X', ⊤) from
      B.val.comp_algebraMap] at h3
  have : LocallyOfFiniteType (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{u})).mpr hft
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← hf]
  exact (MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType.{u}) X'.toSpecΓ
    (Spec.map φ)).mpr inferInstance

/-! ### Restricting a contraction to an open neighbourhood of its centre -/

/-- **A contraction restricts to a contraction.** On an open `U` containing the centre, the
restriction of a contraction contracts the restricted ideal sheaf. This uses that blowing up
commutes with the flat base change `U ⟶ X'` ([Stacks, Tag 0805]). -/
private theorem contraction_restrict {X X' : Scheme.{u}} (D : X.IdealSheafData) (b : X ⟶ X')
    (z : X') (hz : IsClosed ({z} : Set X')) [IsNoetherian X']
    (hreg : IsRegularLocalRing (X'.presheaf.stalk z))
    (hdim : ringKrullDim (X'.presheaf.stalk z) = 2)
    (hD : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (ε : X ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')))
    (hε : ε.hom ≫
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')) = b)
    (U : X'.Opens) (hzU : z ∈ U) :
    IsContractionOfExceptionalCurve (D.comap (b ⁻¹ᵁ U).ι) (b ∣_ U) := by
  let zU : U := ⟨z, hzU⟩
  have hz' : IsClosed ({zU} : Set U) := by
    have hpre : (Subtype.val : U → X') ⁻¹' ({z} : Set X') = {zU} := by
      ext y
      show (y : X') = z ↔ y = zU
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact hpre ▸ hz.preimage continuous_subtype_val
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨{zU}, hz'⟩ : Closeds U)
  have hIJ : I.comap U.ι = J := pointIdeal_comap_open z hz U hzU hz'
  have : IsRegularLocalRing (U.toScheme.presheaf.stalk zU) := by
    let := hreg
    exact IsRegularLocalRing.of_ringEquiv (U.stalkIso zU).commRingCatIsoToRingEquiv.symm
  have : NoetherianSpace X' := IsNoetherian.noetherianSpace
  have : NoetherianSpace {x : X' // x ∈ U} := NoetherianSpace.set _
  have : CompactSpace U.toScheme := by
    show CompactSpace {x : X' // x ∈ U}
    exact NoetherianSpace.compactSpace _
  have : IsNoetherian U.toScheme := ⟨⟩
  refine ⟨inferInstance, zU, hz', inferInstance, ?_, ?_, ?_⟩
  · rw [(U.stalkIso zU).commRingCatIsoToRingEquiv.ringKrullDim]
    exact hdim
  · show D.comap (b ⁻¹ᵁ U).ι = J.comap (b ∣_ U)
    rw [hD, ← Scheme.IdealSheafData.comap_comp, ← hIJ, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  · obtain ⟨h, hh⟩ := exists_isPullback_blowUpToBase_comap U.ι I
    have hlocal : IsPullback (b ∣_ U) ((b ⁻¹ᵁ U).ι ≫ ε.hom) U.ι (blowUpToBase I) :=
      (isPullback_morphismRestrict b U).of_iso (Iso.refl _) (Iso.refl _) ε (Iso.refl _)
        (by simp) (by simp) (by simp) (by simpa using hε.symm)
    let eU := hlocal.isoPullback ≪≫ hh.isoPullback.symm
    have hcomm : eU.hom ≫ blowUpToBase (I.comap U.ι) = b ∣_ U := by
      dsimp [eU]
      rw [Category.assoc, hh.isoPullback_inv_fst, hlocal.isoPullback_hom_fst]
    show ∃ eU : (b ⁻¹ᵁ U).toScheme ≅ blowUp J, eU.hom ≫ blowUpToBase J = b ∣_ U
    rw [← hIJ]
    exact ⟨eU, hcomm⟩

/-! ### Tag 0CDF: the finiteness half -/

/-- **[Stacks, Tag 0CDF], the finiteness half.** Let `b : X ⟶ X'` contract an exceptional curve
of the first kind in `X`, and suppose the composite `X ⟶ X' ⟶ Spec R` is at-worst-nodal of
relative dimension one over a Noetherian ring `R`. Then `X' ⟶ Spec R` is locally of finite
presentation. -/
public theorem locallyOfFinitePresentation_of_isContractionOfExceptionalCurve
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f')) :
    LocallyOfFinitePresentation f' := by
  have _ : projectiveLineProj k ≅ D.subscheme := e
  have : LocallyOfFinitePresentation (b ≫ f') := locallyOfFinitePresentation hf.1.1
  have := hb.isNoetherian
  obtain ⟨z, hz, hreg, hdim, hD, ε, hε⟩ := hb.exists_blowUp_iso
  obtain ⟨U, hUaff, hzU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X') (U := ⊤) (x := z) trivial
  have : IsAffine U.toScheme := hUaff
  have hc : IsContractionOfExceptionalCurve (D.comap (b ⁻¹ᵁ U).ι) (b ∣_ U) :=
    contraction_restrict D b z hz hreg hdim hD ε hε U hzU
  have : LocallyOfFiniteType ((b ∣_ U) ≫ U.ι ≫ f') := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have hU : LocallyOfFiniteType (U.ι ≫ f') :=
    locallyOfFiniteType_of_contraction_of_isAffine hc (U.ι ≫ f')
  let W : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
  have hW : LocallyOfFiniteType (W.ι ≫ f') := by
    have := locallyOfFinitePresentation (nodal_on_compl_centre D b z hz ε hε f' hf).1.1
    infer_instance
  let C : Bool → X'.Opens := fun t => if t then U else W
  have hcover : iSup C = ⊤ := by
    refine top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ?_
    by_cases hy : y = z
    · exact ⟨true, hy ▸ hzU⟩
    · exact ⟨false, hy⟩
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  have : LocallyOfFiniteType f' :=
    IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType.{u}) C hcover
      (fun t => by cases t with
        | false => exact hW
        | true => exact hU)
  infer_instance

end AlgebraicGeometry

end
