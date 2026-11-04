module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.SerreClass
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDiagonalEquivalence
public import StacksFrontier.Homology.Perfect.ModelIndependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Complexes of quasi-coherent modules representing `D_QCoh`

Two inputs of the twist resolution of a pseudo-coherent complex on a projective space.

## Main results

* `AlgebraicGeometry.exists_quasicoherent_representative`: on a quasi-compact scheme with affine
  diagonal, an object of `D(𝒪_X)` with quasi-coherent cohomology is represented by a complex
  whose terms are quasi-coherent, at an arbitrary chosen model of `D(𝒪_X)`. This is the essential
  surjectivity half of [Stacks, Tag 08DB].
* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_epi_comp_of_qcqs`: on a
  quasi-compact quasi-separated scheme, an epimorphism from a quasi-coherent module onto a module
  of finite type stays an epimorphism on some quasi-coherent submodule of finite type of its
  source ([Stacks, Tag 01PG]).

## Implementation notes

[Stacks, Tag 08DB] is available at the locally small model
`SheafOfModules.hasDerivedCategory`, so the representative is first produced there and its
isomorphism is then carried to an arbitrary model by `StacksDraft.DerivedModel.qObjIsoOfModel`,
which only ever moves isomorphisms between localizations of cochain complexes.

The second result is the argument of
`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_epi_comp`, whose Noetherian
hypothesis is used there only to supply quasi-compactness and quasi-separatedness and to read
finite type off coherence; it is stated here with those two hypotheses directly.

## References

* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

/-- **A complex with quasi-coherent cohomology is quasi-isomorphic to one with quasi-coherent
terms**, at the locally small model, on a quasi-compact scheme with affine diagonal. -/
theorem exists_quasicoherent_representative_locallySmall (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (terminal.from X))]
    (L : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
      (DerivedCategory.Q.obj L)).IsQuasicoherent) :
    ∃ K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ, (∀ i, (K.X i).IsQuasicoherent) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) := by
  have := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal X
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let G : (DerivedCategoryB.derivedCategoryB P).FullSubcategory := ⟨DerivedCategory.Q.obj L, hL⟩
  let F := Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison.{u} X
  let M := F.objPreimage G
  let e : F.obj M ≅ G := F.objObjPreimageIso G
  let K₀ := (DerivedCategory.Q (C := P.FullSubcategory)).objPreimage M
  let e₀ : DerivedCategory.Q.obj K₀ ≅ M := (DerivedCategory.Q).objObjPreimageIso M
  refine ⟨(P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀, fun i => (K₀.X i).2, ⟨?_⟩⟩
  exact (P.ι.mapDerivedCategoryFactors.app K₀).symm ≪≫ P.ι.mapDerivedCategory.mapIso e₀ ≪≫
    (DerivedCategoryB.derivedCategoryB P).ι.mapIso e

/-- **[Stacks, Tag 08DB], essential surjectivity, at an arbitrary model.** On a quasi-compact
scheme with affine diagonal, an object of a chosen derived category of `𝒪_X`-modules whose
cohomology sheaves are quasi-coherent is isomorphic to the class of a complex with quasi-coherent
terms. -/
theorem exists_quasicoherent_representative (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (terminal.from X))]
    (h : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf))
    (F : @DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) _ _ h)
    (hF : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) _ _ h
      i).obj F).IsQuasicoherent) :
    ∃ K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ, (∀ i, (K.X i).IsQuasicoherent) ∧
      Nonempty ((@DerivedCategory.Q (SheafOfModules.{u} X.ringCatSheaf) _ _ h).obj K ≅ F) := by
  let Qh := @DerivedCategory.Q (SheafOfModules.{u} X.ringCatSheaf) _ _ h
  have : Qh.EssSurj := by
    let := h
    exact inferInstanceAs (DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf)).EssSurj
  let L := Qh.objPreimage F
  let eL : Qh.obj L ≅ F := Qh.objObjPreimageIso F
  let hs : HasDerivedCategory.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    SheafOfModules.hasDerivedCategory X.ringCatSheaf
  have hL : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) _ _
      hs i).obj ((@DerivedCategory.Q _ _ _ hs).obj L)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((@DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) _ _ h i).mapIso
          eL).symm ≪≫
        (@DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} X.ringCatSheaf) _ _ h
          i).app L ≪≫
        ((@DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} X.ringCatSheaf) _ _ hs
          i).app L).symm)
      (hF i)
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_quasicoherent_representative_locallySmall X L hL
  exact ⟨K, hK, ⟨StacksDraft.DerivedModel.qObjIsoOfModel hs h e ≪≫ eL⟩⟩

/-- `AlgebraicGeometry.exists_quasicoherent_representative` in the `Scheme.Modules` spelling of
the category of `𝒪_X`-modules. -/
theorem exists_quasicoherent_representative' (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (terminal.from X))]
    (h : HasDerivedCategory.{w} X.Modules) (F : @DerivedCategory X.Modules _ _ h)
    (hF : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor X.Modules _ _ h i).obj F).IsQuasicoherent) :
    ∃ K : CochainComplex X.Modules ℤ, (∀ i, (K.X i).IsQuasicoherent) ∧
      Nonempty ((@DerivedCategory.Q X.Modules _ _ h).obj K ≅ F) :=
  exists_quasicoherent_representative X h F hF

/-- **An epimorphism onto a module of finite type stays one on a quasi-coherent submodule of
finite type of its source**, on a quasi-compact quasi-separated scheme. The source is the filtered
colimit of its quasi-coherent submodules of finite type ([Stacks, Tag 01PG]), so their images in
the target have supremum the whole target, and one stage of that filtered system already
surjects onto a target of finite type ([Stacks, Tag 01BB]). -/
@[sga "6 II 2.1.1" "a)"]
theorem exists_finiteTypeQuasicoherentSubobject_epi_comp_of_qcqs {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {G F : X.Modules} [G.IsQuasicoherent] (hF : F.IsFiniteType) (f : G ⟶ F) [Epi f] :
    ∃ S : FiniteTypeQuasicoherentSubobject G, Epi (S.obj.arrow ≫ f) := by
  classical
  let J := FiniteTypeQuasicoherentSubobject G
  have : IsFiltered J := inferInstance
  have : Nonempty J := IsFiltered.nonempty
  let img : J → Subobject F := fun S => imageSubobject (S.obj.arrow ≫ f)
  let I := { K : Subobject F // ∃ S : J, img S = K }
  have : Nonempty I := ⟨⟨img (Classical.arbitrary J), ⟨Classical.arbitrary J, rfl⟩⟩⟩
  have : IsDirectedOrder I := by
    constructor
    intro A B
    have hmono : ∀ {S U : J} (h : S ⟶ U), img S ≤ img U := fun {S U} h => by
      dsimp [img]
      rw [← Subobject.ofLE_arrow (leOfHom h.hom)]
      exact imageSubobject_comp_le _ _
    obtain ⟨S, hS⟩ := A.property
    obtain ⟨T, hT⟩ := B.property
    obtain ⟨U, hSU, hTU, -⟩ := IsFilteredOrEmpty.cocone_objs S T
    exact ⟨⟨img U, ⟨U, rfl⟩⟩, hS.symm.trans_le (hmono hSU),
      hT.symm.trans_le (hmono hTU)⟩
  let e := equivSmallModel.{u} I
  let K := CategoryTheory.SmallModel.{u} I
  let toSmallObj : I → K := e.functor.obj
  let fromSmallObj : K → I := e.symm.functor.obj
  let unitHom : ∀ i : I, i ⟶ fromSmallObj (toSmallObj i) := fun i => (e.unitIso.app i).hom
  let : Preorder K :=
    { le A B := (fromSmallObj A).1 ≤ (fromSmallObj B).1
      le_refl _ := le_rfl
      le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂ }
  let : Category K := Preorder.smallCategory K
  have : Nonempty K := ⟨toSmallObj (Classical.choice (inferInstance : Nonempty I))⟩
  have : IsDirectedOrder K :=
    { directed A B := by
        obtain ⟨C, hAC, hBC⟩ := exists_ge_ge (fromSmallObj A) (fromSmallObj B)
        refine ⟨toSmallObj C, ?_, ?_⟩
        · show (fromSmallObj A).1 ≤ (fromSmallObj (toSmallObj C)).1
          exact le_trans hAC (leOfHom (unitHom C))
        · show (fromSmallObj B).1 ≤ (fromSmallObj (toSmallObj C)).1
          exact le_trans hBC (leOfHom (unitHom C)) }
  have : IsFiltered K := inferInstance
  let toI : K ⥤ I :=
    { obj := fromSmallObj
      map := fun {A B} h => by
        have hle : A ≤ B := leOfHom h
        change (fromSmallObj A).1 ≤ (fromSmallObj B).1 at hle
        exact homOfLE hle
      map_id := by intro A; apply Subsingleton.elim
      map_comp := by intro A B C f g; apply Subsingleton.elim }
  let imgK : K → Subobject F := fun A => (toI.obj A).1
  let Msup : Subobject F := ⨆ A : K, imgK A
  have hle : ∀ S : J, img S ≤ Msup := fun S =>
    (show (⟨img S, ⟨S, rfl⟩⟩ : I).1 ≤ _ from leOfHom (unitHom _)).trans
      (le_iSup imgK (toSmallObj ⟨img S, ⟨S, rfl⟩⟩))
  have harrow : ∀ S : J, factorThruImageSubobject (S.obj.arrow ≫ f) ≫
      Subobject.ofLE (img S) Msup (hle S) ≫ Msup.arrow = S.obj.arrow ≫ f := by
    intro S
    rw [Subobject.ofLE_arrow]
    exact imageSubobject_arrow_comp _
  have hsup : Msup = ⊤ := by
    let t : ∀ S : J, (Subobject.underlying.obj S.obj : X.Modules) ⟶
        (Subobject.underlying.obj Msup : X.Modules) := fun S =>
      factorThruImageSubobject (S.obj.arrow ≫ f) ≫ Subobject.ofLE (img S) Msup (hle S)
    have ht : ∀ S : J, t S ≫ Msup.arrow = S.obj.arrow ≫ f := fun S =>
      (Category.assoc _ _ _).trans (harrow S)
    have hnat : ∀ {S T : J} (p : S ⟶ T), Subobject.underlying.map p.hom ≫ t T = t S := by
      intro S T p
      apply (cancel_mono Msup.arrow).1
      rw [Category.assoc, ht T, ht S, ← Category.assoc, Subobject.underlying_arrow]
    let d : Cocone (finiteTypeQuasicoherentSubobjectFunctor G) :=
      Cocone.mk (Subobject.underlying.obj Msup)
        { app := t
          naturality := fun {S T} p => (hnat p).trans (Category.comp_id (t S)).symm }
    let hc := isColimit_finiteTypeQuasicoherentSubobjectCocone G
    have hgf : hc.desc d ≫ Msup.arrow = f := by
      refine hc.hom_ext fun S => ?_
      rw [← Category.assoc, hc.fac d S]
      exact ht S
    have : Epi (hc.desc d ≫ Msup.arrow) := by rw [hgf]; assumption
    have : Epi Msup.arrow := epi_of_epi (hc.desc d) Msup.arrow
    have : IsIso Msup.arrow := isIso_of_mono_of_epi Msup.arrow
    simpa [Msup] using (Subobject.isIso_iff_mk_eq_top Msup.arrow).mp inferInstance
  have hsupK : (⨆ A : K, imgK A) = ⊤ := by simpa [Msup, imgK] using hsup
  have hrep : ∀ A : K, ThinSkeleton.mk (Subobject.representative.obj (imgK A)) = imgK A :=
    fun A => Subobject.thinSkeleton_mk_representative_eq_self _
  let Fmono : K ⥤ MonoOver F :=
    { obj := fun A => Subobject.representative.obj (imgK A)
      map := fun {A B} h => Subobject.representative.map (homOfLE (leOfHom (toI.map h)))
      map_id := by intro A; apply Subsingleton.elim
      map_comp := by intro A B C f g; apply Subsingleton.elim }
  let cOver : Cocone (Fmono ⋙ MonoOver.forget F) := Cocone.mk (Over.mk (𝟙 F))
    { app := fun A => Over.homMk (Fmono.obj A).arrow
      naturality := by
        intro A B h
        apply Over.OverMorphism.ext
        dsimp [Fmono]
        exact MonoOver.w (Fmono.map h) }
  have : Mono cOver.pt.hom := by
    dsimp [cOver]
    infer_instance
  have hsup' : Subobject.mk cOver.pt.hom = ⨆ A : K, Subobject.mk (Fmono.obj A).arrow := by
    calc
      Subobject.mk cOver.pt.hom = ⊤ := by
        show Subobject.mk (𝟙 F) = ⊤
        exact (Subobject.top_eq_id F).symm
      _ = ⨆ A : K, imgK A := hsupK.symm
      _ = ⨆ A : K, Subobject.mk (Fmono.obj A).arrow := by
        exact iSup_congr fun A => (hrep A).symm
  have hcol : IsColimit ((Over.forget F).mapCocone cOver) :=
    IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup Fmono cOver hsup'
  let D := Fmono ⋙ MonoOver.forget F ⋙ Over.forget F
  let cD := (Over.forget F).mapCocone cOver
  have hcDpt : cD.pt.IsFiniteType := hF
  let eCol := IsColimit.coconePointUniqueUpToIso (colimit.isColimit D) hcol
  have hcolFT : (colimit D).IsFiniteType := isFiniteType_of_iso_modules eCol hcDpt
  obtain ⟨A, hA⟩ := @Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType
    _ X.ringCatSheaf _ _ _ _ K _ _ _ _ D hcolFT
  have : Epi (cD.ι.app A) := by
    have hfac : colimit.ι D A ≫ eCol.hom = cD.ι.app A :=
      IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit D) hcol A
    rw [← hfac]
    exact epi_comp' hA (by infer_instance)
  have hImgTop : imgK A = ⊤ := by
    have : Mono (cD.ι.app A) := (Fmono.obj A).property
    have : IsIso (cD.ι.app A) := isIso_of_mono_of_epi _
    have htop := (Subobject.isIso_iff_mk_eq_top (cD.ι.app A)).mp inferInstance
    rw [← hrep A]
    exact htop
  obtain ⟨S, hS⟩ := (fromSmallObj A).property
  refine ⟨S, ?_⟩
  have hTopImage : img S = ⊤ := by simpa [img, hS] using hImgTop
  have hIso : IsIso (imageSubobject (S.obj.arrow ≫ f)).arrow :=
    (Subobject.isIso_iff_mk_eq_top (imageSubobject (S.obj.arrow ≫ f)).arrow).2 (by
      simpa [img] using hTopImage)
  have hepi : Epi (factorThruImageSubobject (S.obj.arrow ≫ f) ≫
      (imageSubobject (S.obj.arrow ≫ f)).arrow) := inferInstance
  simpa [imageSubobject_arrow_comp] using hepi

end AlgebraicGeometry

end
