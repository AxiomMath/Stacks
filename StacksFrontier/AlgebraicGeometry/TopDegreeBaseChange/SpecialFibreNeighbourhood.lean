module

public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseFlatnessAndVanishingNearSpecialFibre
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheafNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimensionOneCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SpecialFibreFiniteness
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SurjectivityAfterBaseChange

/-!
# A neighbourhood of the special fibre

Let `X --f--> Y --q--> S` be morphisms of schemes and `s ∈ S`, with `X ⟶ S` locally of finite
presentation and flat along `X_s`, `f` proper, the fibres of `f_s : X_s ⟶ Y_s` of dimension at
most one, `R¹ f_{s,*} 𝒪_{X_s} = 0` and `𝒪_{Y_s} ⟶ f_{s,*} 𝒪_{X_s}` surjective. [Stacks, Tag 0E7J]
produces an open `Y_s ⊆ V ⊆ Y` with `f⁻¹(V)` flat over `S`, `dim(X_y) ≤ 1` for `y ∈ V`,
`R¹ f_* 𝒪_X|_V = 0` and `𝒪_V ⟶ f_* 𝒪_X|_V` surjective, the last three persisting after any base
change `Y' ⟶ V`. This file proves it.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `exists_isOpen_notMem_supp_cokernel_unit`: near a point of `Y_s`, the cokernel of
  `𝒪_Y ⟶ f_* 𝒪_X` vanishes. This is the last paragraph but one of the source's proof: the
  cokernel is of finite type by the source's claim (`SpecialFibreFiniteness.lean`), its pullback
  to `Y_s` vanishes because formation of `f_* 𝒪_X` commutes with the base change to the fibre
  ([Stacks, Tag 0E7K]), and Nakayama's lemma, in the form of [Stacks, Tag 056J], concludes.
* `exists_isOpen_flat_fibreDimension_vanishing_epi_near_specialFibre`: **[Stacks, Tag 0E7J]**.

## Implementation notes

The base-change clauses are stated, as in the source, for the base change of
`f ∣_ V : f⁻¹(V) ⟶ V` along an arbitrary `g : Y' ⟶ V`. The persistence of the surjectivity is
[Stacks, Tag 0E7I], `epi_unitToPushforwardUnit_of_baseChange`.

## References

* [Stacks Project, Tag 0E7J](https://stacks.math.columbia.edu/tag/0E7J)
* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 0E7I](https://stacks.math.columbia.edu/tag/0E7I)
* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

variable {X Y S : Scheme.{u}}

set_option synthInstance.maxHeartbeats 400000 in
-- The `Epi` instance search on the composite times out at the default limit.
/-- **Surjectivity of `𝒪_Y ⟶ f_* 𝒪_X` passes to a flat base change.** The degree-zero
base-change comparison is invertible along a flat morphism ([Stacks, Tag 02KH]) and is
compatible with the two canonical maps, and pullback preserves epimorphisms. -/
theorem epi_unitToPushforwardUnit_of_isPullback_of_flat {X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [Epi (Scheme.Modules.unitToPushforwardUnit f)] :
    Epi (Scheme.Modules.unitToPushforwardUnit f') := by
  have hbc := isIso_pushforwardBaseChange_unit_of_flat H
  have : Epi ((Scheme.Modules.pullbackUnitIso g).hom ≫
      Scheme.Modules.unitToPushforwardUnit f' ≫ (Scheme.Modules.pushforward f').map
        (Scheme.Modules.pullbackUnitIso g').inv) := by
    rw [unitToPushforwardUnit_comp_pushforwardBaseChange H.w]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).1 ((epi_comp_iff_of_epi _ _).1 this)

/-- The cokernel of the restriction of `𝒪_Y ⟶ f_* 𝒪_X` to an open `U` is the cokernel of
`𝒪_U ⟶ (f ∣_ U)_* 𝒪`. Restriction to an open is a left adjoint, so it preserves cokernels, and
it carries the structure-sheaf map of `f` to that of `f ∣_ U` up to isomorphism
(`ProjectiveSpaceHigherDirectImage.restrictUnitToPushforwardUnitSquare`). -/
def restrictCokernelUnitIso (f : X ⟶ Y) (U : Y.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj (cokernel (Scheme.Modules.unitToPushforwardUnit f)) ≅
      cokernel (Scheme.Modules.unitToPushforwardUnit (f ∣_ U)) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.ι) _ ≪≫
    cokernel.mapIso _ _ (ProjectiveSpaceHigherDirectImage.restrictUnitModuleIso U.ι)
      ((AffinePushforward.restrictPushforwardIso f U).app (Scheme.unitModule X) ≪≫
        (Scheme.Modules.pushforward (f ∣_ U)).mapIso
          (ProjectiveSpaceHigherDirectImage.restrictUnitModuleIso (f ⁻¹ᵁ U).ι))
      (by
        simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
          ProjectiveSpaceHigherDirectImage.restrictUnitToPushforwardUnitSquare f U)

/-- A point of an open `U` outside the support of the cokernel of `𝒪_U ⟶ (f ∣_ U)_* 𝒪` is
outside the support of the cokernel of `𝒪_Y ⟶ f_* 𝒪_X`. -/
theorem notMem_supp_cokernel_unit_of_restrict (f : X ⟶ Y) (U : Y.Opens) (w : U.toScheme)
    (hw : w ∉ SheafOfModules.supp (cokernel (Scheme.Modules.unitToPushforwardUnit (f ∣_ U)))) :
    U.ι w ∉ SheafOfModules.supp (cokernel (Scheme.Modules.unitToPushforwardUnit f)) := by
  have h1 := (TopDegreeBaseChange.notMem_supp_iff_isZero_stalk
    (cokernel (Scheme.Modules.unitToPushforwardUnit (f ∣_ U))) w).mp hw
  refine (TopDegreeBaseChange.notMem_supp_iff_isZero_stalk
    (cokernel (Scheme.Modules.unitToPushforwardUnit f)) (U.ι w)).mpr ?_
  have e1 := (TopCat.Presheaf.stalkFunctor _ w).mapIso
    ((Scheme.Modules.toPresheaf _).mapIso (restrictCokernelUnitIso f U))
  exact IsZero.of_iso (IsZero.of_iso h1 e1)
    ((Scheme.Modules.restrictStalkNatIso U.ι w).app _).symm

/-- Flatness of `U.ι ≫ p` follows from that of `V.ι ≫ p` for opens `U ≤ V`. -/
private theorem flat_ι_comp_of_le {Z : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (p : X ⟶ Z)
    (hV : Flat (V.ι ≫ p)) : Flat (U.ι ≫ p) := by
  rw [← X.homOfLE_ι h, Category.assoc]
  infer_instance

/-- A module vanishing on an open `V` vanishes on every open `U ≤ V`. -/
private theorem isZero_restrict_of_le (M : Y.Modules) {U V : Y.Opens} (h : U ≤ V)
    (hV : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
  isZero_of_forall_isZero_stalk _ fun w => IsZero.of_iso
    (SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict V _ _ (h w.2) hV)
    ((Scheme.Modules.restrictStalkNatIso U.ι w).app _)

/-- A morphism `a` to an open `S₁` of `S` is flat when `a ≫ S₁.ι` is. -/
private theorem flat_of_comp_ι {T : Scheme.{u}} {S₁ : S.Opens} (a : T ⟶ S₁.toScheme)
    (h : Flat (a ≫ S₁.ι)) : Flat a := by
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.HasOfPostcompProperty (@Flat : MorphismProperty Scheme.{u})
      @IsOpenImmersion := by
    apply hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
    intro A B g W hg
    have : Flat g := hg
    infer_instance
  exact MorphismProperty.of_postcomp (W' := @IsOpenImmersion) _ _ S₁.ι inferInstance h

/-- A morphism `a` to an open `S₁` of `S` is locally of finite presentation when `a ≫ S₁.ι`
is. -/
private theorem locallyOfFinitePresentation_of_comp_ι {T : Scheme.{u}} {S₁ : S.Opens}
    (a : T ⟶ S₁.toScheme) (h : LocallyOfFinitePresentation (a ≫ S₁.ι)) :
    LocallyOfFinitePresentation a := by
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @IsOpenImmersion := by
    apply hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
    intro A B g W hg
    have : LocallyOfFinitePresentation g := hg
    infer_instance
  exact MorphismProperty.of_postcomp (W' := @IsOpenImmersion) _ _ S₁.ι inferInstance h

/-- If `𝒪_{Y_s} ⟶ f_{s,*} 𝒪_{X_s}` is surjective, then so is the corresponding map for
`f ∣_ U` over the point `s` of an open `S₁ ∋ s`, for any `qU : U ⟶ S₁` lifting `q`. -/
private theorem exists_epi_unitToPushforwardUnit_fibre_morphismRestrict (f : X ⟶ Y) (q : Y ⟶ S)
    (s : S) [IsProper f] (U : Y.Opens) {S₁ : S.Opens} (hsS₁ : s ∈ S₁)
    (qU : U.toScheme ⟶ S₁.toScheme) (hqU : qU ≫ S₁.ι = U.ι ≫ q)
    (hsurj : Epi (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s)))) :
    ∃ t : Spec (S.residueField s) ⟶ S₁.toScheme, t ≫ S₁.ι = S.fromSpecResidueField s ∧
      Epi (Scheme.Modules.unitToPushforwardUnit (pullback.snd (f ∣_ U) (pullback.fst qU t))) := by
  have hrt : Set.range (S.fromSpecResidueField s) ⊆ Set.range S₁.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.fromSpecResidueField_apply]
    exact hsS₁
  set t₁ := IsOpenImmersion.lift S₁.ι (S.fromSpecResidueField s) hrt
  have ht₁ : t₁ ≫ S₁.ι = S.fromSpecResidueField s := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, k', hk, H⟩ := exists_isPullback_fibre_morphismRestrict f q U S₁ qU hqU t₁
  have hsurj' : Epi (Scheme.Modules.unitToPushforwardUnit
      (pullback.snd f (pullback.fst q (t₁ ≫ S₁.ι)))) := by
    rwa [ht₁]
  exact ⟨t₁, ht₁, @epi_unitToPushforwardUnit_of_isPullback_of_flat _ _ _ _ _ _ _ _ H hk _ _ hsurj'⟩

/-- The pullback of `𝒪_Y ⟶ f_* 𝒪_X` along `g` is surjective when the base-change map of
`f_* 𝒪_X` along `g` is invertible and `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is surjective. -/
private theorem epi_pullback_map_unitToPushforwardUnit {Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsIso (directImageStructureSheafBaseChangeMap f g)]
    [Epi (Scheme.Modules.unitToPushforwardUnit (pullback.snd f g))] :
    Epi ((Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f)) := by
  have : Epi ((Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f) ≫
      directImageStructureSheafBaseChangeMap f g) := by
    rw [← unitToPushforwardUnit_comp_directImageStructureSheafBaseChangeMap f g]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).1 this

/-- A point `y ∈ U` over `s` lies in the image of the fibre `U ×_{S₁} Spec κ(s)`. -/
private theorem exists_pullback_fst_eq_of_mem_fiber (q : Y ⟶ S) {s : S} {U : Y.Opens} {S₁ : S.Opens}
    (qU : U.toScheme ⟶ S₁.toScheme) (hqU : qU ≫ S₁.ι = U.ι ≫ q)
    (t : Spec (S.residueField s) ⟶ S₁.toScheme) (ht : t ≫ S₁.ι = S.fromSpecResidueField s)
    (y : Y) (hyU : y ∈ U) (hy : q y = s) :
    ∃ z, pullback.fst qU t z = ⟨y, hyU⟩ := by
  have e1 : S₁.ι (qU ⟨y, hyU⟩) = s := by
    have := congrArg (fun k : U.toScheme ⟶ S => k ⟨y, hyU⟩) hqU
    simp only at this
    exact this.trans hy
  have e2 : S₁.ι (t (default : Spec (S.residueField s))) = s := by
    rw [← Scheme.Hom.comp_apply, ht, Scheme.fromSpecResidueField_apply]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := qU) (g := t)
    (⟨y, hyU⟩ : U.toScheme) (default : Spec (S.residueField s))
    (S₁.ι.isOpenEmbedding.injective (e1.trans e2.symm))
  exact ⟨z, hz⟩

/-- **The surjectivity of `𝒪_Y ⟶ f_* 𝒪_X` near a point of the special fibre**, the core of
the proof of [Stacks, Tag 0E7J]. Let `V ⊆ Y` be open with `f⁻¹(V)` flat over `S`, the fibres of
`f` over `V` of dimension at most one and `R¹ f_* 𝒪_X|_V = 0`, and suppose
`𝒪_{Y_s} ⟶ f_{s,*} 𝒪_{X_s}` is surjective. Then every `y ∈ V` over `s` has an open
neighbourhood outside the support of the cokernel of `𝒪_Y ⟶ f_* 𝒪_X`.

Over affine opens `y ∈ U ⊆ V` and `s ∈ S₁ ⊆ S`, `f_* 𝒪_X|_U` is of finite type
(`isFiniteType_directImageStructureSheaf_of_isAffine`, the source's claim), hence so is the
cokernel `𝒞`; its formation commutes with the base change to the fibre over `s`
([Stacks, Tag 0E7K]), where it vanishes by hypothesis; so `y` is outside the closed support of
`𝒞` ([Stacks, Tag 056J]) — the source's Nakayama step. -/
theorem exists_isOpen_notMem_supp_cokernel_unit (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFinitePresentation (f ≫ q)] [IsProper f] (V : Y.Opens)
    (hflatV : Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)))
    (hdimV : ∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hRV : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)))
    (hsurj : Epi (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s))))
    (y : Y) (hy : q y = s) (hyV : y ∈ V) :
    ∃ N : Y.Opens, y ∈ N ∧ ∀ w : Y, w ∈ N →
      w ∉ SheafOfModules.supp (cokernel (Scheme.Modules.unitToPushforwardUnit f)) := by
  obtain ⟨S₁, hS₁, hsS₁, -⟩ : ∃ S₁ : S.Opens, IsAffineOpen S₁ ∧ s ∈ S₁ ∧ S₁ ≤ ⊤ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show s ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hyU, hUle⟩ : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧ U ≤ V ⊓ q ⁻¹ᵁ S₁ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show y ∈ V ⊓ q ⁻¹ᵁ S₁ from ⟨hyV, show q y ∈ S₁ from hy ▸ hsS₁⟩)
  have hUV : U ≤ V := hUle.trans inf_le_left
  have : IsAffine S₁.toScheme := hS₁
  have : IsAffine U.toScheme := hU
  set qU := q.resLE S₁ U (hUle.trans inf_le_right)
  have hqU : qU ≫ S₁.ι = U.ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
  obtain ⟨t₁, ht₁, hepi⟩ :=
    exists_epi_unitToPushforwardUnit_fibre_morphismRestrict f q s U hsS₁ qU hqU hsurj
  set fU := f ∣_ U
  have : IsProper fU := MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
    inferInstance
  have hcomp : (fU ≫ qU) ≫ S₁.ι = (f ⁻¹ᵁ U).ι ≫ (f ≫ q) := by
    rw [Category.assoc, hqU, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  have : Flat ((f ⁻¹ᵁ U).ι ≫ (f ≫ q)) := flat_ι_comp_of_le (U := f ⁻¹ᵁ U) (V := f ⁻¹ᵁ V)
    (fun x hx => hUV hx) _ hflatV
  have : Flat (fU ≫ qU) := flat_of_comp_ι _ <| by
    rw [hcomp]
    infer_instance
  have : LocallyOfFinitePresentation (fU ≫ qU) := locallyOfFinitePresentation_of_comp_ι _ <| by
    rw [hcomp]
    infer_instance
  have hdimU : ∀ u : U.toScheme, topologicalKrullDim (fU.fiber u) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_morphismRestrict_le f U 1 fun y hy => hdimV y (hUV hy)
  have hRU : IsZero (firstDirectImageStructureSheaf fU) :=
    IsZero.of_iso (isZero_restrict_of_le _ hUV hRV) (firstDirectImageRestrictIso f U)
  have hft : (directImageStructureSheaf fU).IsFiniteType :=
    isFiniteType_directImageStructureSheaf_of_isAffine fU qU hdimU hRU
  set φU := Scheme.Modules.unitToPushforwardUnit fU
  let C : U.toScheme.Modules := cokernel φU
  have hC : C.IsFiniteType := Scheme.Modules.isFiniteType_of_epi (cokernel.π φU)
  set g := pullback.fst qU t₁
  have : IsIso (directImageStructureSheafBaseChangeMap fU g) :=
    isIso_directImageStructureSheafBaseChangeMap_of_flat fU qU hdimU hRU t₁
  have := epi_pullback_map_unitToPushforwardUnit fU g
  have hCz : IsZero ((Scheme.Modules.pullback g).obj C) :=
    IsZero.of_iso (isZero_cokernel_of_epi _) (PreservesCokernel.iso _ φU)
  have hyU' : (⟨y, hyU⟩ : U.toScheme) ∉ SheafOfModules.supp C := by
    obtain ⟨z, hz⟩ := exists_pullback_fst_eq_of_mem_fiber q qU hqU t₁ ht₁ y hyU hy
    have := notMem_supp_of_isZero_pullback C hC g z hCz
    rwa [hz] at this
  let N' : U.toScheme.Opens := ⟨(SheafOfModules.supp C)ᶜ,
    (SheafOfModules.isClosed_supp C).isOpen_compl⟩
  refine ⟨U.ι ''ᵁ N', ⟨⟨y, hyU⟩, hyU', rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact notMem_supp_cokernel_unit_of_restrict f U w hw

set_option synthInstance.maxHeartbeats 400000 in
-- The `Epi` instance search on the composite times out at the default limit.
/-- **`𝒪_V ⟶ f_* 𝒪_X|_V` surjective gives `𝒪_V ⟶ (f ∣_ V)_* 𝒪` surjective**: the two maps
differ by the isomorphisms of
`ProjectiveSpaceHigherDirectImage.restrictUnitToPushforwardUnitSquare`. -/
theorem epi_unitToPushforwardUnit_morphismRestrict_of_epi (f : X ⟶ Y) (V : Y.Opens)
    (h : Epi ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.unitToPushforwardUnit f))) :
    Epi (Scheme.Modules.unitToPushforwardUnit (f ∣_ V)) := by
  have : Epi ((ProjectiveSpaceHigherDirectImage.restrictUnitModuleIso V.ι).hom ≫
      Scheme.Modules.unitToPushforwardUnit (f ∣_ V)) := by
    rw [← ProjectiveSpaceHigherDirectImage.restrictUnitToPushforwardUnitSquare f V]
    infer_instance
  exact epi_of_epi ((ProjectiveSpaceHigherDirectImage.restrictUnitModuleIso V.ι).hom) _

/-- **Persistence under base change.** If over an open `V ⊆ Y` the fibres of `f` have dimension
at most one, `R¹ f_* 𝒪_X|_V = 0` and `𝒪_V ⟶ f_* 𝒪_X|_V` is surjective, then the same holds
for the base change of `f ∣_ V` along any `g : Y' ⟶ V`. -/
private theorem fibreDimension_vanishing_epi_baseChange_morphismRestrict (f : X ⟶ Y) [IsProper f]
    (V : Y.Opens)
    (hdimV : ∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hresV : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)))
    (hepiV : Epi ((Scheme.Modules.restrictFunctor V.ι).map
      (Scheme.Modules.unitToPushforwardUnit f)))
    {Y' : Scheme.{u}} (g : Y' ⟶ V.toScheme) :
    (∀ y' : Y', topologicalKrullDim ((pullback.snd (f ∣_ V) g).fiber y') ≤
      ((1 : ℕ) : WithBot ℕ∞)) ∧
    IsZero (firstDirectImageStructureSheaf (pullback.snd (f ∣_ V) g)) ∧
    Epi (Scheme.Modules.unitToPushforwardUnit (pullback.snd (f ∣_ V) g)) := by
  have : IsProper (f ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip inferInstance
  have hdimV' : ∀ v : V.toScheme, topologicalKrullDim ((f ∣_ V).fiber v) ≤
      ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_morphismRestrict_le f V 1 hdimV
  have hRV : IsZero (firstDirectImageStructureSheaf (f ∣_ V)) :=
    IsZero.of_iso hresV (firstDirectImageRestrictIso f V)
  have hRbc : ∀ {Y'' : Scheme.{u}} (g' : Y'' ⟶ V.toScheme),
      IsZero (firstDirectImageStructureSheaf (pullback.snd (f ∣_ V) g')) := fun g' =>
    (isZero_pullback_firstDirectImage_iff (f ∣_ V) hdimV' g').mp (Functor.map_isZero _ hRV)
  have hfib : ∀ v : V.toScheme, IsZero (firstCohomologyStructureSheaf ((f ∣_ V).fiber v)) := by
    intro v
    have : IsProper ((f ∣_ V).fiberToSpecResidueField v) :=
      isProper_fiberToSpecResidueField (f ∣_ V) v
    exact isZero_cohomology_of_isZero_rightDerivedPlus_pushforward
      ((f ∣_ V).fiberToSpecResidueField v) 1 _ (hRbc (V.toScheme.fromSpecResidueField v))
  exact ⟨fun y' => topologicalKrullDim_fiber_le_of_isPullback
      (IsPullback.of_hasPullback (f ∣_ V) g) 1 y' (hdimV' (g y')), hRbc g,
    epi_unitToPushforwardUnit_of_baseChange (f ∣_ V) hdimV' hfib
      (epi_unitToPushforwardUnit_morphismRestrict_of_epi f V hepiV) g⟩

/-- **[Stacks, Tag 0E7J].** Let `X --f--> Y --q--> S` be morphisms of schemes and let `s ∈ S`.
Write `f_s : X_s ⟶ Y_s` for the induced morphism of fibres over `s` (in the two spellings
`Stacks.Flatness.fiberHom f q s` and `pullback.snd f (q.fiberι s)` of `X_s = X ×_Y Y_s`).
Assume

1. `X ⟶ S` is locally of finite presentation and flat at the points of `X_s`,
2. `f` is proper,
3. the fibres of `f_s` have dimension at most one and `R¹ f_{s,*} 𝒪_{X_s} = 0`,
4. `𝒪_{Y_s} ⟶ f_{s,*} 𝒪_{X_s}` is surjective.

Then there is an open `Y_s ⊆ V ⊆ Y` such that (a) `f⁻¹(V)` is flat over `S`, (b)
`dim(X_y) ≤ 1` for `y ∈ V`, (c) `R¹ f_* 𝒪_X|_V = 0`, (d) `𝒪_V ⟶ f_* 𝒪_X|_V` is surjective,
and (b), (c) and (d) remain true after base change of `f⁻¹(V) ⟶ V` by any `Y' ⟶ V`.

(a) and (b) are `exists_isOpen_flat_and_fibreDimension_le_one`; (c) and its persistence are
[Stacks, Tag 0E7G] along `Y_s` (`exists_isOpen_firstDirectImage_vanishes_of_factor`); (d) is
`exists_isOpen_notMem_supp_cokernel_unit` at every point of `Y_s`, and its persistence is
[Stacks, Tag 0E7I] (`epi_unitToPushforwardUnit_of_baseChange`), whose hypotheses on the fibres
follow from the persistence of (b) and (c). -/
@[stacks 0E7J]
theorem exists_isOpen_flat_fibreDimension_vanishing_epi_near_specialFibre (f : X ⟶ Y)
    (q : Y ⟶ S) (s : S) [LocallyOfFinitePresentation (f ≫ q)] [IsProper f]
    (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s,
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s))))
    (hsurj : Epi (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s)))) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) ∧
      (∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      Epi ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.unitToPushforwardUnit f)) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme),
        (∀ y' : Y', topologicalKrullDim ((pullback.snd (f ∣_ V) g).fiber y') ≤
          ((1 : ℕ) : WithBot ℕ∞)) ∧
        IsZero (firstDirectImageStructureSheaf (pullback.snd (f ∣_ V) g)) ∧
        Epi (Scheme.Modules.unitToPushforwardUnit (pullback.snd (f ∣_ V) g)) := by
  obtain ⟨V₁, hV₁, hflat₁, hdim₁, -⟩ :=
    exists_isOpen_flat_and_fibreDimension_le_one f q s hflat hdim
  have hr₁ : Set.range (q.fiberι s) ⊆ Set.range V₁.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.range_fiberι]
    exact fun y hy => hV₁ y hy
  obtain ⟨V₂, hV₂₁, hr₂, hres₂, -⟩ := exists_isOpen_firstDirectImage_vanishes_of_factor f V₁
    hdim₁ (IsPullback.of_hasPullback f (q.fiberι s))
    (IsOpenImmersion.lift V₁.ι (q.fiberι s) hr₁) (IsOpenImmersion.lift_fac _ _ _) hR
  rw [Scheme.Hom.range_fiberι] at hr₂
  have hV₂ : ∀ y : Y, q y = s → y ∈ V₂ := fun y hy => hr₂ hy
  have hflat₂ : Flat ((f ⁻¹ᵁ V₂).ι ≫ (f ≫ q)) :=
    flat_ι_comp_of_le (U := f ⁻¹ᵁ V₂) (V := f ⁻¹ᵁ V₁) (fun x hx => hV₂₁ hx) _ hflat₁
  have hdim₂ : ∀ y : Y, y ∈ V₂ → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    fun y hy => hdim₁ y (hV₂₁ hy)
  choose N hyN hNs using fun y : {y : Y // q y = s} =>
    exists_isOpen_notMem_supp_cokernel_unit f q s V₂ hflat₂ hdim₂ hres₂ hsurj y.1 y.2 (hV₂ y.1 y.2)
  let V : Y.Opens := ⨆ y : {y : Y // q y = s}, N y ⊓ V₂
  have hVV₂ : V ≤ V₂ := iSup_le fun _ => inf_le_right
  have hVs : ∀ y : Y, q y = s → y ∈ V := fun y hy =>
    Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyN _, hV₂ y hy⟩
  have hflatV : Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) :=
    flat_ι_comp_of_le (U := f ⁻¹ᵁ V) (V := f ⁻¹ᵁ V₂) (fun x hx => hVV₂ hx) _ hflat₂
  have hdimV : ∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    fun y hy => hdim₂ y (hVV₂ hy)
  have hresV : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (firstDirectImageStructureSheaf f)) := isZero_restrict_of_le _ hVV₂ hres₂
  have hepiV : Epi ((Scheme.Modules.restrictFunctor V.ι).map
      (Scheme.Modules.unitToPushforwardUnit f)) :=
    Preadditive.epi_of_isZero_cokernel _ <| IsZero.of_iso
      (isZero_restrict_of_forall_notMem_supp _ V fun w hw => by
        obtain ⟨y, hy⟩ := Opens.mem_iSup.mp hw
        exact hNs y w hy.1)
      (PreservesCokernel.iso (Scheme.Modules.restrictFunctor V.ι) _).symm
  exact ⟨V, hVs, hflatV, hdimV, hresV, hepiV, fun Y' g =>
    fibreDimension_vanishing_epi_baseChange_morphismRestrict f V hdimV hresV hepiV g⟩

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
