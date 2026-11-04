module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DirectImageStructureSheafCommutesBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.NoetherianModelOfProperFlat
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheafNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibre
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FlatNeighbourhoodOfSpecialFibre
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf near a special fibre: the reduction to a Noetherian base

This file proves [Stacks, Tag 0E7L]: for `X --f--> Y --q--> S` and `s ∈ S` with `X ⟶ S` locally
of finite presentation and flat along `X_s`, `Y ⟶ S` locally of finite presentation, `f` proper,
the fibres of `f_s` of dimension at most one, `R¹f_{s,*}𝒪_{X_s} = 0` and
`𝒪_{Y_s} ≅ f_{s,*}𝒪_{X_s}`, there is an open `Y_s ⊂ V ⊂ Y` over which `Y` and `X` are flat over
`S`, the fibres of `f` have dimension at most one, `R¹f_*𝒪_X` vanishes and `𝒪_V ≅ f_*𝒪_X|_V`,
all of which persist after any base change `S' ⟶ S`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `exists_isOpen_flat_fibreDimension_le_one_isZero_firstDirectImage_of_specialFibre`:
  conclusions (b), (c) and (d) of the tag on one open, from hypotheses (1), (3) and (4).
* `exists_isOpen_bijective_stalk_of_isLocallyNoetherian`: the claim of the source's proof over a
  locally Noetherian target: `𝒪_Y ⟶ f_*𝒪_X` is bijective on stalks near `Y_s`.
* `exists_isOpen_bijective_stalk_of_isAffine`: the same over affine `S` and `Y`, via a
  Noetherian model.
* `exists_isOpen_bijective_stalk_of_mem_fiber`: the same near a point of `Y_s`.
* `exists_isOpen_isIso_unitToPushforwardUnit_of_specialFibre`: **[Stacks, Tag 0E7L]**.

## References

* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

variable {X Y S : Scheme.{u}}

/-- A point of an open on which a module vanishes is outside its support. -/
theorem notMem_supp_of_isZero_restrict (M : Y.Modules) (V : Y.Opens)
    (h : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M)) (y : Y) (hy : y ∈ V) :
    y ∉ SheafOfModules.supp M := by
  rw [notMem_supp_iff_isZero_stalk]
  have h1 := (TopCat.Presheaf.stalkFunctor _ (⟨y, hy⟩ : V.toScheme)).map_isZero
    ((Scheme.Modules.toPresheaf _).map_isZero h)
  exact IsZero.of_iso h1 ((Scheme.Modules.restrictStalkNatIso V.ι ⟨y, hy⟩).app M).symm

/-- Flatness of `f⁻¹(V₁) ⟶ S` passes to `f⁻¹(V) ⟶ S` for an open `V ⊆ V₁`. -/
private theorem flat_preimage_ι_comp_of_le (f : X ⟶ Y) {V V₁ : Y.Opens} (h : V ≤ V₁) (g : X ⟶ S)
    [Flat ((f ⁻¹ᵁ V₁).ι ≫ g)] : Flat ((f ⁻¹ᵁ V).ι ≫ g) := by
  have hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V₁ := fun x hx => h hx
  rw [← X.homOfLE_ι hpre, Category.assoc]
  infer_instance

/-- Flatness of `f⁻¹(V) ⟶ S` gives flatness of `f ∣_ V ≫ V.ι ≫ g`. -/
private theorem flat_morphismRestrict_comp (f : X ⟶ Y) (g : Y ⟶ S) (V : Y.Opens)
    [Flat ((f ⁻¹ᵁ V).ι ≫ f ≫ g)] : Flat (f ∣_ V ≫ V.ι ≫ g) := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  infer_instance

/-- **Conclusions (b), (c) and (d) of [Stacks, Tag 0E7L] on one open.** Under hypotheses (1),
(3) and (4) of the tag there is an open `Y_s ⊂ V ⊂ Y` with `f⁻¹(V)` flat over `S`,
`dim(X_y) ≤ 1` for `y ∈ V` and `R¹f_*𝒪_X|_V = 0`.

`exists_isOpen_flat_and_fibreDimension_le_one` gives an open `V₁ ⊇ Y_s` carrying the first two;
`exists_isOpen_firstDirectImage_vanishes_of_factor` (the engine of [Stacks, Tag 0E7G]) applied to
`Y_s ⟶ V₁` shrinks it to an open containing `Y_s` on which `R¹f_*𝒪_X` vanishes. -/
theorem exists_isOpen_flat_fibreDimension_le_one_isZero_firstDirectImage_of_specialFibre
    (f : X ⟶ Y) (q : Y ⟶ S) (s : S) [LocallyOfFinitePresentation (f ≫ q)] [IsProper f]
    (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s, topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧ Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) ∧
      (∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) := by
  obtain ⟨V₁, hV₁, hflat₁, hdim₁, -⟩ :=
    exists_isOpen_flat_and_fibreDimension_le_one f q s hflat hdim
  have hrange : Set.range (q.fiberι s) ⊆ Set.range V₁.ι := by
    rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
    exact fun y hy => hV₁ y hy
  obtain ⟨V, hVle, hVs, hRV, -⟩ := exists_isOpen_firstDirectImage_vanishes_of_factor f V₁ hdim₁
    (IsPullback.of_hasPullback f (q.fiberι s)) (IsOpenImmersion.lift V₁.ι (q.fiberι s) hrange)
    (IsOpenImmersion.lift_fac _ _ _) hR
  refine ⟨V, fun y hy => hVs ?_, flat_preimage_ι_comp_of_le f hVle (f ≫ q),
    fun y hy => hdim₁ y (hVle hy), hRV⟩
  rwa [Scheme.Hom.range_fiberι]

/-- Over a locally Noetherian `Y`, with `X` flat over `S`, `f` proper with fibres of dimension at
most one and `R¹f_*𝒪_X = 0`, if `𝒪_{Y_s} ⟶ f_{s,*}𝒪_{X_s}` is an isomorphism then
`𝒪_Y ⟶ f_*𝒪_X` is bijective on the stalks at the points of an open `V ⊇ Y_s`. -/
private theorem exists_isOpen_bijective_stalk_of_fibreDimension_le_one (f : X ⟶ Y) (q : Y ⟶ S)
    (s : S) [IsLocallyNoetherian Y] [IsProper f] [Flat (f ≫ q)]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f))
    [IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s)))] :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧ ∀ y : Y, y ∈ V → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)) := by
  have : Mono ((Scheme.Modules.pullback (q.fiberι s)).map
      (Scheme.Modules.unitToPushforwardUnit f)) :=
    mono_pullback_map_unitToPushforwardUnit f (q.fiberι s)
  -- the pullback of `𝒪 ⟶ f_* 𝒪` to the special fibre is invertible, by [Stacks, Tag 0E7K] (b)
  set φ := Scheme.Modules.unitToPushforwardUnit f
  have hbc : IsIso (directImageStructureSheafBaseChangeMap f (q.fiberι s)) :=
    isIso_directImageStructureSheafBaseChangeMap_of_flat f q hdim hR (S.fromSpecResidueField s)
  have : IsIso ((Scheme.Modules.pullback (q.fiberι s)).map φ) := by
    have : IsIso ((Scheme.Modules.pullback (q.fiberι s)).map φ ≫
        directImageStructureSheafBaseChangeMap f (q.fiberι s)) := by
      rw [← unitToPushforwardUnit_comp_directImageStructureSheafBaseChangeMap f (q.fiberι s)]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (directImageStructureSheafBaseChangeMap f (q.fiberι s))
  -- the cokernel of `𝒪 ⟶ f_* 𝒪` is coherent ([Stacks, Tag 02O5]) and dies on `Y_s`
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (Scheme.unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  have : (directImageStructureSheaf f).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f (Scheme.unitModule _)
  have : (directImageStructureSheaf f).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := directImageStructureSheaf f)
  let C : Y.Modules := cokernel φ
  have hC : C.IsFiniteType := Scheme.Modules.isFiniteType_of_epi (cokernel.π φ)
  have hCz : IsZero ((Scheme.Modules.pullback (q.fiberι s)).obj C) :=
    IsZero.of_iso (isZero_cokernel_of_epi _) (PreservesCokernel.iso _ φ)
  let V₀ : Y.Opens := ⟨(SheafOfModules.supp C)ᶜ, (SheafOfModules.isClosed_supp C).isOpen_compl⟩
  have hV₀ : ∀ y : Y, q y = s → y ∈ V₀ := fun y hy => by
    obtain ⟨y', rfl⟩ : y ∈ Set.range (q.fiberι s) := by rwa [Scheme.Hom.range_fiberι]
    exact notMem_supp_of_isZero_pullback C hC _ y' hCz
  have hFflat := isFlatOver_directImageStructureSheaf_of_fibreDimension_le_one f q hdim hR
  exact exists_isOpen_bijective_stalk_unitToPushforwardUnit_of_isLocallyNoetherian f q s V₀ hV₀
    (fun y hy => (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel φ y).2 hy)
    (fun y _ => hFflat y)

/-- **The claim of [Stacks, Tag 0E7L] over a locally Noetherian target.** Under the hypotheses
of the tag, with `Y` locally Noetherian and `X` flat over `S`, there is an open `V ⊇ Y_s` with
`dim(X_y) ≤ 1` for `y ∈ V`, `R¹f_* 𝒪_X|_V = 0`, and `𝒪_Y ⟶ f_* 𝒪_X` bijective on the stalks at
the points of `V`. -/
theorem exists_isOpen_bijective_stalk_of_isLocallyNoetherian (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [IsLocallyNoetherian Y] [LocallyOfFinitePresentation (f ≫ q)]
    [IsProper f] [Flat (f ≫ q)]
    (hdim : ∀ y : q.fiber s, topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s))))
    [hiso : IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s)))] :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      (∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      ∀ y : Y, y ∈ V → Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)) := by
  obtain ⟨V₁, hV₁, -, hdim₁, hR₁⟩ :=
    exists_isOpen_flat_fibreDimension_le_one_isZero_firstDirectImage_of_specialFibre f q s
      (fun x _ => Flat.stalkMap (f ≫ q) x) hdim hR
  set f₁ := f ∣_ V₁
  set q₁ := V₁.ι ≫ q
  have : Flat (f₁ ≫ q₁) := flat_morphismRestrict_comp f q V₁
  have hdim₁' : ∀ v : V₁.toScheme, topologicalKrullDim (f₁.fiber v) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_morphismRestrict_le f V₁ 1 hdim₁
  have hR₁' : IsZero (firstDirectImageStructureSheaf f₁) :=
    IsZero.of_iso hR₁ (firstDirectImageRestrictIso f V₁)
  -- the fibre of the restricted triangle
  obtain ⟨k, k', hk, H⟩ := exists_isPullback_fibre_morphismRestrict' f q
    (S.fromSpecResidueField s) V₁
  have : IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f₁ (q₁.fiberι s))) :=
    @isIso_unitToPushforwardUnit_of_isPullback _ _ _ _ _ _ k _ H hk _ _ hiso
  obtain ⟨W, hWs, hW⟩ := exists_isOpen_bijective_stalk_of_fibreDimension_le_one f₁ q₁ s hdim₁' hR₁'
  refine ⟨V₁.ι ''ᵁ W, fun y hy => ?_, fun y hy => ?_, ?_, fun y hy => ?_⟩
  · exact ⟨⟨y, hV₁ y hy⟩, hWs _ hy, rfl⟩
  · obtain ⟨w, -, rfl⟩ := hy
    exact hdim₁ _ w.2
  · refine isZero_restrict_of_forall_notMem_supp _ _ fun y hy => ?_
    obtain ⟨w, -, rfl⟩ := hy
    exact notMem_supp_of_isZero_restrict _ V₁ hR₁ _ w.2
  · obtain ⟨w, hw, rfl⟩ := hy
    exact bijective_stalk_unitToPushforwardUnit_of_isPullback'
      (isPullback_morphismRestrict f V₁).flip w (hW w hw)

/-- A morphism `Spec K ⟶ Spec k` from the spectrum of a field to the spectrum of a field is
flat and surjective. -/
@[ega "IV 11.9.9" "partial"]
theorem flat_and_surjective_specMap_of_field {k K : Type u} [Field k] [Field K]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    Flat (Spec.map φ) ∧ Surjective (Spec.map φ) := by
  rw [flat_and_surjective_SpecMap_iff]
  let := φ.hom.toAlgebra
  change Module.FaithfullyFlat k K
  infer_instance

/-- Let `f : X ⟶ Y` over `S` be the base change of `f₀ : X₀ ⟶ Y₀` over `S₀` along `S ⟶ S₀`. If
over an open `V₀ ⊆ Y₀` the fibres of `f₀` have dimension at most one, `R¹f₀_*𝒪_{X₀}` vanishes and
`𝒪_{Y₀} ⟶ f₀_*𝒪_{X₀}` is bijective on stalks, then `𝒪_Y ⟶ f_*𝒪_X` is bijective on the stalks
at the points of the preimage of `V₀`. -/
private theorem bijective_stalk_of_isPullback_of_model {X₀ Y₀ S₀ : Scheme.{u}} {f : X ⟶ Y}
    {q : Y ⟶ S} {f₀ : X₀ ⟶ Y₀} {q₀ : Y₀ ⟶ S₀} {π : S ⟶ S₀} {πY : Y ⟶ Y₀} {πX : X ⟶ X₀}
    (hY : IsPullback πY q q₀ π) (hX : IsPullback πX f f₀ πY) [IsProper f] [IsProper f₀]
    [Flat (f₀ ≫ q₀)] {V₀ : Y₀.Opens}
    (hdimV₀ : ∀ y : Y₀, y ∈ V₀ → topologicalKrullDim (f₀.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hRV₀ : IsZero ((Scheme.Modules.restrictFunctor V₀.ι).obj (firstDirectImageStructureSheaf f₀)))
    (hbijV₀ : ∀ y : Y₀, y ∈ V₀ → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y₀ y).map
        (Scheme.Modules.unitToPushforwardUnit f₀)))
    (w : Y) (hwV : w ∈ πY ⁻¹ᵁ V₀) :
    Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y w).map
      (Scheme.Modules.unitToPushforwardUnit f)) := by
  -- the triangle over `V₀` satisfies the hypotheses of Tag 0E7K
  set W : Y.Opens := πY ⁻¹ᵁ V₀
  have : Flat (f₀ ∣_ V₀ ≫ V₀.ι ≫ q₀) := flat_morphismRestrict_comp f₀ q₀ V₀
  have hY' : IsPullback (πY ∣_ V₀) (W.ι ≫ q) (V₀.ι ≫ q₀) π :=
    (isPullback_morphismRestrict πY V₀).paste_vert hY
  have hs := (isPullback_morphismRestrict f W).flip.paste_horiz hX
  rw [← morphismRestrict_ι πY V₀] at hs
  have hw := IsPullback.of_right' hs (isPullback_morphismRestrict f₀ V₀).flip
  have hbc := isIso_baseChangeNatTrans_structureSheaf_of_flat hw hY'
    (topologicalKrullDim_fiber_morphismRestrict_le f₀ V₀ 1 hdimV₀)
    (IsZero.of_iso hRV₀ (firstDirectImageRestrictIso f₀ V₀))
  rw [Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange]
    at hbc
  let w' : W.toScheme := ⟨w, hwV⟩
  have h1 : Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor V₀.toScheme
      ((πY ∣_ V₀) w')).map (Scheme.Modules.unitToPushforwardUnit (f₀ ∣_ V₀))) := by
    refine bijective_stalk_unitToPushforwardUnit_of_isPullback
      (isPullback_morphismRestrict f₀ V₀).flip _ ?_
    exact hbijV₀ _ ((πY ∣_ V₀) w').2
  have h2 := (bijective_stalk_unitToPushforwardUnit_iff_of_isPullback hw w').2
    (bijective_modulesStalkFunctor_map_pullback _ _ w' h1)
  exact bijective_stalk_unitToPushforwardUnit_of_isPullback'
    (isPullback_morphismRestrict f W).flip w' h2

/-- **The claim of [Stacks, Tag 0E7L] over affine `S` and `Y`.** The special-fibre hypotheses
are taken along an arbitrary field-valued point `t : Spec K ⟶ S`. The situation is the base change
of a Noetherian model (`exists_noetherianModel`); the hypotheses descend to the image point
`s₀` of the model base along the faithfully flat `Spec K ⟶ Spec κ(s₀)`; the claim holds over the
model (`exists_isOpen_bijective_stalk_of_isLocallyNoetherian`), and its conclusion is carried
back by [Stacks, Tag 0E7K] (b). -/
theorem exists_isOpen_bijective_stalk_of_isAffine (f : X ⟶ Y) (q : Y ⟶ S)
    [IsAffine S] [IsAffine Y] [IsProper f] [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)] {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ S)
    (hdimt : ∀ z, topologicalKrullDim ((pullback.snd f (pullback.fst q t)).fiber z) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (hRt : IsZero (firstDirectImageStructureSheaf (pullback.snd f (pullback.fst q t))))
    (hisot : IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (pullback.fst q t))))
    (z : (pullback q t : Scheme.{u})) :
    ∃ W : Y.Opens, pullback.fst q t z ∈ W ∧ ∀ w : Y, w ∈ W → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y w).map
        (Scheme.Modules.unitToPushforwardUnit f)) := by
  obtain ⟨S₀, Y₀, X₀, q₀, f₀, π, πY, πX, hN, hA, hlfp, hpr, hfl, hY, hX⟩ :=
    exists_noetherianModel f q
  have : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian q₀
  set p := Scheme.SpecToEquivOfField K S₀ (t ≫ π)
  set s₀ := p.1
  set e : Spec (.of K) ⟶ Spec (S₀.residueField s₀) := Spec.map p.2
  have he : t ≫ π = e ≫ S₀.fromSpecResidueField s₀ :=
    ((Scheme.SpecToEquivOfField K S₀).left_inv (t ≫ π)).symm
  obtain ⟨hef, hes⟩ := flat_and_surjective_specMap_of_field p.2
  obtain ⟨a, b, ha, hb⟩ := exists_isPullback_fibre_of_model hY hX t
    (S₀.fromSpecResidueField s₀) e he
  have haf : Flat a := MorphismProperty.of_isPullback ha.flip hef
  have has : Surjective a := MorphismProperty.of_isPullback ha.flip hes
  -- the fibre-dimension bound descends
  have hdim₀ : ∀ z₀, topologicalKrullDim
      ((pullback.snd f₀ (q₀.fiberι s₀)).fiber z₀) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro z₀
    obtain ⟨z', rfl⟩ := a.surjective z₀
    exact topologicalKrullDim_fiber_le_of_isPullback' hb 1 z' (hdimt z')
  obtain ⟨hR₀, hiso₀⟩ := isZero_and_isIso_of_isPullback_of_surjective hb hdim₀ hRt hisot
  have hdimH : ∀ y : q₀.fiber s₀, topologicalKrullDim
      ((Stacks.Flatness.fiberHom f₀ q₀ s₀).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y =>
    topologicalKrullDim_fiber_le_of_isPullback (Stacks.Flatness.isPullback_fiberHom f₀ q₀ s₀).flip
      1 y
      (topologicalKrullDim_fiber_le_of_isPullback'
        (IsPullback.of_hasPullback f₀ (q₀.fiberι s₀)) 1 y (hdim₀ y))
  obtain ⟨V₀, hV₀s, hdimV₀, hRV₀, hbijV₀⟩ :=
    exists_isOpen_bijective_stalk_of_isLocallyNoetherian f₀ q₀ s₀ hdimH hR₀ (hiso := hiso₀)
  -- the point
  refine ⟨πY ⁻¹ᵁ V₀, ?_, bijective_stalk_of_isPullback_of_model hY hX hdimV₀ hRV₀ hbijV₀⟩
  change πY (pullback.fst q t z) ∈ V₀
  refine hV₀s _ ?_
  have h1 : q₀ (πY (pullback.fst q t z)) = π (t (pullback.snd q t z)) := by
    rw [← Scheme.Hom.comp_apply, hY.w, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ q,
      pullback.condition, Scheme.Hom.comp_apply]
  rw [h1, ← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- The fibres of the base change of `f` to `Y_s` are bounded by those of `X_s ⟶ Y_s`. -/
private theorem topologicalKrullDim_fiber_pullback_snd_fiberι_le (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFiniteType f]
    (hdim : ∀ y : q.fiber s, topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (y : q.fiber s) :
    topologicalKrullDim ((pullback.snd f (q.fiberι s)).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have h := Set.mem_range_self (f := q.fiberι s) y
  rw [Scheme.Hom.range_fiberι] at h
  exact topologicalKrullDim_fiber_le_of_isPullback (IsPullback.of_hasPullback f (q.fiberι s)) 1 y
    (topologicalKrullDim_fiber_le_of_specialFibre f q s 1 hdim _ h)

/-- Restricting `X ⟶ Y ⟶ S` to opens `U ⊆ Y` and `S₁ ⊆ S` with `q(U) ⊆ S₁` preserves local
finite presentation, and flatness when `f⁻¹(U)` is flat over `S`. -/
private theorem locallyOfFinitePresentation_and_flat_resLE (f : X ⟶ Y) (q : Y ⟶ S)
    [LocallyOfFinitePresentation q] [LocallyOfFinitePresentation (f ≫ q)] {S₁ : S.Opens}
    {U : Y.Opens} (hUS : U ≤ q ⁻¹ᵁ S₁) [Flat ((f ⁻¹ᵁ U).ι ≫ (f ≫ q))] :
    LocallyOfFinitePresentation (q.resLE S₁ U hUS) ∧
      LocallyOfFinitePresentation (f ∣_ U ≫ q.resLE S₁ U hUS) ∧
      Flat (f ∣_ U ≫ q.resLE S₁ U hUS) := by
  have hqU : q.resLE S₁ U hUS ≫ S₁.ι = U.ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
  have hcomp : (f ∣_ U ≫ q.resLE S₁ U hUS) ≫ S₁.ι = (f ⁻¹ᵁ U).ι ≫ (f ≫ q) := by
    rw [Category.assoc, hqU, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have key : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso],
      (∀ {A B : Scheme.{u}} (g : A ⟶ B) (W : B.Opens), P g → P (g ∣_ W)) →
        ∀ {A : Scheme.{u}} (a : A ⟶ S₁.toScheme), P (a ≫ S₁.ι) → P a :=
    fun P _ H _ a ha => (hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict P H).of_postcomp
      a S₁.ι inferInstance ha
  have hL : LocallyOfFinitePresentation (q.resLE S₁ U hUS ≫ S₁.ι) := by
    rw [hqU]
    infer_instance
  have hL' : LocallyOfFinitePresentation ((f ∣_ U ≫ q.resLE S₁ U hUS) ≫ S₁.ι) := by
    rw [hcomp]
    infer_instance
  have hF : Flat ((f ∣_ U ≫ q.resLE S₁ U hUS) ≫ S₁.ι) := by
    rw [hcomp]
    infer_instance
  exact ⟨key _ (fun g W (hg : LocallyOfFinitePresentation g) => inferInstance) _ hL,
    key _ (fun g W (hg : LocallyOfFinitePresentation g) => inferInstance) _ hL',
    key _ (fun g W (hg : Flat g) => inferInstance) _ hF⟩

/-- **The claim of [Stacks, Tag 0E7L] at a point of the special fibre.** Under the hypotheses of
the tag, every point `y` of `Y` over `s` has an open neighbourhood on whose points
`𝒪_Y ⟶ f_* 𝒪_X` is bijective on stalks. The situation is restricted to affine opens
`y ∈ U ⊆ Y` and `s ∈ S₁ ⊆ S` with `f⁻¹(U)` flat over `S`, where
`exists_isOpen_bijective_stalk_of_isAffine`
applies to the fibre over `Spec κ(s) ⟶ S₁`. -/
theorem exists_isOpen_bijective_stalk_of_mem_fiber (f : X ⟶ Y)
    (q : Y ⟶ S) (s : S) [LocallyOfFinitePresentation (f ≫ q)] [LocallyOfFinitePresentation q]
    [IsProper f] (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s, topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s))))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s))))
    (y : Y) (hy : q y = s) :
    ∃ W : Y.Opens, y ∈ W ∧ ∀ w : Y, w ∈ W → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y w).map
        (Scheme.Modules.unitToPushforwardUnit f)) := by
  obtain ⟨V₁, hV₁, hflat₁, -, -⟩ := exists_isOpen_flat_and_fibreDimension_le_one f q s hflat hdim
  obtain ⟨S₁, hS₁, hsS₁, -⟩ : ∃ S₁ : S.Opens, IsAffineOpen S₁ ∧ s ∈ S₁ ∧ S₁ ≤ ⊤ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show s ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hyU, hUle⟩ : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧ U ≤ V₁ ⊓ q ⁻¹ᵁ S₁ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show y ∈ V₁ ⊓ q ⁻¹ᵁ S₁ from ⟨hV₁ y hy, show q y ∈ S₁ by rwa [hy]⟩)
  have hUS : U ≤ q ⁻¹ᵁ S₁ := hUle.trans inf_le_right
  have : IsAffine S₁.toScheme := hS₁
  have : IsAffine U.toScheme := hU
  have : Flat ((f ⁻¹ᵁ U).ι ≫ (f ≫ q)) :=
    flat_preimage_ι_comp_of_le f (hUle.trans inf_le_left) (f ≫ q)
  obtain ⟨hlU, hlfU, hflU⟩ := locallyOfFinitePresentation_and_flat_resLE f q hUS
  set qU := q.resLE S₁ U hUS
  set fU := f ∣_ U
  have hqU : qU ≫ S₁.ι = U.ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
  -- the field point
  have hrange : Set.range (S.fromSpecResidueField s) ⊆ Set.range S₁.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    simpa using hsS₁
  set t₁ : Spec (.of (S.residueField s)) ⟶ S₁.toScheme :=
    IsOpenImmersion.lift S₁.ι (S.fromSpecResidueField s) hrange
  have ht : t₁ ≫ S₁.ι = S.fromSpecResidueField s := IsOpenImmersion.lift_fac _ _ _
  have hfib := exists_isPullback_fibre_morphismRestrict f q U S₁ qU hqU t₁
  rw [ht] at hfib
  obtain ⟨k, k', hk, H⟩ := hfib
  -- the special-fibre hypotheses pass to the restricted triangle
  have hdimF := topologicalKrullDim_fiber_pullback_snd_fiberι_le f q s hdim
  obtain ⟨hRU, hisoU⟩ := isZero_and_isIso_of_isPullback H hdimF hR hiso
  have hdimU : ∀ z, topologicalKrullDim ((pullback.snd fU (pullback.fst qU t₁)).fiber z) ≤
      ((1 : ℕ) : WithBot ℕ∞) := fun z =>
    topologicalKrullDim_fiber_le_of_isPullback H 1 z (hdimF _)
  -- the point of the restricted fibre over `y`
  let yU : U.toScheme := ⟨y, hyU⟩
  have hpt : qU yU = t₁ (IsLocalRing.closedPoint (S.residueField s)) := by
    apply S₁.ι.isOpenEmbedding.injective
    have e1 : (qU ≫ S₁.ι) yU = q y := by
      rw [hqU]
      rfl
    have e2 : (t₁ ≫ S₁.ι) (IsLocalRing.closedPoint (S.residueField s)) = s := by
      rw [ht]
      exact Scheme.fromSpecResidueField_apply _ _
    exact e1.trans (hy.trans e2.symm)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hpt
  obtain ⟨W, hzW, hW⟩ := exists_isOpen_bijective_stalk_of_isAffine fU qU t₁ hdimU hRU hisoU z
  rw [hz] at hzW
  refine ⟨U.ι ''ᵁ W, ⟨yU, hzW, rfl⟩, fun w hw => ?_⟩
  obtain ⟨w, hw', rfl⟩ := hw
  exact bijective_stalk_unitToPushforwardUnit_of_isPullback'
    (isPullback_morphismRestrict f U).flip w (hW w hw')

/-- **[Stacks, Tag 0E7L].** Let `X --f--> Y --q--> S` be a commutative triangle of schemes and
`s ∈ S`. Assume
1. `X ⟶ S` is locally of finite presentation and flat at the points of `X_s`,
2. `Y ⟶ S` is locally of finite presentation,
3. `f` is proper,
4. the fibres of `f_s : X_s ⟶ Y_s` have dimension `≤ 1` and `R¹f_{s,*}𝒪_{X_s} = 0`,
5. `𝒪_{Y_s} ⟶ f_{s,*}𝒪_{X_s}` is an isomorphism.

Then there is an open `Y_s ⊂ V ⊂ Y` such that (a) `V` is flat over `S`, (b) `f⁻¹(V)` is flat
over `S`, (c) `dim(X_y) ≤ 1` for `y ∈ V`, (d) `R¹f_*𝒪_X|_V = 0`, (e) `𝒪_V ⟶ f_*𝒪_X|_V` is an
isomorphism, and (a) – (e) remain true after base change of `f⁻¹(V) ⟶ V` by any `S' ⟶ S`
(for the base change `X' ⟶ V'` of `f⁻¹(V) ⟶ V`, the open of (a) – (e) being all of `V'`).

In the hypotheses, `f_s` is the base change of `f` along `Y_s ⟶ Y` for (4) on `R¹` and for (5),
and `(f ≫ q).fiber s ⟶ q.fiber s` for the dimension bound of (4); these are the same morphism
up to the canonical isomorphism `X ×_Y Y_s ≅ X_s`.

The proof is the source's. Near each `y ∈ Y_s` one restricts to affine opens of `Y` and `S`
over which `X` is flat; the situation is the base change of a Noetherian model
(`exists_noetherianModel`, [Stacks, Tags 01ZM, 081F, 04AI]), the special-fibre hypotheses
descend to the image point of the model base along a faithfully flat field extension, and over
the Noetherian model the stalk maps of `𝒪_Y ⟶ f_*𝒪_X` are bijective near the special fibre
(surjective by coherence of the cokernel, [Stacks, Tag 02O5], and Nakayama; injective by the
local flatness criterion, [Stacks, Tag 00ME]); this is carried back by [Stacks, Tag 0E7K] (b).
Conclusions (a) and (e) and the persistence then follow from [Stacks, Tag 0E7K] on `V`
(`conclusions_of_isOpen`). -/
@[stacks 0E7L]
theorem exists_isOpen_isIso_unitToPushforwardUnit_of_specialFibre (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFinitePresentation (f ≫ q)]
    [LocallyOfFinitePresentation q] [IsProper f]
    (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s, topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s))))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s)))) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      Flat (V.ι ≫ q) ∧
      Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) ∧
      (∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.unitToPushforwardUnit f)) ∧
      ∀ ⦃S' : Scheme.{u}⦄ (h : S' ⟶ S),
        Flat (pullback.snd (V.ι ≫ q) h) ∧
        Flat (pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h) ≫ pullback.snd (V.ι ≫ q) h) ∧
        (∀ y' : (pullback (V.ι ≫ q) h : Scheme.{u}), topologicalKrullDim
          ((pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h)).fiber y') ≤
            ((1 : ℕ) : WithBot ℕ∞)) ∧
        IsZero (firstDirectImageStructureSheaf
          (pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h))) ∧
        IsIso (Scheme.Modules.unitToPushforwardUnit
          (pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h))) := by
  obtain ⟨V₁, hV₁, hflat₁, hdim₁, hR₁⟩ :=
    exists_isOpen_flat_fibreDimension_le_one_isZero_firstDirectImage_of_specialFibre f q s hflat
      hdim hR
  choose W hyW hW using fun (y : {y : Y // q y = s}) =>
    exists_isOpen_bijective_stalk_of_mem_fiber f q s hflat hdim hR hiso y.1 y.2
  set V : Y.Opens := V₁ ⊓ ⨆ y, W y
  have hVs : ∀ y : Y, q y = s → y ∈ V := fun y hy =>
    ⟨hV₁ y hy, TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyW _⟩⟩
  have hle : V ≤ V₁ := inf_le_left
  have hflatX : Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) := flat_preimage_ι_comp_of_le f hle (f ≫ q)
  have hdimV : ∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    fun y hy => hdim₁ y (hle hy)
  have hRV : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (firstDirectImageStructureSheaf f)) :=
    isZero_restrict_of_forall_notMem_supp _ _ fun y hy =>
      notMem_supp_of_isZero_restrict _ V₁ hR₁ y (hle hy)
  have hbij : ∀ y : Y, y ∈ V → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)) := fun y hy => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy.2
    exact hW i y hi
  have : Flat (f ∣_ V ≫ V.ι ≫ q) := flat_morphismRestrict_comp f q V
  have hdimV' := topologicalKrullDim_fiber_morphismRestrict_le f V 1 hdimV
  have hRV' : IsZero (firstDirectImageStructureSheaf (f ∣_ V)) :=
    IsZero.of_iso hRV (firstDirectImageRestrictIso f V)
  obtain ⟨hq, -, hisoV, hbc⟩ := conclusions_of_isOpen f q V hflatX hdimV hRV hbij
    (isFlatOver_directImageStructureSheaf_of_fibreDimension_le_one (f ∣_ V) (V.ι ≫ q)
      hdimV' hRV')
    (fun _ h => isIso_directImageStructureSheafBaseChangeMap_of_flat (f ∣_ V) (V.ι ≫ q)
      hdimV' hRV' h)
  refine ⟨V, hVs, hq, hflatX, hdimV, hRV, ?_, hbc⟩
  have hsq := ProjectiveSpaceHigherDirectImage.restrictUnitToPushforwardUnitSquare f V
  have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.unitToPushforwardUnit f) ≫
      (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).hom.app
        (Scheme.unitModule X) ≫ (Scheme.Modules.pushforward (f ∣_ V)).map
          (ProjectiveSpaceHigherDirectImage.restrictUnitModuleIso (f ⁻¹ᵁ V).ι).hom) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).hom.app
      (Scheme.unitModule X) ≫ (Scheme.Modules.pushforward (f ∣_ V)).map
        (ProjectiveSpaceHigherDirectImage.restrictUnitModuleIso (f ⁻¹ᵁ V).ι).hom)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
