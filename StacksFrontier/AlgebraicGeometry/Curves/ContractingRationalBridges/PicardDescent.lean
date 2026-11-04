module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionAffine
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionGenus
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructurePushforward
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.FibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections

/-!
# Invertible modules trivial along a contracted rational bridge

Let `c : X ⟶ Y` be the contraction of a rational bridge `C` ([Stacks, Tag 0E3M]) and let `y` be
the point onto which `C` is collapsed. This file shows that `c` is an isomorphism over
`Y \ {y}`, that the scheme-theoretic fibre of `c` over `y` is `C`, and that an invertible
`𝒪_X`-module which is trivial on `C` is the pullback of an invertible `𝒪_Y`-module. This is the
part of [Stacks, Tag 0E24] used in the proof of [Stacks, Tag 0E3N].

## Main results

* `Stacks.Curves.isIso_morphismRestrict_compl_contraction_bridge`: `c` is an isomorphism over the
  complement of the image of `C`.
* `Stacks.Curves.mem_support_of_mem_image_contraction_bridge`: the fibre of `c` over the collapsed
  point is `C` as a set.
* `Stacks.Curves.exists_pullback_iso_of_trivial_near_contraction_bridge` and
  `Stacks.Curves.exists_pullback_iso_of_trivial_nbhd_contraction_bridge`: an invertible module
  trivial on a neighbourhood of `C` is the pullback of an invertible module on `Y`.
* `Stacks.Curves.isPullback_subschemeι_contraction_bridge`: `C = X ×_Y Spec κ(y)`.
* `Stacks.Curves.exists_pullback_iso_of_pullback_subschemeι_iso_unit_contraction_bridge`: an
  invertible module trivial on `C` is the pullback of an invertible module on `Y`.

## References

* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- A contraction of a rational bridge is proper, and its target is locally Noetherian. -/
private theorem isProper_and_isLocallyNoetherian_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) : IsProper c ∧ IsLocallyNoetherian Y := by
  obtain ⟨g, hcg, hg, -⟩ :=
    exists_isProper_structureMorphism_and_genus_eq_contraction_bridge k X hdim hnodal C hC c hc
  have : IsProper (c ≫ g) := by rw [hcg]; infer_instance
  exact ⟨IsProper.of_comp c g, LocallyOfFiniteType.isLocallyNoetherian g⟩

/-- The image of a rational bridge under its contraction is closed. -/
theorem isClosed_image_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    IsClosed (c.base '' (C.support : Set X)) := by
  have := (isProper_and_isLocallyNoetherian_contraction_bridge hdim hnodal hc).1
  exact c.isClosedMap _ C.support.isClosed

/-- The spectrum of the global sections of a rational bridge is a single point. -/
private theorem subsingleton_spec_globalSections_bridge {K : Type u} [Field K] {Z : Scheme.{u}}
    [Z.Over (Spec (.of K))] [IsProper (Z ↘ Spec (.of K))] {C : Z.IdealSheafData}
    (hC : IsRationalBridge K Z C) : Subsingleton (Spec Γ(C.subscheme, ⊤)) := by
  let : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed K (C.subschemeι ≫ (Z ↘ Spec (.of K)))).toField
  exact inferInstanceAs (Subsingleton (PrimeSpectrum Γ(C.subscheme, ⊤)))

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- A contraction of a rational bridge collapses the bridge to a single point. -/
theorem subsingleton_image_contraction_bridge
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    (c.base '' (C.support : Set X)).Subsingleton := by
  obtain ⟨-, a, b, -, -, hbc⟩ := hc
  have := subsingleton_spec_globalSections_bridge hC
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx hx'
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨z', rfl⟩ := hx'
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbc, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply]
  exact congrArg b.base (Subsingleton.elim _ _)

/-- A point outside the bridge is the image of a point of the closure of the complement. -/
private theorem exists_complementaryCurveι_eq_of_notMem {C : X.IdealSheafData} {x : X}
    (hx : x ∉ (C.support : Set X)) : ∃ z, (complementaryCurveι C).base z = x := by
  obtain ⟨w, hw⟩ : x ∈ Set.range (Scheme.Opens.ι C.support.compl).base := by
    rw [Scheme.Opens.range_ι]; exact hx
  exact ⟨(Scheme.Opens.ι C.support.compl).toImage.base w, by
    rw [← hw, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]⟩

/-- **A contraction of a rational bridge is an isomorphism over the complement of the image of
the bridge.** Over that open the closure `X'` of the complement maps isomorphically onto `Y`
([Stacks, Tag 0E25]), and `X'` agrees with `X` away from the bridge. -/
theorem isIso_morphismRestrict_compl_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    IsIso (c ∣_ ⟨(c.base '' (C.support : Set X))ᶜ,
      (isClosed_image_contraction_bridge hdim hnodal hc).isOpen_compl⟩) := by
  set V : Y.Opens := ⟨(c.base '' (C.support : Set X))ᶜ,
      (isClosed_image_contraction_bridge hdim hnodal hc).isOpen_compl⟩ with hV
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have := isAffineHom_complementaryCurveι_comp_contraction hdim hnodal hc
  have := isIntegralHom_intersection_toSpec_bridgeSections hdim hnodal hC
  obtain ⟨-, a, b, hpo, hac, hbc⟩ := hc
  subst hac
  have hb : b ⁻¹ᵁ V = ⊥ := by
    refine TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp ?_)
    have := subsingleton_spec_globalSections_bridge hC
    have := hC.isIntegral
    obtain ⟨z⟩ : Nonempty C.subscheme := inferInstance
    have hp : p = C.subscheme.toSpecΓ z := Subsingleton.elim _ _
    refine ⟨C.subschemeι z, ?_, ?_⟩
    · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    · rw [hp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbc]
  have ha : IsIso ((complementaryCurveι C ≫ c) ∣_ V) :=
    isIso_morphismRestrict_of_isPushout_of_preimage_eq_bot hpo V hb
  have : Surjective (complementaryCurveι C ∣_ c ⁻¹ᵁ V) := by
    refine ⟨fun x => ?_⟩
    have hx : x.1 ∉ (C.support : Set X) := fun h => x.2 ⟨x.1, h, rfl⟩
    obtain ⟨z, hz⟩ := exists_complementaryCurveι_eq_of_notMem hx
    have hzV : z ∈ complementaryCurveι C ⁻¹ᵁ c ⁻¹ᵁ V := by
      show (complementaryCurveι C).base z ∈ c ⁻¹ᵁ V
      rw [hz]; exact x.2
    exact ⟨⟨z, hzV⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz)⟩
  have : IsIso (complementaryCurveι C ∣_ c ⁻¹ᵁ V) :=
    isIso_of_isClosedImmersion_of_surjective _
  have hcomp : (complementaryCurveι C ≫ c) ∣_ V =
      complementaryCurveι C ∣_ c ⁻¹ᵁ V ≫ c ∣_ V := morphismRestrict_comp _ _ _
  have : c ∣_ V = inv (complementaryCurveι C ∣_ c ⁻¹ᵁ V) ≫ (complementaryCurveι C ≫ c) ∣_ V := by
    rw [hcomp, IsIso.inv_hom_id_assoc]
  rw [this]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ha


/-- The pushout of [Stacks, Tag 0E25] for a bridge is identified with the target of a contraction,
compatibly with the maps from `X'` and from `Spec κ(y)`. -/
private theorem exists_iso_pushoutScheme_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    ∃ (b : Spec Γ(C.subscheme, ⊤) ⟶ Y)
      (e : pushoutScheme (bridgePushoutSituation hdim hnodal hC) ≅ Y),
      C.subschemeι ≫ c = C.subscheme.toSpecΓ ≫ b ∧
      pushoutInl (bridgePushoutSituation hdim hnodal hC) ≫ e.hom = complementaryCurveι C ≫ c ∧
      pushoutInr (bridgePushoutSituation hdim hnodal hC) ≫ e.hom = b := by
  obtain ⟨-, a, b, hpo, hac, hbc⟩ := hc
  subst hac
  let s := bridgePushoutSituation hdim hnodal hC
  have hpos : IsPushout s.i s.j (complementaryCurveι C ≫ c) b := hpo
  exact ⟨b, (pushoutAlongClosedImmersionAndIntegral s).isPushout.isoIsPushout _ _ hpos, hbc,
    IsPushout.inl_isoIsPushout_hom _ _ (pushoutAlongClosedImmersionAndIntegral s).isPushout hpos,
    IsPushout.inr_isoIsPushout_hom _ _ (pushoutAlongClosedImmersionAndIntegral s).isPushout hpos⟩

/-- **The fibre of a contraction of a rational bridge over the collapsed point is the bridge.**
A point of the closure `X'` of the complement lying over that point lies in `C ∩ X'`, because
the pushout square of [Stacks, Tag 0E25] is also a fibre square. -/
theorem mem_support_of_mem_image_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {x : X}
    (hx : c x ∈ c.base '' (C.support : Set X)) : x ∈ (C.support : Set X) := by
  by_contra hxC
  obtain ⟨x₀, hx₀, hcx⟩ := hx
  obtain ⟨b, e, hbc, hea, heb⟩ := exists_iso_pushoutScheme_bridge hdim hnodal hc
  let s := bridgePushoutSituation hdim hnodal hC
  obtain ⟨x', hx'⟩ := exists_complementaryCurveι_eq_of_notMem hxC
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx₀
  obtain ⟨z, rfl⟩ := hx₀
  have hab : pushoutInl s x' = pushoutInr s (C.subscheme.toSpecΓ z) := by
    apply e.hom.homeomorph.injective
    show (pushoutInl s ≫ e.hom) x' = (pushoutInr s ≫ e.hom) (C.subscheme.toSpecΓ z)
    rw [hea, heb]
    show c ((complementaryCurveι C) x') = (C.subscheme.toSpecΓ ≫ b) z
    rw [hx', ← hbc, Scheme.Hom.comp_apply, hcx]
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hab
  have hP := pushoutSquare_isPullback s
  set d := hP.isoPullback.inv q
  have hd : s.i d = x' := by
    rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]; exact hq
  have hii : s.i ≫ complementaryCurveι C = Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subschemeι := by
    show Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_right ≫ complementaryCurveι C = _
    rw [Scheme.IdealSheafData.inclusion_subschemeι, Scheme.IdealSheafData.inclusion_subschemeι]
  apply hxC
  rw [← hx', ← hd]
  show (s.i ≫ complementaryCurveι C) d ∈ (C.support : Set X)
  rw [hii, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨Scheme.IdealSheafData.inclusion (I := C)
    (J := intersectionWithComplementaryCurveIdeal C) le_sup_left d, rfl⟩

/-- **An invertible module trivial on the inverse image of a neighbourhood of the contracted
bridge descends along the contraction.** Away from the image of the bridge the contraction is
an isomorphism, so the module is trivial above a neighbourhood of every point of the target, and
the descent of [Stacks, Tag 0C0T] applies over the complement of a single closed point. -/
theorem exists_pullback_iso_of_trivial_near_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (W : Y.Opens) (hW : c.base '' (C.support : Set X) ⊆ W)
    (eW : Nonempty (L.restrict (c ⁻¹ᵁ W).ι ≅ SheafOfModules.unit (c ⁻¹ᵁ W).toScheme.ringCatSheaf)) :
    ∃ M : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf
          (structureSheafRing Y.toRingedSpace).property M ∧
        Nonempty ((Scheme.Modules.pullback c).obj M ≅ L) := by
  set V : Y.Opens := ⟨(c.base '' (C.support : Set X))ᶜ,
      (isClosed_image_contraction_bridge hdim hnodal hc).isOpen_compl⟩ with hV
  have : IsIso (c ∣_ V) := isIso_morphismRestrict_compl_contraction_bridge hdim hnodal hc
  have : Subsingleton (Vᶜ : Set Y) := by
    refine ⟨fun p q => Subtype.ext ?_⟩
    have hp : p.1 ∈ c.base '' (C.support : Set X) := by simpa [hV] using p.2
    have hq : q.1 ∈ c.base '' (C.support : Set X) := by simpa [hV] using q.2
    exact subsingleton_image_contraction_bridge hc hp hq
  have : DiscreteTopology (Vᶜ : Set Y) := inferInstance
  refine Stacks.PicFinite.exists_isInvertible_modulePullback_iso_of_hasTrivializingTargetCover
    c V L fun z => ?_
  by_cases hz : z ∈ V
  · obtain ⟨P, hP, ePmem⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible L
    obtain ⟨x', hx'⟩ := (c ∣_ V).homeomorph.surjective ⟨z, hz⟩
    obtain ⟨y₀, hy₀⟩ := Opens.mem_iSup.mp (hP.ge (Set.mem_univ x'.1))
    set U : Y.Opens := V.ι ''ᵁ ((c ∣_ V) ''ᵁ ((c ⁻¹ᵁ V).ι ⁻¹ᵁ P y₀)) with hU
    refine ⟨U, ⟨⟨z, hz⟩, ⟨x', hy₀, hx'⟩, rfl⟩, ?_⟩
    refine ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE L (A := P y₀) ?_ (ePmem y₀).some⟩
    rintro x ⟨w, ⟨w', hw', hww'⟩, hw⟩
    have hxV : x ∈ c ⁻¹ᵁ V := by
      show c x ∈ V
      rw [← hw]; exact w.2
    have hinj : (⟨x, hxV⟩ : c ⁻¹ᵁ V) = w' := by
      refine (c ∣_ V).homeomorph.injective (Subtype.ext ?_)
      show ((c ∣_ V) ⟨x, hxV⟩).1 = ((c ∣_ V) w').1
      calc ((c ∣_ V) ⟨x, hxV⟩).1 = c x := morphismRestrict_base_coe c V _
        _ = w.1 := hw.symm
        _ = ((c ∣_ V) w').1 := by rw [← hww']; rfl
    have : x = w'.1 := congrArg Subtype.val hinj
    rw [this]
    exact hw'
  · refine ⟨W, hW ?_, ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE L le_rfl eW.some⟩⟩
    simpa [hV] using hz

/-- **An invertible module trivial on a neighbourhood of a rational bridge descends along its
contraction.** The contraction is closed and its fibre over the collapsed point is the bridge,
so the neighbourhood contains the inverse image of a neighbourhood of that point. -/
theorem exists_pullback_iso_of_trivial_nbhd_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (P : X.Opens) (hP : (C.support : Set X) ⊆ P)
    (eP : Nonempty (L.restrict P.ι ≅ SheafOfModules.unit P.toScheme.ringCatSheaf)) :
    ∃ M : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf
          (structureSheafRing Y.toRingedSpace).property M ∧
        Nonempty ((Scheme.Modules.pullback c).obj M ≅ L) := by
  have := (isProper_and_isLocallyNoetherian_contraction_bridge hdim hnodal hc).1
  let W : Y.Opens := ⟨(c.base '' (P : Set X)ᶜ)ᶜ,
    (c.isClosedMap _ P.isOpen.isClosed_compl).isOpen_compl⟩
  have hyW : c.base '' (C.support : Set X) ⊆ W := by
    rintro _ ⟨x₀, hx₀, rfl⟩ ⟨x, hxP, hx⟩
    exact hxP (hP (mem_support_of_mem_image_contraction_bridge hdim hnodal hc ⟨x₀, hx₀, hx.symm⟩))
  have hWP : c ⁻¹ᵁ W ≤ P := fun x hx => by
    by_contra h
    exact hx ⟨x, h, rfl⟩
  exact exists_pullback_iso_of_trivial_near_contraction_bridge hdim hnodal hc L W hyW
    ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE L (A := P) hWP eP.some⟩

/-! ### The fibre over the collapsed point, scheme-theoretically -/

/-- The image of a rational bridge under its contraction is the closed point `{c x}`. -/
private theorem image_eq_singleton_and_isClosed_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {x : X} (hx : x ∈ (C.support : Set X)) :
    c.base '' (C.support : Set X) = {c x} ∧ IsClosed ({c x} : Set Y) := by
  have himg : c.base '' (C.support : Set X) = {c x} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨x, hx, rfl⟩, fun z hz =>
      subsingleton_image_contraction_bridge hc hz ⟨x, hx, rfl⟩⟩
  exact ⟨himg, himg ▸ isClosed_image_contraction_bridge hdim hnodal hc⟩

/-- **A morphism from a reduced scheme whose image lies in the image of a closed immersion
factors through it.** The base change of the closed immersion is a surjective closed immersion
onto the reduced source, hence an isomorphism. -/
theorem exists_comp_eq_of_range_subset_of_isClosedImmersion {S Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (g : S ⟶ T) [IsReduced S]
    (h : Set.range g ⊆ Set.range i) : ∃ s : S ⟶ Z, s ≫ i = g := by
  have : Surjective (pullback.fst g i) := ⟨fun p => by
    have hp : p ∈ Set.range (pullback.fst g i) := by
      rw [Scheme.Pullback.range_fst]
      exact h ⟨p, rfl⟩
    exact hp⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.fst g i)
  exact ⟨inv (pullback.fst g i) ≫ pullback.snd g i, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- **The scheme-theoretic fibre of a contraction of a rational bridge over the collapsed point
is the bridge.** Let `y` be the point onto which `c` collapses `C`. The ideal `𝔪_y 𝒪_X` of the
fibre is contained in the ideal of `C`, since `C ⟶ Y` factors through `Spec k' ⟶ Y`. Conversely
the fibre meets the closure `X'` of the complement inside `X' ×_Y Spec k' = C ∩ X'`, the pushout
square of [Stacks, Tag 0E25] being cartesian; so `𝔪_y 𝒪_X + ℐ_{X'} ⊇ ℐ_C + ℐ_{X'}`, and the modular
law together with `ℐ_C ∩ ℐ_{X'} = 0` (`X` is the scheme-theoretic union of `C` and `X'`) gives
`ℐ_C ⊆ 𝔪_y 𝒪_X`. -/
theorem isPullback_subschemeι_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) {x : X} (hx : x ∈ (C.support : Set X)) :
    ∃ q : C.subscheme ⟶ Spec (Y.residueField (c x)),
      IsPullback C.subschemeι q c (Y.fromSpecResidueField (c x)) := by
  have := hC.isIntegral
  have hycl := (image_eq_singleton_and_isClosed_contraction_bridge hdim hnodal hc hx).2
  have : IsClosedImmersion (Y.fromSpecResidueField (c x)) :=
    isClosed_singleton_iff_isClosedImmersion.1 hycl
  obtain ⟨b, e, hbc, hea, heb⟩ := exists_iso_pushoutScheme_bridge hdim hnodal hc
  have hunion := hc.1
  let s := bridgePushoutSituation hdim hnodal hC
  have : IsClosedImmersion b := by
    rw [← heb]
    exact @IsClosedImmersion.comp _ _ _ (pushoutInr s) e.hom (pushoutInr_isClosedImmersion s) _
  -- `b` and `Spec κ(y) ⟶ Y` are closed immersions with the same image `{y}`
  obtain ⟨z, rfl⟩ : x ∈ Set.range C.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have hbz : b (C.subscheme.toSpecΓ z) = c (C.subschemeι z) := by
    rw [← Scheme.Hom.comp_apply, ← hbc, Scheme.Hom.comp_apply]
  have hrb : Set.range b = {c (C.subschemeι z)} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hbz⟩, fun w ⟨p, hp⟩ => ?_⟩
    have := subsingleton_spec_globalSections_bridge hC
    rw [← hp, Subsingleton.elim p (C.subscheme.toSpecΓ z), hbz]
  have hrange : Set.range (Y.fromSpecResidueField (c (C.subschemeι z))) =
      {c (C.subschemeι z)} := Scheme.range_fromSpecResidueField _
  obtain ⟨σ, hσ⟩ := exists_comp_eq_of_range_subset_of_isClosedImmersion
    (Y.fromSpecResidueField (c (C.subschemeι z))) b (by rw [hrb, hrange])
  obtain ⟨ρ, hρ⟩ := exists_comp_eq_of_range_subset_of_isClosedImmersion
    b (Y.fromSpecResidueField (c (C.subschemeι z))) (by rw [hrb, hrange])
  let q := C.subscheme.toSpecΓ ≫ σ
  have hq : C.subschemeι ≫ c = q ≫ Y.fromSpecResidueField (c (C.subschemeι z)) := by
    rw [hbc, Category.assoc, hσ]
  refine ⟨q, isPullback_of_isClosedImmersion _ _ q c hq ?_⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  set K := (Y.fromSpecResidueField (c (C.subschemeι z))).ker.comap c with hK
  have hKC : K ≤ C := by
    rw [hK, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map, hq]
    exact Scheme.Hom.le_ker_comp _ _
  refine le_antisymm hKC ?_
  -- the closed subscheme cut out by `K + ℐ_{X'}` lies in `X' ×_Y Spec k' = C ∩ X'`
  have hkey : intersectionWithComplementaryCurveIdeal C ≤ K ⊔ complementaryCurveIdeal C := by
    let T := K ⊔ complementaryCurveIdeal C
    let ιX : s.X ⟶ X := complementaryCurveι C
    let u : T.subscheme ⟶ s.X :=
      Scheme.IdealSheafData.inclusion (le_sup_right : complementaryCurveIdeal C ≤ T)
    have hu : u ≫ ιX = T.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι _
    have hea' : pushoutInl s ≫ e.hom = ιX ≫ c := hea
    have hH : (Y.fromSpecResidueField (c (C.subschemeι z))).ker ≤ (T.subschemeι ≫ c).ker := by
      show _ ≤ T.map c
      rw [Scheme.IdealSheafData.le_map_iff_comap_le]
      exact le_sup_left
    let v : T.subscheme ⟶ Spec Γ(C.subscheme, ⊤) := IsClosedImmersion.lift _ _ hH ≫ ρ
    let v' : T.subscheme ⟶ s.Y := v
    have hv : v ≫ b = T.subschemeι ≫ c := by
      rw [Category.assoc, hρ, IsClosedImmersion.lift_fac]
    have hw : u ≫ pushoutInl s = v' ≫ pushoutInr s := by
      refine (cancel_mono e.hom).1 ?_
      rw [Category.assoc, Category.assoc, hea', heb, ← Category.assoc, hu]
      exact hv.symm
    let t := (pushoutSquare_isPullback s).lift u v' hw
    have hii : s.i ≫ ιX = (intersectionWithComplementaryCurveIdeal C).subschemeι :=
      Scheme.IdealSheafData.inclusion_subschemeι _
    have ht : t ≫ (intersectionWithComplementaryCurveIdeal C).subschemeι = T.subschemeι := by
      rw [← hii, ← Category.assoc, (pushoutSquare_isPullback s).lift_fst u v' hw, hu]
    refine (Scheme.IdealSheafData.ker_subschemeι _).ge.trans ?_
    exact (Scheme.Hom.le_ker_comp t _).trans_eq (by rw [ht, Scheme.IdealSheafData.ker_subschemeι])
  -- the modular law in the lattice of ideal sheaves, and `ℐ_C ∩ ℐ_{X'} = 0`
  have hmod : (K ⊔ complementaryCurveIdeal C) ⊓ C = K ⊔ complementaryCurveIdeal C ⊓ C :=
    Scheme.IdealSheafData.ext (funext fun U => sup_inf_assoc_of_le _ (hKC U))
  calc C = (C ⊔ complementaryCurveIdeal C) ⊓ C := by rw [inf_comm, inf_sup_self]
    _ ≤ (K ⊔ complementaryCurveIdeal C) ⊓ C := inf_le_inf_right _ hkey
    _ = K := by rw [hmod, inf_comm, hunion, sup_bot_eq]

/-- **An invertible module trivial on a rational bridge descends along its contraction**: this is
the part of [Stacks, Tag 0E24] used in [Stacks, Tag 0E3N]. The scheme-theoretic fibre of the
contraction over the collapsed point `y` is the bridge
(`Stacks.Curves.isPullback_subschemeι_contraction_bridge`), which has dimension at most one and
`H¹(C, 𝒪_C) = 0` (genus zero). So an invertible module trivial on `C` is trivial on `c⁻¹(V)` for
a neighbourhood `V` of `y` (`Stacks.PicardFibreTrivial.exists_restrict_iso_unit_of_fiber`, the
theorem on formal functions), and it descends
(`Stacks.Curves.exists_pullback_iso_of_trivial_near_contraction_bridge`). -/
theorem exists_pullback_iso_of_pullback_subschemeι_iso_unit_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (eC : (Scheme.Modules.pullback C.subschemeι).obj L ≅
      SheafOfModules.unit C.subscheme.ringCatSheaf) :
    ∃ M : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf
          (structureSheafRing Y.toRingedSpace).property M ∧
        Nonempty ((Scheme.Modules.pullback c).obj M ≅ L) := by
  obtain ⟨_, _⟩ := isProper_and_isLocallyNoetherian_contraction_bridge hdim hnodal hc
  have := hC.isIntegral
  obtain ⟨z⟩ : Nonempty C.subscheme := inferInstance
  have hx : C.subschemeι z ∈ (C.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  obtain ⟨q, hpb⟩ := isPullback_subschemeι_contraction_bridge hdim hnodal hc hx
  obtain ⟨himg, hycl⟩ := image_eq_singleton_and_isClosed_contraction_bridge hdim hnodal hc hx
  have : IsClosedImmersion (Y.fromSpecResidueField (c (C.subschemeι z))) :=
    isClosed_singleton_iff_isClosedImmersion.1 hycl
  -- the bridge is the fibre, over `X`
  let φ : C.subscheme ≅ c.fiber (c (C.subschemeι z)) := hpb.isoPullback
  have hφ : φ.hom ≫ c.fiberι (c (C.subschemeι z)) = C.subschemeι := hpb.isoPullback_hom_fst
  have hφ' : c.fiberι (c (C.subschemeι z)) = φ.inv ≫ C.subschemeι :=
    ((Iso.inv_comp_eq φ).2 hφ.symm).symm
  have : IsClosedImmersion (c.fiberι (c (C.subschemeι z))) := by
    rw [hφ']
    infer_instance
  have hdimF : topologicalKrullDim (c.fiber (c (C.subschemeι z))) ≤ 1 := by
    rw [← hdim]
    exact (c.fiberι _).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  -- `H¹` of the fibre is `H¹(C, 𝒪_C) = 0`
  have hH1 : IsZero ((Stacks.PicardFibreTrivial.coh (c.fiber (c (C.subschemeι z))) 1).obj
      (SheafOfModules.unit (c.fiber (c (C.subschemeι z))).ringCatSheaf)) := by
    have hC1 : IsZero ((Stacks.PicardFibreTrivial.coh C.subscheme 1).obj
        (SheafOfModules.unit C.subscheme.ringCatSheaf)) := by
      have h := (isZero_cohomologyOverField_iff_isZero_hgroup k
        (C.subschemeι ≫ (X ↘ Spec (.of k))) _ 1).2 (isZero_Hgroup_unit_one_bridge hC)
      exact ModuleCat.isZero_iff_subsingleton.mpr (@ModuleCat.subsingleton_of_isZero k _ _ h)
    have hX := (Stacks.PicardFibreTrivial.isZero_coh_pushforward_iff C.subschemeι _ 1).2 hC1
    have : IsIso (structureSheafToPushforward φ.hom) :=
      isIso_structureSheafToPushforward_of_forall_isIso_app φ.hom fun _ => inferInstance
    let ε : (Scheme.Modules.pushforward (c.fiberι (c (C.subschemeι z)))).obj
          (SheafOfModules.unit (c.fiber (c (C.subschemeι z))).ringCatSheaf) ≅
        (Scheme.Modules.pushforward C.subschemeι).obj
          (SheafOfModules.unit C.subscheme.ringCatSheaf) :=
      (Scheme.Modules.pushforward (c.fiberι _)).mapIso
          (asIso (structureSheafToPushforward φ.hom)) ≪≫
        (Scheme.Modules.pushforwardComp φ.hom (c.fiberι _)).app _ ≪≫
        (Scheme.Modules.pushforwardCongr hφ).app _
    exact (Stacks.PicardFibreTrivial.isZero_coh_pushforward_iff (c.fiberι _) _ 1).1
      (hX.of_iso ((Stacks.PicardFibreTrivial.coh X 1).mapIso ε))
  -- `ℒ` is trivial on the fibre
  let e : (Scheme.Modules.pullback (c.fiberι (c (C.subschemeι z)))).obj L ≅
      SheafOfModules.unit (c.fiber (c (C.subschemeι z))).ringCatSheaf :=
    (Scheme.Modules.pullbackCongr hφ').app L ≪≫
      ((Scheme.Modules.pullbackComp φ.inv C.subschemeι).app L).symm ≪≫
      (Scheme.Modules.pullback φ.inv).mapIso eC ≪≫
      Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso φ.inv
  obtain ⟨V, hyV, eV⟩ :=
    Stacks.PicardFibreTrivial.exists_restrict_iso_unit_of_fiber c _ hycl hdimF hH1 L e
  exact exists_pullback_iso_of_trivial_near_contraction_bridge hdim hnodal hc L V
    (by rw [himg]; exact Set.singleton_subset_iff.2 hyV) eV

end Stacks.Curves
