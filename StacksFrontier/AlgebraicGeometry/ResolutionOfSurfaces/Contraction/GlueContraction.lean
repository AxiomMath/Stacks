module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupOpenCover
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionExistence
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChange
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurve

/-!
# Glueing a contraction defined near an exceptional curve

Let `X` be a Noetherian scheme and `E ⊆ X` a closed subscheme cut out by an ideal sheaf `D`. If an
open subscheme `U ⊆ X` containing `E` admits a contraction `c : U ⟶ V` of `E`, then so does `X`:
glue `V` and `X \ E` along `U \ E`, which `c` identifies with `V` minus the contracted point, and
glue `c` with the identity of `X \ E`. This is the construction in the proof of
[Stacks, Tag 0C2N] (1).

The glueing of two schemes along open subschemes is the pushout of the two open immersions,
which exists in the category of schemes (`AlgebraicGeometry.Scheme.IsLocallyDirected`).

## Main results

* `AlgebraicGeometry.exists_hom_of_sup_eq_top`: morphisms out of two opens covering a scheme
  which agree on the intersection glue.
* `AlgebraicGeometry.isContractionOfExceptionalCurve_of_openImmersion`: a morphism which is a
  contraction over an open containing the image of the curve and an isomorphism elsewhere is a
  contraction.
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_chart`: a contraction defined on
  an open neighbourhood of the curve glues to a contraction of the whole scheme.

## References

* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Equal composites of morphisms of schemes agree on underlying points. -/
private theorem base_apply_eq_of_comp_eq {X Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (x : X) :
    g.base (f.base x) = g'.base (f'.base x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]

/-! ### Pushouts of open immersions -/

section PushoutOpenImmersion

variable {W A B : Scheme.{u}} (i₁ : W ⟶ A) (i₂ : W ⟶ B) [IsOpenImmersion i₁] [IsOpenImmersion i₂]

instance isOpenImmersion_span_map {a b : WalkingSpan} (f : a ⟶ b) :
    IsOpenImmersion ((span i₁ i₂).map f) := by
  rcases f with (_ | _ | _) <;>
    simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id, span_zero, span_left,
      span_right, span_map_fst, span_map_snd] <;>
    infer_instance

instance : HasPushout i₁ i₂ :=
  inferInstanceAs (HasColimit (span i₁ i₂))

/-- The first inclusion into the pushout of two open immersions is an open immersion. -/
instance : IsOpenImmersion (pushout.inl i₁ i₂) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span i₁ i₂) _))

/-- The second inclusion into the pushout of two open immersions is an open immersion. -/
instance : IsOpenImmersion (pushout.inr i₁ i₂) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span i₁ i₂) _))

/-- **The two open subschemes glued by a pushout of open immersions cover it.** -/
theorem pushout_inl_or_inr (x : (pushout i₁ i₂ : Scheme.{u})) :
    x ∈ Set.range (pushout.inl i₁ i₂).base ∨ x ∈ Set.range (pushout.inr i₁ i₂).base := by
  obtain ⟨k, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span i₁ i₂) x
  rcases k with (_ | (_ | _))
  · refine Or.inl ⟨i₁.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun g => g.base y) (colimit.w (span i₁ i₂) WalkingSpan.Hom.fst)
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

/-- **The two open subschemes glued by a pushout of open immersions meet exactly along the
image of the common open subscheme.** -/
theorem pushout_inl_eq_inr_iff (a : A) (b : B) :
    (pushout.inl i₁ i₂).base a = (pushout.inr i₁ i₂).base b ↔
      ∃ w : W, i₁.base w = a ∧ i₂.base w = b := by
  refine ⟨fun h => ?_, fun ⟨w, ha, hb⟩ => ?_⟩
  · obtain ⟨k, fi, fj, x, hx, hx'⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (span i₁ i₂) (i := WalkingSpan.left)
        (j := WalkingSpan.right)).1 h
    rcases k with (_ | (_ | _))
    · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      obtain rfl : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      exact ⟨x, by simpa using hx, by simpa using hx'⟩
    · change WidePushoutShape.Hom _ _ at fj
      nomatch fj
    · change WidePushoutShape.Hom _ _ at fi
      nomatch fi
  · subst ha hb
    exact base_apply_eq_of_comp_eq pushout.condition w

end PushoutOpenImmersion

/-! ### Glueing morphisms on two opens -/

/-- Two opens with join `⊤` form the open cover indexed by `Bool`. -/
private theorem isOpenCover_cond_of_sup_eq_top {X : Scheme.{u}} {U V : X.Opens} (h : U ⊔ V = ⊤) :
    IsOpenCover fun t => cond t U V := by
  change (⨆ t, cond t U V) = ⊤
  simpa [iSup_bool_eq] using h

/-- **Morphisms out of a scheme covered by two opens glue.** If `X = U ∪ V` and morphisms out of
`U` and `V` agree on `U ∩ V`, they are the restrictions of a morphism out of `X`. -/
theorem exists_hom_of_sup_eq_top {X Y : Scheme.{u}} (U V : X.Opens) (h : U ⊔ V = ⊤)
    (fU : U.toScheme ⟶ Y) (fV : V.toScheme ⟶ Y)
    (hUV : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ fU = X.homOfLE inf_le_right ≫ fV) :
    ∃ f : X ⟶ Y, U.ι ≫ f = fU ∧ V.ι ≫ f = fV := by
  let C := X.openCoverOfIsOpenCover _ (isOpenCover_cond_of_sup_eq_top h)
  let fs : ∀ t : C.I₀, C.X t ⟶ Y := fun t => match t with
    | true => fU
    | false => fV
  have hP := isPullback_opens_inf U V
  have hUV' : pullback.fst U.ι V.ι ≫ fU = pullback.snd U.ι V.ι ≫ fV := by
    rw [← cancel_epi hP.isoPullback.hom, hP.isoPullback_hom_fst_assoc,
      hP.isoPullback_hom_snd_assoc, hUV]
  have hVV : pullback.fst V.ι V.ι ≫ fV = pullback.snd V.ι V.ι ≫ fV := by
    rw [(cancel_mono V.ι).1 pullback.condition]
  have hUU : pullback.fst U.ι U.ι ≫ fU = pullback.snd U.ι U.ι ≫ fU := by
    rw [(cancel_mono U.ι).1 pullback.condition]
  have hVU : pullback.fst V.ι U.ι ≫ fV = pullback.snd V.ι U.ι ≫ fU := by
    rw [← cancel_epi (pullbackSymmetry U.ι V.ι).hom, pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc, hUV']
  have hfs : ∀ a b, pullback.fst (C.f a) (C.f b) ≫ fs a =
      pullback.snd (C.f a) (C.f b) ≫ fs b := fun a b =>
    match a, b with
    | true, true => hUU
    | true, false => hUV'
    | false, true => hVU
    | false, false => hVV
  exact ⟨C.glueMorphisms fs hfs, C.ι_glueMorphisms fs hfs true, C.ι_glueMorphisms fs hfs false⟩

/-! ### A local criterion for a contraction -/

/-- A point of an open subscheme lies in the support of the restricted ideal sheaf iff its image
lies in the support. -/
private theorem mem_support_comap_ι_iff {X : Scheme.{u}} (D : X.IdealSheafData) (U : X.Opens)
    (y : U) : y ∈ ((D.comap U.ι).support : Set U.toScheme) ↔ U.ι.base y ∈ (D.support : Set X) := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The pullback of an ideal sheaf along a morphism whose image misses its support is the unit
ideal sheaf. -/
private theorem comap_eq_top_of_forall_notMem_support {U X : Scheme.{u}} (D : X.IdealSheafData)
    (j : U ⟶ X) (h : ∀ y, j.base y ∉ (D.support : Set X)) : D.comap j = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext y
  simp only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
    Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  exact h y

/-- The inverse image of the reduced ideal sheaf of a closed point along an open immersion
missing it is the unit ideal sheaf. -/
theorem vanishingIdeal_singleton_comap_eq_top {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (z : X) (hz : IsClosed ({z} : Set X)) (hzj : z ∉ Set.range j.base) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)).comap j = ⊤ :=
  comap_eq_top_of_forall_notMem_support _ j fun y hy => hzj
    ⟨y, by rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hy⟩

/-- **A contraction may be recognised near its centre.** Let `b : X ⟶ X'` be a morphism to a
Noetherian scheme and `D` an effective Cartier divisor on `X` with nonempty support. Suppose that
an open immersion `j : V' ⟶ X'` and an open `W` of `X'` cover `X'`, that over `W` the morphism
`b` is an isomorphism and `D` is trivial, and that over the image of `j` the morphism `b` is a
contraction `c : U ⟶ V'` of the restriction of `D` to `U = b⁻¹(j(V'))`. Then `b` is a
contraction of `D`.

The centre is the image under `j` of the centre of `c`; that `b` is the blowup there is checked
on the cover of the blowup by the parts over `j(V')`, where it is the blowup of `V'` by flat base
change ([Stacks, Tag 0805]), and over `W`, where the blowup is an isomorphism. -/
theorem isContractionOfExceptionalCurve_of_openImmersion {X X' V' : Scheme.{u}} [IsNoetherian X']
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hne : (D.support : Set X).Nonempty) (b : X ⟶ X') (U₀ : X.Opens) (c : U₀.toScheme ⟶ V')
    (hc : IsContractionOfExceptionalCurve (D.comap U₀.ι) c) (j : V' ⟶ X') [IsOpenImmersion j]
    (hjc : U₀.ι ≫ b = c ≫ j) (hpre : b ⁻¹ᵁ j.opensRange = U₀) (W : X'.Opens)
    (hcov : j.opensRange ⊔ W = ⊤) (hW : IsIso (b ∣_ W)) (hDW : D.comap (b ⁻¹ᵁ W).ι = ⊤) :
    IsContractionOfExceptionalCurve D b := by
  obtain ⟨-, v, hv, hreg, hdim, hDc, ε, hε⟩ := hc
  set z : X' := j.base v with hzdef
  have hmem : ∀ y : X', y ∈ j.opensRange ∨ y ∈ W := fun y => by
    have : y ∈ (j.opensRange ⊔ W : X'.Opens) := by rw [hcov]; trivial
    exact this
  -- the support of `D` lies over `z`, and misses `b⁻¹ W`
  have hsuppW : ∀ x ∈ (D.support : Set X), b.base x ∉ W := by
    intro x hx hxW
    have h' := (mem_support_comap_ι_iff D (b ⁻¹ᵁ W) ⟨x, hxW⟩).2 hx
    rw [hDW, Scheme.IdealSheafData.support_top] at h'
    exact h'
  have hmapz : ∀ x ∈ (D.support : Set X), b.base x = z := by
    intro x hx
    have hxU : x ∈ U₀ := by
      rw [← hpre]
      exact (hmem (b.base x)).resolve_right (hsuppW x hx)
    have h' := (mem_support_comap_ι_iff D U₀ ⟨x, hxU⟩).2 hx
    rw [hDc, Scheme.IdealSheafData.support_comap] at h'
    have hcv : c.base ⟨x, hxU⟩ = v := h'
    rw [hzdef, ← hcv]
    exact base_apply_eq_of_comp_eq hjc ⟨x, hxU⟩
  have hzW : z ∉ W := by
    obtain ⟨x, hx⟩ := hne
    intro hz
    exact hsuppW x hx (by rw [hmapz x hx]; exact hz)
  have hz : IsClosed ({z} : Set X') := by
    rw [← isOpen_compl_iff]
    have hset : ({z} : Set X')ᶜ = (W : Set X') ∪ j.base '' ({v}ᶜ) := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_image]
      constructor
      · intro hy
        rcases hmem y with ⟨w, rfl⟩ | h
        · exact Or.inr ⟨w, fun hw => hy (by rw [hw]), rfl⟩
        · exact Or.inl h
      · rintro (h | ⟨w, hw, rfl⟩)
        · rintro rfl
          exact hzW h
        · intro h
          exact hw (j.isOpenEmbedding.injective h)
    rw [hset]
    exact W.isOpen.union (j.isOpenEmbedding.isOpenMap _ hv.isOpen_compl)
  -- the local ring at the centre
  let es : X'.presheaf.stalk z ≅ V'.presheaf.stalk v := asIso (j.stalkMap v)
  have := hreg
  have hreg' : IsRegularLocalRing (X'.presheaf.stalk z) :=
    IsRegularLocalRing.of_ringEquiv es.symm.commRingCatIsoToRingEquiv
  have hdim' : ringKrullDim (X'.presheaf.stalk z) = 2 := by
    rwa [es.commRingCatIsoToRingEquiv.ringKrullDim]
  -- the ideal sheaf of the centre
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X') with hIdef
  have hIj : I.comap j = Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V') :=
    pointIdeal_comap_isOpenImmersion j v hv hz
  have hIW : I.comap W.ι = ⊤ :=
    vanishingIdeal_singleton_comap_eq_top W.ι z hz (by rwa [Scheme.Opens.range_ι])
  have hDI : D = I.comap b := by
    let O : Bool → X.Opens := fun t => cond t U₀ (b ⁻¹ᵁ W)
    refine Stacks.GenericFlatness.idealSheafData_eq_of_comap_eq (fun t => (O t).ι)
      (fun _ => inferInstance) ?_ fun t => ?_
    · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
      rcases hmem (b.base x) with h | h
      · refine ⟨true, ?_⟩
        rw [Scheme.Opens.range_ι]
        show x ∈ U₀
        rw [← hpre]
        exact h
      · exact ⟨false, by rw [Scheme.Opens.range_ι]; exact h⟩
    · cases t
      · show D.comap (b ⁻¹ᵁ W).ι = (I.comap b).comap (b ⁻¹ᵁ W).ι
        rw [hDW, ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι,
          Scheme.IdealSheafData.comap_comp, hIW, Scheme.IdealSheafData.comap_top]
      · show D.comap U₀.ι = (I.comap b).comap U₀.ι
        rw [hDc, ← Scheme.IdealSheafData.comap_comp, hjc, Scheme.IdealSheafData.comap_comp,
          hIj]
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap b) := hDI ▸ hD
  rw [hDI]
  refine isContractionOfExceptionalCurve_of_isIso_blowUpClassifying z hz hreg' hdim' b hcart ?_
  intro g hg
  subst hg
  obtain ⟨hj, hjo, hjcomm, hjrange⟩ : ∃ hj : blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V')) ⟶ blowUp I,
      IsOpenImmersion hj ∧
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V')) ≫ j =
          hj ≫ blowUpToBase I ∧
        Set.range hj.base = (blowUpToBase I).base ⁻¹' Set.range j.base := by
    rw [← hIj]
    exact exists_isOpenImmersion_blowUp_comap I j
  have := hjo
  have hOcov := isOpenCover_cond_of_sup_eq_top (U := hj.opensRange) (V := blowUpToBase I ⁻¹ᵁ W)
    (top_le_iff.1 fun y _ => by
      rcases hmem ((blowUpToBase I).base y) with h | h
      · refine Or.inl ?_
        show y ∈ Set.range hj.base
        rw [hjrange]
        exact h
      · exact Or.inr h)
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hOcov fun t => ?_
  rw [MorphismProperty.isomorphisms.iff]
  cases t
  · -- over `W` both the blowup and `b` are isomorphisms
    have hbW : IsIso ((g ≫ blowUpToBase I) ∣_ W) := hW
    rw [morphismRestrict_comp] at hbW
    let C : X'.Opens := I.support.compl
    have hWle : W ≤ C := by
      intro y hy
      show y ∉ (I.support : Set X')
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rintro rfl
      exact hzW hy
    have : IsIso (blowUpToBase I ∣_ W) := by
      have h₁ := isIso_blowUp_restrict_compl_support I
      have h₂ : IsIso (blowUpToBase I ∣_ C ∣_ (C.ι ⁻¹ᵁ W)) := inferInstance
      have e := morphismRestrictRestrict (blowUpToBase I) C (C.ι ⁻¹ᵁ W) ≪≫
        morphismRestrictEq (blowUpToBase I)
          (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
            inf_eq_right.2 hWle])
      exact (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e |>.1 h₂
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g ∣_ blowUpToBase I ⁻¹ᵁ W)
      (blowUpToBase I ∣_ W) inferInstance hbW
  · -- over the image of `j` the classifying morphism is the given contraction
    have hpreO : g ⁻¹ᵁ hj.opensRange = U₀ := by
      rw [← hpre]
      ext x
      show g.base x ∈ Set.range hj.base ↔ _
      rw [hjrange]
      rfl
    have hrange : Set.range (U₀.ι ≫ g).base ⊆ Set.range hj.base := by
      rintro _ ⟨x, rfl⟩
      have hx : U₀.ι.base x ∈ g ⁻¹ᵁ hj.opensRange := by rw [hpreO]; exact x.2
      exact hx
    let g₀ := IsOpenImmersion.lift hj (U₀.ι ≫ g) hrange
    have hg₀ : g₀ ≫ blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V')) = c := by
      rw [← cancel_mono j, Category.assoc, hjcomm, ← Category.assoc, IsOpenImmersion.lift_fac,
        Category.assoc, hjc]
    have hcart' : Stacks.Blowup.IsCartierOver
        (Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V')) (Over.mk c) := by
      show Stacks.Divisors.IsEffectiveCartierDivisor
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V')).comap c)
      rw [← hDc]
      exact Stacks.Divisors.isPullbackDefined_of_flat U₀.ι D hD
    have hg₀ε : g₀ = ε.hom := (blowUpLift_unique _ c hcart' g₀ hg₀).trans
      (blowUpLift_unique _ c hcart' ε.hom hε).symm
    have : IsIso g₀ := hg₀ε ▸ inferInstance
    have heq : g ∣_ hj.opensRange = (X.isoOfEq hpreO).hom ≫ g₀ ≫ hj.isoOpensRange.hom := by
      rw [← cancel_mono hj.opensRange.ι, morphismRestrict_ι, Category.assoc, Category.assoc,
        Scheme.Hom.isoOpensRange_hom_ι, IsOpenImmersion.lift_fac, Scheme.isoOfEq_hom_ι_assoc]
    show IsIso (g ∣_ hj.opensRange)
    rw [heq]
    infer_instance

/-! ### Glueing a contraction defined near the curve -/

/-- **A contraction defined on an open neighbourhood of the curve glues to a contraction of the
whole scheme.** Let `X` be Noetherian, `D` an effective Cartier divisor on `X` with nonempty
support, `U ⊆ X` an open containing the support, and `c : U ⟶ V'` a contraction of the
restriction of `D` to `U`. Glueing `V'` and the complement `X \ E` of the support along
`U \ E` — which `c` maps isomorphically onto `V'` minus the contracted point — gives a scheme
`X'` with open immersions `j : V' ⟶ X'` and `k : X \ E ⟶ X'` covering it, and glueing `c` with
the identity of `X \ E` gives a contraction `b : X ⟶ X'` of `D`, with `b⁻¹(j(V')) = U` and
`b⁻¹(k(X \ E)) = X \ E`, and `b` is an isomorphism over `k(X \ E)`. The open `X \ E` is
passed as `W₀` together with the equation describing it. This is the construction in the proof of
[Stacks, Tag 0C2N] (1). -/
theorem exists_isContractionOfExceptionalCurve_of_chart {X V' : Scheme.{u}} [IsNoetherian X]
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hne : (D.support : Set X).Nonempty) (U₀ : X.Opens) (hsupp : (D.support : Set X) ⊆ U₀)
    (c : U₀.toScheme ⟶ V') (hc : IsContractionOfExceptionalCurve (D.comap U₀.ι) c)
    (W₀ : X.Opens) (hW₀ : (W₀ : Set X) = (D.support : Set X)ᶜ) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (j : V' ⟶ X') (k : W₀.toScheme ⟶ X')
      (_ : IsOpenImmersion j) (_ : IsOpenImmersion k), U₀.ι ≫ b = c ≫ j ∧ W₀.ι ≫ b = k ∧
        b ⁻¹ᵁ j.opensRange = U₀ ∧ b ⁻¹ᵁ k.opensRange = W₀ ∧
        j.opensRange ⊔ k.opensRange = ⊤ ∧ IsIso (b ∣_ k.opensRange) ∧
        IsContractionOfExceptionalCurve D b := by
  obtain ⟨hV'N, v, hv, -, -, hDc, ε, hε⟩ := id hc
  have hmemW₀ : ∀ x : X, x ∈ W₀ ↔ x ∉ (D.support : Set X) := fun x => Set.ext_iff.1 hW₀ x
  let V'' : V'.Opens := ⟨({v} : Set V')ᶜ, hv.isOpen_compl⟩
  let O' : U₀.toScheme.Opens := c ⁻¹ᵁ V''
  have hO' : ∀ y : U₀.toScheme, y ∈ O' ↔ U₀.ι.base y ∈ W₀ := by
    intro y
    have h2 : c.base y = v ↔ U₀.ι.base y ∈ (D.support : Set X) := by
      rw [← mem_support_comap_ι_iff D U₀ y, hDc, Scheme.IdealSheafData.support_comap]
      simp [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rw [hmemW₀]
    exact not_congr h2
  have : IsIso (c ∣_ V'') := isIso_morphismRestrict_compl_of_blowUp_iso _ v hv
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ε hε
  let i₁ : O'.toScheme ⟶ V' := O'.ι ≫ c
  have : IsOpenImmersion i₁ := by
    show IsOpenImmersion (O'.ι ≫ c)
    rw [← morphismRestrict_ι c V'']
    infer_instance
  have hrange₂ : Set.range (O'.ι ≫ U₀.ι).base ⊆ Set.range W₀.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hO' _).1 y.2
  let i₂ : O'.toScheme ⟶ W₀.toScheme := IsOpenImmersion.lift W₀.ι (O'.ι ≫ U₀.ι) hrange₂
  have hi₂ : i₂ ≫ W₀.ι = O'.ι ≫ U₀.ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion i₂ := by
    have : IsOpenImmersion (i₂ ≫ W₀.ι) := by rw [hi₂]; infer_instance
    exact IsOpenImmersion.of_comp i₂ W₀.ι
  let j := pushout.inl i₁ i₂
  let k := pushout.inr i₁ i₂
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (pushout.inl i₁ i₂))
  have : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (pushout.inr i₁ i₂))
  have hcond : i₁ ≫ j = i₂ ≫ k := pushout.condition
  have hcovX : U₀ ⊔ W₀ = ⊤ := top_le_iff.1 fun x _ =>
    (em (x ∈ (D.support : Set X))).imp (fun hx => hsupp hx) (hmemW₀ x).2
  have hrangeq : Set.range (U₀ ⊓ W₀).ι.base ⊆ Set.range (O'.ι ≫ U₀.ι).base := by
    rintro _ ⟨⟨x, hxU, hxW⟩, rfl⟩
    exact ⟨⟨⟨x, hxU⟩, (hO' ⟨x, hxU⟩).2 hxW⟩, rfl⟩
  let q := IsOpenImmersion.lift (O'.ι ≫ U₀.ι) (U₀ ⊓ W₀).ι hrangeq
  have hq : q ≫ O'.ι ≫ U₀.ι = (U₀ ⊓ W₀).ι := IsOpenImmersion.lift_fac _ _ _
  have hqU : X.homOfLE (inf_le_left : U₀ ⊓ W₀ ≤ U₀) = q ≫ O'.ι := by
    rw [← cancel_mono U₀.ι, Scheme.homOfLE_ι, Category.assoc, hq]
  have hqW : X.homOfLE (inf_le_right : U₀ ⊓ W₀ ≤ W₀) = q ≫ i₂ := by
    rw [← cancel_mono W₀.ι, Scheme.homOfLE_ι, Category.assoc, hi₂, hq]
  obtain ⟨b, hbU, hbW⟩ := exists_hom_of_sup_eq_top U₀ W₀ hcovX (c ≫ j) k (by
    rw [hqU, hqW, Category.assoc, Category.assoc, ← Category.assoc O'.ι c j]
    exact congrArg (q ≫ ·) hcond)
  have hbUx := base_apply_eq_of_comp_eq hbU
  have hbWx : ∀ x : W₀.toScheme, b.base (W₀.ι.base x) = k.base x := fun x => by
    rw [← hbW]
    rfl
  have hpreJ : b ⁻¹ᵁ j.opensRange = U₀ := by
    ext x
    constructor
    · intro hx
      by_contra hxU
      have hxW : x ∈ W₀ := (show x ∈ (U₀ ⊔ W₀ : X.Opens) by rw [hcovX]; trivial).resolve_left hxU
      obtain ⟨y, hy⟩ := hx
      have hy' : j.base y = k.base ⟨x, hxW⟩ := by
        rw [hy]
        exact hbWx ⟨x, hxW⟩
      obtain ⟨o, -, ho⟩ := (pushout_inl_eq_inr_iff i₁ i₂ y ⟨x, hxW⟩).1 hy'
      have := base_apply_eq_of_comp_eq hi₂ o
      rw [ho] at this
      exact hxU (by rw [show x = W₀.ι.base ⟨x, hxW⟩ from rfl, this]; exact (O'.ι.base o).2)
    · intro hxU
      exact ⟨c.base ⟨x, hxU⟩, (hbUx ⟨x, hxU⟩).symm⟩
  have hpreK : b ⁻¹ᵁ k.opensRange = W₀ := by
    ext x
    constructor
    · intro hx
      by_contra hxW
      have hxU : x ∈ U₀ := hsupp (by_contra fun h => hxW ((hmemW₀ x).2 h))
      obtain ⟨w, hw⟩ := hx
      have hcx : c.base ⟨x, hxU⟩ = v := by
        by_contra hne'
        exact hxW ((hO' ⟨x, hxU⟩).1 hne')
      have hw' : j.base v = k.base w := by
        rw [hw, ← hcx]
        exact (hbUx ⟨x, hxU⟩).symm
      obtain ⟨o, ho, -⟩ := (pushout_inl_eq_inr_iff i₁ i₂ v w).1 hw'
      exact o.2 ho
    · intro hxW
      exact ⟨⟨x, hxW⟩, (hbWx ⟨x, hxW⟩).symm⟩
  have hcovX' : j.opensRange ⊔ k.opensRange = ⊤ :=
    top_le_iff.1 fun x _ => pushout_inl_or_inr i₁ i₂ x
  -- the glued scheme is Noetherian
  have : IsNoetherian (pushout i₁ i₂ : Scheme.{u}) := by
    have : IsLocallyNoetherian (pushout i₁ i₂ : Scheme.{u}) := by
      rw [isLocallyNoetherian_iff_openCover
        ((pushout i₁ i₂ : Scheme.{u}).openCoverOfIsOpenCover _
          (isOpenCover_cond_of_sup_eq_top hcovX'))]
      intro t
      cases t
      · show IsLocallyNoetherian k.opensRange.toScheme
        exact isLocallyNoetherian_of_isOpenImmersion k.isoOpensRange.inv
      · show IsLocallyNoetherian j.opensRange.toScheme
        exact isLocallyNoetherian_of_isOpenImmersion j.isoOpensRange.inv
    have : CompactSpace (pushout i₁ i₂ : Scheme.{u}) := by
      have hW₀c : CompactSpace W₀.toScheme :=
        isCompact_iff_compactSpace.1 (NoetherianSpace.isCompact (W₀ : Set X))
      refine ⟨?_⟩
      have hu : (Set.univ : Set (pushout i₁ i₂ : Scheme.{u})) =
          Set.range j.base ∪ Set.range k.base :=
        Set.eq_univ_of_forall (pushout_inl_or_inr i₁ i₂) |>.symm
      rw [hu]
      exact (isCompact_range j.continuous).union (isCompact_range k.continuous)
    exact ⟨⟩
  have hbK : IsIso (b ∣_ k.opensRange) := by
    have heq : b ∣_ k.opensRange = (X.isoOfEq hpreK).hom ≫ k.isoOpensRange.hom := by
      have h' : (X.isoOfEq hpreK).hom ≫ W₀.ι ≫ b = (b ⁻¹ᵁ k.opensRange).ι ≫ b := by
        rw [Scheme.isoOfEq_hom_ι_assoc]
      rw [hbW] at h'
      rw [← cancel_mono k.opensRange.ι, morphismRestrict_ι, Category.assoc,
        Scheme.Hom.isoOpensRange_hom_ι, h']
    rw [heq]
    infer_instance
  have hDK : D.comap (b ⁻¹ᵁ k.opensRange).ι = ⊤ := by
    rw [hpreK]
    exact comap_eq_top_of_forall_notMem_support D W₀.ι fun y => (hmemW₀ _).1 y.2
  exact ⟨pushout i₁ i₂, b, j, k, inferInstance, inferInstance, hbU, hbW, hpreJ, hpreK, hcovX',
    hbK, isContractionOfExceptionalCurve_of_openImmersion D hD hne b U₀ c hc j hbU hpreJ
      k.opensRange hcovX' hbK hDK⟩

end AlgebraicGeometry

end
