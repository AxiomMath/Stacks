module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelUniqueness
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Irreducible
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme

/-!
# Several minimal models in genus zero

Let `C` be a smooth projective curve of genus `0` over the fraction field `K` of a discrete
valuation ring `R`, with `H⁰(C, 𝒪_C) = K`. We prove [Stacks, Tag 0CDA]: if `C` has two minimal
models which are not isomorphic as models, then the special fibre of every minimal model is the
projective line over the residue field `k` of `R`.

## Main definitions

* `Stacks.Models.IsProjectiveLineSpecialFiber`: the special fibre `X ×_R k` of `p : X ⟶ Spec R`
  is isomorphic to `𝐏¹_k` over `k`.

## Main results

* `Stacks.Models.isProjectiveLineSpecialFiber_of_isMinimalModel`: [Stacks, Tag 0CDA].
* `RegularProperModelSituation.subsingleton_and_exists_iso_projectiveLineProj_of_contraction`:
  contracting one of two meeting exceptional components of the special fibre gives a model whose
  special fibre is irreducible and is `𝐏¹_k`.

## Implementation notes

The proof differs from the source's, which goes through the numerical type of a minimal model
([Stacks, Tags 0CA6, 0C8S]). Let `X` be a minimal model whose special fibre is not `𝐏¹_k`. The
comparison of [Stacks, Tag 0C6B] shows that any other minimal model `N` is isomorphic to `X` as a
model, provided that for every sequence of point blowups `W ⟶ X` every exceptional curve of the
first kind on `W` is contracted to a point of `X`. Were some curve not contracted, follow it down
the blowups `W ⟶ ⋯ ⟶ X`: at some stage `Bl_v V ⟶ V` it is an exceptional curve meeting the
exceptional curve of the blowup. Then [Stacks, Tag 0C6A] says the special fibre of `Bl_v V` is
the sum of these two curves, with multiplicities one, and both are `𝐏¹_k`; contracting the
exceptional curve of the blowup ([Stacks, Tag 0C6C]) shows that `V` has an irreducible special
fibre `Γ`, hence no exceptional curve, so `V ≅ X`. And `Γ ≅ 𝐏¹_k`: multiplicity one of the
exceptional curve says that the local equation of `Γ` at `v` is a regular parameter, so `Γ` is
regular at `v` and lifts to the blowup, onto the strict transform. This contradicts the choice
of `X`, so all minimal models are isomorphic to `X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The special fibre of `p : X ⟶ Spec R` is the projective line over the residue field, as a
scheme over the residue field. -/
def IsProjectiveLineSpecialFiber {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) : Prop :=
  ∃ e : projectiveLineProj (IsLocalRing.ResidueField R) ≅
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))),
    e.hom ≫ pullback.snd p (Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R)))) = projToSpecCoeff (IsLocalRing.ResidueField R) 1

/-- Being the projective line on the special fibre is invariant under isomorphism over `R`. -/
theorem IsProjectiveLineSpecialFiber.of_iso {X Y : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    {q : Y ⟶ Spec (.of R)} (g : X ≅ Y) (hg : g.hom ≫ q = p) (h : IsProjectiveLineSpecialFiber p) :
    IsProjectiveLineSpecialFiber q := by
  obtain ⟨e, he⟩ := h
  subst hg
  let m := pullback.map (g.hom ≫ q) (Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R)))) q (Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R)))) g.hom (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  refine ⟨e ≪≫ asIso m, ?_⟩
  simpa only [Iso.trans_hom, asIso_hom, Category.assoc, m, pullback.lift_snd, Category.comp_id]
    using he

/-- The stages of a sequence of blowups at closed points of a regular proper model are regular
proper models. -/
theorem exists_isModel_of_pointBlowupChain {C Y : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (q₀ : Y ⟶ Spec (.of R))
    (eY : C ≅ pullback q₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c q₀ eY) [IsProper q₀] (hreg : IsRegular Y) {T : Set Y} {W : Scheme.{u}}
    {q : W ⟶ Y} (hq : PointBlowupChain Y T W q) :
    ∃ eW : C ≅ pullback (q ≫ q₀) (Spec.map (CommRingCat.ofHom (algebraMap R K))),
      IsModel c (q ≫ q₀) eW ∧ IsProper (q ≫ q₀) ∧ IsRegular W := by
  induction hq with
  | refl =>
    rw [Category.id_comp]
    exact ⟨eY, hmod, inferInstance, hreg⟩
  | @step V qV hqV w hw hwT ih =>
    obtain ⟨eV, hmodV, hpropV, hregV⟩ := ih
    have := hpropV
    obtain ⟨e', hmod', hprop', hreg', -⟩ :=
      exists_isModel_pointBlowUp c hproj (qV ≫ q₀) eV hmodV hregV hw
    rw [Category.assoc]
    exact ⟨e', hmod', hprop', hreg'⟩

/-- **A regular proper model with an irreducible special fibre contains no exceptional curve of
the first kind**: such a curve would be the unique component, a minus-one index of the associated
numerical type, whose self-intersection is `0` and not `-w`. -/
theorem RegularProperModelSituation.not_hasExceptionalCurveOfFirstKind_of_subsingleton
    (S : RegularProperModelSituation.{u})
    [Subsingleton (irreducibleComponents S.specialFiber)] :
    ¬ S.X.HasExceptionalCurveOfFirstKind := by
  classical
  rintro ⟨κ, hκ, D, ε, hE⟩
  let := hκ
  obtain ⟨Z, rfl⟩ := S.exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj D κ ε
  have : Unique (irreducibleComponents S.specialFiber) := uniqueOfSubsingleton Z
  let e : Fin 1 ≃ irreducibleComponents S.specialFiber := Equiv.ofUnique _ _
  have h := S.isMinusOneIndex_associatedNumericalType_of_isExceptionalCurveOfFirstKind 1 e Z κ hE
  have h0 := AlgebraicGeometry.NumericalType.intersection_self_eq_zero_of_componentCount_eq_one
    (S.associatedNumericalType 1 e) rfl
  have hi : e.symm Z = ⟨0, (S.associatedNumericalType 1 e).componentCount_pos⟩ :=
    Subsingleton.elim _ _
  have hw := (S.associatedNumericalType 1 e).weight_pos (e.symm Z)
  have h2 : (S.associatedNumericalType 1 e).intersection (e.symm Z) (e.symm Z) = 0 := by
    rwa [hi]
  have := h.2
  omega

/-! ### The image of a curve is regular at the blown up point -/

/-- **Killing a regular parameter in a two-dimensional regular local ring.** If `φ : A ⟶ B` is
surjective with kernel generated by `g ∈ 𝔪 ∖ 𝔪²`, where `A` is regular local of dimension two,
then the maximal ideal of `B` is generated by a nonzerodivisor: `B ≅ A/(g)` is regular local of
dimension one, a discrete valuation ring ([Stacks, Tag 00NQ]). -/
theorem exists_mem_nonZeroDivisors_maximalIdeal_eq_span_of_surjective {A B : Type u}
    [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) {g : A}
    (hker : RingHom.ker φ = Ideal.span {g}) (hg : g ∈ IsLocalRing.maximalIdeal A)
    (hg2 : g ∉ IsLocalRing.maximalIdeal A ^ 2) :
    ∃ t ∈ nonZeroDivisors B, IsLocalRing.maximalIdeal B = Ideal.span {t} := by
  obtain ⟨hQreg, hQdim⟩ := quotient_isRegularLocalRing A g hg hg2
  let e : A ⧸ Ideal.span {g} ≃+* B :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have : IsRegularLocalRing B := IsRegularLocalRing.of_ringEquiv e
  have : IsNoetherianRing B := isNoetherianRing_of_ringEquiv _ e
  have : IsDomain B := IsRegularLocalRing.isDomain B
  have hB : ringKrullDim B = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    rw [hdim] at hQdim
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (A ⧸ Ideal.span {g}) = n := by
      have hne : ringKrullDim (A ⧸ Ideal.span {g}) ≠ ⊥ := ringKrullDim_ne_bot
      have hlt : ringKrullDim (A ⧸ Ideal.span {g}) < ⊤ := ringKrullDim_lt_top
      cases h : ringKrullDim (A ⧸ Ideal.span {g}) with
      | bot => exact absurd h hne
      | coe m =>
        cases m with
        | top => exact absurd (h ▸ hlt) (lt_irrefl _)
        | coe n => exact ⟨n, rfl⟩
    rw [hn] at hQdim ⊢
    have : n + 1 = 2 := by exact_mod_cast hQdim
    obtain rfl : n = 1 := by omega
    rfl
  have : IsDiscreteValuationRing B :=
    ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one B hB).out 1 3).mp
      (inferInstance : IsRegularLocalRing B)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible B
  exact ⟨t, mem_nonZeroDivisors_of_ne_zero ht.ne_zero,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht⟩

/-- The image of the maximal ideal under a surjective homomorphism of local rings is the maximal
ideal. -/
theorem map_maximalIdeal_eq_of_surjective {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : Function.Surjective φ) :
    (IsLocalRing.maximalIdeal A).map φ = IsLocalRing.maximalIdeal B :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.IsMaximal.map_of_surjective_of_ker_le hφ
      (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)))

/-- A point of the closed subscheme cut out by `D` lies in the support of `D`. -/
private theorem subschemeι_apply_mem_support {X : Scheme.{u}} (D : X.IdealSheafData)
    (z : D.subscheme) :
    D.subschemeι z ∈ (D.support : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- A point lies in the support of the inverse image of the ideal of a closed point `z` iff it
maps to `z`. -/
private theorem mem_support_comap_vanishingIdeal_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {z : Y}
    (hz : IsClosed ({z} : Set Y)) (x : X) :
    x ∈ (((Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Y)).comap f).support :
      Set X) ↔ f x = z := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **The maximal ideal of a closed point pulls back to an effective Cartier divisor on a curve
through it which is regular there.** Let `Γ` be a closed subscheme of a scheme `V`, `v` a closed
point whose local ring is regular of dimension two, and suppose the ideal of `Γ` at `v` is
generated by an element `g ∈ 𝔪_v ∖ 𝔪_v²`. Then the inverse image on `Γ` of the ideal of `v` is an
effective Cartier divisor: at the points over `v` it is the maximal ideal of `𝒪_{V,v}/(g)`, a
discrete valuation ring, and elsewhere it is the unit ideal ([Stacks, Tag 0AG8]). -/
theorem isEffectiveCartierDivisor_comap_vanishingIdeal_of_stalk_eq_span {V : Scheme.{u}} {v : V}
    (hv : IsClosed ({v} : Set V)) (Γ : V.IdealSheafData) [IsLocallyNoetherian Γ.subscheme]
    (hreg : IsRegularLocalRing (V.presheaf.stalk v)) (hdim : ringKrullDim (V.presheaf.stalk v) = 2)
    {g : V.presheaf.stalk v} (hgen : AlgebraicGeometry.IdealSheafData.stalk Γ v = Ideal.span {g})
    (hg : g ∈ IsLocalRing.maximalIdeal _) (hg2 : g ∉ IsLocalRing.maximalIdeal _ ^ 2) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V)).comap Γ.subschemeι) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun z hz => ?_
  obtain rfl : Γ.subschemeι z = v := (mem_support_comap_vanishingIdeal_iff _ hv z).1 hz
  have hsurj : Function.Surjective (Γ.subschemeι.stalkMap z).hom :=
    Γ.subschemeι.stalkMap_surjective z
  obtain ⟨t, ht, hteq⟩ := exists_mem_nonZeroDivisors_maximalIdeal_eq_span_of_surjective hdim
    (Γ.subschemeι.stalkMap z).hom hsurj
    ((AlgebraicGeometry.IdealSheafData.ker_stalkMap_subschemeι Γ z).trans hgen) hg hg2
  refine ⟨t, ht, ?_⟩
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap,
    Stacks.Divisors.stalk_vanishingIdeal_singleton_of_isClosed _ hv,
    map_maximalIdeal_eq_of_surjective _ hsurj, hteq]

/-- A morphism restricting to an isomorphism over an open `U` is injective on the points over
`U`. -/
theorem eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)] {a b : X} (ha : f a ∈ U) (hab : f a = f b) : a = b := by
  have hb : f b ∈ U := hab ▸ ha
  let a' : (f ⁻¹ᵁ U : X.Opens) := ⟨a, ha⟩
  let b' : (f ⁻¹ᵁ U : X.Opens) := ⟨b, hb⟩
  have h : (f ∣_ U) a' = (f ∣_ U) b' := Subtype.ext <|
    show ((f ∣_ U) ≫ U.ι) a' = ((f ∣_ U) ≫ U.ι) b' by rwa [morphismRestrict_ι]
  exact congrArg Subtype.val ((asIso (f ∣_ U)).hom.homeomorph.injective h)

/-- If a local homomorphism into a discrete valuation ring sends `g` to a uniformizer, then `g`
lies in `𝔪 ∖ 𝔪²`. -/
private theorem mem_maximalIdeal_and_notMem_sq_of_span_map_eq {A B : Type*} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (φ : A →+* B)
    [IsLocalHom φ] {g : A} (h : Ideal.span {φ g} = IsLocalRing.maximalIdeal B) :
    g ∈ IsLocalRing.maximalIdeal A ∧ g ∉ IsLocalRing.maximalIdeal A ^ 2 := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hne2 := maximalIdeal_ne_sq_of_eq_span (mem_nonZeroDivisors_of_ne_zero ht.ne_zero)
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht)
  refine ⟨(IsLocalRing.mem_maximalIdeal g).mpr fun hu =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (h.symm.trans (Ideal.span_singleton_eq_top.mpr (hu.map φ))), fun hg2 => hne2 ?_⟩
  refine le_antisymm ((le_of_eq h.symm).trans ?_) (Ideal.pow_le_self two_ne_zero)
  rw [Ideal.span_le, Set.singleton_subset_iff]
  have hm : (IsLocalRing.maximalIdeal A).map φ ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => (IsLocalRing.mem_maximalIdeal (φ x)).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal x).mp hx (isUnit_of_map_unit φ x hu)
  have hle : (IsLocalRing.maximalIdeal A ^ 2).map φ ≤ IsLocalRing.maximalIdeal B ^ 2 := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hm 2
  exact hle (Ideal.mem_map_of_mem _ hg2)

/-- **A curve through a regular point lifts to the blowup.** If the ideal of a closed subscheme
`Γ` at a closed point `z` with two-dimensional regular local ring is generated by an element of
`𝔪_z ∖ 𝔪_z²`, then `Γ ⟶ X'` lifts to a closed immersion into any `Y ≅ Bl_z X'` over `X'`. -/
private theorem exists_isClosedImmersion_comp_eq_subschemeι_of_blowUp_iso {X' Y : Scheme.{u}}
    [IsNoetherian X'] {z : X'} (hz : IsClosed ({z} : Set X'))
    (hregz : IsRegularLocalRing (X'.presheaf.stalk z))
    (hdimz : ringKrullDim (X'.presheaf.stalk z) = 2) {f : Y ⟶ X'}
    (eb : Y ≅ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')))
    (heb : eb.hom ≫ AlgebraicGeometry.blowUpToBase _ = f) (Γ : X'.IdealSheafData)
    {g : X'.presheaf.stalk z} (hgen : AlgebraicGeometry.IdealSheafData.stalk Γ z = Ideal.span {g})
    (hg : g ∈ IsLocalRing.maximalIdeal _) (hg2 : g ∉ IsLocalRing.maximalIdeal _ ^ 2) :
    ∃ j : Γ.subscheme ⟶ Y, IsClosedImmersion j ∧ j ≫ f = Γ.subschemeι := by
  subst heb
  have : IsLocallyNoetherian Γ.subscheme := Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have := isIso_blowUp_restrict_compl_support
    (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X'))
  obtain ⟨j₀, hj₀⟩ := Stacks.Blowup.exists_hom_blowUp_of_isEffectiveCartierDivisor _ Γ.subschemeι
    (isEffectiveCartierDivisor_comap_vanishingIdeal_of_stalk_eq_span hz Γ hregz hdimz hgen hg hg2)
  have hj : (j₀ ≫ eb.inv) ≫ eb.hom ≫ AlgebraicGeometry.blowUpToBase _ = Γ.subschemeι := by
    rw [Category.assoc, Iso.inv_hom_id_assoc, hj₀]
  have : IsSeparated (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X'))) :=
    Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase _
  have : IsClosedImmersion ((j₀ ≫ eb.inv) ≫ eb.hom ≫ AlgebraicGeometry.blowUpToBase _) := by
    rw [hj]
    infer_instance
  exact ⟨_, IsClosedImmersion.of_comp _ (eb.hom ≫ AlgebraicGeometry.blowUpToBase _), hj⟩

/-- A closed immersion whose kernel is `I` identifies its source with `I.subscheme`. -/
private theorem exists_iso_subscheme_of_ker_eq {X Γ : Scheme.{u}} (j : Γ ⟶ X)
    [IsClosedImmersion j] {I : X.IdealSheafData} (hker : j.ker = I) :
    ∃ b : Γ ≅ I.subscheme, b.hom ≫ I.subschemeι = j := by
  have hle : I.subschemeι.ker ≤ j.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hker]
  have hb := IsClosedImmersion.lift_fac _ j hle
  have := IsClosedImmersion.isIso_of_ker_eq j _ _ hb
    (by rw [Scheme.IdealSheafData.ker_subschemeι, hker])
  exact ⟨asIso (IsClosedImmersion.lift _ j hle), hb⟩

/-- A closed immersion from an irreducible scheme into `X` sending the generic point to that of a
component `C_Z` of the special fibre identifies its source with `C_Z`. -/
private theorem RegularProperModelSituation.exists_iso_componentIdeal_of_apply_genericPoint
    (S : RegularProperModelSituation.{u}) (Z : irreducibleComponents S.specialFiber)
    {Γ : Scheme.{u}} [IsIntegral Γ] (j : Γ ⟶ S.X) [IsClosedImmersion j]
    (hj : j (genericPoint Γ) = (S.specialFiberComponentPrimeDivisor Z).genericPoint) :
    ∃ b : Γ ≅ (S.specialFiberComponentIdeal Z).subscheme,
      b.hom ≫ (S.specialFiberComponentIdeal Z).subschemeι = j := by
  have hker : j.ker = S.specialFiberComponentIdeal Z := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    show closure (Set.range j) = closure (S.specialFiberι.base '' (Z.1 : Set S.specialFiber))
    rw [(S.isClosed_image_specialFiberComponent Z).closure_eq,
      ← S.closure_singleton_genericPoint_specialFiberComponent Z,
      show (S.specialFiberComponentIdeal Z).subschemeι.base
          (genericPoint (S.specialFiberComponentIdeal Z).subscheme) = j (genericPoint Γ)
        from hj.symm,
      j.isClosedEmbedding.isClosed_range.closure_eq, ← Set.image_singleton,
      j.isClosedMap.closure_image_eq_of_continuous j.continuous, genericPoint_closure,
      Set.image_univ]
  exact exists_iso_subscheme_of_ker_eq j hker

/-- If the special fibre ideal of a regular proper model is `I`, the closed subscheme cut out by
`I` is the special fibre. -/
private theorem RegularProperModelSituation.exists_iso_pullback_of_specialFiberIdeal_eq
    (T : RegularProperModelSituation.{u}) {I : T.X.IdealSheafData}
    (hI : T.specialFiberIdeal = I) :
    ∃ c : I.subscheme ≅ pullback T.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap T.R T.k))),
      c.hom ≫ pullback.fst T.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap T.R T.k))) =
        I.subschemeι := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap T.R T.k))) :=
    IsClosedImmersion.spec_of_surjective _ T.surjective_algebraMap_residueField
  have hker : (pullback.fst T.X_to_R
      (Spec.map (CommRingCat.ofHom (algebraMap T.R T.k)))).ker = I := by
    rw [← hI]
  obtain ⟨b, hb⟩ := exists_iso_subscheme_of_ker_eq _ hker
  exact ⟨b.symm, by rw [Iso.symm_hom, ← hb, Iso.inv_hom_id_assoc]⟩

/-- If the special fibre of a regular proper model has a single component, of multiplicity one,
the special fibre ideal is the ideal of that component. -/
private theorem RegularProperModelSituation.specialFiberIdeal_eq_specialFiberComponentIdeal
    (T : RegularProperModelSituation.{u}) [Subsingleton (irreducibleComponents T.specialFiber)]
    (Γ : irreducibleComponents T.specialFiber) (h : T.specialFiberMultiplicity Γ = 1) :
    T.specialFiberIdeal = T.specialFiberComponentIdeal Γ := by
  have : Unique (irreducibleComponents T.specialFiber) := uniqueOfSubsingleton Γ
  rw [T.specialFiberIdeal_eq_prod, Fintype.prod_unique,
    Subsingleton.elim (default : irreducibleComponents T.specialFiber) Γ, h, pow_one]

/-- If the special fibre consists of the components `C_D` and `C_E`, contracting `C_E` leaves a
model with an irreducible special fibre. -/
private theorem RegularProperModelSituation.subsingleton_irreducibleComponents_contractedSituation
    (S : RegularProperModelSituation.{u}) {ZD ZE : irreducibleComponents S.specialFiber}
    (hcover : ∀ Z : irreducibleComponents S.specialFiber, Z = ZD ∨ Z = ZE) {X' : Scheme.{u}}
    {f : S.X ⟶ X'} (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal ZE) f) :
    Subsingleton (irreducibleComponents (S.contractedSituation hf).specialFiber) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := (S.contractedComponentEquiv hf).surjective a
  obtain ⟨b', rfl⟩ := (S.contractedComponentEquiv hf).surjective b
  have h1 : a'.1 = ZD := (hcover a'.1).resolve_right a'.2
  have h2 : b'.1 = ZD := (hcover b'.1).resolve_right b'.2
  rw [Subtype.ext (h1.trans h2.symm)]

/-- If a component `C_Z` of multiplicity one is contracted by `f`, the special fibre ideal of the
contracted model is generated at the image of `C_Z` by an element of `𝔪 ∖ 𝔪²`. -/
private theorem RegularProperModelSituation.exists_stalk_contractedSituation_eq_span
    (S : RegularProperModelSituation.{u}) {Z : irreducibleComponents S.specialFiber}
    (hZ : S.specialFiberMultiplicity Z = 1) {X' : Scheme.{u}} {f : S.X ⟶ X'}
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal Z) f) :
    ∃ g : X'.presheaf.stalk (f (S.specialFiberComponentPrimeDivisor Z).genericPoint),
      AlgebraicGeometry.IdealSheafData.stalk (S.contractedSituation hf).specialFiberIdeal
          (f (S.specialFiberComponentPrimeDivisor Z).genericPoint) = Ideal.span {g} ∧
        g ∈ IsLocalRing.maximalIdeal _ ∧ g ∉ IsLocalRing.maximalIdeal _ ^ 2 := by
  have hTcart : Stacks.Divisors.IsEffectiveCartierDivisor
      (S.contractedSituation hf).specialFiberIdeal :=
    have := (S.contractedSituation hf).flat
    isEffectiveCartierDivisor_specialFiber (S.contractedSituation hf).residueEquiv
      (S.contractedSituation hf).X_to_R
  obtain ⟨g, -, hgspan⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor
      (S.contractedSituation hf).specialFiberIdeal hTcart
      (f (S.specialFiberComponentPrimeDivisor Z).genericPoint)
  have hst := S.stalk_specialFiberIdeal_genericPoint Z
  rw [hZ, pow_one, S.specialFiberIdeal_eq_comap_contraction hf,
    AlgebraicGeometry.IdealSheafData.stalk_comap, hgspan, Ideal.map_span,
    Set.image_singleton] at hst
  have : IsLocallyNoetherian S.X := S.isLocallyNoetherian_X
  obtain ⟨hdom, hdvr⟩ := isDiscreteValuationRing_stalk_genericPoint
    (S.specialFiberComponentIdeal Z) (S.isEffectiveCartierDivisor_specialFiberComponent Z)
  have : IsDomain
      (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor Z).genericPoint) := hdom
  have : IsDiscreteValuationRing
      (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor Z).genericPoint) := hdvr
  exact ⟨g, hgspan, mem_maximalIdeal_and_notMem_sq_of_span_map_eq
    (f.stalkMap (S.specialFiberComponentPrimeDivisor Z).genericPoint).hom hst⟩

/-- The contraction of a component `C_E` identifies no point of `X` with the generic point of
another component `C_D`. -/
private theorem RegularProperModelSituation.eq_genericPoint_of_contraction_apply_eq
    (S : RegularProperModelSituation.{u}) {ZD ZE : irreducibleComponents S.specialFiber}
    (hZ : ZD ≠ ZE) {X' : Scheme.{u}} {f : S.X ⟶ X'}
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal ZE) f) {a : S.X}
    (ha : f a = f (S.specialFiberComponentPrimeDivisor ZD).genericPoint) :
    a = (S.specialFiberComponentPrimeDivisor ZD).genericPoint := by
  obtain ⟨z, hz, -, -, hDz, eb, heb⟩ := hf.exists_blowUp_iso
  have hoff : IsIso (f ∣_ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens)) :=
    AlgebraicGeometry.isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) eb heb
  have h2 : f (S.specialFiberComponentPrimeDivisor ZD).genericPoint ∈
      (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens) := fun hmem =>
    S.genericPoint_specialFiberComponent_notMem_support hZ.symm (by
      rw [hDz]
      exact (mem_support_comap_vanishingIdeal_iff f hz _).2 hmem)
  exact eq_of_isIso_morphismRestrict f _ (by rwa [ha]) ha

/-- **Contracting one of two meeting exceptional components.** Let `C_D` and `C_E` be distinct
meeting components of the special fibre of a regular proper model which are exceptional curves of
the first kind, and let `f : X ⟶ X'` contract `C_E`. Then the special fibre of `X'` is irreducible
and, over the residue field, it is the projective line.

By [Stacks, Tag 0C6A] the special fibre of `X` is `C_D + C_E` with multiplicities one and `C_D` is
`𝐏¹_k`. The special fibre of `X'` is `Γ = f(C_D)`, with multiplicity one by [Stacks, Tag 0C6C].
Multiplicity one of `C_E` says that the local equation of `Γ` at the centre `x` of the contraction
is not in `𝔪_x²`, so `Γ` is regular at `x` and the ideal of `x` pulls back to an effective
Cartier divisor on `Γ`; the universal property of the blowup lifts `Γ ⟶ X'` to a closed immersion
`Γ ⟶ X` with image `C_D`, so `Γ ≅ C_D ≅ 𝐏¹_k`. -/
theorem RegularProperModelSituation.subsingleton_and_exists_iso_projectiveLineProj_of_contraction
    (S : RegularProperModelSituation.{u}) {ZD ZE : irreducibleComponents S.specialFiber}
    (hZ : ZD ≠ ZE) {κD κE : Type u} [Field κD] [Field κE]
    {eD : projectiveLineProj κD ≅ (S.specialFiberComponentIdeal ZD).subscheme}
    {eE : projectiveLineProj κE ≅ (S.specialFiberComponentIdeal ZE).subscheme}
    (hD : (S.specialFiberComponentIdeal ZD).IsExceptionalCurveOfFirstKind κD eD)
    (hE : (S.specialFiberComponentIdeal ZE).IsExceptionalCurveOfFirstKind κE eE)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal ZD ⊔ S.specialFiberComponentIdeal ZE).subscheme)
    {X' : Scheme.{u}} {f : S.X ⟶ X'}
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal ZE) f) :
    Subsingleton (irreducibleComponents (S.contractedSituation hf).specialFiber) ∧
      ∀ p : X' ⟶ Spec (.of S.R), f ≫ p = S.X_to_R →
        ∃ e : projectiveLineProj S.k ≅
            pullback p (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))),
          e.hom ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) =
            projToSpecCoeff S.k 1 := by
  classical
  have hcover :=
    (S.forall_eq_or_eq_and_multiplicity_eq_of_isExceptionalCurveOfFirstKind hZ hD hE hmeet).1
  have hmult := S.specialFiberMultiplicity_eq_one_of_isExceptionalCurveOfFirstKind hZ hD hE hmeet
  have hsub := S.subsingleton_irreducibleComponents_contractedSituation hcover hf
  refine ⟨hsub, fun p hp => ?_⟩
  obtain rfl : (S.contractedSituation hf).X_to_R = p :=
    (S.existsUnique_comp_eq_X_to_R hf).unique (S.contraction_comp_contractionToBase hf) hp
  obtain ⟨ΓZ, hΓZ⟩ : ∃ W, W = S.contractedComponentEquiv hf ⟨ZD, hZ⟩ := ⟨_, rfl⟩
  have hTΓ := (S.contractedSituation hf).specialFiberIdeal_eq_specialFiberComponentIdeal ΓZ
    (by rw [hΓZ, S.specialFiberMultiplicity_contractedComponentEquiv hf ⟨ZD, hZ⟩, hmult ZD])
  obtain ⟨z, hz, hregz, hdimz, hDz, eb, heb⟩ := hf.exists_blowUp_iso
  have hξEz : f (S.specialFiberComponentPrimeDivisor ZE).genericPoint = z := by
    rw [← mem_support_comap_vanishingIdeal_iff f hz, ← hDz]
    exact subschemeι_apply_mem_support _ _
  have hloc := S.exists_stalk_contractedSituation_eq_span (hmult ZE) hf
  rw [hξEz, hTΓ] at hloc
  obtain ⟨g, hgen, hg, hg2⟩ := hloc
  have : IsNoetherian X' := hf.isNoetherian
  have : IsIntegral ((S.contractedSituation hf).specialFiberComponentIdeal ΓZ).subscheme :=
    (S.contractedSituation hf).isIntegral_specialFiberComponentIdeal ΓZ
  obtain ⟨j, hjci, hj⟩ :=
    exists_isClosedImmersion_comp_eq_subschemeι_of_blowUp_iso hz hregz hdimz eb heb _ hgen hg hg2
  have hjη : j (genericPoint ((S.contractedSituation hf).specialFiberComponentIdeal ΓZ).subscheme) =
      (S.specialFiberComponentPrimeDivisor ZD).genericPoint :=
    S.eq_genericPoint_of_contraction_apply_eq hZ hf (by
      rw [← Scheme.Hom.comp_apply, hj,
        S.contraction_genericPoint_specialFiberComponentPrimeDivisor hf ⟨ZD, hZ⟩, ← hΓZ]
      rfl)
  obtain ⟨b, hb⟩ := S.exists_iso_componentIdeal_of_apply_genericPoint ZD j hjη
  obtain ⟨cc, hcc⟩ := (S.contractedSituation hf).exists_iso_pullback_of_specialFiberIdeal_eq hTΓ
  obtain ⟨fD, hfD, eP, heP⟩ :=
    S.exists_iso_projectiveLineProj_of_isExceptionalCurveOfFirstKind hZ hD hE hmeet ZD
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  refine ⟨eP ≪≫ b.symm ≪≫ cc,
    (cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))).mp ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← pullback.condition, reassoc_of% hcc, ← hj, ← hb]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [S.contraction_comp_contractionToBase hf, ← hfD, reassoc_of% heP]

/-- **Two meeting exceptional curves after one blowup.** Let `V` be a regular proper model, `v` a
closed point of `V` with two-dimensional local ring, and let `D` be an exceptional curve of the
first kind on the blowup of `V` at `v`, distinct from the exceptional curve `E` of the blowup and
meeting it. Then `V` contains no exceptional curve of the first kind and its special fibre is the
projective line. -/
theorem not_hasExceptionalCurveOfFirstKind_and_isProjectiveLineSpecialFiber {C V : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (pV : V ⟶ Spec (.of R))
    (eV : C ≅ pullback pV (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c pV eV) [IsProper pV] (hreg : IsRegular V) {v : V}
    (hv : IsClosed ({v} : Set V)) (hdim : ringKrullDim (V.presheaf.stalk v) = 2)
    {D : (pointBlowUp hv).IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hne : D ≠ exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V)))
    (hmeet : Nonempty (D ⊔ exceptionalIdeal
      (Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V))).subscheme) :
    ¬ V.HasExceptionalCurveOfFirstKind ∧ IsProjectiveLineSpecialFiber pV := by
  classical
  have hVsurf := isIntegralRegularSurface_of_isModel c hproj pV eV hmod hreg
  have : IsNoetherian V := hVsurf.isNoetherian
  have hregv : IsRegularLocalRing (V.presheaf.stalk v) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hVsurf.isRegular v
  obtain ⟨e', hmod', hprop', hreg', -⟩ := exists_isModel_pointBlowUp c hproj pV eV hmod hreg hv
  have := hprop'
  obtain ⟨eE, hEE⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal
      v hv hregv hdim
  have hcontr := AlgebraicGeometry.isContractionOfExceptionalCurve_blowUpToBase v hv hregv hdim
  let S' := regularProperModelSituation c hproj (pointBlowUpToBase hv ≫ pV) e' hmod' hreg'
  generalize hEdef : exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
    (⟨{v}, hv⟩ : Closeds V)) = E at hcontr eE hEE hne hmeet
  obtain ⟨ZE, rfl⟩ := S'.exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj E _ eE
  obtain ⟨ZD, rfl⟩ := S'.exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj D k e
  have hZ : ZD ≠ ZE := fun h => hne (by rw [h])
  obtain ⟨hsub, hP⟩ :=
    S'.subsingleton_and_exists_iso_projectiveLineProj_of_contraction hZ hE hEE hmeet hcontr
  exact ⟨(S'.contractedSituation hcontr).not_hasExceptionalCurveOfFirstKind_of_subsingleton,
    hP pV rfl⟩

/-- A morphism that is constant on the points of `D.subscheme` takes that value on all of
`D.support`. -/
private theorem apply_eq_of_mem_support {X Z : Scheme.{u}} {D : X.IdealSheafData} (g : X ⟶ Z)
    {y : Z} (hy : ∀ z : D.subscheme, g (D.subschemeι z) = y) {x : X}
    (hx : x ∈ (D.support : Set X)) : g x = y := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨z, rfl⟩ := hx
  exact hy z

/-- A curve on the blowup of `V` at `w` which does not meet the exceptional curve lies off the
fibre over `w`. -/
private theorem pointBlowUpToBase_ne_of_isEmpty_sup {V : Scheme.{u}} {w : V}
    (hw : IsClosed ({w} : Set V)) {D : (pointBlowUp hw).IdealSheafData}
    (hmeet : ¬ Nonempty (D ⊔ exceptionalIdeal
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))).subscheme) :
    ∀ x ∈ (D.support : Set (pointBlowUp hw)), pointBlowUpToBase hw x ≠ w := by
  intro x hx hxw
  have hxE : x ∈ ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds V))).support : Set (pointBlowUp hw)) :=
    (mem_support_comap_vanishingIdeal_iff _ hw x).2 hxw
  have : x ∈ ((D ⊔ exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds V))).support : Set (pointBlowUp hw)) := by
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨hx, hxE⟩
  rw [← Scheme.IdealSheafData.range_subschemeι] at this
  obtain ⟨z, -⟩ := this
  exact hmeet ⟨z⟩

/-- **The key lemma of [Stacks, Tag 0CDA].** Let `Y` be a minimal model and `q : W ⟶ Y` a sequence
of blowups at closed points. If some exceptional curve of the first kind on `W` is not contracted
to a point by `q`, then the special fibre of `Y` is the projective line over the residue field.

By induction on the sequence. On `Y` there is no exceptional curve. At a blowup `Bl_v V ⟶ V` the
curve is not the exceptional curve `E` of the blowup, which is contracted; if it is disjoint from
`E` it descends to `V`, still not contracted; if it meets `E`, then by [Stacks, Tag 0C6A] the two
are the whole special fibre, `V` has an irreducible special fibre, hence no exceptional curve, so
the rest of the sequence is an isomorphism, and the special fibre of `V` is a projective line. -/
theorem isProjectiveLineSpecialFiber_of_not_const {C Y : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (q₀ : Y ⟶ Spec (.of R))
    (eY : C ≅ pullback q₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hY : IsMinimalModel c q₀ eY) {T : Set Y} {W : Scheme.{u}} {q : W ⟶ Y}
    (hq : PointBlowupChain Y T W q) (D : W.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme) (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hnc : ¬ ∃ y : Y, ∀ z : D.subscheme, q (D.subschemeι z) = y) :
    IsProjectiveLineSpecialFiber q₀ := by
  classical
  have := hY.isIso_globalSections
  have := hY.isProper
  have hproj := hY.curveProjective
  have hYs := isIntegralRegularSurface_of_isModel c hproj q₀ eY hY.isModel hY.regular
  induction hq generalizing k with
  | refl => exact (hY.not_hasExceptionalCurveOfFirstKind ⟨k, inferInstance, D, e, hE⟩).elim
  | @step V qV hqV w hw hwT ih =>
    obtain ⟨eV, hmodV, hpropV, hregV⟩ :=
      exists_isModel_of_pointBlowupChain c hproj q₀ eY hY.isModel hY.regular hqV
    have := hpropV
    have hVsurf := isIntegralRegularSurface_of_isModel c hproj (qV ≫ q₀) eV hmodV hregV
    have hVLN : IsLocallyNoetherian V := hVsurf.isNoetherian.toIsLocallyNoetherian
    let π := pointBlowUpToBase hw
    rcases Stacks.ResolutionOfSurfaces.isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two
      hVsurf w hw with hiso | hdim2
    · have hsurj : (D.support : Set (pointBlowUp hw)) ⊆ Set.range (inv π).base := fun x _ =>
        (Scheme.homeoOfIso (asIso (inv π))).surjective x
      refine ih (D.comap (inv π)) k _
        (Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap (j := inv π) (hE := hE)
          (h := hsurj)) fun ⟨y, hy⟩ => hnc ⟨y, fun z => ?_⟩
      have hmem : π (D.subschemeι z) ∈ ((D.comap (inv π)).support : Set V) := by
        rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
          Set.mem_preimage, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
        exact subschemeι_apply_mem_support D z
      rw [Scheme.Hom.comp_apply]
      exact apply_eq_of_mem_support qV hy hmem
    set E := exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))
    by_cases hDE : D = E
    · refine (hnc ⟨qV w, fun z => ?_⟩).elim
      have hz := subschemeι_apply_mem_support D z
      have hsupp : (D.support : Set (pointBlowUp hw)) = E.support := by rw [hDE]
      rw [hsupp] at hz
      rw [Scheme.Hom.comp_apply]
      exact congrArg qV (pointBlowUpToBase_eq_of_mem_support hw hz)
    by_cases hmeet : Nonempty (D ⊔ E).subscheme
    · obtain ⟨hVmin, hVP⟩ := not_hasExceptionalCurveOfFirstKind_and_isProjectiveLineSpecialFiber
        c hproj (qV ≫ q₀) eV hmodV hregV hw hdim2 hE hDE hmeet
      have : IsIso qV := isIso_of_pointBlowupChain_of_not_hasExceptionalCurveOfFirstKind hYs hqV
        hVmin
      exact hVP.of_iso (asIso qV) rfl
    obtain ⟨D', e'', hE'', hmap⟩ := exists_isExceptionalCurveOfFirstKind_of_disjoint hw hE
      (pointBlowUpToBase_ne_of_isEmpty_sup hw hmeet)
    refine ih D' k e'' hE'' fun ⟨y, hy⟩ => hnc ⟨y, fun z => ?_⟩
    rw [Scheme.Hom.comp_apply]
    exact apply_eq_of_mem_support qV hy (hmap _ (subschemeι_apply_mem_support D z))

/-- **Stacks Project, Tag 0CDA.** Let `C` be a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K` and genus `0`. If there is more than one minimal model for `C` — two minimal
models which are not isomorphic as models of `C` — then the special fibre of every minimal model
is isomorphic to `𝐏¹_k` over the residue field `k`. -/
@[stacks 0CDA]
theorem isProjectiveLineSpecialFiber_of_isMinimalModel {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (_hproj : Stacks.HProjective.IsHProjective c)
    (_hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)) (_hg : genus c = 0)
    (hmore : ∃ (X₁ X₂ : Scheme.{u}) (p₁ : X₁ ⟶ Spec (.of R)) (p₂ : X₂ ⟶ Spec (.of R))
      (e₁ : C ≅ pullback p₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (e₂ : C ≅ pullback p₂ (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c p₁ e₁ ∧ IsMinimalModel c p₂ e₂ ∧
        ¬ ∃ φ : X₁ ≅ X₂, φ.hom ≫ p₂ = p₁ ∧
          e₁.hom ≫ pullback.fst p₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
            e₂.hom ≫ pullback.fst p₂ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsMinimalModel c p e) : IsProjectiveLineSpecialFiber p := by
  classical
  -- a minimal model not isomorphic to `X`
  have hN : ∃ (N : Scheme.{u}) (pN : N ⟶ Spec (.of R))
      (eN : C ≅ pullback pN (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c pN eN ∧ ¬ ∃ φ : N ≅ X, φ.hom ≫ p = pN ∧
        eN.hom ≫ pullback.fst pN (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
          e.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    obtain ⟨X₁, X₂, p₁, p₂, e₁, e₂, h₁, h₂, h12⟩ := hmore
    by_cases hi₁ : ∃ φ : X₁ ≅ X, φ.hom ≫ p = p₁ ∧
        e₁.hom ≫ pullback.fst p₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ.hom =
          e.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    · refine ⟨X₂, p₂, e₂, h₂, fun ⟨φ₂, hφ₂p, hφ₂c⟩ => h12 ?_⟩
      obtain ⟨φ₁, hφ₁p, hφ₁c⟩ := hi₁
      refine ⟨φ₁ ≪≫ φ₂.symm, ?_, ?_⟩
      · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hφ₂p, Iso.inv_hom_id_assoc, hφ₁p]
      · rw [Iso.trans_hom, Iso.symm_hom, reassoc_of% hφ₁c, ← reassoc_of% hφ₂c]
        simp
    · exact ⟨X₁, p₁, e₁, h₁, hi₁⟩
  obtain ⟨N, pN, eN, hNmin, hNX⟩ := hN
  by_contra hnot
  exact hNX (existsUnique_iso_of_isMinimalModel_of_const c pN p eN e hNmin hX
    fun {T W f} hf D k _ eD hD => Classical.byContradiction fun hnc =>
      hnot (isProjectiveLineSpecialFiber_of_not_const c p e hX hf D k eD hD hnc)).exists

end Stacks.Models

end
