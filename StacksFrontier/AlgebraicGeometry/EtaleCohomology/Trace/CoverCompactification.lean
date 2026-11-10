module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCurveFactorization
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The smooth projective compactification of a finite étale cover of a curve

Let `k` be a perfect field, `U` a smooth curve over `k` with an open immersion `j_U : U ⟶ Ū` into
a proper `k`-scheme, and `f : V ⟶ U` a finite étale morphism with `V` connected. Then `V` is a
smooth curve, and its smooth projective compactification `j : V ⟶ V̄` ([Stacks, Tag 0H1F]) carries
a finite morphism `f̄ : V̄ ⟶ Ū` extending `f`, with `V = f̄^{-1}(U)`; every automorphism of `V`
over `U` extends uniquely to an automorphism of `V̄` over `Ū`.

## Main definitions

* `AlgebraicGeometry.CoverCompactification`: a smooth projective curve `V̄` containing `V` as a
  dense open, with a finite morphism `f̄ : V̄ ⟶ Ū` extending `f` and `V = V̄ ×_Ū U`.
* `AlgebraicGeometry.CoverCompactification.extendIso`: the automorphism of `V̄` extending an
  automorphism of `V` over `U`.

## Main results

* `AlgebraicGeometry.isCurve_comp_of_isFinite_of_etale`: a connected finite étale cover of a smooth
  curve is a curve.
* `AlgebraicGeometry.exists_coverCompactification`: a connected finite étale cover of a smooth
  curve has a smooth projective compactification `V̄` with a finite morphism `f̄ : V̄ ⟶ Ū`
  extending `f`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
* [Stacks Project, Tag 0H1F](https://stacks.math.columbia.edu/tag/0H1F).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section Cover

variable (k : Type u) [Field k] {U V : Scheme.{u}} (pU : U ⟶ Spec (.of k)) [IsCurve k pU]
  [Smooth pU] (f : V ⟶ U) [IsFinite f] [Etale f] [ConnectedSpace V]

/-- A connected finite étale cover `f : V ⟶ U` of a smooth curve `U` over `k` is a curve over
`k`. -/
theorem isCurve_comp_of_isFinite_of_etale : IsCurve k (f ≫ pU) := by
  have : IsIntegral V := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (f ≫ pU)
  have : IsIntegral U := IsCurve.toIsVariety.toIsIntegral (k := k) (f := pU)
  have : Nonempty V := ConnectedSpace.toNonempty
  have hdimU : topologicalKrullDim U = 1 := IsCurve.topologicalKrullDim_eq_one pU
  let Y : FiniteEtaleOver U := MorphismProperty.Over.mk ⊤ f ⟨inferInstance, inferInstance⟩
  have : Nonempty Y.left := inferInstanceAs (Nonempty V)
  have : IsIntegral ((𝟭 Scheme).obj V) := ‹IsIntegral V›
  exact (isCurve_iff k _).2 ⟨IsVariety.mk, le_antisymm (hdimU ▸ topologicalKrullDim_le_of_etale f)
    (hdimU ▸ topologicalKrullDim_le_of_surjective_of_isClosedMap f (surjective_of_finiteEtale Y)
      f.isClosedMap)⟩

end Cover

section Compactification

variable (k : Type u) [Field k] [PerfectField k] {U Ub V : Scheme.{u}} (pU : U ⟶ Spec (.of k))
  [IsCurve k pU] [Smooth pU] (pUb : Ub ⟶ Spec (.of k)) [IsProper pUb] (jU : U ⟶ Ub)
  [IsOpenImmersion jU] (hjU : jU ≫ pUb = pU) (f : V ⟶ U) [IsFinite f] [Etale f] [ConnectedSpace V]

omit [PerfectField k] [IsProper pUb] [Etale f] in
/-- If `j : V ⟶ V̄` is an open immersion into an irreducible scheme separated over `k`, and
`f̄ : V̄ ⟶ Ū` over `k` satisfies `j ≫ f̄ = f ≫ j_U`, then `f̄^{-1}(U)` is the image of `j`. -/
theorem preimage_opensRange_eq_of_comp_eq {Vb : Scheme.{u}} [IrreducibleSpace Vb]
    (q : Vb ⟶ Spec (.of k)) [IsSeparated q] (j : V ⟶ Vb) [IsOpenImmersion j] (fb : Vb ⟶ Ub)
    (hfb : j ≫ fb = f ≫ jU) (hq : fb ≫ pUb = q) :
    fb ⁻¹ᵁ jU.opensRange = j.opensRange := by
  have : IsSeparated (fb ≫ pUb) := hq ▸ inferInstance
  have : IsSeparated fb := IsSeparated.of_comp fb pUb
  set W := fb ⁻¹ᵁ jU.opensRange with hW
  have hjW : Set.range j.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    change fb.base (j.base v) ∈ Set.range jU.base
    rw [← Scheme.Hom.comp_apply, hfb, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let j' : V ⟶ W.toScheme := IsOpenImmersion.lift W.ι j hjW
  have hj' : j' ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion j' := IsOpenImmersion.of_comp j' W.ι
  have hcomp : j' ≫ (fb ∣_ jU.opensRange) = f ≫ jU.isoOpensRange.hom := by
    rw [← cancel_mono jU.opensRange.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hj', hfb,
      Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have : UniversallyClosed (j' ≫ (fb ∣_ jU.opensRange)) := hcomp ▸ inferInstance
  have : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (fb ∣_ jU.opensRange)
  have : Nonempty V := ConnectedSpace.toNonempty
  have hWirr : IsPreirreducible (W : Set Vb) :=
    (IrreducibleSpace.isIrreducible_univ Vb).isPreirreducible.open_subset W.isOpen
      (Set.subset_univ _)
  have : PreirreducibleSpace W.toScheme := Subtype.preirreducibleSpace hWirr
  have huniv : Set.range j'.base = Set.univ :=
    IsClopen.eq_univ ⟨j'.isClosedMap.isClosed_range, j'.isOpenEmbedding.isOpen_range⟩
      (Set.range_nonempty _)
  ext x
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨v, hv⟩ : (⟨x, hx⟩ : W.toScheme) ∈ Set.range j'.base := huniv ▸ Set.mem_univ _
    refine ⟨v, ?_⟩
    rw [← hj', Scheme.Hom.comp_apply, hv]
    rfl
  · rintro ⟨v, rfl⟩
    exact hjW ⟨v, rfl⟩ |>.elim fun w hw => hw ▸ w.2

/-- A morphism from `V` to a proper `k`-scheme `Y` that is compatible with the structure maps
extends along an open immersion `j : V ⟶ V̄` into a curve with finite closed-point
complement. -/
private theorem exists_extension_of_open_immersion (K : Type u) [Field K] {V Vb Y : Scheme.{u}}
    (q : Vb ⟶ Spec (.of K)) [IsCurve K q] [Smooth q] [IsNoetherian Vb]
    (pY : Y ⟶ Spec (.of K)) [IsProper pY] (j : V ⟶ Vb) [IsOpenImmersion j] [Nonempty V]
    (hfin : ((Set.range j.base)ᶜ).Finite)
    (hcl : ∀ y : Vb, y ∉ Set.range j.base → IsClosed ({y} : Set Vb)) (g : V ⟶ Y)
    (hg : g ≫ pY = j ≫ q) : ∃ F : Vb ⟶ Y, F ≫ pY = q ∧ j ≫ F = g := by
  have hdense : Dense ((j.opensRange : Vb.Opens) : Set Vb) :=
    j.opensRange.isOpen.dense ⟨_, (Classical.arbitrary V), rfl⟩
  have hfin' : (((j.opensRange : Vb.Opens) : Set Vb)ᶜ).Finite := by
    simpa [Scheme.Hom.coe_opensRange] using hfin
  have hstalk : ∀ z : Vb, z ∉ ((j.opensRange : Vb.Opens) : Set Vb) →
      ∃ _ : IsDomain (Vb.presheaf.stalk z), ValuationRing (Vb.presheaf.stalk z) := by
    intro z hz
    have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed K q
      (hcl z (by simpa [Scheme.Hom.coe_opensRange] using hz))
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨F, hFq, hF⟩ := exists_extension_of_finite_compl_valuationRing_stalk q pY j.opensRange
    hdense hfin' hstalk (j.isoOpensRange.inv ≫ g) (by
      rw [Category.assoc, hg, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp])
  refine ⟨F, hFq, ?_⟩
  calc j ≫ F = j.isoOpensRange.hom ≫ (j.opensRange.ι ≫ F) := by
        rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    _ = g := by rw [hF, Iso.hom_inv_id_assoc]

include hjU in
/-- **The smooth projective compactification of a connected finite étale cover.**  For `U` a
smooth curve over a perfect field `k` with an open immersion `j_U : U ⟶ Ū` into a proper
`k`-scheme and `f : V ⟶ U` finite étale with `V` connected, there are a smooth projective curve
`V̄` over `k`, an open immersion `j : V ⟶ V̄` with finite complement consisting of closed points,
and a finite morphism `f̄ : V̄ ⟶ Ū` over `k` with `V = V̄ ×_Ū U`. -/
theorem exists_coverCompactification :
    ∃ (Vb : Scheme.{u}) (q : Vb ⟶ Spec (.of k)) (j : V ⟶ Vb) (_ : IsOpenImmersion j)
      (fb : Vb ⟶ Ub), j ≫ fb = f ≫ jU ∧ fb ≫ pUb = q ∧ IsCurve k q ∧ Smooth q ∧ IsProper q ∧
        IsFinite fb ∧ IsPullback j f fb jU ∧ ((Set.range j.base)ᶜ).Finite ∧
          ∀ y : Vb, y ∉ Set.range j.base → IsClosed ({y} : Set Vb) := by
  have : IsCurve k (f ≫ pU) := isCurve_comp_of_isFinite_of_etale k pU f
  obtain ⟨-, Vb, q, j, hj, hjq, hcq, hproj, -, hsq, hfin, hbdry⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k (f ≫ pU)
      (isRegular_of_smooth_over_field (f ≫ pU))
  have : IsOpenImmersion j := hj
  have : IsCurve k q := hcq
  have : Smooth q := hsq
  have : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have : IsLocallyNoetherian Vb := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Vb := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian Vb := ⟨⟩
  have : IsIntegral Vb := IsCurve.toIsVariety.toIsIntegral (k := k) (f := q)
  have : Nonempty V := ConnectedSpace.toNonempty
  obtain ⟨fb, hfbq, hjfb⟩ := exists_extension_of_open_immersion k q pUb j hfin hbdry (f ≫ jU)
    (by rw [Category.assoc, hjU, hjq])
  have hpre := preimage_opensRange_eq_of_comp_eq k pUb jU f q j fb hjfb hfbq
  have hpb : IsPullback j f fb jU := (IsOpenImmersion.isPullback f j jU fb hjfb hpre).flip
  have : IsProper (fb ≫ pUb) := hfbq ▸ inferInstance
  have : IsProper fb := IsProper.of_comp fb pUb
  have : LocallyQuasiFinite fb := by
    refine (locallyQuasiFinite_iff_finite_preimage_singleton).2 fun x => ?_
    by_cases hx : x ∈ Set.range jU.base
    · obtain ⟨u, rfl⟩ := hx
      refine ((f.finite_preimage_singleton u).image j.base).subset ?_
      intro z hz
      have hz' : z ∈ (fb ⁻¹ᵁ jU.opensRange : Set Vb) := by
        change fb.base z ∈ Set.range jU.base
        rw [Set.mem_preimage.1 hz]
        exact ⟨u, rfl⟩
      rw [hpre] at hz'
      obtain ⟨v, rfl⟩ := hz'
      refine ⟨v, ?_, rfl⟩
      apply jU.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← hjfb, Scheme.Hom.comp_apply]
      exact Set.mem_preimage.1 hz
    · refine hfin.subset ?_
      rintro z hz ⟨v, rfl⟩
      apply hx
      rw [← Set.mem_preimage.1 hz, ← Scheme.Hom.comp_apply, hjfb, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
  exact ⟨Vb, q, j, hj, fb, hjfb, hfbq, hcq, hsq, inferInstance,
    IsFinite.of_isProper_of_locallyQuasiFinite fb, hpb, hfin, hbdry⟩

/-- A smooth projective compactification of a finite étale cover `f : V ⟶ U` over
`j_U : U ⟶ Ū`: a smooth proper curve `V̄` over `k` with an open immersion `j : V ⟶ V̄` whose
complement is a finite set of closed points, and a finite morphism `f̄ : V̄ ⟶ Ū` over `k` with
`V = V̄ ×_Ū U`. -/
structure CoverCompactification where
  /-- The compactification `V̄`. -/
  Vb : Scheme.{u}
  /-- Its structure morphism. -/
  q : Vb ⟶ Spec (.of k)
  /-- The open immersion `V ⟶ V̄`. -/
  j : V ⟶ Vb
  /-- `j` is an open immersion. -/
  isOpenImmersion : IsOpenImmersion j
  /-- The finite morphism `f̄ : V̄ ⟶ Ū`. -/
  fb : Vb ⟶ Ub
  /-- `f̄` extends `f`. -/
  w : j ≫ fb = f ≫ jU
  /-- `f̄` is a morphism over `k`. -/
  hq : fb ≫ pUb = q
  /-- `V̄` is a curve over `k`. -/
  isCurve : IsCurve k q
  /-- `V̄` is smooth over `k`. -/
  smooth : Smooth q
  /-- `V̄` is proper over `k`. -/
  isProper : IsProper q
  /-- `f̄` is finite. -/
  isFinite : IsFinite fb
  /-- `V = V̄ ×_Ū U`. -/
  isPullback : IsPullback j f fb jU
  /-- The complement of `V` in `V̄` is finite. -/
  finite_compl : ((Set.range j.base)ᶜ).Finite
  /-- Every point of `V̄` outside `V` is closed. -/
  isClosed_compl : ∀ y : Vb, y ∉ Set.range j.base → IsClosed ({y} : Set Vb)

include hjU in
/-- A connected finite étale cover of a smooth curve has a smooth projective compactification
over `Ū`. -/
theorem nonempty_coverCompactification :
    Nonempty (CoverCompactification k pUb jU f) := by
  obtain ⟨Vb, q, j, hj, fb, w, hq, hc, hs, hp, hf, hpb, hfin, hcl⟩ :=
    exists_coverCompactification k pU pUb jU hjU f
  exact ⟨⟨Vb, q, j, hj, fb, w, hq, hc, hs, hp, hf, hpb, hfin, hcl⟩⟩

namespace CoverCompactification

variable {k pUb jU f} (C : CoverCompactification k pUb jU f)

attribute [instance] isOpenImmersion isCurve smooth isProper isFinite

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsProper pUb] [IsOpenImmersion jU] [IsFinite f]
  [Etale f] [ConnectedSpace V] in
include hjU in
/-- The structure morphism of `V̄` restricts on `V` to that of `V`. -/
lemma j_comp_q : C.j ≫ C.q = f ≫ pU := by
  rw [← C.hq, reassoc_of% C.w, hjU]

/-- `V̄` is integral. -/
instance : IsIntegral C.Vb := IsCurve.toIsVariety.toIsIntegral (k := k) (f := C.q)

/-- `V` is dense in `V̄`. -/
instance : IsDominant C.j := by
  have : Nonempty V := ConnectedSpace.toNonempty
  exact ⟨C.j.opensRange.isOpen.dense ⟨_, (Classical.arbitrary V), rfl⟩⟩

/-- `V̄` is locally Noetherian. -/
instance : IsLocallyNoetherian C.Vb := LocallyOfFiniteType.isLocallyNoetherian C.q

/-- `V̄` is smooth of relative dimension `1` over `k`. -/
instance : SmoothOfRelativeDimension 1 C.q := smoothOfRelativeDimension_one_of_isCurve _ C.q

/-- `V̄` is Noetherian. -/
instance : IsNoetherian C.Vb :=
  haveI : CompactSpace C.Vb := QuasiCompact.compactSpace_of_compactSpace C.q
  ⟨⟩

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
include hjU in
/-- Every endomorphism of `V` over `U` extends to an endomorphism of `V̄` over `Ū`. -/
theorem exists_extend (a : V ⟶ V) (ha : a ≫ f = f) :
    ∃ σ : C.Vb ⟶ C.Vb, C.j ≫ σ = a ≫ C.j ∧ σ ≫ C.fb = C.fb := by
  have hjq := C.j_comp_q pU hjU
  obtain ⟨σ, hσq, hjσ⟩ := exists_extension_of_open_immersion k C.q C.q C.j C.finite_compl
    C.isClosed_compl (a ≫ C.j) (by rw [Category.assoc, hjq, reassoc_of% ha, ← hjq])
  refine ⟨σ, hjσ, ?_⟩
  refine ext_of_isDominant_of_isSeparated pUb (by rw [Category.assoc, C.hq, hσq]) C.j ?_
  rw [reassoc_of% hjσ, C.w, reassoc_of% ha]

/-- The extension `σ_a : V̄ ⟶ V̄` of an endomorphism `a` of `V` over `U`. -/
def extend (a : V ⟶ V) (ha : a ≫ f = f) : C.Vb ⟶ C.Vb :=
  (C.exists_extend pU hjU a ha).choose

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- `σ_a` restricts to `a` on `V`. -/
@[reassoc]
lemma j_comp_extend (a : V ⟶ V) (ha : a ≫ f = f) :
    C.j ≫ C.extend pU hjU a ha = a ≫ C.j :=
  (C.exists_extend pU hjU a ha).choose_spec.1

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- `σ_a` is a morphism over `Ū`. -/
@[reassoc (attr := simp)]
lemma extend_comp_fb (a : V ⟶ V) (ha : a ≫ f = f) :
    C.extend pU hjU a ha ≫ C.fb = C.fb :=
  (C.exists_extend pU hjU a ha).choose_spec.2

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- `σ_a` is a morphism over `k`. -/
@[reassoc (attr := simp)]
lemma extend_comp_q (a : V ⟶ V) (ha : a ≫ f = f) :
    C.extend pU hjU a ha ≫ C.q = C.q := by
  rw [← C.hq, extend_comp_fb_assoc]

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- The extension is unique among endomorphisms of `V̄` over `k`. -/
lemma eq_extend (a : V ⟶ V) (ha : a ≫ f = f) (σ : C.Vb ⟶ C.Vb) (hσq : σ ≫ C.q = C.q)
    (hσ : C.j ≫ σ = a ≫ C.j) : σ = C.extend pU hjU a ha :=
  ext_of_isDominant_of_isSeparated C.q (by rw [hσq, extend_comp_q]) C.j
    (by rw [hσ, j_comp_extend])

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- The extension of the identity of `V` is the identity of `V̄`. -/
lemma extend_id : C.extend pU hjU (𝟙 V) (Category.id_comp f) = 𝟙 C.Vb :=
  (C.eq_extend pU hjU _ _ _ (Category.id_comp _) (by simp)).symm

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- Extension is compatible with composition: `σ_{a ≫ b} = σ_a ≫ σ_b`. -/
lemma extend_comp (a b : V ⟶ V) (ha : a ≫ f = f) (hb : b ≫ f = f) :
    C.extend pU hjU (a ≫ b) (by rw [Category.assoc, hb, ha]) =
      C.extend pU hjU a ha ≫ C.extend pU hjU b hb :=
  (C.eq_extend pU hjU _ _ _ (by simp) (by rw [j_comp_extend_assoc, j_comp_extend,
    Category.assoc])).symm

/-- The extension of an automorphism of `V` over `U` is an automorphism of `V̄`. -/
def extendIso (a : V ≅ V) (ha : a.hom ≫ f = f) : C.Vb ≅ C.Vb where
  hom := C.extend pU hjU a.hom ha
  inv := C.extend pU hjU a.inv (a.inv_comp_eq.2 ha.symm)
  hom_inv_id := by
    rw [← C.extend_comp pU hjU, ← C.extend_id pU hjU]
    congr 1
    exact a.hom_inv_id
  inv_hom_id := by
    rw [← C.extend_comp pU hjU, ← C.extend_id pU hjU]
    congr 1
    exact a.inv_hom_id

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- `V` is stable under `σ_a`: `V = σ_a^{-1}(V)`. -/
lemma isPullback_extend (a : V ≅ V) (ha : a.hom ≫ f = f) :
    IsPullback a.hom C.j C.j (C.extend pU hjU a.hom ha) := by
  refine IsOpenImmersion.isPullback a.hom C.j C.j _ (C.j_comp_extend pU hjU a.hom ha) ?_
  have hinv : C.extend pU hjU a.hom ha ≫
      C.extend pU hjU a.inv (a.inv_comp_eq.2 ha.symm) = 𝟙 _ :=
    (C.extendIso pU hjU a ha).hom_inv_id
  ext z
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨a.inv.base v, ?_⟩
    rw [← Scheme.Hom.comp_apply,
      ← C.j_comp_extend pU hjU a.inv (a.inv_comp_eq.2 ha.symm),
      Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply, hinv, Scheme.Hom.id_base]
    rfl
  · rintro ⟨v, rfl⟩
    refine ⟨a.hom.base v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, C.j_comp_extend pU hjU]

end CoverCompactification

end Compactification

end AlgebraicGeometry

end
