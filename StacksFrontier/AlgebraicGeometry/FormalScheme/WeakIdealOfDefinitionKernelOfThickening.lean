module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionPoints
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# The kernel of a thickening of a McQuillan formal scheme

Let `𝔛` be a formal scheme in the sense of McQuillan and let `i : h_Z → h_𝔛` be a morphism from
the functor of points of a scheme `Z` which is representable by thickenings: for every point
`T → 𝔛` of a scheme the fibre product `Z ×_𝔛 T` is a scheme and its projection to `T` is a
surjective closed immersion. Let `φ : Z → 𝔛` be the morphism of locally topologically ringed
spaces underlying `i`. This file shows that the kernel ideal sheaf `ker φ ⊆ 𝒪_𝔛` is a weak ideal
of definition, that it is cut out by its sections over the weak affine formal opens
(`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.IsCutOutOn`), and that the points
of `𝔛` killing it are exactly the points factoring through `Z`, uniquely. This is the half of the
correspondence of Stacks 0AIV going from thickenings to weak ideals of definition.

Over a weak affine formal open `𝔘 ≅ Spfw A` the argument runs as follows. For a weak ideal of
definition `J` of `A` the fibre product `W_J = Z ×_𝔛 Spec (A/J)` is a thickening of `Spec (A/J)`.
Every point of the preimage `Z_𝔘 = φ⁻¹(𝔘)` lies in the image of `W_J`: the residue field point at
it factors through some `Spec (A/J')` with `J' ⊆ J`, and the transition map
`Spec (A/J) → Spec (A/J')` is surjective while `W_{J'} → Spec (A/J')` is injective. So `Z_𝔘` is
quasi-compact, being the image of the affine scheme `W_J`, and the point `Z_𝔘 → 𝔛` kills some
`J₀`. The ideal `J'` of the elements of `A` killed by `φ` contains `J₀`, and consists of
topologically nilpotent elements because `Z_𝔘 → Spec (A/J₀)` is surjective; so it is a weak ideal
of definition, and its elements are exactly those whose sections vanish under `φ`. Finally the
closed immersion `W_{J'} → Spec (A/J')` is injective on global sections, because `Z_𝔘 → 𝔛` factors
through `W_{J'}`, so it is an isomorphism and the quotient point `Spec (A/J') → 𝔛` factors
through `Z`. Every point landing in `𝔘` and killing `ker φ` therefore factors through `Z`, and the
factorisations over the preimages of the weak affine formal opens glue, `i` being a
monomorphism.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isWeakIdealOfDefinitionOn_ker_of_isThickening`: the kernel of a thickening is a weak ideal of
  definition.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isCutOutOn_ker_of_isThickening`:
  it is cut out by its sections over the weak affine formal opens.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.existsUnique_factor_of_kills_ker_of_isThickening`: a point of `𝔛` killing it factors uniquely
  through `Z`.

## Implementation notes

A thickening of `𝔛` is given, as in the source, by its functor of points: a morphism
`h_Z → h_𝔛` of presheaves on schemes satisfying
`CategoryTheory.MorphismProperty.presheaf` for `Stacks.Thickenings.IsThickening`. The morphism of
locally topologically ringed spaces `Z → 𝔛` is recovered by the Yoneda lemma, and its kernel ideal
sheaf is the ideal sheaf attached to the thickening.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-- In a linearly topologised ring an element is topologically nilpotent as soon as one of its
powers is: the powers of the element eventually lie in any open ideal containing a power of it. -/
theorem IsTopologicallyNilpotent.of_pow {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsLinearTopology R R] {a : R} {n : ℕ} (h : IsTopologicallyNilpotent (a ^ n)) :
    IsTopologicallyNilpotent a := by
  refine (IsLinearTopology.hasBasis_ideal.tendsto_right_iff).2 fun I hI => ?_
  obtain ⟨k, hk⟩ := h.exists_pow_mem_of_mem_nhds hI
  refine Filter.eventually_atTop.2 ⟨n * k, fun m hm => ?_⟩
  change a ^ m ∈ I
  rw [← Nat.sub_add_cancel hm, pow_add, pow_mul]
  exact I.mul_mem_left _ hk

namespace AlgebraicGeometry

open TopologicalRing

/-- A global function on an affine scheme `Spec R` that is killed by a surjective morphism of
schemes is nilpotent: its basic open has empty preimage, hence is empty. -/
theorem isNilpotent_of_surjective_of_appTop_eq_zero {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (hf : Function.Surjective f) {r : R}
    (hr : f.appTop ((Scheme.ΓSpecIso R).inv r) = 0) : IsNilpotent r := by
  rw [← PrimeSpectrum.basicOpen_eq_bot_iff, ← basicOpen_eq_of_affine]
  have h := Scheme.preimage_basicOpen_top f ((Scheme.ΓSpecIso R).inv r)
  rw [hr, Scheme.basicOpen_zero] at h
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ f ⁻¹ᵁ (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r) := hy
  rw [h] at hx
  exact hx.elim

/-- For weak ideals of definition `K ⊆ J` the closed immersion `Spec (A/J) → Spec (A/K)` is
surjective: every prime of `A/K` pulls back to an open prime of `A`, which contains `J`. -/
theorem surjective_spec_map_factor_of_weakIdeal (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {J K : WeakIdealsOfDefinition A} (h : K.1 ≤ J.1) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
  intro y
  have hJ := (mem_openPrimes_iff_le_of_isWeakIdealOfDefinition A J.2 _).1
    (spfOfQuotientOn_mem A K y)
  have hy : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ J.1 := by
      rw [SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem] at hx
      exact hx
    exact hJ ha
  exact hy

/-- The quotient point `Spec (A/J) → X` of a weak affine formal chart is a monomorphism on points
over schemes. -/
theorem weakChartPoint_cancel_left {X : LTRS.{u}} {U : Opens X} (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] (hA : IsWeaklyAdmissible A)
    (χ : X.restrict U ≅ spfwLTRS A hA.1) (J : WeakIdealsOfDefinition A) {T : Scheme.{u}}
    {b b' : T ⟶ Spec (spfQuotientOn A J)}
    (h : schemeToLTRS.map b ≫ weakChartPoint A hA χ J =
      schemeToLTRS.map b' ≫ weakChartPoint A hA χ J) : b = b' :=
  spfwQuotientPoint_cancel A hA J (weakChartEmbedding_cancel A hA χ
    ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)))

namespace LocallyTopologicallyRingedSpace.IdealSheaf

/-- Restricting a point `h : T → X` to an open `W` of `T` containing the preimage of `V` does not
change its kernel over `V`: the restriction of sections to `W` is injective over opens inside
`W`. -/
theorem mem_ker_of_mem_ker_schemeToLTRS_map_ι_comp {X : LTRS.{u}} {T : Scheme.{u}}
    (h : schemeToLTRSObj T ⟶ X) {V : Opens X} (W : T.Opens)
    (hW : (Opens.map h.toHom.base).obj V ≤ W) {s : (X.presheaf.obj (op V)).α}
    (hs : s ∈ (ker (schemeToLTRS.map W.ι ≫ h)).ideal V) : s ∈ (ker h).ideal V := by
  rw [mem_ker_iff] at hs ⊢
  have hcomp : (schemeToLTRS.map W.ι ≫ h).toHom.c.app (op V) = h.toHom.c.app (op V) ≫
      (schemeToLTRS.map W.ι).toHom.c.app (op ((Opens.map h.toHom.base).obj V)) :=
    PresheafedSpace.comp_c_app _ _ _
  rw [hcomp] at hs
  have key : ∀ O : T.Opens, O ≤ W → W.ι ''ᵁ W.ι ⁻¹ᵁ O = O := fun O hO => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hO
  have heq := key _ hW
  have hinj : Function.Injective
      ((schemeToLTRS.map W.ι).toHom.c.app (op ((Opens.map h.toHom.base).obj V))).1 :=
    injective_presheaf_map_of_eq T.presheaf heq _
  exact hinj (hs.trans (map_zero _).symm)

/-- Precomposing a point `h` with the image of a composite of morphisms of schemes. -/
private theorem schemeToLTRS_map_comp_comp {X : LTRS.{u}} {S T R : Scheme.{u}} (a : S ⟶ T)
    (b : T ⟶ R) (h : schemeToLTRSObj R ⟶ X) :
    schemeToLTRS.map (a ≫ b) ≫ h = schemeToLTRS.map a ≫ schemeToLTRS.map b ≫ h :=
  (congrArg (· ≫ h) (schemeToLTRS.map_comp a b)).trans (Category.assoc _ _ _)

/-! ### Thickenings -/

section Thickening

variable {𝔛 : McQuillanFormalScheme.{u}} {Z : Scheme.{u}}
  {i : yoneda.obj Z ⟶ mcQuillanFormalSchemePoints 𝔛}

/-- A morphism `h_Z → h_𝔛` acts by precomposition with the morphism `Z → 𝔛` it corresponds to
under the Yoneda lemma. -/
theorem app_hom_eq_schemeToLTRS_map_comp {T : Scheme.{u}} (k : T ⟶ Z) :
    (i.app (op T) k).hom = schemeToLTRS.map k ≫ (yonedaEquiv i).hom := by
  have : i.app (op T) k = (mcQuillanFormalSchemePoints 𝔛).map k.op (yonedaEquiv i) := by
    rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [this]
  rfl

variable (hi : MorphismProperty.presheaf @Stacks.Thickenings.IsThickening.{u} i)
include hi

/-- A morphism of presheaves representable by thickenings is a monomorphism, thickenings being
closed immersions and hence monomorphisms. -/
theorem mono_of_presheaf_isThickening : Mono i :=
  MorphismProperty.presheaf_mono_of_le (fun _ _ f hf => by
    have := hf.1
    exact (inferInstance : Mono f)) hi

/-- The morphism `Z → 𝔛` underlying a thickening is a monomorphism on points over schemes. -/
theorem schemeToLTRS_map_cancel_of_isThickening {T : Scheme.{u}} {k k' : T ⟶ Z}
    (h : schemeToLTRS.map k ≫ (yonedaEquiv i).hom = schemeToLTRS.map k' ≫ (yonedaEquiv i).hom) :
    k = k' := by
  have := (NatTrans.mono_iff_mono_app i).1 (mono_of_presheaf_isThickening hi) (op T)
  refine (mono_iff_injective (i.app (op T))).1 this ?_
  exact InducedCategory.hom_ext ((app_hom_eq_schemeToLTRS_map_comp k).trans
    (h.trans (app_hom_eq_schemeToLTRS_map_comp k').symm))

end Thickening

section Chart

variable {𝔛 : McQuillanFormalScheme.{u}} {U : Opens 𝔛.obj} (A : Type u) [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] (hA : IsWeaklyAdmissible A)
  (χ : 𝔛.obj.restrict U ≅ spfwLTRS A hA.1)

/-- The quotient point `Spec (A/J) → 𝔛` of a weak affine formal chart, as a morphism of functors
of points `h_{Spec (A/J)} → h_𝔛`. -/
noncomputable def weakChartPointMap (J : WeakIdealsOfDefinition A) :
    yoneda.obj (Spec (spfQuotientOn A J)) ⟶ mcQuillanFormalSchemePoints 𝔛 :=
  yonedaEquiv.symm (ObjectProperty.homMk (weakChartPoint A hA χ J))

/-- The morphism of functors of points of a quotient point acts by precomposition. -/
theorem weakChartPointMap_app_hom (J : WeakIdealsOfDefinition A) {T : Scheme.{u}}
    (b : T ⟶ Spec (spfQuotientOn A J)) :
    ((weakChartPointMap A hA χ J).app (op T) b).hom =
      schemeToLTRS.map b ≫ weakChartPoint A hA χ J :=
  rfl

variable {Z : Scheme.{u}} {i : yoneda.obj Z ⟶ mcQuillanFormalSchemePoints 𝔛}

/-- A commutative square of points over schemes of `𝔛` gives a commutative square of functors of
points. -/
theorem yoneda_map_comp_eq_yoneda_map_comp_weakChartPointMap (J : WeakIdealsOfDefinition A)
    {T : Scheme.{u}} {a : T ⟶ Z} {b : T ⟶ Spec (spfQuotientOn A J)}
    (h : schemeToLTRS.map a ≫ (yonedaEquiv i).hom = schemeToLTRS.map b ≫ weakChartPoint A hA χ J) :
    yoneda.map a ≫ i = yoneda.map b ≫ weakChartPointMap A hA χ J := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
  refine InducedCategory.hom_ext ?_
  rw [app_hom_eq_schemeToLTRS_map_comp, weakChartPointMap_app_hom]
  exact h

variable (hi : MorphismProperty.presheaf @Stacks.Thickenings.IsThickening.{u} i)

/-- The fibre product `Z ×_𝔛 Spec (A/J)` of a thickening with the quotient point of a weak affine
formal chart at a weak ideal of definition `J`. -/
noncomputable abbrev thickeningPullback (J : WeakIdealsOfDefinition A) : Scheme.{u} :=
  hi.rep.pullback (weakChartPointMap A hA χ J)

/-- The first projection `Z ×_𝔛 Spec (A/J) → Z`. -/
noncomputable abbrev thickeningPullbackFst (J : WeakIdealsOfDefinition A) :
    thickeningPullback A hA χ hi J ⟶ Z :=
  hi.rep.fst' (weakChartPointMap A hA χ J)

/-- The second projection `Z ×_𝔛 Spec (A/J) → Spec (A/J)`, a thickening. -/
noncomputable abbrev thickeningPullbackSnd (J : WeakIdealsOfDefinition A) :
    thickeningPullback A hA χ hi J ⟶ Spec (spfQuotientOn A J) :=
  hi.rep.snd (weakChartPointMap A hA χ J)

/-- The projection `Z ×_𝔛 Spec (A/J) → Spec (A/J)` is a thickening. -/
theorem isThickening_thickeningPullbackSnd (J : WeakIdealsOfDefinition A) :
    Stacks.Thickenings.IsThickening (thickeningPullbackSnd A hA χ hi J) :=
  hi.property_snd _

/-- The square of the fibre product `Z ×_𝔛 Spec (A/J)` commutes. -/
theorem thickeningPullback_w (J : WeakIdealsOfDefinition A) :
    schemeToLTRS.map (thickeningPullbackFst A hA χ hi J) ≫ (yonedaEquiv i).hom =
      schemeToLTRS.map (thickeningPullbackSnd A hA χ hi J) ≫ weakChartPoint A hA χ J := by
  have h := congrArg yonedaEquiv (hi.rep.isPullback' (weakChartPointMap A hA χ J)).w
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at h
  have h' := congrArg (fun x => x.hom) h
  simp only at h'
  rw [app_hom_eq_schemeToLTRS_map_comp, weakChartPointMap_app_hom] at h'
  exact h'

/-- The fibre product `Z ×_𝔛 Spec (A/J)` maps into the preimage of the open of the chart. -/
theorem range_thickeningPullbackFst_subset (J : WeakIdealsOfDefinition A)
    (w : thickeningPullback A hA χ hi J) :
    (yonedaEquiv i).hom.toHom.base (thickeningPullbackFst A hA χ hi J w) ∈ U := by
  have h := congrArg (fun f => f.toHom.base w) (thickeningPullback_w A hA χ hi J)
  change (yonedaEquiv i).hom.toHom.base (thickeningPullbackFst A hA χ hi J w) =
    (weakChartPoint A hA χ J).toHom.base (thickeningPullbackSnd A hA χ hi J w) at h
  rw [h]
  exact range_weakChartPoint_subset A hA χ J (Set.mem_range_self _)

/-- **Every point of `Z` over the open of a chart comes from `Z ×_𝔛 Spec (A/J)`**, for every weak
ideal of definition `J`. The residue field point at `z` factors through `Spec (A/L)` for some
`L ⊆ J`; the point of `Z ×_𝔛 Spec (A/L)` it gives has the same image in `Spec (A/L)` as a point
coming from `Z ×_𝔛 Spec (A/J)`, the transition map being surjective, and the closed immersion
`Z ×_𝔛 Spec (A/L) → Spec (A/L)` is injective. -/
theorem exists_thickeningPullbackFst_eq (J : WeakIdealsOfDefinition A) (z : Z)
    (hz : (yonedaEquiv i).hom.toHom.base z ∈ U) :
    ∃ w, thickeningPullbackFst A hA χ hi J w = z := by
  let p := Z.fromSpecResidueField z
  have hp : Set.range (schemeToLTRS.map p ≫ (yonedaEquiv i).hom).toHom.base ⊆
      (U : Set 𝔛.obj) := by
    rintro _ ⟨s, rfl⟩
    have key : ∀ x : Z, x = z → (yonedaEquiv i).hom.toHom.base x ∈ U := by
      rintro _ rfl
      exact hz
    exact key (p s) (Scheme.fromSpecResidueField_apply z s)
  obtain ⟨K, hK⟩ := exists_weakIdeal_kill_weakChartSections A hA χ _ hp
  let L := spfIndexMeet A J K
  obtain ⟨b, hb, -⟩ := existsUnique_weakChartPoint_factor A hA χ L _ hp fun a ha => hK a ha.2
  have hpb := yoneda_map_comp_eq_yoneda_map_comp_weakChartPointMap A hA χ L hb.symm
  let l := hi.rep.lift' p b hpb
  let s0 : Spec (Z.residueField z) := IsLocalRing.closedPoint _
  have hl : thickeningPullbackFst A hA χ hi L (l s0) = z := by
    rw [← Scheme.Hom.comp_apply, hi.rep.lift'_fst p b hpb, Scheme.fromSpecResidueField_apply]
  have hLJ : L.1 ≤ J.1 := inf_le_left
  let π := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hLJ))
  obtain ⟨y, hy⟩ := surjective_spec_map_factor_of_weakIdeal A hLJ
    (thickeningPullbackSnd A hA χ hi L (l s0))
  obtain ⟨w, hw⟩ := (isThickening_thickeningPullbackSnd A hA χ hi J).2 y
  have ht : schemeToLTRS.map (thickeningPullbackFst A hA χ hi J) ≫ (yonedaEquiv i).hom =
      schemeToLTRS.map (thickeningPullbackSnd A hA χ hi J ≫ π) ≫ weakChartPoint A hA χ L :=
    (thickeningPullback_w A hA χ hi J).trans (by
      rw [schemeToLTRS_map_comp_comp, schemeToLTRS_map_comp_weakChartPoint A hA χ hLJ])
  have htpb := yoneda_map_comp_eq_yoneda_map_comp_weakChartPointMap A hA χ L ht
  let t := hi.rep.lift' _ _ htpb
  have htw : t w = l s0 := by
    have := (isThickening_thickeningPullbackSnd A hA χ hi L).1
    refine (thickeningPullbackSnd A hA χ hi L).isClosedEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hi.rep.lift'_snd _ _ htpb, Scheme.Hom.comp_apply, hw, hy]
  refine ⟨w, ?_⟩
  rw [← hi.rep.lift'_fst _ _ htpb, Scheme.Hom.comp_apply]
  change thickeningPullbackFst A hA χ hi L (t w) = z
  rw [htw, hl]

include hA χ hi in
/-- The preimage under a thickening of the open of a weak affine formal chart is quasi-compact: it
is the image of the affine scheme `Z ×_𝔛 Spec (A/J)`. -/
theorem isCompact_pointPreimage_of_isThickening :
    IsCompact ((pointPreimage (yonedaEquiv i).hom U : Z.Opens) : Set Z) := by
  let J₁ := weaklyPreAdmissibleSpfIndex A hA.1
  have := (isThickening_thickeningPullbackSnd A hA χ hi J₁).1
  have := (IsClosedImmersion.isAffine_surjective_of_isAffine
    (thickeningPullbackSnd A hA χ hi J₁)).1
  have heq : ((pointPreimage (yonedaEquiv i).hom U : Z.Opens) : Set Z) =
      Set.range (thickeningPullbackFst A hA χ hi J₁) := by
    ext z
    refine ⟨fun hz => exists_thickeningPullbackFst_eq A hA χ hi J₁ z hz, ?_⟩
    rintro ⟨w, rfl⟩
    exact range_thickeningPullbackFst_subset A hA χ hi J₁ w
  rw [heq]
  exact isCompact_range (thickeningPullbackFst A hA χ hi J₁).continuous

include hi in
/-- **The kernel of a thickening over a weak affine formal chart.** The elements of `A` whose
sections over `U` are killed by `Z → 𝔛` form a weak ideal of definition `J'`, and the quotient
point `Spec (A/J') → 𝔛` factors through `Z`. -/
theorem exists_weakIdeal_ker_eq_of_isThickening :
    ∃ J' : WeakIdealsOfDefinition A,
      (∀ a, a ∈ J'.1 ↔
        ((yonedaEquiv i).hom.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0) ∧
      ∃ c : Spec (spfQuotientOn A J') ⟶ Z,
        schemeToLTRS.map c ≫ (yonedaEquiv i).hom = weakChartPoint A hA χ J' := by
  let W := pointPreimage (yonedaEquiv i).hom U
  have : CompactSpace W.toScheme :=
    isCompact_iff_compactSpace.1 (isCompact_pointPreimage_of_isThickening A hA χ hi)
  let g := schemeToLTRS.map W.ι ≫ (yonedaEquiv i).hom
  have hg : Set.range g.toHom.base ⊆ U := range_pointPreimage_subset _ U
  have hiff : ∀ t, (g.toHom.c.app (op U)).1 t = 0 ↔
      ((yonedaEquiv i).hom.toHom.c.app (op U)).1 t = 0 := fun t =>
    ⟨fun h => mem_ker_iff.1 (mem_ker_of_mem_ker_schemeToLTRS_map_ι_comp _ W le_rfl
      (mem_ker_iff.2 h)),
     fun h => mem_ker_iff.1 (ker_le_ker_comp (schemeToLTRS.map W.ι) _ U (mem_ker_iff.2 h))⟩
  obtain ⟨J₀, hJ₀⟩ := exists_weakIdeal_kill_weakChartSections A hA χ g hg
  obtain ⟨b₀, hb₀, -⟩ := existsUnique_weakChartPoint_factor A hA χ J₀ g hg hJ₀
  have hsurj : Function.Surjective b₀ := by
    intro y
    obtain ⟨w, hw⟩ := (isThickening_thickeningPullbackSnd A hA χ hi J₀).2 y
    have hrange : Set.range (thickeningPullbackFst A hA χ hi J₀) ⊆ Set.range W.ι := by
      rintro _ ⟨w', rfl⟩
      rw [Scheme.Opens.range_ι]
      exact range_thickeningPullbackFst_subset A hA χ hi J₀ w'
    let e := IsOpenImmersion.lift W.ι _ hrange
    have he : e ≫ W.ι = thickeningPullbackFst A hA χ hi J₀ := IsOpenImmersion.lift_fac _ _ _
    have hcomp : e ≫ b₀ = thickeningPullbackSnd A hA χ hi J₀ :=
      weakChartPoint_cancel_left A hA χ J₀ (by
        rw [schemeToLTRS_map_comp_comp, hb₀]
        have := thickeningPullback_w A hA χ hi J₀
        rw [← he] at this
        exact (schemeToLTRS_map_comp_comp e W.ι _).symm.trans this)
    exact ⟨e w, by rw [← Scheme.Hom.comp_apply, hcomp, hw]⟩
  let K : Ideal A :=
    Ideal.comap (weakChartSectionsRingEquiv A hA χ) ((ker (yonedaEquiv i).hom).ideal U)
  have hK : ∀ a, a ∈ K ↔
      ((yonedaEquiv i).hom.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 :=
    fun _ => mem_ker_iff
  have hJ₀K : J₀.1 ≤ K := fun a ha => (hK a).2 ((hiff _).1 (hJ₀ a ha))
  have hKnil : ∀ a ∈ K, IsTopologicallyNilpotent a := by
    intro a ha
    have h1 : (g.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 :=
      (hiff _).2 ((hK a).1 ha)
    have h2 := (c_app_weakChartSections_eq_zero_iff_of_comp A hA χ
      (schemeToLTRS.map b₀ ≫ spfwQuotientPoint A hA J₀) g
      ((Category.assoc _ _ _).trans hb₀) a).1 h1
    rw [spfPointGammaHomOn_comp_spfwQuotientPoint] at h2
    have h3 : b₀.appTop ((Scheme.ΓSpecIso (spfQuotientOn A J₀)).inv
        (Ideal.Quotient.mk J₀.1 a)) = 0 := h2
    obtain ⟨n, hn⟩ := isNilpotent_of_surjective_of_appTop_eq_zero b₀ hsurj h3
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact IsTopologicallyNilpotent.of_pow (J₀.2.2 _ hn)
  let J' : WeakIdealsOfDefinition A := ⟨K, Submodule.isOpen_mono hJ₀K J₀.2.1, hKnil⟩
  refine ⟨J', hK, ?_⟩
  have hgJ' : ∀ a ∈ J'.1, (g.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 :=
    fun a ha => (hiff _).2 ((hK a).1 ha)
  obtain ⟨b', hb', -⟩ := existsUnique_weakChartPoint_factor A hA χ J' g hg hgJ'
  have hspb := yoneda_map_comp_eq_yoneda_map_comp_weakChartPointMap A hA χ J' (a := W.ι) hb'.symm
  let sct := hi.rep.lift' W.ι b' hspb
  have hsct : sct ≫ thickeningPullbackFst A hA χ hi J' = W.ι := hi.rep.lift'_fst _ _ hspb
  have := (isThickening_thickeningPullbackSnd A hA χ hi J').1
  have hinj : Function.Injective (thickeningPullbackSnd A hA χ hi J').appTop := by
    refine (injective_iff_map_eq_zero (thickeningPullbackSnd A hA χ hi J').appTop.hom).2
      fun x hx => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (spfQuotientOn A J')).hom x)
    have hxa : x = (Scheme.ΓSpecIso (spfQuotientOn A J')).inv (Ideal.Quotient.mk J'.1 a) := by
      rw [ha]
      exact ((Scheme.ΓSpecIso (spfQuotientOn A J')).hom_inv_id_apply x).symm
    have h1 : ((schemeToLTRS.map (thickeningPullbackFst A hA χ hi J') ≫
        (yonedaEquiv i).hom).toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 := by
      refine (c_app_weakChartSections_eq_zero_iff_of_comp A hA χ
        (schemeToLTRS.map (thickeningPullbackSnd A hA χ hi J') ≫ spfwQuotientPoint A hA J') _
        ((Category.assoc _ _ _).trans (thickeningPullback_w A hA χ hi J').symm) a).2 ?_
      rw [spfPointGammaHomOn_comp_spfwQuotientPoint]
      change (thickeningPullbackSnd A hA χ hi J').appTop
        ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk J'.1 a)) = 0
      rw [← hxa]
      exact hx
    have h2 : g = schemeToLTRS.map sct ≫ (schemeToLTRS.map (thickeningPullbackFst A hA χ hi J') ≫
        (yonedaEquiv i).hom) :=
      (congrArg (fun m => schemeToLTRS.map m ≫ (yonedaEquiv i).hom) hsct).symm.trans
        (schemeToLTRS_map_comp_comp _ _ _)
    have h3 : (g.toHom.c.app (op U)).1 ((weakChartSections A hA χ).1 a) = 0 := by
      have := ker_le_ker_comp (schemeToLTRS.map sct) _ U (mem_ker_iff.2 h1)
      rw [← h2] at this
      exact mem_ker_iff.1 this
    have h4 : a ∈ J'.1 := (hK a).2 ((hiff _).1 h3)
    rw [hxa, (Ideal.Quotient.eq_zero_iff_mem).2 h4, map_zero]
  have := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  refine ⟨inv (thickeningPullbackSnd A hA χ hi J') ≫ thickeningPullbackFst A hA χ hi J', ?_⟩
  exact (schemeToLTRS_map_comp_comp _ _ _).trans
    ((congrArg (schemeToLTRS.map _ ≫ ·) (thickeningPullback_w A hA χ hi J')).trans
      ((schemeToLTRS_map_comp_comp _ _ _).symm.trans
        ((congrArg (· ≫ weakChartPoint A hA χ J') ((schemeToLTRS.map_comp _ _).symm.trans
          (congrArg schemeToLTRS.map (IsIso.inv_hom_id _)))).trans
          ((congrArg (· ≫ weakChartPoint A hA χ J') (schemeToLTRS.map_id _)).trans
            (Category.id_comp _)))))

end Chart

/-! ### The kernel of a thickening -/

section Main

variable {𝔛 : McQuillanFormalScheme.{u}} {Z : Scheme.{u}}
  {i : yoneda.obj Z ⟶ mcQuillanFormalSchemePoints 𝔛}
  (hi : MorphismProperty.presheaf @Stacks.Thickenings.IsThickening.{u} i)
include hi

/-- **The kernel ideal sheaf of a thickening is a weak ideal of definition** (Stacks 0AIV): over a
weak affine formal open `𝔘 ≅ Spfw A` it corresponds to the weak ideal of definition of `A`
formed by the elements killed by the thickening. -/
theorem isWeakIdealOfDefinitionOn_ker_of_isThickening :
    (ker (yonedaEquiv i).hom).IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj) := by
  intro U hU
  obtain ⟨J', hJ', -⟩ := exists_weakIdeal_ker_eq_of_isThickening hU.chart.ring.α
    hU.chart.admissible hU.chart.iso hi
  let e := weakChartSectionsHomeomorph hU.chart.ring.α hU.chart.admissible hU.chart.iso
  have hmem : ∀ t, t ∈ (ker (yonedaEquiv i).hom).ideal U ↔ e.symm t ∈ J'.1 := fun t => by
    have he : (weakChartSections hU.chart.ring.α hU.chart.admissible hU.chart.iso).1
        (e.symm t) = t := e.apply_symm_apply t
    rw [hJ', he, mem_ker_iff]
  refine ⟨?_, fun t ht => ?_⟩
  · have heq : ((ker (yonedaEquiv i).hom).ideal U : Set (𝔛.obj.presheaf.obj (op U)).α) =
        e.symm ⁻¹' J'.1 := Set.ext hmem
    rw [heq]
    exact J'.2.1.preimage e.symm.continuous
  · have h := IsTopologicallyNilpotent.map
      (φ := weakChartSectionsRingEquiv hU.chart.ring.α hU.chart.admissible hU.chart.iso)
      e.continuous (J'.2.2 _ ((hmem t).1 ht))
    have he : weakChartSectionsRingEquiv hU.chart.ring.α hU.chart.admissible hU.chart.iso
        (e.symm t) = t := e.apply_symm_apply t
    rwa [he] at h

/-- A point of `𝔛` landing in a weak affine formal open `U` and killing the sections of the kernel
of a thickening over `U` factors through the thickening. -/
theorem exists_factor_of_isThickening {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U)
    {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ 𝔛.obj) (hf : Set.range f.toHom.base ⊆ U)
    (hkill : ∀ t ∈ (ker (yonedaEquiv i).hom).ideal U, (f.toHom.c.app (op U)).1 t = 0) :
    ∃ k : T ⟶ Z, schemeToLTRS.map k ≫ (yonedaEquiv i).hom = f := by
  obtain ⟨J', hJ', c, hc⟩ := exists_weakIdeal_ker_eq_of_isThickening hU.chart.ring.α
    hU.chart.admissible hU.chart.iso hi
  obtain ⟨b, hb, -⟩ := existsUnique_weakChartPoint_factor _ _ _ J' f hf fun a ha =>
    hkill _ (mem_ker_iff.2 ((hJ' a).1 ha))
  exact ⟨b ≫ c, 
    (schemeToLTRS_map_comp_comp b c _).trans ((congrArg (schemeToLTRS.map b ≫ ·) hc).trans hb)⟩

/-- **The kernel ideal sheaf of a thickening is cut out by its sections over the weak affine
formal opens.** A section over `V ⊆ U` killed by every point landing in `U` and killing the
kernel over `U` is in particular killed by `φ⁻¹(U) → 𝔛`, hence by `Z → 𝔛`; conversely such a
point factors through `Z`. -/
theorem isCutOutOn_ker_of_isThickening :
    (ker (yonedaEquiv i).hom).IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj) := by
  intro U hU V hVU s
  refine ⟨fun hs T f hf hkill => ?_, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := exists_factor_of_isThickening hi hU f hf hkill
    have key : ∀ f' : schemeToLTRSObj T ⟶ 𝔛.obj,
        schemeToLTRS.map k ≫ (yonedaEquiv i).hom = f' → (f'.toHom.c.app (op V)).1 s = 0 := by
      rintro _ rfl
      exact mem_ker_iff.1 (ker_le_ker_comp _ _ V hs)
    exact key f hk
  · let W := pointPreimage (yonedaEquiv i).hom U
    have h1 := h W.toScheme (schemeToLTRS.map W.ι ≫ (yonedaEquiv i).hom)
      (range_pointPreimage_subset _ U) fun t ht => mem_ker_iff.1 (ker_le_ker_comp _ _ U ht)
    exact mem_ker_of_mem_ker_schemeToLTRS_map_ι_comp _ W (fun _ hx => hVU hx) (mem_ker_iff.2 h1)

/-- **A point of `𝔛` killing the kernel of a thickening `Z → 𝔛` factors uniquely through `Z`.**
Over the preimage of each weak affine formal open the point factors through `Z`, and these
factorisations glue, the thickening being a monomorphism. -/
theorem existsUnique_factor_of_kills_ker_of_isThickening {T : Scheme.{u}}
    (f : schemeToLTRSObj T ⟶ 𝔛.obj) (hf : (ker (yonedaEquiv i).hom).Kills f) :
    ∃! k : T ⟶ Z, schemeToLTRS.map k ≫ (yonedaEquiv i).hom = f := by
  choose U hxU hU using (isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen _).1
    𝔛.property
  let W : T → T.Opens := fun p => pointPreimage f (U (f.toHom.base p))
  have hW : iSup W = ⊤ := iSup_eq_top_of_forall_exists_mem W fun p => ⟨p, hxU _⟩
  have hloc : ∀ p, ∃ k : (W p).toScheme ⟶ Z,
      schemeToLTRS.map k ≫ (yonedaEquiv i).hom = schemeToLTRS.map (W p).ι ≫ f := fun p =>
    exists_factor_of_isThickening hi (hU _) _ (range_pointPreimage_subset f _)
      fun t ht => mem_ker_iff.1 ((hf.comp _) _ ht)
  choose k hk using hloc
  have hcomp : ∀ p {S : Scheme.{u}} (a : S ⟶ (W p).toScheme),
      schemeToLTRS.map (a ≫ k p) ≫ (yonedaEquiv i).hom =
        schemeToLTRS.map (a ≫ (W p).ι) ≫ f := fun p S a =>
    (schemeToLTRS_map_comp_comp a (k p) _).trans ((congrArg (schemeToLTRS.map a ≫ ·) (hk p)).trans
      (schemeToLTRS_map_comp_comp a (W p).ι f).symm)
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers T (fun p => (W p).toScheme) (fun p => (W p).ι)
    (fun p => ⟨p, ⟨p, hxU _⟩, rfl⟩)
  have hcompat : ∀ p q, pullback.fst (𝒰.f p) (𝒰.f q) ≫ k p = pullback.snd _ _ ≫ k q :=
    fun p q => schemeToLTRS_map_cancel_of_isThickening hi ((hcomp p _).trans
      ((congrArg (fun m => schemeToLTRS.map m ≫ f)
        (pullback.condition : pullback.fst (𝒰.f p) (𝒰.f q) ≫ 𝒰.f p = _)).trans
        (hcomp q _).symm))
  let K := 𝒰.glueMorphisms k hcompat
  have hK : ∀ p, (W p).ι ≫ K = k p := fun p => 𝒰.ι_glueMorphisms k hcompat p
  have hKf : schemeToLTRS.map K ≫ (yonedaEquiv i).hom = f := by
    obtain ⟨f₀, -, huniq⟩ := existsUnique_ltrsHom_of_openCover_scheme W hW
      (fun p => schemeToLTRS.map (W p).ι ≫ f) fun p q => by
        rw [← schemeToLTRS_map_comp_comp, ← schemeToLTRS_map_comp_comp, T.homOfLE_ι, T.homOfLE_ι]
    refine (huniq _ fun p => ?_).trans (huniq f fun _ => rfl).symm
    exact (schemeToLTRS_map_comp_comp _ _ _).symm.trans
      ((congrArg (fun m => schemeToLTRS.map m ≫ (yonedaEquiv i).hom) (hK p)).trans (hk p))
  exact ⟨K, hKf, fun k' hk' => schemeToLTRS_map_cancel_of_isThickening hi (hk'.trans hKf.symm)⟩

end Main

end LocallyTopologicallyRingedSpace.IdealSheaf

end AlgebraicGeometry

end
