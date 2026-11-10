module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteUnramifiedClosedImmersionNearFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PresheafPointTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# A closed subscheme of an étale chart which is a closed subspace of the space

Let `e : W ⟶ X` be an étale morphism from a scheme to an algebraic space and `j : P ⟶ W` a
closed immersion of schemes such that the composite `π = j ≫ e : P ⟶ X` is a closed immersion of
algebraic spaces. Then the range `D` of `π` is a closed subspace of `X`, and if `P` is an
effective Cartier divisor in `W` near each of its points, then `D` is an effective Cartier divisor
on `X` (Stacks 083B).

This is how a divisor constructed on an étale chart of a family of curves becomes a divisor on
the family, in the proof that families of curves are étale locally schemes (Stacks 0E6F).

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_range_of_etaleChart`: the statement above,
  through the affine principal étale neighbourhoods of Stacks 083C, condition (4).

## Implementation notes

The fibre product `Y = W ×_X P` contains the graph of `j` as an open and closed piece: its
projection to `P` is étale with the graph as a section (Stacks 024T), and its projection to `W`
is a closed immersion, being a base change of `π`. The image in `W` of the complement of the
graph is closed and misses `j(P)`, because the projection to `W` is injective. Over an open
`U ⊆ W` avoiding that image, a morphism `T ⟶ U` whose composite to `X` factors through `π` lands
in the graph, hence factors through `j`; so `D ×_X U = P ×_W U`. The neighbourhoods of the points
of `P` on which `P` is cut out by a nonzerodivisor are chosen inside that open.

## References

* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- Two points of a represented presheaf attached to equal points of the representing scheme
are equal. -/
theorem presheafPoint_congr (U : BigFppfOver B S hS) {a b : U.left.1} (h : a = b)
    (ha : B.Contains (Spec (.of (U.left.1.residueField a))))
    (hb : B.Contains (Spec (.of (U.left.1.residueField b)))) :
    presheafPoint B S hS U a ha = presheafPoint B S hS U b hb := by
  subst h
  rfl

/-- **The range of a closed immersion through an étale chart is an effective Cartier divisor
when it is one on the chart.** Let `e : W ⟶ X` be étale, `j : P ⟶ W` a morphism of schemes with
`π = j ≫ e` a closed immersion, and suppose that each point `v` of `P` has, inside every open of
`W` containing `j(v)`, an affine open neighbourhood `U` on which `P ×_W U` is cut out by a
nonzerodivisor. Then the range of `π` is an effective Cartier divisor on `X`. -/
theorem isEffectiveCartierDivisor_range_of_etaleChart
    {X : AlgebraicSpaces B S hS} {W P : BigFppfOver B S hS} (e : yoneda.obj W ⟶ X.1)
    (he : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e) (j : P ⟶ W)
    (hπ : IsClosedImmersion B S hS (yoneda.map j ≫ e))
    (hloc : ∀ (v : (𝒯).obj P) (O : ((𝒯).obj W).Opens), (𝒯).map j v ∈ O →
      ∃ (U R : BigFppfOver B S hS) (ι : U ⟶ W) (r : R ⟶ P) (k : R ⟶ U) (w : (𝒯).obj U),
        _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map ι) ∧ IsAffine ((𝒯).obj U) ∧
        Set.range ((𝒯).map ι) ⊆ O ∧ (𝒯).map ι w = (𝒯).map j v ∧ IsPullback r k j ι ∧
        ∃ (f : Γ((𝒯).obj U, ⊤))
          (iso : (𝒯).obj R ≅ (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subscheme),
          IsRegular f ∧ (𝒯).map k =
            iso.hom ≫ (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι) :
    IsEffectiveCartierDivisor B S hS X
      ⟨Subfunctor.range (yoneda.map j ≫ e), isClosedSubspace_range_of_isClosedImmersion B S hS _
        (isAlgebraicSpace_yoneda B S hS P) hπ⟩ := by
  set π := yoneda.map j ≫ e with hπdef
  have hrep := relativelyRepresentable_of_isAlgebraicSpace (B := B) (S := S) (hS := hS) X.2 π
  -- the fibre product `Y = W ×_X P`, with its two projections and the graph of `j`
  set Y := hrep.pullback e
  set pP : Y ⟶ P := hrep.fst' e
  set pW : Y ⟶ W := hrep.snd e
  have sqY : IsPullback (yoneda.map pP) (yoneda.map pW) π e := hrep.isPullback' e
  have hpW : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map pW) :=
    hπ.property e (yoneda.map pP) pW sqY
  have hpP : Etale ((𝒯).map pP) := he.property π (yoneda.map pW) pP sqY.flip
  have hlift : ∀ {T : BigFppfOver B S hS} (a : T ⟶ P) (b : T ⟶ W),
      yoneda.map a ≫ π = yoneda.map b ≫ e → ∃ κ : T ⟶ Y, κ ≫ pP = a ∧ κ ≫ pW = b := fun a b h =>
    ⟨Yoneda.fullyFaithful.preimage (sqY.lift (yoneda.map a) (yoneda.map b) h),
      Yoneda.fullyFaithful.map_injective (by simp), Yoneda.fullyFaithful.map_injective (by simp)⟩
  obtain ⟨γ, hγP, hγW⟩ := hlift (𝟙 P) j (by simp [π])
  have hγ : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map γ) :=
    Unramified.section_isOpenImmersion ((𝒯).map pP) ((𝒯).map γ)
      (by rw [← Functor.map_comp, hγP, CategoryTheory.Functor.map_id])
  -- the open of `W` avoiding the off-graph part
  let K : Set ((𝒯).obj W) := (𝒯).map pW '' (Set.range ((𝒯).map γ))ᶜ
  have hK : IsClosed K :=
    ((𝒯).map pW).isClosedMap _ hγ.base_open.isOpen_range.isClosed_compl
  let O₀ : ((𝒯).obj W).Opens := ⟨Kᶜ, hK.isOpen_compl⟩
  have hjO : ∀ v, (𝒯).map j v ∈ O₀ := by
    rintro v ⟨y, hy, hyv⟩
    apply hy
    refine ⟨v, ((𝒯).map pW).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hγW, hyv]
  apply isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods
  intro x
  -- the point `x` comes from a point `v` of `P`
  have hmono : Mono π := by
    have : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (𝒯)) ≤ MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
      intro A A' g hg
      have : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map g) := hg
      exact ⟨fun g₁ g₂ hgg => (𝒯).map_injective ((cancel_mono ((𝒯).map g)).1 (by
        rw [← Functor.map_comp, ← Functor.map_comp, hgg]))⟩
    exact MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone this _ hπ)
  obtain ⟨x', rfl⟩ : ∃ x', pointsMap B S hS _ (asIso (Subfunctor.toRange π)).hom x' = x := by
    refine ⟨pointsMap B S hS _ (asIso (Subfunctor.toRange π)).inv x, ?_⟩
    have h := congrFun (pointsMap_comp B S hS _ (asIso (Subfunctor.toRange π)).inv
      (asIso (Subfunctor.toRange π)).hom) x
    rw [Iso.inv_hom_id, pointsMap_id] at h
    exact h.symm
  set v := pointsToScheme B S hS P x'
  have hv : B.Contains (Spec (.of (P.left.1.residueField v))) :=
    B.residueField_spec_contains P.left.property v
  have hx' : x' = presheafPoint B S hS P v hv := by
    apply injective_pointsToScheme B S hS P
    rw [pointsToScheme_presheafPoint]
  obtain ⟨U, R, ι, r, k, w, hι, hUaff, hιO, hιw, hpb, f, iso, hreg, hk⟩ := hloc v O₀ (hjO v)
  have hw : B.Contains (Spec (.of (U.left.1.residueField w))) :=
    B.residueField_spec_contains U.left.property w
  have hιet : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf (yoneda.map ι) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS @Etale ι).2 inferInstance
  refine ⟨U, yoneda.map ι ≫ e, presheafPoint B S hS U w hw, hUaff, ?_, ?_, f, R, k, iso, hreg,
    hk, ?_⟩
  · exact isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2 hιet)
      ((isEtale_iff_presheaf_of_yoneda B S hS _).2 he)
  · have e1 := congrFun (pointsMap_comp B S hS _ (yoneda.map ι) e) (presheafPoint B S hS U w hw)
    have e2 := congrFun (pointsMap_comp B S hS _ (asIso (Subfunctor.toRange π)).hom
      (Subfunctor.range π).ι) x'
    have e3 := congrFun (pointsMap_comp B S hS _ (yoneda.map j) e) (presheafPoint B S hS P v hv)
    simp only [Function.comp_apply, asIso_hom, Subfunctor.toRange_ι] at e1 e2 e3
    rw [e1]
    change _ = pointsMap B S hS (Subfunctor.range π).toFunctor (Subfunctor.range π).ι
      (pointsMap B S hS (yoneda.obj P) (Subfunctor.toRange π) x')
    rw [← e2]
    conv_rhs => rw [hx', show π = yoneda.map j ≫ e from rfl, e3]
    rw [pointsMap_presheafPoint B S hS U W ι w hw
        (B.residueField_spec_contains W.left.property _),
      pointsMap_presheafPoint B S hS P W j v hv
        (B.residueField_spec_contains W.left.property _)]
    exact congrArg _ (presheafPoint_congr W hιw _ _)
  · -- `D ×_X U` is `P ×_W U`
    ext T t
    simp only [Subfunctor.preimage_obj, Set.mem_preimage, Subfunctor.range_obj, Set.mem_range]
    constructor
    · rintro ⟨s, hs⟩
      have hs' : yoneda.map s ≫ π = yoneda.map t ≫ yoneda.map ι ≫ e := by
        rw [hπdef, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
        exact hs
      obtain ⟨κ, hκP, hκW⟩ := hlift s (t ≫ ι) (by
        rw [hs', Functor.map_comp, Category.assoc])
      have hrange : Set.range ((𝒯).map κ) ⊆ Set.range ((𝒯).map γ) := by
        rintro _ ⟨τ, rfl⟩
        by_contra hτ
        have h1 : (𝒯).map pW ((𝒯).map κ τ) ∈ K := ⟨_, hτ, rfl⟩
        have h2 : (𝒯).map pW ((𝒯).map κ τ) = (𝒯).map ι ((𝒯).map t τ) := by
          rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hκW, Functor.map_comp,
            Scheme.Hom.comp_apply]
        rw [h2] at h1
        exact (hιO ⟨_, rfl⟩) h1
      let l := _root_.AlgebraicGeometry.IsOpenImmersion.lift ((𝒯).map γ) ((𝒯).map κ) hrange
      have hl : l ≫ (𝒯).map γ = (𝒯).map κ := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
      have hsj : s ≫ j = t ≫ ι := by
        apply (𝒯).map_injective
        calc (𝒯).map (s ≫ j) = ((l ≫ (𝒯).map γ) ≫ (𝒯).map pP) ≫ (𝒯).map j := by
              rw [hl, ← Functor.map_comp, hκP, Functor.map_comp]
          _ = l ≫ (𝒯).map (γ ≫ pW) := by
              simp only [Category.assoc]
              rw [← Functor.map_comp_assoc, hγP, CategoryTheory.Functor.map_id, Category.id_comp,
                hγW]
          _ = (𝒯).map (t ≫ ι) := by
              rw [Functor.map_comp, ← Category.assoc, hl, ← Functor.map_comp, hκW]
      exact ⟨hpb.lift s t hsj, hpb.lift_snd _ _ _⟩
    · rintro ⟨s', rfl⟩
      refine ⟨s' ≫ r, ?_⟩
      change e.app T ((s' ≫ r) ≫ j) = e.app T ((s' ≫ k) ≫ ι)
      rw [Category.assoc, Category.assoc, hpb.w]

end AlgebraicGeometry.Space

end
