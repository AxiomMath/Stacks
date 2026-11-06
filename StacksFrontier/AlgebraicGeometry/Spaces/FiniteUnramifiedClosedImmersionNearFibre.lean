module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.ClosedImmersion

/-!
# A finite unramified morphism to an algebraic space is a closed immersion near a fibre

Let `f : X ⟶ T` be a separated morphism from an algebraic space to a scheme, and let
`π : P ⟶ X` be a morphism from a scheme `P` which is unramified and such that `P ⟶ T` is finite.
If over a point `t ∈ T` every point of `P ×_X P` lies on the diagonal, then over an open
neighbourhood of `t` the morphism `π` is a closed immersion: for every scheme `Y ⟶ X` whose
image in `T` lies in that neighbourhood, the base change `P ×_X Y ⟶ Y` is a closed immersion
of schemes.

This is the form in which a relative effective Cartier divisor constructed on an étale chart of
a family of curves is moved to the family itself, in the proof that families of curves are
étale locally schemes (Stacks 0E6F).

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_toScheme_lift_of_isSeparated`: for two schemes
  `Y₁`, `Y₂` over `X`, the comparison `Y₁ ×_X Y₂ ⟶ Y₁ ×_T Y₂` is a closed immersion when
  `X ⟶ T` is separated.
* `AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_of_isFinite_of_unramified`: the
  statement above.

## Implementation notes

The proof follows the usual argument. The diagonal `δ : P ⟶ P ×_X P` is a section of the second
projection, which is unramified, so `δ` is an open immersion (Stacks 024T); its complement `R` is
closed, and `P ×_X P` is finite over `T` because it is closed in `P ×_T P`. The image of `R` in
`T` is therefore closed and misses `t`. Over its complement `V`, for a scheme `Y ⟶ X` landing in
`V`, the diagonal of `P ×_X Y ⟶ Y` is a base change of `δ`, an open immersion all of whose
points lie in the range of `δ`, hence an isomorphism; so `P ×_X Y ⟶ Y` is a monomorphism, and it
is proper, being closed in the finite `P ×_T Y`. A proper monomorphism is a closed immersion
(Stacks 04XV).

## References

* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- Two schemes over `X` and a pullback square over `X` give equal composites to the base `T`. -/
private theorem comp_eq_comp_of_isPullback_of_comp_eq
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T Y₁ Y₂ Z : BigFppfOver B S hS}
    {f : X ⟶ yoneda.obj T} {g₁ : yoneda.obj Y₁ ⟶ X} {g₂ : yoneda.obj Y₂ ⟶ X}
    {a : Z ⟶ Y₁} {b : Z ⟶ Y₂} (sq : IsPullback (yoneda.map a) (yoneda.map b) g₁ g₂)
    {p₁ : Y₁ ⟶ T} {p₂ : Y₂ ⟶ T} (h₁ : g₁ ≫ f = yoneda.map p₁) (h₂ : g₂ ≫ f = yoneda.map p₂) :
    a ≫ p₁ = b ≫ p₂ := Yoneda.fullyFaithful.map_injective (by
  rw [Functor.map_comp, Functor.map_comp, ← h₁, ← h₂, ← Category.assoc, sq.w, Category.assoc])

/-- A pair of maps to the legs of a pullback square over `X` that agree in `X` factors through the
pullback. -/
private theorem exists_comp_eq_of_isPullback
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₁ Y₂ Z W : BigFppfOver B S hS}
    {g₁ : yoneda.obj Y₁ ⟶ X} {g₂ : yoneda.obj Y₂ ⟶ X} {a : Z ⟶ Y₁} {b : Z ⟶ Y₂}
    (sq : IsPullback (yoneda.map a) (yoneda.map b) g₁ g₂) (u : W ⟶ Y₁) (v : W ⟶ Y₂)
    (w : yoneda.map u ≫ g₁ = yoneda.map v ≫ g₂) : ∃ e : W ⟶ Z, e ≫ a = u ∧ e ≫ b = v :=
  ⟨Yoneda.fullyFaithful.preimage (sq.lift _ _ w),
    Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, sq.lift_fst]),
    Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, sq.lift_snd])⟩

/-- **The comparison of fibre products over a separated base change.** For a separated morphism
`f : X ⟶ T` from an algebraic space to a scheme and two schemes `Y₁`, `Y₂` over `X`, the morphism
from a fibre product `Z = Y₁ ×_X Y₂` to `Y₁ ×_T Y₂` is a closed immersion of schemes. -/
theorem isClosedImmersion_toScheme_lift_of_isSeparated
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T Y₁ Y₂ Z : BigFppfOver B S hS}
    (f : X ⟶ yoneda.obj T) (hf : IsSeparated B S hS f)
    (g₁ : yoneda.obj Y₁ ⟶ X) (g₂ : yoneda.obj Y₂ ⟶ X) (a : Z ⟶ Y₁) (b : Z ⟶ Y₂)
    (sq : IsPullback (yoneda.map a) (yoneda.map b) g₁ g₂)
    (p₁ : Y₁ ⟶ T) (p₂ : Y₂ ⟶ T) (h₁ : g₁ ≫ f = yoneda.map p₁) (h₂ : g₂ ≫ f = yoneda.map p₂) :
    AlgebraicGeometry.IsClosedImmersion
      ((𝒯).map (pullback.lift a b (Yoneda.fullyFaithful.map_injective (by
        rw [Functor.map_comp, Functor.map_comp, ← h₁, ← h₂, ← Category.assoc, sq.w,
          Category.assoc]) : a ≫ p₁ = b ≫ p₂))) := by
  have hab : a ≫ p₁ = b ≫ p₂ := comp_eq_comp_of_isPullback_of_comp_eq sq h₁ h₂
  -- the square of represented presheaves of `Y₁ ×_T Y₂`
  have hP : IsPullback (yoneda.map (pullback.fst p₁ p₂)) (yoneda.map (pullback.snd p₁ p₂))
      (g₁ ≫ f) (g₂ ≫ f) := by
    rw [h₁, h₂]
    exact (IsPullback.of_hasPullback p₁ p₂).map yoneda
  -- instance search for pullbacks of presheaves times out: supply the ones used below
  have : HasLimit (cospan f f) := HasLimitsOfShape.has_limit _
  have : HasLimit (cospan g₁ g₂) := HasLimitsOfShape.has_limit _
  have : HasLimit (cospan (g₁ ≫ f) (g₂ ≫ f)) := HasLimitsOfShape.has_limit _
  have : HasLimit (cospan (pullback.diagonal f) (pullback.map (g₁ ≫ f) (g₂ ≫ f) f f g₁ g₂ (𝟙 _)
      (Category.comp_id _) (Category.comp_id _))) := HasLimitsOfShape.has_limit _
  -- Mathlib's square exhibiting `pullback g₁ g₂ ⟶ pullback (g₁ ≫ f) (g₂ ≫ f)` as a base change
  -- of the diagonal of `f`
  have H' : IsPullback (yoneda.map a ≫ g₁) (yoneda.map (pullback.lift a b hab))
      (pullback.diagonal f)
      (pullback.lift (f := f) (g := f) (yoneda.map (pullback.fst p₁ p₂) ≫ g₁)
        (yoneda.map (pullback.snd p₁ p₂) ≫ g₂)
        (by rw [Category.assoc, Category.assoc]; exact hP.w)) := by
    refine (pullback_map_diagonal_isPullback g₁ g₂ f).of_iso sq.isoPullback.symm (Iso.refl _)
      hP.isoPullback.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · apply hP.hom_ext
      · simp only [Category.assoc, ← Functor.map_comp, pullback.lift_fst]
        simp only [Iso.symm_hom, IsPullback.isoPullback_inv_fst]
        exact pullback.lift_fst _ _ _
      · simp only [Category.assoc, ← Functor.map_comp, pullback.lift_snd]
        simp only [Iso.symm_hom, IsPullback.isoPullback_inv_snd]
        exact pullback.lift_snd _ _ _
    · simp
    · apply pullback.hom_ext
      · simp only [Iso.refl_hom, Category.comp_id, Category.assoc, pullback.lift_fst, Iso.symm_hom,
          IsPullback.isoPullback_inv_fst_assoc]
      · simp only [Iso.refl_hom, Category.comp_id, Category.assoc, pullback.lift_snd, Iso.symm_hom,
          IsPullback.isoPullback_inv_snd_assoc]
  exact hf.property _ _ _ H'

/-- **A finite unramified morphism to an algebraic space is a closed immersion near a fibre on
which it has no off-diagonal points.** Let `f : X ⟶ T` be a separated morphism from an algebraic
space to a scheme and `π : P ⟶ X` an unramified morphism from a scheme with `P ⟶ T` finite.
Suppose that over `t ∈ T` every point of `P ×_X P` lies on the diagonal. Then there is an open
neighbourhood `V` of `t` such that for every scheme `Y ⟶ X` landing over `V`, the base change
`P ×_X Y ⟶ Y` is a closed immersion. -/
theorem exists_isOpen_isClosedImmersion_of_isFinite_of_unramified
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {T P : BigFppfOver B S hS} (f : X ⟶ yoneda.obj T) (hf : IsSeparated B S hS f)
    (p : P ⟶ T) [_root_.AlgebraicGeometry.IsFinite ((𝒯).map p)]
    (π : yoneda.obj P ⟶ X) (hπ : π ≫ f = yoneda.map p)
    (hun : (MorphismProperty.inverseImage @Unramified (𝒯)).presheaf π)
    (t : (𝒯).obj T)
    (hfib : ∀ {Q : BigFppfOver B S hS} (a b : Q ⟶ P) (δ : P ⟶ Q),
      IsPullback (yoneda.map a) (yoneda.map b) π π → δ ≫ a = 𝟙 P → δ ≫ b = 𝟙 P →
      ∀ q : (𝒯).obj Q, (𝒯).map (a ≫ p) q = t → q ∈ Set.range ((𝒯).map δ)) :
    ∃ V : ((𝒯).obj T).Opens, t ∈ V ∧
      ∀ {Y Z : BigFppfOver B S hS} (g : yoneda.obj Y ⟶ X) (pY : Y ⟶ T),
        g ≫ f = yoneda.map pY → ∀ (a : Z ⟶ P) (b : Z ⟶ Y),
        IsPullback (yoneda.map a) (yoneda.map b) π g →
        (∀ y, (𝒯).map pY y ∈ V) → AlgebraicGeometry.IsClosedImmersion ((𝒯).map b) := by
  have hrep := relativelyRepresentable_of_isAlgebraicSpace (B := B) (S := S) (hS := hS) hX π
  set Q := hrep.pullback π
  set a₀ : Q ⟶ P := hrep.fst' π
  set b₀ : Q ⟶ P := hrep.snd π
  have sq₀ : IsPullback (yoneda.map a₀) (yoneda.map b₀) π π := hrep.isPullback' π
  obtain ⟨δ, hδa, hδb⟩ := exists_comp_eq_of_isPullback sq₀ (𝟙 P) (𝟙 P) rfl
  -- the second projection is unramified, so the diagonal is an open immersion
  have hb₀ : Unramified ((𝒯).map b₀) := hun.property π (yoneda.map a₀) b₀ sq₀
  have hδ : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map δ) :=
    Unramified.section_isOpenImmersion ((𝒯).map b₀) ((𝒯).map δ)
      (by rw [← Functor.map_comp, hδb, CategoryTheory.Functor.map_id])
  -- `P ×_X P` is finite over `T`
  have hab₀ : a₀ ≫ p = b₀ ≫ p := comp_eq_comp_of_isPullback_of_comp_eq sq₀ hπ hπ
  have hc := isClosedImmersion_toScheme_lift_of_isSeparated f hf π π a₀ b₀ sq₀ p p hπ hπ
  have hfst : _root_.AlgebraicGeometry.IsFinite ((𝒯).map (pullback.fst p p)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback p p).map (𝒯)).flip
      (inferInstance : _root_.AlgebraicGeometry.IsFinite ((𝒯).map p))
  have hQfin : _root_.AlgebraicGeometry.IsFinite ((𝒯).map (a₀ ≫ p)) := by
    have : a₀ ≫ p = pullback.lift a₀ b₀ hab₀ ≫ pullback.fst p p ≫ p :=
      (pullback.lift_fst_assoc a₀ b₀ hab₀ p).symm
    rw [this, Functor.map_comp, Functor.map_comp]
    infer_instance
  -- the closed image of the off-diagonal part
  let K : Set ((𝒯).obj T) := (𝒯).map (a₀ ≫ p) '' (Set.range ((𝒯).map δ))ᶜ
  have hK : IsClosed K :=
    ((𝒯).map (a₀ ≫ p)).isClosedMap _ (hδ.base_open.isOpen_range.isClosed_compl)
  have htK : t ∉ K := by
    rintro ⟨q, hq, hqt⟩
    exact hq (hfib a₀ b₀ δ sq₀ hδa hδb q hqt)
  refine ⟨⟨Kᶜ, hK.isOpen_compl⟩, htK, ?_⟩
  intro Y Z g pY hg a b sq hV
  have hap : a ≫ p = b ≫ pY := comp_eq_comp_of_isPullback_of_comp_eq sq hπ hg
  -- properness: `Z` is closed in `P ×_T Y`, which is finite over `Y`
  have hc' := isClosedImmersion_toScheme_lift_of_isSeparated f hf π g a b sq p pY hπ hg
  have hsnd : _root_.AlgebraicGeometry.IsFinite ((𝒯).map (pullback.snd p pY)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback p pY).map (𝒯))
      (inferInstance : _root_.AlgebraicGeometry.IsFinite ((𝒯).map p))
  have hprop : _root_.AlgebraicGeometry.IsProper ((𝒯).map b) := by
    have : b = pullback.lift a b hap ≫ pullback.snd p pY := (pullback.lift_snd a b hap).symm
    rw [this, Functor.map_comp]
    infer_instance
  -- monomorphism: two maps to `Z` agreeing in `Y` agree in `P`, through the diagonal
  have hmono : Mono b := by
    refine ⟨fun {W} u₁ u₂ hu => ?_⟩
    have hw : yoneda.map (u₁ ≫ a) ≫ π = yoneda.map (u₂ ≫ a) ≫ π := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, sq.w,
        ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hu]
    obtain ⟨e, hea, heb⟩ := exists_comp_eq_of_isPullback sq₀ _ _ hw
    have hrange : Set.range ((𝒯).map e) ⊆ Set.range ((𝒯).map δ) := by
      rintro _ ⟨w, rfl⟩
      by_contra hw'
      have : (𝒯).map (a₀ ≫ p) ((𝒯).map e w) ∈ K := ⟨_, hw', rfl⟩
      have h1 : (𝒯).map (a₀ ≫ p) ((𝒯).map e w) = (𝒯).map pY ((𝒯).map (u₁ ≫ b) w) := by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Scheme.Hom.comp_apply,
          ← Functor.map_comp, ← Category.assoc, hea, Category.assoc, hap, Category.assoc]
      exact hV _ (h1 ▸ this)
    let l := _root_.AlgebraicGeometry.IsOpenImmersion.lift ((𝒯).map δ) ((𝒯).map e) hrange
    have hl : l ≫ (𝒯).map δ = (𝒯).map e := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
    have key : ∀ {c : Q ⟶ P} {u : W ⟶ P}, δ ≫ c = 𝟙 P → e ≫ c = u → (𝒯).map u = l := by
      intro c u hδc hec
      rw [← hec, Functor.map_comp, ← hl, Category.assoc, ← Functor.map_comp, hδc,
        CategoryTheory.Functor.map_id, Category.comp_id]
    have ha : u₁ ≫ a = u₂ ≫ a := (𝒯).map_injective ((key hδa hea).trans (key hδb heb).symm)
    apply Yoneda.fullyFaithful.map_injective
    apply sq.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp, ha]
    · rw [← Functor.map_comp, ← Functor.map_comp, hu]
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono _).2
    ⟨hprop, Functor.map_mono _ b⟩

/-- **The base change over a neighbourhood is a closed immersion.** In the situation of
`AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_of_isFinite_of_unramified`, let `V` be
an open of `T` such that every base change `P ×_X Y ⟶ Y` along a scheme `Y` over `V` is a closed
immersion. Then for every morphism `ι : T' ⟶ T` of the site with image in `V`, the morphism
`π' : P ×_T T' ⟶ X ×_T T'` induced by `π` is a closed immersion. -/
theorem isClosedImmersion_of_isPullback_of_forall_mem
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    {T T' P P' : BigFppfOver B S hS} (f : X ⟶ yoneda.obj T) (p : P ⟶ T)
    (π : yoneda.obj P ⟶ X) (hπ : π ≫ f = yoneda.map p) (V : ((𝒯).obj T).Opens)
    (hV : ∀ {Y Z : BigFppfOver B S hS} (g : yoneda.obj Y ⟶ X) (pY : Y ⟶ T),
        g ≫ f = yoneda.map pY → ∀ (a : Z ⟶ P) (b : Z ⟶ Y),
        IsPullback (yoneda.map a) (yoneda.map b) π g →
        (∀ y, (𝒯).map pY y ∈ V) → AlgebraicGeometry.IsClosedImmersion ((𝒯).map b))
    (ι : T' ⟶ T) (hι : ∀ t', (𝒯).map ι t' ∈ V)
    (q : X' ⟶ X) (f' : X' ⟶ yoneda.obj T') (sqX : IsPullback q f' f (yoneda.map ι))
    (pP : P' ⟶ P) (p' : P' ⟶ T') (sqP : IsPullback pP p' p ι)
    (π' : yoneda.obj P' ⟶ X') (hπ'q : π' ≫ q = yoneda.map pP ≫ π)
    (hπ'f : π' ≫ f' = yoneda.map p') :
    IsClosedImmersion B S hS π' := by
  have htop : IsPullback (yoneda.map pP) π' π q := by
    refine IsPullback.of_bot ?_ hπ'q.symm sqX
    rw [hπ'f, hπ]
    exact sqP.map yoneda
  refine ⟨relativelyRepresentable_of_isAlgebraicSpace (B := B) (S := S) (hS := hS) hX' π', ?_⟩
  intro Y Z g fst snd hsq
  have H := hsq.paste_horiz htop
  have hfst : yoneda.map (Yoneda.fullyFaithful.preimage fst ≫ pP) = fst ≫ yoneda.map pP := by
    rw [Functor.map_comp, Functor.FullyFaithful.map_preimage]
  have hg : (g ≫ q) ≫ f = yoneda.map (Yoneda.fullyFaithful.preimage (g ≫ f') ≫ ι) := by
    rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, Category.assoc, sqX.w,
      Category.assoc]
  refine hV (g ≫ q) _ hg (Yoneda.fullyFaithful.preimage fst ≫ pP) snd (hfst ▸ H) ?_
  intro y
  rw [Functor.map_comp, Scheme.Hom.comp_apply]
  exact hι _

end AlgebraicGeometry.Space

end
