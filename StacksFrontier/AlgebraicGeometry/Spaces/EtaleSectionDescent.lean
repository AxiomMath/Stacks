module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenSubspaceOfRepr
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairCoequalizer
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Descending a section of an étale morphism along a universal homeomorphism

Let `p : P ⟶ T` be an étale morphism of algebraic spaces over a scheme `S` and let
`g : T' ⟶ T` be integral, universally injective and surjective. This file shows that every
section of the base change `p' : P ×_T T' ⟶ T'` is the base change of a section of `p`:
`AlgebraicGeometry.Space.exists_section_of_isPullback_of_section`.

## Main results

* `AlgebraicGeometry.Space.isHomeomorph_pointsMap_of_universalHomeomorphism_of_isAlgebraicSpace`:
  a universal homeomorphism to an algebraic space is itself a homeomorphism on points.
* `AlgebraicGeometry.Space.universalHomeomorphism_of_isIntegralHom_of_universallyInjective`: an
  integral, universally injective and surjective morphism is a universal homeomorphism.
* `AlgebraicGeometry.Space.isEtale_of_isPullback_presheaf`: étaleness is stable under base change
  along any cartesian square of presheaves.
* `AlgebraicGeometry.Space.isSurjective_of_comm_of_surjective`,
  `AlgebraicGeometry.Space.injective_pointsMap_of_comm` and
  `AlgebraicGeometry.Space.universallyInjective_of_comm_of_isIso`: surjectivity, injectivity on
  points and universal injectivity descend across a commuting square whose other three edges are
  controlled.
* `AlgebraicGeometry.Space.isIso_of_isEtale_of_isPullback_of_isIso_of_universallyInjective`: an
  étale morphism one of whose base changes along a surjective, universally injective morphism is
  an isomorphism is itself an isomorphism.
* `AlgebraicGeometry.Space.exists_section_of_isPullback_of_section`: a section of the base change
  of an étale morphism along an integral, universally injective and surjective morphism is the
  base change of a section.
* `AlgebraicGeometry.Space.exists_hom_of_section_descent`: a morphism `T' ⟶ V₀` over the base,
  with `V₀` étale over the base, descends along such a morphism `T' ⟶ T`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 05Z4](https://stacks.math.columbia.edu/tag/05Z4)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_etaleSectionDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Universal homeomorphisms -/

section UniversalHomeomorphism

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A universal homeomorphism of algebraic spaces over `S` is a homeomorphism on the point
spaces. -/
theorem isHomeomorph_pointsMap_of_universalHomeomorphism_of_isAlgebraicSpace {f : F ⟶ G}
    (hG : IsAlgebraicSpace B S hS G) (hf : UniversalHomeomorphism B S hS f) :
    IsHomeomorph (pointsMap B S hS F f) :=
  have sq₀ : IsPullback (𝟙 F) f f (𝟙 G) := IsPullback.of_horiz_isIso ⟨by simp⟩
  isHomeomorph_pointsMap_of_comp_isIso B S hS sq₀.flip.isoPullback.hom
    sq₀.flip.isoPullback_hom_fst (hf G hG (𝟙 G))

/-- An integral, universally injective and surjective morphism of algebraic spaces over `S` is a
universal homeomorphism. -/
theorem universalHomeomorphism_of_isIntegralHom_of_universallyInjective
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G}
    (hint : IsIntegralHom B S hS f) (hui : UniversallyInjective B S hS f)
    (hsurj : IsSurjective B S hS f) :
    UniversalHomeomorphism B S hS f :=
  universalHomeomorphism_of_universallyClosed B S hS f hsurj hui
    (universallyClosed_of_isIntegralHom B S hS hF hG hint)

end UniversalHomeomorphism

/-! ### Étaleness of a base change, for presheaves -/

section EtaleBaseChange

variable {F G H P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Étaleness is stable under base change along any cartesian square of presheaves. -/
theorem isEtale_of_isPullback_presheaf (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H) {f : F ⟶ H} {g : G ⟶ H}
    {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst snd f g) (hf : IsEtale B S hS f) :
    IsEtale B S hS snd := by
  rw [← sq.isoPullback_hom_snd]
  exact isEtale_comp B S hS (isEtale_of_isIso B S hS sq.isoPullback.hom)
    (isEtale_pullback_snd B S hS hG hH hF f g hf)

end EtaleBaseChange

/-! ### Descending surjectivity and universal injectivity across a square -/

section Descent

variable {A A' T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A commuting square `u ≫ h = h' ≫ g` induces a commuting square on points. -/
private theorem pointsMap_comp_comm {h : A ⟶ T} {g : T' ⟶ T} {u : A' ⟶ A} {h' : A' ⟶ T'}
    (w : u ≫ h = h' ≫ g) :
    pointsMap B S hS A h ∘ pointsMap B S hS A' u =
      pointsMap B S hS T' g ∘ pointsMap B S hS A' h' := by
  rw [← pointsMap_comp, w, pointsMap_comp]

/-- If `u ≫ h = h' ≫ g` and both `g` and `h'` are surjective on points, then so is `h`. -/
theorem isSurjective_of_comm_of_surjective {h : A ⟶ T} {g : T' ⟶ T} {u : A' ⟶ A} {h' : A' ⟶ T'}
    (w : u ≫ h = h' ≫ g) (hg : IsSurjective B S hS g)
    (hh' : Function.Surjective (pointsMap B S hS A' h')) :
    IsSurjective B S hS h := by
  refine Function.Surjective.of_comp (g := pointsMap B S hS A' u) ?_
  rw [pointsMap_comp_comm B S hS w]
  exact hg.comp hh'

/-- If `u ≫ h = h' ≫ g`, if `u` is surjective on points and if both `g` and `h'` are injective on
points, then `h` is injective on points. -/
theorem injective_pointsMap_of_comm {h : A ⟶ T} {g : T' ⟶ T} {u : A' ⟶ A} {h' : A' ⟶ T'}
    (w : u ≫ h = h' ≫ g) (hu : Function.Surjective (pointsMap B S hS A' u))
    (hg : Function.Injective (pointsMap B S hS T' g))
    (hh' : Function.Injective (pointsMap B S hS A' h')) :
    Function.Injective (pointsMap B S hS A h) := by
  refine Function.Injective.of_comp_right ?_ hu
  rw [pointsMap_comp_comm B S hS w]
  exact hg.comp hh'

/-- Let `sq` present `h' : A' ⟶ T'` as the base change of `h : A ⟶ T` along `g : T' ⟶ T`, with
`h'` an isomorphism and `g` surjective and universally injective. Then `h` is universally
injective. -/
theorem universallyInjective_of_comm_of_isIso {h : A ⟶ T} {g : T' ⟶ T} {u : A' ⟶ A}
    {h' : A' ⟶ T'} (hgui : UniversallyInjective B S hS g) (hgs : IsSurjective B S hS g)
    (sq : IsPullback u h' h g) [IsIso h'] :
    UniversallyInjective B S hS h := by
  have hleft : IsPullback (inv h') (𝟙 T') h' (𝟙 T') :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have sqw : IsPullback (inv h' ≫ u) (𝟙 T') h g := by
    have := hleft.paste_horiz sq
    rwa [Category.id_comp] at this
  have hwsurj : Function.Surjective (pointsMap B S hS T' (inv h' ≫ u)) :=
    surjective_pointsMap_of_isPullback B S hS sqw.flip hgs
  intro Z hZ k
  have hsqQ : IsPullback (pullback.fst k h) (pullback.snd k h) k h :=
    IsPullback.of_hasPullback k h
  have hsqZ : IsPullback (pullback.fst k g) (pullback.snd k g) k ((inv h' ≫ u) ≫ h) := by
    rw [sqw.w, Category.id_comp]
    exact IsPullback.of_hasPullback k g
  have hr := IsPullback.of_right' hsqZ hsqQ
  refine injective_pointsMap_of_comm B S hS (h' := 𝟙 _) ?_
    (surjective_pointsMap_of_isPullback B S hS hr.flip hwsurj) (hgui Z hZ k) ?_
  · rw [Category.id_comp]
    exact hsqQ.lift_fst _ _ _
  · simpa using Function.injective_id

end Descent

/-! ### Descending an isomorphism -/

section Isomorphism

variable {A A' T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale morphism whose base change along a surjective, universally injective morphism is an
isomorphism is itself an isomorphism. -/
theorem isIso_of_isEtale_of_isPullback_of_isIso_of_universallyInjective
    (hA : IsAlgebraicSpace B S hS A) (hT : IsAlgebraicSpace B S hS T) {h : A ⟶ T} {g : T' ⟶ T}
    {u : A' ⟶ A} {h' : A' ⟶ T'}
    (hh : IsEtale B S hS h) (hgui : UniversallyInjective B S hS g)
    (hgs : IsSurjective B S hS g) (sq : IsPullback u h' h g) [IsIso h'] :
    IsIso h :=
  isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS hA hT h hh
    (universallyInjective_of_comm_of_isIso B S hS hgui hgs sq)
    (isSurjective_of_comm_of_surjective B S hS sq.w hgs
      (surjective_pointsMap_of_isIso B S hS (asIso h')))

end Isomorphism

/-! ### Descending a section of an étale morphism -/

section Sections

variable {T T' P P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `p : P ⟶ T` be étale, let `g : T' ⟶ T` be integral, universally injective and surjective,
and let `sq` present `p' : P' ⟶ T'` as the base change of `p` along `g`, with `q : P' ⟶ P` the
other projection. Every section `s` of `p'` is then the base change of a section `a` of `p`,
the compatibility being recorded as `g ≫ a = s ≫ q`. -/
theorem exists_section_of_isPullback_of_section (hT : IsAlgebraicSpace B S hS T)
    (hT' : IsAlgebraicSpace B S hS T') (hP : IsAlgebraicSpace B S hS P)
    (hP' : IsAlgebraicSpace B S hS P') {p : P ⟶ T} (hp : IsEtale B S hS p) {g : T' ⟶ T}
    (hint : IsIntegralHom B S hS g) (hgui : UniversallyInjective B S hS g)
    (hgs : IsSurjective B S hS g) {q : P' ⟶ P} {p' : P' ⟶ T'} (sq : IsPullback q p' p g)
    (s : T' ⟶ P') (hs : s ≫ p' = 𝟙 T') :
    ∃ a : T ⟶ P, a ≫ p = 𝟙 T ∧ g ≫ a = s ≫ q := by
  have hqh : IsHomeomorph (pointsMap B S hS P' q) :=
    isHomeomorph_pointsMap_of_universalHomeomorphism_of_isAlgebraicSpace B S hS hP
      (universalHomeomorphism_of_isPullback B S hS hT' hP hT g p
        (universalHomeomorphism_of_isIntegralHom_of_universallyInjective B S hS hT' hT hint
          hgui hgs) sq)
  have hp' : IsEtale B S hS p' := isEtale_of_isPullback_presheaf B S hS hP hT' hT sq hp
  have hsoi : IsOpenImmersion B S hS s :=
    isOpenImmersion_of_isEtale_of_section B S hS hP' hT' p' hp' s hs
  have _ : Mono s := mono_of_isOpenImmersion B S hS s hsoi
  have hΓ' : IsOpenSubspace B S hS (Subfunctor.range s) :=
    isOpenSubspace_subfunctorRange B S hS hT' hsoi
  set W : Set (points B S hS P) := pointsMap B S hS P' q ''
    Set.range (pointsMap B S hS (Subfunctor.range s).toFunctor (Subfunctor.range s).ι) with hW
  have hWopen : IsOpen W :=
    hqh.isOpenMap _ (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hΓ'.2)
  set Γ : Subfunctor P := openSubspaceOfPoints B S hS P W with hΓdef
  have hΓ : IsOpenSubspace B S hS Γ := isOpenSubspace_openSubspaceOfPoints B S hS hP W hWopen
  have hpre : Γ.preimage q = Subfunctor.range s := by
    rw [hΓdef, preimage_openSubspaceOfPoints, hW, Set.preimage_image_eq _ hqh.injective]
    exact (eq_openSubspaceOfPoints_range_pointsMap B S hS hP' _ hΓ').symm
  set α : (Subfunctor.range s).toFunctor ⟶ (Γ.preimage q).toFunctor :=
    Subfunctor.homOfLe hpre.ge with hαdef
  have hαι : α ≫ (Γ.preimage q).ι = (Subfunctor.range s).ι := Subfunctor.homOfLe_ι hpre.ge
  have hβι : Subfunctor.homOfLe hpre.le ≫ (Subfunctor.range s).ι = (Γ.preimage q).ι :=
    Subfunctor.homOfLe_ι hpre.le
  have _ : IsIso α := by
    refine ⟨Subfunctor.homOfLe hpre.le, ?_, ?_⟩
    · rw [← cancel_mono (Subfunctor.range s).ι, Category.assoc, hβι, hαι, Category.id_comp]
    · rw [← cancel_mono (Γ.preimage q).ι, Category.assoc, hαι, hβι, Category.id_comp]
  have hιfac : inv (Subfunctor.toRange s) ≫ s = (Subfunctor.range s).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι s).symm
  have hrange : (Subfunctor.range s).ι ≫ p' = inv (Subfunctor.toRange s) := by
    rw [← hιfac, Category.assoc, hs, Category.comp_id]
  have hαv : α ≫ ((Γ.preimage q).ι ≫ p') = inv (Subfunctor.toRange s) := by
    rw [← Category.assoc, hαι, hrange]
  have hsec : (Subfunctor.toRange s ≫ α) ≫ ((Γ.preimage q).ι ≫ p') = 𝟙 T' := by
    rw [Category.assoc, hαv, IsIso.hom_inv_id]
  have _ : IsIso ((Γ.preimage q).ι ≫ p') := by
    have _ : IsIso (α ≫ ((Γ.preimage q).ι ≫ p')) := hαv ▸ inferInstance
    exact IsIso.of_isIso_comp_left α _
  have sqOuter : IsPullback (Γ.fromPreimage q) ((Γ.preimage q).ι ≫ p') (Γ.ι ≫ p) g :=
    (Subfunctor.isPullback_preimage q Γ).paste_vert sq
  have _ : IsIso (Γ.ι ≫ p) :=
    isIso_of_isEtale_of_isPullback_of_isIso_of_universallyInjective B S hS hΓ.1 hT
      (isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hΓ.2) hp) hgui hgs sqOuter
  have hinvv : inv ((Γ.preimage q).ι ≫ p') = Subfunctor.toRange s ≫ α := by
    rw [← Category.comp_id (Subfunctor.toRange s ≫ α), ← IsIso.hom_inv_id
      ((Γ.preimage q).ι ≫ p'), ← Category.assoc, hsec, Category.id_comp]
  have hsq : inv ((Γ.preimage q).ι ≫ p') ≫ (Γ.preimage q).ι = s := by
    rw [hinvv, Category.assoc, hαι, Subfunctor.toRange_ι]
  refine ⟨inv (Γ.ι ≫ p) ≫ Γ.ι, by rw [Category.assoc]; exact IsIso.inv_hom_id _, ?_⟩
  have hg : inv ((Γ.preimage q).ι ≫ p') ≫ Γ.fromPreimage q ≫ (Γ.ι ≫ p) = g := by
    rw [sqOuter.w, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [← hg, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc,
    Subfunctor.fromPreimage_ι, ← Category.assoc, hsq]

end Sections

/-! ### Descending a morphism over the base -/

section Morphisms

variable {Y₀ T T' V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `v : V₀ ⟶ Y₀` be étale, let `t : T ⟶ Y₀` be arbitrary, and let `g : T' ⟶ T` be integral,
universally injective and surjective. Every morphism `d : T' ⟶ V₀` with `d ≫ v = g ≫ t` is
`g` followed by a morphism `a : T ⟶ V₀` over `Y₀`. -/
theorem exists_hom_of_section_descent (hY : IsAlgebraicSpace B S hS Y₀)
    (hT : IsAlgebraicSpace B S hS T) (hT' : IsAlgebraicSpace B S hS T')
    (hV : IsAlgebraicSpace B S hS V₀) {t : T ⟶ Y₀} {v : V₀ ⟶ Y₀} (hv : IsEtale B S hS v)
    {g : T' ⟶ T} (hint : IsIntegralHom B S hS g) (hgui : UniversallyInjective B S hS g)
    (hgs : IsSurjective B S hS g) (d : T' ⟶ V₀) (hd : d ≫ v = g ≫ t) :
    ∃ a : T ⟶ V₀, g ≫ a = d ∧ a ≫ v = t := by
  have hP : IsAlgebraicSpace B S hS (pullback t v) :=
    isAlgebraicSpace_pullback B S hS t v hT hV hY
  have hp : IsEtale B S hS (pullback.fst t v) :=
    isEtale_of_isPullback_presheaf B S hS hV hT hY (IsPullback.of_hasPullback t v).flip hv
  have hσ : pullback.lift g d hd.symm ≫ pullback.fst t v = 𝟙 T' ≫ g :=
    (pullback.lift_fst _ _ _).trans (Category.id_comp g).symm
  obtain ⟨a₀, ha₀, hcompat⟩ :=
    exists_section_of_isPullback_of_section B S hS hT hT' hP
      (isAlgebraicSpace_pullback B S hS (pullback.fst t v) g hP hT' hT) hp hint hgui hgs
      (IsPullback.of_hasPullback (pullback.fst t v) g)
      (pullback.lift (pullback.lift g d hd.symm) (𝟙 T') hσ) (pullback.lift_snd _ _ _)
  refine ⟨a₀ ≫ pullback.snd t v, ?_, ?_⟩
  · rw [← Category.assoc, hcompat, pullback.lift_fst, pullback.lift_snd]
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha₀, Category.id_comp]

end Morphisms

end AlgebraicGeometry.Space

end
