module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Size.AtlasOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# The five local criteria for an affine morphism of algebraic spaces

Stacks 03WG characterizes affineness of a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S` by five conditions: (1) representability with affine represented base changes;
(2) affineness in the sense of Stacks 03WF; (3) affineness of the base change along every étale
morphism from an affine object of the site; (4) affineness of the base change along one
surjective étale scheme chart of the target; and (5) affineness over the members of a Zariski
covering of the target. This file proves relative Tag 03JH for morphisms out of an algebraic
space with no containment hypothesis, the implication (5) ⇒ (2), and the equivalence of the five
conditions conditionally on effective descent of affine morphisms along surjective étale maps.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_of_isEmpty`: a scheme with empty carrier is contained
  in every big fppf site.
* `AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`
  and
  `AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`: relative
  Tag 03JH for a morphism out of an *algebraic space*, with no containment hypothesis.
* `AlgebraicGeometry.Space.presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace` and
  `AlgebraicGeometry.Space.presheaf_isAffineHom_of_etaleChart_of_isAlgebraicSpace`: the
  implications (2) ⇒ (1) and (4) ⇒ (1) of Stacks 03WG with no containment hypothesis.
* `AlgebraicGeometry.Space.isAffineHom_of_zariskiCover_isAffineHom`: the implication (5) ⇒ (2) of
  Stacks 03WG.
* `AlgebraicGeometry.Space.isAffineHom_tfae`: the five conditions of Stacks 03WG are equivalent,
  conditionally on `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` for the
  class of affine morphisms of schemes.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-! ### Schemes with empty carrier -/

/-- A scheme with empty carrier is contained in every big fppf site. -/
theorem BigFppfSite.contains_of_isEmpty (B : BigFppfSite.{u}) {Z : Scheme.{u}}
    (hZ : IsEmpty Z) : B.Contains Z := by
  refine lt_of_le_of_lt (Scheme.size_le_of_bounds le_rfl ?_ ?_) B.aleph0_lt_cutoff
  · have hsub : Subsingleton Z.affineOpens :=
      ⟨fun _ _ => Subtype.ext (TopologicalSpace.Opens.ext (by ext x; exact (hZ.false x).elim))⟩
    exact (le_one_iff_subsingleton.mpr hsub).trans one_le_aleph0
  · exact fun U => (le_one_iff_subsingleton.mpr inferInstance).trans one_le_aleph0

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

/-! ### Relative Tag 03JH with no containment hypothesis -/

/-- Reparametrizing the source of a pullback square by an isomorphism whose inverse composes with
the second projection to `q` yields a pullback square with first projection `e.inv ≫ fst`. -/
private theorem isPullback_of_iso_inv_comp {C : Type*} [Category C] {X Y Z P P' : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hpb : IsPullback fst snd f g)
    (e : P ≅ P') (q : P' ⟶ Y) (hq : e.inv ≫ snd = q) : IsPullback (e.inv ≫ fst) q f g :=
  hpb.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using hq) (by simp) (by simp)

/-- Let `π : F ⟶ yoneda.obj T` be a morphism from an algebraic space `F` to a representable, and
let `Q` be a property of morphisms of schemes that is Zariski local on the target. If every base
change of `π` along a morphism from an affine object of the site is represented by a morphism
satisfying `Q`, then `F` is represented by an object `Y` of the site over `T` whose structure
morphism satisfies `Q`. -/
theorem exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (π : F ⟶ yoneda.obj T)
    (hπ : HoldsOnAffineBaseChange B S hS Q π) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧ Q ((BigFppfOver.toScheme B S hS).map P) := by
  obtain ⟨U₀, a, haS, haE⟩ := hF.exists_atlas
  choose V u hu hurange hVaff using
    fun U => BigFppfOver.exists_affineOpen_restrict B S hS T U
  choose W p q hpb hWaff hQp using fun U => hπ (V U) (hVaff U) (yoneda.map (u U))
  refine exists_representing_over_of_openCover B S hS hQ hF.isSheaf π
    (V := V) (W := W) (u := u) (p := p) (q := q) hu ?_ hpb hQp ?_
  · intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨U, by rw [hurange U]; exact hU⟩
  · intro Z k hk hkcov
    have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj T).affineOpens :=
      ⟨⟨⊥, isAffineOpen_bot _⟩⟩
    have hμ : max #((BigFppfOver.toScheme B S hS).obj T).affineOpens
        (max (2 ^ #((BigFppfOver.toScheme B S hS).obj U₀ : Type u))
          (2 ^ ((BigFppfOver.toScheme B S hS).obj U₀).size)) < B.cutoff :=
      max_lt (((BigFppfOver.toScheme B S hS).obj T).mk_affineOpens_le_size.trans_lt
          T.left.property)
        (Scheme.max_two_pow_mk_two_pow_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit
          U₀.left.property)
    have := hk
    refine B.contains_of_openCover_of_size_le hμ (le_max_left _ _) k hkcov fun U => ?_
    exact le_max_of_le_right (size_le_of_isOpenImmersion_of_atlas B S hS haS haE
      (isOpenImmersion_of_isPullback_yoneda_map B S hS (hu U) (hpb U)))

/-- Let `π : F ⟶ G` be a morphism of algebraic spaces and let `Q` be a property of morphisms of
schemes that is Zariski local on the target. If every base change of `π` along a morphism from an
affine object of the site is represented by a morphism satisfying `Q`, then `π` is representable
and every base change of `π` along a morphism from a representable satisfies `Q`. -/
theorem presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {π : F ⟶ G}
    (hπ : HoldsOnAffineBaseChange B S hS Q π) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf π := by
  have := hQ
  have hRI : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun T g => ?_
  have hpbT : IsPullback (Limits.pullback.fst π g) (Limits.pullback.snd π g) π g :=
    IsPullback.of_hasPullback π g
  obtain ⟨Y, e, P, hP, hQP⟩ :=
    exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS hQ
      (isAlgebraicSpace_pullback B S hS π g hF (isAlgebraicSpace_yoneda B S hS T) hG)
      (Limits.pullback.snd π g) (hπ.of_isPullback hpbT)
  exact ⟨Y, e.inv ≫ Limits.pullback.fst π g, P,
    isPullback_of_iso_inv_comp hpbT e _ hP, hQP⟩

/-! ### Stacks 03WG -/

/-- An affine morphism of algebraic spaces over `S` in the sense of Stacks 03WF is representable,
and all of its represented base changes are affine morphisms of schemes. -/
theorem presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsAffineHom B S hS f) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f := by
  have h := presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS
    isZariskiLocalAtTarget_isAffineHom hX hY
    ((isAffineHom_iff_holdsOnAffineBaseChange f).1 hf)
  exact ⟨h.rep, h⟩

/-- Assume affine morphisms of schemes satisfy effective descent along surjective étale
morphisms. Let `f : X ⟶ Y` be a morphism of algebraic spaces and `g : yoneda.obj V ⟶ Y` a
surjective étale morphism such that the base change of `f` along `g` is affine. Then `f` is
representable, and all of its represented base changes are affine morphisms of schemes. -/
theorem presheaf_isAffineHom_of_etaleChart_of_isAlgebraicSpace
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hs : IsSurjective B S hS g) (he : IsEtale B S hS g)
    (h₄ : IsAffineHom B S hS (Limits.pullback.snd f g)) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_isAffineHom_of_surjectiveEtaleChart hdesc hX hY hs he
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY)
      (isAlgebraicSpace_yoneda B S hS V) h₄).2

/-- If a morphism `f` of algebraic spaces over `S` is affine over the members of some Zariski
covering of its target, then `f` is affine in the sense of Stacks 03WF. -/
theorem isAffineHom_of_zariskiCover_isAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h₅ : ∀ i, IsAffineHom B S hS (Limits.pullback.snd f (U i).ι)) :
    IsAffineHom B S hS f := by
  intro Z g
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  have hres : ∀ i, (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Limits.pullback.snd f (U i).ι) := fun i =>
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (isAlgebraicSpace_pullback B S hS f (U i).ι hX (hU.1 i).1 hY) (hU.1 i).1 (h₅ i)).2
  have key : ∀ i, ∃ (W : BigFppfOver B S hS) (p : W ⟶ (hU.1 i).2.rep.pullback g)
      (q : yoneda.obj W ⟶ Limits.pullback f g),
      IsPullback q (yoneda.map p) (Limits.pullback.snd f g)
        (yoneda.map ((hU.1 i).2.rep.snd g)) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map p) := by
    intro i
    have step := ((hres i).rep.isPullback ((hU.1 i).2.rep.fst g)).paste_horiz
      (IsPullback.of_hasPullback f (U i).ι)
    rw [((hU.1 i).2.rep.isPullback g).w] at step
    exact ⟨_, _, _, IsPullback.of_right' step (IsPullback.of_hasPullback f g),
      (hres i).property_snd _⟩
  choose W p q hpb hQp using key
  have hu : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map ((hU.1 i).2.rep.snd g)) :=
    fun i => (hU.1 i).2.property_snd g
  obtain ⟨σ, hσ⟩ := (isCompact_univ (X := (BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj Z))).elim_finite_subcover
    (fun i => Set.range ((BigFppfOver.toScheme B S hS).map ((hU.1 i).2.rep.snd g)))
    (fun i => by
      have := hu i
      exact ((BigFppfOver.toScheme B S hS).map
        ((hU.1 i).2.rep.snd g)).isOpenEmbedding.isOpen_range)
    fun y _ => Set.mem_iUnion.2 (exists_mem_range_snd_of_zariskiCover B S hS hU g y)
  have hσcov : ∀ y : (BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj Z), ∃ i : {i // i ∈ σ},
      y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hU.1 i.1).2.rep.snd g)) := by
    intro y
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (hσ (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, hy⟩
  have hcontains : ∀ (Z' : Scheme.{u}) (k : ∀ i : {i // i ∈ σ},
      (BigFppfOver.toScheme B S hS).obj (W i.1) ⟶ Z'),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z', ∃ i, z ∈ Set.range (k i)) → B.Contains Z' := by
    intro Z' k hk hkcov
    rcases isEmpty_or_nonempty {i // i ∈ σ} with hemp | hne
    · exact B.contains_of_isEmpty ⟨fun z => hemp.false (hkcov z).choose⟩
    · have := hk
      exact B.contains_of_openCover
        (lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) B.aleph0_lt_cutoff_cof.le)
        k hkcov fun i => (W i.1).left.property
  obtain ⟨Y₀, e, P, hP, hQP⟩ := exists_representing_over_of_openCover B S hS
    isZariskiLocalAtTarget_isAffineHom
    (BigFppfOver.isSheaf_pullback_yoneda_obj f g hX.isSheaf hY.isSheaf)
    (Limits.pullback.snd f g)
    (V := fun i : {i // i ∈ σ} => (hU.1 i.1).2.rep.pullback g) (W := fun i => W i.1)
    (u := fun i => (hU.1 i.1).2.rep.snd g) (p := fun i => p i.1) (q := fun i => q i.1)
    (fun i => hu i.1) hσcov (fun i => hpb i.1) (fun i => hQp i.1) hcontains
  have := hQP
  exact ⟨⟨Y₀, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map P)⟩,
    e.inv ≫ Limits.pullback.fst f g, P,
    isPullback_of_iso_inv_comp (IsPullback.of_hasPullback f g) e _ hP⟩

/-- Assume affine morphisms of schemes satisfy effective descent along surjective étale
morphisms. For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the following five
conditions are equivalent: `f` is relatively representable and all of its represented base
changes are affine morphisms of schemes; `f` is affine in the sense of Stacks 03WF; the base
change of `f` along every étale morphism from an affine object of the site is represented by an
affine object of the site; there is a surjective étale scheme chart of the target along which the
base change of `f` is affine; and there is a Zariski covering of the target over whose members
the base changes of `f` are affine. -/
theorem isAffineHom_tfae {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})) :
    List.TFAE [
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f),
      IsAffineHom B S hS f,
      (∀ (V : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ Y),
        IsEtale B S hS g →
          ∃ (W : BigAffineFppf B S hS)
            (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ X)
            (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
              (BigAffineFppf.inclusion B S hS).obj V),
            IsPullback p (yoneda.map q) f g),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧
        IsEtale B S hS g ∧
        IsAffineHom B S hS (Limits.pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsAffineHom B S hS (Limits.pullback.snd f (U i).ι))] := by
  tfae_have 1 → 2 := fun h => isAffineHom_of_presheaf h.2
  tfae_have 2 → 3 := fun h V g _ => h V g
  tfae_have 3 → 4 := fun h => exists_etaleChart_isAffineHom_of_isEtale_affine hX hY h
  tfae_have 4 → 1 := fun ⟨_, _, hs, he, h₄⟩ =>
    presheaf_isAffineHom_of_etaleChart_of_isAlgebraicSpace B S hS hdesc hX hY hs he h₄
  tfae_have 2 → 5 := fun h => IsAffineHom.exists_zariskiCover hY h
  tfae_have 5 → 2 := fun ⟨_, _, hU, h₅⟩ =>
    isAffineHom_of_zariskiCover_isAffineHom B S hS hX hY hU h₅
  tfae_finish

end Space

end AlgebraicGeometry

end
