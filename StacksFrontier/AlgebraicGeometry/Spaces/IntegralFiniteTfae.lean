module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete

/-!
# Integral and finite morphisms of algebraic spaces: the local criteria of Stacks 03ZQ

Stacks 03ZQ asserts, for each of the two properties of Stacks 03ZP, the equivalence of four
conditions on a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`: (1) `f` is
relatively representable and every represented base change of it is an integral, respectively
finite, morphism of schemes; (2) `f` is integral, respectively finite, in the sense of Stacks
03ZP, which is the affine-base-change pattern
`AlgebraicGeometry.Space.HoldsOnAffineBaseChange`; (3) the property holds after one surjective
étale morphism from a representable presheaf onto the target; (4) it holds on the base changes
of `f` along the members of some Zariski covering of the target.

## Main results

* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_zariskiCover`: condition (4) implies
  condition (2) for an arbitrary `Q` which is Zariski local at the target and whose source is
  affine over an affine target.
* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_etaleChart`: condition (3) implies
  condition (2) for such a `Q`, given effective descent for `Q` along the surjective étale
  morphisms of the site.
* `AlgebraicGeometry.Space.holdsOnAffineBaseChange_iff_presheaf`,
  `AlgebraicGeometry.Space.holdsOnAffineBaseChange_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.holdsOnAffineBaseChange_iff_exists_zariskiCover`: the three
  equivalences for an arbitrary such `Q`.
* `AlgebraicGeometry.Space.isIntegralHom_iff_representable`,
  `AlgebraicGeometry.Space.isFinite_iff_representable`,
  `AlgebraicGeometry.Space.isIntegralHom_iff_zariskiCover` and
  `AlgebraicGeometry.Space.isFinite_iff_zariskiCover`: the four instances of those equivalences
  at Mathlib's `AlgebraicGeometry.IsIntegralHom` and `AlgebraicGeometry.IsFinite` which need no
  descent hypothesis.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (4) implies condition (2) -/

/-- Let `Q` be a property of scheme morphisms which is Zariski local at the target and whose source
is affine over an affine target. If `Q` holds on the affine base changes of the base change of `f`
along each member of some Zariski covering of the target, then it holds on the affine base changes
of `f` itself. -/
theorem HoldsOnAffineBaseChange.of_zariskiCover
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h₄ : ∀ i, HoldsOnAffineBaseChange B S hS Q (Limits.pullback.snd f (U i).ι)) :
    HoldsOnAffineBaseChange B S hS Q f := by
  intro T hT g
  have hres : ∀ i, (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS)).presheaf (Limits.pullback.snd f (U i).ι) := fun i =>
    presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS hQ
      (isAlgebraicSpace_pullback B S hS f (U i).ι hX (hU.1 i).1 hY) (hU.1 i).1 (h₄ i)
  have key : ∀ i, ∃ (W : BigFppfOver B S hS) (p : W ⟶ (hU.1 i).2.rep.pullback g)
      (q : yoneda.obj W ⟶ Limits.pullback f g),
      IsPullback q (yoneda.map p) (Limits.pullback.snd f g)
        (yoneda.map ((hU.1 i).2.rep.snd g)) ∧
      Q ((BigFppfOver.toScheme B S hS).map p) := by
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
  obtain ⟨σ, hσ⟩ := (isCompact_univ (X := (BigFppfOver.toScheme B S hS).obj T)).elim_finite_subcover
    (fun i => Set.range ((BigFppfOver.toScheme B S hS).map ((hU.1 i).2.rep.snd g)))
    (fun i => by
      have := hu i
      exact ((BigFppfOver.toScheme B S hS).map
        ((hU.1 i).2.rep.snd g)).isOpenEmbedding.isOpen_range)
    fun y _ => Set.mem_iUnion.2 (exists_mem_range_snd_of_zariskiCover B S hS hU g y)
  have hσcov : ∀ y : (BigFppfOver.toScheme B S hS).obj T, ∃ i : {i // i ∈ σ},
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
  obtain ⟨Y₀, e, P, hP, hQP⟩ := exists_representing_over_of_openCover B S hS hQ
    (BigFppfOver.isSheaf_pullback_yoneda_obj f g hX.isSheaf hY.isSheaf)
    (Limits.pullback.snd f g)
    (V := fun i : {i // i ∈ σ} => (hU.1 i.1).2.rep.pullback g) (W := fun i => W i.1)
    (u := fun i => (hU.1 i.1).2.rep.snd g) (p := fun i => p i.1) (q := fun i => q i.1)
    (fun i => hu i.1) hσcov (fun i => hpb i.1) (fun i => hQp i.1) hcontains
  exact ⟨Y₀, P, e.inv ≫ Limits.pullback.fst f g,
    (IsPullback.of_hasPullback f g).of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simpa using hP) (by simp) (by simp),
    hQaff _ hQP hT, hQP⟩

/-! ### Condition (3) implies condition (2) -/

/-- Let `Q` be a property of scheme morphisms which is Zariski local at the target, whose source is
affine over an affine target, and which descends effectively along the surjective étale morphisms
of the site. If `Q` holds on the affine base changes of the base change of `f` along one
surjective étale morphism `g` from a representable presheaf onto the target, then it holds on the
affine base changes of `f` itself. -/
theorem HoldsOnAffineBaseChange.of_etaleChart
    {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso] (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (h₃ : HoldsOnAffineBaseChange B S hS Q (Limits.pullback.snd f g)) :
    HoldsOnAffineBaseChange B S hS Q f :=
  HoldsOnAffineBaseChange.of_presheaf hQaff
    (presheaf_of_surjectiveEtaleChart hdesc hX.isSheaf hY.isSheaf hs he
      (presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS hQ
        (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY)
        (isAlgebraicSpace_yoneda B S hS V) h₃))

/-! ### The three equivalences for an arbitrary property -/

/-- Let `Q` be a property of scheme morphisms which is Zariski local at the target and whose source
is affine over an affine target. A morphism of algebraic spaces over `S` has `Q` on its affine
base changes exactly when it is relatively representable and all of its represented base changes
have `Q`. -/
theorem holdsOnAffineBaseChange_iff_presheaf
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    HoldsOnAffineBaseChange B S hS Q f ↔
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf f) :=
  ⟨fun hf =>
    have h := presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS hQ hX hY hf
    ⟨h.rep, h⟩,
    fun hf => HoldsOnAffineBaseChange.of_presheaf hQaff hf.2⟩

/-- Let `Q` be a property of scheme morphisms which is Zariski local at the target, whose source is
affine over an affine target, and which descends effectively along the surjective étale morphisms
of the site. A morphism of algebraic spaces over `S` has `Q` on its affine base changes exactly
when it does so after base change along some surjective étale morphism from a representable
presheaf onto its target. -/
theorem holdsOnAffineBaseChange_iff_exists_etaleChart
    {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso] (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    HoldsOnAffineBaseChange B S hS Q f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
          HoldsOnAffineBaseChange B S hS Q (Limits.pullback.snd f g) :=
  ⟨fun hf => hf.exists_etaleChart hY,
    fun ⟨_, _, hs, he, h₃⟩ =>
      HoldsOnAffineBaseChange.of_etaleChart B S hS hQ hQaff hdesc hX hY hs he h₃⟩

/-- Let `Q` be a property of scheme morphisms which is Zariski local at the target and whose source
is affine over an affine target. A morphism of algebraic spaces over `S` has `Q` on its affine
base changes exactly when there is a Zariski covering of its target over whose members its base
changes do. -/
theorem holdsOnAffineBaseChange_iff_exists_zariskiCover
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    HoldsOnAffineBaseChange B S hS Q f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
          ∀ i, HoldsOnAffineBaseChange B S hS Q (Limits.pullback.snd f (U i).ι) :=
  ⟨fun hf => hf.exists_zariskiCover hY,
    fun ⟨_, _, hU, h₄⟩ =>
      HoldsOnAffineBaseChange.of_zariskiCover B S hS hQ hQaff hX hY hU h₄⟩

/-! ### Stacks 03ZQ for integral and for finite morphisms -/

/-- A morphism of algebraic spaces over `S` is integral in the sense of Stacks 03ZP exactly when it
is relatively representable and all of its represented base changes are integral morphisms of
schemes. -/
@[stacks 03ZQ "integral: conditions (1) and (2)",
  stacks 03ZO "integral case: the affine test criterion for a representable morphism"]
theorem isIntegralHom_iff_representable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsIntegralHom B S hS f ↔
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f) :=
  (isIntegralHom_iff_holdsOnAffineBaseChange f).trans
    (holdsOnAffineBaseChange_iff_presheaf B S hS isZariskiLocalAtTarget_isIntegralHom
      (fun p hp hZ => isAffine_of_isIntegralHom p hp hZ) hX hY f)

/-- A morphism of algebraic spaces over `S` is finite in the sense of Stacks 03ZP exactly when it
is relatively representable and all of its represented base changes are finite morphisms of
schemes. -/
@[stacks 03ZQ "finite: conditions (1) and (2)",
  stacks 03ZO "finite case: the affine test criterion for a representable morphism"]
theorem isFinite_iff_representable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsFinite B S hS f ↔
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f) :=
  (isFinite_iff_holdsOnAffineBaseChange f).trans
    (holdsOnAffineBaseChange_iff_presheaf B S hS isZariskiLocalAtTarget_isFinite
      (fun p hp hZ => isAffine_of_isFinite p hp hZ) hX hY f)

/-- A morphism of algebraic spaces over `S` is integral in the sense of Stacks 03ZP exactly when
there is a Zariski covering of its target over whose members its base changes are integral. -/
@[stacks 03ZQ "integral: conditions (2) and (4)"]
theorem isIntegralHom_iff_zariskiCover {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsIntegralHom B S hS f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
          ∀ i, IsIntegralHom B S hS (Limits.pullback.snd f (U i).ι) :=
  holdsOnAffineBaseChange_iff_exists_zariskiCover B S hS
    isZariskiLocalAtTarget_isIntegralHom
    (fun p hp hZ => isAffine_of_isIntegralHom p hp hZ) hX hY f

/-- A morphism of algebraic spaces over `S` is finite in the sense of Stacks 03ZP exactly when
there is a Zariski covering of its target over whose members its base changes are finite. -/
@[stacks 03ZQ "finite: conditions (2) and (4)"]
theorem isFinite_iff_zariskiCover {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsFinite B S hS f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
          ∀ i, IsFinite B S hS (Limits.pullback.snd f (U i).ι) := by
  simp only [isFinite_iff_holdsOnAffineBaseChange]
  exact holdsOnAffineBaseChange_iff_exists_zariskiCover B S hS isZariskiLocalAtTarget_isFinite
    (fun p hp hZ => isAffine_of_isFinite p hp hZ) hX hY f

end AlgebraicGeometry.Space

end
