module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Unramified monomorphisms of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. [Stacks Project, Tag 05W6]
lists four equivalent conditions on `f`:

1. `f` is unramified and a monomorphism,
2. `f` is unramified and universally injective,
3. `f` is locally of finite type and a monomorphism,
4. `f` is universally injective, locally of finite type and formally unramified,

and asserts that such an `f` is moreover representable, separated and locally quasi-finite.

This file proves the equivalence of conditions (1) and (3) in full, and the implications from
condition (1) to conditions (2) and (4).

## Main results

* `AlgebraicGeometry.Space.universallyInjective_of_mono`: a monomorphism of algebraic spaces is
  universally injective.
* `AlgebraicGeometry.Space.formallyUnramifiedCharts_of_mono`: the scheme morphism in every
  commuting square of étale scheme charts of a monomorphism of algebraic spaces is formally
  unramified.
* `AlgebraicGeometry.Space.isUnramified_of_isLocallyOfFiniteType_of_mono`: a monomorphism of
  algebraic spaces which is locally of finite type is unramified.
* `AlgebraicGeometry.Space.isUnramified_mono_iff_isLocallyOfFiniteType_mono`: the equivalence
  of conditions (1) and (3) of [Stacks Project, Tag 05W6].
* `AlgebraicGeometry.Space.isUnramified_universallyInjective_of_isUnramified_mono` is the
  implication from condition (1) to condition (2) and, in the same namespace,
  `universallyInjective_isLocallyOfFiniteType_formallyUnramified_of_isUnramified_mono` is the
  implication from condition (1) to condition (4).
* `AlgebraicGeometry.isOpenImmersion_diagonal_of_etale_section`: a morphism of schemes `U ⟶ V`
  whose self-fibre-product embeds compatibly into one with an étale projection admitting a
  section has open-immersion diagonal.
* `CategoryTheory.Limits.isPullback_id_of_comp_mono`: if `m` is a monomorphism and
  `e ≫ m = g`, the square with sides `𝟙`, `e`, `g` and `m` is cartesian.

## Implementation notes

The source proves (3) ⇒ (4) ⇒ (2) ⇒ (1) ⇒ (3), with the step (2) ⇒ (1) going through
[Stacks Project, Tag 05W1] and [Stacks Project, Tag 040X]. This file proves (1) ⟺ (3) directly
and reaches conditions (2) and (4) from condition (1) only; the converse implications and the
representability, separatedness and local quasi-finiteness clauses are not proved here.

The implication (3) ⇒ (1) is the diagonal argument of [Stacks Project, Tag 05W1] carried out on
a commuting square of étale charts `a : h_U ⟶ X`, `b : h_V ⟶ Y` with scheme morphism
`h : U ⟶ V`: the diagonal of `h` is a base change of the diagonal of the self-fibre-product
`U ×_X U`, which is a section of an étale morphism and hence an open immersion. No algebraicity
of `X` or `Y`, and no étaleness of `b`, is used.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Limits

/-- **A morphism factoring through a monomorphism is a base change of that factorisation.**
If `m` is a monomorphism and `g = e ≫ m`, then the square with sides `𝟙`, `e`, `g` and `m` is
cartesian. -/
theorem isPullback_id_of_comp_mono {C : Type u} [Category.{v} C] {A W R : C}
    (e : A ⟶ W) (m : W ⟶ R) [Mono m] {g : A ⟶ R} (hg : e ≫ m = g) :
    IsPullback (𝟙 A) e g m := by
  have hcomm : CommSq (𝟙 A) e g m := ⟨by rw [Category.id_comp, hg]⟩
  refine IsPullback.of_isLimit' hcomm (PullbackCone.IsLimit.mk hcomm.w
    (fun c => c.fst) (fun c => by simp) (fun c => ?_) (fun c k hk₁ hk₂ => by simpa using hk₁))
  apply (cancel_mono m).1
  rw [Category.assoc, hg, c.condition]

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **The diagonal of a morphism of schemes which embeds into an étale self-fibre-product is an
open immersion.** The data is a cartesian square exhibiting `W` as `U ×_V U`, a morphism
`p₂ : R ⟶ U` which is étale, a section `d` of it, and a morphism `m : W ⟶ R` compatible with
the projections `p₁, p₂` and with a section `δ` of the two projections of `W`. -/
theorem isOpenImmersion_diagonal_of_etale_section {U V R W : Scheme.{u}}
    (hs : U ⟶ V) {π₁ π₂ : W ⟶ U} (hpb : IsPullback π₁ π₂ hs hs)
    {p₁ p₂ : R ⟶ U} (hp₂ : Etale p₂)
    {d : U ⟶ R} (hd₂ : d ≫ p₂ = 𝟙 U)
    {m : W ⟶ R} (hm₁ : m ≫ p₁ = π₁) (hm₂ : m ≫ p₂ = π₂)
    {δ : U ⟶ W} (hδ₁ : δ ≫ π₁ = 𝟙 U) (hδ₂ : δ ≫ π₂ = 𝟙 U) (hδm : δ ≫ m = d) :
    IsOpenImmersion (pullback.diagonal hs) := by
  have _ : Etale p₂ := hp₂
  have _ : Mono m := ⟨fun u₁ u₂ heq => hpb.hom_ext
    (by rw [← hm₁, ← Category.assoc, heq, Category.assoc])
    (by rw [← hm₂, ← Category.assoc, heq, Category.assoc])⟩
  have _ : Etale (d ≫ p₂) := by rw [hd₂]; infer_instance
  have _ : Etale d := Etale.of_comp d p₂
  have _ : IsSplitMono d := IsSplitMono.mk' ⟨p₂, hd₂⟩
  have _ : IsOpenImmersion δ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
      (isPullback_id_of_comp_mono δ m hδm) (IsOpenImmersion.of_flat_of_mono d)
  have hdiag : δ ≫ hpb.isoPullback.hom = pullback.diagonal hs := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hpb.isoPullback_hom_fst, hδ₁, pullback.diagonal_fst]
    · rw [Category.assoc, hpb.isoPullback_hom_snd, hδ₂, pullback.diagonal_snd]
  rw [← hdiag]
  infer_instance

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Monomorphisms are universally injective -/

/-- **A monomorphism of algebraic spaces over `S` is universally injective.** -/
theorem universallyInjective_of_mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : Mono f) : UniversallyInjective B S hS f := by
  intro Y' _ g
  have _ : Mono f := hf
  exact pointsMap_injective_of_mono B S hS (pullback.fst g f)

/-! ### Monomorphisms are formally unramified on charts -/

/-- **The scheme morphism of every commuting square of étale charts of a monomorphism of
algebraic spaces over `S` is formally unramified.** -/
@[ega "IV 17.1.3" "clause (i), special case"]
theorem formallyUnramifiedCharts_of_mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : Mono f) :
    HoldsOnEveryEtaleChart B S hS
      (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) f := by
  intro U V a b h ha hb hsq
  have hmono : Mono f := hf
  have hid : yoneda.map (𝟙 U) ≫ a = yoneda.map (𝟙 U) ≫ a := rfl
  have hkey : yoneda.map (pullback.fst h h) ≫ a = yoneda.map (pullback.snd h h) ≫ a := by
    apply (cancel_mono f).1
    rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc, ← Category.assoc,
      ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  have hd₁ : ha.rep.lift' (𝟙 U) (𝟙 U) hid ≫ ha.rep.fst' a = 𝟙 U := by simp
  have hd₂ : ha.rep.lift' (𝟙 U) (𝟙 U) hid ≫ ha.rep.snd a = 𝟙 U := by simp
  have hm₁ : ha.rep.lift' (pullback.fst h h) (pullback.snd h h) hkey ≫ ha.rep.fst' a =
      pullback.fst h h := by simp
  have hm₂ : ha.rep.lift' (pullback.fst h h) (pullback.snd h h) hkey ≫ ha.rep.snd a =
      pullback.snd h h := by simp
  have hδ₁ : (pullback.lift (𝟙 U) (𝟙 U) rfl : U ⟶ pullback h h) ≫ pullback.fst h h = 𝟙 U :=
    pullback.lift_fst _ _ _
  have hδ₂ : (pullback.lift (𝟙 U) (𝟙 U) rfl : U ⟶ pullback h h) ≫ pullback.snd h h = 𝟙 U :=
    pullback.lift_snd _ _ _
  have hδm : (pullback.lift (𝟙 U) (𝟙 U) rfl : U ⟶ pullback h h) ≫
      ha.rep.lift' (pullback.fst h h) (pullback.snd h h) hkey =
      ha.rep.lift' (𝟙 U) (𝟙 U) hid := by
    refine ha.rep.hom_ext' ?_ ?_
    · rw [Category.assoc, hm₁, hδ₁, hd₁]
    · rw [Category.assoc, hm₂, hδ₂, hd₂]
  have hpb : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst h h))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd h h))
      ((BigFppfOver.toScheme B S hS).map h) ((BigFppfOver.toScheme B S hS).map h) :=
    (IsPullback.of_hasPullback h h).map (BigFppfOver.toScheme B S hS)
  have hOI : _root_.AlgebraicGeometry.IsOpenImmersion
      (pullback.diagonal ((BigFppfOver.toScheme B S hS).map h)) :=
    isOpenImmersion_diagonal_of_etale_section
      (p₁ := (BigFppfOver.toScheme B S hS).map (ha.rep.fst' a))
      (d := (BigFppfOver.toScheme B S hS).map (ha.rep.lift' (𝟙 U) (𝟙 U) hid))
      (m := (BigFppfOver.toScheme B S hS).map
        (ha.rep.lift' (pullback.fst h h) (pullback.snd h h) hkey))
      (δ := (BigFppfOver.toScheme B S hS).map (pullback.lift (𝟙 U) (𝟙 U) rfl))
      _ hpb (ha.property_snd a)
      (by rw [← CategoryTheory.Functor.map_comp, hd₂, CategoryTheory.Functor.map_id])
      (by rw [← CategoryTheory.Functor.map_comp, hm₁])
      (by rw [← CategoryTheory.Functor.map_comp, hm₂])
      (by rw [← CategoryTheory.Functor.map_comp, hδ₁, CategoryTheory.Functor.map_id])
      (by rw [← CategoryTheory.Functor.map_comp, hδ₂, CategoryTheory.Functor.map_id])
      (by rw [← CategoryTheory.Functor.map_comp, hδm])
  infer_instance

/-- **A monomorphism of algebraic spaces over `S` which is locally of finite type is
unramified.** -/
theorem isUnramified_of_isLocallyOfFiniteType_of_mono
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hft : IsLocallyOfFiniteType B S hS f) (hf : Mono f) : IsUnramified B S hS f :=
  (isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts B S hS f).mpr
    ⟨hft, formallyUnramifiedCharts_of_mono B S hS f hf⟩

/-! ### The equivalent characterisations of an unramified monomorphism -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05W6, conditions (1) and (3).** A morphism of algebraic spaces over `S` is
unramified and a monomorphism if and only if it is locally of finite type and a monomorphism. -/
@[stacks 05W6 "conditions (1) and (3)"]
theorem isUnramified_mono_iff_isLocallyOfFiniteType_mono
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (IsUnramified B S hS f ∧ Mono f) ↔ (IsLocallyOfFiniteType B S hS f ∧ Mono f) :=
  ⟨fun ⟨hu, hm⟩ => ⟨isLocallyOfFiniteType_of_isUnramified B S hS hu, hm⟩,
    fun ⟨hft, hm⟩ => ⟨isUnramified_of_isLocallyOfFiniteType_of_mono B S hS f hft hm, hm⟩⟩

/-- **Stacks 05W6, condition (1) implies condition (2).** An unramified monomorphism of
algebraic spaces over `S` is unramified and universally injective. -/
theorem isUnramified_universallyInjective_of_isUnramified_mono
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h : IsUnramified B S hS f ∧ Mono f) :
    IsUnramified B S hS f ∧ UniversallyInjective B S hS f :=
  ⟨h.1, universallyInjective_of_mono B S hS f h.2⟩

/-- **Stacks 05W6, condition (1) implies condition (4).** An unramified monomorphism of
algebraic spaces over `S` is universally injective, locally of finite type and formally
unramified. -/
theorem universallyInjective_isLocallyOfFiniteType_formallyUnramified_of_isUnramified_mono
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h : IsUnramified B S hS f ∧ Mono f) :
    UniversallyInjective B S hS f ∧ IsLocallyOfFiniteType B S hS f ∧
      FormallyUnramified (B := B) (S := S) (hS := hS) f :=
  ⟨universallyInjective_of_mono B S hS f h.2,
    isLocallyOfFiniteType_of_isUnramified B S hS h.1,
    have _ : Mono f := h.2
    formallyUnramified_of_mono f⟩

end Space

end AlgebraicGeometry

end
