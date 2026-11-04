module

import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.SmallExtensionLift
public import StacksFrontier.Deformation.Terminal

/-!
# Vanishing of relative infinitesimal automorphisms (Stacks 06JZ)

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), and let
`x' ⟶ x` be a morphism of `𝓕` lying over a surjection `B → A`. If the group of
infinitesimal automorphisms at a pushforward `x₀` of `x` to the special fibre is
trivial, then so is the group `Inf(x'/x)` of infinitesimal automorphisms of `x'`
over `x`.

The route is not the source's. Stacks deduces this from Tag 06JY, the statement that
`Inf(x'/x)` is a torsor under the infinitesimal automorphisms of the special fibre tensored
with the kernel; but only transitivity of that action is used here, and transitivity is
available directly. Two elementary reductions — the case of an isomorphism in the base and
the stability of vanishing under composition — reduce the surjective case to the case of a
small extension along the factorization of Tag 06GE. The case of a small extension rests on
the identification `B ×_A B ≅ B ×_k k[ε]`, proved here from the one-dimensionality of the
kernel of a small extension; applying (RS) to that square is what produces an infinitesimal
automorphism at the special fibre out of one of `x'` over `x`, and applying (RS) to the same
square read with the dual numbers as one coordinate is what makes that automorphism detect
the original one.

## Main results

* `Deformation.relativeInfinitesimalAutomorphisms_eq_bot_of_isIso`: vanishing over an
  isomorphism of the base.
* `Deformation.relativeInfinitesimalAutomorphisms_eq_bot_comp`: vanishing is stable
  under composition.
* `Deformation.relativeInfinitesimalAutomorphisms_eq_bot_of_isSmallExtension`: the case of a
  small extension.
* `Deformation.relativeInfinitesimalAutomorphisms_eq_bot`: **Stacks 06JZ**, the case of an
  arbitrary surjection.

## References

* [Stacks Project, Tag 06JZ](https://stacks.math.columbia.edu/tag/06JZ)
-/

@[expose] public section

namespace Deformation

open CategoryTheory CategoryTheory.Limits IsLocalRing

/-! ### Elementary reductions -/

section
open CategoryTheory
universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C] {p : F ⥤ C}

/-- Relative infinitesimal automorphisms along an isomorphism of the base are trivial:
the morphism itself is then an isomorphism, hence a monomorphism. -/
theorem relativeInfinitesimalAutomorphisms_eq_bot_of_isIso
    (hp : IsCofiberedInGroupoids p) {A' A : C} {x' : p.Fiber A'} {x : p.Fiber A}
    (g : A' ⟶ A) (f : x'.1 ⟶ x.1) (hf : p.IsHomLift g f) [IsIso g] :
    relativeInfinitesimalAutomorphisms hp g f hf = ⊥ := by
  let := hf
  have hmap : p.map f = eqToHom (IsHomLift.domain_eq p g f) ≫ g ≫
      eqToHom (IsHomLift.codomain_eq p g f).symm := IsHomLift.fac' p g f
  have : IsIso (p.map f) := by rw [hmap]; infer_instance
  have : IsIso f := isIso_of_isCofiberedInGroupoids_of_map_isIso hp f
  refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  rw [mem_relativeInfinitesimalAutomorphisms_iff] at ha
  exact Aut.ext (Functor.Fiber.hom_ext ((cancel_mono f).1 (ha.trans (Category.id_comp f).symm)))

/-- Vanishing of relative infinitesimal automorphisms is stable under composition:
an automorphism fixing the composite pushes forward to one fixing the second
morphism, and the pushforward records exactly the obstruction. -/
theorem relativeInfinitesimalAutomorphisms_eq_bot_comp
    (hp : IsCofiberedInGroupoids p) {A'' A' A : C}
    {x'' : p.Fiber A''} {x' : p.Fiber A'} {x : p.Fiber A}
    (g' : A'' ⟶ A') (f' : x''.1 ⟶ x'.1) (hf' : p.IsHomLift g' f')
    (g : A' ⟶ A) (f : x'.1 ⟶ x.1) (hf : p.IsHomLift g f)
    (hcomp : p.IsHomLift (g' ≫ g) (f' ≫ f))
    (h' : relativeInfinitesimalAutomorphisms hp g' f' hf' = ⊥)
    (h : relativeInfinitesimalAutomorphisms hp g f hf = ⊥) :
    relativeInfinitesimalAutomorphisms hp (g' ≫ g) (f' ≫ f) hcomp = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  rw [mem_relativeInfinitesimalAutomorphisms_iff] at ha
  let := hf
  let := hf'
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g' f' hf'
  set b := pushforwardAutomorphism hp g' f' hf' a
  have hsq : a.hom.val ≫ f' = f' ≫ b.hom.val :=
    hom_comp_eq_comp_pushforwardEndomorphism hp g' f' hf' a
  let : p.IsHomLift (𝟙 A') b.hom.val := b.hom.2
  let : p.IsHomLift g (b.hom.val ≫ f) := IsHomLift.comp_lift_id_left p g f b.hom.val
  have hkey : b.hom.val ≫ f = f := by
    refine Functor.IsStronglyCocartesian.ext p g' f' g ?_
    rw [← Category.assoc, ← hsq, Category.assoc, ha]
  have hb1 : b = 1 := (Subgroup.eq_bot_iff_forall _).1 h b
    ((mem_relativeInfinitesimalAutomorphisms_iff hp g f hf b).2 hkey)
  have ha' : a ∈ relativeInfinitesimalAutomorphisms hp g' f' hf' := by
    rw [mem_relativeInfinitesimalAutomorphisms_iff, hsq, hb1]
    show f' ≫ 𝟙 x'.1 = f'
    simp
  exact (Subgroup.eq_bot_iff_forall _).1 h' a ha'

end


/-! ### The dual-number coordinate of a small extension -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The kernel of a small extension is annihilated by the maximal ideal of its source:
a length-one kernel is a simple module, so its annihilator is the maximal ideal. -/
private theorem kernel_annihilated
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : B ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom g.hom.toRingHom))
    (b : B) (hb : b ∈ maximalIdeal B) (j : RingHom.ker g.hom.toRingHom) :
    b • j = 0 := by
  obtain ⟨_, _, _, _, _, hlen⟩ := hsmall
  have hsimp : IsSimpleModule B (RingHom.ker g.hom.toRingHom) :=
    Module.length_eq_one_iff.mp hlen
  have hAnn : (Module.annihilator B (RingHom.ker g.hom.toRingHom)).IsMaximal :=
    IsSimpleModule.annihilator_isMaximal
  exact (Module.mem_annihilator.mp (by rwa [IsLocalRing.eq_maximalIdeal hAnn])) j

/-- A one-dimensional coordinate on the kernel of a small extension, twisted by a chosen
identification of a residue-field object with `k`: an additive bijection `ker g ≃+ k` for
which multiplication by `b` acts through the value of the canonical map `B ⟶ A₀`. This is
the datum that presents `B ×_A B` as `B ×_k k[ε]`. -/
private theorem exists_kernelCoordinate
    {B A A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : B ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom g.hom.toRingHom))
    (ρ : B ⟶ A₀) (hA₀ : maximalIdeal A₀ = ⊥) (i₀ : A₀ ≃ₐ[Λ] k) :
    ∃ ψ : RingHom.ker g.hom.toRingHom ≃+ k,
      ∀ (b : B) (j : RingHom.ker g.hom.toRingHom),
        ψ (b • j) = i₀ (ρ.hom b) * ψ j := by
  classical
  have hsmall' := hsmall
  obtain ⟨_, _, _, _, _, hlen₀⟩ := hsmall'
  set I : Ideal B := RingHom.ker g.hom.toRingHom
  have hlen : Module.length B I = 1 := hlen₀
  have hsimp : IsSimpleModule B I := Module.length_eq_one_iff.mp hlen
  let σ : B →ₐ[Λ] k := i₀.toAlgHom.comp ρ.hom
  have hσzero : ∀ b : B, σ b = 0 ↔ b ∈ maximalIdeal B := by
    intro b
    rw [mem_maximalIdeal, mem_nonunits_iff,
      ← ArtinianLocalAlgCat.hom_eq_zero_iff_not_isUnit B A₀ hA₀ ρ b]
    show i₀ (ρ.hom b) = 0 ↔ _
    exact ⟨fun h => i₀.injective (by simpa using h), fun h => by simp [h]⟩
  have hσsurj : Function.Surjective σ := by
    intro c
    obtain ⟨a, rfl⟩ := i₀.surjective c
    obtain ⟨b, rfl⟩ := ArtinianLocalAlgCat.hom_surjective B A₀ hA₀ ρ a
    exact ⟨b, rfl⟩
  have hkerσ : RingHom.ker σ.toRingHom = maximalIdeal B := Ideal.ext hσzero
  have hInz : I ≠ ⊥ := by
    intro h
    rw [h] at hlen
    simp at hlen
  obtain ⟨x, hxI, hx0⟩ := Submodule.ne_bot_iff I |>.mp hInz
  set t : I := ⟨x, hxI⟩ with htdef
  have ht0 : t ≠ 0 := fun h => hx0 (by simpa [htdef] using congrArg Subtype.val h)
  set L : B →ₗ[B] I := LinearMap.toSpanSingleton B I t
  have hLsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range]
    exact IsSimpleModule.span_singleton_eq_top B ht0
  have hLker : LinearMap.ker L = maximalIdeal B := by
    ext b
    refine ⟨fun hb => ?_, fun hb => kernel_annihilated g hsmall b hb t⟩
    by_contra hbm
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hbm
    exact ht0 (hbm.smul_eq_zero.mp (show b • t = 0 from hb))
  set e₂ : (B ⧸ maximalIdeal B) ≃ₗ[B] I :=
    (Submodule.quotEquivOfEq (maximalIdeal B) (LinearMap.ker L) hLker.symm).trans
      (L.quotKerEquivOfSurjective hLsurj)
  set e₁ : (B ⧸ maximalIdeal B) ≃+* k :=
    (Ideal.quotEquivOfEq hkerσ).symm.trans
      (RingHom.quotientKerEquivOfSurjective (f := σ.toRingHom) hσsurj)
  have he₁_mk : ∀ b : B, e₁ (Ideal.Quotient.mk (maximalIdeal B) b) = σ b := fun _ => rfl
  refine ⟨e₂.symm.toAddEquiv.trans e₁.toAddEquiv, ?_⟩
  intro b j
  have hquot : ∀ (q : B ⧸ maximalIdeal B),
      e₁ (b • q) = σ b * e₁ q := by
    intro q
    induction q using Quotient.inductionOn with
    | h c =>
        have : (b • (Ideal.Quotient.mk (maximalIdeal B) c)) =
            Ideal.Quotient.mk (maximalIdeal B) (b * c) := rfl
        rw [show (Quotient.mk _ c : B ⧸ maximalIdeal B) =
          Ideal.Quotient.mk (maximalIdeal B) c from rfl, this,
          he₁_mk, he₁_mk, map_mul]
  show e₁ (e₂.symm (b • j)) = σ b * e₁ (e₂.symm j)
  rw [LinearEquiv.map_smul, hquot]

/-- A bijective morphism of `𝒞_Λ` is an isomorphism. -/
private noncomputable def isoOfBijective
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (hf : Function.Bijective f.hom) : A ≅ B := by
  let e : A ≃ₐ[Λ] B := AlgEquiv.ofBijective f.hom hf
  refine ⟨f, ⟨e.symm.toAlgHom, IsLocalHom.of_surjective e.symm.toRingEquiv.toRingHom
      e.symm.surjective, ?_⟩, ?_, ?_⟩
  · intro b
    have hc := f.residue_comm (e.symm b)
    rw [show f.hom (e.symm b) = b from e.apply_symm_apply b] at hc
    exact hc.symm
  · exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext e.symm_apply_apply)
  · exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext e.apply_symm_apply)

/-- The isomorphism attached to a bijective morphism has that morphism as its forward
direction. -/
private lemma isoOfBijective_hom
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (hf : Function.Bijective f.hom) : (isoOfBijective f hf).hom = f := rfl

/-- A categorical pullback square in `𝒞_Λ` over a cospan with a surjective leg is a
pullback on elements: the two projections are jointly injective, and every compatible pair
of elements is attained. -/
private theorem isPullback_elementwise
    {A₁ A₂ A Y : ArtinianLocalAlgCat.{u, v, w} Λ k} (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hs : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
    {pr₁ : Y ⟶ A₁} {pr₂ : Y ⟶ A₂} (hPB : IsPullback pr₁ pr₂ f₁ f₂) :
    (∀ t s : Y, pr₁.hom t = pr₁.hom s → pr₂.hom t = pr₂.hom s → t = s) ∧
      (∀ (a₁ : A₁) (a₂ : A₂), f₁.hom a₁ = f₂.hom a₂ →
        ∃ t : Y, pr₁.hom t = a₁ ∧ pr₂.hom t = a₂) := by
  classical
  have hP : IsPullback (ArtinianLocalAlgCat.pullbackFst_of_surjective f₁ f₂ hs)
      (ArtinianLocalAlgCat.pullbackSnd_of_surjective f₁ f₂ hs) f₁ f₂ :=
    ArtinianLocalAlgCat.isPullback_of_surjective f₁ f₂ hs
  set ι : Y ≅ ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs :=
    hPB.isoIsPullback A₁ A₂ hP
  have hfst : ∀ z : ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs,
      (ArtinianLocalAlgCat.pullbackFst_of_surjective f₁ f₂ hs).hom z = z.val.1 := by
    intro z
    rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
    rfl
  have hsnd : ∀ z : ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs,
      (ArtinianLocalAlgCat.pullbackSnd_of_surjective f₁ f₂ hs).hom z = z.val.2 := by
    intro z
    rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
    rfl
  have hval1 : ∀ t : Y, (ι.hom.hom t).val.1 = pr₁.hom t := by
    intro t
    rw [← hfst]
    exact congrArg (fun q : Y ⟶ A₁ => q.hom t) (hPB.isoIsPullback_hom_fst A₁ A₂ hP)
  have hval2 : ∀ t : Y, (ι.hom.hom t).val.2 = pr₂.hom t := by
    intro t
    rw [← hsnd]
    exact congrArg (fun q : Y ⟶ A₂ => q.hom t) (hPB.isoIsPullback_hom_snd A₁ A₂ hP)
  have hinvhom : ∀ t : Y, ι.inv.hom (ι.hom.hom t) = t := fun t =>
    congrArg (fun q : Y ⟶ Y => q.hom t) ι.hom_inv_id
  have hhominv : ∀ q : ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs,
      ι.hom.hom (ι.inv.hom q) = q := fun q =>
    congrArg (fun r : ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs ⟶
      ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs => r.hom q) ι.inv_hom_id
  refine ⟨fun t s h₁ h₂ => ?_, fun a₁ a₂ hcompat => ?_⟩
  · have hz : ι.hom.hom t = ι.hom.hom s := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · rw [hval1, hval1, h₁]
      · rw [hval2, hval2, h₂]
    rw [← hinvhom t, ← hinvhom s, hz]
  · refine ⟨ι.inv.hom ⟨(a₁, a₂), hcompat⟩, ?_, ?_⟩
    · exact (hval1 _).symm.trans
        (congrArg (fun z : ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs => z.val.1)
          (hhominv ⟨(a₁, a₂), hcompat⟩))
    · exact (hval2 _).symm.trans
        (congrArg (fun z : ArtinianLocalAlgCat.pullbackObj_of_surjective f₁ f₂ hs => z.val.2)
          (hhominv ⟨(a₁, a₂), hcompat⟩))

/-- The canonical map to a residue-field object kills the maximal ideal. -/
private theorem hom_eq_zero_of_mem_maximalIdeal
    {B A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (ρ : B ⟶ A₀)
    (hA₀ : maximalIdeal A₀ = ⊥) {b : B} (hb : b ∈ maximalIdeal B) : ρ.hom b = 0 := by
  rw [ArtinianLocalAlgCat.hom_eq_zero_iff_not_isUnit B A₀ hA₀ ρ b]
  rwa [mem_maximalIdeal, mem_nonunits_iff] at hb

/-- **The dual-number presentation of a small extension.** For a small extension
`g : B ⟶ A` and a fibre square `Y = B ×_A B`, the difference of the two projections
is a coordinate identifying `Y` with `B ×_k k[ε]`: there is a morphism `γ : Y ⟶ Aε` making
`Y` the fibre product of `B` and `Aε` over the residue-field object, and `γ` restricted to
the diagonal is the constant inclusion. -/
private theorem exists_dualNumberPullback
    {B A A₀ Aε Y : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : B ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom g.hom.toRingHom))
    {i : A₀ ⟶ Aε} {e : Aε ⟶ A₀} (hpair : IsCanonicalDualNumberPair i e)
    (ρ : B ⟶ A₀) {pr₁ pr₂ : Y ⟶ B} (hPB : IsPullback pr₁ pr₂ g g) :
    ∃ γ : Y ⟶ Aε, IsPullback γ pr₁ e ρ ∧
      ∀ {T : ArtinianLocalAlgCat.{u, v, w} Λ k} (u : T ⟶ Y),
        u ≫ pr₁ = u ≫ pr₂ → u ≫ γ = u ≫ pr₁ ≫ ρ ≫ i := by
  classical
  obtain ⟨i₀, iε, hi1, hi2, -⟩ := hpair
  have hA₀ : maximalIdeal A₀ = ⊥ := by
    rw [← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact MulEquiv.isField (Field.toIsField k) i₀.toMulEquiv
  have hgsurj : Function.Surjective g.hom := by
    obtain ⟨-, -, -, -, hs, -⟩ := hsmall
    exact hs
  have hesurj : Function.Surjective e.hom :=
    ArtinianLocalAlgCat.hom_surjective Aε A₀ hA₀ e
  obtain ⟨ψ, hψ⟩ := exists_kernelCoordinate g hsmall ρ hA₀ i₀
  obtain ⟨hYinj, hYsurj⟩ := isPullback_elementwise g g (Or.inl hgsurj) hPB
  have hdiff : ∀ t : Y, pr₂.hom t - pr₁.hom t ∈ RingHom.ker g.hom.toRingHom := by
    intro t
    have hw := congrArg (fun q : Y ⟶ A => q.hom t) hPB.w
    have hw' : g.hom (pr₁.hom t) = g.hom (pr₂.hom t) := by simpa using hw
    show g.hom (pr₂.hom t - pr₁.hom t) = 0
    rw [map_sub, ← hw', sub_self]
  set d : Y → RingHom.ker g.hom.toRingHom := fun t => ⟨pr₂.hom t - pr₁.hom t, hdiff t⟩
    with hddef
  have hσpr : ∀ t : Y, i₀ (ρ.hom (pr₂.hom t)) = i₀ (ρ.hom (pr₁.hom t)) := by
    intro t
    have hmem : pr₂.hom t - pr₁.hom t ∈ maximalIdeal B :=
      Deformation.ArtinianLocalAlgCat.ker_le_maximalIdeal g (hdiff t)
    have h0 : ρ.hom (pr₂.hom t - pr₁.hom t) = 0 :=
      hom_eq_zero_of_mem_maximalIdeal ρ hA₀ hmem
    rw [map_sub] at h0
    rw [sub_eq_zero.mp h0]
  have hd0 : ∀ t : Y, pr₂.hom t = pr₁.hom t → d t = 0 := fun t h =>
    Subtype.ext (by change pr₂.hom t - pr₁.hom t = 0; rw [h, sub_self])
  let δ : Y →ₐ[Λ] DualNumber k :=
    { toFun := fun t => (i₀ (ρ.hom (pr₁.hom t)), ψ (d t))
      map_one' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · show i₀ (ρ.hom (pr₁.hom 1)) = (1 : k)
          rw [map_one, map_one, map_one]
        · show ψ (d 1) = (0 : k)
          rw [hd0 1 (by simp), map_zero]
      map_mul' := by
        intro t s
        refine TrivSqZeroExt.ext ?_ ?_
        · show i₀ (ρ.hom (pr₁.hom (t * s))) =
            i₀ (ρ.hom (pr₁.hom t)) * i₀ (ρ.hom (pr₁.hom s))
          rw [map_mul, map_mul, map_mul]
        · show ψ (d (t * s)) =
            (i₀ (ρ.hom (pr₁.hom t)), ψ (d t)).fst •
                (i₀ (ρ.hom (pr₁.hom s)), ψ (d s)).snd +
              MulOpposite.op (i₀ (ρ.hom (pr₁.hom s)), ψ (d s)).fst •
                (i₀ (ρ.hom (pr₁.hom t)), ψ (d t)).snd
          have hkey : d (t * s) = pr₁.hom t • d s + pr₂.hom s • d t := by
            apply Subtype.ext
            show pr₂.hom (t * s) - pr₁.hom (t * s) =
              pr₁.hom t * (pr₂.hom s - pr₁.hom s) + pr₂.hom s * (pr₂.hom t - pr₁.hom t)
            rw [map_mul, map_mul]
            ring
          rw [hkey, map_add, hψ, hψ, hσpr s]
          simp only [smul_eq_mul, op_smul_eq_mul]
          ring
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · show i₀ (ρ.hom (pr₁.hom 0)) = (0 : k)
          rw [map_zero, map_zero, map_zero]
        · show ψ (d 0) = (0 : k)
          rw [hd0 0 (by simp), map_zero]
      map_add' := by
        intro t s
        refine TrivSqZeroExt.ext ?_ ?_
        · show i₀ (ρ.hom (pr₁.hom (t + s))) =
            i₀ (ρ.hom (pr₁.hom t)) + i₀ (ρ.hom (pr₁.hom s))
          rw [map_add, map_add, map_add]
        · show ψ (d (t + s)) = ψ (d t) + ψ (d s)
          have hadd : d (t + s) = d t + d s := by
            apply Subtype.ext
            show pr₂.hom (t + s) - pr₁.hom (t + s) =
              (pr₂.hom t - pr₁.hom t) + (pr₂.hom s - pr₁.hom s)
            rw [map_add, map_add]
            ring
          rw [hadd, map_add]
      commutes' := by
        intro r
        refine TrivSqZeroExt.ext ?_ ?_
        · show i₀ (ρ.hom (pr₁.hom (algebraMap Λ Y r))) =
            (algebraMap Λ (DualNumber k) r).fst
          rw [AlgHom.commutes, AlgHom.commutes, AlgEquiv.commutes,
            TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl]
        · show ψ (d (algebraMap Λ Y r)) = (algebraMap Λ (DualNumber k) r).snd
          rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl]
          rw [hd0 _ (by rw [AlgHom.commutes, AlgHom.commutes]), map_zero] }
  have hδfst : ∀ t : Y, (δ t).fst = i₀ (ρ.hom (pr₁.hom t)) := fun _ => rfl
  have hδsnd : ∀ t : Y, (δ t).snd = ψ (d t) := fun _ => rfl
  have hfstHom : ∀ z : Aε, i₀ (e.hom z) = (iε z).fst := by
    intro z
    exact congrArg (fun q : Aε →ₐ[Λ] k => q z) hi2
  have hinlHom : ∀ a : A₀, iε (i.hom a) = TrivSqZeroExt.inl (i₀ a) := by
    intro a
    exact congrArg (fun q : A₀ →ₐ[Λ] DualNumber k => q a) hi1
  have hγcomp : ∀ t : Y, e.hom (iε.symm (δ t)) = ρ.hom (pr₁.hom t) := by
    intro t
    apply i₀.injective
    rw [hfstHom, iε.apply_symm_apply, hδfst]
  let γ : Y ⟶ Aε :=
    { hom := iε.symm.toAlgHom.comp δ
      isLocal := by
        constructor
        intro t ht
        by_contra hnu
        have htm : ¬ IsUnit (pr₁.hom t) := by
          intro hu
          exact hnu (pr₁.isLocal.map_nonunit _ hu)
        have h0 : ρ.hom (pr₁.hom t) = 0 :=
          hom_eq_zero_of_mem_maximalIdeal ρ hA₀
            (by rw [mem_maximalIdeal, mem_nonunits_iff]; exact htm)
        have hunit : IsUnit (δ t) := by
          have h' : IsUnit (iε.symm (δ t)) := ht
          have := h'.map iε.toAlgHom
          rwa [show iε.toAlgHom (iε.symm (δ t)) = δ t from iε.apply_symm_apply (δ t)] at this
        have hfst : IsUnit ((δ t).fst) := hunit.map (TrivSqZeroExt.fstHom Λ k k)
        rw [hδfst, h0, map_zero] at hfst
        exact not_isUnit_zero hfst
      residue_comm := by
        intro t
        show Aε.residueEquiv (residue Aε (iε.symm (δ t))) = Y.residueEquiv (residue Y t)
        rw [← e.residue_comm (iε.symm (δ t)), hγcomp t]
        exact (pr₁ ≫ ρ).residue_comm t }
  have hγhom : ∀ t : Y, γ.hom t = iε.symm (δ t) := fun _ => rfl
  have hcomm : γ ≫ e = pr₁ ≫ ρ := by
    apply ArtinianLocalAlgCat.hom_ext
    refine AlgHom.ext fun t => ?_
    exact hγcomp t
  have hs' : Function.Surjective e.hom ∨ Function.Surjective ρ.hom := Or.inl hesurj
  have hPconc : IsPullback (ArtinianLocalAlgCat.pullbackFst_of_surjective e ρ hs')
      (ArtinianLocalAlgCat.pullbackSnd_of_surjective e ρ hs') e ρ :=
    ArtinianLocalAlgCat.isPullback_of_surjective e ρ hs'
  obtain ⟨hPinj, -⟩ := isPullback_elementwise e ρ hs' hPconc
  set Φ : Y ⟶ ArtinianLocalAlgCat.pullbackObj_of_surjective e ρ hs' :=
    hPconc.lift γ pr₁ hcomm with hΦdef
  have hΦ1 : Φ ≫ ArtinianLocalAlgCat.pullbackFst_of_surjective e ρ hs' = γ :=
    hPconc.lift_fst γ pr₁ hcomm
  have hΦ2 : Φ ≫ ArtinianLocalAlgCat.pullbackSnd_of_surjective e ρ hs' = pr₁ :=
    hPconc.lift_snd γ pr₁ hcomm
  have hΦ1' : ∀ t : Y,
      (ArtinianLocalAlgCat.pullbackFst_of_surjective e ρ hs').hom (Φ.hom t) = γ.hom t :=
    fun t => congrArg (fun q : Y ⟶ Aε => q.hom t) hΦ1
  have hΦ2' : ∀ t : Y,
      (ArtinianLocalAlgCat.pullbackSnd_of_surjective e ρ hs').hom (Φ.hom t) = pr₁.hom t :=
    fun t => congrArg (fun q : Y ⟶ B => q.hom t) hΦ2
  have hbij : Function.Bijective Φ.hom := by
    constructor
    · intro t s hts
      have hγts : γ.hom t = γ.hom s := by rw [← hΦ1' t, ← hΦ1' s, hts]
      have h1 : pr₁.hom t = pr₁.hom s := by rw [← hΦ2' t, ← hΦ2' s, hts]
      have hδts : δ t = δ s := by
        have := congrArg (fun z : Aε => iε z) hγts
        rwa [hγhom, hγhom, iε.apply_symm_apply, iε.apply_symm_apply] at this
      have hdts : d t = d s := by
        apply ψ.injective
        rw [← hδsnd, ← hδsnd, hδts]
      have h2 : pr₂.hom t = pr₂.hom s := by
        have hval := congrArg Subtype.val hdts
        change pr₂.hom t - pr₁.hom t = pr₂.hom s - pr₁.hom s at hval
        rw [h1] at hval
        exact sub_left_injective hval
      exact hYinj t s h1 h2
    · intro z
      set zε : Aε := (ArtinianLocalAlgCat.pullbackFst_of_surjective e ρ hs').hom z with hzε
      set b : B := (ArtinianLocalAlgCat.pullbackSnd_of_surjective e ρ hs').hom z with hb
      have hzb : e.hom zε = ρ.hom b :=
        congrArg
          (fun q : ArtinianLocalAlgCat.pullbackObj_of_surjective e ρ hs' ⟶ A₀ => q.hom z)
          hPconc.w
      set c : RingHom.ker g.hom.toRingHom := ψ.symm ((iε zε).snd) with hc
      have hgc : g.hom (b + c.val) = g.hom b := by
        have : g.hom c.val = 0 := c.2
        rw [map_add, this, add_zero]
      obtain ⟨t, ht1, ht2⟩ := hYsurj b (b + c.val) hgc.symm
      have hdt : d t = c := by
        apply Subtype.ext
        show pr₂.hom t - pr₁.hom t = c.val
        rw [ht1, ht2]
        ring
      have hδt : δ t = iε zε := by
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [hδfst, ht1, ← hfstHom, hzb]
        · rw [hδsnd, hdt, hc, ψ.apply_symm_apply]
      have hγt : γ.hom t = zε := by
        rw [hγhom, hδt, iε.symm_apply_apply]
      refine ⟨t, hPinj _ _ ?_ ?_⟩
      · rw [hΦ1' t, hγt]
      · rw [hΦ2' t, ht1]
  refine ⟨γ, ?_, ?_⟩
  · refine hPconc.of_iso' (isoOfBijective Φ hbij) (Iso.refl Aε) (Iso.refl B)
      (Iso.refl A₀) ?_ ?_ ?_ ?_
    · rw [isoOfBijective_hom]
      simpa using hΦ1
    · rw [isoOfBijective_hom]
      simpa using hΦ2
    · simp
    · simp
  · intro T u hu
    apply ArtinianLocalAlgCat.hom_ext
    refine AlgHom.ext fun x => ?_
    have hd0' : d (u.hom x) = 0 := hd0 _ (congrArg (fun q : T ⟶ B => q.hom x) hu).symm
    show γ.hom (u.hom x) = i.hom (ρ.hom (pr₁.hom (u.hom x)))
    apply iε.injective
    rw [hγhom, iε.apply_symm_apply, hinlHom]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hδfst, TrivSqZeroExt.fst_inl]
    · rw [hδsnd, hd0', map_zero, TrivSqZeroExt.snd_inl]

end

/-! ### The case of a small extension -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

variable {F : Type u₁} [Category.{v₁} F]

/-- An object of `F`, read as an object of the fibre over its own image. Stated as an
`abbrev` so that it reduces at `reducible` transparency: the fibre of a functor is a plain
`def`, and both the fibre category instance and the unifier need the comparison to be
cheap at every call site below. -/
private abbrev fiberOfSelf (q : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (X : F) :
    q.Fiber (q.obj X) := ⟨X, rfl⟩

variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- **Vanishing over a small extension, for arrows whose base morphisms are their own
images.** This is the shape to which the statement of Tag 06JZ reduces, and the one in
which the (RS) fibre squares and their dual-number coordinate can be written without any
transport. -/
private theorem relativeInfinitesimalAutomorphisms_eq_bot_of_isSmallExtension_aux
    (hrs : SatisfiesRS p) {X' X X₀ Xε : F}
    (f : X' ⟶ X) (f₀ : X ⟶ X₀) (fi : X₀ ⟶ Xε)
    (e : p.obj Xε ⟶ p.obj X₀)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (p.map f).hom.toRingHom))
    (hpair : IsCanonicalDualNumberPair (p.map fi) e)
    (htriv : infinitesimalAutomorphisms (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
      hrs.1 (p.map fi) e hpair fi (IsHomLift.map p fi) = ⊥) :
    relativeInfinitesimalAutomorphisms (x' := fiberOfSelf p X') (x := fiberOfSelf p X)
      hrs.1 (p.map f) f (IsHomLift.map p f) = ⊥ := by
  classical
  have hgsurj : Function.Surjective (p.map f).hom := by
    obtain ⟨-, -, -, -, hs, -⟩ := hsmall
    exact hs
  have hA₀ : maximalIdeal (p.obj X₀) = ⊥ :=
    maximalIdeal_eq_bot_of_isCanonicalDualNumberPair hpair
  have hesurj : Function.Surjective e.hom :=
    ArtinianLocalAlgCat.hom_surjective (p.obj Xε) (p.obj X₀) hA₀ e
  obtain ⟨c, ⟨hc⟩, ⟨hcp⟩⟩ := hrs.2 f f hgsurj
  have hPB : IsPullback (p.map c.fst) (p.map c.snd) (p.map f) (p.map f) :=
    IsPullback.of_isLimit hcp
  obtain ⟨γ, hγPB, hγdiag⟩ :=
    exists_dualNumberPullback (p.map f) hsmall hpair (p.map (f ≫ f₀)) hPB
  have hdiagcond : (𝟙 X') ≫ f = (𝟙 X') ≫ f := rfl
  have hδ1 : PullbackCone.IsLimit.lift hc (𝟙 X') (𝟙 X') hdiagcond ≫ c.fst = 𝟙 X' :=
    PullbackCone.IsLimit.lift_fst hc (𝟙 X') (𝟙 X') hdiagcond
  have hδ2 : PullbackCone.IsLimit.lift hc (𝟙 X') (𝟙 X') hdiagcond ≫ c.snd = 𝟙 X' :=
    PullbackCone.IsLimit.lift_snd hc (𝟙 X') (𝟙 X') hdiagcond
  set δ : X' ⟶ c.pt := PullbackCone.IsLimit.lift hc (𝟙 X') (𝟙 X') hdiagcond with hδdef
  have hΔ1 : p.map δ ≫ p.map c.fst = 𝟙 (p.obj X') := by
    rw [← p.map_comp, hδ1, p.map_id]
  have hΔ2 : p.map δ ≫ p.map c.snd = 𝟙 (p.obj X') := by
    rw [← p.map_comp, hδ2, p.map_id]
  have hdiag : p.map (f ≫ f₀) ≫ p.map fi = p.map δ ≫ γ := by
    rw [hγdiag (p.map δ) (hΔ1.trans hΔ2.symm), reassoc_of% hΔ1]
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1 (p.map δ) δ
    (IsHomLift.map p δ)
  have hqlift : p.IsHomLift γ
      (Functor.IsStronglyCocartesian.map p (p.map δ) δ hdiag ((f ≫ f₀) ≫ fi)) :=
    Functor.IsStronglyCocartesian.map_isHomLift p (p.map δ) δ hdiag ((f ≫ f₀) ≫ fi)
  have hδq : δ ≫ Functor.IsStronglyCocartesian.map p (p.map δ) δ hdiag ((f ≫ f₀) ≫ fi)
      = (f ≫ f₀) ≫ fi :=
    Functor.IsStronglyCocartesian.fac p (p.map δ) δ hdiag ((f ≫ f₀) ≫ fi)
  set q : c.pt ⟶ Xε :=
    Functor.IsStronglyCocartesian.map p (p.map δ) δ hdiag ((f ≫ f₀) ≫ fi) with hqdef
  have := hqlift
  have hpq : p.map q = γ := (IsHomLift.eq_of_isHomLift p γ q).symm
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1 γ q hqlift
  have hcomm₂ : p.map c.fst ≫ p.map (f ≫ f₀) = γ ≫ e := hγPB.w.symm
  have hhlift : p.IsHomLift e
      (Functor.IsStronglyCocartesian.map p γ q hcomm₂ (c.fst ≫ f ≫ f₀)) :=
    Functor.IsStronglyCocartesian.map_isHomLift p γ q hcomm₂ (c.fst ≫ f ≫ f₀)
  have hqh : q ≫ Functor.IsStronglyCocartesian.map p γ q hcomm₂ (c.fst ≫ f ≫ f₀)
      = c.fst ≫ f ≫ f₀ :=
    Functor.IsStronglyCocartesian.fac p γ q hcomm₂ (c.fst ≫ f ≫ f₀)
  set h : Xε ⟶ X₀ :=
    Functor.IsStronglyCocartesian.map p γ q hcomm₂ (c.fst ≫ f ≫ f₀) with hhdef
  have := hhlift
  have hpeh : p.map h = e := (IsHomLift.eq_of_isHomLift p e h).symm
  have hfih : fi ≫ h = 𝟙 X₀ := by
    have hl1 : p.IsHomLift (𝟙 (p.obj X₀)) (fi ≫ h) := by
      rw [← hpair.split]
      infer_instance
    have hl2 : p.IsHomLift (𝟙 (p.obj X₀)) (𝟙 X₀) := IsHomLift.id rfl
    have := hl1
    have := hl2
    have := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1
      (p.map (f ≫ f₀)) (f ≫ f₀) (IsHomLift.map p (f ≫ f₀))
    refine Functor.IsStronglyCocartesian.ext p (p.map (f ≫ f₀)) (f ≫ f₀)
      (𝟙 (p.obj X₀)) ?_
    rw [Category.comp_id, ← Category.assoc, ← hδq, Category.assoc, hqh, reassoc_of% hδ1]
  have hret : h = (canonicalRetraction (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
      hrs.1 (p.map fi) e hpair.split fi (IsHomLift.map p fi)).1 := by
    obtain ⟨r, hr, hruniq⟩ :=
      existsUnique_retraction (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
        hrs.1 (p.map fi) e hpair fi (IsHomLift.map p fi)
    rw [hruniq h hfih, hruniq _
      (canonicalRetraction (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
        hrs.1 (p.map fi) e hpair.split fi (IsHomLift.map p fi)).2.2]
  have hPB₂ : IsPullback (p.map c.fst) (p.map q) (p.map (f ≫ f₀)) (p.map h) := by
    rw [hpq, hpeh]
    exact hγPB.flip
  have hhsurj : Function.Surjective (p.map h).hom := by rw [hpeh]; exact hesurj
  have hc₂plim : IsLimit ((PullbackCone.mk c.fst q hqh.symm).map p) := by
    refine IsLimit.ofIsoLimit hPB₂.isLimit (PullbackCone.ext (Iso.refl _) ?_ ?_)
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
  obtain ⟨hc₂⟩ := isLimit_of_map_isLimit hrs (f ≫ f₀) h
    (PullbackCone.mk c.fst q hqh.symm) hhsurj ⟨hc₂plim⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  replace ha : a.hom.val ≫ f = f :=
    (mem_relativeInfinitesimalAutomorphisms_iff
      (x' := fiberOfSelf p X') (x := fiberOfSelf p X)
      hrs.1 (p.map f) f (IsHomLift.map p f) a).mp ha
  have hcancel : a.hom.val ≫ a.inv.val = 𝟙 X' :=
    congrArg (fun t : fiberOfSelf p X' ⟶ fiberOfSelf p X' => t.val) a.hom_inv_id
  have hcancel' : a.inv.val ≫ a.hom.val = 𝟙 X' :=
    congrArg (fun t : fiberOfSelf p X' ⟶ fiberOfSelf p X' => t.val) a.inv_hom_id
  have hainv : a.inv.val ≫ f = f := by
    rw [← ha, reassoc_of% hcancel', ha]
  have := a.hom.2
  have := a.inv.2
  have hamap : p.map a.hom.val = 𝟙 (p.obj X') :=
    (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj X')) a.hom.val).symm
  have hainvmap : p.map a.inv.val = 𝟙 (p.obj X') :=
    (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj X')) a.inv.val).symm
  -- an endomorphism `s` of `X'` over `f` and the identity induces an endomorphism of `c.pt`
  -- fixing the first projection and acting by `s` on the second, again over the identity
  have hlift : ∀ s : X' ⟶ X', s ≫ f = f → p.map s = 𝟙 (p.obj X') →
      ∃ φ : c.pt ⟶ c.pt, φ ≫ c.fst = c.fst ∧ φ ≫ c.snd = c.snd ≫ s ∧
        p.map φ = 𝟙 (p.obj c.pt) := by
    intro s hs hps
    have hcond : c.fst ≫ f = (c.snd ≫ s) ≫ f := by
      rw [Category.assoc, hs]; exact c.condition
    obtain ⟨φ, h1, h2⟩ : ∃ φ : c.pt ⟶ c.pt, φ ≫ c.fst = c.fst ∧ φ ≫ c.snd = c.snd ≫ s :=
      ⟨_, PullbackCone.IsLimit.lift_fst hc c.fst (c.snd ≫ s) hcond,
        PullbackCone.IsLimit.lift_snd hc c.fst (c.snd ≫ s) hcond⟩
    refine ⟨φ, h1, h2, PullbackCone.IsLimit.hom_ext hcp ?_ ?_⟩
    · change p.map φ ≫ p.map c.fst = 𝟙 _ ≫ p.map c.fst
      rw [← p.map_comp, h1, Category.id_comp]
    · change p.map φ ≫ p.map c.snd = 𝟙 _ ≫ p.map c.snd
      rw [← p.map_comp, h2, p.map_comp, hps, Category.comp_id, Category.id_comp]
  obtain ⟨φ, hφ1, hφ2, hφmap⟩ := hlift _ ha hamap
  obtain ⟨φ', hφ'1, hφ'2, hφ'map⟩ := hlift _ hainv hainvmap
  have hinv1 : φ ≫ φ' = 𝟙 c.pt := by
    refine PullbackCone.IsLimit.hom_ext hc ?_ ?_
    · rw [Category.assoc, hφ'1, hφ1, Category.id_comp]
    · rw [Category.assoc, hφ'2, reassoc_of% hφ2, hcancel, Category.comp_id, Category.id_comp]
  have hinv2 : φ' ≫ φ = 𝟙 c.pt := by
    refine PullbackCone.IsLimit.hom_ext hc ?_ ?_
    · rw [Category.assoc, hφ1, hφ'1, Category.id_comp]
    · rw [Category.assoc, hφ2, reassoc_of% hφ'2, hcancel', Category.comp_id, Category.id_comp]
  have hφlift : p.IsHomLift (𝟙 (p.obj c.pt)) φ := by
    rw [← hφmap]; exact IsHomLift.map p φ
  have hφ'lift : p.IsHomLift (𝟙 (p.obj c.pt)) φ' := by
    rw [← hφ'map]; exact IsHomLift.map p φ'
  set Φ : Aut (fiberOfSelf p c.pt) :=
    { hom := ⟨φ, hφlift⟩
      inv := ⟨φ', hφ'lift⟩
      hom_inv_id := Subtype.ext hinv1
      inv_hom_id := Subtype.ext hinv2 } with hΦdef
  have hpush : φ ≫ q = q ≫ (pushforwardAutomorphism (x := fiberOfSelf p Xε)
      hrs.1 γ q hqlift Φ).hom.val :=
    hom_comp_eq_comp_pushforwardEndomorphism (x := fiberOfSelf p Xε)
      hrs.1 γ q hqlift Φ
  have hmem : pushforwardAutomorphism (x := fiberOfSelf p Xε) hrs.1 γ q hqlift Φ ∈
      infinitesimalAutomorphisms (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
        hrs.1 (p.map fi) e hpair fi (IsHomLift.map p fi) := by
    refine (mem_infinitesimalAutomorphisms_iff
      (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
      hrs.1 (p.map fi) e hpair fi (IsHomLift.map p fi) _).mpr ?_
    rw [← hret]
    have hendlift := (pushforwardAutomorphism (x := fiberOfSelf p Xε)
      hrs.1 γ q hqlift Φ).hom.2
    have := hendlift
    have hl : p.IsHomLift e
        ((pushforwardAutomorphism (x := fiberOfSelf p Xε)
          hrs.1 γ q hqlift Φ).hom.val ≫ h) :=
      IsHomLift.comp_lift_id_left p e h
        ((pushforwardAutomorphism (x := fiberOfSelf p Xε)
          hrs.1 γ q hqlift Φ).hom.val)
    have := hl
    refine Functor.IsStronglyCocartesian.ext p γ q e ?_
    rw [← Category.assoc, ← hpush, Category.assoc, hqh, reassoc_of% hφ1]
  have hΨ1 : pushforwardAutomorphism (x := fiberOfSelf p Xε) hrs.1 γ q hqlift Φ = 1 :=
    (Subgroup.eq_bot_iff_forall _).1 htriv _ hmem
  have hend : (pushforwardAutomorphism (x := fiberOfSelf p Xε)
      hrs.1 γ q hqlift Φ).hom.val = 𝟙 Xε := by
    rw [hΨ1]
    rfl
  have hφq : φ ≫ q = q := by rw [hpush, hend, Category.comp_id]
  have hφid : φ = 𝟙 c.pt := by
    refine PullbackCone.IsLimit.hom_ext hc₂ ?_ ?_
    · exact hφ1.trans (Category.id_comp _).symm
    · exact hφq.trans (Category.id_comp _).symm
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1
    (p.map c.snd) c.snd (IsHomLift.map p c.snd)
  have hidlift : p.IsHomLift (𝟙 (p.obj X')) (𝟙 X') := IsHomLift.id rfl
  have := hidlift
  have hafinal : a.hom.val = 𝟙 X' := by
    refine Functor.IsStronglyCocartesian.ext p (p.map c.snd) c.snd (𝟙 (p.obj X')) ?_
    rw [← hφ2, hφid, Category.id_comp, Category.comp_id]
  exact Aut.ext (Functor.Fiber.hom_ext hafinal)

/-- **Vanishing over a small extension.** For a category cofibered in groupoids over
`𝒞_Λ` satisfying (RS), if the infinitesimal automorphisms at a pushforward of `x` to the
special fibre vanish, then so do the infinitesimal automorphisms of `x'` over `x` along a
morphism lying over a small extension. -/
theorem relativeInfinitesimalAutomorphisms_eq_bot_of_isSmallExtension
    (hrs : SatisfiesRS p)
    {B A A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x' : p.Fiber B} {x : p.Fiber A} {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (g : B ⟶ A) (f : x'.1 ⟶ x.1) (hf : p.IsHomLift g f)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom g.hom.toRingHom))
    (g₀ : A ⟶ A₀) (f₀ : x.1 ⟶ x₀.1) (hf₀ : p.IsHomLift g₀ f₀)
    (i : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair i e)
    (fi : x₀.1 ⟶ xε.1) (hfi : p.IsHomLift i fi)
    (htriv : infinitesimalAutomorphisms hrs.1 i e hpair fi hfi = ⊥) :
    relativeInfinitesimalAutomorphisms hrs.1 g f hf = ⊥ := by
  obtain ⟨X', rfl⟩ := x'
  obtain ⟨X, rfl⟩ := x
  obtain ⟨X₀, rfl⟩ := x₀
  obtain ⟨Xε, rfl⟩ := xε
  have := hf
  have := hf₀
  have := hfi
  obtain rfl : g = p.map f := IsHomLift.eq_of_isHomLift p g f
  obtain rfl : g₀ = p.map f₀ := IsHomLift.eq_of_isHomLift p g₀ f₀
  obtain rfl : i = p.map fi := IsHomLift.eq_of_isHomLift p i fi
  exact relativeInfinitesimalAutomorphisms_eq_bot_of_isSmallExtension_aux
    hrs f f₀ fi e hsmall hpair htriv

end

/-! ### The general surjective case -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- Being a small extension is unaffected by an identification of the target. -/
private theorem isSmallExtension_comp_eqToHom
    {B A A' : ArtinianLocalAlgCat.{u, v, w} Λ k} (φ : B ⟶ A) (hA : A = A')
    (hφ : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom φ.hom.toRingHom)) :
    InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (φ ≫ eqToHom hA).hom.toRingHom) := by
  cases hA
  simpa using hφ

/-- **Vanishing over a surjection, for arrows whose base morphisms are their own images.**
The factorization of Tag 06GE is walked from the left: at each stage the next small
extension is pushed forward off the current object, and the remaining leg is factored
through that pushforward, so the new stage still maps to the original target and hence to
the special fibre. -/
private theorem relativeInfinitesimalAutomorphisms_eq_bot_aux
    (hrs : SatisfiesRS p) {X₀ Xε : F} (fi : X₀ ⟶ Xε)
    (e : p.obj Xε ⟶ p.obj X₀)
    (hpair : IsCanonicalDualNumberPair (p.map fi) e)
    (htriv : infinitesimalAutomorphisms (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
      hrs.1 (p.map fi) e hpair fi (IsHomLift.map p fi) = ⊥)
    {X' X : F} (f : X' ⟶ X) (f₀ : X ⟶ X₀)
    (hsurj : Function.Surjective (p.map f).hom) :
    relativeInfinitesimalAutomorphisms (x' := fiberOfSelf p X') (x := fiberOfSelf p X)
      hrs.1 (p.map f) f (IsHomLift.map p f) = ⊥ := by
  classical
  obtain ⟨n, G, hB, ee, hcomp, hsm⟩ :=
    surjective_factors_into_smallExtensions (p.map f) hsurj
  have key : ∀ m : ℕ, ∀ hm : m ≤ n,
      ∃ (Y : F) (hY : p.obj Y = G.obj' m hm) (u : X' ⟶ Y) (v : Y ⟶ X),
        u ≫ v = f ∧
        p.map v = eqToHom hY ≫ G.map' m n hm le_rfl ≫ ee.hom ∧
        ∀ a : Aut (fiberOfSelf p X'), a.hom.val ≫ u = u → a = 1 := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨X', hB.symm, 𝟙 X', f, Category.id_comp f, hcomp.symm, ?_⟩
      intro a ha
      exact Aut.ext (Functor.Fiber.hom_ext ((Category.comp_id a.hom.val).symm.trans ha))
    | succ m ih =>
      intro hm
      obtain ⟨Y, hY, u, v, huv, hv, hub⟩ := ih (Nat.le_of_succ_le hm)
      set b : p.obj Y ⟶ G.obj' (m + 1) hm :=
        eqToHom hY ≫ G.map' m (m + 1) (Nat.le_succ m) hm with hbdef
      have hbsmall : InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom b.hom.toRingHom) := by
        rw [hbdef]
        simpa using isSmallExtension_eqToHom_comp hY rfl
          (G.map' m (m + 1) (Nat.le_succ m) hm) (hsm m (Nat.lt_of_succ_le hm))
      obtain ⟨Z, u', hu'⟩ := exists_pushforward hrs.1 b Y rfl
      have hZ : p.obj Z = G.obj' (m + 1) hm := IsHomLift.codomain_eq p b u'
      have := hu'
      have hpu' : p.map u' = b ≫ eqToHom hZ.symm := by
        simpa using IsHomLift.fac' p b u'
      have hpu'small : InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom (p.map u').hom.toRingHom) := by
        rw [hpu']
        exact isSmallExtension_comp_eqToHom b hZ.symm hbsmall
      have hv2 : p.map v
          = p.map u' ≫ eqToHom hZ ≫ G.map' (m + 1) n hm le_rfl ≫ ee.hom := by
        rw [hpu', hbdef, hv, G.map'_comp m (m + 1) n (Nat.le_succ m) hm le_rfl]
        simp
      have := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1 (p.map u') u'
        (IsHomLift.map p u')
      have hu'v' : u' ≫ Functor.IsStronglyCocartesian.map p (p.map u') u' hv2 v = v :=
        Functor.IsStronglyCocartesian.fac p (p.map u') u' hv2 v
      have hv'lift : p.IsHomLift
          (eqToHom hZ ≫ G.map' (m + 1) n hm le_rfl ≫ ee.hom)
          (Functor.IsStronglyCocartesian.map p (p.map u') u' hv2 v) :=
        Functor.IsStronglyCocartesian.map_isHomLift p (p.map u') u' hv2 v
      set v' : Z ⟶ X := Functor.IsStronglyCocartesian.map p (p.map u') u' hv2 v
      have hpv' : p.map v' = eqToHom hZ ≫ G.map' (m + 1) n hm le_rfl ≫ ee.hom :=
        (IsHomLift.eq_of_isHomLift p _ v').symm
      have hstep : relativeInfinitesimalAutomorphisms (x' := fiberOfSelf p Y)
          (x := fiberOfSelf p Z) hrs.1 (p.map u') u' (IsHomLift.map p u') = ⊥ :=
        relativeInfinitesimalAutomorphisms_eq_bot_of_isSmallExtension
          (x' := fiberOfSelf p Y) (x := fiberOfSelf p Z)
          (x₀ := fiberOfSelf p X₀) (xε := fiberOfSelf p Xε)
          hrs (p.map u') u' (IsHomLift.map p u') hpu'small
          (p.map (v' ≫ f₀)) (v' ≫ f₀) (IsHomLift.map p (v' ≫ f₀))
          (p.map fi) e hpair fi (IsHomLift.map p fi) htriv
      have hprev : relativeInfinitesimalAutomorphisms (x' := fiberOfSelf p X')
          (x := fiberOfSelf p Y) hrs.1 (p.map u) u (IsHomLift.map p u) = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
        exact hub a ((mem_relativeInfinitesimalAutomorphisms_iff
          (x' := fiberOfSelf p X') (x := fiberOfSelf p Y)
          hrs.1 (p.map u) u (IsHomLift.map p u) a).mp ha)
      have hcompos : relativeInfinitesimalAutomorphisms (x' := fiberOfSelf p X')
          (x := fiberOfSelf p Z) hrs.1 (p.map u ≫ p.map u') (u ≫ u')
          (IsHomLift.comp p (p.map u) (p.map u') u u') = ⊥ :=
        relativeInfinitesimalAutomorphisms_eq_bot_comp
          (x'' := fiberOfSelf p X') (x' := fiberOfSelf p Y) (x := fiberOfSelf p Z)
          hrs.1 (p.map u) u (IsHomLift.map p u) (p.map u') u' (IsHomLift.map p u')
          (IsHomLift.comp p (p.map u) (p.map u') u u') hprev hstep
      refine ⟨Z, hZ, u ≫ u', v', ?_, hpv', ?_⟩
      · rw [Category.assoc, hu'v', huv]
      · intro a ha
        refine (Subgroup.eq_bot_iff_forall _).1 hcompos a ?_
        exact (mem_relativeInfinitesimalAutomorphisms_iff
          (x' := fiberOfSelf p X') (x := fiberOfSelf p Z)
          hrs.1 (p.map u ≫ p.map u') (u ≫ u')
          (IsHomLift.comp p (p.map u) (p.map u') u u') a).mpr ha
  obtain ⟨Y, hY, u, v, huv, hv, hub⟩ := key n le_rfl
  have hiso : IsIso (p.map v) := by
    rw [hv, G.map'_self n, Category.id_comp]
    infer_instance
  have hvIso : IsIso v := isIso_of_isCofiberedInGroupoids_of_map_isIso hrs.1 v
  refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  replace ha : a.hom.val ≫ f = f :=
    (mem_relativeInfinitesimalAutomorphisms_iff (x' := fiberOfSelf p X')
      (x := fiberOfSelf p X) hrs.1 (p.map f) f (IsHomLift.map p f) a).mp ha
  refine hub a ((cancel_mono v).1 ?_)
  rw [Category.assoc, huv, ha]

/-- Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), let `x' ⟶ x` be a
morphism of `𝓕` lying over a surjection, and let `x₀` be a pushforward of `x` to the special
fibre. If the infinitesimal automorphisms of `x₀` vanish, then so do the infinitesimal
automorphisms of `x'` over `x`. -/
@[stacks 06JZ]
theorem relativeInfinitesimalAutomorphisms_eq_bot
    (hrs : SatisfiesRS p)
    {B A A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x' : p.Fiber B} {x : p.Fiber A} {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (g : B ⟶ A) (f : x'.1 ⟶ x.1) (hf : p.IsHomLift g f)
    (hg : Function.Surjective g.hom)
    (g₀ : A ⟶ A₀) (f₀ : x.1 ⟶ x₀.1) (hf₀ : p.IsHomLift g₀ f₀)
    (i : A₀ ⟶ Aε) (e : Aε ⟶ A₀)
    (hpair : IsCanonicalDualNumberPair i e)
    (fi : x₀.1 ⟶ xε.1) (hfi : p.IsHomLift i fi)
    (htriv : infinitesimalAutomorphisms hrs.1 i e hpair fi hfi = ⊥) :
    relativeInfinitesimalAutomorphisms hrs.1 g f hf = ⊥ := by
  obtain ⟨X', rfl⟩ := x'
  obtain ⟨X, rfl⟩ := x
  obtain ⟨X₀, rfl⟩ := x₀
  obtain ⟨Xε, rfl⟩ := xε
  have := hf
  have := hf₀
  have := hfi
  obtain rfl : g = p.map f := IsHomLift.eq_of_isHomLift p g f
  obtain rfl : g₀ = p.map f₀ := IsHomLift.eq_of_isHomLift p g₀ f₀
  obtain rfl : i = p.map fi := IsHomLift.eq_of_isHomLift p i fi
  exact relativeInfinitesimalAutomorphisms_eq_bot_aux hrs fi e hpair htriv f f₀ hg

end

end Deformation

end
