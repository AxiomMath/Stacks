module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Defs
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.FpqcLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties of morphisms of schemes that are fpqc local on the base

A property of morphisms of schemes which is preserved by arbitrary base change and which
descends along every fpqc covering of the target is said to be *fpqc local on the base*;
such a property may be transported to a morphism of presheaves on a big site that is only
locally representable. Three entries of the Stacks Project's list are recorded here: being a
monomorphism, being surjective, and being universally injective. Each is fpqc local on the
base, hence also fppf local on the base, the fppf precoverage being coarser.

## Main results

* `AlgebraicGeometry.instIsLocalAtTargetFppfMonomorphisms`: monomorphisms are fppf
  local on the target.
* `AlgebraicGeometry.surjective_isLocalAtTarget_fpqc` and
  `AlgebraicGeometry.surjective_isLocalAtTarget_fppf`: surjectivity is fpqc, hence
  fppf, local on the target.
* `AlgebraicGeometry.universallyInjective_isLocalAtTarget_fpqc` and
  `AlgebraicGeometry.universallyInjective_isLocalAtTarget_fppf`: universal injectivity
  is fpqc, hence fppf, local on the target. The fpqc statement is Tag 02KW.

## Implementation notes

Every statement here is about morphisms of *schemes*, so each lives in the `AlgebraicGeometry`
namespace beside `AlgebraicGeometry.isLocalAtTarget_monomorphisms_fpqc`, which is the fpqc half
of the first entry. The namespace `AlgebraicGeometry.Space` is reserved for the corresponding
statements about morphisms of *algebraic spaces* over a base, which are about a different
category and are a different entry of the list:
`AlgebraicGeometry.Space.surjective_isLocalAtTarget_fpqc` and
`AlgebraicGeometry.Space.surjective_isLocalAtTarget_fppf` are Stacks Tag 041Q, in
`StacksFrontier/AlgebraicGeometry/Spaces/SurjectiveFpqcLocalAtTarget.lean`, and
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf` is Stacks Tag 0429 in the same shape.

Locality on the base is `CategoryTheory.MorphismProperty.IsLocalAtTarget` for the fpqc
respectively fppf precoverage of schemes; it packages both preservation under base change
and descent from an arbitrary covering family, so each statement above is the whole entry of
the list rather than one half of it. Passage from the fpqc to the fppf precoverage is
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` applied to
`AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`.

Surjectivity descends because an fpqc covering family is jointly surjective on points, and a
point of the target lifts to the fibre product of the source with any member of the family
through which it is hit. Universal injectivity is handled through its description as the
universal closure of injectivity on points: a descent criterion for a universal closure is
isolated first, and the joint surjectivity of an fpqc family then reduces injectivity of a
morphism to injectivity of its base changes along the family.

## References

* [Stacks Project, Tag 02KW](https://stacks.math.columbia.edu/tag/02KW)
* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Monomorphisms -/

add_to_stacks 02WH "monomorphism" MorphismProperty.IsStableUnderBaseChange.monomorphisms

add_to_stacks 02WH "monomorphism" AlgebraicGeometry.isLocalAtTarget_monomorphisms_fpqc

/-- Monomorphisms of schemes are local on the target for the fppf precoverage. -/
@[stacks 02WH "monomorphism", sga "4 IV 8.5.5" "special case"]
instance instIsLocalAtTargetFppfMonomorphisms :
    (MorphismProperty.monomorphisms Scheme).IsLocalAtTarget Scheme.fppfPrecoverage :=
  .of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-! ### Surjective morphisms -/

add_to_stacks 02WH "surjective" AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme

/-- **Stacks Project, Tag 02WH (surjective).** Surjectivity of scheme morphisms is local
on the target for the fpqc precoverage. -/
@[stacks 02WH "surjective", sga "4 IV 8.5.5"]
public instance surjective_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fpqcPrecoverage := by
  apply MorphismProperty.IsLocalAtTarget.mk_of_iff
  intro X Y f R hR
  refine ⟨?_, ?_⟩
  · intro hf U g hpb hg
    have : Surjective f := hf
    exact inferInstance
  · intro h
    have hjoint : ∀ y : Scheme.forget.obj Y, ∃ (U : Scheme.{u}) (g : U ⟶ Y),
        R g ∧ y ∈ Set.range (Scheme.forget.map g) := by
      simpa only [Scheme.jointlySurjectivePrecoverage,
        Presieve.mem_comap_jointlySurjectivePrecoverage_iff] using
        (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp
          (show R ∈ Scheme.jointlySurjectivePrecoverage Y from hR.2.1)
    refine ⟨fun y => ?_⟩
    obtain ⟨U, g, hg, ⟨z, hzy⟩⟩ := hjoint y
    obtain ⟨w, hw⟩ := (h g hg).surj z
    refine ⟨pullback.fst f g w, ?_⟩
    rw [← hzy]
    simpa [Scheme.Hom.comp_apply, hw] using
      congrArg (fun k : pullback f g ⟶ Y => k w)
        (pullback.condition (f := f) (g := g))

/-- **Stacks Project, Tag 02WH (surjective).** Surjectivity of scheme morphisms is local
on the target for the fppf precoverage. -/
@[stacks 02WH "surjective"]
public instance surjective_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le
    Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-! ### Universally injective morphisms -/

/-- A criterion for the universal closure of a morphism property to be local on the target:
it suffices that the property itself descend along every covering family of the given
precoverage, provided the precoverage is stable under base change. -/
private theorem universally_isLocalAtTarget_of_descending
    (K : Precoverage Scheme.{u}) (P : MorphismProperty Scheme.{u})
    [K.IsStableUnderBaseChange]
    [P.RespectsIso]
    (hdesc : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (𝒰 : Precoverage.ZeroHypercover.{u + 1} K Y),
      (∀ i, P (pullback.snd f (𝒰.f i))) → P f) :
    P.universally.IsLocalAtTarget K := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_isStableUnderBaseChange ?_
  intro X Y f 𝒰 hf
  apply MorphismProperty.universally_mk'
  · intro T g _
    apply hdesc (pullback.fst g f) (𝒰.pullback₁ g)
    intro i
    let ui := 𝒰.f i
    let V := pullback g ui
    let a : V ⟶ T := pullback.fst g ui
    let b : V ⟶ 𝒰.X i := pullback.snd g ui
    let p := pullback.snd f ui
    have hp : P (pullback.snd p b) :=
      hf i (pullback.fst p b) b (pullback.snd p b)
        (IsPullback.of_hasPullback p b).flip
    let e₁ : pullback (pullback.fst g f) a ≅ pullback (pullback.snd f g) a := by
      let e₀ := pullbackSymmetry f g
      have h₁ : pullback.fst g f ≫ 𝟙 T = e₀.inv ≫ pullback.snd f g := by
        simp [e₀]
      haveI : IsIso (e₀.inv) := inferInstance
      haveI : IsIso (𝟙 V) := inferInstance
      haveI : IsIso (𝟙 T) := inferInstance
      haveI : IsIso (pullback.map (pullback.fst g f) a (pullback.snd f g) a
          e₀.inv (𝟙 V) (𝟙 T) h₁ rfl) := by apply pullback.map_isIso
      exact asIso (pullback.map (pullback.fst g f) a (pullback.snd f g) a
        e₀.inv (𝟙 V) (𝟙 T) h₁ rfl)
    let e₂ := pullbackLeftPullbackSndIso f g a
    let e₃ := pullbackLeftPullbackSndIso f ui b
    have hab : a ≫ g = b ≫ ui := pullback.condition
    let e₄ := pullback.congrHom (f₁ := f) (f₂ := f)
      (g₁ := a ≫ g) (g₂ := b ≫ ui) rfl hab
    let e : pullback (pullback.fst g f) a ≅ pullback p b :=
      e₁.trans (e₂.trans (e₄.trans e₃.symm))
    have he₄ : e₄.hom ≫ pullback.snd f (b ≫ ui) =
        pullback.snd f (a ≫ g) := by
      dsimp [e₄]; rw [pullback.congrHom_hom]; simp only [pullback.map]
      rw [pullback.lift_snd]; simp
    have he₁ : e₁.hom ≫ pullback.snd (pullback.snd f g) a =
        pullback.snd (pullback.fst g f) a := by
      change pullback.map (pullback.fst g f) a (pullback.snd f g) a
        (pullbackSymmetry f g).inv (𝟙 V) (𝟙 T)
        (by rw [Category.comp_id, pullbackSymmetry_inv_comp_snd]) (by simp) ≫
          pullback.snd (pullback.snd f g) a = _
      simp only [pullback.map, pullback.lift_snd]
      simp
    have he : e.hom ≫ pullback.snd p b = pullback.snd (pullback.fst g f) a := by
      calc
        e.hom ≫ pullback.snd p b =
            e₁.hom ≫ e₂.hom ≫ e₄.hom ≫ e₃.inv ≫ pullback.snd p b := rfl
        _ = e₁.hom ≫ e₂.hom ≫ e₄.hom ≫ pullback.snd f (b ≫ ui) := by
          simp [e₃, p]
        _ = e₁.hom ≫ e₂.hom ≫ pullback.snd f (a ≫ g) := by
          rw [he₄]
        _ = e₁.hom ≫ pullback.snd (pullback.snd f g) a := by
          simp [e₂]
        _ = pullback.snd (pullback.fst g f) a := by
          rw [he₁]
    have hp' : P (e.hom ≫ pullback.snd p b) :=
      (MorphismProperty.cancel_left_of_respectsIso P e.hom (pullback.snd p b)).mpr hp
    rw [he] at hp'
    exact hp'

/-- A morphism of schemes whose base change along each member of a jointly surjective family
is injective on points is itself injective on points. -/
private theorem injective_of_jointly_surjective_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{u + 1}
      Scheme.fpqcPrecoverage Y)
    (hcover : ∀ y, ∃ i z, (𝒰.f i) z = y)
    (h : ∀ i, Function.Injective (pullback.snd f (𝒰.f i))) :
    Function.Injective f := by
  intro x₁ x₂ h₁₂
  obtain ⟨i, y, hy⟩ := hcover (f x₁)
  obtain ⟨z₁, hz₁x, hz₁y⟩ :=
    Scheme.Pullback.exists_preimage_pullback x₁ y hy.symm
  have h₂y : f x₂ = (𝒰.f i) y := h₁₂.symm.trans hy.symm
  obtain ⟨z₂, hz₂x, hz₂y⟩ :=
    Scheme.Pullback.exists_preimage_pullback x₂ y h₂y
  have hz : z₁ = z₂ := h i (hz₁y.trans hz₂y.symm)
  calc
    x₁ = pullback.fst f (𝒰.f i) z₁ := hz₁x.symm
    _ = pullback.fst f (𝒰.f i) z₂ := congrArg _ hz
    _ = x₂ := hz₂x

add_to_stacks 02WH "universally_injective"
  AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange

/-- Universal injectivity of morphisms of schemes is fpqc local on the target. -/
@[stacks 02WH "universally_injective"]
public instance universallyInjective_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@UniversallyInjective : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage := by
  rw [universallyInjective_eq]
  refine universally_isLocalAtTarget_of_descending Scheme.fpqcPrecoverage
    (topologically (Function.Injective ·)) ?_
  intro X Y f 𝒰 h
  apply injective_of_jointly_surjective_cover f 𝒰 ?_ h
  intro y
  have hmem : 𝒰.toPreZeroHypercover.presieve₀ ∈
      Scheme.precoverage (@Flat : MorphismProperty Scheme.{u}) Y := by
    apply Scheme.propQCPrecoverage_le_precoverage
    change 𝒰.toPreZeroHypercover.presieve₀ ∈ Scheme.fpqcPrecoverage Y
    exact 𝒰.mem₀
  let : Scheme.JointlySurjective
      (Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨Z, g, hg, z, hz⟩ :=
    Scheme.JointlySurjective.exists_eq
      (K := Scheme.precoverage (@Flat : MorphismProperty Scheme.{u}))
      𝒰.toPreZeroHypercover.presieve₀ hmem y
  rcases hg with ⟨i⟩
  exact ⟨i, z, by simpa using hz⟩

add_to_stacks 02KW "universal injectivity is fpqc local on the target"
  AlgebraicGeometry.universallyInjective_isLocalAtTarget_fpqc

/-- Universal injectivity of morphisms of schemes is fppf local on the target. -/
@[stacks 02WH "universally_injective"]
public instance universallyInjective_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (@UniversallyInjective : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

end AlgebraicGeometry

end
