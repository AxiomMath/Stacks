module

public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Lifting an Artinian local point of an algebraic space to an étale chart

Let `X` be an algebraic space over `S` and let `x ∈ X(T)` be a point with values in an affine
object `T` of the big fppf site whose ring of global functions `A` is an Artinian local ring with
residue field `k`.  This file produces an étale chart `a : U ⟶ X` and a finite separable extension
`L / k` such that every Artinian local `T₁ ⟶ T` whose residue field receives `L` compatibly with
`k` lifts `x|_{T₁}` to a `T₁`-valued point of `U`.

The proof runs as follows.  Base changing an atlas `U ⟶ X` along `x` gives
a scheme `P` with a surjective étale map `P ⟶ T`, so `P` has a point; an affine open
`Spec C ⊆ P` around it has `A ⟶ C` étale, and `L` is the residue field of `C` at the chosen
prime.  It is finite and separable over `k` by Stacks 00UW, the `A`-algebra `C` being formally
unramified and essentially of finite type.  Given `T₁` and `ι : L ⟶ κ(T₁)`, the composite
`C ⟶ L ⟶ κ(T₁) = Γ(T₁) / 𝔪` is an `A`-algebra map, and since `𝔪` is nilpotent (`Γ(T₁)` is
Artinian local) and `C` is formally smooth over `A`, it lifts to `C ⟶ Γ(T₁)`
(`Algebra.FormallySmooth.lift`).  The resulting morphism `T₁ ⟶ Spec C ⊆ P ⟶ U` is the lift.

## Main results

* `AlgebraicGeometry.exists_lift_of_etale_of_isArtinianLocal`: the scheme-level statement, for an
  étale morphism `P₀ ⟶ T₀` with `T₀` affine Artinian local and a point of `P₀`.
* `AlgebraicGeometry.Space.exists_etale_chart_lift_of_isArtinianLocal`: the statement on an
  algebraic space, in the spelling the 07XW assembly consumes.

## Implementation notes

The extension `L` depends only on the chosen point of `P`, not on `T₁`; it is the residue field
of the localization of `C` at that point, so it lives in the universe `u` of the schemes.  Nothing
here carries a `stacks` attribute: this is an input to the proof of Stacks 07XW, not a tag.

## References

* [Stacks Project, Tag 00UW](https://stacks.math.columbia.edu/tag/00UW)
* [Stacks Project, Tag 07XW](https://stacks.math.columbia.edu/tag/07XW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Artinian local points lift along an étale morphism, after a finite separable extension of
the residue field.**  Let `q : P₀ ⟶ T₀` be étale with `T₀` affine and `Γ(T₀)` Artinian local with
residue field `k`, and let `x` be a point of `P₀`.  There is a finite separable extension `L / k`
such that for every affine `T₁` with `Γ(T₁)` Artinian local, every `π₀ : T₁ ⟶ T₀` and every
embedding `ι : L ⟶ κ(T₁)` compatible with `π₀` on residue fields, `π₀` factors through `q`.

`L` is the residue field of an affine open `Spec C ∋ x` at `x`; the factorization is the
formally smooth lift of `C ⟶ L ⟶ κ(T₁)` along the nilpotent maximal ideal of `Γ(T₁)`. -/
theorem exists_lift_of_etale_of_isArtinianLocal {P₀ T₀ : Scheme.{u}} (q : P₀ ⟶ T₀) [Etale q]
    [IsAffine T₀] [IsLocalRing Γ(T₀, ⊤)] [IsArtinianRing Γ(T₀, ⊤)] (x : P₀) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (ResidueField Γ(T₀, ⊤)) L),
      FiniteDimensional (ResidueField Γ(T₀, ⊤)) L ∧
      Algebra.IsSeparable (ResidueField Γ(T₀, ⊤)) L ∧
      ∀ (T₁ : Scheme.{u}) (π₀ : T₁ ⟶ T₀) [IsAffine T₁] [IsLocalRing Γ(T₁, ⊤)]
        [IsArtinianRing Γ(T₁, ⊤)] (ι : L →+* ResidueField Γ(T₁, ⊤)),
        (ι.comp (algebraMap _ L)).comp (residue _) = (residue _).comp π₀.appTop.hom →
        ∃ b : T₁ ⟶ P₀, b ≫ q = π₀ := by
  obtain ⟨W, hW, hxW, -⟩ : ∃ W : P₀.Opens, W ∈ P₀.affineOpens ∧ x ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 P₀.isBasis_affineOpens)
      (show x ∈ (⊤ : P₀.Opens) from trivial)
  have hW : IsAffineOpen W := hW
  let A := Γ(T₀, ⊤)
  let C := Γ(P₀, W)
  let ψ : A ⟶ C := q.appLE ⊤ W le_top
  let : Algebra A C := ψ.hom.toAlgebra
  have : Algebra.Etale A C :=
    HasRingHomProperty.appLE (P := @Etale) q ‹_› ⟨⊤, isAffineOpen_top T₀⟩ ⟨W, hW⟩ le_top
  let 𝔮 := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  let S := Localization.AtPrime 𝔮
  have hmax : ∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A C a ∈ 𝔮 := by
    have h𝔮 : 𝔮.comap (algebraMap A C) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.comap _).isMaximal'
    intro a
    rw [← h𝔮]
    rfl
  have : IsLocalHom (algebraMap A S) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    rw [IsScalarTower.algebraMap_apply A C S] at ha
    exact (IsLocalization.AtPrime.isUnit_to_map_iff S 𝔮 _).1 ha ((hmax a).1 hna)
  have : Algebra.FormallyUnramified A S := Algebra.FormallyUnramified.comp A C S
  have : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A C S
  refine ⟨ResidueField S, inferInstance, inferInstance, inferInstance, inferInstance,
    fun T₁ π₀ _ _ _ ι hι ↦ ?_⟩
  let A₁ := Γ(T₁, ⊤)
  let : Algebra A A₁ := π₀.appTop.hom.toAlgebra
  have hnil : IsNilpotent (maximalIdeal A₁) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  let g : C →ₐ[A] A₁ ⧸ maximalIdeal A₁ :=
    { toRingHom := ι.comp ((residue S).comp (algebraMap C S))
      commutes' := fun a ↦ by
        have h := DFunLike.congr_fun hι a
        simp only [RingHom.comp_apply] at h
        change ι (residue S (algebraMap C S (algebraMap A C a))) = residue A₁ (π₀.appTop.hom a)
        rw [← h, ← IsScalarTower.algebraMap_apply, ResidueField.algebraMap_residue] }
  let ℓ := Algebra.FormallySmooth.lift (maximalIdeal A₁) hnil g
  refine ⟨T₁.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ℓ.toRingHom) ≫ hW.fromSpec, ?_⟩
  have hℓ : ψ ≫ CommRingCat.ofHom ℓ.toRingHom = π₀.appTop := by
    ext a
    exact ℓ.commutes a
  rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q
    (isAffineOpen_top T₀) hW le_top, IsAffineOpen.fromSpec_top, ← Spec.map_comp_assoc]
  change T₁.isoSpec.hom ≫ Spec.map (ψ ≫ CommRingCat.ofHom ℓ.toRingHom) ≫ T₀.isoSpec.inv = π₀
  rw [hℓ, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-- **An Artinian local point of an algebraic space lifts to an étale chart, after a finite
separable extension of the residue field.**  For `x ∈ X(T)` with `T` affine and `Γ(T)` Artinian
local with residue field `k`, there are an étale chart `a : U ⟶ X` and a finite separable
extension `L / k` such that for every Artinian local affine `T₁` over `T`, by `π`, whose residue
field receives `L` compatibly with `k`, the restriction `x|_{T₁}` comes from a `T₁`-valued point
`g` of `U`.

`U` is the scheme of an atlas of `X`; `L` is supplied by
`AlgebraicGeometry.exists_lift_of_etale_of_isArtinianLocal` applied to the base change of the
atlas along `x`, which is a scheme surjective and étale over `T`. -/
theorem exists_etale_chart_lift_of_isArtinianLocal
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
    [IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
    (x : X.obj (Opposite.op T)) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) L),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      FiniteDimensional (IsLocalRing.ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) L ∧
      Algebra.IsSeparable (IsLocalRing.ResidueField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) L ∧
      ∀ (T₁ : BigFppfOver B S hS) (π : T₁ ⟶ T)
        [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
        [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj T₁, ⊤)]
        [IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj T₁, ⊤)]
        (ι : L →+* IsLocalRing.ResidueField Γ((BigFppfOver.toScheme B S hS).obj T₁, ⊤)),
        (ι.comp (algebraMap _ L)).comp (IsLocalRing.residue _) =
          (IsLocalRing.residue _).comp ((BigFppfOver.toScheme B S hS).map π).appTop.hom →
        ∃ g : T₁ ⟶ U, a.app (Opposite.op T₁) g = X.map π.op x := by
  obtain ⟨U, f, hfS, hfE⟩ := hX.exists_atlas
  let x' : yoneda.obj T ⟶ X := yonedaEquiv.symm x
  let P := hfE.rep.pullback x'
  let p : P ⟶ T := hfE.rep.snd x'
  have hpE : Etale ((BigFppfOver.toScheme B S hS).map p) := hfE.property_snd x'
  have hpS : Surjective ((BigFppfOver.toScheme B S hS).map p) := hfS.property_snd x'
  let t : (BigFppfOver.toScheme B S hS).obj T :=
    (BigFppfOver.toScheme B S hS).obj T |>.isoSpec.inv (IsLocalRing.closedPoint _)
  obtain ⟨y, -⟩ := hpS.surj t
  obtain ⟨L, _, _, hfin, hsep, hlift⟩ :=
    AlgebraicGeometry.exists_lift_of_etale_of_isArtinianLocal
      ((BigFppfOver.toScheme B S hS).map p) y
  refine ⟨U, f, L, inferInstance, inferInstance, hfE, hfin, hsep, fun T₁ π _ _ _ ι hι ↦ ?_⟩
  obtain ⟨b, hb⟩ := hlift _ ((BigFppfOver.toScheme B S hS).map π) ι hι
  have hb' : ObjectProperty.homMk b ≫ p.left = π.left := B.inclusion.map_injective hb
  let g₁ : T₁ ⟶ P := Over.homMk (ObjectProperty.homMk b) (by
    rw [← Over.w p, ← Category.assoc, hb', Over.w π])
  have hg₁ : g₁ ≫ p = π := Over.OverMorphism.ext hb'
  refine ⟨g₁ ≫ hfE.rep.fst' x', ?_⟩
  rw [← yonedaEquiv_yoneda_map (g₁ ≫ hfE.rep.fst' x'), ← yonedaEquiv_comp, Functor.map_comp,
    Category.assoc, hfE.rep.map_fst', hfE.rep.w, ← Category.assoc, ← Functor.map_comp, hg₁,
    ← yonedaEquiv_naturality, Equiv.apply_symm_apply]

end AlgebraicGeometry.Space

end
