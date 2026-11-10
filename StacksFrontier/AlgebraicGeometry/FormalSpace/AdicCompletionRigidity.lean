module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphism

/-!
# Sections of a completion detected through an adic morphism

Let `V` be an object of the big fppf site of `S`, `Z ⊆ |V|` a set of points and
`x̂ : V_{/Z} ⟶ W` an adic morphism (representable by algebraic spaces) into an fppf sheaf `W`.
Let `T` be an object of the site with a tower of objects `W_n ⟶ T` for which sections of every
algebraic space over `T` are the same as compatible families over the `W_n` (Stacks 0AQH, when
`T = Spec R` for a Noetherian complete local ring `R` and `W_n = Spec(R/𝔪ⁿ⁺¹)`).

A morphism `φ : T ⟶ V` whose restrictions to the `W_n` have image in `Z` need not itself have
image in `Z`. This file shows that it does as soon as the sections `x̂(φ|_{W_n})` are the
restrictions of a single section `ω ∈ W(T)`: the restrictions `(φ|_{W_n}, W_n ⟶ T)` are then a
compatible family of sections of the algebraic space `V_{/Z} ×_{x̂, W, ω} T`, which comes from a
section over `T` whose first component is `φ`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasImageIn_of_isAdicMorphism_of_truncations`.

## References

* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Sections over `T` exist for compatible families over the `W_n` of a `ULift`ed algebraic space,
as soon as they exist for algebraic spaces. -/
private theorem exists_section_of_isAlgebraicSpaceULift {T : BigFppfOver B S hS}
    (Wn : ℕ → BigFppfOver B S hS) (ι : ∀ n, Wn n ⟶ T) (τ : ∀ n, Wn n ⟶ Wn (n + 1))
    (hT : ∀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F →
      ∀ x : ∀ n, F.obj (op (Wn n)), (∀ n, F.map (τ n).op (x (n + 1)) = x n) →
        ∃! y : F.obj (op T), ∀ n, F.map (ι n).op y = x n)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (hP : Space.IsAlgebraicSpaceULift.{u + 1} B S hS P)
    (s : ∀ n, P.obj (op (Wn n))) (hs : ∀ n, P.map (τ n).op (s (n + 1)) = s n) :
    ∃ sT : P.obj (op T), ∀ n, P.map (ι n).op sT = s n := by
  obtain ⟨F', hF', ⟨e⟩⟩ := Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hP
  let x : ∀ n, F'.obj (op (Wn n)) := fun n => (e.inv.app _ (s n)).down
  have hx : ∀ n, F'.map (τ n).op (x (n + 1)) = x n := fun n => by
    refine (congrArg ULift.down (e.inv.naturality_apply (τ n).op (s (n + 1)))).symm.trans ?_
    change (e.inv.app _ (P.map (τ n).op (s (n + 1)))).down = _
    rw [hs n]
  obtain ⟨y', hy', -⟩ := hT F' hF' x hx
  refine ⟨e.hom.app _ (ULift.up y'), fun n => ?_⟩
  rw [← e.hom.naturality_apply (ι n).op (ULift.up y' : ULift.{u + 1} (F'.obj _))]
  change e.hom.app _ (ULift.up (F'.map (ι n).op y')) = s n
  rw [hy' n]
  change (e.inv ≫ e.hom).app _ (s n) = s n
  rw [Iso.inv_hom_id]
  rfl

/-- A morphism `φ : T ⟶ V`, determined by its restrictions along the `ι n`, has image in `Z` as
soon as those restrictions are the restrictions of one section of the completion `V_{/Z}`. -/
private theorem hasImageIn_of_completionSheaf_restrictions {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} {T : BigFppfOver B S hS}
    {Wn : ℕ → BigFppfOver B S hS} (ι : ∀ n, Wn n ⟶ T) (φ : T ⟶ V)
    (hφ : ∀ n, Space.HasImageIn B S hS (yoneda.obj V) Z (Wn n) (ι n ≫ φ))
    (huniq : ∀ ψ : T ⟶ V, (∀ n, ι n ≫ ψ = ι n ≫ φ) → ψ = φ)
    (aT : (Space.completionSheaf B S hS (yoneda.obj V) Z).obj.obj (op T))
    (haT : ∀ n, (Space.completionSheaf B S hS (yoneda.obj V) Z).obj.map (ι n).op aT =
      presheafSection B S hS (F := yoneda.obj V) (ι n ≫ φ) (hφ n)) :
    Space.HasImageIn B S hS (yoneda.obj V) Z T φ := by
  let e' := Space.completionSheafIsoSubfunctor B S hS (isAlgebraicSpace_yoneda B S hS V).isSheaf Z
  have hres : ∀ n, ι n ≫ (e'.hom.app (op T) aT).1.down = ι n ≫ φ := fun n => by
    have h1 := e'.hom.naturality_apply (ι n).op aT
    have h2 : e'.hom.app (op (Wn n)) (presheafSection B S hS (F := yoneda.obj V) (ι n ≫ φ)
        (hφ n)) = ⟨ULift.up (ι n ≫ φ), hφ n⟩ :=
      congrArg (fun ψ => ψ.app (op (Wn n)) ⟨ULift.up (ι n ≫ φ), hφ n⟩) e'.inv_hom_id
    rw [haT n, h2] at h1
    exact (congrArg (fun t => t.1.down) h1).symm
  exact huniq _ hres ▸ (e'.hom.app (op T) aT).2

/-- **Image in `Z` detected through an adic morphism.** Let `x̂ : V_{/Z} ⟶ W` be adic, and let
`T` carry a tower `W_n ⟶ T` along which sections of algebraic spaces are determined by, and
exist for, compatible families. If `φ : T ⟶ V` restricts on every `W_n` to a section of `V_{/Z}`
whose image under `x̂` is the restriction of one section `ω ∈ W(T)`, then `φ` itself has
point-set image in `Z`. -/
theorem hasImageIn_of_isAdicMorphism_of_truncations {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} {W : FppfSheaf B S hS}
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (hxhat : IsAdicMorphism B S hS xhat) {T : BigFppfOver B S hS}
    (Wn : ℕ → BigFppfOver B S hS) (ι : ∀ n, Wn n ⟶ T) (τ : ∀ n, Wn n ⟶ Wn (n + 1))
    (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    (hT : ∀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F →
      ∀ x : ∀ n, F.obj (op (Wn n)), (∀ n, F.map (τ n).op (x (n + 1)) = x n) →
        ∃! y : F.obj (op T), ∀ n, F.map (ι n).op y = x n)
    (φ : T ⟶ V) (hφ : ∀ n, Space.HasImageIn B S hS (yoneda.obj V) Z (Wn n) (ι n ≫ φ))
    (ω : W.obj.obj (op T))
    (hω : ∀ n, xhat.hom.app (op (Wn n)) (presheafSection B S hS (F := yoneda.obj V)
      (ι n ≫ φ) (hφ n)) = W.obj.map (ι n).op ω) :
    Space.HasImageIn B S hS (yoneda.obj V) Z T φ := by
  let C := (Space.completionSheaf B S hS (yoneda.obj V) Z).obj
  let ωm : uliftYoneda.{u + 1}.obj T ⟶ W.obj := uliftYonedaEquiv.symm ω
  let P := pullback ωm xhat.hom
  have hφτ : ∀ n, τ n ≫ ι (n + 1) ≫ φ = ι n ≫ φ := fun n => by rw [← Category.assoc, hτ n]
  let a : ∀ n, C.obj (op (Wn n)) := fun n =>
    presheafSection B S hS (F := yoneda.obj V) (ι n ≫ φ) (hφ n)
  have ha : ∀ n, C.map (τ n).op (a (n + 1)) = a n := fun n => by
    have h' : Space.HasImageIn B S hS (yoneda.obj V) Z (Wn n)
        ((yoneda.obj V).map (τ n).op (ι (n + 1) ≫ φ)) := by
      change Space.HasImageIn B S hS (yoneda.obj V) Z (Wn n) (τ n ≫ ι (n + 1) ≫ φ)
      rw [hφτ n]
      exact hφ n
    refine (presheafSection_map B S hS (F := yoneda.obj V) (τ n) (ι (n + 1) ≫ φ) (hφ (n + 1))
      h').trans ?_
    exact presheafSection_congr B S hS (hφτ n) _ _
  have hcomm : ∀ n, uliftYoneda.map (ι n) ≫ ωm = uliftYonedaEquiv.symm (a n) ≫ xhat.hom :=
    fun n => by
      have h1 : uliftYoneda.map (ι n) ≫ ωm = uliftYonedaEquiv.symm (W.obj.map (ι n).op ω) :=
        (uliftYonedaEquiv_symm_map (ι n).op ω).symm
      rw [h1, uliftYonedaEquiv_symm_comp, hω n]
  let l : ∀ n, uliftYoneda.{u + 1}.obj (Wn n) ⟶ P := fun n =>
    pullback.lift (uliftYoneda.map (ι n)) (uliftYonedaEquiv.symm (a n)) (hcomm n)
  have hl : ∀ n, uliftYoneda.map (τ n) ≫ l (n + 1) = l n := fun n => by
    apply pullback.hom_ext
    · simp only [l, Category.assoc, pullback.lift_fst, ← Functor.map_comp, hτ n]
    · simp only [l, Category.assoc, pullback.lift_snd]
      rw [← ha n, uliftYonedaEquiv_symm_map]
      rfl
  let s : ∀ n, P.obj (op (Wn n)) := fun n => uliftYonedaEquiv (l n)
  have hs : ∀ n, P.map (τ n).op (s (n + 1)) = s n := fun n => by
    simp only [s]
    rw [uliftYonedaEquiv_naturality]
    exact congrArg uliftYonedaEquiv (hl n)
  obtain ⟨sT, hsT⟩ := exists_section_of_isAlgebraicSpaceULift Wn ι τ hT (hxhat T ωm) s hs
  obtain ⟨y₀, -, huniq⟩ := hT (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
    (fun n => ι n ≫ φ) (fun n => hφτ n)
  refine hasImageIn_of_completionSheaf_restrictions ι φ hφ
    (fun ψ hψ => (huniq ψ hψ).trans (huniq φ fun _ => rfl).symm)
    ((pullback.snd ωm xhat.hom).app (op T) sT) fun n => ?_
  rw [← (pullback.snd ωm xhat.hom).naturality_apply (ι n).op sT, hsT n]
  change uliftYonedaEquiv (l n ≫ pullback.snd ωm xhat.hom) = a n
  rw [pullback.lift_snd, Equiv.apply_symm_apply]

end AlgebraicGeometry.FormalSpace

end
