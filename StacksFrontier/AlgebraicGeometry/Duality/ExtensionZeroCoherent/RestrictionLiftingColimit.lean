module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingTransfer
import all StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingTransfer
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit

/-!
# `RestrictionLifting` along a morphism of targets, and the colimit cocone

`CategoryTheory.RestrictionLifting F R N` is the elementwise form of the identification
`colim_n Mor(F_n, N) = colim_n Mor(R F_n, R N)` of [Stacks, Tag 0G2H]. This file transfers it
along a morphism of targets `s : N' ⟶ N` through which every morphism out of the system factors,
and which `R` turns into a bijection on morphisms out of the restricted system; this passes from
a truncation `τ^{≤b}L` to `L` itself when the system lives in degrees `≤ b`, as in
[Stacks, Tag 0G4K].

It also records the converse of `CategoryTheory.restrictionLifting_of_isColimit`: the elementwise
statement makes the cocone of `CategoryTheory.restrictionHomCocone` a colimit cocone, which is the
displayed identification `colim_n Hom(F_n, N) = Hom(A, R N)` itself.

## Main results

* `CategoryTheory.RestrictionLifting.of_comp`
* `CategoryTheory.RestrictionLifting.isColimitRestrictionHomCocone`

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4K](https://stacks.math.columbia.edu/tag/0G4K)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open InverseSequence

universe v u u' u''

namespace CategoryTheory

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- **`CategoryTheory.RestrictionLifting` transports along a morphism of targets.** Let
`s : N' ⟶ N` be such that every morphism `F_n ⟶ N` factors through `s`, and such that `R s`
induces a bijection `Mor(R F_n, R N') ⟶ Mor(R F_n, R N)` for every `n`. Then the identification
for `N'` gives it for `N`.

A lift for `N` is a lift for `N'` followed by `s`; and two morphisms `F_n ⟶ N` with equal
restrictions are `s` after two morphisms into `N'` whose restrictions are equal already, by the
injectivity of composition with `R s`. -/
public lemma RestrictionLifting.of_comp {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} {N' N : 𝒟} (s : N' ⟶ N)
    (h : RestrictionLifting F R N')
    (hX : ∀ (n : ℕ) (f : F.obj (op n) ⟶ N), ∃ f' : F.obj (op n) ⟶ N', f = f' ≫ s)
    (hU : ∀ n : ℕ,
      Function.Bijective fun g : R.obj (F.obj (op n)) ⟶ R.obj N' => g ≫ R.map s) :
    RestrictionLifting F R N where
  lift n g := by
    obtain ⟨g', rfl⟩ := (hU n).2 g
    obtain ⟨m, hm, f, hf⟩ := h.lift n g'
    refine ⟨m, hm, f ≫ s, ?_⟩
    show R.map (f ≫ s) = R.map (tr F hm) ≫ g' ≫ R.map s
    rw [R.map_comp, hf, Category.assoc]
  eq n f g hfg := by
    obtain ⟨f', rfl⟩ := hX n f
    obtain ⟨g', rfl⟩ := hX n g
    have hR : R.map f' = R.map g' :=
      (hU n).1 (by simpa only [R.map_comp] using hfg)
    obtain ⟨m, hm, he⟩ := h.eq n f' g' hR
    exact ⟨m, hm, by rw [← Category.assoc, ← Category.assoc, he]⟩

/-- An identification `e` of the restricted sequence with the constant sequence at `A` is
compatible with the transitions: `e⁻¹_m ≫ R(F_m ⟶ F_n) = e⁻¹_n`. -/
public lemma restrictionHomCocone_inv_app_comp_map_tr {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} {A : 𝒞}
    (e : F ⋙ R ≅ (Functor.const ℕᵒᵖ).obj A) {n m : ℕ} (hnm : n ≤ m) :
    e.inv.app (op m) ≫ R.map (tr F hnm) = e.inv.app (op n) := by
  have hh := e.inv.naturality (homOfLE hnm).op
  change 𝟙 A ≫ e.inv.app (op n) = e.inv.app (op m) ≫ R.map (tr F hnm) at hh
  rw [Category.id_comp] at hh
  exact hh.symm

/-- **The elementwise identification is the identification of the colimit.** If `R` identifies
`colim_n Mor(F_n, N)` with `colim_n Mor(R F_n, R N)` elementwise, and `F ⋙ R` is identified with
the constant sequence at `A` by `e`, then the cocone of `CategoryTheory.restrictionHomCocone`,
which sends `f : F_n ⟶ N` to `e⁻¹_n ≫ R f`, is a colimit cocone:
`colim_n Mor(F_n, N) = Mor(A, R N)`.

This is the converse of `CategoryTheory.restrictionLifting_of_isColimit`. -/
public def RestrictionLifting.isColimitRestrictionHomCocone {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} {N : 𝒟}
    (h : RestrictionLifting F R N) (A : 𝒞) (e : F ⋙ R ≅ (Functor.const ℕᵒᵖ).obj A) :
    IsColimit (restrictionHomCocone F R N A e) :=
  Types.FilteredColimit.isColimitOf (homColimitDiagram F N) (restrictionHomCocone F R N A e)
    (fun x => by
      change A ⟶ R.obj N at x
      obtain ⟨m, hm, f, hf⟩ := h.lift 0 (e.hom.app (op 0) ≫ x)
      refine ⟨m, f, ?_⟩
      change x = e.inv.app (op m) ≫ R.map f
      rw [hf, ← Category.assoc, restrictionHomCocone_inv_app_comp_map_tr e hm,
        Iso.inv_hom_id_app_assoc])
    (fun i k xi xk hik => by
      change F.obj (op i) ⟶ N at xi
      change F.obj (op k) ⟶ N at xk
      change e.inv.app (op i) ≫ R.map xi = e.inv.app (op k) ≫ R.map xk at hik
      have hi : i ≤ max i k := le_max_left _ _
      have hk : k ≤ max i k := le_max_right _ _
      have hR : R.map (tr F hi ≫ xi) = R.map (tr F hk ≫ xk) :=
        (cancel_epi (e.inv.app (op (max i k)))).mp <| by
          rwa [R.map_comp, R.map_comp, ← Category.assoc, ← Category.assoc,
            restrictionHomCocone_inv_app_comp_map_tr e hi,
            restrictionHomCocone_inv_app_comp_map_tr e hk]
      obtain ⟨q, hq, he⟩ := h.eq (max i k) _ _ hR
      refine ⟨q, homOfLE (hi.trans hq), homOfLE (hk.trans hq), ?_⟩
      change tr F (hi.trans hq) ≫ xi = tr F (hk.trans hq) ≫ xk
      rw [← tr_comp F hq hi, ← tr_comp F hq hk, Category.assoc, Category.assoc]
      exact he)

end CategoryTheory

end
