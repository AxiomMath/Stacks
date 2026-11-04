module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.Hypothesis
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionBaseChange

/-!
# The hypothesis of Stacks 0CQM is stable under base change

Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` satisfy the hypothesis of **Stacks 0CQM**
(`AlgebraicGeometry.Stack.ValuativeCriterion.DenseTestExistence`), let `g : 𝒴' ⟶ 𝒴` be a
1-morphism and `P` a 2-fibre product of `g` and `f`, and let `h' : 𝒰' ⟶ 𝒳 ×_𝒴 𝒴'` come with a
1-morphism `u : 𝒰' ⟶ 𝒰` and a 2-isomorphism `h' ≫ P.snd ≅ u ≫ h`. Then `h'` and the base change
`P.fst` satisfy the hypothesis of Stacks 0CQM.

## Main results

* `AlgebraicGeometry.Stack.ValuativeCriterion.denseTestExistence_baseChange`: the statement
  above.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0CLE](https://stacks.math.columbia.edu/tag/0CLE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace CategoryTheory.Bicategory

universe w' v' u'

/-- **Transporting the pasted filler along a 2-isomorphism of the generic point.** In any
bicategory, the pasting of a square `c` of represented spectra with a filler `Γ` whose generic
point is `x₀` agrees with the pasting of `c` with the filler `Γ ≫ θ ▷ f` (generic point
`x₁ ≫ h`) followed by the inverse of `θ`. -/
theorem pastedFiller_transport {𝔅 : Type u'} [Bicategory.{w', v'} 𝔅]
    {U T U₀ T₀ Y X Z₁ : 𝔅} (j : U ⟶ T) (a : T ⟶ T₀) (k : U ⟶ U₀) (jq : U₀ ⟶ T₀)
    (y₀ : T₀ ⟶ Y) (x₀ : U₀ ⟶ X) (x₁ : U₀ ⟶ Z₁) (h : Z₁ ⟶ X) (f : X ⟶ Y)
    (c : (j ≫ a) ⟶ (k ≫ jq)) (Γ : (jq ≫ y₀) ⟶ (x₀ ≫ f)) (θ : x₀ ≅ (x₁ ≫ h)) :
    (α_ j a y₀).inv ≫ (c ▷ y₀) ≫ (α_ k jq y₀).hom ≫ (k ◁ Γ) ≫ (α_ k x₀ f).inv =
      ((α_ j a y₀).inv ≫ (c ▷ y₀) ≫ (α_ k jq y₀).hom ≫
          (k ◁ ((Γ ≫ (θ.hom ▷ f) ≫ (α_ x₁ h f).hom) ≫ (α_ x₁ h f).inv)) ≫
          (α_ k (x₁ ≫ h) f).inv) ≫ ((k ◁ θ.inv) ▷ f) := by
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Bicategory.whiskerLeft_comp,
    Bicategory.whisker_assoc_symm]
  simp only [← Bicategory.comp_whiskerRight]
  rw [← Bicategory.whiskerLeft_comp, Iso.hom_inv_id, Bicategory.whiskerLeft_id,
    Bicategory.id_whiskerRight, Category.comp_id]

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace ValuativeCriterion

variable {𝒰 𝒳 𝒴 𝒴' 𝒰' : AlgebraicStacks.{u, w} B S hS}

/-- **The hypothesis of Stacks 0CQM is stable under base change.** If `h : 𝒰 ⟶ 𝒳` and
`f : 𝒳 ⟶ 𝒴` satisfy it, `P` is a 2-fibre product of `g : 𝒴' ⟶ 𝒴` and `f`, and
`h' : 𝒰' ⟶ P.pt` satisfies `h' ≫ P.snd ≅ u ≫ h` for some `u : 𝒰' ⟶ 𝒰`, then `h'` and the base
change `P.fst` satisfy it. -/
theorem denseTestExistence_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (h : 𝒰 ⟶ 𝒳) (h' : 𝒰' ⟶ P.pt) (u : 𝒰' ⟶ 𝒰) (κ : h' ≫ P.snd ≅ u ≫ h)
    (hlift : DenseTestExistence B S hS h f) :
    DenseTestExistence B S hS h' P.fst := by
  classical
  let φ := baseChangeFiller B S hS f g P
  obtain ⟨hcart⟩ := nonempty_isTwoCartesian_baseChange B S hS f g P hP
  intro q hq
  let Q := ValuativeSquare.compRight B S hS q
  let ϑ : (h'.hom ≫ P.snd.hom) ≅ (u.hom ≫ h.hom) :=
    { hom := κ.hom.hom
      inv := κ.inv.hom
      hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom κ.hom_inv_id
      inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom κ.inv_hom_id }
  let θ₀ : ((q.x ≫ h'.hom) ≫ P.snd.hom) ≅ ((q.x ≫ u.hom) ≫ h.hom) :=
    α_ _ _ _ ≪≫ whiskerLeftIso q.x ϑ ≪≫ (α_ _ _ _).symm
  let ΓQ : (q.j ≫ (q.y ≫ g.hom)) ⟶ ((Q.x ≫ P.snd.hom) ≫ f.hom) :=
    (α_ q.j q.y g.hom).inv ≫ (Q.γ ▷ g.hom) ≫ (α_ Q.x P.fst.hom g.hom).hom ≫
      (Q.x ◁ φ.hom) ≫ (α_ Q.x P.snd.hom f.hom).inv
  let q₁ : ValuativeSquare B S hS (h ≫ f) :=
    { q with
      x := q.x ≫ u.hom
      y := q.y ≫ g.hom
      γ := ΓQ ≫ (θ₀.hom ▷ f.hom) ≫ (α_ (q.x ≫ u.hom) h.hom f.hom).hom }
  obtain ⟨e, ⟨d⟩⟩ := hlift q₁ hq
  let q₀ : ValuativeSquare B S hS f :=
    { Q with
      x := Q.x ≫ P.snd.hom
      y := Q.y ≫ g.hom
      γ := ΓQ }
  let E : Q.DominatingExtension := { e with }
  let E₀ : q₀.DominatingExtension := { e with }
  have hγ : IsIso E.inducedGamma :=
    (CatFiberedInGroupoids.homGroupoid _ _).all_isIso E.inducedGamma
  obtain ⟨E'⟩ := CategoryTheory.DottedArrowBaseChange.dottedArrows_baseChange_equivalence
    E.j (E.k ≫ Q.x) P.snd.hom P.fst.hom f.hom (E.a ≫ Q.y) g.hom φ
    (asIso E.inducedGamma) hcart
  have hγeq : ((α_ E.j (E.a ≫ Q.y) g.hom).symm ≪≫
      Bicategory.whiskerRightIso (asIso E.inducedGamma) g.hom ≪≫
      (α_ (E.k ≫ Q.x) P.fst.hom g.hom) ≪≫
      Bicategory.whiskerLeftIso (E.k ≫ Q.x) φ ≪≫
      (α_ (E.k ≫ Q.x) P.snd.hom f.hom).symm).hom = E₀.inducedGamma := by
    dsimp only [ValuativeSquare.DominatingExtension.inducedGamma]
    simp only [Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerRightIso_hom,
      Bicategory.whiskerLeftIso_hom]
    exact CatFiberedInGroupoids.pastedGamma e.j e.a e.k q.j q.y Q.x P.fst.hom P.snd.hom
      g.hom f.hom e.commute Q.γ φ.hom
  have hgamma : E₀.inducedGamma = e.inducedGamma ≫ ((e.k ◁ θ₀.inv) ▷ f.hom) :=
    Bicategory.pastedFiller_transport e.j e.a e.k q.j (q.y ≫ g.hom) (Q.x ≫ P.snd.hom)
      (q.x ≫ u.hom) h.hom f.hom e.commute ΓQ θ₀
  exact ⟨E, ⟨E'.inverse.obj
    { a := d.a
      α := d.α ≫ (e.k ◁ θ₀.inv)
      β := d.β
      compat := by
        refine hγeq.trans (hgamma.trans ?_)
        refine (congrArg (· ≫ ((e.k ◁ θ₀.inv) ▷ f.hom)) d.compat).trans ?_
        refine (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
          (congrArg _ (Bicategory.comp_whiskerRight _ _ _).symm))) }⟩⟩

end ValuativeCriterion

end AlgebraicGeometry.Stack

end
