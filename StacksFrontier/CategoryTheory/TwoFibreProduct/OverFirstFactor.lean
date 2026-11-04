module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Exchanging the factors of a 2-fibre product, and changing the first one

Fix a base category `𝒞`. The 2-fibre product over `𝒞` of Stacks 0040,
`CategoryTheory.TwoFibreProductOver`, is symmetric in its two factors: exchanging them and
inverting the comparison isomorphism of an object is an equivalence
`CategoryTheory.TwoFibreProductOver.swap`, strictly over `𝒞`. Conjugating
`CategoryTheory.TwoFibreProductOver.precomposeSnd` with it gives the change of the *first* factor,
`CategoryTheory.TwoFibreProductOver.precomposeFst`: a 1-morphism `t : 𝒯' ⥤ 𝒯` over `𝒞` induces
`𝒯' ×_{t ⋙ G, ℬ, F} 𝒜 ⥤ 𝒯 ×_{G, ℬ, F} 𝒜`, an equivalence as soon as `t` is.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.swap`: exchange of the two factors.
* `CategoryTheory.TwoFibreProductOver.precomposeFst`: change of the first factor.

## Main results

* `CategoryTheory.TwoFibreProductOver.swap_comp_structureFunctor` and
  `CategoryTheory.TwoFibreProductOver.precomposeFst_comp_structureFunctor`: both are strictly over
  `𝒞`.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_precomposeFst`: changing the first factor along
  an equivalence over `𝒞` is an equivalence.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

section Swap

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

/-- **Exchanging the two factors of a 2-fibre product over `𝒞`.** An object `(U, x, y, φ)` of
`𝒳 ×_𝒮 𝒴` becomes the object `(U, y, x, φ⁻¹)` of `𝒴 ×_𝒮 𝒳`, and a morphism `(a, b)` becomes
`(b, a)`. -/
def swap : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ TwoFibreProductOver p𝒴 p𝒳 p𝒮 G F where
  obj P :=
    { base := P.base
      x := P.y
      y := P.x
      hx := P.hy
      hy := P.hx
      iso := P.iso.symm
      vertical := by
        have := P.vertical
        exact IsHomLift.lift_id_inv p𝒮 P.base P.iso }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.b
      b := f.a
      ha := f.hb
      hb := f.ha
      w := by
        have hgoal : G.map f.b ≫ Q.iso.inv = P.iso.inv ≫ F.map f.a := by
          rw [Iso.eq_inv_comp, ← Category.assoc, ← f.w, Category.assoc, Iso.hom_inv_id,
            Category.comp_id]
        exact hgoal }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

/-- Exchanging the two factors is strictly over `𝒞`: it does not change the base object of an
object, nor the base morphism of a morphism. -/
lemma swap_comp_structureFunctor :
    swap p𝒳 p𝒴 p𝒮 F G ⋙ structureFunctor p𝒴 p𝒳 p𝒮 G F = structureFunctor p𝒳 p𝒴 p𝒮 F G := rfl

/-- Exchanging the two factors of a 2-fibre product is faithful. -/
instance : (swap p𝒳 p𝒴 p𝒮 F G).Faithful where
  map_injective h := Hom.ext' (congrArg Hom.b h) (congrArg Hom.a h)

/-- Exchanging the two factors of a 2-fibre product is full. -/
instance : (swap p𝒳 p𝒴 p𝒮 F G).Full where
  map_surjective {P Q} f := by
    obtain ⟨fa, hfa⟩ : ∃ g : P.y ⟶ Q.y, g = Hom.a f := ⟨_, rfl⟩
    obtain ⟨fb, hfb⟩ : ∃ g : P.x ⟶ Q.x, g = Hom.b f := ⟨_, rfl⟩
    have hw : G.map fa ≫ Q.iso.inv = P.iso.inv ≫ F.map fb := by
      rw [hfa, hfb]
      exact f.w
    have h₁ : P.iso.hom ≫ G.map fa ≫ Q.iso.inv = F.map fb := by
      rw [hw, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    have hw' : F.map fb ≫ Q.iso.hom = P.iso.hom ≫ G.map fa := by
      rw [← h₁, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    obtain ⟨fh, hfh⟩ : ∃ g : P.base ⟶ Q.base, g = f.hbase := ⟨_, rfl⟩
    have hha : p𝒳.IsHomLift fh fb := by
      rw [hfb, hfh]
      exact f.hb
    have hhb : p𝒴.IsHomLift fh fa := by
      rw [hfa, hfh]
      exact f.ha
    exact ⟨{ hbase := fh, a := fb, b := fa, ha := hha, hb := hhb, w := hw' },
      Hom.ext' hfa hfb⟩

/-- Exchanging the two factors of a 2-fibre product is essentially surjective. -/
instance : (swap p𝒳 p𝒴 p𝒮 F G).EssSurj where
  mem_essImage Q := ⟨(swap p𝒴 p𝒳 p𝒮 G F).obj Q, ⟨Iso.refl _⟩⟩

/-- Exchanging the two factors of a 2-fibre product is an equivalence. -/
instance : (swap p𝒳 p𝒴 p𝒮 F G).IsEquivalence := Functor.IsEquivalence.mk

end Swap

section PrecomposeFst

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒯' : Type u₂} [Category.{v₂} 𝒯']
  {𝒯 : Type u₃} [Category.{v₃} 𝒯] {𝒜 : Type u₄} [Category.{v₄} 𝒜] {ℬ : Type u₅} [Category.{v₅} ℬ]
  (pT' : 𝒯' ⥤ 𝒞) (pT : 𝒯 ⥤ 𝒞) (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞)
  (Gl : 𝒯 ⥤ ℬ) (Fl : 𝒜 ⥤ ℬ) (t : 𝒯' ⥤ 𝒯) (ht : t ⋙ pT = pT')

/-- **Precomposition of the first leg of a 2-fibre product over `𝒞` with a 1-morphism
`t : 𝒯' ⥤ 𝒯` over `𝒞`:** an object `(U, t', x, φ : G (t t') ≅ F x)` of `𝒯' ×_{t ⋙ G, ℬ, F} 𝒜` is
sent to `(U, t t', x, φ)`, an object of `𝒯 ×_{G, ℬ, F} 𝒜`. It is
`CategoryTheory.TwoFibreProductOver.precomposeSnd` conjugated by
`CategoryTheory.TwoFibreProductOver.swap`. -/
def precomposeFst :
    TwoFibreProductOver pT' p𝒜 pℬ (t ⋙ Gl) Fl ⥤ TwoFibreProductOver pT p𝒜 pℬ Gl Fl :=
  swap pT' p𝒜 pℬ (t ⋙ Gl) Fl ⋙ precomposeSnd (pT := p𝒜) (pℬ := pℬ) Fl Gl t ht ⋙
    swap p𝒜 pT pℬ Fl Gl

/-- Changing the first factor is strictly over `𝒞`. -/
lemma precomposeFst_comp_structureFunctor :
    precomposeFst pT' pT p𝒜 pℬ Gl Fl t ht ⋙ structureFunctor pT p𝒜 pℬ Gl Fl =
      structureFunctor pT' p𝒜 pℬ (t ⋙ Gl) Fl := rfl

/-- `CategoryTheory.TwoFibreProductOver.isEquivalence_precomposeSnd` with the first factor
exchanged and the comparison equivalence given as an explicit argument. -/
private theorem isEquivalence_precomposeSnd_swapped (hpT' : pT'.IsFiberedInGroupoids)
    (hpT : pT.IsFiberedInGroupoids) (hp𝒜 : p𝒜.IsFiberedInGroupoids) (hte : t.IsEquivalence)
    (hGl : Gl ⋙ pℬ = pT) :
    (precomposeSnd (pT := p𝒜) (pℬ := pℬ) Fl Gl t ht).IsEquivalence := by
  have _ := hte
  exact isEquivalence_precomposeSnd (pT := p𝒜) (pℬ := pℬ) (G := Fl) (F := Gl) (a := t)
    hp𝒜 hpT' hpT ht hGl

/-- **Changing the first factor of a 2-fibre product over `𝒞` along an equivalence over `𝒞` is an
equivalence.** The hypotheses are those of
`CategoryTheory.TwoFibreProductOver.isEquivalence_precomposeSnd` with the two factors exchanged;
`hGl` says that the leg out of the factor being replaced is a 1-morphism over `𝒞`. -/
theorem isEquivalence_precomposeFst (hp𝒜 : p𝒜.IsFiberedInGroupoids)
    (hpT' : pT'.IsFiberedInGroupoids) (hpT : pT.IsFiberedInGroupoids) (hte : t.IsEquivalence)
    (hGl : Gl ⋙ pℬ = pT) : (precomposeFst pT' pT p𝒜 pℬ Gl Fl t ht).IsEquivalence := by
  have := isEquivalence_precomposeSnd_swapped pT' pT p𝒜 pℬ Gl Fl t ht hpT' hpT hp𝒜 hte hGl
  exact inferInstanceAs ((swap pT' p𝒜 pℬ (t ⋙ Gl) Fl ⋙
    precomposeSnd (pT := p𝒜) (pℬ := pℬ) Fl Gl t ht ⋙ swap p𝒜 pT pℬ Fl Gl).IsEquivalence)

/-- Changing the second factor of a 2-fibre product over `𝒞` along an equivalence over `𝒞` is an
equivalence: `CategoryTheory.TwoFibreProductOver.isEquivalence_precomposeSnd`, with the hypothesis
that the comparison 1-morphism is an equivalence supplied as an explicit argument. -/
theorem isEquivalence_precomposeSnd' (hpT' : pT'.IsFiberedInGroupoids)
    (hpT : pT.IsFiberedInGroupoids) (hp𝒜 : p𝒜.IsFiberedInGroupoids) (hte : t.IsEquivalence)
    (hGl : Gl ⋙ pℬ = pT) :
    (precomposeSnd (pT := p𝒜) (pℬ := pℬ) Fl Gl t ht).IsEquivalence := by
  exact isEquivalence_precomposeSnd_swapped pT' pT p𝒜 pℬ Gl Fl t ht hpT' hpT hp𝒜 hte hGl

end PrecomposeFst

end CategoryTheory.TwoFibreProductOver

end
