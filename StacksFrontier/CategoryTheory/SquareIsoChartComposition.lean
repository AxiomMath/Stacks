module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Composing a comparison of two routes round a square, read through a further identification

Let a square of categories be given by `p : 𝒜 ⥤ 𝒞` on one side and `e : 𝒜 ⥤ 𝒜'`, `r : 𝒜' ⥤ 𝒞'`
on the other, with `Φ : p ⋙ e' ≅ e ⋙ r` the comparison of the two routes.  Suppose the squares
for two composable `p`'s compose, and that the functor `r` on the second side is identified with
another functor `q` by `k : q ≅ r`.  Then the comparisons read through `k` compose as well.

This is the two-categorical skeleton of the composition law for the comparison of the two
direct images of sheaves of modules round the square of small étale ringed sites of a
representable morphism of algebraic spaces.  Every datum is a variable of an arbitrary category,
and both hypotheses are the two statements a consumer has about its own square: the composition
law for the comparisons *before* the further identification, and the compatibility of that
identification with the composition comparisons on the two sides.

## Main results

* `Stacks.CategoryTheory.squareIsoCompOfChart`: **the composition law for the comparisons read
  through the further identification**, from the composition law for the comparisons themselves
  and the compatibility of the identification with the two composition comparisons.

## Implementation notes

The three comparisons read through the identification enter as variables `Φhf`, `Φgf`, `Φcf`
pinned by equations, rather than written out as `Φ ≪≫ _`: a consumer holds them as named
constructions, and supplying the equations lets it apply the law with no statement of its own
written out.  The same idiom, for the same reason, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardCongrComposition.lean`.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory

namespace Stacks.CategoryTheory

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞] {𝒜' : Type u₄} [Category.{v₄} 𝒜']
  {ℬ' : Type u₅} [Category.{v₅} ℬ'] {𝒞' : Type u₆} [Category.{v₆} 𝒞']

/-! ### Iterated whiskerings -/

/-- Whiskering on the left twice is whiskering by the composite. -/
theorem isoWhiskerLeft_isoWhiskerLeft (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) {H H' : 𝒞 ⥤ 𝒞'} (e : H ≅ H') :
    Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft G e) =
      Functor.isoWhiskerLeft (F ⋙ G) e :=
  rfl

/-- Whiskering a left whiskering on the right is whiskering the right whiskering on the left. -/
theorem isoWhiskerRight_isoWhiskerLeft (F : 𝒜 ⥤ ℬ) {G G' : ℬ ⥤ 𝒞} (e : G ≅ G') (H : 𝒞 ⥤ 𝒞') :
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft F e) H =
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight e H) :=
  rfl

/-- **The interchange law for whiskering, for isomorphisms.** -/
theorem isoWhiskerLeft_trans_isoWhiskerRight {F F' : 𝒜 ⥤ ℬ} {G G' : ℬ ⥤ 𝒞} (α : F ≅ F')
    (β : G ≅ G') :
    Functor.isoWhiskerLeft F β ≪≫ Functor.isoWhiskerRight α G' =
      Functor.isoWhiskerRight α G ≪≫ Functor.isoWhiskerLeft F' β :=
  Iso.ext (NatTrans.ext (funext fun X => (β.hom.naturality (α.hom.app X)).symm))

/-- Four-fold congruence for a composite of isomorphisms, so that a consumer replacing each
factor of a four-fold composite supplies four equations and writes no composite out. -/
theorem transFourCongr {𝒟 : Type u₁} [Category.{v₁} 𝒟] {W X Y Z Z' : 𝒟}
    {a a' : W ≅ X} {b b' : X ≅ Y} {c c' : Y ≅ Z} {d d' : Z ≅ Z'}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    a ≪≫ b ≪≫ c ≪≫ d = a' ≪≫ b' ≪≫ c' ≪≫ d' := by
  subst ha hb hc hd; rfl

/-! ### The composition law -/

variable {pₕ : 𝒜 ⥤ ℬ} {p_g : ℬ ⥤ 𝒞} {p_c : 𝒜 ⥤ 𝒞} {eA : 𝒜 ⥤ 𝒜'} {eB : ℬ ⥤ ℬ'} {eC : 𝒞 ⥤ 𝒞'}
  {rₕ qₕ : 𝒜' ⥤ ℬ'} {r_g q_g : ℬ' ⥤ 𝒞'} {r_c q_c : 𝒜' ⥤ 𝒞'}

/-- **The composition law for the comparisons of the two routes round a square, read through a
further identification of the functors on one side.**

`Ψ` is the composition comparison on the first side, `Θ'` and `Θ` the composition comparisons on
the second side before and after the identification `k`, and `Φhf`, `Φgf`, `Φcf` are the three
comparisons read through `k`.  `hstep` is the composition law before the identification and
`hchart` the compatibility of the identification with the two composition comparisons; the
conclusion is the composition law after it. -/
theorem squareIsoCompOfChart (Ψ : p_c ≅ pₕ ⋙ p_g) {Φh : pₕ ⋙ eB ≅ eA ⋙ rₕ}
    {Φg : p_g ⋙ eC ≅ eB ⋙ r_g} {Φc : p_c ⋙ eC ≅ eA ⋙ r_c} {kh : qₕ ≅ rₕ} {kg : q_g ≅ r_g}
    {kc : q_c ≅ r_c} {Θ : qₕ ⋙ q_g ≅ q_c} {Θ' : rₕ ⋙ r_g ≅ r_c}
    {Φhf : pₕ ⋙ eB ≅ eA ⋙ qₕ} {Φgf : p_g ⋙ eC ≅ eB ⋙ q_g} {Φcf : p_c ⋙ eC ≅ eA ⋙ q_c}
    (hΦh : Φhf = Φh ≪≫ Functor.isoWhiskerLeft eA kh.symm)
    (hΦg : Φgf = Φg ≪≫ Functor.isoWhiskerLeft eB kg.symm)
    (hΦc : Φcf = Φc ≪≫ Functor.isoWhiskerLeft eA kc.symm)
    (hstep : Φc = Functor.isoWhiskerRight Ψ eC ≪≫ Functor.isoWhiskerLeft pₕ Φg ≪≫
      Functor.isoWhiskerRight Φh r_g ≪≫ Functor.isoWhiskerLeft eA Θ')
    (hchart : Functor.isoWhiskerLeft rₕ kg.symm ≪≫ Functor.isoWhiskerRight kh.symm q_g ≪≫ Θ =
      Θ' ≪≫ kc.symm) :
    Functor.isoWhiskerLeft pₕ Φgf ≪≫ Functor.isoWhiskerRight Φhf q_g ≪≫
        Functor.isoWhiskerLeft eA Θ =
      Functor.isoWhiskerRight Ψ.symm eC ≪≫ Φcf := by
  subst hΦh hΦg hΦc hstep
  simp only [Functor.isoWhiskerLeft_trans, Functor.isoWhiskerRight_trans,
    isoWhiskerLeft_isoWhiskerLeft, isoWhiskerRight_isoWhiskerLeft, Iso.trans_assoc]
  rw [show Functor.isoWhiskerRight Ψ.symm eC = (Functor.isoWhiskerRight Ψ eC).symm from rfl,
    Iso.symm_self_id_assoc]
  refine congrArg (fun z => Functor.isoWhiskerLeft pₕ Φg ≪≫ z) ?_
  rw [← Iso.trans_assoc (Functor.isoWhiskerLeft (pₕ ⋙ eB) kg.symm),
    isoWhiskerLeft_trans_isoWhiskerRight, Iso.trans_assoc, ← isoWhiskerLeft_isoWhiskerLeft,
    ← Functor.isoWhiskerLeft_trans, ← Functor.isoWhiskerLeft_trans, hchart,
    Functor.isoWhiskerLeft_trans]

end Stacks.CategoryTheory

end
