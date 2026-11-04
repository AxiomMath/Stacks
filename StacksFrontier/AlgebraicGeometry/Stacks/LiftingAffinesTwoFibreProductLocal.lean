module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesChart
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCartesianLifts

/-!
# Being a 2-fibre product along a thickening is étale local on the target

Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S`, `y : Y ⟶ 𝒳'` a 1-morphism out of
the stack of an algebraic space and `(U, a, i, α)` a 2-commutative square over `(ι, y)` whose
apex is the stack of an algebraic space `U`. If `{e_k : A_k ⟶ Y}` is an étale covering and the
base change `N_k = U ×_Y A_k` with the pasted square is a 2-fibre product of `(ι, y ∘ e_k)` for
every `k`, then `(U, a, i, α)` is a 2-fibre product of `(ι, y)`.

This is the step of Stacks 0CJU which checks the 2-fibre product condition `U = 𝒳 ×_{𝒳'} U'`
of a glued smooth lift on the members of an étale covering of `U'`.

## Main results

* `AlgebraicGeometry.Stack.isIso_of_preHom_of_isTwoFibreProduct`: a morphism of algebraic spaces
  underlying a morphism of 2-commutative squares between two 2-fibre products of the same cospan
  is an isomorphism.
* `AlgebraicGeometry.Stack.exists_isTwoFibreProduct_of_isThickening`: the 2-fibre product of a
  thickening with a 1-morphism out of the stack of an algebraic space has an algebraic space as
  apex, with second leg a morphism of algebraic spaces.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_of_isEtaleCovering`: the locality statement above.

## Implementation notes

The proof compares the given square with the model `I = 𝒳 ×_{𝒳'} Y` of
`exists_isTwoFibreProduct_of_isThickening`: terminality of the model gives a morphism
`c : U ⟶ I` of algebraic spaces over `Y`, whose base change to each `A_k` is the comparison
between two 2-fibre products of `(ι, y ∘ e_k)` and hence an isomorphism. Being an isomorphism is
fpqc local on the target (**Stacks 041Y**), so `c` is an isomorphism, and a square comparable to a
2-fibre product along an invertible 1-morphism is one (**Stacks 003Q**).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

/-- **The compatibility of a base-changed comparison of squares.** In a strict bicategory, let
`φ` be the comparison 2-cell of a morphism `c` from a square `(a, i, α)` over `(ι, y)` to a square
`(p, q, γ)` over the same cospan, with `i = c ≫ q`, and paste both squares with strictly
commuting squares along `n, j` and `g, s` respectively, with `n ≫ c = m ≫ g` and `j = m ≫ s`.
Then `m`, with the comparison `n^*φ`, is a morphism between the two pasted squares: this is the
compatibility condition of Stacks 003O for it. -/
theorem paste_compat_of_compat {𝔅 : Type*} [Bicategory 𝔅] [Bicategory.Strict 𝔅]
    {N U I Ik A Y X X' : 𝔅} {n : N ⟶ U} {a : U ⟶ X} {ι : X ⟶ X'} {i : U ⟶ Y} {y : Y ⟶ X'}
    {j : N ⟶ A} {e : A ⟶ Y} {c : U ⟶ I} {p : I ⟶ X} {q : I ⟶ Y} {m : N ⟶ Ik} {g : Ik ⟶ I}
    {s : Ik ⟶ A} (α : a ≫ ι ⟶ i ≫ y) (γ : p ≫ ι ⟶ q ≫ y) (φ : a ⟶ c ≫ p)
    (hcq : i = c ≫ q) (h0 : n ≫ c = m ≫ g) (h2 : j = m ≫ s) (hw : n ≫ i = j ≫ e)
    (hw' : g ≫ q = s ≫ e) (h1 : n ≫ (c ≫ p) = m ≫ (g ≫ p))
    (hc : α ≫ (eqToHom hcq ▷ y) ≫ (α_ c q y).hom = (φ ▷ ι) ≫ (α_ c p ι).hom ≫ (c ◁ γ)) :
    ((α_ n a ι).hom ≫ (n ◁ α) ≫ (α_ n i y).inv ≫ (eqToHom hw ▷ y) ≫ (α_ j e y).hom) ≫
        (eqToHom h2 ▷ (e ≫ y)) ≫ (α_ m s (e ≫ y)).hom =
      (((n ◁ φ) ≫ eqToHom h1) ▷ ι) ≫ (α_ m (g ≫ p) ι).hom ≫
        (m ◁ ((α_ g p ι).hom ≫ (g ◁ γ) ≫ (α_ g q y).inv ≫ (eqToHom hw' ▷ y) ≫
          (α_ s e y).hom)) := by
  subst hcq h2
  have hα : α = (φ ▷ ι) ≫ (α_ c p ι).hom ≫ (c ◁ γ) ≫ (α_ c q y).inv := by
    rw [← cancel_mono (α_ c q y).hom]
    simpa using hc
  subst hα
  have h₁ : m ≫ (g ≫ (p ≫ ι)) = n ≫ (c ≫ (p ≫ ι)) := by
    rw [← Strict.assoc, ← h0, Strict.assoc]
  have h₂ : m ≫ (g ≫ (q ≫ y)) = n ≫ (c ≫ (q ≫ y)) := by
    rw [← Strict.assoc, ← h0, Strict.assoc]
  have key := whiskerLeft_whiskerLeft_eqToHom h0 γ h₁ h₂
  have key' : m ◁ g ◁ γ = eqToHom h₁ ≫ n ◁ c ◁ γ ≫ eqToHom h₂.symm := by
    rw [reassoc_of% key, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [whiskerLeft_comp, comp_whiskerRight, Strict.associator_eqToIso, eqToIso.hom,
    eqToIso.inv, eqToHom_whiskerRight, whiskerLeft_eqToHom, whisker_assoc, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, id_whiskerRight]
  rw [key']
  simp

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A 1-morphism between the stacks of two algebraic spaces is the image of a morphism. -/
private theorem exists_map_eq_of_hom {X Y : AlgebraicSpaces B S hS}
    (φ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y) :
    ∃ m : X ⟶ Y, (algebraicSpaceStackFunctor.{u, w} B S hS).map m = φ :=
  ⟨_, algebraicSpaceStackFunctor_map_homMk_representingMap φ⟩

/-- The image of a commuting square of morphisms of algebraic spaces commutes. -/
private theorem map_comp_eq_map_comp {X Y Z W : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z} (h : f ≫ g = f' ≫ g') :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map f ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map g =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map f' ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map g' := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

/-- **A comparison of 2-fibre products over algebraic spaces is an isomorphism.** Let `T` and
`T'` be 2-fibre products of the same cospan whose apexes are the stacks of algebraic spaces `X`
and `Z`, and let `m` be a morphism of 2-commutative squares from `T` to `T'` whose underlying
1-morphism is the image of `m₀ : X ⟶ Z`. Then `m₀` is an isomorphism: terminality supplies a
morphism back, both composites are 2-cell equivalent to identities, and a 2-morphism between
1-morphisms into the stack of an algebraic space is an equality. -/
theorem isIso_of_preHom_of_isTwoFibreProduct {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {X Z : AlgebraicSpaces B S hS}
    {a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶ 𝒳}
    {b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶ 𝒴} {γ : a ≫ f ≅ b ≫ g}
    {a' : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Z ⟶ 𝒳}
    {b' : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Z ⟶ 𝒴} {γ' : a' ≫ f ≅ b' ≫ g}
    (hT : IsTwoFibreProduct (⟨_, a, b, γ⟩ : TwoCommSq f g))
    (hT' : IsTwoFibreProduct (⟨_, a', b', γ'⟩ : TwoCommSq f g))
    (m : TwoCommSq.PreHom (⟨_, a, b, γ⟩ : TwoCommSq f g) ⟨_, a', b', γ'⟩) (m₀ : X ⟶ Z)
    (hm : m.hom = (algebraicSpaceStackFunctor.{u, w} B S hS).map m₀) : IsIso m₀ := by
  let m' := twoFibreProductPreHom hT ⟨_, a', b', γ'⟩
  obtain ⟨m'₀, hm'⟩ := exists_map_eq_of_hom m'.hom
  obtain ⟨θ₁, -, -⟩ := twoFibreProductPreHom_rel hT (m.comp m') (TwoCommSq.PreHom.id _)
  obtain ⟨θ₂, -, -⟩ := twoFibreProductPreHom_rel hT' (m'.comp m) (TwoCommSq.PreHom.id _)
  have e₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).map (m₀ ≫ m'₀) =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (𝟙 X) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, ← hm, hm']
    exact eq_of_hom₂_algebraicSpaceStackFunctor_obj θ₁.hom
  have e₂ : (algebraicSpaceStackFunctor.{u, w} B S hS).map (m'₀ ≫ m₀) =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (𝟙 Z) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, ← hm, hm']
    exact eq_of_hom₂_algebraicSpaceStackFunctor_obj θ₂.hom
  exact ⟨m'₀, algebraicSpaceStackFunctor_map_injective e₁,
    algebraicSpaceStackFunctor_map_injective e₂⟩

/-- **The base change of a thickening to an algebraic space is an algebraic space.** For a
thickening `ι : 𝒳 ⟶ 𝒳'` and a 1-morphism `y` out of the stack of an algebraic space `Y`, there
are an algebraic space `I`, a 1-morphism `p : I ⟶ 𝒳`, a morphism `q : I ⟶ Y` of algebraic spaces
and a 2-isomorphism `γ : ι ∘ p ≅ y ∘ q` exhibiting `I` as the 2-fibre product `𝒳 ×_{𝒳'} Y`. -/
theorem exists_isTwoFibreProduct_of_isThickening {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    {ι : 𝒳 ⟶ 𝒳'} (hι : IsThickening ι) {Y : AlgebraicSpaces B S hS}
    (y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y ⟶ 𝒳') :
    ∃ (I : AlgebraicSpaces B S hS) (p : (algebraicSpaceStackFunctor.{u, w} B S hS).obj I ⟶ 𝒳)
      (q : I ⟶ Y) (γ : p ≫ ι ≅ (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ y),
      Nonempty (IsTwoFibreProduct (⟨_, p, _, γ⟩ : TwoCommSq ι y)) := by
  have hrep : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} y.hom ι.hom).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ ι.hom y.hom _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        y.hom ι.hom) hι.1.1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS Y.obj Y.property)
  obtain ⟨I, c, p, γ, ⟨hγ⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj y ι hrep
  obtain ⟨q, rfl⟩ := exists_map_eq_of_hom c
  exact ⟨I, p, q, γ.symm, ⟨isTwoFibreProduct_swap hγ⟩⟩

/-- **Being a 2-fibre product along a thickening is étale local on the target.** Let
`ι : 𝒳 ⟶ 𝒳'` be a thickening, `y` a 1-morphism out of the stack of an algebraic space `Y` and
`(U, a, i, α)` a 2-commutative square over `(ι, y)` with apex the stack of an algebraic space.
Let `{e_k : A_k ⟶ Y}` be an étale covering and `N_k = U ×_Y A_k`, with projections `n_k` and
`j_k`. If for every `k` the square pasted from `(U, a, i, α)` and the cartesian square of `N_k`
is a 2-fibre product of `(ι, y ∘ e_k)`, then `(U, a, i, α)` is a 2-fibre product of `(ι, y)`.

The comparison `c : U ⟶ I` into the model `I = 𝒳 ×_{𝒳'} Y` of
`AlgebraicGeometry.Stack.exists_isTwoFibreProduct_of_isThickening` base-changes along
`I ×_Y A_k ⟶ I` to a comparison between two 2-fibre products of `(ι, y ∘ e_k)`, which is an
isomorphism by `AlgebraicGeometry.Stack.isIso_of_preHom_of_isTwoFibreProduct`; so `c` is an
isomorphism by **Stacks 041Y**, and the square is a 2-fibre product by **Stacks 003Q**. -/
theorem isTwoFibreProduct_of_isEtaleCovering {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    {ι : 𝒳 ⟶ 𝒳'} (hι : IsThickening ι) {U Y : AlgebraicSpaces B S hS}
    {a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳} {i : U ⟶ Y}
    {y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y ⟶ 𝒳'}
    (α : a ≫ ι ≅ (algebraicSpaceStackFunctor.{u, w} B S hS).map i ≫ y)
    {K : Type v} {N A : K → AlgebraicSpaces B S hS} (n : ∀ k, N k ⟶ U) (j : ∀ k, N k ⟶ A k)
    (e : ∀ k, A k ⟶ Y) (hpb : ∀ k, IsPullback (n k) (j k) i (e k))
    (he : Space.IsEtaleCovering B S hS (fun k => (A k).obj) (fun k => (e k).hom))
    (hN : ∀ k, Nonempty (IsTwoFibreProduct ((⟨_, a, _, α⟩ : TwoCommSq ι y).paste
      (algebraicSpaceStackSquare.{u, w} B S hS U.property (A k).property Y.property
        (N k).property (AlgebraicSpaces.isPullback_hom B S hS (hpb k)).w :
          TwoCommSq ((algebraicSpaceStackFunctor.{u, w} B S hS).map i)
            ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k)))))) :
    Nonempty (IsTwoFibreProduct (⟨_, a, _, α⟩ : TwoCommSq ι y)) := by
  classical
  obtain ⟨I, p, q, γ, ⟨hP⟩⟩ := exists_isTwoFibreProduct_of_isThickening hι y
  let Q : TwoCommSq ι y := ⟨_, a, _, α⟩
  let c := twoFibreProductPreHom hP Q
  obtain ⟨c₀, hc₀⟩ := exists_map_eq_of_hom c.hom
  have hcq : (algebraicSpaceStackFunctor.{u, w} B S hS).map i =
      c.hom ≫ (algebraicSpaceStackFunctor.{u, w} B S hS).map q :=
    eq_of_hom₂_algebraicSpaceStackFunctor_obj c.isoSnd.hom
  have hq : c₀ ≫ q = i := algebraicSpaceStackFunctor_map_injective (by
    rw [CategoryTheory.Functor.map_comp, hc₀, hcq])
  have hiso : IsIso c₀ := by
    let Ik : K → AlgebraicSpaces B S hS := fun k => AlgebraicSpaces.fiberProduct B S hS q (e k)
    let g : ∀ k, Ik k ⟶ I := fun k => ObjectProperty.homMk (pullback.fst q.hom (e k).hom)
    let sk : ∀ k, Ik k ⟶ A k := fun k => ObjectProperty.homMk (pullback.snd q.hom (e k).hom)
    have hIk : ∀ k, IsPullback (g k) (sk k) q (e k) := fun k =>
      AlgebraicSpaces.isPullback_fiberProduct B S hS q (e k)
    have hcov : Space.IsEtaleCovering B S hS (fun k => (Ik k).obj) (fun k => (g k).hom) :=
      Space.isEtaleCovering_pullback B S hS q.hom I.property (fun k => (A k).obj)
        (fun k => (e k).hom) he
    let Kp := Space.Topology.precoverage.{u, v} .fpqc B S hS
    let _ : (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget Kp :=
      Space.isomorphisms_isLocalAtTarget_fpqc.{u, v} B S hS
    have hmem : Presieve.ofArrows Ik g ∈ Kp I :=
      ⟨K, Ik, g, rfl, I.property, fun k => (Ik k).property,
        Space.isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov⟩
    suffices hk : ∀ k, IsIso (pullback.snd c₀ (g k)) by
      apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
        (P := MorphismProperty.isomorphisms _) hmem
      rintro V gV _ ⟨k⟩
      exact hk k
    intro k
    let mk : N k ⟶ Ik k := (hIk k).lift (n k ≫ c₀) (j k) (by rw [Category.assoc, hq, (hpb k).w])
    have hmk1 : mk ≫ g k = n k ≫ c₀ := (hIk k).lift_fst _ _ _
    have hmk2 : mk ≫ sk k = j k := (hIk k).lift_snd _ _ _
    have hsq : IsPullback (n k) mk c₀ (g k) :=
      IsPullback.of_bot (by rw [hmk2, hq]; exact hpb k) hmk1.symm (hIk k)
    let T'k : TwoCommSq ((algebraicSpaceStackFunctor.{u, w} B S hS).map q)
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k)) :=
      algebraicSpaceStackSquare.{u, w} B S hS I.property (A k).property Y.property
        (Ik k).property (p := (g k).hom) (q := (sk k).hom) (a := q.hom) (b := (e k).hom)
        (AlgebraicSpaces.isPullback_hom B S hS (hIk k)).w
    have hT' : IsTwoFibreProduct ((⟨_, p, _, γ⟩ : TwoCommSq ι y).paste T'k) :=
      isTwoFibreProduct_paste hP (isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS
        I.property (A k).property Y.property (Ik k).property (p := (g k).hom) (q := (sk k).hom)
        (a := q.hom) (b := (e k).hom) (AlgebraicSpaces.isPullback_hom B S hS (hIk k)))
    let Tk : TwoCommSq ((algebraicSpaceStackFunctor.{u, w} B S hS).map i)
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k)) :=
      algebraicSpaceStackSquare.{u, w} B S hS U.property (A k).property Y.property
        (N k).property (AlgebraicSpaces.isPullback_hom B S hS (hpb k)).w
    have : ∀ {𝒯 : AlgebraicStacks.{u, w} B S hS} {Z : AlgebraicSpaces B S hS}
        (φ ψ : 𝒯 ⟶ (algebraicSpaceStackFunctor.{u, w} B S hS).obj Z), Subsingleton (φ ⟶ ψ) :=
      fun φ ψ => subsingleton_hom₂_algebraicSpaceStackFunctor_obj φ ψ
    have hh0 : (algebraicSpaceStackFunctor.{u, w} B S hS).map (n k) ≫ c.hom =
        (algebraicSpaceStackFunctor.{u, w} B S hS).map mk ≫
          (algebraicSpaceStackFunctor.{u, w} B S hS).map (g k) := by
      rw [← hc₀]
      exact map_comp_eq_map_comp hmk1.symm
    have hh2 : (algebraicSpaceStackFunctor.{u, w} B S hS).map (j k) =
        (algebraicSpaceStackFunctor.{u, w} B S hS).map mk ≫
          (algebraicSpaceStackFunctor.{u, w} B S hS).map (sk k) := by
      rw [← CategoryTheory.Functor.map_comp, hmk2]
    have hh1 : (algebraicSpaceStackFunctor.{u, w} B S hS).map (n k) ≫ (c.hom ≫ p) =
        (algebraicSpaceStackFunctor.{u, w} B S hS).map mk ≫
          ((algebraicSpaceStackFunctor.{u, w} B S hS).map (g k) ≫ p) := by
      rw [← Strict.assoc, hh0, Strict.assoc]
    have hw : (algebraicSpaceStackFunctor.{u, w} B S hS).map (n k) ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map i =
          (algebraicSpaceStackFunctor.{u, w} B S hS).map (j k) ≫
            (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) := by
      exact map_comp_eq_map_comp (hpb k).w
    have hw' : (algebraicSpaceStackFunctor.{u, w} B S hS).map (g k) ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map q =
          (algebraicSpaceStackFunctor.{u, w} B S hS).map (sk k) ≫
            (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) := by
      exact map_comp_eq_map_comp (hIk k).w
    have hTk : Tk.iso.hom = eqToHom hw := Subsingleton.elim _ _
    have hT'k : T'k.iso.hom = eqToHom hw' := Subsingleton.elim _ _
    have hsnd : c.isoSnd.hom = eqToHom hcq := Subsingleton.elim _ _
    have hc : α.hom ≫ (eqToHom hcq ▷ y) ≫
          (α_ c.hom ((algebraicSpaceStackFunctor.{u, w} B S hS).map q) y).hom =
        (c.isoFst.hom ▷ ι) ≫ (α_ c.hom p ι).hom ≫ (c.hom ◁ γ.hom) := by
      rw [← hsnd]
      exact c.compat
    let M : TwoCommSq.PreHom (Q.paste Tk) ((⟨_, p, _, γ⟩ : TwoCommSq ι y).paste T'k) :=
      { hom := (algebraicSpaceStackFunctor.{u, w} B S hS).map mk
        isoFst := whiskerLeftIso ((algebraicSpaceStackFunctor.{u, w} B S hS).map (n k))
          c.isoFst ≪≫ eqToIso hh1
        isoSnd := eqToIso hh2
        compat := by
          have h := paste_compat_of_compat α.hom γ.hom c.isoFst.hom hcq hh0 hh2 hw hw' hh1 hc
          rw [← hTk, ← hT'k] at h
          exact h }
    have hmk : IsIso mk :=
      isIso_of_preHom_of_isTwoFibreProduct (X := N k) (Z := Ik k) (hN k).some hT' M mk rfl
    rw [← hsq.isoPullback_inv_snd]
    infer_instance
  have e₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).map (inv c₀) ≫ c.hom = 𝟙 _ := by
    rw [← hc₀, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  have e₂ : c.hom ≫ (algebraicSpaceStackFunctor.{u, w} B S hS).map (inv c₀) = 𝟙 _ := by
    rw [← hc₀, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  exact ⟨isTwoFibreProduct_of_section hP (c.ofSection _ (eqToIso e₁)) c.hom (eqToIso e₂)⟩

end AlgebraicGeometry.Stack
