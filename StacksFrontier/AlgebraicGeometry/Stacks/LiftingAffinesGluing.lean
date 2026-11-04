module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesTwoFibreProductLocal

/-!
# Gluing a smooth lift of an étale open from local smooth lifts (Stacks 0CJU)

Let `U ⟶ W` be étale and suppose given the data of a smooth lift of `U` except for the 2-fibre
product condition: an algebraic space `Y`, a morphism `i : U ⟶ Y`, a smooth 1-morphism
`y : Y ⟶ 𝒳'` and a filler `α`. If `Y` is covered by an étale covering `{e_k : U'_k ⟶ Y}` by the
ambient spaces of smooth lifts `ξ_k = (U_k, U'_k, …)` together with morphisms `U_k ⟶ U` making the
squares `U_k = U ×_Y U'_k` cartesian, and with comparisons `x'_k ⟶ y ∘ e_k` satisfying the
coherence of Stacks 0CJP, then `(U, Y, i, y, α)` is a smooth lift, and the given data are
morphisms `ξ_k ⟶ (U, Y, i, y, α)` of the category of Stacks 0CJP.

This is the last step of the source's construction of a descended object in the proof of
Stacks 0CJU: the 2-fibre product condition `U = 𝒳 ×_{𝒳'} U'` is checked on the members of the
étale covering `{U'_k ⟶ U'}`, where it holds for the `ξ_k`.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleSmoothLift.glue`: the glued smooth lift.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.glueHom`: the morphisms from the local smooth lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

/-- **Changing the legs of a 2-fibre product along equalities.** A square with the apex of a
2-fibre product `P`, legs equal to those of `P` and filler the filler of `P` transported along
these equalities is a 2-fibre product. -/
theorem isTwoFibreProduct_of_eq {𝔅 : Type*} [Bicategory 𝔅] {x y z : 𝔅} {f : x ⟶ z}
    {g : y ⟶ z} (P : TwoCommSq f g) (hP : IsTwoFibreProduct P) {a : P.pt ⟶ x} {b : P.pt ⟶ y}
    (ha : a = P.fst) (hb : b = P.snd) (γ : a ≫ f ≅ b ≫ g)
    (hγ : γ.hom = eqToHom (by rw [ha]) ≫ P.iso.hom ≫ eqToHom (by rw [hb])) :
    Nonempty (IsTwoFibreProduct (⟨P.pt, a, b, γ⟩ : TwoCommSq f g)) := by
  subst ha hb
  obtain rfl : γ = P.iso := Iso.ext (by simpa using hγ)
  exact ⟨hP⟩

/-- **The filler of a pasted square, against a coherent filler.** In a strict bicategory, paste
a square with filler `α` along a strictly commuting square `n ≫ i = j ≫ e`; if a filler `comm`
of `(ξ, j)` with `n ≫ a = ξ` is related to `α` through `γ` by the coherence condition of
Stacks 0CJP, the pasted filler is `comm` followed by `j^*γ`, up to transports. -/
theorem paste_iso_hom_eq_of_coherence {𝔅 : Type*} [Bicategory 𝔅] [Bicategory.Strict 𝔅]
    {N U A Y X X' : 𝔅} {n : N ⟶ U} {a : U ⟶ X} {ι : X ⟶ X'} {i : U ⟶ Y} {y : Y ⟶ X'}
    {j : N ⟶ A} {e : A ⟶ Y} {ξ : N ⟶ X} {yk : A ⟶ X'} (α : a ≫ ι ⟶ i ≫ y)
    (comm : ξ ≫ ι ⟶ j ≫ yk) (γ : yk ⟶ e ≫ y) {hw : n ≫ i = j ≫ e} (τ : n ≫ i ⟶ j ≫ e)
    (hτ : τ = eqToHom hw)
    (hL : ξ ≫ ι = n ≫ (a ≫ ι)) (hR : n ≫ (i ≫ y) = j ≫ (e ≫ y)) (h : (n ≫ a) ≫ ι = ξ ≫ ι)
    (hcoh : comm ≫ (j ◁ γ) = eqToHom hL ≫ (n ◁ α) ≫ eqToHom hR) :
    (α_ n a ι).hom ≫ (n ◁ α) ≫ (α_ n i y).inv ≫ (τ ▷ y) ≫ (α_ j e y).hom =
      eqToHom h ≫ (comm ≫ j ◁ γ) ≫ eqToHom rfl := by
  subst hτ
  rw [hcoh]
  simp [Strict.associator_eqToIso, eqToHom_whiskerRight]

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- The structure morphism of the source of a morphism `b : V ⟶ U` over `W` factors through
`b`, read in the 2-category of algebraic stacks. -/
theorem gluing_base_leg {V U : Space.SpacesEtale B S hS W} (b : V ⟶ U) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map V.obj.hom =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map b.hom.left ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map U.obj.hom := by
  rw [← CategoryTheory.Functor.map_comp, Over.w b.hom]

/-- A commuting square of algebraic spaces, read in the 2-category of algebraic stacks. -/
theorem gluing_square_leg {V U Y A : AlgebraicSpaces B S hS} {b : V ⟶ U} {i : U ⟶ Y}
    {j : V ⟶ A} {e : A ⟶ Y} (h : j ≫ e = b ≫ i) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map b ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map i =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map j ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map e := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

/-- The left-hand leg of the coherence condition for a morphism `b : V ⟶ U` over `W` into a
candidate smooth lift of `U`. -/
theorem gluing_left_leg {V U : Space.SpacesEtale B S hS W} (b : V ⟶ U) :
    ((algebraicSpaceStackFunctor.{u, w} B S hS).map V.obj.hom ≫ x) ≫ ι =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map b.hom.left ≫
        (((algebraicSpaceStackFunctor.{u, w} B S hS).map U.obj.hom ≫ x) ≫ ι) :=
  congrArg (fun p => (p ≫ x) ≫ ι) (gluing_base_leg b)

/-- The right-hand leg of the coherence condition for a commuting square of inclusions into a
candidate smooth lift. -/
theorem gluing_right_leg {V U Y A : AlgebraicSpaces B S hS}
    (y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y ⟶ 𝒳') {b : V ⟶ U} {i : U ⟶ Y}
    {j : V ⟶ A} {e : A ⟶ Y} (h : j ≫ e = b ≫ i) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map b ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map i ≫ y) =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map j ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ y) :=
  congrArg (· ≫ y) (gluing_square_leg h)

/-- **Local gluing data for a smooth lift.** The data of a smooth lift of `U` except for the
2-fibre product condition, together with an étale covering of the candidate ambient space by the
ambient spaces of smooth lifts `ξ k`, morphisms `b k : U_k ⟶ U` with cartesian squares, and
comparisons `γ k` satisfying the coherence of Stacks 0CJP. -/
structure GluingDatum (U : Space.SpacesEtale B S hS W) where
  /-- The candidate ambient space `U'`. -/
  ambient : AlgebraicSpaces B S hS
  /-- The candidate inclusion `i : U ⟶ U'`. -/
  inclusion : U.obj.left ⟶ ambient
  /-- The candidate 1-morphism `x' : U' ⟶ 𝒳'`. -/
  ambientMap : (algebraicSpaceStackFunctor.{u, w} B S hS).obj ambient ⟶ 𝒳'
  /-- The candidate 1-morphism is smooth. -/
  isSmooth_ambientMap : AlgebraicStacks.IsSmooth B S hS ambientMap
  /-- The candidate filler. -/
  comm : ((algebraicSpaceStackFunctor.{u, w} B S hS).map U.obj.hom ≫ x) ≫ ι ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map inclusion ≫ ambientMap
  /-- The index type of the covering. -/
  K : Type v
  /-- The local smooth lifts. -/
  ξ : K → EtaleSmoothLift B S hS ι hι W x hx
  /-- The morphisms `U_k ⟶ U` over `W`. -/
  base : ∀ k, (ξ k).base ⟶ U
  /-- The morphisms `U'_k ⟶ U'`. -/
  e : ∀ k, (ξ k).ambient ⟶ ambient
  /-- The squares commute. -/
  inclusion_comp : ∀ k, (ξ k).inclusion ≫ e k = (base k).hom.left ≫ inclusion
  /-- The squares are cartesian. -/
  isPullback : ∀ k, IsPullback (ξ k).inclusion (base k).hom.left (e k) inclusion
  /-- The `e k` form an étale covering. -/
  isEtaleCovering : Space.IsEtaleCovering B S hS (fun k => (ξ k).ambient.obj)
    (fun k => (e k).hom)
  /-- The comparisons `x'_k ⟶ x' ∘ e_k`. -/
  γ : ∀ k, (ξ k).ambientMap ⟶ (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ ambientMap
  /-- The coherence of Stacks 0CJP. -/
  coherence : ∀ k, (ξ k).comm.hom ≫
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (ξ k).inclusion ◁ γ k) =
      eqToHom (gluing_left_leg (base k)) ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map (base k).hom.left ◁ comm.hom) ≫
          eqToHom (gluing_right_leg ambientMap (inclusion_comp k))

variable {U : Space.SpacesEtale B S hS W}

/-- **The glued square is a 2-fibre product.** It is checked on the members of the étale
covering by `AlgebraicGeometry.Stack.isTwoFibreProduct_of_isEtaleCovering`, where the pasted
square is the 2-fibre product square of `ξ k` reindexed along `γ k`. -/
theorem GluingDatum.isTwoFibreProduct (G : GluingDatum.{u, w, v} (hι := hι) (hx := hx) U) :
    Nonempty (IsTwoFibreProduct (⟨_, _, _, G.comm⟩ : TwoCommSq ι G.ambientMap)) := by
  have : ∀ {𝒯 : AlgebraicStacks.{u, w} B S hS} {Z : AlgebraicSpaces B S hS}
      (φ ψ : 𝒯 ⟶ (algebraicSpaceStackFunctor.{u, w} B S hS).obj Z), Subsingleton (φ ⟶ ψ) :=
    fun φ ψ => subsingleton_hom₂_algebraicSpaceStackFunctor_obj φ ψ
  refine isTwoFibreProduct_of_isEtaleCovering hι G.comm (fun k => (G.base k).hom.left)
    (fun k => (G.ξ k).inclusion) G.e (fun k => (G.isPullback k).flip) G.isEtaleCovering
    fun k => ?_
  have h2 := isTwoFibreProduct_reindexSnd (asIso (G.γ k)) (G.ξ k).isTwoFibreProduct
  refine isTwoFibreProduct_of_eq _ h2 ?_ rfl _ ?_
  · exact ((congrArg (· ≫ x) (gluing_base_leg (G.base k))).trans (Strict.assoc _ _ _)).symm
  · exact paste_iso_hom_eq_of_coherence G.comm.hom (G.ξ k).comm.hom (G.γ k)
      (hw := gluing_square_leg (G.inclusion_comp k)) _ (Subsingleton.elim _ _)
      (gluing_left_leg (G.base k)) (gluing_right_leg G.ambientMap (G.inclusion_comp k)) _
      (G.coherence k)

/-- **The glued smooth lift** of a gluing datum over `U`: its base is `U`, and its 2-fibre product
condition is `AlgebraicGeometry.Stack.EtaleSmoothLift.GluingDatum.isTwoFibreProduct`. -/
def GluingDatum.glue (G : GluingDatum.{u, w, v} (hι := hι) (hx := hx) U) :
    EtaleSmoothLift B S hS ι hι W x hx where
  base := U
  ambient := G.ambient
  inclusion := G.inclusion
  ambientMap := G.ambientMap
  isSmooth_ambientMap := G.isSmooth_ambientMap
  comm := G.comm
  isTwoFibreProduct := G.isTwoFibreProduct.some

/-- The glued smooth lift lies over `U`. -/
@[simp]
theorem GluingDatum.glue_base (G : GluingDatum.{u, w, v} (hι := hι) (hx := hx) U) :
    G.glue.base = U :=
  rfl

/-- **The morphisms from the local smooth lifts to the glued one.** -/
def GluingDatum.glueHom (G : GluingDatum.{u, w, v} (hι := hι) (hx := hx) U) (k : G.K) :
    G.ξ k ⟶ G.glue :=
  (⟨G.base k, G.e k, G.inclusion_comp k, G.γ k, G.coherence k⟩ : Hom (G.ξ k) G.glue)

/-- The base component of `glueHom` is the given morphism `U_k ⟶ U`. -/
@[simp]
theorem GluingDatum.glueHom_base (G : GluingDatum.{u, w, v} (hι := hι) (hx := hx) U) (k : G.K) :
    Hom.base (G.glueHom k) = G.base k :=
  rfl

/-- The ambient component of `glueHom` is the given morphism `U'_k ⟶ U'`. -/
@[simp]
theorem GluingDatum.glueHom_ambient (G : GluingDatum.{u, w, v} (hι := hι) (hx := hx) U)
    (k : G.K) : Hom.ambient (G.glueHom k) = G.e k :=
  rfl

end EtaleSmoothLift

end AlgebraicGeometry.Stack
