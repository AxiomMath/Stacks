module

public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceSourceFibre
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# Representability of the diagonal of a category fibred in groupoids (Stacks 02YA)

Let `𝒞` be a category with products of pairs and fibre products and let `p : 𝒮 ⥤ 𝒞` be a
category fibred in groupoids. Stacks 02YA (Lemma 4.42.6) says that the following are
equivalent:

1. the diagonal `Δ : 𝒮 ⥤ 𝒮 × 𝒮` is representable, where `𝒮 × 𝒮 = 𝒮 ×_𝒞 𝒮` is the 2-fibre
   product over the final object `𝟭 𝒞` (Stacks 0040);
2. for every object `U` of `𝒞`, every 1-morphism `G : 𝒞/U ⥤ 𝒮` is representable.

Representability of a 1-morphism is Stacks 02Y7
(`Stacks.RepresentableMorphism.IsRepresentableMorphism`): every base change along a 1-morphism
`𝒞/V ⥤ 𝒮` out of a slice is equivalent over `𝒞/V` to a slice category.

## Proof

Both conditions are turned into statements about presheaves of sets on slices of `𝒞`.

* By `CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver`, the base change of `Δ`
  along `Y = (Y₁, Y₂) : 𝒞/W ⥤ 𝒮 × 𝒮` is the category of elements of the presheaf of vertical
  morphisms `Y₁ ⟶ Y₂` on `𝒞/W`.
* By `CategoryTheory.TwoFibreProductOver.SliceSourceFibre.nonempty_equivalenceOver`, the base
  change of `G : 𝒞/U ⥤ 𝒮` along `G' : 𝒞/V ⥤ 𝒮` is the category of elements of the presheaf on
  `𝒞/V` of pairs `(k, m)` of a morphism `k : T ⟶ U` and a vertical morphism `m : G' T ⟶ G k`.

A category fibred in groupoids over `𝒞/V` equivalent to the category of elements of a presheaf
is a slice exactly when the presheaf is representable
(`Stacks.RepresentableMorphism.isRepresentableCFG_iff_exists_representableBy`). The two
implications then become the two computations in the source:

* (1) ⇒ (2): apply (1) to `(G ∘ pr₁, G' ∘ pr₂) : 𝒞/(U × V) ⥤ 𝒮 × 𝒮`. If its presheaf of
  vertical morphisms is represented by `W ⟶ U × V`, the presheaf of pairs `(k, m)` is
  represented by `W ⟶ U × V ⟶ V`: a pair `(k, m)` over `T ⟶ V` is a vertical morphism over
  `(k, T ⟶ V) : T ⟶ U × V`.
* (2) ⇒ (1): apply (2) to `G = Y₂` and `G' = Y₁`. If the presheaf of pairs `(k, m)` is
  represented by `a : W ⟶ U` with universal pair `(a', m₀)`, the presheaf of vertical morphisms
  `Y₁ ⟶ Y₂` is the subpresheaf of pairs with `k` the structure morphism, and is represented by
  the equalizer of `a` and `a'`, that is, by `W ×_{(a, a'), U × U, Δ} U`.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableMorphism_diagonal_iff`: **Stacks 02YA**.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver

namespace Stacks.RepresentableMorphism

universe v u₁ u₂ u₃ w

section Presheaf

variable {T : Type u₃} [Category.{v} T]

/-- A presheaf of sets `P` is represented by `Z` exactly when it has a universal element over `Z`:
an element `ξ` of `P(Z)` such that every element of every `P(a)` is the restriction of `ξ` along a
unique morphism `a ⟶ Z`. -/
theorem nonempty_representableBy_iff (P : Tᵒᵖ ⥤ Type v) (Z : T) :
    Nonempty (P.RepresentableBy Z) ↔
      ∃ ξ : P.obj (op Z), ∀ (a : T) (s : P.obj (op a)), ∃! f : a ⟶ Z, P.map f.op ξ = s := by
  constructor
  · rintro ⟨R⟩
    refine ⟨R.homEquiv (𝟙 Z), fun a s => ⟨R.homEquiv.symm s, ?_, fun f hf => ?_⟩⟩
    · dsimp only
      rw [← R.homEquiv_eq, Equiv.apply_symm_apply]
    · dsimp only at hf
      rw [← R.homEquiv_eq] at hf
      rw [← hf, Equiv.symm_apply_apply]
  · rintro ⟨ξ, h⟩
    have hbij : ∀ a : T, Function.Bijective (fun f : a ⟶ Z => P.map f.op ξ) := fun a =>
      ⟨fun f g hfg => (h a _).unique rfl hfg.symm, fun s => (h a s).exists⟩
    exact ⟨{ homEquiv := Equiv.ofBijective _ (hbij _)
             homEquiv_comp := fun f g => by simp }⟩

/-- Two presheaves of sets valued in one universe are isomorphic as soon as they become isomorphic
after the trivial universe lift. -/
def isoOfUliftIso {P Q : Tᵒᵖ ⥤ Type v}
    (i : P ⋙ uliftFunctor.{v, v} ≅ Q ⋙ uliftFunctor.{v, v}) : P ≅ Q :=
  (Functor.rightUnitor P).symm ≪≫ Functor.isoWhiskerLeft P uliftFunctorTrivial.symm ≪≫ i ≪≫
    Functor.isoWhiskerLeft Q uliftFunctorTrivial ≪≫ Functor.rightUnitor Q

end Presheaf

variable {𝒞 : Type u₁} [Category.{v} 𝒞]

/-- A category fibred in groupoids `s` over a slice `𝒞/V` which is equivalent over `𝒞/V` to the
category of elements of a presheaf of sets `P` is representable (Stacks 02Y3) exactly when `P` is
a representable presheaf. -/
theorem isRepresentableCFG_iff_exists_representableBy {V : 𝒞} {𝒟 : Type u₃} [Category.{w} 𝒟]
    {s : 𝒟 ⥤ Over V} (hs : s.IsFiberedInGroupoids) (P : (Over V)ᵒᵖ ⥤ Type v)
    (e : StacksRepresentableCFG.EquivalenceOver s (presheafOfCategories (P ⋙ typeToCat)).p) :
    IsRepresentableCFG s ↔ ∃ Z : Over V, Nonempty (P.RepresentableBy Z) := by
  constructor
  · rintro ⟨Z, E, hE⟩
    obtain ⟨Ginv, -, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
    obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hs
      (StacksRepresentableCFG.over_isFiberedInSetoids Z).isFiberedInGroupoids E
      hE.isCartesianFunctor.comm
      (CategoryTheory.Equivalence.mk E Ginv ε.symm η).isEquivalence_functor
    obtain ⟨i⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff P (yoneda.obj Z)).1
      ⟨e.symm.trans (k.trans (PresheafOfCategories.sliceElementsEquivalenceOver Z))⟩
    exact ⟨Z, ⟨Functor.representableByEquiv.symm (isoOfUliftIso i).symm⟩⟩
  · rintro ⟨Z, ⟨R⟩⟩
    obtain ⟨e'⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff P (yoneda.obj Z)).2
      ⟨Functor.isoWhiskerRight (Functor.representableByEquiv R).symm uliftFunctor⟩
    exact isRepresentableCFG_of_isRepresentable _
      ⟨Z, ⟨e.trans (e'.trans (PresheafOfCategories.sliceElementsEquivalenceOver Z).symm)⟩⟩

variable {𝒮 : Type u₂} [Category.{v} 𝒮] {p : 𝒮 ⥤ 𝒞}

open DiagonalFibre in
/-- The diagonal of a category fibred in groupoids is representable (Stacks 02Y7) exactly when, for
every object `U` of `𝒞` and every 1-morphism `Y = (Y₁, Y₂) : 𝒞/U ⥤ 𝒮 ×_𝒞 𝒮`, the presheaf on
`𝒞/U` of vertical morphisms `Y₁ ⟶ Y₂` is representable. -/
theorem isRepresentableMorphism_diag_iff (hp : p.IsFiberedInGroupoids) :
    IsRepresentableMorphism p (ProdP p) (Diag p) ↔
      ∀ (U : 𝒞) (Y : Over U ⥤ Prod' p) (hY : Y ⋙ ProdP p = Over.forget U),
        ∃ Z : Over U, Nonempty ((vertHomPresheaf hp hY).RepresentableBy Z) := by
  have hprod : (ProdP p).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p p (𝟭 𝒞) p p hp hp
      Functor.isFiberedInGroupoids_id (Functor.comp_id p) (Functor.comp_id p)
  refine forall_congr' fun U => forall_congr' fun Y => forall_congr' fun hY => ?_
  exact isRepresentableCFG_iff_exists_representableBy
    (fst_isFiberedInGroupoids U p (ProdP p) (Diag p) Y hp hprod rfl hY) _ (equivalenceOver hp hY)

/-- A 1-morphism `G : 𝒞/U ⥤ 𝒮` out of a slice is representable (Stacks 02Y7) exactly when, for
every 1-morphism `G' : 𝒞/V ⥤ 𝒮` out of a slice, the presheaf on `𝒞/V` of pairs `(k, m)` of a
morphism `k : T ⟶ U` and a vertical morphism `m : G' T ⟶ G k` is representable. -/
theorem isRepresentableMorphism_over_iff (hp : p.IsFiberedInGroupoids) {U : 𝒞}
    {G : Over U ⥤ 𝒮} (hG : G ⋙ p = Over.forget U) :
    IsRepresentableMorphism (Over.forget U) p G ↔
      ∀ (V : 𝒞) (G' : Over V ⥤ 𝒮) (hG' : G' ⋙ p = Over.forget V),
        ∃ Z : Over V, Nonempty ((SliceSourceFibre.presheaf hp hG' hG).RepresentableBy Z) := by
  refine forall_congr' fun V => forall_congr' fun G' => forall_congr' fun hG' => ?_
  have hfst := fst_isFiberedInGroupoids V (Over.forget U) p G G'
    (Functor.IsFiberedInGroupoids.over_forget U) hp hG hG'
  obtain ⟨e⟩ := SliceSourceFibre.nonempty_equivalenceOver hp hG' hG hfst
  exact isRepresentableCFG_iff_exists_representableBy hfst _ e

open DiagonalFibre SliceSourceFibre

/-! ### (1) ⇒ (2): the presheaf of pairs is a relocalized presheaf of vertical morphisms -/

section ProdSlice

variable {U V : 𝒞} [HasBinaryProduct U V] {G : Over U ⥤ 𝒮} {G' : Over V ⥤ 𝒮}

/-- A vertical morphism `G' (pr₂ b) ⟶ G (pr₁ b)` over an object `b` of `𝒞/(U × V)` is a pair
`(k, m)` over `pr₂ b` in `𝒞/V`, with `k = pr₁ ∘ b`. -/
noncomputable def toSliceHom {b : Over (U ⨯ V)}
    (t : VertHom p (Over.forget (U ⨯ V)) (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G')
      (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) b) :
    SliceHom p (Over.forget V) U G' G ((Over.map prod.snd).obj b) :=
  ⟨b.hom ≫ prod.fst, t.1, t.2⟩

lemma toSliceHom_injective {b : Over (U ⨯ V)}
    {t t' : VertHom p (Over.forget (U ⨯ V)) (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G')
      (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) b}
    (h : toSliceHom t = toSliceHom t') : t = t' :=
  Subtype.ext (eq_of_heq (SliceHom.mk.inj h).2)

lemma exists_toSliceHom_eq {b : Over (U ⨯ V)}
    (s : SliceHom p (Over.forget V) U G' G ((Over.map prod.snd).obj b))
    (hk : s.k = b.hom ≫ prod.fst) :
    ∃ t : VertHom p (Over.forget (U ⨯ V)) (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G')
      (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) b, toSliceHom t = s := by
  obtain ⟨k, m, hv⟩ := s
  dsimp only at hk
  subst hk
  exact ⟨⟨m, hv⟩, rfl⟩

variable (hp : p.IsFiberedInGroupoids) (hG : G ⋙ p = Over.forget U)
  (hG' : G' ⋙ p = Over.forget V)
  (h₁ : (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G') ⋙ p = Over.forget (U ⨯ V))
  (h₂ : (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) ⋙ p = Over.forget (U ⨯ V))

include hG in
/-- `toSliceHom` commutes with restriction. -/
lemma toSliceHom_restrict {b' b : Over (U ⨯ V)} (g : b' ⟶ b)
    (t : VertHom p (Over.forget (U ⨯ V)) (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G')
      (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) b) :
    toSliceHom (VertHom.restrict hp h₁ h₂ g t) =
      SliceHom.restrict hp hG' hG ((Over.map prod.snd).map g) (toSliceHom t) := by
  refine SliceHom.eq_restrict hp hG' hG _ _ _ ?_ ?_
  · change b'.hom ≫ prod.fst = g.left ≫ b.hom ≫ prod.fst
    rw [← Over.w g, Category.assoc]
  · exact VertHom.restrict_fac hp h₁ h₂ g t

/-- **(1) ⇒ (2) of Stacks 02YA, on presheaves.** If the presheaf on `𝒞/(U × V)` of vertical
morphisms `G' ∘ pr₂ ⟶ G ∘ pr₁` is represented by `Z`, then the presheaf on `𝒞/V` of pairs
`(k, m)` with `k : T ⟶ U` and `m : G' T ⟶ G k` vertical is represented by `pr₂ ∘ Z`. -/
theorem nonempty_representableBy_presheaf_of_vertHom {Z : Over (U ⨯ V)}
    (R : (VertHom.presheaf hp h₁ h₂).RepresentableBy Z) :
    Nonempty ((SliceSourceFibre.presheaf hp hG' hG).RepresentableBy
      ((Over.map prod.snd).obj Z)) := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ : VertHom p (Over.forget (U ⨯ V)) (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G')
      (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) Z, ∀ (b : Over (U ⨯ V)) (t : VertHom p
        (Over.forget (U ⨯ V)) (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G')
        (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) b),
        ∃! g : b ⟶ Z, VertHom.restrict hp h₁ h₂ g ξ = t :=
    (nonempty_representableBy_iff _ Z).1 ⟨R⟩
  refine (nonempty_representableBy_iff _ _).2 ⟨toSliceHom ξ, fun a s => ?_⟩
  change ∃! f, SliceHom.restrict hp hG' hG f (toSliceHom ξ) = s
  let b : Over (U ⨯ V) := Over.mk (prod.lift s.k a.hom)
  let α : a ≅ (Over.map prod.snd).obj b := Over.isoMk (Iso.refl _) (by simp [b])
  obtain ⟨t, ht⟩ := exists_toSliceHom_eq (SliceHom.restrict hp hG' hG α.inv s)
    (by simp [b, α])
  obtain ⟨g, hg, hgu⟩ := hξ b t
  refine ⟨α.hom ≫ (Over.map prod.snd).map g, ?_, fun f₁ hf₁ => ?_⟩
  · dsimp only
    rw [SliceHom.restrict_comp, ← toSliceHom_restrict hp hG hG' h₁ h₂, hg, ht,
      ← SliceHom.restrict_comp, Iso.hom_inv_id, SliceHom.restrict_id]
  · beta_reduce at hf₁
    have hk₁ : s.k = f₁.left ≫ Z.hom ≫ prod.fst := SliceHom.k_eq_of_eq_restrict hp hG' hG hf₁.symm
    let g₁ : b ⟶ Z := Over.homMk f₁.left (by
      apply prod.hom_ext
      · simp [b, hk₁]
      · simpa [b] using Over.w f₁)
    have e₁ : α.inv ≫ f₁ = (Over.map prod.snd).map g₁ := by
      ext
      dsimp [α, g₁]
      try exact Category.id_comp _
    have e₂ : f₁ = α.hom ≫ (Over.map prod.snd).map g₁ := by
      rw [← e₁, Iso.hom_inv_id_assoc]
    have hres : VertHom.restrict hp h₁ h₂ g₁ ξ = t := by
      apply toSliceHom_injective
      rw [toSliceHom_restrict hp hG hG' h₁ h₂, ht, ← e₁, SliceHom.restrict_comp, hf₁]
    rw [e₂, hgu g₁ hres]

end ProdSlice

/-! ### (2) ⇒ (1): the presheaf of vertical morphisms is cut out of the presheaf of pairs -/

section Equalizer

variable {U : 𝒞} {Y₁ Y₂ : Over U ⥤ 𝒮}

/-- A vertical morphism `Y₁ a ⟶ Y₂ a` over `a : 𝒞/U` is a pair `(k, m)` with `k` the structure
morphism of `a`. -/
def vertToSliceHom {a : Over U} (φ : VertHom p (Over.forget U) Y₁ Y₂ a) :
    SliceHom p (Over.forget U) U Y₁ Y₂ a :=
  ⟨a.hom, φ.1, φ.2⟩

lemma vertToSliceHom_injective {a : Over U} {φ φ' : VertHom p (Over.forget U) Y₁ Y₂ a}
    (h : vertToSliceHom φ = vertToSliceHom φ') : φ = φ' :=
  Subtype.ext (eq_of_heq (SliceHom.mk.inj h).2)

lemma exists_vertToSliceHom_eq {a : Over U} (s : SliceHom p (Over.forget U) U Y₁ Y₂ a)
    (hk : s.k = a.hom) : ∃ φ : VertHom p (Over.forget U) Y₁ Y₂ a, vertToSliceHom φ = s := by
  obtain ⟨k, m, hv⟩ := s
  dsimp only at hk
  subst hk
  exact ⟨⟨m, hv⟩, rfl⟩

variable (hp : p.IsFiberedInGroupoids) (h₁ : Y₁ ⋙ p = Over.forget U)
  (h₂ : Y₂ ⋙ p = Over.forget U)

/-- `vertToSliceHom` commutes with restriction. -/
lemma vertToSliceHom_restrict {a' a : Over U} (h : a' ⟶ a)
    (φ : VertHom p (Over.forget U) Y₁ Y₂ a) :
    vertToSliceHom (VertHom.restrict hp h₁ h₂ h φ) =
      SliceHom.restrict hp h₁ h₂ h (vertToSliceHom φ) := by
  refine SliceHom.eq_restrict hp h₁ h₂ _ _ _ (Over.w h).symm ?_
  exact VertHom.restrict_fac hp h₁ h₂ h φ

/-- **(2) ⇒ (1) of Stacks 02YA, on presheaves.** If the presheaf on `𝒞/U` of pairs `(k, m)` with
`k : T ⟶ U` and `m : Y₁ T ⟶ Y₂ k` vertical is representable, so is the presheaf of vertical
morphisms `Y₁ ⟶ Y₂`: it is represented by the equalizer of the structure morphism of the
representing object and the morphism `k` of the universal pair. -/
theorem exists_representableBy_vertHom_of_presheaf [HasEqualizers 𝒞] {Z : Over U}
    (R : (SliceSourceFibre.presheaf hp h₁ h₂).RepresentableBy Z) :
    ∃ Z' : Over U, Nonempty ((VertHom.presheaf hp h₁ h₂).RepresentableBy Z') := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ : SliceHom p (Over.forget U) U Y₁ Y₂ Z,
      ∀ (a : Over U) (s : SliceHom p (Over.forget U) U Y₁ Y₂ a),
        ∃! g : a ⟶ Z, SliceHom.restrict hp h₁ h₂ g ξ = s :=
    (nonempty_representableBy_iff _ Z).1 ⟨R⟩
  let ι := equalizer.ι ξ.k Z.hom
  let Z' : Over U := Over.mk (ι ≫ Z.hom)
  let j : Z' ⟶ Z := Over.homMk ι
  obtain ⟨ξ', hξ'⟩ := exists_vertToSliceHom_eq (SliceHom.restrict hp h₁ h₂ j ξ)
    (equalizer.condition ξ.k Z.hom)
  have key : ∀ {a : Over U} (f : a ⟶ Z'), vertToSliceHom (VertHom.restrict hp h₁ h₂ f ξ') =
      SliceHom.restrict hp h₁ h₂ (f ≫ j) ξ := fun f => by
    rw [vertToSliceHom_restrict, hξ', SliceHom.restrict_comp]
  refine ⟨Z', (nonempty_representableBy_iff _ _).2
    ⟨ξ', fun a (φ : VertHom p (Over.forget U) Y₁ Y₂ a) => ?_⟩⟩
  change ∃! f, VertHom.restrict hp h₁ h₂ f ξ' = φ
  obtain ⟨g, hg, hgu⟩ := hξ a (vertToSliceHom φ)
  have hk : a.hom = g.left ≫ ξ.k := SliceHom.k_eq_of_eq_restrict hp h₁ h₂ hg.symm
  let l : a.left ⟶ equalizer ξ.k Z.hom :=
    equalizer.lift g.left (hk.symm.trans (Over.w g).symm)
  let f : a ⟶ Z' := Over.homMk l (by simp [Z', l, ι])
  have hfj : f ≫ j = g := by ext; simp [f, j, l, ι]
  refine ⟨f, vertToSliceHom_injective (by rw [key, hfj, hg]), fun f₁ hf₁ => ?_⟩
  beta_reduce at hf₁
  have h₁j : f₁ ≫ j = g := hgu _ (by beta_reduce; rw [← key, hf₁])
  ext
  have := congrArg CommaMorphism.left (h₁j.trans hfj.symm)
  simp only [Over.comp_left, j, Over.homMk_left] at this
  exact (cancel_mono ι).1 this

end Equalizer

/-- **Stacks 02YA.** Let `𝒞` be a category with products of pairs and fibre products, and let
`p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids. The diagonal `𝒮 ⥤ 𝒮 × 𝒮` into the 2-fibre product
`𝒮 × 𝒮 = 𝒮 ×_𝒞 𝒮` over the final object `𝟭 𝒞` (Stacks 0040) is representable (Stacks 02Y7) if and
only if, for every object `U` of `𝒞`, every 1-morphism `G : 𝒞/U ⥤ 𝒮` is representable.

The morphisms of `𝒞` and of `𝒮` are taken in one universe. -/
@[stacks 02YA]
theorem isRepresentableMorphism_diagonal_iff [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    (hp : p.IsFiberedInGroupoids) :
    IsRepresentableMorphism p (structureFunctor p p (𝟭 𝒞) p p) (diagonal (Functor.comp_id p)) ↔
      ∀ (U : 𝒞) (G : Over U ⥤ 𝒮), G ⋙ p = Over.forget U →
        IsRepresentableMorphism (Over.forget U) p G := by
  have : HasEqualizers 𝒞 := hasEqualizers_of_hasPullbacks_and_binary_products
  refine (isRepresentableMorphism_diag_iff hp).trans ⟨fun h U G hG => ?_, fun h U Y hY => ?_⟩
  · refine (isRepresentableMorphism_over_iff hp hG).2 fun V G' hG' => ?_
    have h₁ : (Over.map (prod.snd : U ⨯ V ⟶ V) ⋙ G') ⋙ p = Over.forget (U ⨯ V) := by
      rw [Functor.assoc, hG', Over.mapForget_eq]
    have h₂ : (Over.map (prod.fst : U ⨯ V ⟶ U) ⋙ G) ⋙ p = Over.forget (U ⨯ V) := by
      rw [Functor.assoc, hG, Over.mapForget_eq]
    obtain ⟨Z, ⟨R⟩⟩ := h (U ⨯ V)
      (lift p p (𝟭 𝒞) p p (Over.forget (U ⨯ V)) _ _ h₁ h₂ (eqToIso (h₁.trans h₂.symm))
        (fun b => IsHomLift.of_fac' _ _ _ (Functor.congr_obj h₁ b) (Functor.congr_obj h₂ b)
          (by simp [eqToHom_app])))
      rfl
    exact ⟨_, nonempty_representableBy_presheaf_of_vertHom hp hG hG' h₁ h₂ R⟩
  · obtain ⟨Z, ⟨R⟩⟩ := (isRepresentableMorphism_over_iff hp (h2' hY)).1 (h U _ (h2' hY)) U _
      (h1' hY)
    exact exists_representableBy_vertHom_of_presheaf hp (h1' hY) (h2' hY) R

end Stacks.RepresentableMorphism

end
