module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismEtale

/-!
# The morphism of self-intersections of a composite of smooth lifts

For a morphism `m = (f, f', γ_m) : ξ ⟶ η` of smooth lifts of étale opens of `W` (Stacks 0CJP),
`Φ_m : I'_ξ ⟶ I'_η` is the morphism of self-intersections `I'_ξ = U' ×_{x', 𝒳', x'} U'`
induced by `f'` and `γ_m` (`AlgebraicGeometry.Stack.EtaleSmoothLift.selfIntersectionMap`). This
file shows that it is functorial: `Φ_{m ≫ n} = Φ_m ≫ Φ_n`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.selfIntersectionMap_comp`). The 2-cell bookkeeping is
the strict-bicategory lemma `CategoryTheory.Bicategory.whiskerLeft_comp_eq_of_selfIntersectionMap`.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Bicategory

universe w₀ v₀ u₀

variable {𝔅 : Type u₀} [Bicategory.{w₀, v₀} 𝔅] [Bicategory.Strict 𝔅]

/-- Whiskering along two equal 1-morphisms, read along `eqToHom`s. -/
theorem whiskerLeft_eq_eqToHom_comp_whiskerLeft_of_eqs {T A C : 𝔅} {t t' : T ⟶ A} (h : t = t')
    {g g' : A ⟶ C} (η : g ⟶ g') (e₁ : t ≫ g = t' ≫ g) (e₂ : t' ≫ g' = t ≫ g') :
    t ◁ η = eqToHom e₁ ≫ (t' ◁ η) ≫ eqToHom e₂ := by
  subst h
  simp

/-- **The 2-cell of a composite of maps of self-intersections.** In a strict bicategory, let
`γP`, `γQ`, `γR` be 2-cells over `P ⇉ A`, `Q ⇉ B`, `R ⇉ D`, let `c : xA ⟶ f ≫ xB` and
`d : xB ⟶ g ≫ xD` be invertible, and let `Φ : P ⟶ Q` and `Ψ : Q ⟶ R` lie over `f` and `g` with
`Φ^*γQ = (qP^*c) ∘ γP ∘ (pP^*c⁻¹)` and `Ψ^*γR = (qQ^*d) ∘ γQ ∘ (pQ^*d⁻¹)`. Then
`(Φ ≫ Ψ)^*γR` is the transport of `γP` along the composite `c ≫ f^*d`. -/
theorem whiskerLeft_comp_eq_of_selfIntersectionMap {A B D P Q R C : 𝔅} {xA : A ⟶ C}
    {xB : B ⟶ C} {xD : D ⟶ C} {pP qP : P ⟶ A} {pQ qQ : Q ⟶ B} {pR qR : R ⟶ D}
    (γP : pP ≫ xA ⟶ qP ≫ xA) (γQ : pQ ≫ xB ⟶ qQ ≫ xB) (γR : pR ≫ xD ⟶ qR ≫ xD)
    {f : A ⟶ B} {g : B ⟶ D} (c : xA ⟶ f ≫ xB) [IsIso c] (d : xB ⟶ g ≫ xD) [IsIso d]
    {Φ : P ⟶ Q} {Ψ : Q ⟶ R} (hΦp : Φ ≫ pQ = pP ≫ f) (hΦq : Φ ≫ qQ = qP ≫ f)
    (hΨp : Ψ ≫ pR = pQ ≫ g) (hΨq : Ψ ≫ qR = qQ ≫ g)
    (hΦ : ∀ (e₁ : Φ ≫ pQ ≫ xB = pP ≫ f ≫ xB) (e₂ : qP ≫ f ≫ xB = Φ ≫ qQ ≫ xB),
      Φ ◁ γQ = eqToHom e₁ ≫ ((pP ◁ inv c) ≫ γP ≫ (qP ◁ c)) ≫ eqToHom e₂)
    (hΨ : ∀ (e₁ : Ψ ≫ pR ≫ xD = pQ ≫ g ≫ xD) (e₂ : qQ ≫ g ≫ xD = Ψ ≫ qR ≫ xD),
      Ψ ◁ γR = eqToHom e₁ ≫ ((pQ ◁ inv d) ≫ γQ ≫ (qQ ◁ d)) ≫ eqToHom e₂)
    (e₁ : (Φ ≫ Ψ) ≫ pR ≫ xD = pP ≫ f ≫ g ≫ xD)
    (e₂ : qP ≫ f ≫ g ≫ xD = (Φ ≫ Ψ) ≫ qR ≫ xD) :
    (Φ ≫ Ψ) ◁ γR =
      eqToHom e₁ ≫ ((pP ◁ inv (c ≫ (f ◁ d))) ≫ γP ≫ (qP ◁ (c ≫ (f ◁ d)))) ≫ eqToHom e₂ := by
  have h1 := whiskerLeft_eq_eqToHom_comp_whiskerLeft_of_eqs hΦp (inv d)
    (congrArg (· ≫ _) hΦp) (congrArg (· ≫ _) hΦp.symm)
  have h2 := whiskerLeft_eq_eqToHom_comp_whiskerLeft_of_eqs hΦq d
    (congrArg (· ≫ _) hΦq) (congrArg (· ≫ _) hΦq.symm)
  rw [comp_whiskerLeft, hΨ (by rw [← Strict.assoc Ψ pR, hΨp, Strict.assoc])
    (by rw [← Strict.assoc Ψ qR, hΨq, Strict.assoc])]
  simp only [whiskerLeft_comp, Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_eqToHom, Category.assoc]
  rw [hΦ (by rw [← Strict.assoc Φ pQ, hΦp, Strict.assoc])
      (by rw [← Strict.assoc Φ qQ, hΦq, Strict.assoc]),
    comp_whiskerLeft_symm Φ pQ, comp_whiskerLeft_symm Φ qQ, h1, h2, comp_whiskerLeft pP f,
    comp_whiskerLeft qP f]
  simp only [IsIso.inv_comp, inv_whiskerLeft, whiskerLeft_comp, Strict.associator_eqToIso,
    eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

end CategoryTheory.Bicategory

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] (G : 𝒞 ⥤ 𝒟)

/-- A commutative square of `𝒞`, mapped by `G` and followed by a morphism. -/
theorem map_comp_map_comp_eq_of_square {a b c d : 𝒞} {h : a ⟶ b} {k : b ⟶ d} {h' : a ⟶ c}
    {k' : c ⟶ d} (e : h ≫ k = h' ≫ k') {Z : 𝒟} (z : G.obj d ⟶ Z) :
    G.map h ≫ G.map k ≫ z = G.map h' ≫ G.map k' ≫ z := by
  rw [← G.map_comp_assoc, e, G.map_comp_assoc]

/-- A commutative square of `𝒞`, mapped by `G`. -/
theorem map_comp_eq_of_square {a b c d : 𝒞} {h : a ⟶ b} {k : b ⟶ d} {h' : a ⟶ c}
    {k' : c ⟶ d} (e : h ≫ k = h' ≫ k') : G.map h ≫ G.map k = G.map h' ≫ G.map k' := by
  rw [← G.map_comp, e, G.map_comp]

/-- A commutative pentagon of `𝒞` with three edges on each side, mapped by `G` and followed by a
morphism. -/
theorem map_comp_map_comp_map_comp_eq {a b c d b' c' : 𝒞} {h₁ : a ⟶ b} {h₂ : b ⟶ c}
    {h₃ : c ⟶ d} {k₁ : a ⟶ b'} {k₂ : b' ⟶ c'} {k₃ : c' ⟶ d} (e : h₁ ≫ h₂ ≫ h₃ = k₁ ≫ k₂ ≫ k₃)
    {Z : 𝒟} (z : G.obj d ⟶ Z) :
    G.map h₁ ≫ G.map h₂ ≫ G.map h₃ ≫ z = G.map k₁ ≫ G.map k₂ ≫ G.map k₃ ≫ z := by
  simp only [← Category.assoc, ← G.map_comp]
  rw [Category.assoc h₁, e, ← Category.assoc]

end CategoryTheory.Functor

namespace CategoryTheory

/-- Equal morphisms inside two `eqToHom`-sandwiches, one of them nested. -/
theorem eqToHom_comp_comp_eqToHom_eq_nested {𝒞 : Type*} [Category 𝒞]
    {A A₁ B₁ B C₁ C₂ D₂ D₁ : 𝒞} {X X' : A₁ ⟶ B₁} (a : A = A₁) (b : B₁ = B) (p : A = C₁)
    (q : C₁ = C₂) (r : C₂ = A₁) (s : B₁ = D₂) (t : D₂ = D₁) (u : D₁ = B) (h : X = X') :
    eqToHom a ≫ X ≫ eqToHom b =
      eqToHom p ≫ (eqToHom q ≫ (eqToHom r ≫ X' ≫ eqToHom s) ≫ eqToHom t) ≫ eqToHom u := by
  subst h a b p q s t
  simp

end CategoryTheory

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

open Bicategory

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

/-- The defining 2-cell of `Φ_m`, solved for `Φ_m^*γ_ξ`. -/
theorem whiskerLeft_selfIntersectionMap_eq {ξ η : EtaleSmoothLift B S hS ι hι W x hx}
    (m : Hom ξ η)
    (e₁ : (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map η.selfIntersection.fst ≫ η.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫
        (algebraicSpaceStackFunctor B S hS).map m.ambient ≫ η.ambientMap)
    (e₂ : (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫
        (algebraicSpaceStackFunctor B S hS).map m.ambient ≫ η.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map η.selfIntersection.snd ≫ η.ambientMap) :
    (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ◁
        η.selfIntersection.iso.hom =
      eqToHom e₁ ≫ (((algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ◁
          inv m.comm) ≫ ξ.selfIntersection.iso.hom ≫
        ((algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ◁ m.comm)) ≫
        eqToHom e₂ := by
  have h := (selfIntersectionMapIso_hom m).symm.trans (selfIntersectionMap_spec m
    ((congrArg (fun t => (algebraicSpaceStackFunctor B S hS).map t ≫ η.ambientMap)
      (selfIntersectionMap_fst m)).symm.trans (Functor.map_comp_assoc _ _ _ _))
    ((Functor.map_comp_assoc _ _ _ _).symm.trans
      (congrArg (fun t => (algebraicSpaceStackFunctor B S hS).map t ≫ η.ambientMap)
        (selfIntersectionMap_snd m))))
  exact eq_eqToHom_comp_comp_eqToHom_of_sandwich _ _ _ _ h.symm

/-- **`Φ` is functorial**: the morphism of self-intersections induced by a composite of smooth
lifts is the composite of the induced morphisms, `Φ_{m ≫ n} = Φ_m ≫ Φ_n`. -/
theorem selfIntersectionMap_comp {ξ η ζ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom ξ η)
    (n : Hom η ζ) :
    selfIntersectionMap (m.comp n) = selfIntersectionMap m ≫ selfIntersectionMap n := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have hfst : selfIntersectionMap m ≫ selfIntersectionMap n ≫ ζ.selfIntersection.fst =
      ξ.selfIntersection.fst ≫ m.ambient ≫ n.ambient := by
    rw [selfIntersectionMap_fst, ← Category.assoc, selfIntersectionMap_fst, Category.assoc]
  have hp : selfIntersectionMap (m.comp n) ≫ ζ.selfIntersection.fst =
      (selfIntersectionMap m ≫ selfIntersectionMap n) ≫ ζ.selfIntersection.fst := by
    rw [selfIntersectionMap_fst, Category.assoc, hfst]
    rfl
  have hsnd : selfIntersectionMap m ≫ selfIntersectionMap n ≫ ζ.selfIntersection.snd =
      ξ.selfIntersection.snd ≫ m.ambient ≫ n.ambient := by
    rw [selfIntersectionMap_snd, ← Category.assoc, selfIntersectionMap_snd, Category.assoc]
  have hq : selfIntersectionMap (m.comp n) ≫ ζ.selfIntersection.snd =
      (selfIntersectionMap m ≫ selfIntersectionMap n) ≫ ζ.selfIntersection.snd := by
    rw [selfIntersectionMap_snd, Category.assoc, hsnd]
    rfl
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ζ.selfIntersection.isTwoFibreProduct.some hp hq
    (F.map_comp_map_comp_eq_of_comp_eq hp ζ.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq ζ.ambientMap).symm ?_
  have hmn := whiskerLeft_selfIntersectionMap_eq (m.comp n)
    (F.map_comp_map_comp_eq_of_square (selfIntersectionMap_fst (m.comp n)) ζ.ambientMap)
    (F.map_comp_map_comp_eq_of_square (selfIntersectionMap_snd (m.comp n)) ζ.ambientMap).symm
  have hcomp := Bicategory.whiskerLeft_comp_eq_of_selfIntersectionMap ξ.selfIntersection.iso.hom
    η.selfIntersection.iso.hom ζ.selfIntersection.iso.hom m.comm n.comm
    (F.map_comp_eq_of_square (selfIntersectionMap_fst m))
    (F.map_comp_eq_of_square (selfIntersectionMap_snd m))
    (F.map_comp_eq_of_square (selfIntersectionMap_fst n))
    (F.map_comp_eq_of_square (selfIntersectionMap_snd n))
    (whiskerLeft_selfIntersectionMap_eq m) (whiskerLeft_selfIntersectionMap_eq n)
    ((Bicategory.Strict.assoc _ _ _).trans (F.map_comp_map_comp_map_comp_eq hfst ζ.ambientMap))
    ((F.map_comp_map_comp_map_comp_eq hsnd ζ.ambientMap).symm.trans
      (Bicategory.Strict.assoc _ _ _).symm)
  have hw := Bicategory.whiskerLeft_eq_eqToHom_comp_whiskerLeft_of_eqs
    (F.map_comp (selfIntersectionMap m) (selfIntersectionMap n)) ζ.selfIntersection.iso.hom
    (congrArg (· ≫ F.map ζ.selfIntersection.fst ≫ ζ.ambientMap)
      (F.map_comp (selfIntersectionMap m) (selfIntersectionMap n)))
    (congrArg (· ≫ F.map ζ.selfIntersection.snd ≫ ζ.ambientMap)
      (F.map_comp (selfIntersectionMap m) (selfIntersectionMap n)).symm)
  rw [hmn, hw, hcomp]
  exact eqToHom_comp_comp_eqToHom_eq_nested _ _ _ _ _ _ _ _ rfl

end AlgebraicGeometry.Stack.EtaleSmoothLift
