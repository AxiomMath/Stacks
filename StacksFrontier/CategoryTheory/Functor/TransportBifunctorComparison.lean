module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering

/-!
# Transporting a comparison of bifunctors along comparison functors

Let `L_s : C_s ⥤ D_s` and `L_l : C_l ⥤ D_l` be functors carrying bifunctors `T_s, T_l` to
`T'_s, T'_l`, related by functors `G_C : C_s ⥤ C_l`, `G_D : D_s ⥤ D_l` and isomorphisms
`L_s ⋙ G_D ≅ G_C ⋙ L_l`, `G_C ⋙ T_l ⋙ (- ⋙ G_C) ≅ T_s ⋙ (- ⋙ G_C)` and the same on `D`. A natural
comparison `L_s(T_s(K, L)) ⟶ T'_s(L_s K, L_s L)` then has a transport to the `G_C`-images, and a
natural comparison `L_l(T_l(K, L)) ⟶ T'_l(L_l K, L_l L)` agrees with that transport at all images
as soon as it does at the images of a family of objects to which every object is isomorphic.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace CategoryTheory.Functor

variable {Cs Cl Ds Dl : Type*} [Category Cs] [Category Cl] [Category Ds] [Category Dl]
  (GC : Cs ⥤ Cl) (GD : Ds ⥤ Dl) {Ts : Cs ⥤ Cs ⥤ Cs} {Tl : Cl ⥤ Cl ⥤ Cl}
  {Ts' : Ds ⥤ Ds ⥤ Ds} {Tl' : Dl ⥤ Dl ⥤ Dl} {Ls : Cs ⥤ Ds} {Ll : Cl ⥤ Dl}
  (pb : Ls ⋙ GD ≅ GC ⋙ Ll)
  (τC : GC ⋙ Tl ⋙ (whiskeringLeft _ _ _).obj GC ≅ Ts ⋙ (whiskeringRight _ _ _).obj GC)
  (τD : GD ⋙ Tl' ⋙ (whiskeringLeft _ _ _).obj GD ≅ Ts' ⋙ (whiskeringRight _ _ _).obj GD)
  (δs : uncurry.obj Ts ⋙ Ls ⟶ Ls.prod Ls ⋙ uncurry.obj Ts')

/-- The action of a bifunctor on a pair of morphisms is functorial in the pair. -/
lemma bifunctor_map_comp_map {C E : Type*} [Category C] [Category E] (T : C ⥤ C ⥤ E)
    {K₁ K₂ K₃ L₁ L₂ L₃ : C} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (c : K₂ ⟶ K₃) (d : L₂ ⟶ L₃) :
    (T.map a).app L₁ ≫ (T.obj K₂).map b ≫ (T.map c).app L₂ ≫ (T.obj K₃).map d =
      (T.map (a ≫ c)).app L₁ ≫ (T.obj K₃).map (b ≫ d) := by
  rw [← NatTrans.naturality_assoc]
  simp

/-- The inverse of a comparison `G ⋙ T_l ⋙ (- ⋙ G) ≅ T_s ⋙ (- ⋙ G)` is natural in both
variables. -/
@[reassoc]
lemma whiskering_iso_inv_naturality {Cs Cl : Type*} [Category Cs] [Category Cl] (GC : Cs ⥤ Cl)
    {Ts : Cs ⥤ Cs ⥤ Cs} {Tl : Cl ⥤ Cl ⥤ Cl}
    (τC : GC ⋙ Tl ⋙ (whiskeringLeft _ _ _).obj GC ≅ Ts ⋙ (whiskeringRight _ _ _).obj GC)
    {K K' L L' : Cs} (u : K ⟶ K') (v : L ⟶ L') :
    GC.map ((Ts.map u).app _ ≫ (Ts.obj _).map v) ≫ (τC.inv.app K').app L' =
      (τC.inv.app K).app L ≫ (Tl.map (GC.map u)).app _ ≫ (Tl.obj _).map (GC.map v) := by
  have a := NatTrans.congr_app (τC.inv.naturality u) L
  have b := (τC.inv.app K').naturality v
  dsimp at a b
  rw [Functor.map_comp, Category.assoc, b, reassoc_of% a]

/-- The image under a functor of an equation of composites. -/
lemma map_comp_eq_of_eq {C E : Type*} [Category C] [Category E] (G : C ⥤ E)
    {S T T' T'' W S₁ V : C} {a : S ⟶ T} {n₁ : T ⟶ T'} {n₂ : T' ⟶ T''} {c : T'' ⟶ W}
    {ℓ : S ⟶ S₁} {p : S₁ ⟶ V} {q : V ⟶ W} (h : a ≫ n₁ ≫ n₂ ≫ c = ℓ ≫ p ≫ q) :
    G.map a ≫ G.map (n₁ ≫ n₂) ≫ G.map c = G.map ℓ ≫ G.map p ≫ G.map q := by
  simp only [← G.map_comp, Category.assoc, h]

/-- The transport of the comparison `δs` to the images under `GC`. -/
noncomputable def transportBifunctorComparison (K L : Cs) :
    Ll.obj ((Tl.obj (GC.obj K)).obj (GC.obj L)) ⟶
      (Tl'.obj (Ll.obj (GC.obj K))).obj (Ll.obj (GC.obj L)) :=
  Ll.map ((τC.hom.app K).app L) ≫ pb.inv.app ((Ts.obj K).obj L) ≫ GD.map (δs.app (K, L)) ≫
    (τD.inv.app (Ls.obj K)).app (Ls.obj L) ≫ (Tl'.map (pb.hom.app K)).app _ ≫
    (Tl'.obj _).map (pb.hom.app L)

/-- The transport of the comparison `δs` is natural in both variables with respect to morphisms
in the image of `GC`. -/
lemma transportBifunctorComparison_natural {K K' L L' : Cs} (u : K ⟶ K') (v : L ⟶ L') :
    Ll.map ((Tl.map (GC.map u)).app _ ≫ (Tl.obj _).map (GC.map v)) ≫
        transportBifunctorComparison GC GD pb τC τD δs K' L' =
      transportBifunctorComparison GC GD pb τC τD δs K L ≫
        (Tl'.map (Ll.map (GC.map u))).app _ ≫ (Tl'.obj _).map (Ll.map (GC.map v)) := by
  have e1 : (Tl.map (GC.map u)).app _ ≫ (Tl.obj _).map (GC.map v) ≫ (τC.hom.app K').app L' =
      (τC.hom.app K).app L ≫ GC.map ((Ts.map u).app L ≫ (Ts.obj K').map v) := by
    have a := NatTrans.congr_app (τC.hom.naturality u) L
    have b := (τC.hom.app K').naturality v
    dsimp at a b
    rw [b, reassoc_of% a, Functor.map_comp]
  have e2 := pb.inv.naturality ((Ts.map u).app L ≫ (Ts.obj K').map v)
  have e3 := δs.naturality (u ×ₘ v)
  have e4 := whiskering_iso_inv_naturality GD τD (Ls.map u) (Ls.map v)
  have e5 : (Tl'.map (GD.map (Ls.map u))).app _ ≫ (Tl'.obj _).map (GD.map (Ls.map v)) ≫
      (Tl'.map (pb.hom.app K')).app _ ≫ (Tl'.obj _).map (pb.hom.app L') =
      (Tl'.map (pb.hom.app K)).app _ ≫ (Tl'.obj _).map (pb.hom.app L) ≫
        (Tl'.map (Ll.map (GC.map u))).app _ ≫ (Tl'.obj _).map (Ll.map (GC.map v)) := by
    have hu := pb.hom.naturality u
    have hv := pb.hom.naturality v
    dsimp at hu hv
    simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp, hu, NatTrans.naturality_assoc, hv]
    rfl
  dsimp at e2 e3
  simp only [transportBifunctorComparison, Category.assoc]
  rw [← Ll.map_comp_assoc, Category.assoc, e1, Ll.map_comp_assoc, reassoc_of% e2,
    ← GD.map_comp_assoc, e3, GD.map_comp_assoc, reassoc_of% e4, e5]
  rfl

/-- **A natural comparison agrees with the transport of `δs` at all images as soon as it does at
the images of a family of objects to which every object is isomorphic.** -/
theorem eq_transportBifunctorComparison
    (δl : ∀ K L : Cl, Ll.obj ((Tl.obj K).obj L) ⟶ (Tl'.obj (Ll.obj K)).obj (Ll.obj L))
    (hδl : ∀ {K K' L L' : Cl} (u : K ⟶ K') (v : L ⟶ L'),
      Ll.map ((Tl.map u).app _ ≫ (Tl.obj _).map v) ≫ δl K' L' =
        δl K L ≫ (Tl'.map (Ll.map u)).app _ ≫ (Tl'.obj _).map (Ll.map v))
    (good : Cs → Prop) (hgood : ∀ K, ∃ K', good K' ∧ Nonempty (K' ≅ K))
    (h : ∀ K L, good K → good L →
      δl (GC.obj K) (GC.obj L) = transportBifunctorComparison GC GD pb τC τD δs K L)
    (K L : Cs) :
    δl (GC.obj K) (GC.obj L) = transportBifunctorComparison GC GD pb τC τD δs K L := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := hgood K
  obtain ⟨L', hL', ⟨eL⟩⟩ := hgood L
  rw [← cancel_epi (Ll.map ((Tl.map (GC.map eK.hom)).app _ ≫ (Tl.obj _).map (GC.map eL.hom))),
    hδl, transportBifunctorComparison_natural, h K' L' hK' hL']

/-- Pasting commutative squares: cancelling the monomorphism `nl₁ ≫ nl₂ ≫ cl`, the given
equations of composites identify `A` with `m₁ ≫ m₂ ≫ gd ≫ t ≫ k₁ ≫ k₂`. -/
theorem eq_comp_of_squares {C : Type*} [Category C]
    {S S' S₁ T₁ T₁' T₂ T₂' T' T'' U U' U'' U₁ V W : C}
    {A : S ⟶ T₁} {nl₁ : T₁ ⟶ T₁'} {nl₂ : T₁' ⟶ T₂} {cl : T₂ ⟶ W} {ℓ : S ⟶ S₁} {p : S₁ ⟶ V}
    {q : V ⟶ W} {m₁ : S ⟶ S'} {m₂ : S' ⟶ U} {gd : U ⟶ U'} {t : U' ⟶ T'} {k₁ : T' ⟶ T₂'}
    {k₂ : T₂' ⟶ T₁} {n'₁ : T' ⟶ T''} {n'₂ : T'' ⟶ T₂} {gn : U' ⟶ U''} {gc : U'' ⟶ W}
    {gℓ : U ⟶ U₁} {gp : U₁ ⟶ V}
    {ℓ' : S' ⟶ S₁} {m₂' : S₁ ⟶ U₁} (hm : Mono (nl₁ ≫ nl₂ ≫ cl))
    (hls : A ≫ nl₁ ≫ nl₂ ≫ cl = ℓ ≫ p ≫ q) (f₁ : k₁ ≫ k₂ ≫ nl₁ ≫ nl₂ = n'₁ ≫ n'₂)
    (f₂ : t ≫ n'₁ ≫ n'₂ ≫ cl = gn ≫ gc) (f₃ : gd ≫ gn ≫ gc = gℓ ≫ gp ≫ q)
    (f₄ : m₂ ≫ gℓ = ℓ' ≫ m₂') (f₅ : m₂' ≫ gp = p) (f₆ : m₁ ≫ ℓ' = ℓ) :
    A = m₁ ≫ m₂ ≫ gd ≫ t ≫ k₁ ≫ k₂ := by
  rw [← cancel_mono (nl₁ ≫ nl₂ ≫ cl), hls]
  simp only [Category.assoc]
  rw [reassoc_of% f₁, f₂, f₃, reassoc_of% f₄, reassoc_of% f₅, reassoc_of% f₆]

end CategoryTheory.Functor

