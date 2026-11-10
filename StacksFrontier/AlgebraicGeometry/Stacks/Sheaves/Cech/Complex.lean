module

public import Mathlib.CategoryTheory.Limits.Final
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RelativeCechComplex
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksCore.Tactic.StacksAttribute

/-!
# The Čech complex of a covering of a category fibred in groupoids

Let `f : U ⥤ X` be a functor over a base category `C`, thought of as a covering of `X`. Its
Čech nerve has in degree `n` the category `Stacks.RelativeCech.Tuple p f n` of `n + 1` objects
of `U` lying over a common object of `X` with vertical comparison isomorphisms; this is the
simplicial object `U_•` of the source. The *Čech complex* `Č(U → X, F)` of an abelian presheaf
`F` on `X` is the cochain complex of the cosimplicial object `n ↦ Γ(U_n, f_n⁻¹F)`, whose
differential is the alternating sum of the coface pullbacks.

A `2`-commutative square of such coverings induces a morphism of Čech complexes; it is an
isomorphism when the two horizontal functors are equivalences, and `2`-isomorphic coverings of
`X` have isomorphic Čech complexes.

## Main definitions

* `Stacks.Cech.term`: `Γ(U_n, f_n⁻¹F)`, the degree `n` term.
* `Stacks.Cech.cosimplicial`: the cosimplicial object `n ↦ Γ(U_n, f_n⁻¹F)`.
* `Stacks.Cech.complex`: the Čech complex `Č(U → X, F)`.
* `Stacks.Cech.nerveMap`: the functor `V_n ⥤ U_n` of Čech nerves induced by a `2`-commutative
  square.
* `Stacks.Cech.complexPullbackMap`: the induced morphism of Čech complexes.

## Main results

* `Stacks.Cech.complexPullbackMap` and `Stacks.Cech.complexPullbackMap_π` are part (1): the
  morphism of Čech complexes attached to a `2`-commutative square, and the formula pinning it
  down degreewise on the limit cones.
* `Stacks.Cech.isIso_complexPullbackMap` is part (2).
* `Stacks.Cech.nonempty_complexIso_of_natIso` is part (3).
* `Stacks.Cech.complex_d` records that the differential is the alternating sum of the coface
  pullback maps.

## Implementation notes

The Čech nerve is not redefined: the tuples, their projection `f_n` and their strict reindexing
functors are those of `Stacks.RelativeCech`, where the comparison isomorphisms of a tuple are
required to lie over an identity of the base. That verticality is exactly what makes `U_n` the
`n`-fold `2`-fibre product of `f` *over* the base. The source works over `(Sch/S)_{fppf}` with
categories fibred in groupoids; everything here is stated over an arbitrary base category `C`,
with the fibred-in-groupoids hypothesis imposed only where it is used.

Global sections of a presheaf on a category are its limit, so the coefficient category is any
category with limits of the shapes that occur, preadditive once complexes are formed, rather
than `AddCommGrpCat`; abelian presheaves are the case `A = AddCommGrpCat`. Inverse image of a
presheaf along a `1`-morphism is restriction, `e⁻¹F = e.op ⋙ F`.

The `2`-commutativity of the square over the base is expressed by verticality of the components
of the `2`-morphism `α : h ⋙ f ≅ g ⋙ e`, together with `e ⋙ pX = pY` saying that `e` is a
`1`-morphism over the base. That single hypothesis already forces `pX (f (h v)) = pX (e (g v))`,
so no separate equality of composites is needed.

Part (1) is a construction, so it is given by a definition together with the lemma
`Stacks.Cech.complexPullbackMap_π` that characterises it; the two together are the content of
the tag. Parts (2) and (3) then speak about that same map. The hypotheses are kept to those the
statements use, which for parts (2) and (3) is the fibred-in-groupoids condition on the source
of the covering being compared.

## References

* [Stacks Project, Tag 06X5](https://stacks.math.columbia.edu/tag/06X5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open Stacks.RelativeCech (Tuple)
open scoped Simplicial

namespace Stacks.Cech

universe vA vC vU vV vX vY uA uC uU uV uX uY

variable {A : Type uA} [Category.{vA} A]
  {C : Type uC} [Category.{vC} C]
  {U : Type uU} [Category.{vU} U]
  {V : Type uV} [Category.{vV} V]
  {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y]

/-- A morphism of Čech tuples is determined by its target component and its source
components. -/
public theorem tupleHom_ext {p : X ⥤ C} {f : U ⥤ X} {n : ℕ} {a b : Tuple p f n}
    {φ ψ : Tuple.Hom p f a b} (h₁ : φ.target = ψ.target) (h₂ : φ.source = ψ.source) :
    φ = ψ := by
  obtain ⟨t₁, s₁, w₁⟩ := φ
  obtain ⟨t₂, s₂, w₂⟩ := ψ
  dsimp only at h₁ h₂
  subst h₁
  subst h₂
  rfl

/-- A compatible target isomorphism and family of source isomorphisms assemble into an
isomorphism of Čech tuples. -/
public def tupleIso {p : X ⥤ C} {f : U ⥤ X} {n : ℕ} {a b : Tuple p f n}
    (t : a.target ≅ b.target) (s : ∀ i, a.source i ≅ b.source i)
    (w : ∀ i, f.map (s i).hom ≫ (b.comparison i).hom = (a.comparison i).hom ≫ t.hom) :
    a ≅ b where
  hom := ⟨t.hom, fun i => (s i).hom, w⟩
  inv := ⟨t.inv, fun i => (s i).inv, fun i => by
    apply (cancel_mono t.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← w i, ← Category.assoc, ← f.map_comp]
    simp⟩
  hom_inv_id := tupleHom_ext t.hom_inv_id (funext fun i => (s i).hom_inv_id)
  inv_hom_id := tupleHom_ext t.inv_hom_id (funext fun i => (s i).inv_hom_id)

/-- In a category fibred in groupoids over `C`, an isomorphism `g v ≅ y` can be corrected by an
isomorphism of `V` so as to become vertical over `C`. -/
public theorem exists_vertical_comparison (p : Y ⥤ C) (g : V ⥤ Y)
    (hp : (g ⋙ p).IsFiberedInGroupoids) {v : V} {y : Y} (β : g.obj v ≅ y) :
    ∃ (v' : V) (η : v' ≅ v), p.IsHomLift (𝟙 (p.obj y)) ((g.mapIso η ≪≫ β).hom) := by
  obtain ⟨v', _, η, hη⟩ := hp.exists_iso_lift (p.mapIso β)
  have hlift : p.IsHomLift (p.mapIso β).hom (g.mapIso η).hom :=
    (Functor.isHomLift_comp_iff g p _ _).mp hη
  have hinv : p.IsHomLift (p.map β.inv) (g.map η.inv) :=
    IsHomLift.inv_lift_inv p (p.mapIso β) (g.mapIso η)
  refine ⟨v', η.symm, ?_⟩
  change p.IsHomLift (𝟙 (p.obj y)) (g.map η.inv ≫ β.hom)
  simpa only [← p.map_comp, β.inv_hom_id, p.map_id] using
    (IsHomLift.comp p (p.map β.inv) (p.map β.hom) (g.map η.inv) β.hom)

section Cosimplicial

variable (p : X ⥤ C) (f : U ⥤ X) (F : Xᵒᵖ ⥤ A)
  [∀ n : ℕ, HasLimitsOfShape (Tuple p f n)ᵒᵖ A]

/-- `Γ(U_n, f_n⁻¹F)`, the degree `n` term of the Čech complex: the global sections, that is the
limit, of the restriction of `F` along the `n`-th projection of the Čech nerve. -/
@[reducible] public def term (n : ℕ) : A :=
  limit ((Tuple.projection p f n).op ⋙ F)

/-- Pullback along a simplicial reindexing of Čech tuples. -/
public def reindexMap {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) : term p f F m ⟶ term p f F n :=
  limit.pre ((Tuple.projection p f m).op ⋙ F) (Tuple.reindex p f φ.toOrderHom).op

/-- A section of a reindexing map is the original section reindexed. -/
@[simp] public theorem reindexMap_π {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) (j : (Tuple p f n)ᵒᵖ) :
    reindexMap p f F φ ≫ limit.π ((Tuple.projection p f n).op ⋙ F) j =
      limit.π ((Tuple.projection p f m).op ⋙ F)
        ((Tuple.reindex p f φ.toOrderHom).op.obj j) :=
  limit.pre_π _ _ j

/-- Reindexing along an identity does nothing. -/
public theorem reindexMap_id (n : ℕ) : reindexMap p f F (𝟙 ⦋n⦌) = 𝟙 (term p f F n) := by
  refine limit.hom_ext fun j => ?_
  rw [Category.id_comp, reindexMap_π]
  rfl

/-- Reindexing is compatible with composition. -/
public theorem reindexMap_comp {l m n : ℕ} (φ : ⦋l⦌ ⟶ ⦋m⦌) (ψ : ⦋m⦌ ⟶ ⦋n⦌) :
    reindexMap p f F (φ ≫ ψ) = reindexMap p f F φ ≫ reindexMap p f F ψ := by
  refine limit.hom_ext fun j => ?_
  rw [Category.assoc, reindexMap_π, reindexMap_π, reindexMap_π]
  rfl

/-- The cosimplicial object `n ↦ Γ(U_n, f_n⁻¹F)` underlying the Čech complex. -/
public def cosimplicial : CosimplicialObject A where
  obj n := term p f F n.len
  map φ := reindexMap p f F φ
  map_id n := reindexMap_id p f F n.len
  map_comp φ ψ := reindexMap_comp p f F φ ψ

/-- The coface maps of the Čech cosimplicial object are the coface pullbacks. -/
@[simp] public theorem cosimplicial_δ {n : ℕ} (i : Fin (n + 2)) :
    (cosimplicial p f F).δ i = reindexMap p f F (SimplexCategory.δ i) := rfl

end Cosimplicial

section Complex

variable [Preadditive A] (p : X ⥤ C) (f : U ⥤ X) (F : Xᵒᵖ ⥤ A)
  [∀ n : ℕ, HasLimitsOfShape (Tuple p f n)ᵒᵖ A]

/-- The Čech complex `Č(U → X, F)`: the cochain complex of the cosimplicial object
`n ↦ Γ(U_n, f_n⁻¹F)`. -/
public def complex : CochainComplex A ℕ :=
  (alternatingCofaceMapComplex A).obj (cosimplicial p f F)

/-- The degree `n` term of the Čech complex is `Γ(U_n, f_n⁻¹F)`. -/
@[simp] public theorem complex_X (n : ℕ) : (complex p f F).X n = term p f F n := rfl

/-- The differential of the Čech complex is the alternating sum of the coface pullback maps. -/
public theorem complex_d (n : ℕ) :
    (complex p f F).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosimplicial p f F).δ i := by
  simp [complex, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
    AlternatingCofaceMapComplex.objD]

end Complex

section Square

variable (pX : X ⥤ C) (pY : Y ⥤ C) (f : U ⥤ X) (g : V ⥤ Y) (h : V ⥤ U) (e : Y ⥤ X)

/-- Naturality of a `2`-isomorphism `h ⋙ f ≅ g ⋙ e`, stated with the functors applied. -/
private theorem map_comp_naturality {f : U ⥤ X} {g : V ⥤ Y} {h : V ⥤ U} {e : Y ⥤ X}
    (α : h ⋙ f ≅ g ⋙ e) {v v' : V} (k : v ⟶ v') :
    f.map (h.map k) ≫ α.hom.app v' = α.hom.app v ≫ e.map (g.map k) :=
  α.hom.naturality k

/-- The functor `V_n ⥤ U_n` between Čech nerves induced by a `2`-commutative square: it sends
`(v_0, …, v_n, y, β_0, …, β_n)` to `(h v_0, …, h v_n, e y, e β_0 ∘ α_{v_0}, …, e β_n ∘ α_{v_n})`.
-/
public def nerveMap (α : h ⋙ f ≅ g ⋙ e) (he : e ⋙ pX = pY)
    (hα : ∀ v : V, pX.IsHomLift (𝟙 (pX.obj (f.obj (h.obj v)))) (α.hom.app v)) (n : ℕ) :
    Tuple pY g n ⥤ Tuple pX f n where
  obj a :=
    { target := e.obj a.target
      source := fun i => h.obj (a.source i)
      comparison := fun i => α.app (a.source i) ≪≫ e.mapIso (a.comparison i)
      comparison_lift := fun i => by
        have key : (e ⋙ pX).IsHomLift (𝟙 ((e ⋙ pX).obj a.target)) (a.comparison i).hom := by
          rw [he]; exact a.comparison_lift i
        have h₂ : pX.IsHomLift (𝟙 (pX.obj (e.obj a.target))) (e.map (a.comparison i).hom) :=
          (Functor.isHomLift_comp_iff e pX _ _).mp key
        have h₁ := hα (a.source i)
        exact IsHomLift.comp_lift_id_left' pX
          (pX.obj (f.obj (h.obj (a.source i)))) (α.hom.app (a.source i))
          (𝟙 (pX.obj (e.obj a.target))) (e.map (a.comparison i).hom) }
  map {a b} k :=
    { target := e.map (Tuple.Hom.target k)
      source := fun i => h.map (Tuple.Hom.source k i)
      comparison_naturality := fun i => by
        have hnat := α.hom.naturality (Tuple.Hom.source k i)
        have hk := Tuple.Hom.comparison_naturality k i
        simp only [Functor.comp_map] at hnat
        dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app]
        rw [← Category.assoc, hnat, Category.assoc, ← e.map_comp, hk, e.map_comp,
          Category.assoc] }
  map_id a := tupleHom_ext (e.map_id a.target) (funext fun i => h.map_id (a.source i))
  map_comp k l := tupleHom_ext (e.map_comp _ _) (funext fun i => h.map_comp _ _)

variable (α : h ⋙ f ≅ g ⋙ e) (he : e ⋙ pX = pY)
  (hα : ∀ v : V, pX.IsHomLift (𝟙 (pX.obj (f.obj (h.obj v)))) (α.hom.app v))
  (F : Xᵒᵖ ⥤ A)
  [∀ n : ℕ, HasLimitsOfShape (Tuple pX f n)ᵒᵖ A]
  [∀ n : ℕ, HasLimitsOfShape (Tuple pY g n)ᵒᵖ A]

/-- Pullback of sections along the induced functor of Čech nerves, in a fixed degree. -/
public def pullbackTermMap (n : ℕ) : term pX f F n ⟶ term pY g (e.op ⋙ F) n :=
  limit.pre ((Tuple.projection pX f n).op ⋙ F) (nerveMap pX pY f g h e α he hα n).op

/-- The degreewise pullback map is pullback of sections along the induced functor of Čech
nerves. -/
@[simp] public theorem pullbackTermMap_π (n : ℕ) (j : (Tuple pY g n)ᵒᵖ) :
    pullbackTermMap pX pY f g h e α he hα F n ≫
        limit.π ((Tuple.projection pY g n).op ⋙ e.op ⋙ F) j =
      limit.π ((Tuple.projection pX f n).op ⋙ F)
        ((nerveMap pX pY f g h e α he hα n).op.obj j) :=
  limit.pre_π _ _ j

/-- The morphism of Čech cosimplicial objects induced by a `2`-commutative square. -/
public def cosimplicialPullbackMap :
    cosimplicial pX f F ⟶ cosimplicial pY g (e.op ⋙ F) where
  app n := pullbackTermMap pX pY f g h e α he hα F n.len
  naturality m n φ :=
    (limit.pre_pre ((Tuple.projection pX f m.len).op ⋙ F)
        (Tuple.reindex pX f φ.toOrderHom).op
        (nerveMap pX pY f g h e α he hα n.len).op).trans
      (limit.pre_pre ((Tuple.projection pX f m.len).op ⋙ F)
        (nerveMap pX pY f g h e α he hα m.len).op
        (Tuple.reindex pY g φ.toOrderHom).op).symm

/-- The induced functor of Čech nerves is faithful when both horizontal functors are. -/
public lemma nerveMap_faithful [h.Faithful] [e.Faithful] (n : ℕ) :
    (nerveMap pX pY f g h e α he hα n).Faithful where
  map_injective hk :=
    tupleHom_ext (e.map_injective (congrArg Tuple.Hom.target hk))
      (funext fun i => h.map_injective (congrArg (fun q => Tuple.Hom.source q i) hk))

/-- The induced functor of Čech nerves is full when both horizontal functors are. -/
public lemma nerveMap_full [h.Full] [e.Full] [e.Faithful] (n : ℕ) :
    (nerveMap pX pY f g h e α he hα n).Full where
  map_surjective {a b} k := by
    let l : a ⟶ b :=
      { target := e.preimage k.target
        source := fun i => h.preimage (k.source i)
        comparison_naturality := fun i => by
          apply e.map_injective
          apply (cancel_epi (α.hom.app (a.source i))).1
          simp only [Functor.map_comp]
          rw [← Category.assoc, ← map_comp_naturality α (h.preimage (k.source i))]
          simpa [nerveMap, Category.assoc] using k.comparison_naturality i }
    exact ⟨l, tupleHom_ext (e.map_preimage _) (funext fun i => h.map_preimage _)⟩

/-- The induced functor of Čech nerves is essentially surjective when both horizontal functors
are: a tuple downstairs is lifted coordinatewise, and the comparison isomorphisms are corrected
to be vertical by `Stacks.Cech.exists_vertical_comparison`. -/
public lemma nerveMap_essSurj [h.EssSurj] [e.IsEquivalence]
    (hpV : (g ⋙ pY).IsFiberedInGroupoids) (n : ℕ) :
    (nerveMap pX pY f g h e α he hα n).EssSurj where
  mem_essImage a := by
    let y := e.objPreimage a.target
    let t : e.obj y ≅ a.target := e.objObjPreimageIso a.target
    let v (i : Fin (n + 1)) := h.objPreimage (a.source i)
    let s (i : Fin (n + 1)) : h.obj (v i) ≅ a.source i := h.objObjPreimageIso (a.source i)
    let β (i : Fin (n + 1)) : g.obj (v i) ≅ y :=
      e.preimageIso ((α.app (v i)).symm ≪≫ f.mapIso (s i) ≪≫ a.comparison i ≪≫ t.symm)
    choose v' η hη using fun i => exists_vertical_comparison pY g hpV (β i)
    let b : Tuple pY g n :=
      { target := y
        source := v'
        comparison := fun i => g.mapIso (η i) ≪≫ β i
        comparison_lift := hη }
    refine ⟨b, ⟨tupleIso t (fun i => h.mapIso (η i) ≪≫ s i) ?_⟩⟩
    intro i
    dsimp [b, nerveMap]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Category.assoc]
    rw [← map_comp_naturality α (η i).hom]
    simp [β, Category.assoc]

variable [Preadditive A]

/-- **Stacks 06X5 (1).** A `2`-commutative square of coverings over the base induces a morphism
of Čech complexes `Č(U → X, F) ⟶ Č(V → Y, e⁻¹F)`, given in degree `n` by pullback along the
induced functor `V_n ⥤ U_n` of Čech nerves. -/
@[stacks 06X5 "part (1), the morphism of complexes"]
public def complexPullbackMap : complex pX f F ⟶ complex pY g (e.op ⋙ F) :=
  AlternatingCofaceMapComplex.map (cosimplicialPullbackMap pX pY f g h e α he hα F)

/-- **Stacks 06X5 (1).** The morphism of Čech complexes is pullback along the induced functor of
Čech nerves, degreewise on the limit cones. -/
@[stacks 06X5 "part (1), the degreewise description"]
public theorem complexPullbackMap_π (n : ℕ) (a : Tuple pY g n) :
    (complexPullbackMap pX pY f g h e α he hα F).f n ≫
        limit.π ((Tuple.projection pY g n).op ⋙ e.op ⋙ F) (op a) =
      limit.π ((Tuple.projection pX f n).op ⋙ F)
        (op ((nerveMap pX pY f g h e α he hα n).obj a)) :=
  pullbackTermMap_π pX pY f g h e α he hα F n (op a)

/-- **Stacks 06X5 (2).** If the two horizontal functors of the square are equivalences, the
morphism of Čech complexes of part (1) is an isomorphism. -/
@[stacks 06X5 "part (2)"]
public theorem isIso_complexPullbackMap [h.IsEquivalence] [e.IsEquivalence]
    (hpV : (g ⋙ pY).IsFiberedInGroupoids) :
    IsIso (complexPullbackMap pX pY f g h e α he hα F) := by
  have (n : ℕ) : (nerveMap pX pY f g h e α he hα n).IsEquivalence :=
    { faithful := nerveMap_faithful pX pY f g h e α he hα n
      full := nerveMap_full pX pY f g h e α he hα n
      essSurj := nerveMap_essSurj pX pY f g h e α he hα hpV n }
  have (n : ℕ) : IsIso ((complexPullbackMap pX pY f g h e α he hα F).f n) := by
    change IsIso (limit.pre ((Tuple.projection pX f n).op ⋙ F)
      (nerveMap pX pY f g h e α he hα n).op)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end Square

/-- **Stacks 06X5 (3).** `2`-isomorphic coverings `f, f' : U ⥤ X` have isomorphic Čech
complexes. -/
@[stacks 06X5 "part (3)"]
public theorem nonempty_complexIso_of_natIso [Preadditive A] (p : X ⥤ C) (f f' : U ⥤ X)
    (α : f ≅ f') (hα : ∀ u : U, p.IsHomLift (𝟙 (p.obj (f.obj u))) (α.hom.app u))
    (hpU' : (f' ⋙ p).IsFiberedInGroupoids) (F : Xᵒᵖ ⥤ A)
    [∀ n : ℕ, HasLimitsOfShape (Tuple p f n)ᵒᵖ A]
    [∀ n : ℕ, HasLimitsOfShape (Tuple p f' n)ᵒᵖ A] :
    Nonempty (complex p f F ≅ complex p f' F) := by
  let β : (𝟭 U) ⋙ f ≅ f' ⋙ 𝟭 X :=
    Functor.leftUnitor f ≪≫ α ≪≫ (Functor.rightUnitor f').symm
  have hβ : ∀ u : U, p.IsHomLift (𝟙 (p.obj (f.obj ((𝟭 U).obj u)))) (β.hom.app u) :=
    fun u => by simpa [β] using hα u
  have := isIso_complexPullbackMap p p f f' (𝟭 U) (𝟭 X) β (Functor.id_comp p) hβ F hpU'
  exact ⟨asIso (complexPullbackMap p p f f' (𝟭 U) (𝟭 X) β (Functor.id_comp p) hβ F)⟩

end Stacks.Cech

end
