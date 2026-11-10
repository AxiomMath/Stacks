module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.BoundaryLift
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocallyFull

/-!
# Restriction along an arrow of the total site of a hypercovering sees only its image in `C`

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf. An arrow of the total site `(C/K)_total` is a simplex map together with an arrow
of the slice over the target degree, and the localization functor `j_total` remembers only the
latter. This file proves that for a *cartesian* sheaf `F` on the total site the restriction map
`F(ψ)` depends only on `j_total(ψ)`: two parallel arrows of the total site with the same image
in `C` act in the same way on the sections of `F`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.map_eq_of_totalForget_map_eq`: restriction along an
  arrow of the total site of a hypercovering, on the sections of a cartesian sheaf, depends only
  on the image of that arrow in `C`.

## Implementation notes

An arrow of the total site is determined by its simplex map together with its image in `C`
(`CategoryTheory.SimplicialSemiRepresentable.total_hom_ext`, which is faithfulness of the
componentwise localization functor), and an arrow out of a chart exists as soon as the evident
index equation and triangle hold (`.exists_totalHom`). Together these two turn every arrow built
below, and every equation between composites of them, into a comparison of simplex maps in
`SimplexCategory` and of arrows in `C`; no `eqToHom` survives into the main argument. This is why
the Cartesian lifts are not used through `CategoryTheory.Grothendieck.ιNatTrans`, whose cocycle
law carries the transport along `K.map_comp`.

The argument itself is three reductions and one piece of mathematics. Restriction along an arrow
whose image in `C` is invertible is bijective, by
`CategoryTheory.SimplicialSemiRepresentable.isIso_map_of_isIso_totalForget_map`, so composing
with such arrows is free on both sides. Composing the common target with a vertex of its degree
reduces to a target of simplicial degree `⦋0⦌`; the two simplex maps are then two vertices
`i ≤ j` of the source degree, and composing the source with the edge `i ⟶ j` reduces the
statement to the two faces of a `1`-simplex of `K` whose two vertices coincide — a loop.

For a loop the two faces agree because, locally on the object of `C` underlying it, the loop is
all three faces of a single `2`-simplex of `K`: that is
`Stacks.CategoryTheory.Hypercovering.boundaryLiftSieve_mem` at `n = 0`. Writing `p` and `q` for
the two faces of the local `1`-simplex and `c₀, c₁, c₂` for the three faces of the `2`-simplex,
the simplicial identities give `c₁ ≫ p = c₂ ≫ p`, `c₀ ≫ q = c₁ ≫ q` and `c₀ ≫ p = c₂ ≫ q`;
all five arrows restrict bijectively, so cancelling the epimorphism `F(p)` in the first gives
`F(c₁) = F(c₂)`, and then cancelling the monomorphism `F(c₀)` in the third gives `F(p) = F(q)`.

Globalising is separatedness of `F` for the sieve of the loop consisting of the arrows lying over
the covering sieve of `C` just produced. That sieve is covering because `j_total` is
cocontinuous, which is how the componentwise topology is avoided here entirely.

Almost every step below is written in term mode, through `.comp_base_eq` and `.comp_forget_eq`
rather than by rewriting with `CategoryTheory.Grothendieck.comp_base` and `Functor.map_comp`.
The reason is the one recorded in
`StacksFrontier/CategoryTheory/Sites/Simplicial/TransitionCocycle.lean`: the objects of the total
site that the sieve of a covering hands back are typed through
`CategoryTheory.SimplicialSiteSituation.totalCategory`, which is definitionally but not
syntactically `CategoryTheory.Grothendieck (slices K)`, so goals mentioning them are not
type-correct at `implicit` transparency and neither `rw` nor `simp` will touch them.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 01GN](https://stacks.math.columbia.edu/tag/01GN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory

namespace SemiRepresentable

variable {C : Type u} [SmallCategory C]

/-- The componentwise localization functor of a semi-representable object is faithful: an arrow
of `C/K` is an arrow of a single slice, and an arrow of a slice is determined by the arrow of `C`
underlying it. -/
instance componentOverForget_faithful (L : FormalCoproduct.{u} C) :
    (componentOverForget L).Faithful where
  map_injective {_ _} f g h := by
    cases f with
    | mk f =>
      cases g with
      | mk g => exact congrArg CategoryTheory.Sigma.SigmaHom.mk (Over.OverMorphism.ext h)

/-- The source and the target of an arrow of `C/K` lie in the same component. -/
theorem componentOver_index_eq (L : FormalCoproduct.{u} C) {x y : ComponentOver L} (f : x ⟶ y) :
    x.1 = y.1 := by
  cases f
  rfl

/-- The triangle satisfied by an arrow of `C/K`: the chart of the source is the chart of the
target precomposed with the underlying arrow of `C`. -/
theorem componentOver_triangle (L : FormalCoproduct.{u} C) {x y : ComponentOver L} (f : x ⟶ y)
    (h : x.1 = y.1) :
    x.2.hom ≫ eqToHom (congrArg L.obj h) = (componentOverForget L).map f ≫ y.2.hom := by
  cases f with
  | mk f =>
    rw [eqToHom_refl, Category.comp_id]
    exact (Over.w f).symm

end SemiRepresentable

namespace SimplicialSemiRepresentable

open SemiRepresentable

section Arrows

variable {C : Type u} [SmallCategory C] (K : SimplicialObject (FormalCoproduct.{u} C))

/-- **An arrow of the total site is determined by its simplex map and its image in `C`.** -/
theorem total_hom_ext {X Y : Grothendieck (slices K)} (ψ ψ' : X ⟶ Y)
    (hb : ψ.base = ψ'.base)
    (hg : (totalForget K).map ψ = (totalForget K).map ψ') : ψ = ψ' := by
  obtain ⟨b, f⟩ := ψ
  obtain ⟨b', f'⟩ := ψ'
  obtain rfl : b = b' := hb
  obtain rfl : f = f' :=
    (componentOverForget (K.obj Y.base)).map_injective
      ((totalForget_map K _).symm.trans (hg.trans (totalForget_map K _)))
  rfl

/-- The simplex map of a composite, in term mode: no rewriting, so it survives the objects of
the total site whose type is spelled through the simplicial-site situation. -/
theorem comp_base_eq {X Y Z : Grothendieck (slices K)} (α : X ⟶ Y) (β : Y ⟶ Z)
    {b₁ : X.base ⟶ Y.base} {b₂ : Y.base ⟶ Z.base} (h₁ : α.base = b₁) (h₂ : β.base = b₂) :
    (α ≫ β).base = b₁ ≫ b₂ :=
  (congrArg (fun z => z ≫ β.base) h₁).trans (congrArg (fun z => b₁ ≫ z) h₂)

/-- The image in `C` of a composite, in term mode, for the same reason as
`CategoryTheory.SimplicialSemiRepresentable.comp_base_eq`. -/
theorem comp_forget_eq {X Y Z : Grothendieck (slices K)} (α : X ⟶ Y) (β : Y ⟶ Z)
    {g₁ : (totalForget K).obj X ⟶ (totalForget K).obj Y}
    {g₂ : (totalForget K).obj Y ⟶ (totalForget K).obj Z}
    (h₁ : (totalForget K).map α = g₁) (h₂ : (totalForget K).map β = g₂) :
    (totalForget K).map (α ≫ β) = g₁ ≫ g₂ :=
  ((totalForget K).map_comp α β).trans
    ((congrArg (fun z => z ≫ (totalForget K).map β) h₁).trans (congrArg (fun z => g₁ ≫ z) h₂))

/-- Two composites of arrows of the total site agree once their simplex maps and their images in
`C` agree. -/
private theorem comp_eq_comp_of_base_forget {X Y Z W : Grothendieck (slices K)}
    (α : X ⟶ Y) (β : Y ⟶ Z) (γ : X ⟶ W) (δ : W ⟶ Z)
    {b₁ : X.base ⟶ Y.base} {b₂ : Y.base ⟶ Z.base} {b₃ : X.base ⟶ W.base}
    {b₄ : W.base ⟶ Z.base} (hα : α.base = b₁) (hβ : β.base = b₂) (hγ : γ.base = b₃)
    (hδ : δ.base = b₄) (hb : b₁ ≫ b₂ = b₃ ≫ b₄)
    {g₁ : (totalForget K).obj X ⟶ (totalForget K).obj Y}
    {g₂ : (totalForget K).obj Y ⟶ (totalForget K).obj Z}
    {g₃ : (totalForget K).obj X ⟶ (totalForget K).obj W}
    {g₄ : (totalForget K).obj W ⟶ (totalForget K).obj Z}
    (hα' : (totalForget K).map α = g₁) (hβ' : (totalForget K).map β = g₂)
    (hγ' : (totalForget K).map γ = g₃) (hδ' : (totalForget K).map δ = g₄)
    (hg : g₁ ≫ g₂ = g₃ ≫ g₄) : α ≫ β = γ ≫ δ :=
  total_hom_ext K _ _
    ((comp_base_eq K α β hα hβ).trans (hb.trans (comp_base_eq K γ δ hγ hδ).symm))
    ((comp_forget_eq K α β hα' hβ').trans (hg.trans (comp_forget_eq K γ δ hγ' hδ').symm))

/-- **An arrow of the total site out of chart data.** Given a chart `u` in simplicial degree `c`,
a chart `u'` in degree `c'`, a simplex map `b : c ⟶ c'` and an arrow `g` of `C` under which the
`b`-restriction of `u` is `u'`, the pair `(b, g)` is an arrow of the total site. -/
theorem exists_totalHom {c c' : SimplexCategoryᵒᵖ} (b : c ⟶ c') {τ : (K.obj c).I}
    (u : Over ((K.obj c).obj τ)) {i : (K.obj c').I} (u' : Over ((K.obj c').obj i))
    (g : u.left ⟶ u'.left) (hi : (K.map b).f τ = i)
    (he : (u.hom ≫ (K.map b).φ τ) ≫ eqToHom (congrArg (K.obj c').obj hi) = g ≫ u'.hom) :
    ∃ ψ : (⟨c, ⟨τ, u⟩⟩ : Grothendieck (slices K)) ⟶ ⟨c', ⟨i, u'⟩⟩,
      ψ.base = b ∧ (totalForget K).map ψ = g := by
  subst hi
  rw [eqToHom_refl, Category.comp_id] at he
  exact ⟨⟨b, CategoryTheory.Sigma.SigmaHom.mk (Over.homMk g he.symm)⟩, rfl, totalForget_map K _⟩

/-- **The chart data carried by an arrow of the total site.** The converse of
`CategoryTheory.SimplicialSemiRepresentable.exists_totalHom`: the simplex map and the image in
`C` of an arrow of the total site satisfy the index equation and the triangle. -/
theorem total_index_triangle {c c' : SimplexCategoryᵒᵖ} {τ : (K.obj c).I}
    {u : Over ((K.obj c).obj τ)} {i : (K.obj c').I} {u' : Over ((K.obj c').obj i)}
    (ψ : (⟨c, ⟨τ, u⟩⟩ : Grothendieck (slices K)) ⟶ ⟨c', ⟨i, u'⟩⟩) (b : c ⟶ c')
    (hb : ψ.base = b) (g : u.left ⟶ u'.left) (hg : (totalForget K).map ψ = g) :
    ∃ hi : (K.map b).f τ = i,
      (u.hom ≫ (K.map b).φ τ) ≫ eqToHom (congrArg (K.obj c').obj hi) = g ≫ u'.hom := by
  subst hb
  subst hg
  have hi := componentOver_index_eq (K.obj c') ψ.fiber
  refine ⟨hi, ?_⟩
  exact (componentOver_triangle (K.obj c') ψ.fiber hi).trans
    (congrArg (fun z => z ≫ u'.hom) (totalForget_map K ψ).symm)

/-- The identity simplex map acts as the identity on charts. -/
theorem map_id_index (c : SimplexCategoryᵒᵖ) (τ : (K.obj c).I) :
    ∃ h : (K.map (𝟙 c)).f τ = τ,
      (K.map (𝟙 c)).φ τ ≫ eqToHom (congrArg (K.obj c).obj h) = 𝟙 ((K.obj c).obj τ) :=
  (FormalCoproduct.hom_ext_iff' _ _).1 (K.map_id c) τ

/-- **The Cartesian lift of a simplex map at a chart**: an arrow of the total site with the given
simplex map whose image in `C` is the identity. -/
theorem exists_cartLift {c c' : SimplexCategoryᵒᵖ} (b : c ⟶ c') {τ : (K.obj c).I}
    (u : Over ((K.obj c).obj τ)) :
    ∃ ψ : (⟨c, ⟨τ, u⟩⟩ : Grothendieck (slices K)) ⟶
        ⟨c', ⟨(K.map b).f τ, Over.mk (u.hom ≫ (K.map b).φ τ)⟩⟩,
      ψ.base = b ∧ (totalForget K).map ψ = 𝟙 u.left := by
  refine exists_totalHom K b u (Over.mk (u.hom ≫ (K.map b).φ τ)) (𝟙 u.left) rfl ?_
  rw [eqToHom_refl, Category.comp_id]
  exact (Category.id_comp _).symm

/-- **A vertical arrow of the total site**: the arrow with identity simplex map over a given
arrow of `C`. -/
theorem exists_vertHom {c : SimplexCategoryᵒᵖ} {τ : (K.obj c).I} {A' : C}
    (u : Over ((K.obj c).obj τ)) (g : A' ⟶ u.left) :
    ∃ ψ : (⟨c, ⟨τ, Over.mk (g ≫ u.hom)⟩⟩ : Grothendieck (slices K)) ⟶ ⟨c, ⟨τ, u⟩⟩,
      ψ.base = 𝟙 c ∧ (totalForget K).map ψ = g := by
  obtain ⟨hid, hidφ⟩ := map_id_index K c τ
  refine exists_totalHom K (𝟙 c) (Over.mk (g ≫ u.hom)) u g hid ?_
  change ((g ≫ u.hom) ≫ (K.map (𝟙 c)).φ τ) ≫ _ = _
  rw [Category.assoc, Category.assoc, hidφ, Category.comp_id]

/-- Chart data splits along a composite simplex map: the data for `b₁ ≫ b₂` at a chart is the
data for `b₂` at the `b₁`-restriction of that chart. -/
theorem index_triangle_split {c₁ c₂ c₃ : SimplexCategoryᵒᵖ} (b₁ : c₁ ⟶ c₂) (b₂ : c₂ ⟶ c₃)
    {τ : (K.obj c₁).I} {u : Over ((K.obj c₁).obj τ)} {i : (K.obj c₃).I}
    {u' : Over ((K.obj c₃).obj i)} {g : u.left ⟶ u'.left}
    (hi : (K.map (b₁ ≫ b₂)).f τ = i)
    (he : (u.hom ≫ (K.map (b₁ ≫ b₂)).φ τ) ≫ eqToHom (congrArg (K.obj c₃).obj hi) =
      g ≫ u'.hom) :
    ∃ hi' : (K.map b₂).f ((K.map b₁).f τ) = i,
      ((u.hom ≫ (K.map b₁).φ τ) ≫ (K.map b₂).φ ((K.map b₁).f τ)) ≫
        eqToHom (congrArg (K.obj c₃).obj hi') = g ≫ u'.hom := by
  obtain ⟨hc, hcφ⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 (K.map_comp b₁ b₂) τ
  refine ⟨hc.symm.trans hi, ?_⟩
  have h1 : (u.hom ≫ (K.map b₁).φ τ) ≫ (K.map b₂).φ ((K.map b₁).f τ) =
      (u.hom ≫ (K.map (b₁ ≫ b₂)).φ τ) ≫ eqToHom (congrArg (K.obj c₃).obj hc) := by
    simp only [Category.assoc]
    rw [hcφ]
    rfl
  rw [h1, Category.assoc, eqToHom_trans]
  exact he

end Arrows

section Hypercovering

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C]
  (P : Pretopology C) (H : HypercoveringOfTerminal.{u, u, u} P)
  (F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u))
  (hF : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf F)

/-- Restriction along equal composites of arrows: if `α ≫ β = γ ≫ δ` then
`G(β) ≫ G(α) = G(δ) ≫ G(γ)`. -/
private theorem map_op_comp_eq {D E : Type*} [Category D] [Category E] (G : Dᵒᵖ ⥤ E)
    {X Y Z W : D} {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ W} {δ : W ⟶ Z} (h : α ≫ β = γ ≫ δ) :
    G.map β.op ≫ G.map α.op = G.map δ.op ≫ G.map γ.op := by
  rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, h]

include hF in
/-- **The local step for a loop.** With a `2`-simplex of `K` over `A'` all three of whose faces
are the pullback along `g` of the `1`-simplex `m`, the two faces of `m` agree after restriction
along the vertical arrow over `g`. -/
private theorem map_eq_of_loop_local
    {A A' : C} {s : (H.toSimplicialObject.obj (op ⦋1⦌)).I}
    {jj : (H.toSimplicialObject.obj (op ⦋0⦌)).I}
    {m : A ⟶ (H.toSimplicialObject.obj (op ⦋1⦌)).obj s}
    {d : A ⟶ (H.toSimplicialObject.obj (op ⦋0⦌)).obj jj}
    (p q : (⟨op ⦋1⦌, ⟨s, Over.mk m⟩⟩ : Grothendieck (slices H.toSimplicialObject)) ⟶
      ⟨op ⦋0⦌, ⟨jj, Over.mk d⟩⟩)
    (hpb : p.base = (SimplexCategory.δ (1 : Fin 2)).op)
    (hqb : q.base = (SimplexCategory.δ (0 : Fin 2)).op)
    (hpg : (totalForget H.toSimplicialObject).map p = 𝟙 A)
    (hqg : (totalForget H.toSimplicialObject).map q = 𝟙 A)
    {g : A' ⟶ A} {σ : (H.toSimplicialObject.obj (op ⦋2⦌)).I}
    (n : A' ⟶ (H.toSimplicialObject.obj (op ⦋2⦌)).obj σ)
    (hface : ∀ k : Fin 3,
      ∃ hik : (H.toSimplicialObject.map (SimplexCategory.δ k).op).f σ = s,
        (n ≫ (H.toSimplicialObject.map (SimplexCategory.δ k).op).φ σ) ≫
          eqToHom (congrArg (H.toSimplicialObject.obj (op ⦋1⦌)).obj hik) = g ≫ m)
    (ρ : (⟨op ⦋1⦌, ⟨s, Over.mk (g ≫ m)⟩⟩ :
        Grothendieck (slices H.toSimplicialObject)) ⟶ ⟨op ⦋1⦌, ⟨s, Over.mk m⟩⟩)
    (hρb : ρ.base = 𝟙 (op ⦋1⦌)) (hρg : (totalForget H.toSimplicialObject).map ρ = g) :
    F.obj.map p.op ≫ F.obj.map ρ.op = F.obj.map q.op ≫ F.obj.map ρ.op := by
  obtain ⟨hjp, hep⟩ := total_index_triangle H.toSimplicialObject p _ hpb _ hpg
  obtain ⟨hjq, heq⟩ := total_index_triangle H.toSimplicialObject q _ hqb _ hqg
  obtain ⟨hi0, he0⟩ := hface 0
  obtain ⟨hi1, he1⟩ := hface 1
  obtain ⟨hi2, he2⟩ := hface 2
  have hep₁ : (m ≫ (H.toSimplicialObject.map (SimplexCategory.δ (1 : Fin 2)).op).φ s) ≫
      eqToHom (congrArg (H.toSimplicialObject.obj (op ⦋0⦌)).obj hjp) = d :=
    hep.trans (Category.id_comp d)
  have heq₁ : (m ≫ (H.toSimplicialObject.map (SimplexCategory.δ (0 : Fin 2)).op).φ s) ≫
      eqToHom (congrArg (H.toSimplicialObject.obj (op ⦋0⦌)).obj hjq) = d :=
    heq.trans (Category.id_comp d)
  obtain ⟨ρ₀, hρ₀b, hρ₀g⟩ := exists_vertHom H.toSimplicialObject (Over.mk d) g
  obtain ⟨p', hp'b, hp'g⟩ := exists_totalHom H.toSimplicialObject
    (SimplexCategory.δ (1 : Fin 2)).op (Over.mk (g ≫ m)) (Over.mk (g ≫ d)) (𝟙 A') hjp
    (by
      refine Eq.trans ?_ (Category.id_comp (g ≫ d)).symm
      change ((g ≫ m) ≫ _) ≫ _ = g ≫ d
      rw [Category.assoc, Category.assoc, ← Category.assoc m, hep₁])
  obtain ⟨q', hq'b, hq'g⟩ := exists_totalHom H.toSimplicialObject
    (SimplexCategory.δ (0 : Fin 2)).op (Over.mk (g ≫ m)) (Over.mk (g ≫ d)) (𝟙 A') hjq
    (by
      refine Eq.trans ?_ (Category.id_comp (g ≫ d)).symm
      change ((g ≫ m) ≫ _) ≫ _ = g ≫ d
      rw [Category.assoc, Category.assoc, ← Category.assoc m, heq₁])
  obtain ⟨c0, hc0b, hc0g⟩ := exists_totalHom H.toSimplicialObject
    (SimplexCategory.δ (0 : Fin 3)).op (Over.mk n) (Over.mk (g ≫ m)) (𝟙 A') hi0
    (he0.trans (Category.id_comp (g ≫ m)).symm)
  obtain ⟨c1, hc1b, hc1g⟩ := exists_totalHom H.toSimplicialObject
    (SimplexCategory.δ (1 : Fin 3)).op (Over.mk n) (Over.mk (g ≫ m)) (𝟙 A') hi1
    (he1.trans (Category.id_comp (g ≫ m)).symm)
  obtain ⟨c2, hc2b, hc2g⟩ := exists_totalHom H.toSimplicialObject
    (SimplexCategory.δ (2 : Fin 3)).op (Over.mk n) (Over.mk (g ≫ m)) (𝟙 A') hi2
    (he2.trans (Category.id_comp (g ≫ m)).symm)
  have : IsIso (F.obj.map p'.op) :=
    isIso_map_of_isIso_totalForget_map P.toGrothendieck H.toSimplicialObject F hF p'
      (by rw [hp'g]; exact IsIso.id _)
  have : IsIso (F.obj.map c0.op) :=
    isIso_map_of_isIso_totalForget_map P.toGrothendieck H.toSimplicialObject F hF c0
      (by rw [hc0g]; exact IsIso.id _)
  have hδA : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) =
      SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) :=
    SimplexCategory.Hom.ext_zero_left _ _ rfl
  have hδB : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) =
      SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) :=
    SimplexCategory.Hom.ext_zero_left _ _ rfl
  have hδC : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) =
      SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) :=
    SimplexCategory.Hom.ext_zero_left _ _ rfl
  have hA : c1 ≫ p' = c2 ≫ p' :=
    comp_eq_comp_of_base_forget H.toSimplicialObject c1 p' c2 p' hc1b hp'b hc2b hp'b
      (congrArg Quiver.Hom.op hδA) hc1g hp'g hc2g hp'g rfl
  have hB : c0 ≫ q' = c1 ≫ q' :=
    comp_eq_comp_of_base_forget H.toSimplicialObject c0 q' c1 q' hc0b hq'b hc1b hq'b
      (congrArg Quiver.Hom.op hδB) hc0g hq'g hc1g hq'g rfl
  have hCc : c0 ≫ p' = c2 ≫ q' :=
    comp_eq_comp_of_base_forget H.toSimplicialObject c0 p' c2 q' hc0b hp'b hc2b hq'b
      (congrArg Quiver.Hom.op hδC) hc0g hp'g hc2g hq'g rfl
  have hc12 : F.obj.map c1.op = F.obj.map c2.op :=
    (cancel_epi (F.obj.map p'.op)).1 (map_op_comp_eq F.obj hA)
  have hpq : F.obj.map p'.op = F.obj.map q'.op :=
    (cancel_mono (F.obj.map c0.op)).1
      ((map_op_comp_eq F.obj hCc).trans
        ((congrArg (fun z => F.obj.map q'.op ≫ z) hc12.symm).trans
          (map_op_comp_eq F.obj hB).symm))
  have hsq1 : ρ ≫ p = p' ≫ ρ₀ :=
    comp_eq_comp_of_base_forget H.toSimplicialObject ρ p p' ρ₀ hρb hpb hp'b hρ₀b
      ((Category.id_comp _).trans (Category.comp_id _).symm) hρg hpg hp'g hρ₀g
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hsq2 : ρ ≫ q = q' ≫ ρ₀ :=
    comp_eq_comp_of_base_forget H.toSimplicialObject ρ q q' ρ₀ hρb hqb hq'b hρ₀b
      ((Category.id_comp _).trans (Category.comp_id _).symm) hρg hqg hq'g hρ₀g
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact (map_op_comp_eq F.obj hsq1).trans
    ((congrArg (fun z => F.obj.map ρ₀.op ≫ z) hpq).trans (map_op_comp_eq F.obj hsq2).symm)

include hF in
/-- **The two faces of a loop agree.** If the two vertices of a `1`-simplex of `K` over `A`
coincide, then the two face arrows of the total site that it carries restrict a cartesian sheaf
in the same way. -/
private theorem map_eq_of_loop
    {A : C} {s : (H.toSimplicialObject.obj (op ⦋1⦌)).I}
    {jj : (H.toSimplicialObject.obj (op ⦋0⦌)).I}
    {m : A ⟶ (H.toSimplicialObject.obj (op ⦋1⦌)).obj s}
    {d : A ⟶ (H.toSimplicialObject.obj (op ⦋0⦌)).obj jj}
    (p q : (⟨op ⦋1⦌, ⟨s, Over.mk m⟩⟩ : Grothendieck (slices H.toSimplicialObject)) ⟶
      ⟨op ⦋0⦌, ⟨jj, Over.mk d⟩⟩)
    (hpb : p.base = (SimplexCategory.δ (1 : Fin 2)).op)
    (hqb : q.base = (SimplexCategory.δ (0 : Fin 2)).op)
    (hpg : (totalForget H.toSimplicialObject).map p = 𝟙 A)
    (hqg : (totalForget H.toSimplicialObject).map q = 𝟙 A) :
    F.obj.map p.op = F.obj.map q.op := by
  obtain ⟨hjp, hep⟩ := total_index_triangle H.toSimplicialObject p _ hpb _ hpg
  obtain ⟨hjq, heq⟩ := total_index_triangle H.toSimplicialObject q _ hqb _ hqg
  have hep₁ : (m ≫ (H.toSimplicialObject.map (SimplexCategory.δ (1 : Fin 2)).op).φ s) ≫
      eqToHom (congrArg (H.toSimplicialObject.obj (op ⦋0⦌)).obj hjp) = d :=
    hep.trans (Category.id_comp d)
  have heq₁ : (m ≫ (H.toSimplicialObject.map (SimplexCategory.δ (0 : Fin 2)).op).φ s) ≫
      eqToHom (congrArg (H.toSimplicialObject.obj (op ⦋0⦌)).obj hjq) = d :=
    heq.trans (Category.id_comp d)
  have hφ : (m ≫ (H.toSimplicialObject.map (SimplexCategory.δ (0 : Fin 2)).op).φ s) ≫
      eqToHom (congrArg (H.toSimplicialObject.obj (op ⦋0⦌)).obj (hjq.trans hjp.symm)) =
      m ≫ (H.toSimplicialObject.map (SimplexCategory.δ (1 : Fin 2)).op).φ s := by
    refine (cancel_mono (eqToHom
      (congrArg (H.toSimplicialObject.obj (op ⦋0⦌)).obj hjp))).1 ?_
    rw [Category.assoc, eqToHom_trans]
    exact heq₁.trans hep₁.symm
  have hloop : FormalCoproduct.Hom.fromIncl s m ≫
        H.toSimplicialObject.map (SimplexCategory.δ (0 : Fin 2)).op =
      FormalCoproduct.Hom.fromIncl s m ≫
        H.toSimplicialObject.map (SimplexCategory.δ (1 : Fin 2)).op :=
    FormalCoproduct.hom_ext (funext fun _ => hjq.trans hjp.symm) fun _ => hφ
  have hs : ∀ (j k : Fin 3) (hjk : j < k),
      (fun _ : Fin 3 => FormalCoproduct.Hom.fromIncl s m) j ≫
          H.toSimplicialObject.map
            (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))).op =
        (fun _ : Fin 3 => FormalCoproduct.Hom.fromIncl s m) k ≫
          H.toSimplicialObject.map
            (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))).op := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
        | exact absurd hjk (by decide)
        | rfl
        | exact hloop.symm
  have hcov := boundaryLiftSieve_mem P H 0 (fun _ => FormalCoproduct.Hom.fromIncl s m) hs
  have hT := (totalForget H.toSimplicialObject).cover_lift
    ((situation P.toGrothendieck H.toSimplicialObject).totalTopology) P.toGrothendieck
    (U := (⟨op ⦋1⦌, ⟨s, Over.mk m⟩⟩ : Grothendieck (slices H.toSimplicialObject))) hcov
  have hsep := (F.property.isSheafFor _ hT).isSeparatedFor
  apply ConcreteCategory.hom_ext
  intro x
  refine hsep.ext ?_
  rintro W h hh
  obtain ⟨cW, iW, uW⟩ := W
  obtain ⟨t, ht⟩ := hh
  obtain ⟨hiW, heW⟩ := total_index_triangle H.toSimplicialObject h _ rfl _ rfl
  obtain ⟨χ, hχb, hχg⟩ := exists_totalHom H.toSimplicialObject h.base uW
    (Over.mk (((totalForget H.toSimplicialObject).map h) ≫ m)) (𝟙 uW.left) hiW
    (heW.trans (Category.id_comp _).symm)
  obtain ⟨ρ, hρb, hρg⟩ := exists_vertHom H.toSimplicialObject (Over.mk m)
    ((totalForget H.toSimplicialObject).map h)
  have hfac : χ ≫ ρ = h :=
    total_hom_ext H.toSimplicialObject _ _
      ((comp_base_eq H.toSimplicialObject χ ρ hχb hρb).trans (Category.comp_id _))
      ((comp_forget_eq H.toSimplicialObject χ ρ hχg hρg).trans (Category.id_comp _))
  have hface : ∀ k : Fin 3,
      ∃ hik : (H.toSimplicialObject.map (SimplexCategory.δ k).op).f (t.f PUnit.unit) = s,
        ((t.φ PUnit.unit) ≫ (H.toSimplicialObject.map (SimplexCategory.δ k).op).φ
            (t.f PUnit.unit)) ≫
          eqToHom (congrArg (H.toSimplicialObject.obj (op ⦋1⦌)).obj hik) =
            ((totalForget H.toSimplicialObject).map h) ≫ m := fun k =>
    (FormalCoproduct.hom_ext_iff' _ _).1 (ht k) PUnit.unit
  have key := map_eq_of_loop_local P H F hF p q hpb hqb hpg hqg (t.φ PUnit.unit) hface ρ hρb hρg
  have e : F.obj.map h.op = F.obj.map ρ.op ≫ F.obj.map χ.op :=
    (congrArg (fun z => F.obj.map z.op) hfac.symm).trans (F.obj.map_comp ρ.op χ.op)
  exact ConcreteCategory.congr_hom
    ((congrArg (fun z => F.obj.map p.op ≫ z) e).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ F.obj.map χ.op) key).trans
          ((Category.assoc _ _ _).trans (congrArg (fun z => F.obj.map q.op ≫ z) e).symm)))) x

include hF in
/-- The degree-zero-target case of the main theorem, for two vertices in the given order. -/
private theorem map_eq_zero_target_le {nn : ℕ}
    {iX : (H.toSimplicialObject.obj (op ⦋nn⦌)).I}
    {uX : Over ((H.toSimplicialObject.obj (op ⦋nn⦌)).obj iX)}
    {jj : (H.toSimplicialObject.obj (op ⦋0⦌)).I}
    {w : Over ((H.toSimplicialObject.obj (op ⦋0⦌)).obj jj)}
    (ψ ψ' : (⟨op ⦋nn⦌, ⟨iX, uX⟩⟩ : Grothendieck (slices H.toSimplicialObject)) ⟶
      ⟨op ⦋0⦌, ⟨jj, w⟩⟩)
    (hle : ψ.base.unop.toOrderHom 0 ≤ ψ'.base.unop.toOrderHom 0)
    (h : (totalForget H.toSimplicialObject).map ψ = (totalForget H.toSimplicialObject).map ψ') :
    F.obj.map ψ.op = F.obj.map ψ'.op := by
  set e : (op ⦋nn⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋1⦌ :=
    (SimplexCategory.mkOfLe (ψ.base.unop.toOrderHom 0) (ψ'.base.unop.toOrderHom 0) hle).op
    with he_def
  have hψb : ψ.base = e ≫ (SimplexCategory.δ (1 : Fin 2)).op :=
    congrArg Quiver.Hom.op (SimplexCategory.Hom.ext_zero_left _ _ rfl)
  have hψ'b : ψ'.base = e ≫ (SimplexCategory.δ (0 : Fin 2)).op :=
    congrArg Quiver.Hom.op (SimplexCategory.Hom.ext_zero_left _ _ rfl)
  obtain ⟨hiψ, heψ⟩ := total_index_triangle H.toSimplicialObject ψ _ hψb _ rfl
  obtain ⟨hiψ', heψ'⟩ := total_index_triangle H.toSimplicialObject ψ' _ hψ'b _ rfl
  obtain ⟨hjp, hep⟩ := index_triangle_split H.toSimplicialObject e
    (SimplexCategory.δ (1 : Fin 2)).op hiψ heψ
  obtain ⟨hjq, heq⟩ := index_triangle_split H.toSimplicialObject e
    (SimplexCategory.δ (0 : Fin 2)).op hiψ' heψ'
  obtain ⟨ε, hεb, hεg⟩ := exists_cartLift H.toSimplicialObject e uX
  obtain ⟨p, hpb, hpg⟩ := exists_totalHom H.toSimplicialObject
    (SimplexCategory.δ (1 : Fin 2)).op
    (Over.mk (uX.hom ≫ (H.toSimplicialObject.map e).φ iX))
    (Over.mk (((totalForget H.toSimplicialObject).map ψ) ≫ w.hom)) (𝟙 uX.left) hjp
    (hep.trans (Category.id_comp _).symm)
  obtain ⟨q, hqb, hqg⟩ := exists_totalHom H.toSimplicialObject
    (SimplexCategory.δ (0 : Fin 2)).op
    (Over.mk (uX.hom ≫ (H.toSimplicialObject.map e).φ iX))
    (Over.mk (((totalForget H.toSimplicialObject).map ψ) ≫ w.hom)) (𝟙 uX.left) hjq
    (heq.trans ((congrArg (fun z => z ≫ w.hom) h.symm).trans (Category.id_comp _).symm))
  obtain ⟨π, hπb, hπg⟩ := exists_vertHom H.toSimplicialObject w
    ((totalForget H.toSimplicialObject).map ψ)
  have hbp : (p ≫ π).base = (SimplexCategory.δ (1 : Fin 2)).op :=
    (comp_base_eq H.toSimplicialObject p π hpb hπb).trans (Category.comp_id _)
  have hbq : (q ≫ π).base = (SimplexCategory.δ (0 : Fin 2)).op :=
    (comp_base_eq H.toSimplicialObject q π hqb hπb).trans (Category.comp_id _)
  have hgp : (totalForget H.toSimplicialObject).map (p ≫ π) =
      (totalForget H.toSimplicialObject).map ψ :=
    (comp_forget_eq H.toSimplicialObject p π hpg hπg).trans (Category.id_comp _)
  have hgq : (totalForget H.toSimplicialObject).map (q ≫ π) =
      (totalForget H.toSimplicialObject).map ψ :=
    (comp_forget_eq H.toSimplicialObject q π hqg hπg).trans (Category.id_comp _)
  have hψfac : ψ = ε ≫ p ≫ π :=
    total_hom_ext H.toSimplicialObject _ _
      (hψb.trans (comp_base_eq H.toSimplicialObject ε (p ≫ π) hεb hbp).symm)
      ((Category.id_comp _).symm.trans
        (comp_forget_eq H.toSimplicialObject ε (p ≫ π) hεg hgp).symm)
  have hψ'fac : ψ' = ε ≫ q ≫ π :=
    total_hom_ext H.toSimplicialObject _ _
      (hψ'b.trans (comp_base_eq H.toSimplicialObject ε (q ≫ π) hεb hbq).symm)
      (h.symm.trans ((Category.id_comp _).symm.trans
        (comp_forget_eq H.toSimplicialObject ε (q ≫ π) hεg hgq).symm))
  have hloop := map_eq_of_loop P H F hF p q hpb hqb hpg hqg
  have hpq : F.obj.map (p ≫ π).op = F.obj.map (q ≫ π).op :=
    (F.obj.map_comp π.op p.op).trans
      ((congrArg (fun z => F.obj.map π.op ≫ z) hloop).trans (F.obj.map_comp π.op q.op).symm)
  calc F.obj.map ψ.op
      = F.obj.map (ε ≫ p ≫ π).op := congrArg (fun z => F.obj.map (Quiver.Hom.op z)) hψfac
    _ = F.obj.map (p ≫ π).op ≫ F.obj.map ε.op := F.obj.map_comp _ _
    _ = F.obj.map (q ≫ π).op ≫ F.obj.map ε.op := congrArg (fun z => z ≫ F.obj.map ε.op) hpq
    _ = F.obj.map (ε ≫ q ≫ π).op := (F.obj.map_comp _ _).symm
    _ = F.obj.map ψ'.op := congrArg (fun z => F.obj.map (Quiver.Hom.op z)) hψ'fac.symm

include hF in
/-- The degree-zero-target case of the main theorem. -/
private theorem map_eq_zero_target {nn : ℕ}
    {iX : (H.toSimplicialObject.obj (op ⦋nn⦌)).I}
    {uX : Over ((H.toSimplicialObject.obj (op ⦋nn⦌)).obj iX)}
    {jj : (H.toSimplicialObject.obj (op ⦋0⦌)).I}
    {w : Over ((H.toSimplicialObject.obj (op ⦋0⦌)).obj jj)}
    (ψ ψ' : (⟨op ⦋nn⦌, ⟨iX, uX⟩⟩ : Grothendieck (slices H.toSimplicialObject)) ⟶
      ⟨op ⦋0⦌, ⟨jj, w⟩⟩)
    (h : (totalForget H.toSimplicialObject).map ψ = (totalForget H.toSimplicialObject).map ψ') :
    F.obj.map ψ.op = F.obj.map ψ'.op := by
  rcases le_total (ψ.base.unop.toOrderHom 0) (ψ'.base.unop.toOrderHom 0) with hle | hle
  · exact map_eq_zero_target_le P H F hF ψ ψ' hle h
  · exact (map_eq_zero_target_le P H F hF ψ' ψ hle h.symm).symm

include hF in
/-- **Restriction along an arrow of the total site of a hypercovering depends only on its image
in `C`.** For a cartesian sheaf `F` on the total site of a hypercovering of the final presheaf,
two parallel arrows of the total site with the same image under `j_total` act in the same way on
the sections of `F`.

Composing the common target with a vertex of its simplicial degree — an arrow along which
restriction is bijective — reduces the statement to a target of degree `⦋0⦌`, where the two
simplex maps are two vertices of the source degree; the edge joining them reduces the statement
further to the two faces of a `1`-simplex of `K` whose vertices coincide, and those agree by
`map_eq_of_loop`. -/
theorem map_eq_of_totalForget_map_eq
    {X Y : Grothendieck (slices H.toSimplicialObject)} (ψ ψ' : X ⟶ Y)
    (h : (totalForget H.toSimplicialObject).map ψ =
      (totalForget H.toSimplicialObject).map ψ') :
    F.obj.map ψ.op = F.obj.map ψ'.op := by
  obtain ⟨⟨cX⟩, iX, uX⟩ := X
  obtain ⟨⟨cY⟩, iY, uY⟩ := Y
  induction cX using SimplexCategory.rec with | _ nn => ?_
  induction cY using SimplexCategory.rec with | _ nY => ?_
  obtain ⟨κ, hκb, hκg⟩ := exists_cartLift H.toSimplicialObject
    (SimplexCategory.const ⦋0⦌ ⦋nY⦌ (Fin.last nY)).op uY
  have : IsIso (F.obj.map κ.op) :=
    isIso_map_of_isIso_totalForget_map P.toGrothendieck H.toSimplicialObject F hF κ
      (by rw [hκg]; exact IsIso.id _)
  have hcomp : (totalForget H.toSimplicialObject).map (ψ ≫ κ) =
      (totalForget H.toSimplicialObject).map (ψ' ≫ κ) :=
    (comp_forget_eq H.toSimplicialObject ψ κ h hκg).trans
      (comp_forget_eq H.toSimplicialObject ψ' κ rfl hκg).symm
  have key := map_eq_zero_target P H F hF (ψ ≫ κ) (ψ' ≫ κ) hcomp
  refine (cancel_epi (F.obj.map κ.op)).1 ?_
  exact (F.obj.map_comp κ.op ψ.op).symm.trans (key.trans (F.obj.map_comp κ.op ψ'.op))

end Hypercovering

end SimplicialSemiRepresentable

end CategoryTheory

end
