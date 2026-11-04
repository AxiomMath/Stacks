module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback and pushforward of presheaves along a composite (Stacks 06TL)

For a 1-morphism `f : 𝒳 ⟶ 𝒴` the functor `f^p : PSh(𝒴) ⥤ PSh(𝒳)` is precomposition with `f.op`,
its right adjoint `{}_pf : PSh(𝒳) ⥤ PSh(𝒴)` is right Kan extension along `f.op`, and the
adjunction `(f^p, {}_pf)` is `CategoryTheory.Functor.ranAdjunction` (Stacks `00XH`). For a second
1-morphism `g : 𝒴 ⟶ 𝒵` this file records `(g ∘ f)^p = f^p ∘ g^p` and produces the canonical
isomorphism `{}_p(g ∘ f) ≅ {}_pg ∘ {}_pf`.

Following the alternative route offered by the source, the isomorphism is *defined* by its
compatibility with the three adjunctions: `f^p ∘ g^p` is precomposition with `(g ∘ f).op`, so
`{}_pg ∘ {}_pf` and `{}_p(g ∘ f)` are two right adjoints of one functor and
`CategoryTheory.Adjunction.rightAdjointUniq` is the comparison isomorphism they determine. No
separate compatibility verification is then needed, and the isomorphism is the unique natural
transformation with that property.

## Main results

* `CategoryTheory.Functor.ranCompIsoOfAdjunctions`, and in the presheaf dictionary
  `CategoryTheory.Functor.ranOpCompIso`: **Stacks 06TL**, the canonical isomorphism
  `{}_p(g ∘ f) ≅ {}_pg ∘ {}_pf`.
* `CategoryTheory.Functor.homEquiv_comp_ranCompIso_hom_app`, and in the presheaf dictionary
  `CategoryTheory.Functor.homEquiv_comp_ranOpCompIso_hom_app`: **Stacks 06TL**, compatibility of
  that isomorphism with the adjunctions, i.e. the commuting square of hom-set bijections.
* `CategoryTheory.Functor.eq_ranCompIso_hom`: the compatibility characterises the isomorphism
  uniquely, which is what makes it canonical.

The equality `(g ∘ f)^p = f^p ∘ g^p` is Mathlib's `CategoryTheory.Functor.whiskeringLeft_obj_comp`
at `f.op` and `g.op`; it holds on the nose, not just up to isomorphism, because both sides send a
presheaf `H` to `f.op ⋙ (g.op ⋙ H)` and both associativity of functor composition and
`CategoryTheory.Functor.op_comp` are definitional.

## Implementation notes

The source states the lemma for 1-morphisms of categories fibred in groupoids over
`(Sch/S)_{fppf}`, but a presheaf on `𝒳` is by definition (Stacks `06TJ`) a presheaf on the
underlying category of `𝒳`, and neither the structural functors nor the fibration axioms enter the
proof. Everything is therefore proved for arbitrary functors and arbitrary coefficient categories,
and specialises to the source's setting.

Right Kan extension along `(g ∘ f).op` is available as soon as it is available along `f.op` and
along `g.op`, since the composite adjunction exhibits a terminal right extension; this is
`CategoryTheory.Functor.hasRightKanExtension_comp`, so no extra existence hypothesis is assumed.

## References

* [Stacks Project, Tag 06TL](https://stacks.math.columbia.edu/tag/06TL)
-/

@[expose] public section

namespace CategoryTheory

namespace Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The comparison isomorphism between two right adjoints of `F` is compatible with the two
adjunction bijections.

This repeats `CategoryTheory.Adjunction.homEquiv_comp_rightAdjointUniq_hom_app` of
`StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence`, and is kept private
here so that the two modules can be imported together: the statement is general, while that
module carries the machinery of cocontinuous descent, which nothing here needs. -/
private theorem homEquiv_comp_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : F ⊣ G') (X : C) (Y : D) (α : F.obj X ⟶ Y) :
    adj₁.homEquiv X Y α ≫ (rightAdjointUniq adj₁ adj₂).hom.app Y = adj₂.homEquiv X Y α := by
  rw [homEquiv_unit, homEquiv_unit, Category.assoc,
    (rightAdjointUniq adj₁ adj₂).hom.naturality α, ← Category.assoc,
    unit_rightAdjointUniq_hom_app]

/-- Compatibility with the two adjunction bijections characterises the comparison transformation
between two right adjoints of `F`. -/
theorem eq_rightAdjointUniq_hom {F : C ⥤ D} {G G' : D ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : F ⊣ G') (θ : G ⟶ G')
    (hθ : ∀ (X : C) (Y : D) (α : F.obj X ⟶ Y),
      adj₁.homEquiv X Y α ≫ θ.app Y = adj₂.homEquiv X Y α) :
    θ = (rightAdjointUniq adj₁ adj₂).hom := by
  ext Y
  have h := (hθ (G.obj Y) Y (adj₁.counit.app Y)).trans
    (homEquiv_comp_rightAdjointUniq_hom_app adj₁ adj₂ (G.obj Y) Y (adj₁.counit.app Y)).symm
  simpa [homEquiv_unit] using h

end Adjunction

namespace Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] (H : Type u₄) [Category.{v₄} H]
  (L : C ⥤ D) (L' : D ⥤ E)
  [∀ (F : C ⥤ H), L.HasRightKanExtension F] [∀ (F : D ⥤ H), L'.HasRightKanExtension F]

/-- The composite of the two right Kan extension functors is right adjoint to precomposition with
`L ⋙ L'`, by `whiskeringLeft_obj_comp` and composition of adjunctions. -/
noncomputable def ranCompAdjunction :
    (whiskeringLeft C E H).obj (L ⋙ L') ⊣ L.ran ⋙ L'.ran :=
  (L'.ranAdjunction H).comp (L.ranAdjunction H)

/-- Right Kan extensions along `L ⋙ L'` exist as soon as they exist along `L` and along `L'`: the
composite adjunction exhibits a terminal right extension. -/
instance hasRightKanExtension_comp (F : C ⥤ H) : (L ⋙ L').HasRightKanExtension F :=
  (mkTerminalOfRightAdjoint _ (ranCompAdjunction H L L') F).hasTerminal

/-- The canonical isomorphism between right Kan extension along `L ⋙ L'` and the composite of the
right Kan extensions along `L` and along `L'`, namely the comparison of two right adjoints of
precomposition with `L ⋙ L'`. -/
noncomputable def ranCompIsoOfAdjunctions : (L ⋙ L').ran (H := H) ≅ L.ran ⋙ L'.ran :=
  Adjunction.rightAdjointUniq ((L ⋙ L').ranAdjunction H) (ranCompAdjunction H L L')

/-- `ranCompIsoOfAdjunctions` is compatible with the adjunctions along `L`, along `L'` and along
`L ⋙ L'`: transporting a map along it identifies the adjunction bijection for `L ⋙ L'` with the
composite of the bijections for `L` and for `L'`. -/
theorem homEquiv_comp_ranCompIso_hom_app (G : E ⥤ H) (F : C ⥤ H) (α : (L ⋙ L') ⋙ G ⟶ F) :
    ((L ⋙ L').ranAdjunction H).homEquiv G F α ≫ (ranCompIsoOfAdjunctions H L L').hom.app F =
      (ranCompAdjunction H L L').homEquiv G F α :=
  Adjunction.homEquiv_comp_rightAdjointUniq_hom_app
    ((L ⋙ L').ranAdjunction H) (ranCompAdjunction H L L') G F α

/-- `ranCompIsoOfAdjunctions` is the unique natural transformation compatible with the three
adjunctions. -/
theorem eq_ranCompIso_hom (θ : (L ⋙ L').ran (H := H) ⟶ L.ran ⋙ L'.ran)
    (hθ : ∀ (G : E ⥤ H) (F : C ⥤ H) (α : (L ⋙ L') ⋙ G ⟶ F),
      ((L ⋙ L').ranAdjunction H).homEquiv G F α ≫ θ.app F =
        (ranCompAdjunction H L L').homEquiv G F α) :
    θ = (ranCompIsoOfAdjunctions H L L').hom :=
  Adjunction.eq_rightAdjointUniq_hom
    ((L ⋙ L').ranAdjunction H) (ranCompAdjunction H L L') θ hθ

/-- **`ranCompIsoOfAdjunctions` read against the counits.**  Composed with the counit of the right
Kan extension along `L'` and then with the counit of the one along `L`, it is the counit of the
right Kan extension along `L ⋙ L'`.

A right Kan extension is determined by its counit, so this pins the comparison down, and it is
the form in which a flattening of two nested right Kan extensions into one is computed.  Both
sides are right adjoints of precomposition with `L ⋙ L'` and the comparison is
`CategoryTheory.Adjunction.rightAdjointUniq`, whose behaviour on counits is
`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`; the counit of `ranCompAdjunction` is
the composite of the two counits. -/
theorem ranCompIso_hom_app_app_comp_ranCounit (F : C ⥤ H) (X : C) :
    ((ranCompIsoOfAdjunctions H L L').hom.app F).app ((L ⋙ L').obj X) ≫
        (L'.ranCounit.app (L.ran.obj F)).app (L.obj X) ≫ (L.ranCounit.app F).app X =
      ((L ⋙ L').ranCounit.app F).app X := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit ((L ⋙ L').ranAdjunction H)
    (ranCompAdjunction H L L') F
  have h2 := congrArg (fun t ↦ NatTrans.app t X) h
  simp only [NatTrans.comp_app] at h2
  simpa [ranCompAdjunction, Adjunction.comp, ranCompIsoOfAdjunctions] using h2

/-- **The inverse of `ranCompIsoOfAdjunctions` read against the counits**: the counit of the
single right Kan extension along `L ⋙ L'`, reached from the two nested ones. -/
theorem ranCompIso_inv_app_app_comp_ranCounit (F : C ⥤ H) (X : C) :
    ((ranCompIsoOfAdjunctions H L L').inv.app F).app ((L ⋙ L').obj X) ≫
        ((L ⋙ L').ranCounit.app F).app X =
      (L'.ranCounit.app (L.ran.obj F)).app (L.obj X) ≫ (L.ranCounit.app F).app X := by
  rw [← ranCompIso_hom_app_app_comp_ranCounit H L L' F X, Iso.inv_hom_id_app_app_assoc]

end

section Presheaf

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
  {Z : Type u₃} [Category.{v₃} Z] (A : Type u₄) [Category.{v₄} A]
  (f : X ⥤ Y) (g : Y ⥤ Z)
  [∀ (F : Xᵒᵖ ⥤ A), f.op.HasRightKanExtension F]
  [∀ (F : Yᵒᵖ ⥤ A), g.op.HasRightKanExtension F]

/-- Pushforward of presheaves along a composite exists as soon as it exists along each factor. -/
instance hasRightKanExtension_op_comp (F : Xᵒᵖ ⥤ A) : (f ⋙ g).op.HasRightKanExtension F :=
  hasRightKanExtension_comp A f.op g.op F

/-- **Stacks 06TL**: the canonical isomorphism `{}_p(g ∘ f) ≅ {}_pg ∘ {}_pf` of functors
`PSh(𝒳) ⥤ PSh(𝒵)`, namely the comparison of the two right adjoints `{}_p(g ∘ f)` and
`{}_pg ∘ {}_pf` of `(g ∘ f)^p = f^p ∘ g^p`. -/
@[stacks 06TL "the canonical isomorphism of pushforwards"]
noncomputable def ranOpCompIso : (f ⋙ g).op.ran (H := A) ≅ f.op.ran ⋙ g.op.ran :=
  ranCompIsoOfAdjunctions A f.op g.op

/-- **Stacks 06TL**: the isomorphism `{}_p(g ∘ f) ≅ {}_pg ∘ {}_pf` is compatible with adjointness
of `(f^p, {}_pf)`, `(g^p, {}_pg)` and `((g ∘ f)^p, {}_p(g ∘ f))`: the square of hom-set bijections
`Mor(f^p g^p K, F) = Mor(g^p K, {}_pf F) = Mor(K, {}_pg {}_pf F)` and
`Mor((g ∘ f)^p K, F) = Mor(K, {}_p(g ∘ f) F)` commutes. -/
@[stacks 06TL "compatibility of the canonical isomorphism with adjointness"]
theorem homEquiv_comp_ranOpCompIso_hom_app (K : Zᵒᵖ ⥤ A) (F : Xᵒᵖ ⥤ A)
    (α : (f ⋙ g).op ⋙ K ⟶ F) :
    ((f ⋙ g).op.ranAdjunction A).homEquiv K F α ≫ (ranOpCompIso A f g).hom.app F =
      (ranCompAdjunction A f.op g.op).homEquiv K F α :=
  homEquiv_comp_ranCompIso_hom_app A f.op g.op K F α

end Presheaf

end Functor

end CategoryTheory

add_to_stacks 06TL
  "pullback of presheaves along a composite: `(g ∘ f)^p = f^p ∘ g^p`, at `F = f.op`, `G = g.op`"
  CategoryTheory.Functor.whiskeringLeft_obj_comp

end
