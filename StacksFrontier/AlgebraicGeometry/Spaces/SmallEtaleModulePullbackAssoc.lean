module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Associativity of the comparison of inverse images of modules

For a composable pair `f : X ⟶ Y`, `g : Y ⟶ Z` of morphisms of algebraic spaces, Stacks 03LU
provides the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of inverse images of `𝒪`-modules, which is
`AlgebraicGeometry.Space.modulePullbackCompIso`.  For three composable morphisms there are two
ways of comparing `h^* ∘ g^* ∘ f^*` with `(f ≫ g ≫ h)^*`, and the assertion that they agree is
the associativity coherence of the comparison.  This file isolates that coherence as a
predicate and derives from it the reindexing calculus that consumers need.

## Main definitions

* `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc` is the associativity coherence of the
  comparison of inverse images.
* `AlgebraicGeometry.Space.modulePullbackReindex` reindexes a morphism between two inverse
  images of a module along a further morphism, and
  `AlgebraicGeometry.Space.modulePullbackFlatten` identifies a morphism between two inverse
  images of an inverse image with a morphism between two inverse images of the module itself,
  with `AlgebraicGeometry.Space.modulePullbackUnflatten` its inverse.

## Main results

* `CategoryTheory.Adjunction.whiskerLeft_leftAdjointUniq_hom` and
  `CategoryTheory.Adjunction.whiskerRight_leftAdjointUniq_hom`: whiskering the comparison of two
  left adjoints of one functor by a further left adjoint gives the comparison for the composed
  adjunctions.  This is the compatibility of `CategoryTheory.Adjunction.leftAdjointUniq` with
  whiskering that the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` record as missing
  from Mathlib.
* `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc.modulePullbackReindex_comp` and
  `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc.modulePullbackFlatten_reindex`:
  reindexing is functorial in the reindexing morphism, and commutes with flattening.  These two
  are what the coherence is used for.

## Implementation notes

The comparison of inverse images is the mate of the comparison of direct images: both
`g^* ∘ f^*` and `(f ≫ g)^*` are left adjoint to `f_* ∘ g_*`, read through
`AlgebraicGeometry.Space.modulePushforwardCompIso`, and the comparison is
`CategoryTheory.Adjunction.leftAdjointUniq`.  Two natural transformations out of a left adjoint
agree as soon as their transposes do — `CategoryTheory.Adjunction.natTrans_ext` — and that
reduces every statement about the comparison of inverse images to a statement about units.  In
particular the two whiskering laws above hold.  They do not, however, give the associativity
coherence: transposing it turns it into the associativity coherence for direct images, to which
it is equivalent under the bijection between a natural transformation of left adjoints and its
mate, so no amount of adjunction formalism replaces a proof of one of the two.

Associativity of composition in `AlgebraicGeometry.AlgebraicSpaces` holds by definitional
unfolding, so no transport along `Category.assoc` appears in the statements below.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- Two natural transformations out of a left adjoint agree as soon as their transposes along
the adjunction agree. -/
theorem natTrans_ext {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (adj : L₁ ⊣ R) {τ σ : L₁ ⟶ L₂}
    (h : ∀ A, adj.unit.app A ≫ R.map (τ.app A) = adj.unit.app A ≫ R.map (σ.app A)) :
    τ = σ := by
  ext A
  exact (adj.homEquiv A (L₂.obj A)).injective
    (by rw [adj.homEquiv_unit, adj.homEquiv_unit]; exact h A)

/-- Whiskering the comparison of two left adjoints of one functor on the right by a further
left adjoint gives the comparison of the two composed adjunctions. -/
theorem whiskerRight_leftAdjointUniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) {L : D ⥤ E} {R : E ⥤ D} (adjL : L ⊣ R) :
    Functor.whiskerRight (leftAdjointUniq adj1 adj2).hom L =
      (leftAdjointUniq (adj1.comp adjL) (adj2.comp adjL)).hom := by
  refine natTrans_ext (adj1.comp adjL) fun A ↦ ?_
  rw [unit_leftAdjointUniq_hom_app]
  simp only [comp_unit_app, Functor.comp_map, Functor.whiskerRight_app, Category.assoc,
    ← Functor.map_comp]
  rw [adjL.unit_naturality]
  simp only [Functor.map_comp, ← Category.assoc, unit_leftAdjointUniq_hom_app]

/-- Whiskering the comparison of two left adjoints of one functor on the left by a further
left adjoint gives the comparison of the two composed adjunctions. -/
theorem whiskerLeft_leftAdjointUniq_hom {F F' : D ⥤ E} {G : E ⥤ D} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) {L : C ⥤ D} {R : D ⥤ C} (adjL : L ⊣ R) :
    Functor.whiskerLeft L (leftAdjointUniq adj1 adj2).hom =
      (leftAdjointUniq (adjL.comp adj1) (adjL.comp adj2)).hom := by
  refine natTrans_ext (adjL.comp adj1) fun A ↦ ?_
  rw [unit_leftAdjointUniq_hom_app]
  simp only [comp_unit_app, Functor.comp_map, Functor.whiskerLeft_app, Category.assoc,
    ← Functor.map_comp, unit_leftAdjointUniq_hom_app]

/-- The comparison of two left adjoints of one functor is unchanged when the common right
adjoint is transported along a natural isomorphism. -/
theorem leftAdjointUniq_hom_ofNatIsoRight {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) (i : G ≅ G') :
    (leftAdjointUniq (adj1.ofNatIsoRight i) (adj2.ofNatIsoRight i)).hom =
      (leftAdjointUniq adj1 adj2).hom := by
  refine natTrans_ext (adj1.ofNatIsoRight i) fun A ↦ ?_
  rw [unit_leftAdjointUniq_hom_app]
  simp only [ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← i.hom.naturality, ← Category.assoc, unit_leftAdjointUniq_hom_app]

end CategoryTheory.Adjunction

namespace CategoryTheory.Iso

universe v u

variable {C : Type u} [Category.{v} C]

/-- Two factorizations of one isomorphism into two isomorphisms have equal inverse
factorizations. -/
theorem inv_comp_inv_eq {A B₁ B₂ D : C} (a : A ≅ B₁) (b : B₁ ≅ D) (c : A ≅ B₂) (d : B₂ ≅ D)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom) : b.inv ≫ a.inv = d.inv ≫ c.inv :=
  congrArg Iso.inv (Iso.ext (α := a ≪≫ b) (β := c ≪≫ d) h)

end CategoryTheory.Iso

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {V W X Y Z : AlgebraicSpaces B S hS}

/-- The associativity coherence of the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of inverse images of
`𝒪`-modules of Stacks 03LU: for three composable morphisms the two ways of comparing
`h^* ∘ g^* ∘ f^*` with `(f ≫ g ≫ h)^*` — inwards from `h^* ∘ g^*`, or outwards from
`g^* ∘ f^*` — agree. -/
structure ModulePullbackCompIsoAssoc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop where
  /-- The two comparisons of `h^* ∘ g^* ∘ f^*` with `(f ≫ g ≫ h)^*` agree. -/
  hom_app : ∀ {W X Y Z : AlgebraicSpaces B S hS} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2),
    (modulePullback B S hS f).map ((modulePullbackCompIso B S hS g h).hom.app M) ≫
        (modulePullbackCompIso B S hS f (g ≫ h)).hom.app M =
      (modulePullbackCompIso B S hS f g).hom.app ((modulePullback B S hS h).obj M) ≫
        (modulePullbackCompIso B S hS (f ≫ g) h).hom.app M

/-- The associativity coherence, read on the inverse comparisons. -/
theorem ModulePullbackCompIsoAssoc.inv_app (hassoc : ModulePullbackCompIsoAssoc B S hS)
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackCompIso B S hS f (g ≫ h)).inv.app M ≫
        (modulePullback B S hS f).map ((modulePullbackCompIso B S hS g h).inv.app M) =
      (modulePullbackCompIso B S hS (f ≫ g) h).inv.app M ≫
        (modulePullbackCompIso B S hS f g).inv.app ((modulePullback B S hS h).obj M) :=
  Iso.inv_comp_inv_eq
    ((modulePullback B S hS f).mapIso ((modulePullbackCompIso B S hS g h).app M))
    ((modulePullbackCompIso B S hS f (g ≫ h)).app M)
    ((modulePullbackCompIso B S hS f g).app ((modulePullback B S hS h).obj M))
    ((modulePullbackCompIso B S hS (f ≫ g) h).app M) (hassoc.hom_app f g h M)

/-- Reindexing a morphism between the inverse images of a module along two morphisms `a` and
`b`: its inverse image along a further morphism `f`, read as a morphism between the inverse
images along `f ≫ a` and `f ≫ b` through the comparisons of Stacks 03LU. -/
def modulePullbackReindex (f : X ⟶ Y) {a b : Y ⟶ Z} {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) :
    (modulePullback B S hS (f ≫ a)).obj M ⟶ (modulePullback B S hS (f ≫ b)).obj M :=
  (modulePullbackCompIso B S hS f a).inv.app M ≫ (modulePullback B S hS f).map α ≫
    (modulePullbackCompIso B S hS f b).hom.app M

/-- A morphism between the inverse images along two morphisms `a` and `b` of the inverse image
of a module along `f`, read through the comparisons of Stacks 03LU as a morphism between the
inverse images of the module along `a ≫ f` and `b ≫ f`. -/
def modulePullbackFlatten (f : Y ⟶ Z) {a b : X ⟶ Y} {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M)) :
    (modulePullback B S hS (a ≫ f)).obj M ⟶ (modulePullback B S hS (b ≫ f)).obj M :=
  (modulePullbackCompIso B S hS a f).inv.app M ≫ α ≫
    (modulePullbackCompIso B S hS b f).hom.app M

/-- The inverse of flattening: a morphism between the inverse images of a module along `a ≫ f`
and `b ≫ f`, read through the comparisons of Stacks 03LU as a morphism between the inverse
images along `a` and `b` of the inverse image of the module along `f`.

This is the two-sided inverse of `AlgebraicGeometry.Space.modulePullbackFlatten`; see
`AlgebraicGeometry.Space.modulePullbackFlatten_unflatten` and
`AlgebraicGeometry.Space.modulePullbackUnflatten_flatten`.  Naming it lets a consumer construct
a morphism between inverse images of an inverse image without writing a chain of `≫`, which in
the category `AlgebraicGeometry.Space.Modules` is the difference between a definition that can
be unfolded and one that cannot. -/
def modulePullbackUnflatten (f : Y ⟶ Z) {a b : X ⟶ Y} {M : Modules.{u, u} B S hS Z.1 Z.2}
    (φ : (modulePullback B S hS (a ≫ f)).obj M ⟶ (modulePullback B S hS (b ≫ f)).obj M) :
    (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M) :=
  (modulePullbackCompIso B S hS a f).hom.app M ≫ φ ≫
    (modulePullbackCompIso B S hS b f).inv.app M

/-- Flattening undoes unflattening. -/
theorem modulePullbackFlatten_unflatten (f : Y ⟶ Z) {a b : X ⟶ Y}
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (φ : (modulePullback B S hS (a ≫ f)).obj M ⟶ (modulePullback B S hS (b ≫ f)).obj M) :
    modulePullbackFlatten f (modulePullbackUnflatten f φ) = φ := by
  simp [modulePullbackFlatten, modulePullbackUnflatten]

/-- Unflattening undoes flattening. -/
theorem modulePullbackUnflatten_flatten (f : Y ⟶ Z) {a b : X ⟶ Y}
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M)) :
    modulePullbackUnflatten f (modulePullbackFlatten f α) = α := by
  simp [modulePullbackFlatten, modulePullbackUnflatten]

/-- Reindexing is compatible with composition of the morphisms being reindexed. -/
theorem modulePullbackReindex_comp_morphism (f : X ⟶ Y) {a b c : Y ⟶ Z}
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M)
    (β : (modulePullback B S hS b).obj M ⟶ (modulePullback B S hS c).obj M) :
    modulePullbackReindex f (α ≫ β) =
      modulePullbackReindex f α ≫ modulePullbackReindex f β := by
  simp [modulePullbackReindex, Category.assoc]

/-- Flattening is compatible with composition of the morphisms being flattened. -/
theorem modulePullbackFlatten_comp_morphism (f : Y ⟶ Z) {a b c : X ⟶ Y}
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M))
    (β : (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS c).obj ((modulePullback B S hS f).obj M)) :
    modulePullbackFlatten f (α ≫ β) =
      modulePullbackFlatten f α ≫ modulePullbackFlatten f β := by
  simp [modulePullbackFlatten, Category.assoc]

/-- Flattening is injective: it conjugates by two comparison isomorphisms. -/
theorem modulePullbackFlatten_injective (f : Y ⟶ Z) {a b : X ⟶ Y}
    {M : Modules.{u, u} B S hS Z.1 Z.2} :
    Function.Injective
      (modulePullbackFlatten (B := B) (S := S) (hS := hS) f (a := a) (b := b) (M := M)) := by
  intro α β h
  simpa only [modulePullbackFlatten, cancel_epi, cancel_mono] using h

/-- Reindexing the canonical identification of the inverse images along two equal morphisms is
the identification along the two composites. -/
theorem modulePullbackReindex_eqToHom (f : X ⟶ Y) {a b : Y ⟶ Z}
    (M : Modules.{u, u} B S hS Z.1 Z.2) (h : a = b) :
    modulePullbackReindex f
        (eqToHom (congrArg (fun k : Y ⟶ Z => (modulePullback B S hS k).obj M) h)) =
      eqToHom (congrArg (fun k : X ⟶ Z => (modulePullback B S hS k).obj M)
        (congrArg (f ≫ ·) h)) := by
  subst h
  simp [modulePullbackReindex]

/-- Flattening the canonical identification of the inverse images along two equal morphisms is
the identification along the two composites. -/
theorem modulePullbackFlatten_eqToHom (f : Y ⟶ Z) {a b : X ⟶ Y}
    (M : Modules.{u, u} B S hS Z.1 Z.2) (h : a = b) :
    modulePullbackFlatten f
        (eqToHom (congrArg (fun k : X ⟶ Y =>
          (modulePullback B S hS k).obj ((modulePullback B S hS f).obj M)) h)) =
      eqToHom (congrArg (fun k : X ⟶ Z => (modulePullback B S hS k).obj M)
        (congrArg (· ≫ f) h)) := by
  subst h
  simp [modulePullbackFlatten]

/-- **Reindexing is functorial.**  Reindexing along `g` and then along `f` is reindexing along
`f ≫ g`.  This is the associativity coherence of the comparison of inverse images. -/
theorem ModulePullbackCompIsoAssoc.modulePullbackReindex_comp
    (hassoc : ModulePullbackCompIsoAssoc B S hS) (f : V ⟶ W) (g : W ⟶ X) {a b : X ⟶ Y}
    {M : Modules.{u, u} B S hS Y.1 Y.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) :
    modulePullbackReindex f (modulePullbackReindex g α) =
      modulePullbackReindex (f ≫ g) α := by
  have hn := (modulePullbackCompIso B S hS f g).hom.naturality α
  simp only [Functor.comp_map] at hn
  simp only [modulePullbackReindex, Functor.map_comp, Category.assoc]
  rw [hassoc.hom_app f g b M, reassoc_of% hassoc.inv_app f g a M, reassoc_of% hn]
  simp

/-- **Flattening commutes with reindexing.**  This is the associativity coherence of the
comparison of inverse images. -/
theorem ModulePullbackCompIsoAssoc.modulePullbackFlatten_reindex
    (hassoc : ModulePullbackCompIsoAssoc B S hS) (f : V ⟶ W) (g : Y ⟶ Z) {a b : W ⟶ Y}
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj ((modulePullback B S hS g).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS g).obj M)) :
    modulePullbackFlatten g (modulePullbackReindex f α) =
      modulePullbackReindex f (modulePullbackFlatten g α) := by
  simp only [modulePullbackFlatten, modulePullbackReindex, Functor.map_comp, Category.assoc]
  rw [hassoc.hom_app f b g M, reassoc_of% hassoc.inv_app f a g M]

end AlgebraicGeometry.Space

end
