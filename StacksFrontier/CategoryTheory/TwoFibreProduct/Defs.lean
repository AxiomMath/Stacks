module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# 2-fibre products in a (2,1)-category (Stacks 003O, 003Q)

We work in a `(2,1)`-category: a bicategory `B` in which every 2-morphism is invertible.
The invertibility is not imposed as an axiom; instead, every 2-morphism that the source
requires to be invertible is taken here to be an isomorphism `≅` in the relevant
hom-category. This is the *abstract* 2-fibre product of Stacks 003Q, not the concrete
2-fibre product of categories over a base.

Fix a cospan `f : x ⟶ z`, `g : y ⟶ z`. A **2-commutative square** over it (`TwoCommSq f g`,
the objects of Stacks 003O) is an object `pt` with 1-morphisms `fst : pt ⟶ x`,
`snd : pt ⟶ y` and an invertible 2-morphism `fst ≫ f ≅ snd ≫ g`. A morphism of such
squares, in the source, is a 1-morphism `k` between the apexes together with invertible
2-cells comparing the two legs, subject to one compatibility square; but composition of
those data is only associative and unital *up to* an invertible 2-cell, so they do not
form a category on the nose. They are recorded here as `TwoCommSq.PreHom`, and the
morphisms of the category of Stacks 003O are their classes modulo the 2-cell equivalence
`TwoCommSq.PreHom.Rel` (`F` and `G` are equivalent when an invertible `θ : F.hom ≅ G.hom`
matches up their comparison 2-cells). Passing to that quotient is what makes
`TwoCommSq.category` a strict `Category`.

A **2-fibre product** of `f` and `g` (Stacks 003Q) is then a terminal object of that
category: `IsTwoFibreProduct`. Unfolding the definition, a terminal object supplies the
projections `p`, `q` and the invertible `ψ : f ∘ p ⟶ g ∘ q` of the source as its `fst`,
`snd` and `iso` fields, and the terminality is the universal property. Being terminal, a
2-fibre product is unique up to unique isomorphism, which is
`twoFibreProduct_uniqueUpToIso` together with `twoFibreProduct_iso_subsingleton`.

Since the morphisms of the category are classes, the mediating morphism terminality supplies is
a class; `twoFibreProductPreHom` picks a representative of it and `twoFibreProductPreHom_rel`
says any two representatives are 2-cell equivalent. That pair is the universal property in the
form a consumer computing with the mediating 1-morphism uses.
-/

@[expose] public section

open CategoryTheory Bicategory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u
variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B}

/-! ### Bicategorical coherence identities -/

/-- A pentagon-style coherence identity for reassociating whiskered composites. -/
private theorem associator_inv_whiskerRight_associator {a b c d e : B}
    (p : a ⟶ b) (q : b ⟶ c) (u : c ⟶ d) (gg : d ⟶ e) :
    (α_ p (q ≫ u) gg).inv ≫ (α_ p q u).inv ▷ gg ≫ (α_ (p ≫ q) u gg).hom
      = p ◁ (α_ q u gg).hom ≫ (α_ p q (u ≫ gg)).inv := by
  bicategory

/-- A coherence/naturality identity used to close the compatibility square of a
composite cone morphism. -/
private theorem whiskerLeft_associator_naturality {a b c d1 d2 e₁ : B}
    (p : a ⟶ b) (q : b ⟶ c) (u1 : c ⟶ d1) (u2 : c ⟶ d2) (f1 : d1 ⟶ e₁) (g1 : d2 ⟶ e₁)
    (η : u1 ≫ f1 ⟶ u2 ≫ g1) :
    p ◁ (α_ q u1 f1).hom ≫ (p ◁ q ◁ η) ≫ (α_ p q (u2 ≫ g1)).inv
      = (α_ p (q ≫ u1) f1).inv ≫ (α_ p q u1).inv ▷ f1 ≫ (α_ (p ≫ q) u1 f1).hom ≫ (p ≫ q) ◁ η := by
  rw [associator_inv_naturality_right]; bicategory

/-- The naturality "leg" used to show that composition respects the 2-cell equivalence. -/
private theorem comp_whiskerRight_of_rel {t s c d : B}
    (Fh Fh' : t ⟶ s) (Gh Gh' : s ⟶ c) (Uf : c ⟶ d)
    (θ : Fh ≅ Fh') (ψ : Gh ≅ Gh')
    (Tf : t ⟶ d) (Sf : s ⟶ d)
    (Ffst : Tf ⟶ Fh ≫ Sf) (Ffst' : Tf ⟶ Fh' ≫ Sf)
    (Gfst : Sf ⟶ Gh ≫ Uf) (Gfst' : Sf ⟶ Gh' ≫ Uf)
    (hθ : Ffst ≫ θ.hom ▷ Sf = Ffst')
    (hψ : Gfst ≫ ψ.hom ▷ Uf = Gfst') :
    (Ffst ≫ Fh ◁ Gfst ≫ (α_ Fh Gh Uf).inv) ≫ (θ.hom ▷ Gh ≫ Fh' ◁ ψ.hom) ▷ Uf
      = Ffst' ≫ Fh' ◁ Gfst' ≫ (α_ Fh' Gh' Uf).inv := by
  subst hθ hψ
  simp only [comp_whiskerRight, whisker_assoc, Category.assoc]
  have e1 : (α_ Fh Gh Uf).inv ≫ θ.hom ▷ Gh ▷ Uf ≫ (α_ Fh' Gh Uf).hom = θ.hom ▷ (Gh ≫ Uf) := by
    simp
  rw [reassoc_of% e1, whisker_exchange_assoc]
  simp

/-! ### Definition 1: 2-commutative cones over a cospan -/

/-- A **2-commutative cone** over the cospan `(f, g)`: an object `pt` together with
1-morphisms `fst : pt ⟶ x`, `snd : pt ⟶ y` and an invertible 2-morphism
`iso : fst ≫ f ≅ snd ≫ g` filling the square.

**Stacks 003O.** These are the objects of the category of 2-commutative diagrams over
the cospan `(f, g)`. -/
@[stacks_fixed 003O]
structure TwoCommSq (f : x ⟶ z) (g : y ⟶ z) where
  /-- the apex object `w` of the cone -/
  pt : B
  /-- the 1-morphism `a : w ⟶ x` -/
  fst : pt ⟶ x
  /-- the 1-morphism `b : w ⟶ y` -/
  snd : pt ⟶ y
  /-- the invertible filler `γ : a ≫ f ≅ b ≫ g` -/
  iso : fst ≫ f ≅ snd ≫ g

variable {f : x ⟶ z} {g : y ⟶ z}

/-! ### Definition 2: pre-morphisms of cones and the 2-cell equivalence -/

/-- A **pre-morphism of cones** `T ⟶ S`: a 1-morphism `hom : T.pt ⟶ S.pt` together with
invertible comparison 2-cells `isoFst : T.fst ≅ hom ≫ S.fst`, `isoSnd : T.snd ≅ hom ≫ S.snd`
subject to the Stacks 003O compatibility square.

**Stacks 003O.** These are the morphisms of the category of 2-commutative diagrams, before
passing to classes modulo the 2-cell equivalence `TwoCommSq.PreHom.Rel`. -/
@[stacks_fixed 003O]
structure TwoCommSq.PreHom (T S : TwoCommSq f g) where
  /-- the underlying 1-morphism `k : w' ⟶ w` -/
  hom : T.pt ⟶ S.pt
  /-- the comparison `α : a' ≅ k ≫ a` -/
  isoFst : T.fst ≅ hom ≫ S.fst
  /-- the comparison `β : b' ≅ k ≫ b` -/
  isoSnd : T.snd ≅ hom ≫ S.snd
  /-- the compatibility square of Stacks 003O (condition (2)) -/
  compat : T.iso.hom ≫ (isoSnd.hom ▷ g) ≫ (α_ hom S.snd g).hom =
      (isoFst.hom ▷ f) ≫ (α_ hom S.fst f).hom ≫ (hom ◁ S.iso.hom)

namespace TwoCommSq.PreHom

/-- The identity pre-morphism of a cone (Stacks 003O identity, using the left unitors). -/
def id (T : TwoCommSq f g) : TwoCommSq.PreHom T T where
  hom := 𝟙 T.pt
  isoFst := (λ_ T.fst).symm
  isoSnd := (λ_ T.snd).symm
  compat := by simp

/-- Composition of pre-morphisms of cones (Stacks 003O composition rule, in bicategory
order, reassociated). -/
def comp {T S U : TwoCommSq f g} (F : TwoCommSq.PreHom T S) (G : TwoCommSq.PreHom S U) :
    TwoCommSq.PreHom T U where
  hom := F.hom ≫ G.hom
  isoFst := F.isoFst ≪≫ whiskerLeftIso F.hom G.isoFst ≪≫ (α_ F.hom G.hom U.fst).symm
  isoSnd := F.isoSnd ≪≫ whiskerLeftIso F.hom G.isoSnd ≪≫ (α_ F.hom G.hom U.snd).symm
  compat := by
    have hF := F.compat
    have hG := G.compat
    have key : F.hom ◁ (S.iso.hom ≫ G.isoSnd.hom ▷ g ≫ (α_ G.hom U.snd g).hom)
        = F.hom ◁ (G.isoFst.hom ▷ f ≫ (α_ G.hom U.fst f).hom ≫ G.hom ◁ U.iso.hom) :=
      congrArg (fun t => F.hom ◁ t) hG
    simp only [whiskerLeft_comp] at key
    dsimp
    -- `whiskerLeftIso` is a plain `def`, so `dsimp` can no longer unfold its `hom`
    -- projection; name the `@[simps]` lemma explicitly.
    simp only [whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc, Category.assoc]
    rw [reassoc_of% hF, associator_inv_whiskerRight_associator F.hom G.hom U.snd g, reassoc_of% key,
      whiskerLeft_associator_naturality F.hom G.hom U.fst U.snd f g U.iso.hom]

/-- Two pre-morphisms of cones are **equivalent** when they are related by an invertible
2-cell `θ` between their underlying 1-morphisms, compatible with the comparison
isomorphisms.  In a `(2,1)`-category this is the natural notion of 2-isomorphism of cone
morphisms; the category `TwoCommSq (f, g)` of Stacks 003O is the quotient by it. -/
def Rel {T S : TwoCommSq f g} (F G : TwoCommSq.PreHom T S) : Prop :=
  ∃ θ : F.hom ≅ G.hom,
    F.isoFst.hom ≫ (θ.hom ▷ S.fst) = G.isoFst.hom ∧
    F.isoSnd.hom ≫ (θ.hom ▷ S.snd) = G.isoSnd.hom

/-- Reflexivity of the 2-cell equivalence: the identity 2-cell on `F.hom` relates `F` to itself.
One of the three components of `TwoCommSq.PreHom.setoid`. -/
theorem Rel.refl {T S : TwoCommSq f g} (F : TwoCommSq.PreHom T S) : Rel F F :=
  ⟨Iso.refl _, by simp, by simp⟩

/-- Symmetry of the 2-cell equivalence: invert the mediating 2-cell `θ`, its compatibility with
the comparison isomorphisms following by whiskering `θ.inv` on the other side.
One of the three components of `TwoCommSq.PreHom.setoid`. -/
theorem Rel.symm {T S : TwoCommSq f g} {F G : TwoCommSq.PreHom T S} (h : Rel F G) : Rel G F := by
  obtain ⟨θ, h1, h2⟩ := h
  refine ⟨θ.symm, ?_, ?_⟩
  · rw [← h1]; simp [← comp_whiskerRight]
  · rw [← h2]; simp [← comp_whiskerRight]

/-- Transitivity of the 2-cell equivalence: the mediating 2-cell is the composite `θ ≪≫ ψ` of the
two given ones. One of the three components of `TwoCommSq.PreHom.setoid`. -/
theorem Rel.trans {T S : TwoCommSq f g} {F G H : TwoCommSq.PreHom T S}
    (h1 : Rel F G) (h2 : Rel G H) : Rel F H := by
  obtain ⟨θ, a1, a2⟩ := h1
  obtain ⟨ψ, b1, b2⟩ := h2
  refine ⟨θ ≪≫ ψ, ?_, ?_⟩
  · simp [← a1, ← b1]
  · simp [← a2, ← b2]

/-- The 2-cell equivalence as a `Setoid` on pre-morphisms of cones. -/
instance setoid (T S : TwoCommSq f g) : Setoid (TwoCommSq.PreHom T S) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- Composition respects the 2-cell equivalence. -/
theorem comp_rel {T S U : TwoCommSq f g} {F F' : TwoCommSq.PreHom T S} {G G' : TwoCommSq.PreHom S U}
    (hF : Rel F F') (hG : Rel G G') : Rel (F.comp G) (F'.comp G') := by
  obtain ⟨θ, θ1, θ2⟩ := hF
  obtain ⟨ψ, ψ1, ψ2⟩ := hG
  refine ⟨whiskerRightIso θ G.hom ≪≫ whiskerLeftIso F'.hom ψ, ?_, ?_⟩
  · exact comp_whiskerRight_of_rel F.hom F'.hom G.hom G'.hom U.fst θ ψ T.fst S.fst
      F.isoFst.hom F'.isoFst.hom G.isoFst.hom G'.isoFst.hom θ1 ψ1
  · exact comp_whiskerRight_of_rel F.hom F'.hom G.hom G'.hom U.snd θ ψ T.snd S.snd
      F.isoSnd.hom F'.isoSnd.hom G.isoSnd.hom G'.isoSnd.hom θ2 ψ2

/-- Left unitality of composition of pre-morphisms, up to the 2-cell equivalence: `(id T).comp F`
is related to `F` by the left unitor `λ_ F.hom`. On the quotient this becomes the `id_comp` axiom
of `TwoCommSq.category`. -/
theorem id_comp_rel {T S : TwoCommSq f g} (F : TwoCommSq.PreHom T S) : Rel ((id T).comp F) F := by
  refine ⟨λ_ F.hom, ?_, ?_⟩ <;>
  · dsimp [comp, id]
    simp only [Category.assoc]
    simp

/-- Right unitality of composition of pre-morphisms, up to the 2-cell equivalence: `F.comp (id S)`
is related to `F` by the right unitor `ρ_ F.hom`. On the quotient this becomes the `comp_id` axiom
of `TwoCommSq.category`. -/
theorem comp_id_rel {T S : TwoCommSq f g} (F : TwoCommSq.PreHom T S) : Rel (F.comp (id S)) F := by
  refine ⟨ρ_ F.hom, ?_, ?_⟩ <;>
  · dsimp [comp, id]
    simp

/-- Associativity of composition of pre-morphisms, up to the 2-cell equivalence: the two
bracketings are related by the associator `α_ F.hom G.hom H.hom`. On the quotient this becomes the
`assoc` axiom of `TwoCommSq.category`, which is why passing to classes is needed to get a strict
`Category`. -/
theorem assoc_rel {T S U V : TwoCommSq f g}
    (F : TwoCommSq.PreHom T S) (G : TwoCommSq.PreHom S U) (H : TwoCommSq.PreHom U V) :
    Rel ((F.comp G).comp H) (F.comp (G.comp H)) := by
  refine ⟨α_ F.hom G.hom H.hom, ?_, ?_⟩ <;>
  · dsimp [comp]
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc, whiskerLeft_comp]
    bicategory

end TwoCommSq.PreHom

/-! ### The category `TwoCommSq (f, g)` of Stacks 003O -/

/-- Morphisms in the category `TwoCommSq (f, g)`: pre-morphisms modulo the 2-cell equivalence. -/
def TwoCommSq.Hom (T S : TwoCommSq f g) : Type _ := Quotient (TwoCommSq.PreHom.setoid T S)

/-- **Stacks 003O.** The category of 2-commutative diagrams over the cospan `(f, g)`:
objects are the 2-commutative squares, and morphisms are pre-morphisms modulo the 2-cell
equivalence, which is what makes composition strictly associative and unital. -/
@[stacks 003O]
instance TwoCommSq.category : Category (TwoCommSq f g) where
  Hom T S := TwoCommSq.Hom T S
  id T := Quotient.mk _ (TwoCommSq.PreHom.id T)
  comp {T S U} F G :=
    Quotient.map₂ TwoCommSq.PreHom.comp
      (fun _ _ hF _ _ hG => TwoCommSq.PreHom.comp_rel hF hG) F G
  id_comp {T S} F := by
    refine Quotient.inductionOn F (fun F => ?_)
    exact Quotient.sound (TwoCommSq.PreHom.id_comp_rel F)
  comp_id {T S} F := by
    refine Quotient.inductionOn F (fun F => ?_)
    exact Quotient.sound (TwoCommSq.PreHom.comp_id_rel F)
  assoc {T S U V} F G H := by
    refine Quotient.inductionOn₃ F G H (fun F G H => ?_)
    exact Quotient.sound (TwoCommSq.PreHom.assoc_rel F G H)

/-! ### Definition 3: the 2-fibre product predicate (Stacks 003Q) -/

/-- **Stacks 003Q.** A 2-commutative square `P` over `(f, g)` is a **2-fibre product** of
`f` and `g` when it is a terminal (final) object of the category `TwoCommSq f g` of
2-commutative diagrams. Its `fst`, `snd` and `iso` fields are the projections `p`, `q` and
the invertible `ψ : f ∘ p ⟶ g ∘ q` of the source. -/
@[stacks 003Q]
abbrev IsTwoFibreProduct (P : TwoCommSq f g) : Type _ := IsTerminal P

/-- **A pre-morphism realizing the mediating morphism into a 2-fibre product.** A morphism of
`TwoCommSq f g` is a pre-morphism modulo the 2-cell equivalence, so the mediating morphism
`Q ⟶ P` supplied by terminality of `P` is only a class; this chooses a representative, which is
what a consumer that has to compute with the mediating 1-morphism needs. -/
noncomputable def twoFibreProductPreHom {P : TwoCommSq f g} (hP : IsTwoFibreProduct P)
    (Q : TwoCommSq f g) : TwoCommSq.PreHom Q P :=
  Quotient.out (hP.from Q)

/-- **Any two pre-morphisms into a 2-fibre product are 2-cell equivalent.** Terminality of `P`
makes the two classes they define equal, and the 2-cell equivalence is the kernel of the
quotient. -/
theorem twoFibreProductPreHom_rel {P Q : TwoCommSq f g} (hP : IsTwoFibreProduct P)
    (L M : TwoCommSq.PreHom Q P) : TwoCommSq.PreHom.Rel L M :=
  Quotient.exact (hP.hom_ext (Quotient.mk _ L) (Quotient.mk _ M))

/-! ### Main Statement: uniqueness of 2-fibre products -/

/-- **Uniqueness of 2-fibre products (the comparison isomorphism).**
Any two 2-fibre products of the same cospan `(f, g)` are isomorphic as objects of
`TwoCommSq (f, g)`.  Since both are terminal objects, the isomorphism is the canonical one
of `CategoryTheory.Limits.IsTerminal.uniqueUpToIso`. -/
theorem twoFibreProduct_uniqueUpToIso {P₁ P₂ : TwoCommSq f g}
    (hP₁ : IsTwoFibreProduct P₁) (hP₂ : IsTwoFibreProduct P₂) :
    Nonempty (P₁ ≅ P₂) :=
  ⟨hP₁.uniqueUpToIso hP₂⟩

/-- **Uniqueness of the comparison isomorphism.**  Any two isomorphisms from a
2-commutative square to a 2-fibre product of the same cospan `(f, g)` are equal; so the
comparison isomorphism of `twoFibreProduct_uniqueUpToIso` is the unique isomorphism
`P₁ ≅ P₂`, and 2-fibre products are unique up to unique isomorphism. Terminality of `P₂`
alone suffices, since it already forces any two morphisms into `P₂` to agree. -/
theorem twoFibreProduct_iso_subsingleton {P₁ P₂ : TwoCommSq f g}
    (hP₂ : IsTwoFibreProduct P₂) :
    Subsingleton (P₁ ≅ P₂) :=
  ⟨fun i j => Iso.ext (hP₂.hom_ext i.hom j.hom)⟩

end CategoryTheory.Bicategory
