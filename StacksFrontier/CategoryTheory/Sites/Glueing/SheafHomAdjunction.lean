module

public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# The internal hom of sheaves of sets is right adjoint to the product

Let `(C, J)` be a small site. Mathlib's `CategoryTheory.sheafHom G F` is the sheaf of types
`V ↦ Mor_{Sh(C/V)}(G|_{C/V}, F|_{C/V})`, which is the sheaf that the Stacks Project writes
`SheafHom(G, F)` (Stacks 0BWQ and the discussion preceding it). Mathlib records as a `TODO`, in
`Mathlib/CategoryTheory/Sites/SheafHom.lean`, that `sheafHom` should be turned into a functor and
shown to be right adjoint to the product functor. This file does that for sheaves of sets.

## Main results

* `CategoryTheory.SheafHomAdj.prodPresheafIso`: the pointwise product of two presheaves of types is
  their categorical product; used to get concrete access to the sections of a product of sheaves.
* `CategoryTheory.SheafHomAdj.pair`: the section of `G ⨯ X` with prescribed components, with the
  expected `fst`/`snd`/restriction lemmas.
* `CategoryTheory.SheafHomAdj.prodSheafHomEquiv`: the bijection between maps `G × X ⟶ F` and maps
  `X ⟶ SheafHom(G, F)`, given by the source's own formula: `φ` corresponds to the family sending
  `s ∈ X(V)` to the map `G|_{C/V} → F|_{C/V}` which over `a : W → V` is `t ↦ φ(t, s|_W)`.
* `CategoryTheory.SheafHomAdj.sheafHomFunctor`: `SheafHom(G, -)` as a functor.
* `CategoryTheory.SheafHomAdj.prodSheafHomAdjunction`: the adjunction `(G × -) ⊣ SheafHom(G, -)`.

## Relation to Stacks 0BWQ

`prodSheafHomAdjunction` is the content of Stacks 0BWQ read with the Stacks Project's own
`SheafHom`. The tag 0BWQ is already claimed, in
`StacksFrontier/CategoryTheory/Sites/CartesianClosed.lean`, by the hom-equivalence of Mathlib's
abstract `MonoidalClosed (Sheaf J A)` instance; that file's module docstring flags that its
internal hom is *not* known to agree with `sheafHom`, so the displayed formula of the tag, read
with Stacks' `SheafHom`, was not established there. It is established here, but the tag is left
where it is: no tag is claimed in this file.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u

namespace CategoryTheory.SheafHomAdj

variable {C : Type u} [SmallCategory C]

/-- The pointwise product of two presheaves of types. -/
@[simps]
def prodPresheaf (P Q : Cᵒᵖ ⥤ Type u) : Cᵒᵖ ⥤ Type u where
  obj Z := P.obj Z × Q.obj Z
  map f := ↾fun x => (P.map f x.1, Q.map f x.2)
  map_id Z := by ext x <;> simp
  map_comp f g := by ext x <;> simp

section Presheaf
variable (P Q : Cᵒᵖ ⥤ Type u)

/-- First projection of `prodPresheaf`. -/
@[simps] def prodPresheafFst : prodPresheaf P Q ⟶ P where
  app _ := ↾fun x => x.1
  naturality _ _ _ := rfl

/-- Second projection of `prodPresheaf`. -/
@[simps] def prodPresheafSnd : prodPresheaf P Q ⟶ Q where
  app _ := ↾fun x => x.2
  naturality _ _ _ := rfl

/-- The map into `prodPresheaf` determined by its two components. -/
@[simps] def prodPresheafLift {T : Cᵒᵖ ⥤ Type u} (a : T ⟶ P) (b : T ⟶ Q) :
    T ⟶ prodPresheaf P Q where
  app Z := ↾fun t => (a.app Z t, b.app Z t)
  naturality {Z W} f := by
    ext t
    refine Prod.ext ?_ ?_
    · exact NatTrans.naturality_apply a f t
    · exact NatTrans.naturality_apply b f t

/-- `prodPresheaf` is a binary product. -/
def prodPresheafIsLimit : IsLimit (BinaryFan.mk (prodPresheafFst P Q) (prodPresheafSnd P Q)) :=
  BinaryFan.isLimitMk (fun s => prodPresheafLift P Q s.fst s.snd) (fun _ => rfl) (fun _ => rfl)
    (by
      intro s m h1 h2
      ext Z t
      refine Prod.ext ?_ ?_
      · exact congrArg (fun r : s.pt ⟶ P => (ConcreteCategory.hom (r.app Z)) t) h1
      · exact congrArg (fun r : s.pt ⟶ Q => (ConcreteCategory.hom (r.app Z)) t) h2)

/-- `prodPresheaf P Q` is the categorical product `P ⨯ Q`. -/
noncomputable def prodPresheafIso : prodPresheaf P Q ≅ P ⨯ Q :=
  (prodPresheafIsLimit P Q).conePointUniqueUpToIso (limit.isLimit (pair P Q))

/-- `prodPresheafIso` is compatible with the first projections. -/
@[simp] lemma prodPresheafIso_hom_fst :
    (prodPresheafIso P Q).hom ≫ prod.fst = prodPresheafFst P Q := by
  simp [prodPresheafIso]

/-- `prodPresheafIso` is compatible with the second projections. -/
@[simp] lemma prodPresheafIso_hom_snd :
    (prodPresheafIso P Q).hom ≫ prod.snd = prodPresheafSnd P Q := by
  simp [prodPresheafIso]

end Presheaf

section Sheaf
variable {J : GrothendieckTopology C}

/-- For sheaves of types, the underlying presheaf of the product is the pointwise product. -/
noncomputable def sheafProdObjIso (G X : Sheaf J (Type u)) :
    prodPresheaf G.obj X.obj ≅ (G ⨯ X).obj :=
  prodPresheafIso G.obj X.obj ≪≫ (PreservesLimitPair.iso (sheafToPresheaf J (Type u)) G X).symm

variable (G X : Sheaf J (Type u))

/-- `sheafToPresheaf` preserving the product `G ⨯ X` is compatible with the first projections. -/
@[simp] lemma preservesProd_inv_fst :
    (PreservesLimitPair.iso (sheafToPresheaf J (Type u)) G X).inv ≫ (prod.fst : G ⨯ X ⟶ G).hom
      = prod.fst := by
  rw [Iso.inv_comp_eq]
  simp [PreservesLimitPair.iso]

/-- `sheafToPresheaf` preserving the product `G ⨯ X` is compatible with the second
projections. -/
@[simp] lemma preservesProd_inv_snd :
    (PreservesLimitPair.iso (sheafToPresheaf J (Type u)) G X).inv ≫ (prod.snd : G ⨯ X ⟶ X).hom
      = prod.snd := by
  rw [Iso.inv_comp_eq]
  simp [PreservesLimitPair.iso]

/-- `sheafProdObjIso` carries the first projection of `G ⨯ X` to the first projection of the
pointwise product. -/
@[simp] lemma sheafProdObjIso_hom_fst :
    (sheafProdObjIso G X).hom ≫ (prod.fst : G ⨯ X ⟶ G).hom = prodPresheafFst G.obj X.obj := by
  simp [sheafProdObjIso]

/-- `sheafProdObjIso` carries the second projection of `G ⨯ X` to the second projection of the
pointwise product. -/
@[simp] lemma sheafProdObjIso_hom_snd :
    (sheafProdObjIso G X).hom ≫ (prod.snd : G ⨯ X ⟶ X).hom = prodPresheafSnd G.obj X.obj := by
  simp [sheafProdObjIso]

/-- The section of `G ⨯ X` over `Z` with components `g` and `x`. -/
noncomputable def pair {Z : Cᵒᵖ} (g : G.obj.obj Z) (x : X.obj.obj Z) : (G ⨯ X).obj.obj Z :=
  (sheafProdObjIso G X).hom.app Z (g, x)

/-- The first component of `pair G X g x` is `g`. -/
@[simp] lemma fst_pair {Z : Cᵒᵖ} (g : G.obj.obj Z) (x : X.obj.obj Z) :
    (prod.fst : G ⨯ X ⟶ G).hom.app Z (pair G X g x) = g :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (sheafProdObjIso_hom_fst G X) Z)
    ((g, x) : (prodPresheaf G.obj X.obj).obj Z)

/-- The second component of `pair G X g x` is `x`. -/
@[simp] lemma snd_pair {Z : Cᵒᵖ} (g : G.obj.obj Z) (x : X.obj.obj Z) :
    (prod.snd : G ⨯ X ⟶ X).hom.app Z (pair G X g x) = x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (sheafProdObjIso_hom_snd G X) Z)
    ((g, x) : (prodPresheaf G.obj X.obj).obj Z)

/-- The inverse of `sheafProdObjIso` carries the first projection of the pointwise product to the
first projection of `G ⨯ X`. -/
@[simp] lemma sheafProdObjIso_inv_fst :
    (sheafProdObjIso G X).inv ≫ prodPresheafFst G.obj X.obj = (prod.fst : G ⨯ X ⟶ G).hom := by
  rw [← sheafProdObjIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The inverse of `sheafProdObjIso` carries the second projection of the pointwise product to
the second projection of `G ⨯ X`. -/
@[simp] lemma sheafProdObjIso_inv_snd :
    (sheafProdObjIso G X).inv ≫ prodPresheafSnd G.obj X.obj = (prod.snd : G ⨯ X ⟶ X).hom := by
  rw [← sheafProdObjIso_hom_snd, Iso.inv_hom_id_assoc]

/-- A section of `G ⨯ X` is `pair` of its two components. -/
lemma pair_fst_snd {Z : Cᵒᵖ} (z : (G ⨯ X).obj.obj Z) :
    pair G X ((prod.fst : G ⨯ X ⟶ G).hom.app Z z) ((prod.snd : G ⨯ X ⟶ X).hom.app Z z) = z := by
  have hz : ((sheafProdObjIso G X).inv.app Z z : (prodPresheaf G.obj X.obj).obj Z)
      = ((prod.fst : G ⨯ X ⟶ G).hom.app Z z, (prod.snd : G ⨯ X ⟶ X).hom.app Z z) :=
    Prod.ext
      (by conv_rhs => rw [← sheafProdObjIso_inv_fst]
          rfl)
      (by conv_rhs => rw [← sheafProdObjIso_inv_snd]
          rfl)
  have : (sheafProdObjIso G X).hom.app Z ((sheafProdObjIso G X).inv.app Z z) = z :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (sheafProdObjIso G X).inv_hom_id Z) z
  rw [pair, ← hz, this]

/-- Every section of `G ⨯ X` is of the form `pair G X g x`. -/
private lemma exists_pair {Z : Cᵒᵖ} (z : (G ⨯ X).obj.obj Z) : ∃ g x, z = pair G X g x :=
  ⟨_, _, (pair_fst_snd G X z).symm⟩

/-- Restriction of a section of `G ⨯ X` is componentwise. -/
lemma pair_map {Z W : Cᵒᵖ} (f : Z ⟶ W) (g : G.obj.obj Z) (x : X.obj.obj Z) :
    (G ⨯ X).obj.map f (pair G X g x) = pair G X (G.obj.map f g) (X.obj.map f x) :=
  (NatTrans.naturality_apply (sheafProdObjIso G X).hom f ((g, x) : (prodPresheaf _ _).obj Z)).symm

end Sheaf

section Adj
variable {J : GrothendieckTopology C} (G F : Sheaf J (Type u))

variable {X : Sheaf J (Type u)}

/-- The section of `SheafHom(G, F)` over `V` attached to `φ : G × X ⟶ F` and `s ∈ X(V)`. -/
noncomputable def toPresheafHomApp (φ : G ⨯ X ⟶ F) {V : Cᵒᵖ} (s : X.obj.obj V) :
    (presheafHom G.obj F.obj).obj V where
  app a := ↾fun t => φ.hom.app (op a.unop.left) (pair G X t (X.obj.map a.unop.hom.op s))
  naturality := by
    intro a a' h
    ext t
    dsimp
    rw [← NatTrans.naturality_apply φ.hom h.unop.left.op, pair_map]
    congr 2
    rw [← Functor.map_comp_apply, ← op_comp, Over.w h.unop]

/-- The defining formula for `toPresheafHomApp`: over `a : W ⟶ V` it sends `t ∈ G(W)` to
`φ(t, s|_W)`. -/
@[simp] lemma toPresheafHomApp_app (φ : G ⨯ X ⟶ F) {V : Cᵒᵖ} (s : X.obj.obj V)
    (a : (Over V.unop)ᵒᵖ) (t : G.obj.obj (op a.unop.left)) :
    (toPresheafHomApp G F φ s).app a t
      = φ.hom.app (op a.unop.left) (pair G X t (X.obj.map a.unop.hom.op s)) := rfl

/-- `toPresheafHomApp` is compatible with restriction in `X`. -/
lemma toPresheafHomApp_naturality (φ : G ⨯ X ⟶ F) {V V' : Cᵒᵖ} (f : V ⟶ V')
    (s : X.obj.obj V) :
    toPresheafHomApp G F φ (X.obj.map f s)
      = (presheafHom G.obj F.obj).map f (toPresheafHomApp G F φ s) := by
  refine NatTrans.ext (funext fun a => ?_)
  refine Eq.trans ?_ (presheafHom_map_app (unop a).hom f.unop _ rfl _).symm
  exact congrArg (fun (y : X.obj.obj (op (unop a).left)) =>
      (↾fun t => φ.hom.app (op (unop a).left) (pair G X t y) :
        G.obj.obj (op (unop a).left) ⟶ F.obj.obj (op (unop a).left)))
    (show X.obj.map (unop a).hom.op (X.obj.map f s)
        = X.obj.map ((unop a).hom ≫ f.unop).op s by
      rw [op_comp, Functor.map_comp_apply, Quiver.Hom.op_unop])

/-- The map `X ⟶ SheafHom(G, F)` attached to a map `G × X ⟶ F`. -/
@[simps]
noncomputable def toPresheafHom (φ : G ⨯ X ⟶ F) : X.obj ⟶ presheafHom G.obj F.obj where
  app V := ↾fun s => toPresheafHomApp G F φ s
  naturality V V' f := by ext s; exact toPresheafHomApp_naturality G F φ f s

/-- Restricting a section of `presheafHom P Q` along `f : V ⟶ V'` and evaluating at the
tautological object of `C/V'.unop` is evaluating the original section at `f`. -/
lemma presheafHom_map_app_top {P Q : Cᵒᵖ ⥤ Type u} {V V' : Cᵒᵖ} (f : V ⟶ V')
    (α : (presheafHom P Q).obj V) :
    ((presheafHom P Q).map f α).app (op (Over.mk (𝟙 V'.unop)))
      = α.app (op (Over.mk f.unop)) :=
  presheafHom_map_app (𝟙 V'.unop) f.unop f.unop (by simp) α

/-- The value at `z ∈ (G × X)(V)` of the map `G × X ⟶ F` attached to `ψ : X ⟶ SheafHom(G, F)`. -/
noncomputable def ofPresheafHomApp (ψ : X.obj ⟶ presheafHom G.obj F.obj) {V : Cᵒᵖ}
    (z : (G ⨯ X).obj.obj V) : F.obj.obj V :=
  (ψ.app V ((prod.snd : G ⨯ X ⟶ X).hom.app V z)).app (op (Over.mk (𝟙 V.unop)))
    ((prod.fst : G ⨯ X ⟶ G).hom.app V z)

/-- `ofPresheafHomApp` is compatible with restriction, so it is a map of presheaves. -/
lemma ofPresheafHomApp_naturality (ψ : X.obj ⟶ presheafHom G.obj F.obj) {V V' : Cᵒᵖ}
    (f : V ⟶ V') (z : (G ⨯ X).obj.obj V) :
    ofPresheafHomApp G F ψ ((G ⨯ X).obj.map f z)
      = F.obj.map f (ofPresheafHomApp G F ψ z) := by
  obtain ⟨g, x, rfl⟩ := exists_pair G X z
  simp only [ofPresheafHomApp, pair_map, fst_pair, snd_pair,
    NatTrans.naturality_apply ψ f x, presheafHom_map_app_top]
  exact NatTrans.naturality_apply (ψ.app V x)
    (Over.homMk f.unop (by simp) : Over.mk f.unop ⟶ Over.mk (𝟙 V.unop)).op g

/-- The map `G × X ⟶ F` attached to a map `X ⟶ SheafHom(G, F)`. -/
noncomputable def ofPresheafHom (ψ : X.obj ⟶ presheafHom G.obj F.obj) : G ⨯ X ⟶ F :=
  Sheaf.homEquiv.symm
    { app := fun V => ↾fun z => ofPresheafHomApp G F ψ z
      naturality := by
        intro V V' f
        ext z
        exact ofPresheafHomApp_naturality G F ψ f z }

/-- `ofPresheafHom G F ψ` acts on sections by `ofPresheafHomApp`. -/
@[simp] lemma ofPresheafHom_hom_app (ψ : X.obj ⟶ presheafHom G.obj F.obj) {V : Cᵒᵖ}
    (z : (G ⨯ X).obj.obj V) :
    (ofPresheafHom G F ψ).hom.app V z = ofPresheafHomApp G F ψ z :=
  rfl

/-- `ofPresheafHom` undoes `toPresheafHom`. -/
lemma ofPresheafHom_toPresheafHom (φ : G ⨯ X ⟶ F) :
    ofPresheafHom G F (toPresheafHom G F φ) = φ := by
  apply Sheaf.hom_ext
  ext V z
  obtain ⟨g, x, rfl⟩ := exists_pair G X z
  simp only [TypeCat.Fun.toFun_apply, ofPresheafHom_hom_app, ofPresheafHomApp, fst_pair, snd_pair,
    toPresheafHom_app, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, toPresheafHomApp_app]
  simp

/-- `toPresheafHom` undoes `ofPresheafHom`. -/
lemma toPresheafHom_ofPresheafHom (ψ : X.obj ⟶ presheafHom G.obj F.obj) :
    toPresheafHom G F (ofPresheafHom G F ψ) = ψ := by
  refine NatTrans.ext (funext fun V => ?_)
  ext s
  refine NatTrans.ext (funext fun a => ?_)
  ext t
  simp only [TypeCat.Fun.toFun_apply, toPresheafHom_app, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    toPresheafHomApp_app, ofPresheafHom_hom_app, ofPresheafHomApp, fst_pair, snd_pair]
  rw [NatTrans.naturality_apply ψ (unop a).hom.op s, presheafHom_map_app_top]
  rfl

/-- **The internal-hom adjunction for sheaves of sets**, in bijection form: maps `G × X ⟶ F`
are the same thing as maps `X ⟶ SheafHom(G, F)`. -/
noncomputable def prodSheafHomEquiv (X : Sheaf J (Type u)) :
    (G ⨯ X ⟶ F) ≃ (X.obj ⟶ presheafHom G.obj F.obj) where
  toFun := toPresheafHom G F
  invFun := ofPresheafHom G F
  left_inv := ofPresheafHom_toPresheafHom G F
  right_inv := toPresheafHom_ofPresheafHom G F

end Adj

section Functor
variable {J : GrothendieckTopology C} (G : Sheaf J (Type u))

/-- `SheafHom(G, -)` on morphisms. -/
noncomputable def sheafHomMap {F F' : Sheaf J (Type u)} (ψ : F ⟶ F') :
    sheafHom G F ⟶ sheafHom G F' :=
  ⟨{ app := fun V => ↾fun φ => φ ≫ (J.overPullback (Type u) V.unop).map ψ
     naturality := by intro V V' f; ext φ; rfl }⟩

/-- The internal-hom functor `SheafHom(G, -) : Sh(C) ⥤ Sh(C)` for sheaves of sets. -/
noncomputable def sheafHomFunctor : Sheaf J (Type u) ⥤ Sheaf J (Type u) where
  obj F := sheafHom G F
  map ψ := sheafHomMap G ψ
  map_id F := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun V => ?_)
    ext φ
    change φ ≫ (J.overPullback (Type u) V.unop).map (𝟙 F) = φ
    rw [Functor.map_id]
    exact Category.comp_id (φ : (J.overPullback (Type u) V.unop).obj G ⟶ _)
  map_comp ψ ψ' := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun V => ?_)
    ext φ
    change φ ≫ (J.overPullback (Type u) V.unop).map (ψ ≫ ψ') = _
    simp only [Functor.map_comp]
    rfl

/-- Transport of `prodSheafHomEquiv` to `SheafHom` itself. -/
noncomputable def prodSheafHomEquiv' (F X : Sheaf J (Type u)) :
    ((prod.functor.obj G).obj X ⟶ F) ≃ (X ⟶ (sheafHomFunctor G).obj F) :=
  (prodSheafHomEquiv G F X).trans
    (((Iso.refl X.obj).homCongr (sheafHom'Iso G F)).symm.trans
      (Sheaf.homEquiv (J := J) (X := X) (Y := (sheafHomFunctor G).obj F)).symm)

/-- The map `G × X ⟶ F` attached to `χ : X ⟶ SheafHom(G, F)` sends a section `z` to the value of
`χ` at the second component of `z`, evaluated at the tautological object on the first. -/
@[simp] lemma prodSheafHomEquiv'_symm_app {F X : Sheaf J (Type u)}
    (χ : X ⟶ (sheafHomFunctor G).obj F)
    {V : Cᵒᵖ} (z : ((prod.functor.obj G).obj X).obj.obj V) :
    ((prodSheafHomEquiv' G F X).symm χ).hom.app V z
      = (Sheaf.homEquiv (χ.hom.app V ((prod.snd : G ⨯ X ⟶ X).hom.app V z))).app
          (op (Over.mk (𝟙 V.unop))) ((prod.fst : G ⨯ X ⟶ G).hom.app V z) := rfl

/-- `G × -` on morphisms is the identity on the first component. -/
@[simp] lemma fst_prod_functor_map {X' X : Sheaf J (Type u)} (f : X' ⟶ X) {V : Cᵒᵖ}
    (z : ((prod.functor.obj G).obj X').obj.obj V) :
    (prod.fst : G ⨯ X ⟶ G).hom.app V (((prod.functor.obj G).map f).hom.app V z)
      = (prod.fst : G ⨯ X' ⟶ G).hom.app V z := by
  have h : (prod.functor.obj G).map f ≫ (prod.fst : G ⨯ X ⟶ G) = (prod.fst : G ⨯ X' ⟶ G) :=
    show prod.map (𝟙 G) f ≫ (prod.fst : G ⨯ X ⟶ G) = _ by simp
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun (m : G ⨯ X' ⟶ G) => m.hom) h) V) z

/-- `G × -` on morphisms is the given morphism on the second component. -/
@[simp] lemma snd_prod_functor_map {X' X : Sheaf J (Type u)} (f : X' ⟶ X) {V : Cᵒᵖ}
    (z : ((prod.functor.obj G).obj X').obj.obj V) :
    (prod.snd : G ⨯ X ⟶ X).hom.app V (((prod.functor.obj G).map f).hom.app V z)
      = f.hom.app V ((prod.snd : G ⨯ X' ⟶ X').hom.app V z) := by
  have h : (prod.functor.obj G).map f ≫ (prod.snd : G ⨯ X ⟶ X)
      = (prod.snd : G ⨯ X' ⟶ X') ≫ f :=
    show prod.map (𝟙 G) f ≫ (prod.snd : G ⨯ X ⟶ X) = _ by simp
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun (m : G ⨯ X' ⟶ X) => m.hom) h) V) z

/-- The section that `prodSheafHomEquiv' φ` takes at `s` has `toPresheafHomApp G F φ s` as its
underlying map of presheaves. -/
@[simp] lemma prodSheafHomEquiv'_app_hom {F X : Sheaf J (Type u)}
    (φ : (prod.functor.obj G).obj X ⟶ F) {V : Cᵒᵖ} (s : X.obj.obj V) :
    ((((prodSheafHomEquiv' G F X) φ).hom.app V) s).hom = toPresheafHomApp G F φ s := rfl

/-- `SheafHom(G, -)` acts on a morphism `g : F ⟶ F'` by postcomposition with the restriction of
`g` to the slice site. -/
@[simp] lemma sheafHomFunctor_map_hom_app {F F' : Sheaf J (Type u)} (g : F ⟶ F') {V : Cᵒᵖ}
    (φ : ((sheafHomFunctor G).obj F).obj.obj V) :
    (((sheafHomFunctor G).map g).hom.app V) φ
      = φ ≫ (J.overPullback (Type u) V.unop).map g := rfl

/-- **Stacks 0BWQ for `SheafHom`.** For a sheaf of sets `G` on a site, the functor
`G × -` is left adjoint to the internal hom `SheafHom(G, -)`. -/
noncomputable def prodSheafHomAdjunction : prod.functor.obj G ⊣ sheafHomFunctor G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X F => prodSheafHomEquiv' G F X
      homEquiv_naturality_left_symm := by
        intro X' X F f g
        apply Sheaf.hom_ext
        refine NatTrans.ext (funext fun V => ?_)
        ext z
        simp only [TypeCat.Fun.toFun_apply, ObjectProperty.FullSubcategory.comp_hom,
          NatTrans.comp_app, ConcreteCategory.comp_apply, prodSheafHomEquiv'_symm_app,
          fst_prod_functor_map, snd_prod_functor_map]
        rfl
      homEquiv_naturality_right := by
        intro X F F' f g
        apply Sheaf.hom_ext
        refine NatTrans.ext (funext fun V => ?_)
        ext s
        apply Sheaf.hom_ext
        refine NatTrans.ext (funext fun a => ?_)
        ext t
        simp only [TypeCat.Fun.toFun_apply, ObjectProperty.FullSubcategory.comp_hom,
          NatTrans.comp_app, ConcreteCategory.comp_apply, prodSheafHomEquiv'_app_hom,
          sheafHomFunctor_map_hom_app]
        rfl }

end Functor

end CategoryTheory.SheafHomAdj
