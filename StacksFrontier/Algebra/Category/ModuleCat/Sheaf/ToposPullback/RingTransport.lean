module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Transporting a ring structure along a finite-product-preserving functor

An element calculus for functors to types preserving finite products (`prodObjEquiv`,
`prodObjMk`), the sections functor of a sheaf of types, the sheaf condition for a presheaf of
rings (`isSheaf_ringCat_of_isSheaf_forget`), morphisms of sheaves of types given by pointwise
operations, the ring operations of a sheaf of rings on its underlying sheaf of sets, and the
transported ring `ringObjRing` they induce on the image of that sheaf under a
finite-product-preserving functor to types.
-/

@[expose] public section

open CategoryTheory Limits

universe t t' w v u

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D]

section

variable (P : D ⥤ Type t) [PreservesFiniteProducts P]

/-- For a functor `P` to types which preserves finite products, an element of `P (A ⨯ B)` is
the same thing as a pair consisting of an element of `P A` and an element of `P B`. -/
noncomputable def prodObjEquiv (A B : D) : P.obj (A ⨯ B) ≃ P.obj A × P.obj B :=
  (PreservesLimitPair.iso P A B).toEquiv.trans
    (Types.binaryProductIso (P.obj A) (P.obj B)).toEquiv

/-- The first component of `prodObjEquiv P A B x` is the image of `x` under the first
projection. -/
@[simp]
lemma prodObjEquiv_apply_fst {A B : D} (x : P.obj (A ⨯ B)) :
    (prodObjEquiv P A B x).1 = P.map prod.fst x := by
  simp only [prodObjEquiv, Equiv.trans_apply, Iso.toEquiv_fun,
    Types.binaryProductIso_hom_comp_fst_apply]
  have h := ConcreteCategory.congr_hom
    (PreservesLimitPair.iso_inv_fst P A B) ((PreservesLimitPair.iso P A B).hom x)
  rw [types_comp_apply] at h
  simp only [← types_comp_apply (PreservesLimitPair.iso P A B).hom
    (PreservesLimitPair.iso P A B).inv, Iso.hom_inv_id, types_id_apply] at h
  exact h.symm

/-- The second component of `prodObjEquiv P A B x` is the image of `x` under the second
projection. -/
@[simp]
lemma prodObjEquiv_apply_snd {A B : D} (x : P.obj (A ⨯ B)) :
    (prodObjEquiv P A B x).2 = P.map prod.snd x := by
  simp only [prodObjEquiv, Equiv.trans_apply, Iso.toEquiv_fun,
    Types.binaryProductIso_hom_comp_snd_apply]
  have h := ConcreteCategory.congr_hom
    (PreservesLimitPair.iso_inv_snd P A B) ((PreservesLimitPair.iso P A B).hom x)
  rw [types_comp_apply] at h
  simp only [← types_comp_apply (PreservesLimitPair.iso P A B).hom
    (PreservesLimitPair.iso P A B).inv, Iso.hom_inv_id, types_id_apply] at h
  exact h.symm

end

variable {P : D ⥤ Type t} [PreservesFiniteProducts P]

/-- The element of `P (A ⨯ B)` corresponding to a pair of elements of `P A` and `P B`, for a
functor `P` to types which preserves finite products. -/
noncomputable def prodObjMk {A B : D} (a : P.obj A) (b : P.obj B) : P.obj (A ⨯ B) :=
  (prodObjEquiv P A B).symm (a, b)

/-- The first projection sends `prodObjMk a b` to `a`. -/
@[simp]
lemma map_fst_prodObjMk {A B : D} (a : P.obj A) (b : P.obj B) :
    P.map prod.fst (prodObjMk a b) = a := by
  rw [← prodObjEquiv_apply_fst, prodObjMk, Equiv.apply_symm_apply]

/-- The second projection sends `prodObjMk a b` to `b`. -/
@[simp]
lemma map_snd_prodObjMk {A B : D} (a : P.obj A) (b : P.obj B) :
    P.map prod.snd (prodObjMk a b) = b := by
  rw [← prodObjEquiv_apply_snd, prodObjMk, Equiv.apply_symm_apply]

/-- Two elements of `P (A ⨯ B)` are equal if their images under both projections are equal. -/
lemma prodObjMk_ext {A B : D} {x y : P.obj (A ⨯ B)}
    (h₁ : P.map prod.fst x = P.map prod.fst y) (h₂ : P.map prod.snd x = P.map prod.snd y) :
    x = y :=
  (prodObjEquiv P A B).injective (Prod.ext (by simpa using h₁) (by simpa using h₂))

/-- Every element of `P (A ⨯ B)` is `prodObjMk` of its images under the two projections. -/
@[simp]
lemma prodObjMk_map_fst_map_snd {A B : D} (x : P.obj (A ⨯ B)) :
    prodObjMk (P.map prod.fst x) (P.map prod.snd x) = x :=
  prodObjMk_ext (by simp) (by simp)

/-- The image under `P` of a morphism into a binary product, computed on elements. -/
@[simp]
lemma map_lift_apply {Z A B : D} (g : Z ⟶ A) (h : Z ⟶ B) (z : P.obj Z) :
    P.map (prod.lift g h) z = prodObjMk (P.map g z) (P.map h z) :=
  prodObjMk_ext
    (by rw [map_fst_prodObjMk, ← P.map_comp_apply, prod.lift_fst])
    (by rw [map_snd_prodObjMk, ← P.map_comp_apply, prod.lift_snd])

/-- The image under `P` of a product of two morphisms, computed on elements. -/
@[simp]
lemma map_prodMap_apply {A A' B B' : D} (g : A ⟶ A') (h : B ⟶ B') (z : P.obj (A ⨯ B)) :
    P.map (prod.map g h) z =
      prodObjMk (P.map g (P.map prod.fst z)) (P.map h (P.map prod.snd z)) :=
  prodObjMk_ext
    (by rw [map_fst_prodObjMk, ← P.map_comp_apply, ← P.map_comp_apply, prod.map_fst])
    (by rw [map_snd_prodObjMk, ← P.map_comp_apply, ← P.map_comp_apply, prod.map_snd])

/-- The product comparison of a functor `Ψ`, computed on elements after applying a
finite-product-preserving functor `P` to types. -/
@[simp]
lemma map_prodComparison_apply {B : Type*} [Category B] [HasFiniteProducts B] (Ψ : B ⥤ D)
    [PreservesFiniteProducts (Ψ ⋙ P)] (A A' : B) (p : P.obj (Ψ.obj (A ⨯ A'))) :
    P.map (Limits.prodComparison Ψ A A') p =
      prodObjMk (P := P) (A := Ψ.obj A) (B := Ψ.obj A')
        ((Ψ ⋙ P).map prod.fst p) ((Ψ ⋙ P).map prod.snd p) :=
  prodObjMk_ext
    (by rw [map_fst_prodObjMk, ← P.map_comp_apply, Limits.prodComparison_fst]; rfl)
    (by rw [map_snd_prodObjMk, ← P.map_comp_apply, Limits.prodComparison_snd]; rfl)

/-- A functor to types which preserves finite products sends the terminal object to a
singleton. -/
noncomputable instance uniqueTerminalObj : Unique (P.obj (⊤_ D)) :=
  Equiv.unique (β := PUnit.{t + 1})
    (Iso.toEquiv (PreservesTerminal.iso P ≪≫ Types.terminalIso))

/-- The image of an element under the morphism to the terminal object is the unique element of
`P (⊤_ D)`. -/
@[simp]
lemma map_terminalFrom_apply {Z : D} (z : P.obj Z) :
    P.map (terminal.from Z) z = default :=
  Subsingleton.elim _ _

omit [HasFiniteProducts D] [PreservesFiniteProducts P] in
/-- A natural transformation of functors to types, on elements. -/
lemma natTrans_app_map_apply {Q : D ⥤ Type t} (θ : P ⟶ Q) {A B : D} (m : A ⟶ B) (x : P.obj A) :
    θ.app B (P.map m x) = Q.map m (θ.app A x) := by
  rw [← types_comp_apply (P.map m) (θ.app B), θ.naturality, types_comp_apply]

/-- A natural transformation sends the image of the unique element of `P (⊤_ D)` under a map
`m` to the image of the unique element of `Q (⊤_ D)` under `m`. -/
private lemma natTrans_app_map_default {Q : D ⥤ Type t} [PreservesFiniteProducts Q]
    (θ : P ⟶ Q) {A : D} (m : ⊤_ D ⟶ A) :
    θ.app A (P.map m default) = Q.map m default := by
  rw [natTrans_app_map_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- A natural transformation between finite-product-preserving functors to types commutes with
`prodObjMk`. -/
lemma prodObjMk_naturality {Q : D ⥤ Type t} [PreservesFiniteProducts Q] (θ : P ⟶ Q)
    {A B : D} (a : P.obj A) (b : P.obj B) :
    θ.app (A ⨯ B) (prodObjMk a b) = prodObjMk (θ.app A a) (θ.app B b) :=
  prodObjMk_ext
    (by rw [map_fst_prodObjMk, ← types_comp_apply (θ.app _) (Q.map _), ← θ.naturality,
      types_comp_apply, map_fst_prodObjMk])
    (by rw [map_snd_prodObjMk, ← types_comp_apply (θ.app _) (Q.map _), ← θ.naturality,
      types_comp_apply, map_snd_prodObjMk])

end CategoryTheory.Functor

/-! ## Sections of a sheaf of types -/

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The functor taking a sheaf of types to its sections over a fixed object.

This is deliberately a `def` rather than an `abbrev`: all the computation rules below are
stated in terms of it, and they would not match syntactically if it unfolded. It is a composite
of two finite-product-preserving functors, which is recorded as an instance just below. -/
def sectionsFunctor (X : Cᵒᵖ) : Sheaf J (Type w) ⥤ Type w :=
  sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj X

/-- The sections functor over a fixed object preserves finite products. -/
noncomputable instance (X : Cᵒᵖ) : PreservesFiniteProducts (sectionsFunctor.{w} J X) := by
  delta sectionsFunctor
  infer_instance

variable {J}

/-- The sections functor over `X` sends a morphism of sheaves of types to its component at
`X`. -/
lemma sectionsFunctor_map_apply {X : Cᵒᵖ} {A B : Sheaf J (Type w)} (m : A ⟶ B)
    (s : A.obj.obj X) : (sectionsFunctor J X).map m s = m.hom.app X s := rfl

/-- Two morphisms of sheaves of types agree as soon as they agree on all sections. -/
lemma hom_ext_sections {A B : Sheaf J (Type w)} {m m' : A ⟶ B}
    (h : ∀ (X : Cᵒᵖ) (s : (sectionsFunctor J X).obj A),
      (sectionsFunctor J X).map m s = (sectionsFunctor J X).map m' s) :
    m = m' := by
  apply Sheaf.hom_ext
  ext X s
  exact h X s

/-- Restriction of sections, as a natural transformation between sections functors. -/
@[simps]
def sectionsRestrict {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    sectionsFunctor.{w} J X ⟶ sectionsFunctor.{w} J Y where
  app A := A.obj.map g
  naturality _ _ m := (m.hom.naturality g).symm

end CategoryTheory.Sheaf

/-! ## The sheaf condition for a presheaf of rings -/

namespace CategoryTheory.Presheaf

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Sections of a sheaf of types are separated: two sections which agree after restriction
along every arrow of a cover are equal. Unlike `Presheaf.IsSheaf.isSeparated` this is stated for
sheaves of types in an arbitrary universe, with no `HasSheafCompose` hypothesis. -/
lemma eq_of_isSheaf {Q : Cᵒᵖ ⥤ Type w} (hQ : Presheaf.IsSheaf J Q) {X : C} (S : J.Cover X)
    {a b : Q.obj (op X)} (hab : ∀ I : S.Arrow, Q.map I.f.op a = Q.map I.f.op b) : a = b := by
  have h₁ : (↾(fun _ ↦ a) : (PUnit.{w + 1} : Type w) ⟶ Q.obj (op X)) = ↾(fun _ ↦ b) := by
    refine hQ.hom_ext S _ _ (fun I ↦ ?_)
    ext _
    simpa using hab I
  simpa using ConcreteCategory.congr_hom h₁ PUnit.unit

/-- A presheaf of rings whose underlying presheaf of types is a sheaf is itself a sheaf.

Unlike `Presheaf.isSheaf_iff_isSheaf_forget`, this needs no size condition relating the universe
of the rings to the universes of the site: the ring axioms are equations between sections, and a
sheaf is separated, so the amalgamation of a compatible family of ring homomorphisms is again a
ring homomorphism. -/
theorem isSheaf_ringCat_of_isSheaf_forget (P : Cᵒᵖ ⥤ RingCat.{w})
    (h : Presheaf.IsSheaf J (P ⋙ forget RingCat.{w})) : Presheaf.IsSheaf J P := by
  intro E X S hS y hy
  let cover : J.Cover X := ⟨S, hS⟩
  have hx : ∀ ⦃I₁ I₂ : cover.Arrow⦄ (r : I₁.Relation I₂),
      (↾(fun e ↦ (y I₁.f I₁.hf).hom e) : ToType E ⟶ (P ⋙ forget RingCat.{w}).obj (op I₁.Y)) ≫
          (P ⋙ forget RingCat.{w}).map r.g₁.op =
        ↾(fun e ↦ (y I₂.f I₂.hf).hom e) ≫ (P ⋙ forget RingCat.{w}).map r.g₂.op := by
    intro I₁ I₂ r
    ext e
    simpa using congrArg (fun φ ↦ RingCat.Hom.hom φ e) (hy r.g₁ r.g₂ I₁.hf I₂.hf r.w)
  let t := h.amalgamate cover (fun I ↦ ↾(fun e ↦ (y I.f I.hf).hom e)) hx
  have ht : ∀ (I : cover.Arrow) (e : ToType E),
      (P.map I.f.op).hom (t e) = (y I.f I.hf).hom e := fun I e ↦ by
    simpa using ConcreteCategory.congr_hom (h.amalgamate_map cover _ hx I) e
  have key₁ : ∀ (e : ToType E) (c : ToType (P.obj (op X))),
      (∀ I : cover.Arrow, (y I.f I.hf).hom e = (P.map I.f.op).hom c) → t e = c := by
    intro e c hc
    refine eq_of_isSheaf h cover (fun I ↦ ?_)
    show (P.map I.f.op).hom _ = (P.map I.f.op).hom _
    rw [ht I, hc I]
  have key₂ : ∀ (F : ToType E → ToType E → ToType E)
      (G : ∀ R : RingCat.{w}, ToType R → ToType R → ToType R),
      (∀ (R R' : RingCat.{w}) (φ : R ⟶ R') (a b), φ.hom (G R a b) = G R' (φ.hom a) (φ.hom b)) →
      (∀ a b : ToType E, G E a b = F a b) →
      ∀ a b, t (F a b) = G (P.obj (op X)) (t a) (t b) := by
    intro F G hG hGF a b
    refine key₁ _ _ (fun I ↦ ?_)
    calc (y I.f I.hf).hom (F a b)
        = (y I.f I.hf).hom (G E a b) := by rw [hGF]
      _ = G _ ((y I.f I.hf).hom a) ((y I.f I.hf).hom b) := hG _ _ _ _ _
      _ = G _ ((P.map I.f.op).hom (t a)) ((P.map I.f.op).hom (t b)) := by rw [ht I a, ht I b]
      _ = (P.map I.f.op).hom (G _ (t a) (t b)) := (hG _ _ _ _ _).symm
  refine ⟨RingCat.ofHom
    { toFun := fun e ↦ t e
      map_one' := key₁ 1 1 (fun I ↦ by simp)
      map_zero' := key₁ 0 0 (fun I ↦ by simp)
      map_mul' := key₂ (· * ·) (fun _ a b ↦ a * b) (fun _ _ φ a b ↦ by simp) (fun _ _ ↦ rfl)
      map_add' := key₂ (· + ·) (fun _ a b ↦ a + b) (fun _ _ φ a b ↦ by simp) (fun _ _ ↦ rfl) },
    ?_, ?_⟩
  · intro Y f hf
    exact RingCat.hom_ext (RingHom.ext fun e ↦ ht ⟨Y, f, hf⟩ e)
  · intro t' ht'
    refine RingCat.hom_ext (RingHom.ext fun e ↦ ?_)
    refine eq_of_isSheaf h cover (fun I ↦ ?_)
    show (P.map I.f.op).hom (t'.hom e) = (P.map I.f.op).hom (t e)
    rw [ht I]
    exact congrArg (fun φ ↦ RingCat.Hom.hom φ e) (ht' I.f I.hf)

end CategoryTheory.Presheaf

/-! ## Pointwise operations on sheaves of types -/

namespace CategoryTheory.Sheaf

open _root_.CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Operations

variable {A B E : Sheaf J (Type w)}

/-- A natural pointwise binary operation on sections gives a morphism out of the product of two
sheaves of types. -/
noncomputable def binaryOpHom
    (op : ∀ X : Cᵒᵖ, A.obj.obj X → B.obj.obj X → E.obj.obj X)
    (hop : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : A.obj.obj X) (b : B.obj.obj X),
      E.obj.map g (op X a b) = op Y (A.obj.map g a) (B.obj.map g b)) :
    A ⨯ B ⟶ E where
  hom :=
    { app := fun X ↦ ↾(fun p ↦ op X ((Limits.prod.fst : A ⨯ B ⟶ A).hom.app X p)
        ((Limits.prod.snd : A ⨯ B ⟶ B).hom.app X p))
      naturality := by
        intro X Y g
        ext p
        dsimp
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
        exact (hop g _ _).symm }

/-- On sections over `X`, `binaryOpHom op hop` sends the pair of `a` and `b` to `op X a b`. -/
@[simp]
lemma sectionsFunctor_map_binaryOpHom (op) (hop) (X : Cᵒᵖ)
    (a : (sectionsFunctor J X).obj A) (b : (sectionsFunctor J X).obj B) :
    (sectionsFunctor J X).map (binaryOpHom (A := A) (B := B) (E := E) op hop)
      (prodObjMk a b) = op X a b := by
  show op X ((sectionsFunctor J X).map Limits.prod.fst (prodObjMk a b))
    ((sectionsFunctor J X).map Limits.prod.snd (prodObjMk a b)) = _
  rw [map_fst_prodObjMk, map_snd_prodObjMk]

/-- A natural pointwise unary operation on sections gives a morphism of sheaves of types. -/
def unaryOpHom (op : ∀ X : Cᵒᵖ, A.obj.obj X → E.obj.obj X)
    (hop : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : A.obj.obj X),
      E.obj.map g (op X a) = op Y (A.obj.map g a)) :
    A ⟶ E where
  hom := { app := fun X ↦ ↾(op X), naturality := by intro X Y g; ext a; exact (hop g a).symm }

/-- On sections over `X`, `unaryOpHom op hop` sends `a` to `op X a`. -/
@[simp]
lemma sectionsFunctor_map_unaryOpHom (op) (hop) (X : Cᵒᵖ) (a : (sectionsFunctor J X).obj A) :
    (sectionsFunctor J X).map (unaryOpHom (A := A) (E := E) op hop) a = op X a := rfl

/-- A compatible family of distinguished sections gives a morphism from the terminal sheaf. -/
noncomputable def constHom (c : ∀ X : Cᵒᵖ, E.obj.obj X)
    (hc : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y), E.obj.map g (c X) = c Y) :
    ⊤_ (Sheaf J (Type w)) ⟶ E where
  hom := { app := fun X ↦ ↾(fun _ ↦ c X), naturality := by intro X Y g; ext a; exact (hc g).symm }

/-- On sections over `X`, `constHom c hc` takes the value `c X`. -/
@[simp]
lemma sectionsFunctor_map_constHom (c) (hc) (X : Cᵒᵖ)
    (p : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) :
    (sectionsFunctor J X).map (constHom (E := E) c hc) p = c X := rfl

end Operations

/-! ## The underlying sheaf of sets of a sheaf of rings -/

section RingOperations

variable [J.HasSheafCompose (forget RingCat.{w})] (R : Sheaf J RingCat.{w})

/-- The underlying sheaf of sets of a sheaf of rings. -/
noncomputable abbrev ringSheaf : Sheaf J (Type w) := (sheafCompose J (forget RingCat.{w})).obj R

/-- Addition on the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringAddHom : ringSheaf R ⨯ ringSheaf R ⟶ ringSheaf R :=
  binaryOpHom (fun X (a b : R.obj.obj X) ↦ a + b) (fun g a b ↦ (R.obj.map g).hom.map_add a b)

/-- Multiplication on the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringMulHom : ringSheaf R ⨯ ringSheaf R ⟶ ringSheaf R :=
  binaryOpHom (fun X (a b : R.obj.obj X) ↦ a * b) (fun g a b ↦ (R.obj.map g).hom.map_mul a b)

/-- Negation on the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringNegHom : ringSheaf R ⟶ ringSheaf R :=
  unaryOpHom (fun X (a : R.obj.obj X) ↦ -a) (fun g a ↦ (R.obj.map g).hom.map_neg a)

/-- The zero section of the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringZeroHom : ⊤_ (Sheaf J (Type w)) ⟶ ringSheaf R :=
  constHom (fun X ↦ (0 : R.obj.obj X)) (fun g ↦ (R.obj.map g).hom.map_zero)

/-- The unit section of the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringOneHom : ⊤_ (Sheaf J (Type w)) ⟶ ringSheaf R :=
  constHom (fun X ↦ (1 : R.obj.obj X)) (fun g ↦ (R.obj.map g).hom.map_one)

/-- Sections over `X` of the underlying sheaf of sets of a sheaf of rings form a ring: they are
the sections of the sheaf of rings itself. -/
noncomputable instance ringSectionsRing (X : Cᵒᵖ) :
    Ring ((sectionsFunctor J X).obj (ringSheaf R)) :=
  inferInstanceAs (Ring (ToType (R.obj.obj X)))

/-- On sections over `X`, `ringAddHom R` sends the pair of `a` and `b` to `a + b`. -/
@[simp]
lemma sectionsFunctor_map_ringAddHom (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (ringSheaf R)) :
    (sectionsFunctor J X).map (ringAddHom R)
        (prodObjMk (A := ringSheaf R) (B := ringSheaf R) a b) = a + b :=
  sectionsFunctor_map_binaryOpHom (A := ringSheaf R) (B := ringSheaf R) (E := ringSheaf R)
    _ _ X a b

/-- On sections over `X`, `ringMulHom R` sends the pair of `a` and `b` to `a * b`. -/
@[simp]
lemma sectionsFunctor_map_ringMulHom (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (ringSheaf R)) :
    (sectionsFunctor J X).map (ringMulHom R)
        (prodObjMk (A := ringSheaf R) (B := ringSheaf R) a b) = a * b :=
  sectionsFunctor_map_binaryOpHom (A := ringSheaf R) (B := ringSheaf R) (E := ringSheaf R)
    _ _ X a b

/-- On sections over `X`, `ringNegHom R` sends `a` to `-a`. -/
@[simp]
lemma sectionsFunctor_map_ringNegHom (X : Cᵒᵖ)
    (a : (sectionsFunctor J X).obj (ringSheaf R)) :
    (sectionsFunctor J X).map (ringNegHom R) a = -a := rfl

/-- On sections over `X`, `ringZeroHom R` takes the value `0`. -/
@[simp]
lemma sectionsFunctor_map_ringZeroHom (X : Cᵒᵖ)
    (p : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) :
    (sectionsFunctor J X).map (ringZeroHom R) p = (0 : (sectionsFunctor J X).obj (ringSheaf R)) :=
  rfl

/-- On sections over `X`, `ringOneHom R` takes the value `1`. -/
@[simp]
lemma sectionsFunctor_map_ringOneHom (X : Cᵒᵖ)
    (p : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) :
    (sectionsFunctor J X).map (ringOneHom R) p = (1 : (sectionsFunctor J X).obj (ringSheaf R)) :=
  rfl

variable {Z : Sheaf J (Type w)}

/-- Associativity of `ringAddHom R`, for morphisms from a sheaf of types `Z`. -/
lemma ringAddHom_assoc (a b c : Z ⟶ ringSheaf R) :
    Limits.prod.lift (Limits.prod.lift a b ≫ ringAddHom R) c ≫ ringAddHom R =
      Limits.prod.lift a (Limits.prod.lift b c ≫ ringAddHom R) ≫ ringAddHom R := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp [add_assoc]

/-- `ringZeroHom R` is a left identity for `ringAddHom R`. -/
lemma ringAddHom_zero_add (a : Z ⟶ ringSheaf R) :
    Limits.prod.lift (Limits.terminal.from Z ≫ ringZeroHom R) a ≫ ringAddHom R = a := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp

/-- Composing with `ringNegHom R` gives a left inverse for `ringAddHom R`. -/
lemma ringAddHom_neg_add_cancel (a : Z ⟶ ringSheaf R) :
    Limits.prod.lift (a ≫ ringNegHom R) a ≫ ringAddHom R =
      Limits.terminal.from Z ≫ ringZeroHom R := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp

/-- Associativity of `ringMulHom R`, for morphisms from a sheaf of types `Z`. -/
lemma ringMulHom_assoc (a b c : Z ⟶ ringSheaf R) :
    Limits.prod.lift (Limits.prod.lift a b ≫ ringMulHom R) c ≫ ringMulHom R =
      Limits.prod.lift a (Limits.prod.lift b c ≫ ringMulHom R) ≫ ringMulHom R := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp [mul_assoc]

/-- `ringOneHom R` is a left identity for `ringMulHom R`. -/
lemma ringMulHom_one_mul (a : Z ⟶ ringSheaf R) :
    Limits.prod.lift (Limits.terminal.from Z ≫ ringOneHom R) a ≫ ringMulHom R = a := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp

/-- `ringOneHom R` is a right identity for `ringMulHom R`. -/
lemma ringMulHom_mul_one (a : Z ⟶ ringSheaf R) :
    Limits.prod.lift a (Limits.terminal.from Z ≫ ringOneHom R) ≫ ringMulHom R = a := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp

/-- `ringMulHom R` distributes over `ringAddHom R` from the left. -/
lemma ringHom_left_distrib (a b c : Z ⟶ ringSheaf R) :
    Limits.prod.lift a (Limits.prod.lift b c ≫ ringAddHom R) ≫ ringMulHom R =
      Limits.prod.lift (Limits.prod.lift a b ≫ ringMulHom R)
        (Limits.prod.lift a c ≫ ringMulHom R) ≫ ringAddHom R := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp [mul_add]

/-- `ringMulHom R` distributes over `ringAddHom R` from the right. -/
lemma ringHom_right_distrib (a b c : Z ⟶ ringSheaf R) :
    Limits.prod.lift (Limits.prod.lift a b ≫ ringAddHom R) c ≫ ringMulHom R =
      Limits.prod.lift (Limits.prod.lift a c ≫ ringMulHom R)
        (Limits.prod.lift b c ≫ ringMulHom R) ≫ ringAddHom R := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp [add_mul]

end RingOperations

/-! ## Transporting the ring structure along a finite-product-preserving functor -/

section RingTransport

variable [J.HasSheafCompose (forget RingCat.{w})] (R : Sheaf J RingCat.{w})
  (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- Addition transported to the image of the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringAddObj (x y : P.obj (ringSheaf R)) : P.obj (ringSheaf R) :=
  P.map (ringAddHom R) (prodObjMk x y)

/-- Multiplication transported to the image of the underlying sheaf of sets of a sheaf of
rings. -/
noncomputable def ringMulObj (x y : P.obj (ringSheaf R)) : P.obj (ringSheaf R) :=
  P.map (ringMulHom R) (prodObjMk x y)

/-- Negation transported to the image of the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringNegObj (x : P.obj (ringSheaf R)) : P.obj (ringSheaf R) :=
  P.map (ringNegHom R) x

/-- The zero of the image of the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringZeroObj : P.obj (ringSheaf R) := P.map (ringZeroHom R) default

/-- The unit of the image of the underlying sheaf of sets of a sheaf of rings. -/
noncomputable def ringOneObj : P.obj (ringSheaf R) := P.map (ringOneHom R) default

/-- An identity between morphisms `Z ⟶ ringSheaf R`, natural in `Z`, evaluated in the image
under `P` at the triple `(x, (y, z))`. -/
private lemma map_triple_eq
    {m n : ∀ {Z : Sheaf J (Type w)}, (Z ⟶ ringSheaf R) → (Z ⟶ ringSheaf R) →
      (Z ⟶ ringSheaf R) → (Z ⟶ ringSheaf R)}
    (h : ∀ {Z : Sheaf J (Type w)} (a b c : Z ⟶ ringSheaf R), m a b c = n a b c)
    (x y z : P.obj (ringSheaf R)) :
    P.map (m Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst)
      (Limits.prod.snd ≫ Limits.prod.snd)) (prodObjMk (A := ringSheaf R) x (prodObjMk y z)) =
      P.map (n Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst)
      (Limits.prod.snd ≫ Limits.prod.snd)) (prodObjMk (A := ringSheaf R) x (prodObjMk y z)) := by
  rw [h]

/-- The transported addition `ringAddObj R P` is associative. -/
lemma ringAddObj_assoc (x y z : P.obj (ringSheaf R)) :
    ringAddObj R P (ringAddObj R P x y) z = ringAddObj R P x (ringAddObj R P y z) := by
  simpa [ringAddObj] using map_triple_eq R P (ringAddHom_assoc R) x y z

/-- `ringZeroObj R P` is a left identity for `ringAddObj R P`. -/
lemma ringAddObj_zero_add (x : P.obj (ringSheaf R)) :
    ringAddObj R P (ringZeroObj R P) x = x := by
  simpa [ringAddObj, ringZeroObj] using congrArg (fun m ↦ P.map m x)
    (ringAddHom_zero_add R (Z := ringSheaf R) (𝟙 _))

/-- `ringNegObj R P x` is a left inverse of `x` for `ringAddObj R P`. -/
lemma ringAddObj_neg_add_cancel (x : P.obj (ringSheaf R)) :
    ringAddObj R P (ringNegObj R P x) x = ringZeroObj R P := by
  simpa [ringAddObj, ringNegObj, ringZeroObj] using congrArg (fun m ↦ P.map m x)
    (ringAddHom_neg_add_cancel R (Z := ringSheaf R) (𝟙 _))

/-- The transported multiplication `ringMulObj R P` is associative. -/
lemma ringMulObj_assoc (x y z : P.obj (ringSheaf R)) :
    ringMulObj R P (ringMulObj R P x y) z = ringMulObj R P x (ringMulObj R P y z) := by
  simpa [ringMulObj] using map_triple_eq R P (ringMulHom_assoc R) x y z

/-- `ringOneObj R P` is a left identity for `ringMulObj R P`. -/
lemma ringMulObj_one_mul (x : P.obj (ringSheaf R)) :
    ringMulObj R P (ringOneObj R P) x = x := by
  simpa [ringMulObj, ringOneObj] using congrArg (fun m ↦ P.map m x)
    (ringMulHom_one_mul R (Z := ringSheaf R) (𝟙 _))

/-- `ringOneObj R P` is a right identity for `ringMulObj R P`. -/
lemma ringMulObj_mul_one (x : P.obj (ringSheaf R)) :
    ringMulObj R P x (ringOneObj R P) = x := by
  simpa [ringMulObj, ringOneObj] using congrArg (fun m ↦ P.map m x)
    (ringMulHom_mul_one R (Z := ringSheaf R) (𝟙 _))

/-- `ringMulObj R P` distributes over `ringAddObj R P` from the left. -/
lemma ringObj_left_distrib (x y z : P.obj (ringSheaf R)) :
    ringMulObj R P x (ringAddObj R P y z) =
      ringAddObj R P (ringMulObj R P x y) (ringMulObj R P x z) := by
  simpa [ringMulObj, ringAddObj] using map_triple_eq R P (ringHom_left_distrib R) x y z

/-- `ringMulObj R P` distributes over `ringAddObj R P` from the right. -/
lemma ringObj_right_distrib (x y z : P.obj (ringSheaf R)) :
    ringMulObj R P (ringAddObj R P x y) z =
      ringAddObj R P (ringMulObj R P x z) (ringMulObj R P y z) := by
  simpa [ringMulObj, ringAddObj] using map_triple_eq R P (ringHom_right_distrib R) x y z

/-- The image of the underlying sheaf of sets of a sheaf of rings under a functor to types
preserving finite products is a ring, with the transported operations. This is the algebraic
heart of the construction of inverse images of sheaves of modules. -/
@[instance_reducible]
noncomputable def ringObjRing : Ring (P.obj (ringSheaf R)) :=
  letI : Add (P.obj (ringSheaf R)) := ⟨ringAddObj R P⟩
  letI : Mul (P.obj (ringSheaf R)) := ⟨ringMulObj R P⟩
  letI : Neg (P.obj (ringSheaf R)) := ⟨ringNegObj R P⟩
  letI : Zero (P.obj (ringSheaf R)) := ⟨ringZeroObj R P⟩
  letI : One (P.obj (ringSheaf R)) := ⟨ringOneObj R P⟩
  Ring.ofMinimalAxioms (ringAddObj_assoc R P) (ringAddObj_zero_add R P)
    (ringAddObj_neg_add_cancel R P) (ringMulObj_assoc R P) (ringMulObj_one_mul R P)
    (ringMulObj_mul_one R P) (ringObj_left_distrib R P) (ringObj_right_distrib R P)

variable {P} {Q : Sheaf J (Type w) ⥤ Type t} [PreservesFiniteProducts Q] (θ : P ⟶ Q)

/-- A natural transformation `θ : P ⟶ Q` commutes with the transported additions. -/
lemma ringAddObj_naturality (x y : P.obj (ringSheaf R)) :
    θ.app (ringSheaf R) (ringAddObj R P x y) =
      ringAddObj R Q (θ.app _ x) (θ.app _ y) := by
  rw [ringAddObj, ringAddObj, natTrans_app_map_apply, prodObjMk_naturality]

/-- A natural transformation `θ : P ⟶ Q` commutes with the transported multiplications. -/
lemma ringMulObj_naturality (x y : P.obj (ringSheaf R)) :
    θ.app (ringSheaf R) (ringMulObj R P x y) =
      ringMulObj R Q (θ.app _ x) (θ.app _ y) := by
  rw [ringMulObj, ringMulObj, natTrans_app_map_apply, prodObjMk_naturality]

/-- A natural transformation `θ : P ⟶ Q` sends the transported zero to the transported zero. -/
lemma ringZeroObj_naturality :
    θ.app (ringSheaf R) (ringZeroObj R P) = ringZeroObj R Q := by
  exact natTrans_app_map_default θ _

/-- A natural transformation `θ : P ⟶ Q` sends the transported unit to the transported unit. -/
lemma ringOneObj_naturality :
    θ.app (ringSheaf R) (ringOneObj R P) = ringOneObj R Q := by
  exact natTrans_app_map_default θ _

/-- A natural transformation of finite-product-preserving functors to types induces a ring
homomorphism between the transported ring structures. -/
noncomputable def ringObjHom :
    letI := ringObjRing R P
    letI := ringObjRing R Q
    P.obj (ringSheaf R) →+* Q.obj (ringSheaf R) :=
  letI := ringObjRing R P
  letI := ringObjRing R Q
  { toFun := θ.app (ringSheaf R)
    map_one' := ringOneObj_naturality R θ
    map_mul' := ringMulObj_naturality R θ
    map_zero' := ringZeroObj_naturality R θ
    map_add' := ringAddObj_naturality R θ }

end RingTransport

end CategoryTheory.Sheaf
