module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Limits
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Power
public import StacksFrontier.CategoryTheory.Limits.BinaryProductDiagonal
public import StacksFrontier.CategoryTheory.Limits.NonemptyFiniteProducts
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoveringAndHomotopies.FibreProduct
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ConstantPowerMatching
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.RefinementConstruction

/-!
# Refining a hypercovering by a covering in one degree

Given a hypercovering `K` of an object `X` and a covering of its term in a fixed degree, we may
refine `K` by another hypercovering whose map in that degree factors through the given covering.

## Main definitions

There are no new definitions.

## Main results

* `exists_hypercovering_map_factoring_through_covering`: a covering of one term of a
  hypercovering can be incorporated into a refinement.

## Implementation notes

The category `FormalCoproduct (Over X)` models the category `SR(C, X)` of semi-representable
objects over `X`. A morphism of hypercoverings is represented by a natural transformation of the
underlying simplicial objects. The asserted factorization is recorded by an explicit morphism to
the source of the given covering and its commuting equation.

## References

* [Stacks Project, Tag 01GJ](https://stacks.math.columbia.edu/tag/01GJ)
-/

public section

universe w v u

open CategoryTheory CategoryTheory.Limits Simplicial SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

/- `SimplicialObject.power` is semireducible, so a degree `(V.power U).obj n` and the product
`∏ᶜ fun _ : U.obj n.unop => V.obj n` that it is are equal only at default transparency, and the
`eqToHom` of `SimplicialObject.power_obj` is not even type-correct at `implicit` transparency.
Making that one declaration implicitly reducible here resolves this; it is narrower than
file-scope `backward.isDefEq.respectTransparency` options, naming a single
declaration instead of relaxing every defeq check. -/
attribute [local implicit_reducible] CategoryTheory.SimplicialObject.power

/- `FormalCoproduct.instHasProductsOfShape` builds a product of a nonempty finite family out of
binary products; it is used here as the theorem it comes from, never by instance search. As an
instance it is a second route to every `HasProduct` goal in this file, and the search it adds —
`Inhabited` of an index type that may well be empty, over `HasBinaryProducts (Over X)` — exhausts
the elaboration budget of the two matching lemmas below. -/
attribute [-instance] CategoryTheory.Limits.FormalCoproduct.instHasProductsOfShape

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

private theorem isCoveringOver_of_isIso (J : Pretopology C)
    {X : C} {A B : FormalCoproduct.{w} (Over X)} (f : A ⟶ B) [IsIso f] :
    IsCoveringOver J f := by
  intro j
  classical
  let g := inv f
  have hfg (i : A.I) : g.f (f.f i) = i :=
    congrArg (fun q : A ⟶ A => q.f i) (IsIso.hom_inv_id f)
  have hgf (k : B.I) : f.f (g.f k) = k :=
    congrArg (fun q : B ⟶ B => q.f k) (IsIso.inv_hom_id f)
  let : Unique {i : A.I // f.f i = j} :=
    { default := ⟨g.f j, hgf j⟩
      uniq := by
        rintro ⟨i, hi⟩
        exact Subtype.ext ((hfg i).symm.trans (congrArg g.f hi)) }
  have hφ (i : A.I) : IsIso (f.φ i) := by
    let k : B.obj (f.f i) ⟶ A.obj i :=
      g.φ (f.f i) ≫ eqToHom (congrArg A.obj (hfg i))
    refine ⟨⟨k, ?_, ?_⟩⟩
    · have e := ((FormalCoproduct.hom_ext_iff' (f ≫ g) (𝟙 A)).mp
        (IsIso.hom_inv_id f)) i
      rcases e with ⟨_, e₂⟩
      simpa [k, g] using e₂
    · have e := ((FormalCoproduct.hom_ext_iff' (g ≫ f) (𝟙 B)).mp
        (IsIso.inv_hom_id f)) (f.f i)
      rcases e with ⟨_, e₂⟩
      simpa [k, g, hfg i, Category.assoc] using e₂
  rw [Presieve.ofArrows_of_unique]
  have : IsIso (f.φ (g.f j)).left := (Over.forget X).map_isIso _
  apply J.has_isos

/-- Precomposing with an isomorphism does not change whether a morphism is covering: the two
directions are `IsCoveringOver.isIso_comp` and `IsCoveringOver.of_isIso_comp`. -/
private theorem isCoveringOver_iso_comp_iff (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {X : C} {A B D : FormalCoproduct.{w} (Over X)} (e : A ≅ B) (f : B ⟶ D) :
    IsCoveringOver J (e.hom ≫ f) ↔ IsCoveringOver J f :=
  ⟨fun h => IsCoveringOver.of_isIso_comp J e.hom h,
    fun h => IsCoveringOver.isIso_comp J e.hom h⟩

universe w'

private noncomputable def piReindexIso {D : Type u} [Category.{v} D]
    {α : Type w} {β : Type w'} (e : β ≃ α) (F : α → D)
    [HasProduct F] [HasProduct (fun b : β => F (e b))] :
    (∏ᶜ F) ≅ ∏ᶜ fun b : β => F (e b) where
  hom := Pi.lift fun b => Pi.π F (e b)
  inv := Pi.lift fun a =>
    Pi.π (fun b : β => F (e b)) (e.symm a) ≫
      eqToHom (congrArg F (e.apply_symm_apply a))
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    simp [Category.assoc]
  inv_hom_id := by
    apply Pi.hom_ext
    intro b
    simp [Category.assoc]

private noncomputable def piIsoOfComponents {D : Type u} [Category.{v} D]
    {α : Type w} (F G : α → D) [HasProduct F] [HasProduct G]
    (e : ∀ a, F a ≅ G a) : (∏ᶜ F) ≅ ∏ᶜ G where
  hom := Pi.map' (fun a => a) (fun a => (e a).hom)
  inv := Pi.map' (fun a => a) (fun a => (e a).inv)
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    simp [Category.assoc]
  inv_hom_id := by
    apply Pi.hom_ext
    intro a
    simp [Category.assoc]

private noncomputable def piSumIso {D : Type u} [Category.{v} D]
    {α β : Type w} (H : α ⊕ β → D)
    [HasProduct H]
    [HasProduct (fun a : α => H (Sum.inl a))]
    [HasProduct (fun b : β => H (Sum.inr b))]
    [HasBinaryProduct (∏ᶜ fun a : α => H (Sum.inl a))
      (∏ᶜ fun b : β => H (Sum.inr b))] :
    (∏ᶜ H) ≅
      (∏ᶜ fun a : α => H (Sum.inl a)) ⨯
        (∏ᶜ fun b : β => H (Sum.inr b)) where
  hom := prod.lift
    (Pi.lift fun a => Pi.π H (Sum.inl a))
    (Pi.lift fun b => Pi.π H (Sum.inr b))
  inv := Pi.lift fun s => match s with
    | Sum.inl a => prod.fst ≫ Pi.π (fun a : α => H (Sum.inl a)) a
    | Sum.inr b => prod.snd ≫ Pi.π (fun b : β => H (Sum.inr b)) b
  hom_inv_id := by
    apply Pi.hom_ext
    intro s
    cases s
    · rw [Category.assoc, Pi.lift_π, ← Category.assoc, prod.lift_fst,
        Pi.lift_π]
      simp
    · rw [Category.assoc, Pi.lift_π, ← Category.assoc, prod.lift_snd,
        Pi.lift_π]
      simp
  inv_hom_id := by
    apply prod.hom_ext
    · apply Pi.hom_ext
      intro a
      let p := Pi.lift fun a => Pi.π H (Sum.inl a)
      let q := Pi.lift fun b => Pi.π H (Sum.inr b)
      let r := Pi.lift fun s => match s with
        | Sum.inl a => prod.fst ≫ Pi.π (fun a : α => H (Sum.inl a)) a
        | Sum.inr b => prod.snd ≫ Pi.π (fun b : β => H (Sum.inr b)) b
      have hcomp : r ≫ prod.lift p q =
          prod.lift (r ≫ p) (r ≫ q) := prod.comp_lift r p q
      change ((r ≫ prod.lift p q) ≫ prod.fst) ≫
        Pi.π (fun a : α => H (Sum.inl a)) a =
          (𝟙 _ ≫ prod.fst) ≫ Pi.π (fun a : α => H (Sum.inl a)) a
      rw [hcomp, prod.lift_fst, Category.assoc, Pi.lift_π]
      simp [r]
    · apply Pi.hom_ext
      intro b
      let p := Pi.lift fun a => Pi.π H (Sum.inl a)
      let q := Pi.lift fun b => Pi.π H (Sum.inr b)
      let r := Pi.lift fun s => match s with
        | Sum.inl a => prod.fst ≫ Pi.π (fun a : α => H (Sum.inl a)) a
        | Sum.inr b => prod.snd ≫ Pi.π (fun b : β => H (Sum.inr b)) b
      have hcomp : r ≫ prod.lift p q =
          prod.lift (r ≫ p) (r ≫ q) := prod.comp_lift r p q
      change ((r ≫ prod.lift p q) ≫ prod.snd) ≫
        Pi.π (fun b : β => H (Sum.inr b)) b =
          (𝟙 _ ≫ prod.snd) ≫ Pi.π (fun b : β => H (Sum.inr b)) b
      rw [hcomp, prod.lift_snd, Category.assoc, Pi.lift_π]
      simp [r]

private noncomputable def piSplitIso {D : Type u} [Category.{v} D]
    {α β γ : Type w} (e : β ⊕ γ ≃ α) (F : α → D)
    [HasProduct F] [HasProduct (fun b : β => F (e (Sum.inl b)))]
    [HasProduct (fun c : γ => F (e (Sum.inr c)))]
    [HasProduct (fun s : β ⊕ γ => F (e s))]
    [HasBinaryProduct (∏ᶜ fun b : β => F (e (Sum.inl b)))
      (∏ᶜ fun c : γ => F (e (Sum.inr c)))] :
    (∏ᶜ F) ≅
      (∏ᶜ fun b : β => F (e (Sum.inl b))) ⨯
        (∏ᶜ fun c : γ => F (e (Sum.inr c))) :=
  (piReindexIso e F).trans
    (piSumIso (fun s => F (e s)))

private theorem piSplitIso_fst_π {D : Type u} [Category.{v} D]
    {α β γ : Type w} (e : β ⊕ γ ≃ α) (F : α → D)
    [HasProduct F] [HasProduct (fun b : β => F (e (Sum.inl b)))]
    [HasProduct (fun c : γ => F (e (Sum.inr c)))]
    [HasProduct (fun s : β ⊕ γ => F (e s))]
    [HasBinaryProduct (∏ᶜ fun b : β => F (e (Sum.inl b)))
      (∏ᶜ fun c : γ => F (e (Sum.inr c)))] (b : β) :
    (piSplitIso e F).hom ≫ prod.fst ≫
        Pi.π (fun b : β => F (e (Sum.inl b))) b =
      Pi.π F (e (Sum.inl b)) := by
  simp [piSplitIso, piReindexIso, piSumIso, Category.assoc]

private theorem piSplitIso_snd_π {D : Type u} [Category.{v} D]
    {α β γ : Type w} (e : β ⊕ γ ≃ α) (F : α → D)
    [HasProduct F] [HasProduct (fun b : β => F (e (Sum.inl b)))]
    [HasProduct (fun c : γ => F (e (Sum.inr c)))]
    [HasProduct (fun s : β ⊕ γ => F (e s))]
    [HasBinaryProduct (∏ᶜ fun b : β => F (e (Sum.inl b)))
      (∏ᶜ fun c : γ => F (e (Sum.inr c)))] (c : γ) :
    (piSplitIso e F).hom ≫ prod.snd ≫
        Pi.π (fun c : γ => F (e (Sum.inr c))) c =
      Pi.π F (e (Sum.inr c)) := by
  simp [piSplitIso, piReindexIso, piSumIso, Category.assoc]

private theorem simplexTrunc0ObjEq (x : SimplexCategory.Truncated 0) :
    x = ⟨SimplexCategory.mk 0, by simp⟩ := by
  apply ObjectProperty.FullSubcategory.ext
  rcases x with ⟨⟨n⟩, hn⟩
  have h : n = 0 := by simp only at hn; omega
  subst n
  rfl

private theorem simplexTrunc0HomSubsingleton (x y : SimplexCategory.Truncated 0) :
    Subsingleton (x ⟶ y) := by
  obtain rfl := simplexTrunc0ObjEq x
  obtain rfl := simplexTrunc0ObjEq y
  refine ⟨fun f g => ?_⟩
  apply SimplexCategory.Truncated.Hom.ext
  ext i; fin_cases i; simp

private theorem simplexTrunc0OpObjEq (x : (SimplexCategory.Truncated 0)ᵒᵖ) :
    x = Opposite.op (⟨SimplexCategory.mk 0, by simp⟩ : SimplexCategory.Truncated 0) :=
  Opposite.unop_injective (simplexTrunc0ObjEq x.unop)

@[instance_reducible]
private noncomputable def uniqueUliftCoyonedaTrunc0 (k : ℕ)
    (x : (SimplexCategory.Truncated 0)ᵒᵖ) :
    Unique (((uliftCoyoneda.{w}).obj (Opposite.op (SimplexCategory.mk k))).obj
      ((SimplexCategory.Truncated.inclusion 0).op.obj x).unop) := by
  cases simplexTrunc0OpObjEq x
  change Unique (ULift (SimplexCategory.mk k ⟶ SimplexCategory.mk 0))
  infer_instance

private theorem power_obj_π_transport {D : Type u} [Category.{v} D]
    (V : SimplicialObject D) (U : CosimplicialObject (Type w))
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : U.obj n.unop => V.obj n]
    (n : SimplexCategoryᵒᵖ) (i : U.obj n.unop) :
    Pi.π (fun _ : U.obj n.unop => V.obj n) i =
      eqToHom (SimplicialObject.power_obj V U n) ≫
        Pi.π (fun _ : U.obj n.unop => V.obj n) i := by
  cases SimplicialObject.power_obj V U n
  simp

private theorem power_map_productUniqueIso {D : Type u} [Category.{v} D]
    (V : SimplicialObject D) (U : CosimplicialObject (Type w))
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : U.obj n.unop => V.obj n]
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) [Unique (U.obj m.unop)] :
    (V.power U).map φ ≫
        (CategoryTheory.Limits.productUniqueIso
          (fun _ : U.obj m.unop => V.obj m)).hom =
      eqToHom (SimplicialObject.power_obj V U n) ≫
        Pi.π (fun _ : U.obj n.unop => V.obj n)
          (U.map φ.unop default) ≫ V.map φ := by
  rw [CategoryTheory.Limits.productUniqueIso_hom]
  calc
    _ = Pi.π (fun _ : U.obj n.unop => V.obj n)
          (U.map φ.unop default) ≫ V.map φ :=
      CategoryTheory.SimplicialObject.power_map_π V U φ default
    _ = (eqToHom (SimplicialObject.power_obj V U n) ≫
          Pi.π (fun _ : U.obj n.unop => V.obj n)
            (U.map φ.unop default)) ≫ V.map φ :=
      congrArg (fun q => q ≫ V.map φ)
        (power_obj_π_transport V U n (U.map φ.unop default))
    _ = eqToHom (SimplicialObject.power_obj V U n) ≫
          (Pi.π (fun _ : U.obj n.unop => V.obj n)
            (U.map φ.unop default) ≫ V.map φ) := Category.assoc _ _ _

private theorem simplexTrunc0OpHomSubsingleton
    (x y : (SimplexCategory.Truncated 0)ᵒᵖ) : Subsingleton (x ⟶ y) := by
  constructor
  intro f g
  apply Opposite.unop_injective
  have := simplexTrunc0HomSubsingleton y.unop x.unop
  exact Subsingleton.elim f.unop g.unop

private theorem isDiscrete_verticesOverOne :
    IsDiscrete (StructuredArrow (Opposite.op (SimplexCategory.mk 1))
      (SimplexCategory.Truncated.inclusion 0).op) where
  subsingleton X Y := ⟨fun f g => by
    have := simplexTrunc0OpHomSubsingleton X.right Y.right
    exact StructuredArrow.ext _ _ (Subsingleton.elim _ _)⟩
  eq_of_hom := by
    intro X Y f
    apply StructuredArrow.obj_ext X Y
      (simplexTrunc0OpObjEq X.right |>.trans (simplexTrunc0OpObjEq Y.right).symm)
    have := simplexTrunc0OpHomSubsingleton X.right Y.right
    have hf : StructuredArrow.Hom.right f =
        eqToHom (simplexTrunc0OpObjEq X.right |>.trans (simplexTrunc0OpObjEq Y.right).symm) :=
      Subsingleton.elim _ _
    simpa [hf] using (StructuredArrow.w f)

universe a b c d

private noncomputable def discreteLimitCone {J : Type a} [Category.{b} J]
    {D : Type c} [Category.{d} D] (F : J ⥤ D) [HasProduct F.obj] [IsDiscrete J] : Cone F where
  pt := ∏ᶜ F.obj
  π := {
    app := fun j => Pi.π F.obj j
    naturality := by
      intro j j' f
      have hj : j = j' := IsDiscrete.eq_of_hom f
      subst j'
      have hf : f = 𝟙 j := Subsingleton.elim _ _
      subst f
      simp
  }

private noncomputable def isLimit_discreteLimitCone {J : Type a} [Category.{b} J]
    {D : Type c} [Category.{d} D] (F : J ⥤ D) [HasProduct F.obj] [IsDiscrete J] :
    IsLimit (discreteLimitCone F) := by
  refine {
    lift := fun s => Pi.lift fun j => s.π.app j
    fac := ?_
    uniq := ?_
  }
  · intro s j
    simp [discreteLimitCone]
  · intro s m hm
    apply Pi.hom_ext
    intro j
    simpa [discreteLimitCone] using hm j

private noncomputable def pullbackProdFstIso {D : Type u} [Category.{v} D]
    {A B T : D} (f : T ⟶ A) [HasBinaryProducts D] [HasPullback (prod.fst : A ⨯ B ⟶ A) f] :
    pullback (prod.fst : A ⨯ B ⟶ A) f ≅ T ⨯ B where
  hom := prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ prod.snd)
  inv := pullback.lift (prod.lift (prod.fst ≫ f) prod.snd) prod.fst (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext
      · simpa [Category.assoc, pullback.lift_fst, prod.lift_fst] using
          (pullback.condition (f := (prod.fst : A ⨯ B ⟶ A)) (g := f)).symm
      · simp [Category.assoc, pullback.lift_fst]
    · calc
        _ = (prod.lift (pullback.snd (prod.fst : A ⨯ B ⟶ A) f)
              (pullback.fst _ _ ≫ prod.snd)) ≫
              (pullback.lift (prod.lift (prod.fst ≫ f) prod.snd) prod.fst (by simp) ≫
                pullback.snd (prod.fst : A ⨯ B ⟶ A) f) := by
                simp [Category.assoc]
        _ = _ := by simp [pullback.lift_snd]
  inv_hom_id := by
    apply prod.hom_ext
    · simp [pullback.lift_snd]
    · calc
        _ = pullback.lift (prod.lift (prod.fst ≫ f) prod.snd) prod.fst (by simp) ≫
              pullback.fst (prod.fst : A ⨯ B ⟶ A) f ≫ prod.snd := by
                simp only [Category.assoc, prod.lift_snd]
        _ = prod.snd := by
              rw [← Category.assoc, pullback.lift_fst, prod.lift_snd]
        _ = 𝟙 (T ⨯ B) ≫ prod.snd := by simp

private noncomputable def finSumEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun
    | Sum.inl _ => 0
    | Sum.inr i => i.succ
  invFun i := Fin.cases (Sum.inl ()) (fun j => Sum.inr j) i
  left_inv := by
    rintro (u | i) <;> simp
  right_inv := by
    intro i
    exact Fin.cases rfl (fun j => rfl) i

universe w₂ u₁ v₁

/-! ### Degreewise products of a morphism property

Everything between here and the matching hypothesis of Tag 01GH for `Hom(C[k], u)` uses the
covering morphisms of `SR(C, X)` only through three closure properties: they contain the
isomorphisms, they are stable under composition, and they are stable under base change. The
products of families of morphisms are therefore treated here for an arbitrary
`CategoryTheory.MorphismProperty` with those closures, on a category with binary products, and
specialised to the covering morphisms through `coveringOverProperty` below. No empty product —
and so no terminal object — is needed except where the index type is itself empty, where the
product map is an isomorphism.
-/

/-- An isomorphism has any morphism property that contains the identities and is stable under
base change. -/
private theorem prop_of_isIso {E : Type u₁} [Category.{v₁} E] (P : MorphismProperty E)
    [P.ContainsIdentities] [P.IsStableUnderBaseChange] {A B : E} (f : A ⟶ B) [IsIso f] : P f :=
  P.of_isIso f

/-- A morphism that is conjugate by isomorphisms to one with property `P` has property `P`. -/
private theorem prop_of_comp_eq {E : Type u₁} [Category.{v₁} E] (P : MorphismProperty E)
    [P.RespectsIso] {A B A' B' : E} (f : A ⟶ B) (g : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B')
    (h : f ≫ eB.hom = eA.hom ≫ g) (hg : P g) : P f := by
  have hpost : P (f ≫ eB.hom) := by
    rw [h]
    exact (P.cancel_left_of_respectsIso eA.hom g).2 hg
  exact (P.cancel_right_of_respectsIso f eB.hom).1 hpost

/-- The degreewise product of covering morphisms over an index type with exactly one element is
covering: read through `Limits.productUniqueIso` it is the single morphism of the family. -/
private theorem prop_piMap_unique {E : Type u₁} [Category.{v₁} E] (P : MorphismProperty E)
    [P.IsStableUnderBaseChange]
    {ι : Type w₂} [Unique ι] (A B : ι → E)
    [HasProduct A] [HasProduct B] (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, P (f i)) :
    P (CategoryTheory.Limits.Pi.map f) := by
  refine prop_of_comp_eq P _ _ (CategoryTheory.Limits.productUniqueIso A)
    (CategoryTheory.Limits.productUniqueIso B) ?_ (hf default)
  simp [CategoryTheory.Limits.productUniqueIso_hom]

/-- The degreewise product of a family of covering morphisms is covering as soon as the two
partial products cut out by a splitting of the index type are. This is the inductive step of
`prop_piMap_fin`, stated for an arbitrary splitting rather than for the first index
and the rest. -/
private theorem prop_piMap_split {E : Type u₁} [Category.{v₁} E] [HasBinaryProducts E]
    (P : MorphismProperty E) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    {α β γ : Type w₂} (e : β ⊕ γ ≃ α) (A B : α → E)
    [HasProduct A] [HasProduct B]
    [HasProduct fun b : β => A (e (Sum.inl b))]
    [HasProduct fun b : β => B (e (Sum.inl b))]
    [HasProduct fun c : γ => A (e (Sum.inr c))]
    [HasProduct fun c : γ => B (e (Sum.inr c))]
    [HasProduct fun s : β ⊕ γ => A (e s)]
    [HasProduct fun s : β ⊕ γ => B (e s)]
    (f : ∀ i, A i ⟶ B i)
    (hhead : P
      (CategoryTheory.Limits.Pi.map fun b : β => f (e (Sum.inl b))))
    (htail : P
      (CategoryTheory.Limits.Pi.map fun c : γ => f (e (Sum.inr c)))) :
    P (CategoryTheory.Limits.Pi.map f) := by
  let eA := piSplitIso e A
  let eB := piSplitIso e B
  have hsplit : CategoryTheory.Limits.Pi.map f ≫ eB.hom =
      eA.hom ≫ prod.map
        (CategoryTheory.Limits.Pi.map fun b : β => f (e (Sum.inl b)))
        (CategoryTheory.Limits.Pi.map fun c : γ => f (e (Sum.inr c))) := by
    apply prod.hom_ext
    · apply Pi.hom_ext
      intro b
      simp [eA, eB, reassoc_of% (piSplitIso_fst_π e A b), piSplitIso_fst_π e B b]
    · apply Pi.hom_ext
      intro c
      simp [eA, eB, reassoc_of% (piSplitIso_snd_π e A c), piSplitIso_snd_π e B c]
  exact prop_of_comp_eq P _ _ eA eB hsplit
    (CategoryTheory.MorphismProperty.prod_map P _ _ hhead htail)

/-- The degreewise product of a family of covering morphisms indexed by `Fin (n + 1)` is
covering. The induction is based at the one-element index `Fin 1`, so no empty product — and
hence no terminal object — is used: the products it needs are those of nonempty finite families,
which `Limits.hasProductsOfShape_of_finite_of_elem` provides from binary products alone. -/
private theorem prop_piMap_fin {E : Type u₁} [Category.{v₁} E] [HasBinaryProducts E]
    (P : MorphismProperty E) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    (n : ℕ) (A B : Fin (n + 1) → E)
    [HasProduct A] [HasProduct B]
    (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, P (f i)) :
    P (CategoryTheory.Limits.Pi.map f) := by
  induction n with
  | zero =>
      have : Unique (Fin (0 + 1)) := Fin.instUnique
      exact prop_piMap_unique P A B f hf
  | succ n ih =>
      have : HasProductsOfShape Unit E :=
        CategoryTheory.Limits.hasProductsOfShape_of_finite_of_elem _ _ ()
      have : HasProductsOfShape (Fin (n + 1)) E :=
        CategoryTheory.Limits.hasProductsOfShape_of_finite_of_elem _ _ (0 : Fin (n + 1))
      have : HasProductsOfShape (Unit ⊕ Fin (n + 1)) E :=
        CategoryTheory.Limits.hasProductsOfShape_of_finite_of_elem _ _
          (Sum.inl () : Unit ⊕ Fin (n + 1))
      refine prop_piMap_split P (finSumEquiv (n + 1)) A B f ?_ ?_
      · exact prop_piMap_unique P
          (fun b : Unit => A (finSumEquiv (n + 1) (Sum.inl b)))
          (fun b : Unit => B (finSumEquiv (n + 1) (Sum.inl b)))
          (fun b => f (finSumEquiv (n + 1) (Sum.inl b)))
          (fun b => hf (finSumEquiv (n + 1) (Sum.inl b)))
      · exact ih (fun i => A (finSumEquiv (n + 1) (Sum.inr i)))
          (fun i => B (finSumEquiv (n + 1) (Sum.inr i)))
          (fun i => f (finSumEquiv (n + 1) (Sum.inr i)))
          (fun i => hf (finSumEquiv (n + 1) (Sum.inr i)))

private theorem prop_piMap {E : Type u₁} [Category.{v₁} E] [HasBinaryProducts E]
    (P : MorphismProperty E) [P.ContainsIdentities] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange]
    {α : Type w₂} [Finite α]
    (A B : α → E) (f : ∀ a, A a ⟶ B a)
    [HasProduct A] [HasProduct B]
    (hf : ∀ a, P (f a)) :
    P (CategoryTheory.Limits.Pi.map f) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · let g : (∏ᶜ B) ⟶ ∏ᶜ A := Pi.lift fun a => hα.elim a
    let : IsIso (CategoryTheory.Limits.Pi.map f) :=
      ⟨⟨g, Pi.hom_ext _ _ fun a => hα.elim a, Pi.hom_ext _ _ fun a => hα.elim a⟩⟩
    exact prop_of_isIso P (CategoryTheory.Limits.Pi.map f)
  · obtain ⟨p, ⟨e0⟩⟩ := Finite.exists_equiv_fin α
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero fun hp => (hp ▸ e0 hα.some).elim0
    let e : Fin (m + 1) ≃ α := e0.symm
    have : HasProductsOfShape (Fin (m + 1)) E :=
      CategoryTheory.Limits.hasProductsOfShape_of_finite_of_elem _ _ (0 : Fin (m + 1))
    let eA := piReindexIso e A
    let eB := piReindexIso e B
    have hfin : P
        (CategoryTheory.Limits.Pi.map fun i : Fin (m + 1) => f (e i)) :=
      prop_piMap_fin P m (fun i => A (e i))
        (fun i => B (e i)) (fun i => f (e i)) (fun i => hf (e i))
    have hcomp : CategoryTheory.Limits.Pi.map f ≫ eB.hom =
        eA.hom ≫ CategoryTheory.Limits.Pi.map (fun i : Fin (m + 1) => f (e i)) := by
      apply Pi.hom_ext
      intro i
      simp [eA, eB, piReindexIso, CategoryTheory.Limits.Pi.map_π, Category.assoc]
    exact prop_of_comp_eq P _ _ eA eB hcomp hfin

/-- The covering morphisms of `SR(C, X)` read as a `CategoryTheory.MorphismProperty`, so that the
permanence package of Tag 01G4 can be used through that interface. -/
def coveringOverProperty (J : Pretopology C) (X : C) :
    MorphismProperty (FormalCoproduct.{w} (Over X)) := fun _ _ f => IsCoveringOver J f

/-- `coveringOverProperty` holds of exactly the covering morphisms, by definition. -/
theorem coveringOverProperty_iff (J : Pretopology C) {X : C}
    {A B : FormalCoproduct.{w} (Over X)} (f : A ⟶ B) :
    coveringOverProperty J X f ↔ IsCoveringOver J f := Iff.rfl

/-- The identities are covering. -/
instance (J : Pretopology C) (X : C) : (coveringOverProperty J X : MorphismProperty
    (FormalCoproduct.{w} (Over X))).ContainsIdentities where
  id_mem A := IsCoveringOver.of_isIso J (𝟙 A)

/-- **Stacks Project, Tag 01G4, part (1)** read through `MorphismProperty`: the covering
morphisms are stable under composition. -/
instance (J : Pretopology C) [Precoverage.IsStableUnderComposition J.toPrecoverage] (X : C) :
    (coveringOverProperty J X : MorphismProperty
      (FormalCoproduct.{w} (Over X))).IsStableUnderComposition where
  comp_mem _ _ hf hg := IsCoveringOver.comp J hf hg

end Stacks.CategoryTheory.Hypercovering
