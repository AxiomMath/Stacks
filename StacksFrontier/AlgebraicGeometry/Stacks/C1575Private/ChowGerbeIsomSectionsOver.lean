module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeIsomTotalPresheafSections

/-!
# Sections of a total presheaf over a morphism of presheaves

Let `Z` be a presheaf of sets on the big fppf site of `S`, `F` a presheaf on its category of
elements `El Z`, and `Σ_Z F ⟶ Z` the total presheaf
(`CategoryTheory.PresheafOfCategories.elementsTotalPresheaf`). For a morphism `q : T ⟶ Z`, a
lift `σ : T ⟶ Σ_Z F` of `q` is the same thing as a global section of the pullback `q^*F` of `F`
to `El T` along the functor `El T ⥤ El Z` of `q` (Stacks 0458,
`AlgebraicGeometry.Stack.associatedMap`). For `q = 𝟙` this is
`CategoryTheory.PresheafOfCategories.elementsTotalSectionEquiv`.

The proof of [Stacks, Tag 0CQ7] uses this for the isomorphism spaces
`I_{ij} = Isom(x_i, x_j) ⟶ W_i ∩ W_j` (`AlgebraicGeometry.Stack.relativeIsomorphismTotalPresheaf`):
the isomorphisms `φ_{ij} : x_i|_V ⟶ x_j|_V` are sections of `I_{ij}` over `V ⊆ W_i ∩ W_j`, which
Stacks 0CPI extends to the inverse image `b⁻¹(W_i ∩ W_j)` in a `V`-admissible blowup `b`, and such
an extension is an isomorphism between the pullbacks of `x_i` and `x_j` along `b`.

## Main results

* `AlgebraicGeometry.Stack.ChowGerbeIsomOver.sectionOverEquiv`: lifts of `q` along
  `Σ_Z F ⟶ Z` are global sections of `q^*F`.
* `AlgebraicGeometry.Stack.ChowGerbeIsomOver.relativeIsomorphismSectionOverEquiv`: lifts of `q`
  along `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` are natural families of vertical morphisms
  `x₁(q t) ⟶ x₂(q t)` over the components of `α`.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack.ChowGerbeIsomOver

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {T Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : T ⟶ Z)
  (F : ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type u)

/-- The pullback `q^*F` of a presheaf on `El Z` to `El T` along the functor of `q : T ⟶ Z`: its
value at `(V, t)` is `F(V, q t)`. -/
abbrev elementsPullback : ((presheafOfCategories (T ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type u :=
  (associatedMap B S hS q).1.hom.toFunctor.op ⋙ F

/-- **The lift of `q` along `Σ_Z F ⟶ Z` of a global section of `q^*F`**: it sends `t ∈ T(V)` to
the pair `(q t, s(V, t))`. -/
def sectionOverOf (t : ElementsGlobalSection T (elementsPullback q F)) :
    T ⟶ elementsTotalPresheaf Z F where
  app V := ↾fun z => ⟨q.app V z, t.1 (elementsPoint T (V := V.unop) z)⟩
  naturality V W f := by
    ext z
    change (⟨q.app W (T.map f z), t.1 (elementsPoint T (T.map f z))⟩ :
        Σ y : Z.obj W, F.obj (op (elementsPoint Z y))) =
      ⟨Z.map f (q.app V z), F.map (elementsRestrict Z f (q.app V z)).op
        (t.1 (elementsPoint T (V := V.unop) z))⟩
    rw [← t.2 (elementsRestrict T f z)]
    exact totalMk_eq Z F _ _ _ rfl

/-- The lift `sectionOverOf q F t` sends `z ∈ T(V)` to the pair `(q z, t(V, z))`. -/
@[simp]
lemma sectionOverOf_app (t : ElementsGlobalSection T (elementsPullback q F))
    (V : (BigFppfOver B S hS)ᵒᵖ) (z : T.obj V) :
    (sectionOverOf q F t).app V z = ⟨q.app V z, t.1 (elementsPoint T (V := V.unop) z)⟩ :=
  rfl

/-- The morphism `sectionOverOf q F t` is a lift of `q` along `Σ_Z F ⟶ Z`. -/
lemma sectionOverOf_comp_elementsTotalProj (t : ElementsGlobalSection T (elementsPullback q F)) :
    sectionOverOf q F t ≫ elementsTotalProj Z F = q :=
  rfl

variable {q F}

/-- A lift of `q` along `Σ_Z F ⟶ Z` sends `t` to a pair with first component `q t`. -/
lemma app_fst_of_comp_eq {σ : T ⟶ elementsTotalPresheaf Z F}
    (hσ : σ ≫ elementsTotalProj Z F = q) {V : (BigFppfOver B S hS)ᵒᵖ} (z : T.obj V) :
    (σ.app V z).1 = q.app V z :=
  types_congr_hom (NatTrans.congr_app hσ V) z

/-- **The value of a lift of `q` at `t ∈ T(V)`**: the second component of the pair it sends `t`
to, an element of `F(V, q t)`. -/
def valueOver {σ : T ⟶ elementsTotalPresheaf Z F} (hσ : σ ≫ elementsTotalProj Z F = q)
    {V : BigFppfOver B S hS} (z : T.obj (op V)) : F.obj (op (elementsPoint Z (q.app (op V) z))) :=
  cast (congrArg (fun y => F.obj (op (elementsPoint Z y))) (app_fst_of_comp_eq hσ z))
    (σ.app (op V) z).2

/-- A lift of `q` along `Σ_Z F ⟶ Z` sends `z` to the pair `(q z, valueOver hσ z)`. -/
lemma app_eq_of_comp_eq {σ : T ⟶ elementsTotalPresheaf Z F} (hσ : σ ≫ elementsTotalProj Z F = q)
    {V : BigFppfOver B S hS} (z : T.obj (op V)) :
    σ.app (op V) z = ⟨q.app (op V) z, valueOver hσ z⟩ :=
  Sigma.ext (app_fst_of_comp_eq hσ z) (cast_heq _ _).symm

/-- The values of a lift of `q` are compatible with every morphism of `El T`. -/
lemma valueOver_map {σ : T ⟶ elementsTotalPresheaf Z F} (hσ : σ ≫ elementsTotalProj Z F = q)
    {P Q : (presheafOfCategories (T ⋙ typeToCat)).obj} (m : P ⟶ Q) :
    (elementsPullback q F).map m.op (valueOver hσ Q.fiber.as) = valueOver hσ P.fiber.as := by
  have hz : P.fiber.as = T.map m.base.op Q.fiber.as := Discrete.eq_of_hom m.fiber
  have h1 : (⟨q.app (op P.base) P.fiber.as,
        (elementsPullback q F).map m.op (valueOver hσ Q.fiber.as)⟩ :
        Σ y : Z.obj (op P.base), F.obj (op (elementsPoint Z y))) =
      ⟨Z.map m.base.op (q.app (op Q.base) Q.fiber.as),
        F.map (elementsRestrict Z m.base.op (q.app (op Q.base) Q.fiber.as)).op
          (valueOver hσ Q.fiber.as)⟩ :=
    totalMk_eq Z F (valueOver hσ Q.fiber.as) ((associatedMap B S hS q).1.hom.map m)
      (elementsRestrict Z m.base.op _) rfl
  have h2 : σ.app (op P.base) (T.map m.base.op Q.fiber.as) =
      (elementsTotalPresheaf Z F).map m.base.op (σ.app (op Q.base) Q.fiber.as) :=
    types_congr_hom (σ.naturality m.base.op) Q.fiber.as
  rw [app_eq_of_comp_eq hσ, app_eq_of_comp_eq hσ] at h2
  have h3 : (⟨q.app (op P.base) (T.map m.base.op Q.fiber.as),
        valueOver hσ (T.map m.base.op Q.fiber.as)⟩ :
        Σ y : Z.obj (op P.base), F.obj (op (elementsPoint Z y))) =
      ⟨q.app (op P.base) P.fiber.as, valueOver hσ P.fiber.as⟩ := by
    rw [← hz]
  exact eq_of_heq (Sigma.mk.inj_iff.1 (h1.trans (h2.symm.trans h3))).2

/-- The global section of `q^*F` of a lift of `q` along `Σ_Z F ⟶ Z`. -/
def globalSectionOfLift {σ : T ⟶ elementsTotalPresheaf Z F}
    (hσ : σ ≫ elementsTotalProj Z F = q) : ElementsGlobalSection T (elementsPullback q F) :=
  ⟨fun P => valueOver hσ P.fiber.as, fun m => valueOver_map hσ m⟩

variable (q F)

/-- **Lifts of `q : T ⟶ Z` along `Σ_Z F ⟶ Z` are global sections of `q^*F`.** -/
def sectionOverEquiv :
    {σ : T ⟶ elementsTotalPresheaf Z F // σ ≫ elementsTotalProj Z F = q} ≃
      ElementsGlobalSection T (elementsPullback q F) where
  toFun σ := globalSectionOfLift σ.2
  invFun t := ⟨sectionOverOf q F t, sectionOverOf_comp_elementsTotalProj q F t⟩
  left_inv σ := by
    refine Subtype.ext (NatTrans.ext (funext fun V => ?_))
    ext z
    exact (app_eq_of_comp_eq σ.2 (V := V.unop) z).symm
  right_inv t := by
    refine Subtype.ext (funext fun P => ?_)
    have h := app_eq_of_comp_eq (sectionOverOf_comp_elementsTotalProj q F t)
      (V := P.base) P.fiber.as
    exact (eq_of_heq (Sigma.mk.inj_iff.1 h).2).symm

/-- The global section of `q^*F` attached to a lift `σ` takes the value `valueOver σ.2 t` at
`(V, t)`. -/
@[simp]
lemma sectionOverEquiv_apply_coe
    (σ : {σ : T ⟶ elementsTotalPresheaf Z F // σ ≫ elementsTotalProj Z F = q})
    (P : (presheafOfCategories (T ⋙ typeToCat)).obj) :
    (sectionOverEquiv q F σ).1 P = valueOver σ.2 P.fiber.as :=
  rfl

/-- The lift of `q` attached to a global section `t` of `q^*F` is `sectionOverOf q F t`. -/
@[simp]
lemma sectionOverEquiv_symm_apply_coe (t : ElementsGlobalSection T (elementsPullback q F)) :
    ((sectionOverEquiv q F).symm t).1 = sectionOverOf q F t :=
  rfl

/-! ### Lifts of `q` along the sheaf of isomorphisms -/

section Isom

universe w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The point `T ⟶ Z ⟶ 𝒳 ×_𝒴 𝒳` of the twisted point `(x₁, x₂, α)` restricted along `q`. -/
noncomputable abbrev twistedPointOver (hZ : IsAlgebraicSpace B S hS Z) (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :=
  (associatedMap B S hS q).1.hom.toFunctor ⋙
    (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).toFunctor

/-- The composite of `twistedPointOver q hZ f x₁ x₂ α` with the projection of the relative
product to the base is the structure functor of the fibred category of `T`. -/
lemma twistedPointOver_comp (hZ : IsAlgebraicSpace B S hS Z) (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    twistedPointOver q hZ f x₁ x₂ α ⋙
        RelProdP 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor =
      (fibredCategory B S hS T).val.p :=
  (Functor.assoc _ _ _).trans
    ((congrArg ((associatedMap B S hS q).1.hom.toFunctor ⋙ ·)
      (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w).trans
      (associatedMap B S hS q).1.hom.w)

/-- **Lifts of `q : T ⟶ Z` along `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` are natural families of vertical
morphisms `x₁(q t) ⟶ x₂(q t)` over the components of `α`**, indexed by the points `t` of `T`.
For `q = 𝟙 Z` this is `AlgebraicGeometry.Stack.relativeIsomorphismSectionEquiv`. -/
noncomputable def relativeIsomorphismSectionOverEquiv (hZ : IsAlgebraicSpace B S hS Z)
    (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    {σ : T ⟶ relativeIsomorphismTotalPresheaf B S hS Z hZ f x₁ x₂ α //
      σ ≫ PresheafOfCategories.elementsTotalProj Z
        (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
          (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w) = q} ≃
      RelVertFamily (fibredCategory B S hS T).val.p (twistedPointOver q hZ f x₁ x₂ α) :=
  (sectionOverEquiv q _).trans
    (relVertHomGlobalSectionEquiv 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (twistedPointOver_comp q hZ f x₁ x₂ α) f.hom.hom.w)

/-- **The 2-morphism of a natural family of vertical morphisms over `α`.** A family
`ψ t : x₁(q t) ⟶ x₂(q t)` as in `relativeIsomorphismSectionOverEquiv` is a 2-morphism
`x₁ ∘ q ⟶ x₂ ∘ q` of 1-morphisms `T ⟶ 𝒳`. -/
noncomputable def twoMorphismOfRelVertFamily (hT : IsAlgebraicSpace B S hS T)
    (hZ : IsAlgebraicSpace B S hS Z)
    (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    (ψ : RelVertFamily (fibredCategory B S hS T).val.p (twistedPointOver q hZ f x₁ x₂ α)) :
    algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₁ ⟶
      algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₂ :=
  Bicategory.InducedBicategory.mkHom₂ (Bicategory.InducedBicategory.mkHom₂
    { app := fun a => ψ.1 a
      naturality := fun _ _ h => (ψ.2.2.2 h).symm
      isHomLift' := ψ.2.1 })

/-- The component of `twoMorphismOfRelVertFamily q hT hZ f x₁ x₂ α ψ` at `a` is `ψ a`. -/
@[simp]
lemma twoMorphismOfRelVertFamily_app (hT : IsAlgebraicSpace B S hS T)
    (hZ : IsAlgebraicSpace B S hS Z) (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (α : x₁ ≫ f ⟶ x₂ ≫ f)
    (ψ : RelVertFamily (fibredCategory B S hS T).val.p (twistedPointOver q hZ f x₁ x₂ α))
    (a : (fibredCategory B S hS T).val.obj) :
    (twoMorphismOfRelVertFamily q hT hZ f x₁ x₂ α ψ).hom.hom.toNatTrans.app a = ψ.1 a :=
  rfl

/-- **The natural family of vertical morphisms of a 2-morphism over `α`.** A 2-morphism
`η : x₁ ∘ q ⟶ x₂ ∘ q` whose image under `f` is `α` at every point is a family as in
`relativeIsomorphismSectionOverEquiv`. -/
noncomputable def relVertFamilyOfTwoMorphism (hT : IsAlgebraicSpace B S hS T)
    (hZ : IsAlgebraicSpace B S hS Z)
    (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    (η : algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₁ ⟶
      algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₂)
    (hη : ∀ a, f.hom.hom.map (η.hom.hom.toNatTrans.app a) =
      ((twistedPointOver q hZ f x₁ x₂ α).obj a).iso.hom) :
    RelVertFamily (fibredCategory B S hS T).val.p (twistedPointOver q hZ f x₁ x₂ α) :=
  ⟨fun a => η.hom.hom.toNatTrans.app a, fun a => η.hom.hom.isHomLift' a, hη,
    fun h => (η.hom.hom.toNatTrans.naturality h).symm⟩

/-- The 2-morphism of the family `relVertFamilyOfTwoMorphism q hT hZ f x₁ x₂ α η hη` is `η`. -/
lemma twoMorphismOfRelVertFamily_relVertFamilyOfTwoMorphism (hT : IsAlgebraicSpace B S hS T)
    (hZ : IsAlgebraicSpace B S hS Z) (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (α : x₁ ≫ f ⟶ x₂ ≫ f)
    (η : algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₁ ⟶
      algebraicSpaceStackMap.{u, w} B S hS hT hZ q ≫ x₂)
    (hη : ∀ a, f.hom.hom.map (η.hom.hom.toNatTrans.app a) =
      ((twistedPointOver q hZ f x₁ x₂ α).obj a).iso.hom) :
    twoMorphismOfRelVertFamily q hT hZ f x₁ x₂ α
        (relVertFamilyOfTwoMorphism q hT hZ f x₁ x₂ α η hη) =
      η :=
  rfl

end Isom

end AlgebraicGeometry.Stack.ChowGerbeIsomOver

end
