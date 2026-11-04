module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Infinite products of schemes affine over a base

An arbitrary family of schemes affine over a fixed scheme `S` has a product in the category
`Over S` of schemes over `S`. That product is the inverse limit of the products of the finite
subfamilies, and each projection onto such a finite subproduct is an affine morphism.

Schemes over `S` are the objects of `CategoryTheory.Over S`. The inverse system of finite
subproducts is Mathlib's `CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinsetObj`,
indexed by the opposite of the finite subsets of the index type, and its canonical cone is
`CategoryTheory.Limits.ProductsFromFiniteCofiltered.finiteSubproductsCone`.

## Main definitions

* `CategoryTheory.Limits.ProductsFromFiniteCofiltered.finiteSubproductπ`: the projection of a
  finite subproduct onto one of its factors.
* `CategoryTheory.Limits.ProductsFromFiniteCofiltered.coneFromDiscreteCone`: the cone on the
  system of finite subproducts induced by a cone on the discrete diagram.

## Main results

* `CategoryTheory.Limits.ProductsFromFiniteCofiltered.hasProduct_of_hasLimit_liftToFinsetObj`:
  a family has a product as soon as its system of finite subproducts has a limit.
* `CategoryTheory.Limits.ProductsFromFiniteCofiltered.finiteSubproductsConeIsLimit`: a product
  is canonically the inverse limit of the products of its finite subfamilies.
* `AlgebraicGeometry.hasProduct_of_isAffineHom`: an arbitrary family of schemes affine over `S`
  has a product in `Over S`.
* `AlgebraicGeometry.isAffineHom_finiteSubproductsCone_π_app`: the projection from the infinite
  product onto any finite subproduct is affine.
* `AlgebraicGeometry.isAffineHom_over_finiteProduct`: the structure morphism of a finite product
  of schemes affine over `S` is affine.

## Implementation notes

Mathlib's `CategoryTheory.Limits.ProductsFromFiniteCofiltered.isLimitFiniteSubproductsCone` and
`liftToFinsetLimitCone` prove the same statements as `finiteSubproductsConeIsLimit` and
`hasProduct_of_hasLimit_liftToFinsetObj` under the stronger hypothesis
`HasLimitsOfShape (Finset (Discrete I))ᵒᵖ C`. That hypothesis is unavailable here: in `Over S`
the existence of such inverse limits is what is being established, and only the single limit of
the system of finite subproducts is at hand.

The objects of the system of finite subproducts are products indexed by a `Finset`, so their
projections are stated once and for all as `finiteSubproductπ`. Composing with that named
projection keeps every subsequent rewrite type-correct without having to unfold
`liftToFinsetObj`.

## References

* [Stacks Project, Tag 0CNI](https://stacks.math.columbia.edu/tag/0CNI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.ProductsFromFiniteCofiltered

universe u v w

namespace CategoryTheory.Limits.ProductsFromFiniteCofiltered

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {I : Type w} (X : I → C)

/-- The projection of the subproduct of `X` indexed by a finite set `J` of indices onto the
factor at `x ∈ J`. -/
noncomputable def finiteSubproductπ (J : (Finset (Discrete I))ᵒᵖ) (x : J.unop) :
    (liftToFinsetObj (Discrete.functor X)).obj J ⟶ X x.1.as :=
  Pi.π (fun y : J.unop => X y.1.as) x

/-- Two morphisms into a finite subproduct of `X` are equal when their projections onto every
factor agree. -/
lemma finiteSubproduct_hom_ext {J : (Finset (Discrete I))ᵒᵖ} {Z : C}
    {a b : Z ⟶ (liftToFinsetObj (Discrete.functor X)).obj J}
    (h : ∀ x : J.unop, a ≫ finiteSubproductπ X J x = b ≫ finiteSubproductπ X J x) : a = b :=
  Pi.hom_ext _ _ h

/-- The transition map between finite subproducts of `X` commutes with the projections onto the
factors. -/
@[reassoc]
lemma finiteSubproductπ_naturality {J K : (Finset (Discrete I))ᵒᵖ} (g : J ⟶ K) (y : K.unop) :
    (liftToFinsetObj (Discrete.functor X)).map g ≫ finiteSubproductπ X K y =
      finiteSubproductπ X J ⟨y.1, g.unop.down.down y.2⟩ :=
  Pi.lift_π _ _

/-- The projection of the product cone of `X` onto the factor at `i`. -/
noncomputable def finiteSubproductsConeπ [HasProduct X] (i : I) :
    (finiteSubproductsCone X).pt ⟶ X i :=
  Pi.π X i

/-- Two morphisms into the product of `X` are equal when their projections onto every factor
agree. -/
lemma finiteSubproductsCone_hom_ext [HasProduct X] {Z : C}
    {a b : Z ⟶ (finiteSubproductsCone X).pt}
    (h : ∀ i, a ≫ finiteSubproductsConeπ X i = b ≫ finiteSubproductsConeπ X i) : a = b :=
  Pi.hom_ext _ _ h

/-- The projection of the product of `X` onto a finite subproduct, followed by the projection
onto the factor at `x`, is the projection of the product onto that factor. -/
@[reassoc]
lemma finiteSubproductsCone_π_app_finiteSubproductπ [HasProduct X]
    (J : (Finset (Discrete I))ᵒᵖ) (x : J.unop) :
    (finiteSubproductsCone X).π.app J ≫ finiteSubproductπ X J x =
      finiteSubproductsConeπ X x.1.as :=
  Pi.lift_π _ _

/-- Every projection of a cone on the system of finite subproducts factors through its
projection onto a singleton subproduct. -/
lemma cone_π_app_finiteSubproductπ (s : Cone (liftToFinsetObj (Discrete.functor X)))
    (J : (Finset (Discrete I))ᵒᵖ) (x : J.unop) :
    s.π.app J ≫ finiteSubproductπ X J x =
      s.π.app (Opposite.op {x.1}) ≫ finiteSubproductπ X (Opposite.op {x.1}) ⟨x.1, by simp⟩ := by
  have hle : ({x.1} : Finset (Discrete I)) ≤ J.unop := by simp
  rw [← s.w (Quiver.Hom.op (homOfLE hle) : J ⟶ Opposite.op {x.1}), Category.assoc,
    finiteSubproductπ_naturality]

/-- The cone on the system of finite subproducts of `X` induced by a cone on the discrete
diagram of `X`. -/
@[reducible]
noncomputable def coneFromDiscreteCone (s : Cone (Discrete.functor X)) :
    Cone (liftToFinsetObj (Discrete.functor X)) where
  pt := s.pt
  π :=
    { app := fun J => Pi.lift fun x : J.unop => s.π.app ⟨x.1.as⟩
      naturality := by
        intro J K g
        apply Pi.hom_ext
        intro x
        dsimp [liftToFinsetObj]
        simp only [Category.assoc, Pi.lift_π, Category.id_comp] }

/-- The projections of `coneFromDiscreteCone X s` onto the factors of a finite subproduct are
the projections of `s`. -/
@[reassoc]
lemma coneFromDiscreteCone_π_app_finiteSubproductπ (s : Cone (Discrete.functor X))
    (J : (Finset (Discrete I))ᵒᵖ) (x : J.unop) :
    (coneFromDiscreteCone X s).π.app J ≫ finiteSubproductπ X J x = s.π.app ⟨x.1.as⟩ :=
  Pi.lift_π _ _

section HasLimit

variable [HasLimit (liftToFinsetObj (Discrete.functor X))]

/-- The cone on the discrete diagram of `X` whose vertex is the limit of the system of finite
subproducts, with the projection at `i` read off from the subproduct indexed by `{i}`. -/
@[reducible]
noncomputable def coneOfLimitLiftToFinsetObj : Cone (Discrete.functor X) where
  pt := limit (liftToFinsetObj (Discrete.functor X))
  π := Discrete.natTrans fun j =>
    limit.π (liftToFinsetObj (Discrete.functor X)) (Opposite.op {j}) ≫
      finiteSubproductπ X (Opposite.op {j}) ⟨j, by simp⟩

/-- Every projection of the system of finite subproducts factors through the projection onto a
singleton subproduct. -/
lemma limit_π_finiteSubproductπ (J : (Finset (Discrete I))ᵒᵖ) (x : J.unop) :
    limit.π (liftToFinsetObj (Discrete.functor X)) J ≫ finiteSubproductπ X J x =
      limit.π (liftToFinsetObj (Discrete.functor X)) (Opposite.op {x.1}) ≫
        finiteSubproductπ X (Opposite.op {x.1}) ⟨x.1, by simp⟩ :=
  cone_π_app_finiteSubproductπ X (limit.cone _) J x

/-- The cone of `coneOfLimitLiftToFinsetObj` is a product cone. -/
noncomputable def isLimitConeOfLimitLiftToFinsetObj : IsLimit (coneOfLimitLiftToFinsetObj X) where
  lift s := limit.lift _ (coneFromDiscreteCone X s)
  fac s j := by
    dsimp only [coneOfLimitLiftToFinsetObj, Discrete.natTrans_app]
    rw [← Category.assoc, limit.lift_π, coneFromDiscreteCone_π_app_finiteSubproductπ]
  uniq s m hm := by
    refine limit.hom_ext fun J => finiteSubproduct_hom_ext X fun x => ?_
    rw [Category.assoc, limit.lift_π, coneFromDiscreteCone_π_app_finiteSubproductπ,
      limit_π_finiteSubproductπ]
    exact hm ⟨x.1.as⟩

/-- A family has a product as soon as its system of finite subproducts has a limit. -/
theorem hasProduct_of_hasLimit_liftToFinsetObj : HasProduct X :=
  ⟨⟨⟨_, isLimitConeOfLimitLiftToFinsetObj X⟩⟩⟩

end HasLimit

/-- The morphism into the product of `X` determined by a cone on the system of finite
subproducts: its component at `i` is read off from the subproduct indexed by `{i}`. -/
noncomputable def finiteSubproductsConeLift [HasProduct X]
    (s : Cone (liftToFinsetObj (Discrete.functor X))) : s.pt ⟶ (finiteSubproductsCone X).pt :=
  Pi.lift fun i => s.π.app (Opposite.op {Discrete.mk i}) ≫
    finiteSubproductπ X (Opposite.op {Discrete.mk i}) ⟨Discrete.mk i, by simp⟩

/-- The component of `finiteSubproductsConeLift X s` at `i` is the projection of `s` onto the
subproduct indexed by `{i}`. -/
lemma finiteSubproductsConeLift_π [HasProduct X]
    (s : Cone (liftToFinsetObj (Discrete.functor X))) (i : I) :
    finiteSubproductsConeLift X s ≫ finiteSubproductsConeπ X i =
      s.π.app (Opposite.op {Discrete.mk i}) ≫
        finiteSubproductπ X (Opposite.op {Discrete.mk i}) ⟨Discrete.mk i, by simp⟩ :=
  Pi.lift_π _ _

/-- A product is canonically the inverse limit of its finite subproducts. -/
@[stacks 0CNI "limit of finite subproducts"]
noncomputable def finiteSubproductsConeIsLimit [HasProduct X] :
    IsLimit (finiteSubproductsCone X) where
  lift s := finiteSubproductsConeLift X s
  fac s J := by
    refine finiteSubproduct_hom_ext X fun x => ?_
    rw [Category.assoc, finiteSubproductsCone_π_app_finiteSubproductπ,
      finiteSubproductsConeLift_π, cone_π_app_finiteSubproductπ X s J x]
  uniq s m hm := by
    refine finiteSubproductsCone_hom_ext X fun i => ?_
    rw [finiteSubproductsConeLift_π, ← hm (Opposite.op {Discrete.mk i}), Category.assoc,
      finiteSubproductsCone_π_app_finiteSubproductπ]

end CategoryTheory.Limits.ProductsFromFiniteCofiltered

namespace AlgebraicGeometry

/-- Splitting off the factor indexed by `none` identifies a product over `Option α` in `Over K`
with the binary product of that factor and the product of the remaining factors. -/
noncomputable def overOptionProductIso {K : Scheme.{u}} {α : Type w}
    (Y : Option α → Over K) [HasProduct Y] [HasProduct (fun a : α => Y (some a))]
    [HasBinaryProduct (Y none) (∏ᶜ fun a : α => Y (some a))] :
    (∏ᶜ Y) ≅ Y none ⨯ (∏ᶜ fun a : α => Y (some a)) where
  hom := prod.lift (Pi.π Y none) (Pi.lift fun a => Pi.π Y (some a))
  inv := Pi.lift fun o => match o with
    | none => prod.fst
    | some a => prod.snd ≫ Pi.π _ a
  hom_inv_id := by
    apply Pi.hom_ext
    intro o
    cases o <;> simp
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · apply Pi.hom_ext
      intro a
      simp

/-- A limit of a finite diagram in `Over S` with affine vertices over an affine `S` has affine
vertex. -/
private lemma affine_of_isLimitOverProduct {S : Scheme.{u}} {J : Type w} [Finite J]
    (F : Discrete J ⥤ Over S) (c : Cone F) (hc : IsLimit c) [IsAffine S]
    (hF : ∀ j, IsAffine (F.obj j).left) : IsAffine c.pt.left := by
  let e := Over.ConstructProducts.conesEquiv S F
  let c' := e.inverse.obj c
  have hc₁ : IsLimit (e.functor.obj c') := IsLimit.ofIsoLimit hc (e.counitIso.app c).symm
  have hc₂ : IsLimit c' := (IsLimit.ofConeEquiv e) hc₁
  have (j : WidePullbackShape J) :
      IsAffine ((Over.ConstructProducts.widePullbackDiagramOfDiagramOver S F).obj j) := by
    cases j with
    | none => exact ‹IsAffine S›
    | some j => simpa [Over.ConstructProducts.widePullbackDiagramOfDiagramOver] using hF ⟨j⟩
  exact Scheme.isAffine_of_isLimit c' hc₂

/-- The structure morphism of the product in `Over S` of a finite family of schemes affine
over `S` is again affine. -/
lemma isAffineHom_over_finiteProduct {S : Scheme.{u}} {J : Type w} [Finite J]
    (F : J → Over S) (hF : ∀ j, IsAffineHom (F j).hom) : IsAffineHom (∏ᶜ F).hom := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨i, y, rfl⟩ := S.affineCover.exists_eq x
  let U : S.Opens := (S.affineCover.f i).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have : IsAffine U := hU
  have hUmem : (S.affineCover.f i).base y ∈ U := ⟨y, rfl⟩
  let F' := Discrete.functor F
  let G := F' ⋙ Over.pullback U.ι
  let c := (Over.pullback U.ι).mapCone (limit.cone F')
  have hc : IsLimit c := isLimitOfPreserves (Over.pullback U.ι) (limit.isLimit F')
  have hG : ∀ j, IsAffine (G.obj j).left := by
    intro j
    have : MorphismProperty.IsStableUnderBaseChangeAlong (P := @IsAffineHom) U.ι :=
      ⟨fun pb hf => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hf⟩
    have : IsAffineHom (pullback.snd (F j.as).hom U.ι) :=
      MorphismProperty.pullback_snd _ _ (hF j.as)
    exact isAffine_of_isAffineHom (pullback.snd (F j.as).hom U.ι)
  have hpb : IsAffine c.pt.left := affine_of_isLimitOverProduct G c hc hG
  have hpre : IsAffineOpen ((∏ᶜ F).hom ⁻¹ᵁ U) := by
    have : IsAffine (pullback (∏ᶜ F).hom U.ι) := by
      simpa [c, G, F', Over.pullback] using hpb
    exact IsAffine.of_isIso (pullbackRestrictIsoRestrict (∏ᶜ F).hom U).inv
  exact ⟨U, hUmem, hU, hpre⟩

/-- Every object of the system of finite subproducts of a family affine over `S` is affine
over `S`. -/
private lemma isAffineHom_liftToFinsetObj_obj_hom {I : Type u} {S : Scheme.{u}}
    {T : I → Scheme.{u}} (f : ∀ i, T i ⟶ S) [∀ i, IsAffineHom (f i)]
    (J : (Finset (Discrete I))ᵒᵖ) :
    IsAffineHom ((liftToFinsetObj (Discrete.functor fun i => Over.mk (f i))).obj J).hom := by
  simpa [liftToFinsetObj] using
    isAffineHom_over_finiteProduct (fun x : J.unop => Over.mk (f x.1.as))
      (fun x => inferInstanceAs (IsAffineHom (f x.1.as)))

/-- Every transition morphism of the system of finite subproducts of a family affine over `S`
is affine. -/
private lemma isAffineHom_liftToFinsetObj_map {I : Type u} {S : Scheme.{u}}
    {T : I → Scheme.{u}} (f : ∀ i, T i ⟶ S) [∀ i, IsAffineHom (f i)]
    (J K : (Finset (Discrete I))ᵒᵖ) (g : J ⟶ K) :
    IsAffineHom
      (((liftToFinsetObj (Discrete.functor fun i => Over.mk (f i))) ⋙ Over.forget S).map g) := by
  set D := liftToFinsetObj (Discrete.functor fun i => Over.mk (f i)) with hD
  have : IsAffineHom (D.obj K).hom := isAffineHom_liftToFinsetObj_obj_hom f K
  have : IsAffineHom (((D ⋙ Over.forget S).map g) ≫ (D.obj K).hom) := by
    simpa using isAffineHom_liftToFinsetObj_obj_hom f J
  exact IsAffineHom.of_comp ((D ⋙ Over.forget S).map g) (D.obj K).hom

/-- An arbitrary family of schemes affine over `S` has a product in the category of schemes
over `S`. -/
@[stacks 0CNI "existence"]
theorem hasProduct_of_isAffineHom {I : Type u} (S : Scheme.{u})
    (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ S) [∀ i, IsAffineHom (f i)] :
    HasProduct (fun i => Over.mk (f i)) := by
  classical
  set X : I → Over S := fun i => Over.mk (f i) with hX
  set D := liftToFinsetObj (Discrete.functor X) with hD
  have hmap (J K : (Finset (Discrete I))ᵒᵖ) (g : J ⟶ K) :
      IsAffineHom ((D ⋙ Over.forget S).map g) := isAffineHom_liftToFinsetObj_map f J K g
  have : HasLimit (D ⋙ Over.forget S) :=
    hasLimit_of_isCofiltered_of_isAffineHom (D ⋙ Over.forget S)
  have : HasLimit D := hasLimit_of_created D (Over.forget S)
  exact hasProduct_of_hasLimit_liftToFinsetObj X

/-- The canonical projection from the infinite product of a family of schemes affine over `S`
onto any of its finite subproducts is affine. -/
@[stacks 0CNI "affine projections"]
theorem isAffineHom_finiteSubproductsCone_π_app {I : Type u} (S : Scheme.{u})
    (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ S) [∀ i, IsAffineHom (f i)]
    [HasProduct (fun i => Over.mk (f i))] (J : (Finset (Discrete I))ᵒᵖ) :
    IsAffineHom ((finiteSubproductsCone (fun i => Over.mk (f i))).π.app J).left := by
  set X : I → Over S := fun i => Over.mk (f i) with hX
  set D := liftToFinsetObj (Discrete.functor X) with hD
  have hc' := isLimitOfPreserves (Over.forget S) (finiteSubproductsConeIsLimit X)
  have hmap (J K : (Finset (Discrete I))ᵒᵖ) (g : J ⟶ K) :
      IsAffineHom ((D ⋙ Over.forget S).map g) := isAffineHom_liftToFinsetObj_map f J K g
  exact isAffineHom_π_app (D ⋙ Over.forget S)
    ((Functor.mapCone (Over.forget S)) (finiteSubproductsCone X)) hc' J

end AlgebraicGeometry

end
