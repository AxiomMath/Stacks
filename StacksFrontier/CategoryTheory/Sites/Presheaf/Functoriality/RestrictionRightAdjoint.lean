module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# More functoriality of presheaves

Let `u : C ⥤ D` be a functor. The restriction functor `u^p : PSh(D) ⥤ PSh(C)`,
`G ↦ G ∘ u`, has the left adjoint `u_p` and also a right adjoint `{}_pu`. For `V : D` the
category `{}_V I = {}^u_V I` has as objects the pairs `(U, ψ : u U ⟶ V)` and as morphisms
`(U, ψ) ⟶ (U', ψ')` the morphisms `α : U ⟶ U'` with `ψ = ψ' ∘ u α`; this is Mathlib's
`CategoryTheory.CostructuredArrow u V`. A presheaf `F` on `C` gives the functor
`{}_V F : {}_V Iᵒᵖ ⥤ Sets`, `(U, ψ) ↦ F(U)`, which is `(CostructuredArrow.proj u V).op ⋙ F`,
and `{}_pu F (V)` is the limit of `{}_V F`. Concretely, it is the set of collections
`s_{(U, ψ)} ∈ F(U)` with `β^* s_{(U₂, ψ₂)} = s_{(U₁, ψ₁)}` for every morphism
`β : (U₁, ψ₁) ⟶ (U₂, ψ₂)` of `{}_V I`, the correspondence being given by the projection maps
`c(ψ) : {}_pu F (V) ⟶ F(U)` of the limit. The restriction along `g : V' ⟶ V` sends a collection
`s` to `(U, ψ') ↦ s_{(U, g ∘ ψ')}`, and a map of presheaves `F ⟶ F'` acts componentwise. Together
with `u_p ⊣ u^p` this gives the sequence `u_p, u^p, {}_pu` in which each consecutive pair is an
adjoint pair.

## Main definitions

* `CategoryTheory.CostructuredArrow.objEquiv`, `CategoryTheory.CostructuredArrow.homEquiv`: the
  objects and the morphisms of `{}_V I = CostructuredArrow u V`.
* `CategoryTheory.Functor.ranObjIsoLimitCostructuredArrow`: the right Kan extension `{}_pu F`
  along `u.op` evaluated at `V` is the limit of `{}_V F` over `{}_V Iᵒᵖ`.
* `CategoryTheory.Functor.ranObjEquivCompatibleFamilies`: for presheaves of sets, `{}_pu F (V)` is
  the set of compatible collections `(s_{(U, ψ)})`.
* `CategoryTheory.Functor.lanRanAdjunctionTriple`: the adjoint triple `u_p ⊣ u^p ⊣ {}_pu`.

## Main results

* `CategoryTheory.Functor.ranObjIsoLimitCostructuredArrow_hom_π`: the projection maps `c(ψ)`.
* `CategoryTheory.Functor.ranObjEquivCompatibleFamilies_apply`: the correspondence is
  `s ↦ c(ψ)(s)`.
* `CategoryTheory.Functor.ranObjEquivCompatibleFamilies_map`: the restriction mappings of
  `{}_pu F`.
* `CategoryTheory.Functor.ranObjEquivCompatibleFamilies_ran_map`: the action of `{}_pu` on maps of
  presheaves.

## Implementation notes

The functor `{}_pu` is Mathlib's right Kan extension `CategoryTheory.Functor.ran` along `u.op`
(and `u_p` is `CategoryTheory.Functor.lan`), so the presheaf structure of `{}_pu F` and the
functoriality of `{}_pu` are Mathlib's; the results below identify them with the source's formulas.
Mathlib computes the right Kan extension at `op V` as a limit over
`StructuredArrow (op V) u.op`, which is identified with `{}_V Iᵒᵖ` by
`CategoryTheory.costructuredArrowOpEquivalence`. The categorical statements are made for presheaves
with values in any category `A` having the limits (and, for `u_p`, the colimits) that occur; the
presheaves of sets of the source are the case `A = Type w`, with `UnivLE.{max u₁ v₂, w}` saying
that the index categories are small enough for their limits to exist in `Type w`.

## References

* [Stacks Project, Section 00XF](https://stacks.math.columbia.edu/tag/00XF)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃

add_to_stacks 00XF "`u^p : PSh(D) ⥤ PSh(C)` sends `G` to `G ∘ u`"
  CategoryTheory.Functor.whiskeringLeft_obj_obj

namespace CategoryTheory

namespace CostructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (S : C ⥤ D) (T : D)

/-- The objects of the category `{}_T I = CostructuredArrow S T` are the pairs `(U, ψ)` of an
object `U` of `C` and a morphism `ψ : S U ⟶ T`. -/
@[stacks 00XF "the objects of the category `{}_V I` are the pairs `(U, ψ : u U ⟶ V)`"]
def objEquiv : CostructuredArrow S T ≃ Σ U : C, (S.obj U ⟶ T) where
  toFun X := ⟨X.left, X.hom⟩
  invFun p := CostructuredArrow.mk p.2
  left_inv X := by
    cases X
    rfl
  right_inv _ := rfl

/-- `objEquiv` sends `mk ψ` to the pair `⟨U, ψ⟩`. -/
@[simp]
lemma objEquiv_mk {U : C} (ψ : S.obj U ⟶ T) : objEquiv S T (mk ψ) = ⟨U, ψ⟩ := rfl

/-- The inverse of `objEquiv` sends a pair `⟨U, ψ⟩` to `mk ψ`. -/
@[simp]
lemma objEquiv_symm_apply (p : Σ U : C, (S.obj U ⟶ T)) : (objEquiv S T).symm p = mk p.2 := rfl

variable {S T}

/-- The morphisms `(U, ψ) ⟶ (U', ψ')` of `{}_T I = CostructuredArrow S T` are the morphisms
`α : U ⟶ U'` of `C` with `ψ = ψ' ∘ S α`. -/
@[stacks 00XF "a morphism `(U, ψ) ⟶ (U', ψ')` of `{}_V I` is a morphism `α : U ⟶ U'` with
`ψ = ψ' ∘ u(α)`"]
def homEquiv (X Y : CostructuredArrow S T) :
    (X ⟶ Y) ≃ { α : X.left ⟶ Y.left // S.map α ≫ Y.hom = X.hom } where
  toFun β := ⟨β.left, w β⟩
  invFun α := homMk α.1 α.2
  left_inv _ := by
    ext
    rfl
  right_inv _ := rfl

/-- The morphism of `C` underlying `homEquiv X Y β` is `β.left`. -/
@[simp]
lemma homEquiv_apply_coe {X Y : CostructuredArrow S T} (β : X ⟶ Y) :
    (homEquiv X Y β : X.left ⟶ Y.left) = β.left := rfl

/-- The inverse of `homEquiv X Y` sends `α` to `homMk α.1 α.2`. -/
@[simp]
lemma homEquiv_symm_apply {X Y : CostructuredArrow S T}
    (α : { α : X.left ⟶ Y.left // S.map α ≫ Y.hom = X.hom }) :
    (homEquiv X Y).symm α = homMk α.1 α.2 := rfl

end CostructuredArrow

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)

section General

variable {A : Type u₃} [Category.{v₃} A]

/-- The restriction functor `u^p : PSh(D) ⥤ PSh(C)` has a left adjoint `u_p`, the left Kan
extension along `u.op`, and a right adjoint `{}_pu`, the right Kan extension along `u.op`: the
functors `u_p, u^p, {}_pu` form an adjoint triple. -/
@[stacks 00XF "`u^p` has the left adjoint `u_p` and also a right adjoint `{}_pu`; in the sequence
`u_p, u^p, {}_pu` each consecutive pair is an adjoint pair",
  sga "4 I 5.1" "special case",
  sga "4 I 5.3" "more general",
  sga "4 I 5.5.2" "partial",
  sga "4 I 5.8.3" "more general",
  sga "4 III 2.2",
  sga "4 IV 4.5.2" "partial",
  sga "4 V 7.1.0" "more general"]
noncomputable def lanRanAdjunctionTriple [HasLimitsOfSize.{v₁, max u₁ v₂} A]
    [HasColimitsOfSize.{v₁, max u₁ v₂} A] :
    Adjunction.Triple u.op.lan ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op) u.op.ran :=
  ⟨u.op.lanAdjunction A, u.op.ranAdjunction A⟩

variable [HasLimitsOfSize.{v₁, max u₁ v₂} A]

/-- The value `{}_pu F (V)` of the right Kan extension of a presheaf `F` along `u.op` is the limit
over `{}_V Iᵒᵖ = (CostructuredArrow u V)ᵒᵖ` of the functor `{}_V F : (U, ψ) ↦ F(U)`. -/
@[stacks 00XF "`{}_pu F (V)` is the limit over `{}_V Iᵒᵖ` of `{}_V F : (U, ψ) ↦ F(U)`"]
noncomputable def ranObjIsoLimitCostructuredArrow (F : Cᵒᵖ ⥤ A) (V : D) :
    (u.op.ran.obj F).obj (op V) ≅ limit ((CostructuredArrow.proj u V).op ⋙ F) :=
  u.op.ranObjObjIsoLimit F (op V) ≪≫
    (HasLimit.isoOfEquivalence (F := (CostructuredArrow.proj u V).op ⋙ F)
      (G := StructuredArrow.proj (op V) u.op ⋙ F) (costructuredArrowOpEquivalence u V)
      (Iso.refl ((CostructuredArrow.proj u V).op ⋙ F))).symm

/-- The projection map `c(ψ) : {}_pu F (V) ⟶ F(U)` of the limit at an object `(U, ψ)` of `{}_V I`
is the restriction along `ψ` followed by the canonical map `{}_pu F (u U) ⟶ F(U)` of Stacks 00XG,
the counit of `u^p ⊣ {}_pu`. -/
@[reassoc (attr := simp), stacks 00XF "the projection maps `c(ψ) : {}_pu F (V) ⟶ F(U)` of the
limit"]
lemma ranObjIsoLimitCostructuredArrow_hom_π (F : Cᵒᵖ ⥤ A) (V : D)
    (X : CostructuredArrow u V) :
    (u.ranObjIsoLimitCostructuredArrow F V).hom ≫ limit.π _ (op X) =
      (u.op.ran.obj F).map X.hom.op ≫ (u.op.ranCounit.app F).app (op X.left) := by
  rw [ranObjIsoLimitCostructuredArrow, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  refine (congrArg _ ((HasLimit.isoOfEquivalence_inv_π _ _ _).trans (Category.comp_id _))).trans ?_
  exact u.op.ranObjObjIsoLimit_hom_π F (op V) ((costructuredArrowOpEquivalence u V).functor.obj
    (op X))

end General

section Types

variable [UnivLE.{max u₁ v₂, w}] (F : Cᵒᵖ ⥤ Type w) (V : D)

/-- For a presheaf of sets `F` on `C`, the set `{}_pu F (V)` is the set of collections
`s_{(U, ψ)} ∈ F(U)`, indexed by the objects `(U, ψ)` of `{}_V I`, such that
`β^* s_{(U₂, ψ₂)} = s_{(U₁, ψ₁)}` for every morphism `β : (U₁, ψ₁) ⟶ (U₂, ψ₂)` of `{}_V I`. -/
@[stacks 00XF "`{}_pu F (V)` is the set of collections `s_{(U, ψ)} ∈ F(U)` with
`β^* s_{(U₂, ψ₂)} = s_{(U₁, ψ₁)}` for all `β : (U₁, ψ₁) ⟶ (U₂, ψ₂)` in `{}_V I`"]
noncomputable def ranObjEquivCompatibleFamilies :
    (u.op.ran.obj F).obj (op V) ≃
      { s : ∀ X : CostructuredArrow u V, F.obj (op X.left) //
        ∀ ⦃X Y : CostructuredArrow u V⦄ (β : X ⟶ Y), F.map β.left.op (s Y) = s X } :=
  (u.ranObjIsoLimitCostructuredArrow F V).toEquiv.trans <|
    (Types.limitEquivSections _).trans
      { toFun x := ⟨fun X ↦ x.1 (op X), fun _ _ β ↦ x.2 β.op⟩
        invFun s := ⟨fun X ↦ s.1 X.unop, fun {_ _} β ↦ s.2 β.unop⟩
        left_inv _ := rfl
        right_inv _ := rfl }

/-- The correspondence `ranObjEquivCompatibleFamilies` is `s ↦ s_{(U, ψ)} = c(ψ)(s)`, where
`c(ψ)` is the projection map of the limit. -/
@[stacks 00XF "the correspondence is given by `s ↦ s_{(U, ψ)} = c(ψ)(s)`"]
lemma ranObjEquivCompatibleFamilies_apply (s : (u.op.ran.obj F).obj (op V))
    (X : CostructuredArrow u V) :
    (u.ranObjEquivCompatibleFamilies F V s).1 X =
      limit.π ((CostructuredArrow.proj u V).op ⋙ F) (op X)
        ((u.ranObjIsoLimitCostructuredArrow F V).hom s) :=
  rfl

/-- The component `s_{(U, ψ)}` of `s ∈ {}_pu F (V)` is the image of `s` under the restriction
along `ψ : u U ⟶ V` followed by the canonical map `{}_pu F (u U) ⟶ F(U)`. -/
@[simp]
lemma ranObjEquivCompatibleFamilies_apply_eq (s : (u.op.ran.obj F).obj (op V))
    (X : CostructuredArrow u V) :
    (u.ranObjEquivCompatibleFamilies F V s).1 X =
      (u.op.ranCounit.app F).app (op X.left) ((u.op.ran.obj F).map X.hom.op s) := by
  rw [ranObjEquivCompatibleFamilies_apply]
  exact ConcreteCategory.congr_hom (u.ranObjIsoLimitCostructuredArrow_hom_π F V X) s

/-- The restriction mapping `{}_pu F (V) ⟶ {}_pu F (V')` along `g : V' ⟶ V` sends a collection
`s` to the collection `(U, ψ') ↦ s_{(U, g ∘ ψ')}`. -/
@[stacks 00XF "the restriction mappings `{}_pu F (V) ⟶ {}_pu F (V')` along `V' ⟶ V`"]
lemma ranObjEquivCompatibleFamilies_map {V' : D} (g : V' ⟶ V) (s : (u.op.ran.obj F).obj (op V))
    (X : CostructuredArrow u V') :
    (u.ranObjEquivCompatibleFamilies F V' ((u.op.ran.obj F).map g.op s)).1 X =
      (u.ranObjEquivCompatibleFamilies F V s).1 ((CostructuredArrow.map g).obj X) := by
  simp only [ranObjEquivCompatibleFamilies_apply_eq, CostructuredArrow.map_obj_left,
    CostructuredArrow.map_obj_hom, op_comp, Functor.map_comp_apply]

/-- A map of presheaves `φ : F ⟶ F'` induces the map `{}_pu F ⟶ {}_pu F'` acting componentwise:
`s_{(U, ψ)} ↦ φ_U(s_{(U, ψ)})`. -/
@[stacks 00XF "a map of presheaves `F ⟶ F'` gives the map `{}_pu F ⟶ {}_pu F'` componentwise"]
lemma ranObjEquivCompatibleFamilies_ran_map {F' : Cᵒᵖ ⥤ Type w} (φ : F ⟶ F')
    (s : (u.op.ran.obj F).obj (op V)) (X : CostructuredArrow u V) :
    (u.ranObjEquivCompatibleFamilies F' V ((u.op.ran.map φ).app (op V) s)).1 X =
      φ.app (op X.left) ((u.ranObjEquivCompatibleFamilies F V s).1 X) := by
  simp only [ranObjEquivCompatibleFamilies_apply_eq]
  rw [← NatTrans.naturality_apply]
  exact ConcreteCategory.congr_hom (congr_app (u.op.ranCounit.naturality φ) (op X.left)) _

end Types

end Functor

end CategoryTheory
