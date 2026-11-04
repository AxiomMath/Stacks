module

public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.PullbackPseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of descent data along a morphism of families of morphisms with fixed target

Let `p : 𝒳 ⥤ 𝒮` be a fibred category, let `𝒰 = {U i ⟶ U}` and `𝒱 = {V j ⟶ V}` be families of
morphisms with fixed target, and let `Φ = (α, h, g)` be a morphism of families from `𝒰` to `𝒱`
over `h : U ⟶ V`: a reindexing `α : I → J` together with morphisms `g i : U i ⟶ V (α i)` making
the squares over `h` commute.

A descent datum `(Y j, φ j j')` relative to `𝒱` is then pulled back to the descent datum
`(g i ^* Y (α i), (g i × g i') ^* φ (α i) (α i'))` relative to `𝒰`, the construction is
functorial, and it depends on the auxiliary data `(α, g)` only up to a canonical isomorphism:
two morphisms of families lying over one and the same `h : U ⟶ V` induce canonically isomorphic
functors.

## Main definitions

* `CategoryTheory.Functor.FamilyDescentDatum`, the category of descent data relative to a family
  of morphisms with fixed target for a fibred category;
* `CategoryTheory.Functor.FamilyDescentDatum.pull`, the pulled-back descent datum;
* `CategoryTheory.Functor.FamilyDescentDatum.pullFunctor`, the induced functor between the two
  categories of descent data;
* `CategoryTheory.Functor.FamilyDescentDatum.pullFunctorIso` and
  `CategoryTheory.Functor.FamilyDescentDatum.pullFunctorIsoOfEq`, the canonical isomorphism
  between the functors induced by two morphisms of families over the same morphism of targets.

## Implementation notes

Descent data for the fibred category `p` are taken to be descent data for the pullback
pseudofunctor `U ↦ 𝒳_U`, `f ↦ f^*` that `p` and its cleavage determine
(`CategoryTheory.Functor.IsFibered.pullbackPseudofunctor`, Stacks 02XO). The cleavage used is the
one the axiom of choice provides, `CategoryTheory.Functor.chosenPullbacks`, which is a choice of
pullbacks in the sense of Stacks 02XN; `pull_obj` records that the objects of the pulled-back
datum are indeed the chosen pullbacks `g i ^* Y (α i)` of that choice, and `pull_hom` that its
gluing morphisms are those of the original datum, transported along the canonical comparisons
`(a ≫ g)^* ≅ a^* ⋙ g^*` of the cleavage.

Descent data are indexed here by an arbitrary object `Y` mapping to two members of the family
compatibly over the target, rather than by chosen fibre products `U i ×_U U i'`; no fibre product
is therefore assumed to exist. When they do exist the two presentations agree, by
`CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence`. This is the same indexing the
sieve-shaped descent data of `CategoryTheory.Functor.SieveDescentDatum` use.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Opposite IsFibered Pseudofunctor

universe w' w v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The base change of a morphism of fibres along `f`, for the choice of pullbacks of Stacks 02XN
that the cleavage of a fibred category provides, is the action on morphisms of the pullback
functor `f^*` that the pullback pseudofunctor uses: both are the unique lift of `𝟙` through which
the chosen cartesian projection factors. -/
lemma chosenPullbacks_homMap_eq_fiberPullbackMap (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {V U : 𝒮} (f : V ⟶ U)
    {x x' : p.Fiber U} (α : x ⟶ x') :
    (chosenPullbacks p).homMap f α = fiberPullbackMap f α :=
  ((chosenPullbacks p).homMap_uniq f α _ (fiberPullbackMap_comm f α)).symm

/-- The category of *descent data relative to a family of morphisms with fixed target*
`𝒰 = {U i ⟶ U}` for a fibred category `p : 𝒳 ⥤ 𝒮`: an object of the fibre `𝒳_{U i}` for every
`i`, together with a gluing isomorphism between the two pullbacks of these objects to any object
`Y` mapping to `U i` and to `U i'` compatibly over `U`, subject to the cocycle condition and to
compatibility with further base change. -/
@[stacks 026B "The category `DD(𝒰)` for a fibred category: its objects (1), its morphisms (2) and
  its category structure (3). Indexed by an arbitrary object mapping to two members of the family
  in place of the chosen fibre products `U i ×_U U i'`, which the two presentations agree over
  whenever those exist, by
  `CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence`.",
  sga "3 IV 2.1" "descent datum", sga "1 VIII 7.8" "more general"]
abbrev FamilyDescentDatum (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮} (𝒰 : PreZeroHypercover.{w} U) :=
  (pullbackPseudofunctor p).DescentData 𝒰.f

namespace FamilyDescentDatum

variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U V : 𝒮} {𝒰 : PreZeroHypercover.{w} U}
  {𝒱 : PreZeroHypercover.{w'} V} {h : U ⟶ V}

/-- **Stacks 02ZD (1).**
The descent datum relative to `𝒰 = {U i ⟶ U}` obtained from a descent datum `(Y j, φ j j')`
relative to `𝒱 = {V j ⟶ V}` by pulling back along a morphism of families `Φ = (α, h, g)`: its
object over `U i` is the chosen pullback `g i ^* Y (α i)`, and its gluing morphisms are those of
`(Y j, φ j j')` pulled back along the `g i`. -/
@[stacks 02ZD "(1) the descent datum `(g i ^* Y (α i), (g i × g i') ^* φ (α i) (α i'))`"]
noncomputable def pull (Φ : 𝒰.HomOver 𝒱 h) (D : FamilyDescentDatum p 𝒱) :
    FamilyDescentDatum p 𝒰 :=
  DescentData.pullFunctorObj (F := pullbackPseudofunctor p) (f := 𝒱.f) (p := h) (f' := 𝒰.f)
    (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀ D

/-- The object of the pulled-back descent datum over `U i` is the pullback of `Y (α i)` along
`g i`, for the choice of pullbacks (Stacks 02XN) that the cleavage of `p` provides. -/
@[simp]
lemma pull_obj (Φ : 𝒰.HomOver 𝒱 h) (D : FamilyDescentDatum p 𝒱) (i : 𝒰.I₀) :
    ((pull p Φ D).obj i : p.Fiber (𝒰.X i)) =
      (chosenPullbacks p).obj (Φ.h₀ i) (D.obj (Φ.s₀ i)) :=
  rfl

/-- The gluing morphisms of the pulled-back descent datum are those of the original datum, read
at the composites `a ≫ g i` and transported along the canonical comparisons
`(a ≫ g i)^* ≅ a^* ⋙ (g i)^*` of the cleavage. -/
lemma pull_hom (Φ : 𝒰.HomOver 𝒱 h) (D : FamilyDescentDatum p 𝒱) {Y : 𝒮} (q : Y ⟶ U)
    {i₁ i₂ : 𝒰.I₀} (a₁ : Y ⟶ 𝒰.X i₁) (a₂ : Y ⟶ 𝒰.X i₂) (ha₁ : a₁ ≫ 𝒰.f i₁ = q)
    (ha₂ : a₂ ≫ 𝒰.f i₂ = q) :
    (pull p Φ D).hom q a₁ a₂ ha₁ ha₂ =
      ((pullbackPseudofunctor p).mapComp (Φ.h₀ i₁).op.toLoc a₁.op.toLoc).inv.toNatTrans.app
          (D.obj (Φ.s₀ i₁)) ≫
        D.hom (q ≫ h) (a₁ ≫ Φ.h₀ i₁) (a₂ ≫ Φ.h₀ i₂)
            (by rw [Category.assoc, Φ.w₀, reassoc_of% ha₁])
            (by rw [Category.assoc, Φ.w₀, reassoc_of% ha₂]) ≫
          ((pullbackPseudofunctor p).mapComp (Φ.h₀ i₂).op.toLoc a₂.op.toLoc).hom.toNatTrans.app
            (D.obj (Φ.s₀ i₂)) := by
  subst ha₁
  dsimp only [pull, DescentData.pullFunctorObj, DescentData.pullFunctorObjHom]

/-- **Stacks 02ZD (2).**
Pulling back descent data along a morphism of families `Φ = (α, h, g)` from `𝒰` to `𝒱` is a
functor from the category of descent data relative to `𝒱` to the category of descent data
relative to `𝒰`. -/
@[stacks 02ZD "(2) the functor from descent data relative to `𝒱` to descent data relative to `𝒰`",
  stacks 02ZE, implicit_reducible]
noncomputable def pullFunctor (Φ : 𝒰.HomOver 𝒱 h) :
    FamilyDescentDatum p 𝒱 ⥤ FamilyDescentDatum p 𝒰 :=
  DescentData.pullFunctor (pullbackPseudofunctor p) (f := 𝒱.f) (p := h) (f' := 𝒰.f)
    (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀

/-- On objects, the functor of Stacks 02ZD (2) is the construction of Stacks 02ZD (1). -/
@[simp]
lemma pullFunctor_obj (Φ : 𝒰.HomOver 𝒱 h) (D : FamilyDescentDatum p 𝒱) :
    (pullFunctor p Φ).obj D = pull p Φ D :=
  rfl

/-- On morphisms, the functor of Stacks 02ZD (2) applies the pullback functor `(g i)^*` of
Stacks 02XN componentwise. -/
lemma pullFunctor_map_hom (Φ : 𝒰.HomOver 𝒱 h) {D₁ D₂ : FamilyDescentDatum p 𝒱} (φ : D₁ ⟶ D₂)
    (i : 𝒰.I₀) :
    ((pullFunctor p Φ).map φ).hom i = fiberPullbackMap (Φ.h₀ i) (φ.hom (Φ.s₀ i)) :=
  rfl

/-- **Stacks 02ZD (3).**
Two morphisms of families `Φ = (α, h, g)` and `Φ' = (α', h, g')` from `𝒰` to `𝒱` lying over one
and the same morphism `h : U ⟶ V` of the targets induce canonically isomorphic functors on
descent data. The component of the isomorphism at a descent datum `(Y j, φ j j')` and an index
`i` is the gluing isomorphism of that datum between `g i ^* Y (α i)` and `g' i ^* Y (α' i)`. -/
@[stacks 02ZD "(3) for two morphisms of families over one and the same `h : U ⟶ V`"]
noncomputable def pullFunctorIso (Φ Φ' : 𝒰.HomOver 𝒱 h) : pullFunctor p Φ ≅ pullFunctor p Φ' :=
  DescentData.pullFunctorIso (pullbackPseudofunctor p) (f := 𝒱.f) (p := h) (f' := 𝒰.f)
    (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀ (β := Φ'.s₀) (p'' := Φ'.h₀) Φ'.w₀

/-- The component of the canonical isomorphism of Stacks 02ZD (3) at a descent datum
`(Y j, φ j j')` and an index `i` is the gluing morphism of that datum over `U i`, comparing the
pullback of `Y (α i)` along `g i` with the pullback of `Y (α' i)` along `g' i`. -/
lemma pullFunctorIso_hom_app_hom (Φ Φ' : 𝒰.HomOver 𝒱 h) (D : FamilyDescentDatum p 𝒱)
    (i : 𝒰.I₀) :
    ((pullFunctorIso p Φ Φ').hom.app D).hom i =
      D.hom (Φ.h₀ i ≫ 𝒱.f (Φ.s₀ i)) (Φ.h₀ i) (Φ'.h₀ i) rfl
        ((Φ'.w₀ i).trans (Φ.w₀ i).symm) :=
  rfl

/-- **Stacks 02ZD (3)**, with the hypothesis `h = h'` on the two morphisms of targets stated as
such: morphisms of families `Φ` over `h` and `Φ'` over `h'` with `h' = h` induce canonically
isomorphic functors on descent data. -/
@[stacks 02ZD "(3) for morphisms of families over `h` and over `h'` with `h' = h`, as in Stacks"]
noncomputable def pullFunctorIsoOfEq {h' : U ⟶ V} (Φ : 𝒰.HomOver 𝒱 h) (Φ' : 𝒰.HomOver 𝒱 h')
    (hh : h' = h) : pullFunctor p Φ ≅ pullFunctor p Φ' := by
  subst hh
  exact pullFunctorIso p Φ Φ'

end FamilyDescentDatum

end CategoryTheory.Functor
