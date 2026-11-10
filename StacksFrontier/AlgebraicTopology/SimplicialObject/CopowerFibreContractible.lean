module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeOfSimplicialModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian

/-!
# The fibres of a representable on the simplicial site are products with a standard simplex

Let `C` be a small category and let `Δ × C` be the simplicial site of [Stacks, Tag 09D0]. Fix an
object `X = (X₁, X₂)` of `Δ × C` and an object `V` of `C`, and consider the presheaf of types on
`Δ × C` represented by `X`, namely `h_X = Mor_{Δ × C}(-, X)` (universe-lifted, as Mathlib's
`CategoryTheory.uliftYoneda`). Restricted to the fibre `⦋m⦌ ↦ (⦋m⦌, V)` over `V`, it is the
simplicial set `⦋m⦌ ↦ Mor_Δ(⦋m⦌, X₁) × Mor_C(V, X₂)`: the product of [Stacks, Tag 017C] of the
standard simplex `Δ[X₁]` with the constant simplicial set on `Mor_C(V, X₂)`, which is the copower
of `StacksFrontier/AlgebraicTopology/SimplicialObject/Copower.lean`. Under that identification, the
morphism of presheaves which forgets the `Δ`-component of a morphism into `X` becomes the
projection of [Stacks, Tag 017E] (2) of the copower onto its constant factor: the `Δ`-component of
a morphism is exactly the index of the summand it lies in.

The standard simplices are contractible ([Stacks, Tag 08QD]) and the projection out of a product
with a contractible simplicial set is a homotopy equivalence, so the restriction of that morphism
to the fibre over `V` is a homotopy equivalence of simplicial sets; multiplying it by an arbitrary
simplicial object keeps it one, because multiplying by a simplicial object preserves homotopy
equivalences. The last statement is what the proof of [Stacks, Tag 09D2] consumes: there the
simplicial object is the one whose copower by a representable is a free module, and the homotopy
equivalence is what makes the Moore complexes of the two sides quasi-isomorphic.

## Main definitions

* `Stacks.SimplicialSite.prodProjIndex`: the morphism of presheaves of types on `Δ × C` which
  keeps the `C`-component of a morphism into `X`, i.e. the map `h_X ⟶ h_{X₂} ∘ pr₂`.
* `Stacks.SimplicialSite.fibreIndexIso`: the fibre over `V` of `h_X` is the copower of the
  constant simplicial set on `Mor_C(V, X₂)` by the standard simplex `Δ[X₁]`.

## Main results

* `CategoryTheory.SimplicialObject.homotopyEquivalences_copowerProj`: the projection `S × P ⟶ P`
  of [Stacks, Tag 017E] (2) is a homotopy equivalence whenever the simplicial set `S` is homotopy
  equivalent to a singleton.
* `Stacks.SimplicialSite.homotopyEquivalences_prodProjIndex_fibre`: the restriction of
  `prodProjIndex` to the fibre over `V` is a homotopy equivalence of simplicial sets.
* `Stacks.SimplicialSite.homotopyEquivalences_copowerMap_prodProjIndex_fibre`: the product of that
  restriction with an arbitrary simplicial object is a homotopy equivalence.

## Implementation notes

The identification of the fibre with the copower is built from the morphism out of the copower
(`Stacks.SimplicialSite.fibreIndexDown`), which is the one whose naturality is a statement about
the summands of a coproduct; that it is an isomorphism is checked degreewise, where no naturality
is involved.

The target of the restriction of `prodProjIndex` to the fibre over `V` is the simplicial set
`⦋m⦌ ↦ Mor_C(V, X₂)` whose structure maps are `g ↦ id_V ∘ g`; it is the constant simplicial set on
`Mor_C(V, X₂)`, but only up to the isomorphism `Stacks.SimplicialSite.prodSectionSndIsoConst`, not
on the nose, because `id_V ∘ g` and `g` are not the same term.

## References

* [Stacks, Tag 017C](https://stacks.math.columbia.edu/tag/017C)
* [Stacks, Tag 017E](https://stacks.math.columbia.edu/tag/017E)
* [Stacks, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
* [Stacks, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace CategoryTheory.SimplicialObject

/-- **The projection `S × P ⟶ P` of [Stacks, Tag 017E] (2) is a homotopy equivalence** whenever
the simplicial set `S` admits a homotopy equivalence onto the constant simplicial set on a
singleton: the projection factors as the morphism of products induced by such a homotopy
equivalence `f : S ⟶ ∗`, which is a homotopy equivalence because multiplying by `P` preserves
them, followed by the projection out of the product with `∗`, which is an isomorphism. -/
theorem homotopyEquivalences_copowerProj {A : Type*} [Category* A] [HasCoproducts.{w} A]
    (P : SimplicialObject A) {S : SimplicialObject (Type w)}
    {f : S ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1}}
    (hf : homotopyEquivalences (Type w) f) :
    homotopyEquivalences A (P.copowerProj S) := by
  have he : Functor.copowerMap (𝟙 P) f ≫
      P.copowerProj ((Functor.const _).obj PUnit.{w + 1}) = P.copowerProj S := by
    simpa only [Category.comp_id] using Functor.copowerMap_comp_copowerProj (𝟙 P) f
  have h := homotopyEquivalences_iso_comp_iso (Iso.refl _) (Functor.copowerMap (𝟙 P) f)
    (Functor.copowerConstPUnitIso.{w} P) (homotopyEquivalences_copowerMap_id P hf)
  rwa [Iso.refl_hom, Category.id_comp, Functor.copowerConstPUnitIso_hom, he] at h

end CategoryTheory.SimplicialObject

namespace Stacks.SimplicialSite

variable {C : Type u} [SmallCategory C]

/-- The family of summands, in degree `j`, of the copower of the constant simplicial set on
`Mor_C(V, X₂)` by the standard simplex on `X₁`: the `Δ`-simplices `α : ⦋m⦌ ⟶ X₁` index copies of
`Mor_C(V, X₂)`. -/
abbrev fibreIndexFamily (X : SimplexCategory × C) (V : C) (j : SimplexCategoryᵒᵖ) :
    ((SSet.stdSimplex.{u}).obj X.1).obj j → Type u :=
  fun _ => ((Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (V ⟶ X.2))).obj j

/-- **The morphism out of the copower**: the point `g : V ⟶ X₂` of the summand indexed by a
`Δ`-simplex `α : ⦋m⦌ ⟶ X₁` is sent to the morphism `(α, g) : (⦋m⦌, V) ⟶ X` of `Δ × C`. -/
def fibreIndexDown (X : SimplexCategory × C) (V : C) :
    ((Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (V ⟶ X.2))).copower
        ((SSet.stdSimplex.{u}).obj X.1) ⟶
      (Functor.prodSectionFst V).op ⋙ uliftYoneda.{u}.obj X where
  app j := Sigma.desc fun α => ↾ fun g => ULift.up (α.down, g.down)
  naturality j k f := by
    refine Sigma.hom_ext _ _ fun α => ?_
    rw [Functor.copower_map, Sigma.ι_comp_map'_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    refine ConcreteCategory.hom_ext _ _ fun g => ?_
    refine congrArg ULift.up (CategoryTheory.Prod.hom_ext ?_ ?_)
    · rfl
    · exact (Category.id_comp _).symm

/-- The restriction of `Stacks.SimplicialSite.fibreIndexDown` to the summand indexed by the
`Δ`-simplex `α`. -/
@[reassoc (attr := simp)]
lemma ι_fibreIndexDown_app (X : SimplexCategory × C) (V : C) (j : SimplexCategoryᵒᵖ)
    (α : ((SSet.stdSimplex.{u}).obj X.1).obj j) :
    Sigma.ι (fibreIndexFamily X V j) α ≫ (fibreIndexDown X V).app j =
      ↾ fun g => ULift.up (α.down, g.down) :=
  Sigma.ι_comp_desc _ _

/-- **In each degree, `fibreIndexDown` is a bijection**: a morphism `(⦋m⦌, V) ⟶ X` of `Δ × C` is
the same thing as a `Δ`-simplex `α : ⦋m⦌ ⟶ X₁` together with a point `g : V ⟶ X₂` of the summand
it indexes. -/
instance isIso_fibreIndexDown_app (X : SimplexCategory × C) (V : C) (j : SimplexCategoryᵒᵖ) :
    IsIso ((fibreIndexDown X V).app j) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ↾ fun p => Sigma.ι (fibreIndexFamily X V j) (ULift.up p.down.1)
      (ULift.up p.down.2 : ULift.{u} (V ⟶ X.2))
  · refine Sigma.hom_ext _ _ fun α => ?_
    rw [ι_fibreIndexDown_app_assoc]
    refine ConcreteCategory.hom_ext _ _ fun g => ?_
    rfl
  · refine ConcreteCategory.hom_ext _ _ fun p => ?_
    exact ConcreteCategory.congr_hom (ι_fibreIndexDown_app X V j (ULift.up p.down.1))
      (ULift.up p.down.2 : ULift.{u} (V ⟶ X.2))

/-- `Stacks.SimplicialSite.fibreIndexDown` is an isomorphism, being one in every degree. -/
instance isIso_fibreIndexDown (X : SimplexCategory × C) (V : C) :
    IsIso (fibreIndexDown X V) :=
  NatIso.isIso_of_isIso_app _

/-- **The fibre of a representable on `Δ × C` is a product with a standard simplex.** The
restriction to the fibre `⦋m⦌ ↦ (⦋m⦌, V)` over `V` of the presheaf represented by `X = (X₁, X₂)`
is the product of [Stacks, Tag 017C] of the standard simplex on `X₁` with the constant simplicial
set on `Mor_C(V, X₂)`: a morphism `(⦋m⦌, V) ⟶ X` is a pair consisting of its `Δ`-component, which
indexes the summand, and its `C`-component, which is the point of that summand. -/
def fibreIndexIso (X : SimplexCategory × C) (V : C) :
    (Functor.prodSectionFst V).op ⋙ uliftYoneda.{u}.obj X ≅
      ((Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (V ⟶ X.2))).copower
        ((SSet.stdSimplex.{u}).obj X.1) :=
  (asIso (fibreIndexDown X V)).symm

/-- The inverse of `Stacks.SimplicialSite.fibreIndexIso` is
`Stacks.SimplicialSite.fibreIndexDown`. -/
@[simp]
lemma fibreIndexIso_inv (X : SimplexCategory × C) (V : C) :
    (fibreIndexIso X V).inv = fibreIndexDown X V :=
  rfl

/-- **Keeping the `C`-component of a morphism into `X`**: the morphism of presheaves of types on
`Δ × C` from the presheaf represented by `X` to the second projection of the presheaf represented
by `X₂`, which sends a morphism `(⦋m⦌, W) ⟶ X` to its `C`-component `W ⟶ X₂`. -/
def prodProjIndex (X : SimplexCategory × C) :
    uliftYoneda.{u}.obj X ⟶
      (CategoryTheory.Prod.snd SimplexCategory C).op ⋙ uliftYoneda.{u}.obj X.2 where
  app Y := ↾ fun p => ULift.up p.down.2
  naturality Y Z f := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    rfl

/-- The component of `Stacks.SimplicialSite.prodProjIndex` on a morphism `p`. -/
@[simp]
lemma prodProjIndex_app (X : SimplexCategory × C) (Y : (SimplexCategory × C)ᵒᵖ)
    (p : (uliftYoneda.{u}.obj X).obj Y) :
    (prodProjIndex X).app Y p = ULift.up p.down.2 :=
  rfl

/-- **The fibre over `V` of the second projection of a representable is constant**: the simplicial
set `⦋m⦌ ↦ Mor_C(V, W)`, whose structure maps are composition with `id_V`, is the constant
simplicial set on `Mor_C(V, W)`. -/
def prodSectionSndIsoConst (V W : C) :
    (Functor.prodSectionFst V).op ⋙ (CategoryTheory.Prod.snd SimplexCategory C).op ⋙
        uliftYoneda.{u}.obj W ≅
      (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (V ⟶ W)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro j k f
    refine ConcreteCategory.hom_ext _ _ fun g => ?_
    refine congrArg ULift.up ?_
    exact Category.id_comp _)

/-- The components of the inverse of `Stacks.SimplicialSite.prodSectionSndIsoConst` are
identities. -/
@[simp]
lemma prodSectionSndIsoConst_inv_app (V W : C) (j : SimplexCategoryᵒᵖ) :
    (prodSectionSndIsoConst V W).inv.app j = 𝟙 _ :=
  rfl

/-- **The restriction of `prodProjIndex` to the fibre over `V` is the projection out of the
copower.** Forgetting the `Δ`-component of a morphism `(⦋m⦌, V) ⟶ X` is, under
`Stacks.SimplicialSite.fibreIndexIso`, forgetting which summand of the copower a point lies
in. -/
lemma fibreIndexIso_inv_comp_prodProjIndex (X : SimplexCategory × C) (V : C) :
    (fibreIndexIso X V).inv ≫
        Functor.whiskerLeft (Functor.prodSectionFst V).op (prodProjIndex X) =
      Functor.copowerProj ((Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (V ⟶ X.2)))
          ((SSet.stdSimplex.{u}).obj X.1) ≫ (prodSectionSndIsoConst V X.2).inv := by
  refine NatTrans.ext (funext fun j => Sigma.hom_ext _ _ fun α => ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, fibreIndexIso_inv, ι_fibreIndexDown_app_assoc]
  simp only [Functor.copowerProj, Sigma.ι_comp_desc_assoc]
  refine ConcreteCategory.hom_ext _ _ fun g => ?_
  rfl

/-- **The restriction of `prodProjIndex` to the fibre over `V` is a homotopy equivalence of
simplicial sets.** By `Stacks.SimplicialSite.fibreIndexIso_inv_comp_prodProjIndex` it is, up to
isomorphisms on both sides, the projection of the product of the standard simplex on `X₁` with the
constant simplicial set on `Mor_C(V, X₂)` onto the second factor; the standard simplices are
contractible ([Stacks, Tag 08QD]), so that projection is a homotopy equivalence. -/
theorem homotopyEquivalences_prodProjIndex_fibre (X : SimplexCategory × C) (V : C) :
    SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerLeft (Functor.prodSectionFst V).op (prodProjIndex X)) := by
  have hcontr : SimplicialObject.homotopyEquivalences (Type u)
      (Functor.copowerProj ((Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (V ⟶ X.2)))
        ((SSet.stdSimplex.{u}).obj X.1)) :=
    SimplicialObject.homotopyEquivalences_copowerProj _
      (SimplicialObject.homotopyEquivalences_iso_comp_iso (Iso.refl _)
        ((SSet.stdSimplex.{u}).map (default : X.1 ⟶ SimplexCategory.mk 0))
        Stacks.SimplicialModules.stdSimplexZeroIsoConst
        ((SSet.stdSimplex.homotopyEquivalences_hom_obj₀ X.1.len).1 _))
  rw [(Iso.inv_comp_eq _).mp (fibreIndexIso_inv_comp_prodProjIndex X V)]
  exact SimplicialObject.homotopyEquivalences_iso_comp_iso (fibreIndexIso X V) _
    (prodSectionSndIsoConst V X.2).symm hcontr

/-- **The product of the restriction of `prodProjIndex` to the fibre over `V` with an arbitrary
simplicial object is a homotopy equivalence.** This is the input of the proof of
[Stacks, Tag 09D2]: multiplying by a simplicial object preserves homotopy equivalences
([Stacks, Tag 019N]), and the restriction is one by
`Stacks.SimplicialSite.homotopyEquivalences_prodProjIndex_fibre`. -/
theorem homotopyEquivalences_copowerMap_prodProjIndex_fibre {A : Type*} [Category* A]
    [HasCoproducts.{u} A] (P : SimplicialObject A) (X : SimplexCategory × C) (V : C) :
    SimplicialObject.homotopyEquivalences A (Functor.copowerMap (𝟙 P)
      (Functor.whiskerLeft (Functor.prodSectionFst V).op (prodProjIndex X))) :=
  SimplicialObject.homotopyEquivalences_copowerMap_id P
    (homotopyEquivalences_prodProjIndex_fibre X V)

end Stacks.SimplicialSite

end
