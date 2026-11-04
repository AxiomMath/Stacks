module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Grothendieck
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentRestriction

/-!
# Restriction across fibres of a simplicial site (Stacks 09WF)

Let `S` be a simplicial-site situation and `φ : [m] ⟶ [n]` a simplex map.  Restricting a sheaf
on the total site to the components of degrees `m` and `n` gives two sheaves, compared by a
canonical transition map: on sections over an object `V` of degree `m` it is restriction of the
sheaf along the total-category arrow `(φ, 𝟙)` out of the degree-`n` object lying over `V`.

Read as a map of sheaves on the degree-`m` component, this is the *direct-image* transition
`restrictTransition`, landing in the pushforward along `f_φ`.  Its mate under the topos
adjunction of `f_φ` is the *inverse-image* transition `fiberTransition`, which is the form in
which the restrictions of a total-site sheaf constitute a system.

## Main definitions

* `CategoryTheory.Pseudofunctor.CoGrothendieck.ιNatTrans`: for a contravariant pseudofunctor,
  the natural family of Cartesian lifts of a base arrow, read as a natural transformation
  between the two fibre inclusions.
* `CategoryTheory.Grothendieck.ιNatTrans_app_comp_ι_map`: the covariant counterpart of
  `CoGrothendieck.ι_map_comp_ιNatTrans_app`, factoring an arbitrary arrow of a covariant
  Grothendieck construction as a Cartesian lift followed by an arrow inside a fibre.
* `CategoryTheory.SimplicialSiteSituation.continuousInclusionTransition`: that family for the
  total category of a simplicial site in case (A).
* `CategoryTheory.SimplicialSiteSituation.restrictTransition`: the direct-image transition.
* `CategoryTheory.SimplicialSiteSituation.fiberTransition`: the inverse-image transition.

## Main results

* `CategoryTheory.SimplicialSiteSituation.restrictTransition_inl_arrow` and
  `.restrictTransition_inr_arrow`: restriction along an arbitrary cross-fibre arrow of the total
  category factors through the transition, in each of the two cases.
* `CategoryTheory.SimplicialSiteSituation.fiberTransition_adj`: the mate of `fiberTransition`
  under the topos adjunction of `f_φ` is `restrictTransition`.

## Implementation notes

In case (A) the pushforward along `f_φ` is precomposition with the transition functor, so the
transition is the sheaf whiskered with the opposite of `continuousInclusionTransition`.  In case
(B) the pushforward is a right Kan extension along the opposite transition functor, so the
corresponding family of arrows — Mathlib's `CategoryTheory.Grothendieck.ιNatTrans` — is passed
through the Kan-extension adjunction; `restrictTransition_inr_app` undoes that passage on
sections.

The family of Cartesian lifts is built here for an arbitrary contravariant pseudofunctor rather
than for `totalPseudofunctor` directly, and this is what makes the construction go through.
Written at `C.totalPseudofunctor`, the category instance carried by an arrow of
`C.underlying.obj n` is not the instance on `C.totalPseudofunctor.obj ⟨op (op n)⟩` without
unfolding the semireducible `totalPseudofunctor`, which neither `rw` nor instance search will
do; stated for a general pseudofunctor the question does not arise, and the specialisation is
then a definitional type ascription.  What the general construction still needs is that
`CoGrothendieck.ι` and `Quiver.Hom.toLoc` be unfolded when an instance argument is compared:
the objects of `∫ᶜ F` appearing in its goals are spelled `(ι F R).obj x`, whose `.base` is `R`
only after unfolding, so the category instance on the fibre is carried by two different-looking
terms.  Marking exactly those two definitions `implicit_reducible` for this section is enough,
and is narrower than widening definitional equality for a whole declaration.

In case (B) the corresponding factorization is `Grothendieck.ιNatTrans_app_comp_ι_map`, proved
here because Mathlib does not state it.  Its proof goes through a composite of two literal
`Grothendieck.Hom.mk`s at explicitly spelled objects: in that spelling `Grothendieck.comp_base`,
`Grothendieck.comp_fiber` and `Functor.map_id` all apply, whereas on a goal whose objects are
written `(ι G X).obj d` no rewrite is motive-correct and only definitional unfolding would make
progress.  Stating the equation in that direction makes the residual cast proof-irrelevant.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor
open CategoryTheory.Bicategory Opposite

universe v₁ u₁ v₂ u₂ u

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

attribute [local simp] PrelaxFunctor.map₂_eqToHom
attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
attribute [local implicit_reducible] ι Quiver.Hom.toLoc

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂})

/-- The Cartesian lifts of a base arrow `f : R ⟶ S`, as a natural transformation between the
inclusions of the fibres over `R` and over `S`. -/
def ιNatTrans {R S : 𝒮} (f : R ⟶ S) :
    (F.map f.op.toLoc).toFunctor ⋙ ι F R ⟶ ι F S where
  app a := ⟨f, 𝟙 _⟩
  naturality a b g := by
    ext
    · exact (Category.id_comp f).trans (Category.comp_id f).symm
    · simp only [ι, Functor.comp_map, categoryStruct_comp_fiber, Category.id_comp,
        Functor.map_id]
      simp only [op_id, Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor, comp_obj,
        categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc, F.mapComp_id_right_inv_app,
        id_obj, Strict.rightUnitor_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Category.comp_id, eqToHom_naturality,
        Category.assoc, eqToHom_naturality_assoc, ← Cat.Hom₂.comp_app, Iso.inv_hom_id,
        Cat.Hom.toNatTrans_id, NatTrans.id_app, map_comp, F.mapComp_id_left_inv_app,
        Strict.leftUnitor_eqToIso, eqToHom_trans]
      have hid : (F.mapId (⟨op S⟩ : LocallyDiscrete 𝒮ᵒᵖ)).inv.toNatTrans.app b ≫
          (F.mapId (⟨op S⟩ : LocallyDiscrete 𝒮ᵒᵖ)).hom.toNatTrans.app b = 𝟙 b := by
        simp [← Cat.Hom₂.comp_app]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hid]
      simp

/-- An arrow inside the fibre over `R`, followed by a Cartesian lift of `f : R ⟶ S`, is the
arrow of the total category with base `f` and the given fibre component. -/
theorem ι_map_comp_ιNatTrans_app {R S : 𝒮} (f : R ⟶ S) {a : F.obj ⟨op S⟩} {x : F.obj ⟨op R⟩}
    (g : x ⟶ (F.map f.op.toLoc).toFunctor.obj a) :
    (ι F R).map g ≫ (ιNatTrans F f).app a =
      (⟨f, g⟩ : (ι F R).obj x ⟶ (ι F S).obj a) := by
  apply Hom.ext _ _ (Category.id_comp f)
  simp only [ι, ιNatTrans, categoryStruct_comp_fiber]
  simp [F.mapComp_id_right_inv_app, ← Cat.Hom₂.comp_app]

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace CategoryTheory.Grothendieck

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {G : 𝒞 ⥤ Cat.{v₂, u₂}}

/-- A Cartesian lift of a base arrow `u : X ⟶ Y`, followed by an arrow inside the fibre over `Y`,
is the arrow of the total category with base `u` and the given fibre component.

This is the covariant counterpart of
`CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_comp_ιNatTrans_app`. -/
theorem ιNatTrans_app_comp_ι_map {X Y : 𝒞} (u : X ⟶ Y) {d : G.obj X} {e : G.obj Y}
    (g : (G.map u).toFunctor.obj d ⟶ e) :
    (ιNatTrans u).app d ≫ (ι G Y).map g =
      (⟨u, g⟩ : (ι G X).obj d ⟶ (ι G Y).obj e) := by
  have hid : (G.map (𝟙 Y)).toFunctor.obj ((G.map u).toFunctor.obj d) =
      (G.map u).toFunctor.obj d := by
    simp
  have hmk : (⟨u, g⟩ : Hom (⟨X, d⟩ : Grothendieck G) ⟨Y, e⟩) =
      comp (X := ⟨X, d⟩) (Y := ⟨Y, (G.map u).toFunctor.obj d⟩) (Z := ⟨Y, e⟩)
        ⟨u, 𝟙 _⟩ ⟨𝟙 Y, eqToHom hid ≫ g⟩ := by
    refine ext _ _ (Category.comp_id u).symm ?_
    simp only [comp, Functor.map_id, Category.id_comp, eqToHom_trans_assoc]
  exact hmk.symm

end CategoryTheory.Grothendieck

namespace CategoryTheory

namespace SimplicialSiteSituation

/-- The arrows defining restriction across fibres in case (A): the arrow `(φ, 𝟙)` from the
degree-`n` object over `V` to the degree-`m` object `V`. -/
def continuousInclusionTransition (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.underlying.map φ).toFunctor ⋙ CoGrothendieck.ι C.totalPseudofunctor (op n) ⟶
      CoGrothendieck.ι C.totalPseudofunctor (op m) :=
  CoGrothendieck.ιNatTrans C.totalPseudofunctor φ.op

/-- The cross-fibre arrows of case (A) have base `φ` and identity fibre component. -/
@[simp] theorem continuousInclusionTransition_app (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (V : C.underlying.obj m) :
    (continuousInclusionTransition C φ).app V = ⟨φ.op, 𝟙 _⟩ := rfl

/-- The direct-image transition comparing the restrictions of a total-site sheaf to the
components of degrees `m` and `n`.  In case (B) it is obtained from the family of total-category
arrows through the universal property of the right Kan extension. -/
noncomputable def restrictTransition (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.restrict m ⟶ S.restrict n ⋙ (S.transitionMorphism φ).pushforward := by
  rcases S with ⟨C | C⟩
  · exact
      { app := fun F => ⟨whiskerRight (NatTrans.op (continuousInclusionTransition C φ)) F.obj⟩
        naturality := fun F G f => (sheafToPresheaf _ _).map_injective
          (NatTrans.ext (funext fun _ => (f.hom.naturality _).symm)) }
  · exact
      { app := fun F => ⟨((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv
          _ _ (whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            F.obj)⟩
        naturality := fun F G f => by
          apply (sheafToPresheaf _ _).map_injective
          change whiskerLeft (Grothendieck.ι C.underlying (op m)).op f.hom ≫
              _ = _ ≫ (C.underlying.map φ.op).toFunctor.op.ran.map
                (whiskerLeft (Grothendieck.ι C.underlying (op n)).op f.hom)
          apply Adjunction.homEquiv_naturality_left_square
          exact NatTrans.ext (funext fun _ => (f.hom.naturality _).symm) }

/-- In case (A), the transition on sections is restriction along `(φ, 𝟙)`. -/
@[simp] theorem restrictTransition_inl_app (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inl C⟩) (Type u)) (V : C.underlying.obj m) :
    ((restrictTransition ⟨Sum.inl C⟩ φ).app F).hom.app (op V) =
      F.obj.map ((continuousInclusionTransition C φ).app V).op := rfl

/-- In case (B), the Kan-extension mate on sections is restriction along `(φ, 𝟙)`. -/
@[simp] theorem restrictTransition_inr_app (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inr C⟩) (Type u))
    (U : C.underlying.obj (op n)) :
    ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
      ((restrictTransition ⟨Sum.inr C⟩ φ).app F).hom).app (op U) =
      F.obj.map ((Grothendieck.ιNatTrans φ.op).app U).op := by
  exact congrArg (fun t => t.app (op U))
    ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm_apply_apply
      _)

/-- Restricting along `g` and then along `f` is restriction along any `h` equal to `f ≫ g`. -/
private theorem map_op_comp_map_op_eq {D : Type*} [Category D] (P : Dᵒᵖ ⥤ Type*) {X Y Z : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h) :
    P.map g.op ≫ P.map f.op = P.map h.op := by
  rw [← P.map_comp, ← op_comp, hfg]

/-- **Stacks 09WF.** In case (A), restriction along an arbitrary cross-fibre arrow of the total
category is recovered from the transition. -/
theorem restrictTransition_inl_arrow (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inl C⟩) (Type u)) {U : C.underlying.obj n}
    {V : C.underlying.obj m} (f : U ⟶ (C.underlying.map φ).toFunctor.obj V) :
    ((restrictTransition ⟨Sum.inl C⟩ φ).app F).hom.app (op V) ≫
        F.obj.map ((CoGrothendieck.ι C.totalPseudofunctor (op n)).map f).op =
      F.obj.map (Quiver.Hom.op
        (⟨φ.op, f⟩ : (CoGrothendieck.ι C.totalPseudofunctor (op n)).obj U ⟶
          (CoGrothendieck.ι C.totalPseudofunctor (op m)).obj V)) :=
  map_op_comp_map_op_eq F.obj _ _ _
    (CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor φ.op f)

/-- **Stacks 09WF.** In case (B), restriction along an arbitrary cross-fibre arrow of the total
category is recovered from the Kan-extension mate. -/
theorem restrictTransition_inr_arrow (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inr C⟩) (Type u))
    {U : C.underlying.obj (op n)} {V : C.underlying.obj (op m)}
    (f : (C.underlying.map φ.op).toFunctor.obj U ⟶ V) :
    F.obj.map ((Grothendieck.ι C.underlying (op m)).map f).op ≫
        ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
          ((restrictTransition ⟨Sum.inr C⟩ φ).app F).hom).app (op U) =
      F.obj.map (Quiver.Hom.op (⟨φ.op, f⟩ : (Grothendieck.ι C.underlying (op n)).obj U ⟶
        (Grothendieck.ι C.underlying (op m)).obj V)) := by
  rw [restrictTransition_inr_app]
  exact map_op_comp_map_op_eq F.obj _ _ _ (Grothendieck.ιNatTrans_app_comp_ι_map φ.op f)

/-- **Stacks 09WF.** The inverse-image transition on the restrictions of a total-site sheaf: the
mate of `restrictTransition` under the topos adjunction of `f_φ`. -/
@[stacks 09WF "transition induced by total-site restriction"]
noncomputable def fiberTransition (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.restrict m ⋙ (S.transitionMorphism φ).inverseImage ⟶ S.restrict n where
  app F :=
    ((S.transitionMorphism φ).adj.homEquiv _ _).symm ((S.restrictTransition φ).app F)
  naturality F G α := by
    simpa only [Functor.comp_map] using
      (S.transitionMorphism φ).adj.homEquiv_naturality_right_square
        ((S.restrict m).map α)
        ((S.restrictTransition φ).app G)
        ((S.restrictTransition φ).app F)
        ((S.restrict n).map α)
        (by simpa only [Functor.comp_map] using (S.restrictTransition φ).naturality α)

/-- The mate of the inverse-image transition is the direct-image transition. -/
@[simp] theorem fiberTransition_adj (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf S.totalTopology (Type u)) :
    ((S.transitionMorphism φ).adj.homEquiv _ _) ((fiberTransition S φ).app F) =
      (S.restrictTransition φ).app F :=
  ((S.transitionMorphism φ).adj.homEquiv _ _).apply_symm_apply _

end SimplicialSiteSituation

end CategoryTheory

add_to_stacks 09WF "direct-image restriction transition"
  CategoryTheory.SimplicialSiteSituation.restrictTransition
add_to_stacks 09WF "cross-fibre restriction in case (A)"
  CategoryTheory.SimplicialSiteSituation.restrictTransition_inl_arrow
add_to_stacks 09WF "cross-fibre restriction in case (B)"
  CategoryTheory.SimplicialSiteSituation.restrictTransition_inr_arrow

end
