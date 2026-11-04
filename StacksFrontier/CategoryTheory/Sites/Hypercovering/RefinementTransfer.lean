module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoveringAndHomotopies.FibreProduct
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.RefinementConstruction

/-!
# The refinement of a simplicial object is carried along a functor preserving its limits

The refinement `K ×_{Hom(C[k], K_k)} Hom(C[k], Z)` of [Stacks, Tag 01GJ] is built from the
degreewise powers by the standard cosimplicial set `C[k]` and from a degreewise fibre product.
A functor `G` preserving those products and those fibre products therefore carries the refinement
of `K` by `u` to the refinement of `K ⋙ G` by `G u`.

## Main definitions

* `constSimplexPowerCompIso`: `Hom(C[k], T) ⋙ G ≅ Hom(C[k], G T)`.
* `refinementByCoveringCompIso`: the refinement commutes with `G`.

## Main results

* `whiskerRight_constSimplexPowerUnit_comp`: the unit of [Stacks, Tag 0B13] is carried to the
  unit.
* `whiskerRight_constSimplexPowerMap_comp`: the degreewise power of a morphism is carried to the
  degreewise power of its image.

## Implementation notes

The isomorphism of powers is the comparison morphism `Limits.piComparison` of the product in each
degree, which is an isomorphism exactly because `G` preserves that product. Everything about it is
stated through `constSimplexPowerProj`, the coordinate of a power at its own stated type: a degree
of a power is the product it is built from only definitionally, so a statement spelled with
`Limits.Pi.π` cannot be rewritten against one spelled with the structure maps of the power.

That the unit is carried to the unit is not computed: both morphisms have the same coordinate at
the identity of `⦋k⦌` in degree `k`, namely the identity, and
`bijective_comp_constSimplexPowerUnit` -- the adjunction of [Stacks, Tag 0B13] -- says that this
determines them.

The refinement itself is carried across through `IsPullback`: the degreewise fibre product is a
fibre product in the category of simplicial objects (`Limits.isPullback_pointwisePullback`),
post-composition with `G` preserves it, and the two cospans are identified by the isomorphism of
powers. `IsPullback.isoIsPullback` then compares the two points.
-/

@[expose] public section

universe w v₂ u₂ v u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Stacks.CategoryTheory.Hypercovering

/- As in `RefinementConstruction`: a degree of a power is the product it is built from only at
default transparency. -/
attribute [local implicit_reducible] CategoryTheory.SimplicialObject.power

variable {E : Type u} [Category.{v} E] {E' : Type u₂} [Category.{v₂} E'] (G : E ⥤ E')

section Power

variable (T : E) (k : ℕ)
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => T]
  [∀ m : SimplexCategoryᵒᵖ,
    HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => G.obj T]
  [∀ m : SimplexCategoryᵒᵖ,
    PreservesLimit (Discrete.functor fun _ : (simplexPowerIndex.{w} k).obj m.unop => T) G]

/-- The degreewise comparison between the image of the power and the power of the image: the
comparison morphism of the product in that degree. -/
noncomputable def constSimplexPowerCompIsoApp (n : ℕ) :
    G.obj ((constSimplexPower.{w} T k).obj (Opposite.op (SimplexCategory.mk n))) ≅
      (constSimplexPower.{w} (G.obj T) k).obj (Opposite.op (SimplexCategory.mk n)) :=
  PreservesProduct.iso G fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n) => T

/-- The coordinates of `constSimplexPowerCompIsoApp`: its coordinate at `α` is the image under
`G` of the coordinate at `α`. -/
@[reassoc]
theorem constSimplexPowerCompIsoApp_hom_comp_proj (n : ℕ)
    (α : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n)) :
    (constSimplexPowerCompIsoApp.{w} G T k n).hom ≫ constSimplexPowerProj (G.obj T) k n α =
      G.map (constSimplexPowerProj T k n α) := by
  change (PreservesProduct.iso G fun _ : (simplexPowerIndex.{w} k).obj
      (SimplexCategory.mk n) => T).hom ≫
      Pi.π (fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n) => G.obj T) α =
    G.map (Pi.π (fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n) => T) α)
  rw [PreservesProduct.iso_hom, piComparison_comp_π]

/-- The degreewise comparisons assemble into a morphism of simplicial objects. -/
noncomputable def constSimplexPowerCompHom :
    constSimplexPower.{w} T k ⋙ G ⟶ constSimplexPower.{w} (G.obj T) k where
  app m := (constSimplexPowerCompIsoApp.{w} G T k m.unop.len).hom
  naturality := by
    rintro ⟨m⟩ ⟨m'⟩ ⟨φ⟩
    obtain ⟨m⟩ := m
    obtain ⟨m'⟩ := m'
    refine (bijective_comp_constSimplexPowerProj.{w} (G.obj T) k m' _).1 (funext fun α => ?_)
    dsimp only
    rw [Category.assoc, Category.assoc, constSimplexPowerCompIsoApp_hom_comp_proj,
      Functor.comp_map, ← G.map_comp, constSimplexPowerProj_naturality_op,
      constSimplexPowerProj_naturality_op, constSimplexPowerCompIsoApp_hom_comp_proj]

/-- `constSimplexPowerCompHom` is an isomorphism: it is one in every degree. -/
instance isIso_constSimplexPowerCompHom :
    IsIso (constSimplexPowerCompHom.{w} G T k) := by
  have : ∀ m : SimplexCategoryᵒᵖ, IsIso ((constSimplexPowerCompHom.{w} G T k).app m) :=
    fun m => inferInstanceAs
      (IsIso (constSimplexPowerCompIsoApp.{w} G T k m.unop.len).hom)
  exact NatIso.isIso_of_isIso_app _

/-- **The power by `C[k]` commutes with a functor preserving it.** -/
noncomputable def constSimplexPowerCompIso :
    constSimplexPower.{w} T k ⋙ G ≅ constSimplexPower.{w} (G.obj T) k :=
  asIso (constSimplexPowerCompHom.{w} G T k)

/-- The coordinates of `constSimplexPowerCompIso`. -/
@[reassoc]
theorem constSimplexPowerCompIso_hom_app_comp_proj (n : ℕ)
    (α : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n)) :
    (constSimplexPowerCompIso.{w} G T k).hom.app (Opposite.op (SimplexCategory.mk n)) ≫
        constSimplexPowerProj (G.obj T) k n α =
      G.map (constSimplexPowerProj T k n α) :=
  constSimplexPowerCompIsoApp_hom_comp_proj.{w} G T k n α

end Power

/-- The products that a power over a composite functor is built from are the products over the
composite's value: `(K ⋙ G)_d` is `G(K_d)`, but only after `Functor.comp` is unfolded, which
instance search does not do. -/
instance hasProduct_simplexPowerIndex_comp_obj {K : SimplicialObject E} {G : E ⥤ E'} (k : ℕ)
    (d m : SimplexCategoryᵒᵖ)
    [HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => G.obj (K.obj d)] :
    HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => (K ⋙ G).obj d :=
  inferInstanceAs
    (HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => G.obj (K.obj d))

section PowerMap

variable {Y Z : E} (u : Z ⟶ Y) (k : ℕ)
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Y]
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Z]
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => G.obj Y]
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => G.obj Z]
  [∀ m : SimplexCategoryᵒᵖ,
    PreservesLimit (Discrete.functor fun _ : (simplexPowerIndex.{w} k).obj m.unop => Y) G]
  [∀ m : SimplexCategoryᵒᵖ,
    PreservesLimit (Discrete.functor fun _ : (simplexPowerIndex.{w} k).obj m.unop => Z) G]

/-- **The degreewise power of a morphism is carried to the degreewise power of its image.** -/
theorem whiskerRight_constSimplexPowerMap_comp :
    Functor.whiskerRight (constSimplexPowerMap.{w} u k) G ≫
        (constSimplexPowerCompIso.{w} G Y k).hom =
      (constSimplexPowerCompIso.{w} G Z k).hom ≫ constSimplexPowerMap.{w} (G.map u) k := by
  refine NatTrans.ext (funext fun m => ?_)
  obtain ⟨m⟩ := m
  obtain ⟨n⟩ := m
  refine (bijective_comp_constSimplexPowerProj.{w} (G.obj Y) k n _).1 (funext fun α => ?_)
  dsimp only
  rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc, Category.assoc,
    constSimplexPowerCompIso_hom_app_comp_proj, Functor.whiskerRight_app, ← G.map_comp,
    constSimplexPowerMap_app_comp_proj, G.map_comp, constSimplexPowerMap_app_comp_proj,
    ← Category.assoc, constSimplexPowerCompIso_hom_app_comp_proj]

end PowerMap

section Transfer

variable (K : SimplicialObject E) (k : ℕ) {Z : E}
  (u : Z ⟶ K.obj (Opposite.op (SimplexCategory.mk k)))
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop =>
    K.obj (Opposite.op (SimplexCategory.mk k))]
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Z]
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop =>
    G.obj (K.obj (Opposite.op (SimplexCategory.mk k)))]
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => G.obj Z]
  [∀ m : SimplexCategoryᵒᵖ, PreservesLimit (Discrete.functor
    fun _ : (simplexPowerIndex.{w} k).obj m.unop =>
      K.obj (Opposite.op (SimplexCategory.mk k))) G]
  [∀ m : SimplexCategoryᵒᵖ,
    PreservesLimit (Discrete.functor fun _ : (simplexPowerIndex.{w} k).obj m.unop => Z) G]

/-- **The unit of [Stacks, Tag 0B13] is carried to the unit.** Both morphisms have coordinate the
identity at the identity of `⦋k⦌` in degree `k`, and that determines them. -/
theorem whiskerRight_constSimplexPowerUnit_comp :
    Functor.whiskerRight (constSimplexPowerUnit.{w} K k) G ≫
        (constSimplexPowerCompIso.{w} G (K.obj (Opposite.op (SimplexCategory.mk k))) k).hom =
      constSimplexPowerUnit.{w} (K ⋙ G) k := by
  refine (bijective_comp_constSimplexPowerUnit.{w} (K ⋙ G) k (K ⋙ G)).1 ?_
  refine Eq.trans ?_ (constSimplexPowerUnit_app_comp_proj.{w} (K ⋙ G) k).symm
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun q => G.map ((constSimplexPowerUnit.{w} K k).app
      (Opposite.op (SimplexCategory.mk k))) ≫ q)
    (constSimplexPowerCompIso_hom_app_comp_proj.{w} G
      (K.obj (Opposite.op (SimplexCategory.mk k))) k k
      (ULift.up (𝟙 (SimplexCategory.mk k))))).trans ?_
  exact ((G.map_comp _ _).symm.trans
    (congrArg G.map (constSimplexPowerUnit_app_comp_proj.{w} K k))).trans (G.map_id _)

variable [HasPullbacks E] [HasPullbacks E'] [PreservesLimitsOfShape WalkingCospan G]

/-- **The refinement of a simplicial object by a morphism in one degree commutes with a functor
preserving the powers and the fibre products.** -/
noncomputable def refinementByCoveringCompIso :
    refinementByCovering.{w} K k u ⋙ G ≅ refinementByCovering.{w} (K ⋙ G) k (G.map u) :=
  ((isPullback_pointwisePullback (constSimplexPowerUnit.{w} K k)
        (constSimplexPowerMap.{w} u k)).map ((Functor.whiskeringRight _ _ _).obj G)).of_iso
      (Iso.refl _) (Iso.refl _) (constSimplexPowerCompIso.{w} G Z k)
      (constSimplexPowerCompIso.{w} G (K.obj (Opposite.op (SimplexCategory.mk k))) k)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.id_comp _).symm
      ((whiskerRight_constSimplexPowerUnit_comp.{w} G K k).trans (Category.id_comp _).symm)
      (whiskerRight_constSimplexPowerMap_comp.{w} G u k)
    |>.isoIsPullback _ _
      (isPullback_pointwisePullback (constSimplexPowerUnit.{w} (K ⋙ G) k)
        (constSimplexPowerMap.{w} (G.map u) k))

end Transfer

end Stacks.CategoryTheory.Hypercovering

end
