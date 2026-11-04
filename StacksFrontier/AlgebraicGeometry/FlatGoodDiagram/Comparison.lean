module

public import StacksFrontier.AlgebraicGeometry.Existence.Basic

/-!
# The algebra of morphisms of image systems

A `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt` is a morphism of the inverse systems of
scheme-theoretic images attached to two good diagrams. This file gives that notion its identity,
its composition and its restriction to a later tail.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.restrict'`: restriction of a morphism
  of image systems to the stages above a later index.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.id'`: the identity morphism of the
  image system of one good diagram, inducing `𝟙 X` on the limits.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.comp'`: composition.

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ofCompId` and `ofIdComp`: a morphism of
  image systems inducing `f ≫ 𝟙 Y` or `𝟙 X ≫ f` read as one inducing `f`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem'`: the image systems
  of two good diagrams for the same morphism are isomorphic at every sufficiently late stage.
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison'`: these
  comparisons commute eventually with morphisms of image systems inducing the same morphism.

## Implementation notes

`restrict'`, `id'` and `comp'` take their good diagrams and their morphism of schemes as implicit
arguments; `MorphismAt.restrict`, `MorphismAt.id` and `MorphismAt.comp` take the same data
explicitly.

The functor `Over.map (homOfLE (hX.trans k)).op` and the composite
`Over.map (homOfLE k).op ⋙ Over.map (homOfLE hX).op` agree definitionally on objects and on
morphisms, since any two morphisms of a preorder category are equal by proof irrelevance and
structure eta; so `restrict_maps_app'` holds by `rfl`. The lemmas `over_map_obj_trans` and
`over_map_map_trans` state this equality for use in rewriting.

The index type lives in a universe `v` independent of the scheme universe `u`, and no smallness
hypothesis is needed.

## References

* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR), whose `MorphismAt` this
  file manipulates.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace MorphismAt

variable {X Y Z : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
  {pZ : Z ⟶ D.limitScheme}

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Restricting a stage along a later index: the two spellings of the structure morphism of a
stage of the tail above `i₁` seen as a stage of the tail above `k ≤ i₀ ≤ i₁`. -/
public lemma over_map_obj_trans {i₀ i₁ k : I} (h : k ≤ i₀) (l : i₀ ≤ i₁) (j : Over (op i₁)) :
    (Over.map (homOfLE (h.trans l)).op).obj j =
      (Over.map (homOfLE h).op).obj ((Over.map (homOfLE l).op).obj j) :=
  CostructuredArrow.obj_ext _ _ rfl (Subsingleton.elim _ _)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Restricting a transition along a later index. -/
public lemma over_map_map_trans {i₀ i₁ k : I} (h : k ≤ i₀) (l : i₀ ≤ i₁)
    {j j' : Over (op i₁)} (a : j ⟶ j') :
    (Over.map (homOfLE (h.trans l)).op).map a =
      (Over.map (homOfLE h).op).map ((Over.map (homOfLE l).op).map a) :=
  CostructuredArrow.hom_ext _ _ rfl

/-- A morphism of image systems defined on the stages above `i₀` restricts to the stages above
any later index. -/
public noncomputable def restrict' {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ i₁ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀} (k : i₀ ≤ i₁)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    MorphismAt D f GX GY i₁ (hX.trans k) (hY.trans k) where
  maps :=
    { app j := F.maps.app ((Over.map (homOfLE k).op).obj j)
      naturality _ _ a := F.maps.naturality ((Over.map (homOfLE k).op).map a) }
  over_base j := F.over_base ((Over.map (homOfLE k).op).obj j)
  induces j := F.induces ((Over.map (homOfLE k).op).obj j)

/-- The components of `F.restrict' k` are those of `F` at the corresponding earlier stages. -/
@[simp]
public lemma restrict_maps_app' {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ i₁ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀} (k : i₀ ≤ i₁)
    (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₁)) :
    (F.restrict' k).maps.app j = F.maps.app ((Over.map (homOfLE k).op).obj j) :=
  rfl

/-- The identity morphism of the image system of one good diagram, as a morphism of image
systems inducing `𝟙 X` on the limits. -/
public noncomputable def id' (G : GoodDiagram D pX) (i₀ : I) (h : G.index ≤ i₀) :
    MorphismAt D (𝟙 X) G G i₀ h h where
  maps := 𝟙 _
  over_base _ := Category.id_comp _
  induces _ := (Category.comp_id _).trans (Category.id_comp _).symm

/-- Every component of `MorphismAt.id' G i₀ h` is an identity. -/
@[simp]
public lemma id_maps_app' (G : GoodDiagram D pX) (i₀ : I) (h : G.index ≤ i₀)
    (j : Over (op i₀)) : (MorphismAt.id' G i₀ h).maps.app j = 𝟙 _ :=
  rfl

/-- Composition of morphisms of image systems. -/
public noncomputable def comp' {f : X ⟶ Y} {g : Y ⟶ Z} {GX : GoodDiagram D pX}
    {GY : GoodDiagram D pY} {GZ : GoodDiagram D pZ} {i₀ : I} {hX : GX.index ≤ i₀}
    {hY : GY.index ≤ i₀} {hZ : GZ.index ≤ i₀} (F : MorphismAt D f GX GY i₀ hX hY)
    (G : MorphismAt D g GY GZ i₀ hY hZ) :
    MorphismAt D (f ≫ g) GX GZ i₀ hX hZ where
  maps := F.maps ≫ G.maps
  over_base j := by
    rw [NatTrans.comp_app, Category.assoc]
    exact (congrArg (F.maps.app j ≫ ·) (G.over_base j)).trans (F.over_base j)
  induces j :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.maps.app j) (F.induces j)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (f ≫ ·) (G.induces j)).trans (Category.assoc _ _ _).symm)))

/-- The components of `F.comp' G` are the composites of the components of `F` and `G`. -/
@[simp]
public lemma comp_maps_app' {f : X ⟶ Y} {g : Y ⟶ Z} {GX : GoodDiagram D pX}
    {GY : GoodDiagram D pY} {GZ : GoodDiagram D pZ} {i₀ : I} {hX : GX.index ≤ i₀}
    {hY : GY.index ≤ i₀} {hZ : GZ.index ≤ i₀} (F : MorphismAt D f GX GY i₀ hX hY)
    (G : MorphismAt D g GY GZ i₀ hY hZ) (j : Over (op i₀)) :
    (F.comp' G).maps.app j = F.maps.app j ≫ G.maps.app j :=
  rfl

/-- A morphism of image systems inducing `f ≫ 𝟙 Y` is one inducing `f`. -/
public noncomputable def ofCompId {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}
    (F : MorphismAt D (f ≫ 𝟙 Y) GX GY i₀ hX hY) : MorphismAt D f GX GY i₀ hX hY where
  maps := F.maps
  over_base := F.over_base
  induces j := (F.induces j).trans (congrArg (· ≫ _) (Category.comp_id f))

/-- `F.ofCompId` has the same underlying natural transformation as `F`. -/
@[simp]
public lemma ofCompId_maps {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}
    (F : MorphismAt D (f ≫ 𝟙 Y) GX GY i₀ hX hY) : F.ofCompId.maps = F.maps :=
  rfl

/-- A morphism of image systems inducing `𝟙 X ≫ f` is one inducing `f`. -/
public noncomputable def ofIdComp {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}
    (F : MorphismAt D (𝟙 X ≫ f) GX GY i₀ hX hY) : MorphismAt D f GX GY i₀ hX hY where
  maps := F.maps
  over_base := F.over_base
  induces j := (F.induces j).trans (congrArg (· ≫ _) (Category.id_comp f))

/-- `F.ofIdComp` has the same underlying natural transformation as `F`. -/
@[simp]
public lemma ofIdComp_maps {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}
    (F : MorphismAt D (𝟙 X ≫ f) GX GY i₀ hX hY) : F.ofIdComp.maps = F.maps :=
  rfl

end MorphismAt

/-- The inverse systems of scheme-theoretic images attached to two good diagrams for the same
morphism `X ⟶ S` are isomorphic at every stage above some index, by a pair of mutually inverse
morphisms of systems inducing `𝟙 X` on the limits. -/
public theorem exists_eventual_iso_imageSystem' (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} (p : X ⟶ D.limitScheme) (G₁ G₂ : GoodDiagram D p) :
    ∃ (i₀ : I) (h₁ : G₁.index ≤ i₀) (h₂ : G₂.index ≤ i₀)
      (F : MorphismAt D (𝟙 X) G₁ G₂ i₀ h₁ h₂)
      (G : MorphismAt D (𝟙 X) G₂ G₁ i₀ h₂ h₁),
      ∀ j : Over (op i₀),
        F.maps.app j ≫ G.maps.app j = 𝟙 _ ∧ G.maps.app j ≫ F.maps.app j = 𝟙 _ := by
  obtain ⟨iF, hF₁, hF₂, ⟨F₀⟩⟩ :=
    exists_morphismAt_of_dominant D (𝟙 X) (Category.id_comp p) G₁ G₂
  obtain ⟨iG, hG₂, hG₁, ⟨G₀⟩⟩ :=
    exists_morphismAt_of_dominant D (𝟙 X) (Category.id_comp p) G₂ G₁
  obtain ⟨i₀, kF, kG⟩ := exists_ge_ge iF iG
  have h₁ : G₁.index ≤ i₀ := hF₁.trans kF
  have h₂ : G₂.index ≤ i₀ := hF₂.trans kF
  let F : MorphismAt D (𝟙 X) G₁ G₂ i₀ h₁ h₂ := F₀.restrict' kF
  let G : MorphismAt D (𝟙 X) G₂ G₁ i₀ h₂ h₁ := G₀.restrict' kG
  obtain ⟨i₃F, k₃F, hEqF⟩ :=
    MorphismAt.eventually_eq_morphismAt_of_dominant (F.comp' G).ofCompId
      (MorphismAt.id' G₁ i₀ h₁)
  obtain ⟨i₃G, k₃G, hEqG⟩ :=
    MorphismAt.eventually_eq_morphismAt_of_dominant (G.comp' F).ofCompId
      (MorphismAt.id' G₂ i₀ h₂)
  obtain ⟨i₄, kF₄, kG₄⟩ := exists_ge_ge i₃F i₃G
  have k₄ : i₀ ≤ i₄ := k₃F.trans kF₄
  refine ⟨i₄, h₁.trans k₄, h₂.trans k₄, F.restrict' k₄, G.restrict' k₄, fun j => ?_⟩
  have hj : i₄ ≤ unop ((Over.map (homOfLE k₄).op).obj j).left := leOfHom j.hom.unop
  exact ⟨hEqF _ (kF₄.trans hj), hEqG _ (kG₄.trans hj)⟩

/-- The comparison between the image systems of two choices of good diagram commutes, at every
sufficiently late stage, with any morphisms of image systems `H₁` and `H₂` inducing the same
morphism of schemes `f`. -/
public theorem eventually_natural_imageSystem_comparison' (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme} (f : X ⟶ Y)
    {GX₁ GX₂ : GoodDiagram D pX} {GY₁ GY₂ : GoodDiagram D pY}
    {i₀ : I} {hX₁ : GX₁.index ≤ i₀} {hX₂ : GX₂.index ≤ i₀}
    {hY₁ : GY₁.index ≤ i₀} {hY₂ : GY₂.index ≤ i₀}
    (FX : MorphismAt D (𝟙 X) GX₁ GX₂ i₀ hX₁ hX₂)
    (FY : MorphismAt D (𝟙 Y) GY₁ GY₂ i₀ hY₁ hY₂)
    (H₁ : MorphismAt D f GX₁ GY₁ i₀ hX₁ hY₁)
    (H₂ : MorphismAt D f GX₂ GY₂ i₀ hX₂ hY₂) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ j : Over (op i₀), i₃ ≤ unop j.left →
        H₁.maps.app j ≫ FY.maps.app j = FX.maps.app j ≫ H₂.maps.app j :=
  MorphismAt.eventually_eq_morphismAt_of_dominant (H₁.comp' FY).ofCompId
    (FX.comp' H₂).ofIdComp

end AlgebraicGeometry.LimitNoetherianSituation
