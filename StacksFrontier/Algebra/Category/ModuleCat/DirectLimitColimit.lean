module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Presentable.Directed

/-!
# `Module.DirectLimit` as the categorical colimit in `ModuleCat R`

`Mathlib.Algebra.Category.ModuleCat.Limits` records that the cocone `ModuleCat.directLimitCocone
G f`, whose vertex is `ModuleCat.of R (Module.DirectLimit G f)`, is a colimit of the diagram
`ModuleCat.directLimitDiagram G f`: that is `ModuleCat.directLimitIsColimit`. This file gives
the comparison between the categorical colimit and `Module.DirectLimit`, for diagrams indexed by
a preorder and, along a final functor, by a small filtered category.

## Main definitions

* `ModuleCat.colimitDirectLimitIso`: the isomorphism
  `colimit (directLimitDiagram G f) ≅ ModuleCat.of R (Module.DirectLimit G f)`, with `simp`
  lemmas computing both directions on `Module.DirectLimit.of` and on `colimit.ι`.
* `ModuleCat.isColimitOfLinearEquiv` and `ModuleCat.linearEquivOfIsColimit`: a cocone on
  `directLimitDiagram G f` is a colimit exactly when its vertex is linearly equivalent to
  `Module.DirectLimit G f` compatibly with the canonical maps `Module.DirectLimit.of`.
* `ModuleCat.isColimitOfPreorder` and `ModuleCat.linearEquivOfIsColimitOfPreorder`: the same
  for an arbitrary functor out of a preorder, whose underlying directed system is provided by
  the instance `ModuleCat.directedSystem_functorMap`.
* `ModuleCat.isColimitOfFinal` and `ModuleCat.linearEquivOfFinal`: along a final functor
  `F : ι ⥤ J` out of a preorder, a colimit of `D : J ⥤ ModuleCat R` is the direct limit of the
  directed system `F ⋙ D`.
* `ModuleCat.exists_directed_linearEquiv_of_isFiltered`: the consequence, for a small filtered
  index category — the vertex of any colimit cocone is the direct limit of a directed system
  indexed by a nonempty directed partial order, reindexing the given diagram along a final
  functor.

## Implementation notes

A functor `D` out of a preorder *is* the `directLimitDiagram` of its own underlying directed
system, by `rfl` (`ModuleCat.directLimitDiagram_functorMap`): the objects agree by structure
eta and the maps because `homOfLE h.le = h` by proof irrelevance. So the statements about a
general `D` are the statements about `directLimitDiagram` and are proved by `exact` after
naming `G` and `f` explicitly. The equality is far too deep for `rw` or `simp` to act on, and
higher-order unification cannot discover `G` and `f` from `D`, which is why they are supplied
by name rather than left to be inferred.

The final-functor results need no directedness: `Module.DirectLimit` is a quotient of a direct
sum and so computes the colimit over an arbitrary preorder. Directedness enters only through
`CategoryTheory.IsFiltered.exists_directed`, which is what produces the index of
`ModuleCat.exists_directed_linearEquiv_of_isFiltered`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] {ι : Type v} [Preorder ι]

section DirectLimit

variable (G : ι → Type v) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h ↦ f i j h]

/-- The diagram `ModuleCat.directLimitDiagram G f` has a colimit. -/
instance hasColimit_directLimitDiagram : HasColimit (directLimitDiagram G f) := by
  classical exact ⟨_, directLimitIsColimit G f⟩

variable [DecidableEq ι]

/-- The colimit of `ModuleCat.directLimitDiagram G f` is `Module.DirectLimit G f`. -/
def colimitDirectLimitIso :
    colimit (directLimitDiagram G f) ≅ of R (Module.DirectLimit G f) :=
  colimit.isoColimitCocone ⟨directLimitCocone G f, directLimitIsColimit G f⟩

/-- The composite of `colimit.ι` with `ModuleCat.colimitDirectLimitIso` is the canonical map
`Module.DirectLimit.of`. -/
@[reassoc (attr := simp)]
lemma ι_colimitDirectLimitIso_hom (i : ι) :
    colimit.ι (directLimitDiagram G f) i ≫ (colimitDirectLimitIso G f).hom =
      ofHom (Module.DirectLimit.of R ι G f i) :=
  colimit.isoColimitCocone_ι_hom _ i

/-- The composite of the canonical map `Module.DirectLimit.of` with the inverse of
`ModuleCat.colimitDirectLimitIso` is `colimit.ι`. -/
@[reassoc (attr := simp)]
lemma ofHom_of_comp_colimitDirectLimitIso_inv (i : ι) :
    ofHom (Module.DirectLimit.of R ι G f i) ≫ (colimitDirectLimitIso G f).inv =
      colimit.ι (directLimitDiagram G f) i :=
  colimit.isoColimitCocone_ι_inv ⟨directLimitCocone G f, directLimitIsColimit G f⟩ i

/-- `ModuleCat.colimitDirectLimitIso` sends `colimit.ι _ i x` to
`Module.DirectLimit.of R ι G f i x`. -/
@[simp]
lemma colimitDirectLimitIso_hom_apply (i : ι) (x : G i) :
    (colimitDirectLimitIso G f).hom (colimit.ι (directLimitDiagram G f) i x) =
      Module.DirectLimit.of R ι G f i x :=
  ConcreteCategory.congr_hom (ι_colimitDirectLimitIso_hom G f i) x

/-- The inverse of `ModuleCat.colimitDirectLimitIso` sends `Module.DirectLimit.of R ι G f i x` to
`colimit.ι _ i x`. -/
@[simp]
lemma colimitDirectLimitIso_inv_apply (i : ι) (x : G i) :
    (colimitDirectLimitIso G f).inv (Module.DirectLimit.of R ι G f i x) =
      colimit.ι (directLimitDiagram G f) i x :=
  ConcreteCategory.congr_hom (ofHom_of_comp_colimitDirectLimitIso_inv G f i) x

variable {G f} {c : Cocone (directLimitDiagram G f)}

/-- A cocone on `ModuleCat.directLimitDiagram G f` is a colimit as soon as its vertex is
linearly equivalent to `Module.DirectLimit G f` compatibly with the canonical maps
`Module.DirectLimit.of`. -/
def isColimitOfLinearEquiv (e : Module.DirectLimit G f ≃ₗ[R] c.pt)
    (he : ∀ (i : ι) (x : G i), e (Module.DirectLimit.of R ι G f i x) = c.ι.app i x) :
    IsColimit c :=
  IsColimit.ofIsoColimit (directLimitIsColimit G f)
    (Cocone.ext (LinearEquiv.toModuleIso e) fun i ↦ by ext x; exact he i x)

/-- The vertex of a colimit cocone on `ModuleCat.directLimitDiagram G f` is linearly
equivalent to `Module.DirectLimit G f`. -/
def linearEquivOfIsColimit (hc : IsColimit c) : Module.DirectLimit G f ≃ₗ[R] c.pt :=
  ((directLimitIsColimit G f).coconePointUniqueUpToIso hc).toLinearEquiv

/-- `ModuleCat.linearEquivOfIsColimit hc` sends `Module.DirectLimit.of R ι G f i x` to
`c.ι.app i x`. -/
@[simp]
lemma linearEquivOfIsColimit_of (hc : IsColimit c) (i : ι) (x : G i) :
    linearEquivOfIsColimit hc (Module.DirectLimit.of R ι G f i x) = c.ι.app i x :=
  ConcreteCategory.congr_hom
    ((directLimitIsColimit G f).comp_coconePointUniqueUpToIso_hom hc i) x

/-- The inverse of `ModuleCat.linearEquivOfIsColimit hc` sends `c.ι.app i x` to
`Module.DirectLimit.of R ι G f i x`. -/
lemma linearEquivOfIsColimit_symm_ι_app (hc : IsColimit c) (i : ι) (x : G i) :
    (linearEquivOfIsColimit hc).symm (c.ι.app i x) = Module.DirectLimit.of R ι G f i x :=
  (linearEquivOfIsColimit hc).injective (by simp)

end DirectLimit

section Preorder

variable (D : ι ⥤ ModuleCat.{v} R)

/-- The directed system of modules underlying a functor out of a preorder. -/
instance directedSystem_functorMap :
    DirectedSystem (fun i ↦ (D.obj i : Type v)) fun _ _ h ↦ (D.map (homOfLE h)).hom where
  map_self := by intro _ x; simp
  map_map := by
    intro _ _ _ hij hjk x
    rw [← ModuleCat.comp_apply, ← D.map_comp, homOfLE_comp]

/-- A functor out of a preorder *is* the `ModuleCat.directLimitDiagram` of its own underlying
directed system. -/
lemma directLimitDiagram_functorMap :
    directLimitDiagram (fun i ↦ (D.obj i : Type v))
      (fun _ _ h ↦ (D.map (homOfLE h)).hom) = D :=
  rfl

variable [DecidableEq ι] {D} {c : Cocone D}

/-- A cocone on a functor `D` out of a preorder is a colimit as soon as its vertex is linearly
equivalent to the direct limit of the directed system underlying `D`, compatibly with the
canonical maps. -/
def isColimitOfPreorder
    (e : Module.DirectLimit (fun i ↦ (D.obj i : Type v))
      (fun _ _ h ↦ (D.map (homOfLE h)).hom) ≃ₗ[R] c.pt)
    (he : ∀ (i : ι) (x : D.obj i),
      e (Module.DirectLimit.of R ι _ (fun _ _ h ↦ (D.map (homOfLE h)).hom) i x) =
        c.ι.app i x) :
    IsColimit c :=
  isColimitOfLinearEquiv (G := fun i ↦ (D.obj i : Type v))
    (f := fun _ _ h ↦ (D.map (homOfLE h)).hom) (c := c) e he

/-- The vertex of a colimit cocone on a functor `D` out of a preorder is linearly equivalent
to the direct limit of the directed system underlying `D`. -/
def linearEquivOfIsColimitOfPreorder (hc : IsColimit c) :
    Module.DirectLimit (fun i ↦ (D.obj i : Type v))
      (fun _ _ h ↦ (D.map (homOfLE h)).hom) ≃ₗ[R] c.pt :=
  linearEquivOfIsColimit (G := fun i ↦ (D.obj i : Type v))
    (f := fun _ _ h ↦ (D.map (homOfLE h)).hom) (c := c) hc

/-- `ModuleCat.linearEquivOfIsColimitOfPreorder hc` sends the image of `x : D.obj i` under
`Module.DirectLimit.of` to `c.ι.app i x`. -/
@[simp]
lemma linearEquivOfIsColimitOfPreorder_of (hc : IsColimit c) (i : ι) (x : D.obj i) :
    linearEquivOfIsColimitOfPreorder hc
        (Module.DirectLimit.of R ι _ (fun _ _ h ↦ (D.map (homOfLE h)).hom) i x) =
      c.ι.app i x :=
  linearEquivOfIsColimit_of (G := fun i ↦ (D.obj i : Type v))
    (f := fun _ _ h ↦ (D.map (homOfLE h)).hom) (c := c) hc i x

end Preorder

section Final

variable {J : Type v} [SmallCategory J] [DecidableEq ι] (F : ι ⥤ J) [F.Final]
  (D : J ⥤ ModuleCat.{v} R)

/-- **A colimit over a filtered index is a directed colimit.** Along a final functor
`F : ι ⥤ J` out of a preorder, a cocone on `D : J ⥤ ModuleCat R` is a colimit as soon as its
vertex is the direct limit of the directed system `F ⋙ D`, compatibly with the canonical
maps. -/
def isColimitOfFinal {c : Cocone D}
    (e : Module.DirectLimit (fun i ↦ ((F ⋙ D).obj i : Type v))
      (fun _ _ h ↦ ((F ⋙ D).map (homOfLE h)).hom) ≃ₗ[R] c.pt)
    (he : ∀ (i : ι) (x : (F ⋙ D).obj i),
      e (Module.DirectLimit.of R ι _ (fun _ _ h ↦ ((F ⋙ D).map (homOfLE h)).hom) i x) =
        c.ι.app (F.obj i) x) :
    IsColimit c :=
  Functor.Final.isColimitWhiskerEquiv F c
    (isColimitOfPreorder (D := F ⋙ D) (c := c.whisker F) e he)

/-- Along a final functor `F : ι ⥤ J` out of a preorder, the vertex of a colimit cocone on
`D : J ⥤ ModuleCat R` is the direct limit of the directed system `F ⋙ D`. -/
def linearEquivOfFinal {c : Cocone D} (hc : IsColimit c) :
    Module.DirectLimit (fun i ↦ ((F ⋙ D).obj i : Type v))
      (fun _ _ h ↦ ((F ⋙ D).map (homOfLE h)).hom) ≃ₗ[R] c.pt :=
  linearEquivOfIsColimitOfPreorder (D := F ⋙ D) (c := c.whisker F)
    ((Functor.Final.isColimitWhiskerEquiv F c).symm hc)

/-- `ModuleCat.linearEquivOfFinal F D hc` sends the image of `x : (F ⋙ D).obj i` under
`Module.DirectLimit.of` to `c.ι.app (F.obj i) x`. -/
lemma linearEquivOfFinal_of {c : Cocone D} (hc : IsColimit c) (i : ι) (x : (F ⋙ D).obj i) :
    linearEquivOfFinal F D hc
        (Module.DirectLimit.of R ι _ (fun _ _ h ↦ ((F ⋙ D).map (homOfLE h)).hom) i x) =
      c.ι.app (F.obj i) x :=
  linearEquivOfIsColimitOfPreorder_of (D := F ⋙ D) (c := c.whisker F) _ i x

/-- **A filtered colimit of modules is a directed colimit.** The vertex of a colimit cocone on
a diagram of modules indexed by a small filtered category is the `Module.DirectLimit` of a
directed system indexed by a nonempty directed partial order, namely the reindexing of the
diagram along a final functor out of that poset. -/
theorem exists_directed_linearEquiv_of_isFiltered (J : Type v) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ ModuleCat.{v} R) {c : Cocone D} (hc : IsColimit c) :
    ∃ (α : Type v) (_ : PartialOrder α) (_ : IsDirectedOrder α) (_ : Nonempty α)
      (_ : DecidableEq α) (F : α ⥤ J) (_ : F.Final),
      Nonempty (Module.DirectLimit (fun a ↦ ((F ⋙ D).obj a : Type v))
        (fun _ _ h ↦ ((F ⋙ D).map (homOfLE h)).hom) ≃ₗ[R] c.pt) := by
  classical
  obtain ⟨α, _, _, _, F, _⟩ := IsFiltered.exists_directed J
  exact ⟨α, inferInstance, inferInstance, inferInstance, inferInstance, F, inferInstance,
    ⟨linearEquivOfFinal F D hc⟩⟩

end Final

end ModuleCat

end
