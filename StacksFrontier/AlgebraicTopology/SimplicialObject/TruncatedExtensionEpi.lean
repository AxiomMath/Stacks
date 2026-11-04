module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.TruncatedExtension

/-!
# One-step extension data from epimorphism-only degeneracies and a matching cone

`CategoryTheory.SimplicialObject.Truncated.ExtensionData` takes the two families of a one-step
extension of an `M`-truncated simplicial object in full: a morphism `pt ⟶ Y.obj (op x)` for
*every* `m : x.obj ⟶ ⦋M + 1⦌` and a morphism `Y.obj (op x) ⟶ pt` for *every*
`e : ⦋M + 1⦌ ⟶ x.obj`. Neither family is in that shape where the data actually arises. This file
cuts both down to the shape a consumer has.

For the degeneracies the reduction is genuine: the cocone law `degen y (e ≫ g) =
Y.map g.op ≫ degen x e` determines the whole family from its values on the *epimorphisms* out of
`⦋M + 1⦌`, because `e` factors as `factorThruImage e ≫ image.ι e` and the mono part can be
absorbed into `Y`. `EpiExtensionData` therefore asks only for the epimorphism values, together
with the cocone law along epimorphisms, and `EpiExtensionData.toExtensionData` reconstructs the
rest. That the reconstruction is well defined rests on the uniqueness of epi-mono factorizations
in `SimplexCategory`, exactly as `ExtensionData.endo_eq_of_fac` does for the endomorphisms of
`⦋M + 1⦌`.

For the faces the reduction is a restatement: a family subject to `face x (g ≫ m) =
face y m ≫ Y.map g.op` is a cone over the matching diagram, and a morphism `u` into the matching
object `(cosk_M Y)_{M + 1}` supplies one, with the cone legs `(cosk_M Y).map m.op` followed by the
counit of the right Kan extension. That is `coskFace`.

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.image_len_le`: the image of `e : ⦋M + 1⦌ ⟶ x.obj`,
  for `x` an `M`-truncated object, is `M`-truncated.
* `CategoryTheory.SimplicialObject.Truncated.EpiExtensionData`: one-step extension data with the
  degeneracy family given only along epimorphisms.
* `CategoryTheory.SimplicialObject.Truncated.EpiExtensionData.degen`: the degeneracy family on all
  morphisms out of `⦋M + 1⦌` reconstructed from the epimorphism values.
* `CategoryTheory.SimplicialObject.Truncated.matchingObj`: the value in degree `M + 1` of the
  `M`-th coskeleton of an `M`-truncated simplicial object.
* `CategoryTheory.SimplicialObject.Truncated.coskFace`: the face family determined by a morphism
  into the matching object.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.EpiExtensionData.degen_eq_of_fac`: *any* epi-mono
  factorization of `e` through an `M`-truncated object computes `degen`; this is the
  well-definedness statement behind the reconstruction.
* `CategoryTheory.SimplicialObject.Truncated.EpiExtensionData.toExtensionData` together with
  `exists_extend_of_epiExtensionData`: the reconstruction, and the resulting one-step extension.
* `CategoryTheory.SimplicialObject.Truncated.coskFace_comp`: the cone law for `coskFace`, so that
  `coskFace Y u` and `coskFace_comp Y u` are the `face` and `face_comp` fields of an
  `EpiExtensionData` with `pt` the source of `u`.
* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.degen_comp_eq_degen_comp` and
  `ExtensionData.degen_sigma_eq_degen_sigma`: the constraint that two factorizations of one
  morphism out of degree `M + 1` impose on *any* one-step extension, and its instance at the
  simplicial identity `σ i ≫ σ j = σ j.succ ≫ σ i`. These say what the degeneracy half of a
  one-step extension costs; see the implementation notes.

## Implementation notes

The epimorphism hypothesis is carried as an instance binder `[Epi e]` throughout, so that the
instance `CategoryTheory.epi_comp` supplies `Epi (e ≫ g)` in the statement of the cocone law. As
`Epi` is a `Prop`-valued class there is no coherence condition relating two proofs of it.

The three laws of `ExtensionData` are derived through `degen_eq_of_fac` rather than by unfolding
`degen`, and the bookkeeping that remains is the comparison between `image (e ≫ g)` and
`image (image.ι e ≫ g)`: these are *equal*, not identical, and the equality is used by
substituting it away, which is what `degen_eq_of_fac` exists to do. The composites of two
`Y.map (homMk _).op` are contracted by the single `reassoc` lemma `map_op_homMk_comp`.

`coskFace` needs the coskeleton, hence the instance hypothesis that
`(SimplexCategory.Truncated.inclusion M).op` admits right Kan extensions. It is stated with
`Functor.ranCounit` rather than with the counit of `coskAdj`, because `coskAdj` additionally
requires *left* Kan extensions along the same functor, which a consumer of this file has no
reason to have; and it is required only at the level `M`, not at all levels. The weaker
`HasRightKanExtension` hypothesis is implied by the `HasPointwiseRightKanExtension` one that
consumers carry. No universe is narrowed: `A : Type u` with
`[Category.{v} A]` throughout, as in `Mathlib.AlgebraicTopology.SimplicialObject.Basic`.

**What this does not do.** It does not produce the degeneracy family of a hypercovering, and
`degen_sigma_eq_degen_sigma` says why not. The degenerate part of degree `M + 1` has to be *free*
on the nondegenerate parts of the lower degrees, and the cocone law along epimorphisms asked for
here is exactly the content that the relations between the degeneracies and a comparison morphism
cannot supply when that morphism is not a monomorphism. Already at
`σ (0 : Fin 3) ≫ σ (1 : Fin 2) = σ (2 : Fin 3) ≫ σ (0 : Fin 2) : ⦋3⦌ ⟶ ⦋1⦌` the two
factorizations run through *different* intermediate degeneracies, so the extension has to receive
one and the same morphism out of degree `1` through two different objects of degree `2`, with
equal composites; that is a pushout-type condition on `Y`. It holds as soon as the structure
morphisms of `Y` along the surjections are isomorphisms, which for a simplicial object of
semi-representable objects is exactly the hypothesis that it be *split*.

## References

Truncated simplicial objects are [Stacks, Tag 0180](https://stacks.math.columbia.edu/tag/0180)
and the coskeleton one-step extension is
[Stacks, Tag 0187](https://stacks.math.columbia.edu/tag/0187). The splitting notion referred to
above is [Stacks, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU). The Stacks project states
no result of the present shape, so no declaration here carries a Stacks tag.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] {M : ℕ}

/-- Two morphisms of an `M`-truncated simplicial object coming from composable morphisms of
`SimplexCategory` compose to the morphism coming from their composite. -/
@[reassoc]
theorem map_op_homMk_comp (Y : SimplicialObject.Truncated A M)
    {x y z : SimplexCategory.Truncated M} (f : x.obj ⟶ y.obj) (g : y.obj ⟶ z.obj) :
    Y.map (ObjectProperty.homMk (X := y) (Y := z) g).op
        ≫ Y.map (ObjectProperty.homMk (X := x) (Y := y) f).op
      = Y.map (ObjectProperty.homMk (X := x) (Y := z) (f ≫ g)).op := by
  have h : ObjectProperty.homMk (X := x) (Y := z) (f ≫ g)
      = ObjectProperty.homMk (X := x) (Y := y) f
        ≫ ObjectProperty.homMk (X := y) (Y := z) g := rfl
  rw [h, op_comp, Y.map_comp]

/-- The image of a morphism `e : ⦋M + 1⦌ ⟶ x.obj` out of degree `M + 1` into an `M`-truncated
object is `M`-truncated. -/
theorem image_len_le (x : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) : (image e).len ≤ M :=
  (SimplexCategory.len_le_of_mono (image.ι e)).trans x.property

/-- One-step extension data for an `M`-truncated simplicial object `Y` in which the degeneracy
family is prescribed only along the epimorphisms out of `⦋M + 1⦌`. -/
structure EpiExtensionData (Y : SimplicialObject.Truncated A M) where
  /-- The object sitting in degree `M + 1`. -/
  pt : A
  /-- The face data: a morphism out of `pt` for every morphism of `SimplexCategory` from an
  `M`-truncated object into `⦋M + 1⦌`. -/
  face (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌) : pt ⟶ Y.obj (op x)
  /-- The degeneracy data, prescribed only along the epimorphisms out of `⦋M + 1⦌`. -/
  degenEpi (x : SimplexCategory.Truncated M) (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] :
    Y.obj (op x) ⟶ pt
  /-- The face data is a cone: precomposing with a morphism of `SimplexCategory` is applying `Y`
  to it. -/
  face_comp (x y : SimplexCategory.Truncated M) (g : x.obj ⟶ y.obj) (m : y.obj ⟶ ⦋M + 1⦌) :
    face x (g ≫ m) = face y m ≫ Y.map (ObjectProperty.homMk g).op
  /-- The degeneracy data is a cocone along the epimorphisms: postcomposing with an epimorphism of
  `SimplexCategory` is applying `Y` to it. -/
  degenEpi_comp (x y : SimplexCategory.Truncated M)
      (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] (g : x.obj ⟶ y.obj) [Epi g] :
    degenEpi y (e ≫ g) = Y.map (ObjectProperty.homMk g).op ≫ degenEpi x e
  /-- A face after a degeneracy along an epimorphism is computed inside `Y`. -/
  degenEpi_face (x y : SimplexCategory.Truncated M)
      (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] (m : y.obj ⟶ ⦋M + 1⦌) :
    degenEpi x e ≫ face y m = Y.map (ObjectProperty.homMk (m ≫ e)).op

namespace EpiExtensionData

variable {Y : SimplicialObject.Truncated A M} (D : EpiExtensionData Y)

/-- The degeneracy family on *all* morphisms out of `⦋M + 1⦌`, reconstructed from the
epimorphism-only family by the canonical epi-mono factorization. -/
noncomputable def degen (x : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) : Y.obj (op x) ⟶ D.pt :=
  Y.map (ObjectProperty.homMk
      (X := (⟨image e, image_len_le x e⟩ : SimplexCategory.Truncated M)) (Y := x)
      (image.ι e)).op
    ≫ D.degenEpi ⟨image e, image_len_le x e⟩ (factorThruImage e)

/-- *Any* epi-mono factorization of `e : ⦋M + 1⦌ ⟶ x.obj` through an `M`-truncated object
computes `degen`. This is the well-definedness of the reconstruction. -/
theorem degen_eq_of_fac {x : SimplexCategory.Truncated M} {w : SimplexCategory} (hw : w.len ≤ M)
    {e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj} (ε : (⦋M + 1⦌ : SimplexCategory) ⟶ w)
    (ι : w ⟶ x.obj) [Epi ε] [Mono ι] (hfac : ε ≫ ι = e) :
    D.degen x e = Y.map (ObjectProperty.homMk
        (X := (⟨w, hw⟩ : SimplexCategory.Truncated M)) (Y := x) ι).op
      ≫ D.degenEpi ⟨w, hw⟩ ε := by
  obtain rfl : w = image e := (SimplexCategory.image_eq hfac).symm
  obtain rfl : ε = factorThruImage e := (SimplexCategory.factorThruImage_eq hfac).symm
  obtain rfl : ι = image.ι e := (SimplexCategory.image_ι_eq hfac).symm
  rfl

/-- The reconstructed degeneracy along a composite `e ≫ g` is the degeneracy along `e` precomposed
with `Y.map g.op`. -/
theorem degen_comp (x y : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) (g : x.obj ⟶ y.obj) :
    D.degen y (e ≫ g) = Y.map (ObjectProperty.homMk g).op ≫ D.degen x e := by
  have hw₁ := image_len_le x e
  have hw₂ : (image (image.ι e ≫ g)).len ≤ M :=
    (SimplexCategory.len_le_of_mono (image.ι (image.ι e ≫ g))).trans y.property
  have hfac : (factorThruImage e ≫ factorThruImage (image.ι e ≫ g))
      ≫ image.ι (image.ι e ≫ g) = e ≫ g := by
    rw [Category.assoc, image.fac, ← Category.assoc, image.fac]
  rw [D.degen_eq_of_fac hw₂ _ _ hfac,
    D.degenEpi_comp ⟨image e, hw₁⟩ ⟨image (image.ι e ≫ g), hw₂⟩ (factorThruImage e)
      (factorThruImage (image.ι e ≫ g)),
    map_op_homMk_comp_assoc, image.fac (image.ι e ≫ g),
    D.degen_eq_of_fac hw₁ (factorThruImage e) (image.ι e) (image.fac e),
    map_op_homMk_comp_assoc]

/-- A face after a degeneracy is computed inside `Y`, for the degeneracy family reconstructed from
the epimorphism values.

This is the `degen_face` field that `toExtensionData` below must supply, so it is not an instance
of `ExtensionData.degen_face'`: there `D` is an `ExtensionData Y` and `degen` is one of its
fields, whereas here `D` is an `EpiExtensionData Y`, which prescribes `degenEpi` only along the
epimorphisms, and `degen` is the `def` that reconstructs the rest. -/
theorem degen_face (x y : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) (m : y.obj ⟶ ⦋M + 1⦌) :
    D.degen x e ≫ D.face y m = Y.map (ObjectProperty.homMk (m ≫ e)).op := by
  rw [D.degen_eq_of_fac (image_len_le x e) (factorThruImage e) (image.ι e) (image.fac e),
    Category.assoc, D.degenEpi_face, map_op_homMk_comp, Category.assoc, image.fac]

/-- The full one-step extension data reconstructed from epimorphism-only degeneracy data. -/
noncomputable def toExtensionData : ExtensionData Y where
  pt := D.pt
  face := D.face
  degen := D.degen
  face_comp := D.face_comp
  degen_comp := D.degen_comp
  degen_face := D.degen_face

end EpiExtensionData

/-- **One-step extension of a truncated simplicial object from epimorphism-only degeneracy
data.** From an object in degree `M + 1`, a cone of faces and a cocone of degeneracies along the
epimorphisms out of `⦋M + 1⦌`, there is an `(M + 1)`-truncated simplicial object whose
`M`-truncation is `Y` on the nose and whose degree-`M + 1` term is the given object. -/
theorem exists_extend_of_epiExtensionData {Y : SimplicialObject.Truncated A M}
    (D : EpiExtensionData Y) :
    ∃ Z : SimplicialObject.Truncated A (M + 1),
      (SimplicialObject.Truncated.trunc A (M + 1) M).obj Z = Y ∧
        Z.obj (op ⟨⦋M + 1⦌, le_rfl⟩) = D.pt :=
  exists_extend D.toExtensionData

namespace ExtensionData

variable {Y : SimplicialObject.Truncated A M}

/-- **The constraint that two factorizations impose on a one-step extension.** If a morphism out
of degree `M + 1` factors in two ways through `M`-truncated objects, the degeneracy family of any
one-step extension of `Y` must make the two readings agree. Nothing in the data is free here:
both sides are determined by `Y` and by the degeneracies at the two intermediate objects. -/
theorem degen_comp_eq_degen_comp (D : ExtensionData Y) (x x' z : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) (g : x.obj ⟶ z.obj)
    (e' : (⦋M + 1⦌ : SimplexCategory) ⟶ x'.obj) (g' : x'.obj ⟶ z.obj) (h : e ≫ g = e' ≫ g') :
    Y.map (ObjectProperty.homMk (X := x) (Y := z) g).op ≫ D.degen x e
      = Y.map (ObjectProperty.homMk (X := x') (Y := z) g').op ≫ D.degen x' e' := by
  rw [← D.degen_comp x z e g, ← D.degen_comp x' z e' g', h]

/-- The instance of `degen_comp_eq_degen_comp` at the simplicial identity
`σ i ≫ σ j = σ j.succ ≫ σ i`: for `i ≤ j` the two degeneracies `σ (Fin.castSucc i)` and
`σ j.succ` of degree `M + 2` are forced to agree after being read into degree `M` through `Y`.
This is the condition on `Y` that an extension of an `(M + 1)`-truncated simplicial object has to
satisfy, and the smallest instance of it that is not vacuous is `M = 1`, where
`σ (0 : Fin 3) ≫ σ (1 : Fin 2) = σ (2 : Fin 3) ≫ σ (0 : Fin 2) : ⦋3⦌ ⟶ ⦋1⦌` exhibits one
morphism with two factorizations whose intermediate objects carry *different* summands. -/
theorem degen_sigma_eq_degen_sigma {Y : SimplicialObject.Truncated A (M + 1)}
    (D : ExtensionData Y) {i j : Fin (M + 1)} (hij : i ≤ j) :
    Y.map (ObjectProperty.homMk (X := (⟨⦋M + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (M + 1)))
          (Y := ⟨⦋M⦌, Nat.le_succ M⟩) (SimplexCategory.σ j)).op
        ≫ D.degen ⟨⦋M + 1⦌, le_rfl⟩ (SimplexCategory.σ (Fin.castSucc i))
      = Y.map (ObjectProperty.homMk (X := (⟨⦋M + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (M + 1)))
          (Y := ⟨⦋M⦌, Nat.le_succ M⟩) (SimplexCategory.σ i)).op
        ≫ D.degen ⟨⦋M + 1⦌, le_rfl⟩ (SimplexCategory.σ j.succ) :=
  D.degen_comp_eq_degen_comp _ _ _ _ _ _ _ (SimplexCategory.σ_comp_σ hij)

end ExtensionData

section Matching

variable [∀ F : (SimplexCategory.Truncated M)ᵒᵖ ⥤ A,
  (SimplexCategory.Truncated.inclusion M).op.HasRightKanExtension F]

/-- The matching object of an `M`-truncated simplicial object in degree `M + 1`: the value in
degree `M + 1` of its `M`-th coskeleton. -/
noncomputable abbrev matchingObj (Y : SimplicialObject.Truncated A M) : A :=
  ((Truncated.cosk M).obj Y).obj (op ⦋M + 1⦌)

variable (Y : SimplicialObject.Truncated A M) {P : A} (u : P ⟶ matchingObj Y)

/-- The face family of a one-step extension determined by a morphism into the matching object:
transport along `m` inside the coskeleton, then the counit of the truncation-coskeleton
adjunction. -/
noncomputable def coskFace (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌) :
    P ⟶ Y.obj (op x) :=
  u ≫ ((Truncated.cosk M).obj Y).map m.op
    ≫ ((SimplexCategory.Truncated.inclusion M).op.ranCounit.app Y).app (op x)

/-- The face family coming from a morphism into the matching object is a cone over the matching
diagram, so it is the `face` field of an `EpiExtensionData`. -/
theorem coskFace_comp (x y : SimplexCategory.Truncated M) (g : x.obj ⟶ y.obj)
    (m : y.obj ⟶ ⦋M + 1⦌) :
    coskFace Y u x (g ≫ m) = coskFace Y u y m ≫ Y.map (ObjectProperty.homMk g).op := by
  have hnat : ((Truncated.cosk M).obj Y).map g.op
        ≫ ((SimplexCategory.Truncated.inclusion M).op.ranCounit.app Y).app (op x)
      = ((SimplexCategory.Truncated.inclusion M).op.ranCounit.app Y).app (op y)
        ≫ Y.map (ObjectProperty.homMk (X := x) (Y := y) g).op :=
    ((SimplexCategory.Truncated.inclusion M).op.ranCounit.app Y).naturality
      (ObjectProperty.homMk (X := x) (Y := y) g).op
  simp only [coskFace, op_comp, CategoryTheory.Functor.map_comp, Category.assoc, hnat]

end Matching

end CategoryTheory.SimplicialObject.Truncated

end
