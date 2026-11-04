module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The snake-lemma connecting morphism is the one of the derived-category triangle

Let `S` be a short exact sequence of cochain complexes in an abelian category `C`.  There are
two connecting morphisms in cohomology attached to it:

* the snake-lemma one, `CategoryTheory.ShortComplex.ShortExact.δ`, built in
  `Mathlib.Algebra.Homology.HomologySequence` from
  `HomologicalComplex.HomologySequence.snakeInput`;
* the triangulated one, `DerivedCategory.HomologySequence.δ` of the distinguished triangle
  `DerivedCategory.triangleOfSES`, built from the mapping cone of `S.f`.

`DerivedCategory.homologySequenceδ_triangleOfSES` says they agree, read through the
identification `DerivedCategory.homologyFunctorFactors` of the homology functor of the derived
category with the homology of a complex.  Mathlib proves the corresponding statement in the
*homotopy* category (`CochainComplex.mappingCone.homologySequenceδ_triangleh`, a diagram chase
on cocycles) but does not carry it across the localization, which is what the two lemmas here
do.

## Main results

* `CochainComplex.mappingCone.homologyδOfTriangle_triangle_eq`: on the mapping-cone triangle of
  `S.f`, the degreewise connecting morphism of the triangle factors the snake-lemma connecting
  morphism through `CochainComplex.mappingCone.descShortComplex`.
* `DerivedCategory.homologySequenceδ_mapTriangle_mappingCone_triangle`: in the derived category,
  the connecting morphism of the image of the mapping-cone triangle factors the one of
  `DerivedCategory.triangleOfSES` through `descShortComplex`.
* `DerivedCategory.homologySequenceδ_triangleOfSES`: the two connecting morphisms agree.

The file also contains the comparison of the snake-lemma connecting morphism with the one of
the *extension* of a short exact sequence along an embedding of complex shapes
`e : c.Embedding c'`, which is the second ingredient needed to read a connecting morphism of
`ℕ`-indexed complexes off the derived category of `ℤ`-indexed ones:

* `ComplexShape.Embedding.shortExact_map_extendFunctor`: extending a short exact sequence of
  complexes along `e` keeps it short exact.
* `HomologicalComplex.HomologySequence.extendSnakeInputHom`: the induced morphism of snake
  diagrams, from the one of the extension to the one of the original sequence.
* `HomologicalComplex.HomologySequence.δ_extendFunctor`: the connecting morphism of the
  extension is the connecting morphism of the original sequence, read through
  `HomologicalComplex.extendHomologyIso`.

## Implementation notes

The target of `DerivedCategory.homologyFunctorFactors` is spelled
`(HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj K`, whereas
`ShortComplex.ShortExact.δ` is stated with `K.homology n`.  The two are definitionally equal but
not syntactically so, and across that junction neither `rw` nor `simp` fires — not even on
`Category.assoc`.  The last step of `homologySequenceδ_triangleOfSES` is therefore done in term
mode, with `Category.assoc` and `congrArg` applied as explicit terms.

For the same reason `homologySequenceδ_triangleOfSES` takes its degree hypothesis in the form
`(ComplexShape.up ℤ).Rel n₀ n₁` rather than `n₀ + 1 = n₁`: the two are again definitionally
equal, and the statement only elaborates with the spelling that
`ShortComplex.ShortExact.δ` itself asks for.

In `homologySequenceδ_mapTriangle_mappingCone_triangle` the connecting morphism of the image
triangle cannot be rewritten by `DerivedCategory.descShortComplex_triangleOfSESδ` either: the
objects of `Q.mapTriangle.obj T` do not reduce at the transparency `rw` uses to check that its
motive is type-correct.  The rewrite is performed instead by `congrArg` along a function whose
domain is the hom-type written out, which elaborates at default transparency.

## Two general lemmas about shifts

The file opens with two lemmas of pure `CategoryTheory` that the comparison of two connecting
morphisms needs and that Mathlib does not state:

* `CategoryTheory.Functor.comp_shiftMap`: the shift-sequence morphism of a composite
  `π ⋙ H`, where `π` commutes with the shift and `H` carries a shift sequence, is the one of `H`
  at the image of the morphism corrected by the commutation of `π` with the shift.  This is what
  turns a connecting morphism computed by a homological functor of the form `π ⋙ H` — for
  instance `DerivedCategory.Plus.homologyFunctor`, which is by definition
  `DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor` — into one computed by `H`.
* `CategoryTheory.Functor.commShift_comm₃`: for a natural transformation `α : F₁ ⟶ F₂` of
  functors commuting with the shift and compatible with it, and any `f : Y ⟶ Z⟦1⟧`, the third
  square of the induced morphism `F₁.mapTriangle.obj T ⟶ F₂.mapTriangle.obj T` commutes.  Only
  the square is stated, not the morphism of triangles: `CategoryTheory.Functor.mapTriangleIso`
  needs a natural *isomorphism*, which is more than is available when `α` is the unit of a
  right derived functor.
* `CategoryTheory.Functor.mapδ`, the third morphism of the image of a triangle under a functor
  commuting with the shift, together with the calculus it supports: `mapδ_comp` and
  `comp_mapδ` for composites, `mapδ_naturality` and `mapδ_cancel`, `mapδ_commShift` (which is
  `commShift_comm₃` restated) and `mapδ_assoc`.  Comparing two connecting morphisms of a
  derived category means transporting one `mapδ` across a chain of functors and natural
  isomorphisms, and `mapδ_assoc` is there because the `CategoryTheory.Functor.CommShift`
  structures on `(F ⋙ G) ⋙ H` and on `F ⋙ G ⋙ H` are not definitionally equal.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits ComplexShape Pretriangulated

universe v₄ v₅ u₄ u₅

namespace CategoryTheory.Functor

/-- **The shift-sequence morphism of a composite.**  If `π : C ⥤ D` commutes with the shift and
`H : D ⥤ A` carries a shift sequence, then the shift sequence of `π ⋙ H` is the one of `H`
composed with `π`, and `Functor.shiftMap` of `π ⋙ H` at `f : Y ⟶ Z⟦m⟧` is `Functor.shiftMap` of
`H` at the image of `f` under `π`, corrected by the commutation of `π` with the shift. -/
theorem comp_shiftMap {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {D : Type u₅} [Category.{v₅} D] [HasShift D ℤ] {A : Type u₄} [Category.{v₄} A]
    (π : C ⥤ D) [π.CommShift ℤ] (H : D ⥤ A) [H.ShiftSequence ℤ]
    {Y Z : C} {m : ℤ} (f : Y ⟶ Z⟦m⟧) (a a' : ℤ) (ha' : m + a = a') :
    (π ⋙ H).shiftMap f a a' ha' =
      H.shiftMap (π.map f ≫ (π.commShiftIso m).hom.app Z) a a' ha' := by
  simp only [Functor.shiftMap, Functor.shiftIso, Functor.ShiftSequence.leftComp_shiftIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- **The third square of the morphism of triangles induced by a natural transformation that
commutes with the shift.**  For `α : F₁ ⟶ F₂` with `CategoryTheory.NatTrans.CommShift`, and any
`f : Y ⟶ Z⟦1⟧`, the square formed by the third morphisms of `F₁.mapTriangle` and
`F₂.mapTriangle` and the components of `α` commutes.

Only the square is stated, not a morphism of triangles: the first two squares are the plain
naturality of `α`, and `CategoryTheory.Functor.mapTriangleIso` is unavailable because it asks
for a natural *isomorphism*. -/
theorem commShift_comm₃ {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {D : Type u₅} [Category.{v₅} D] [HasShift D ℤ] {F₁ F₂ : C ⥤ D}
    [F₁.CommShift ℤ] [F₂.CommShift ℤ] (α : F₁ ⟶ F₂) [NatTrans.CommShift α ℤ]
    {Y Z : C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    F₁.map f ≫ (F₁.commShiftIso (1 : ℤ)).hom.app Z ≫ (α.app Z)⟦(1 : ℤ)⟧' =
      α.app Y ≫ F₂.map f ≫ (F₂.commShiftIso (1 : ℤ)).hom.app Z := by
  rw [NatTrans.shift_app_comm, ← Category.assoc, α.naturality f, Category.assoc]


section Mapδ

universe v₆ v₇ v₈ v₉ u₆ u₇ u₈ u₉

variable {C : Type u₆} [Category.{v₆} C] [HasShift C ℤ]
  {D : Type u₇} [Category.{v₇} D] [HasShift D ℤ]
  {E : Type u₈} [Category.{v₈} E] [HasShift E ℤ]

/-- **The third morphism of the image of a triangle under a functor commuting with the shift.**
For `f : Y ⟶ Z⟦1⟧` and `G` commuting with the shift, this is the morphism
`G(Y) ⟶ G(Z)⟦1⟧` that `CategoryTheory.Functor.mapTriangle` attaches to `f`; it is given a name
of its own because the comparison of two connecting morphisms is a chain of identities between
such expressions, and `CategoryTheory.Pretriangulated.Triangle.mk` would force the first two
morphisms of a triangle to be carried along as well. -/
def mapδ (G : C ⥤ D) [G.CommShift ℤ] {Y Z : C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    G.obj Y ⟶ (G.obj Z)⟦(1 : ℤ)⟧ :=
  G.map f ≫ (G.commShiftIso (1 : ℤ)).hom.app Z

/-- `mapδ` of a composite is `mapδ` of the second factor at `mapδ` of the first. -/
theorem mapδ_comp (π : C ⥤ D) [π.CommShift ℤ] (G : D ⥤ E) [G.CommShift ℤ]
    {Y Z : C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    mapδ (π ⋙ G) f = mapδ G (mapδ π f) := by
  simp [mapδ, Functor.commShiftIso_comp_hom_app, CategoryTheory.Functor.map_comp]

/-- `mapδ` absorbs a precomposition. -/
theorem comp_mapδ (G : C ⥤ D) [G.CommShift ℤ] {Y Y' Z : C} (u : Y ⟶ Y')
    (f : Y' ⟶ Z⟦(1 : ℤ)⟧) :
    mapδ G (u ≫ f) = G.map u ≫ mapδ G f := by
  simp [mapδ, CategoryTheory.Functor.map_comp]

/-- **`mapδ` is natural**: a square relating two morphisms `Y ⟶ Z⟦1⟧` is carried by `G` to the
corresponding square between their `mapδ`s. -/
theorem mapδ_naturality (G : C ⥤ D) [G.CommShift ℤ] {Y Z Y' Z' : C}
    (f : Y ⟶ Z⟦(1 : ℤ)⟧) (f' : Y' ⟶ Z'⟦(1 : ℤ)⟧) (u : Y ⟶ Y') (v : Z ⟶ Z')
    (h : f ≫ v⟦(1 : ℤ)⟧' = u ≫ f') :
    mapδ G f ≫ (G.map v)⟦(1 : ℤ)⟧' = G.map u ≫ mapδ G f' := by
  have hn := G.commShiftIso_hom_naturality v (1 : ℤ)
  dsimp [mapδ]
  rw [Category.assoc, ← hn, ← CategoryTheory.Functor.map_comp_assoc, h,
    CategoryTheory.Functor.map_comp_assoc]

/-- **A faithful functor commuting with the shift reflects a `mapδ` square.**  This is the
converse of `mapδ_naturality` for `π` faithful, and it is how a square of `D⁺` is checked in
the full derived category. -/
theorem mapδ_cancel (π : C ⥤ D) [π.CommShift ℤ] [π.Faithful] {Y Z Y' Z' : C}
    (f : Y ⟶ Z⟦(1 : ℤ)⟧) (f' : Y' ⟶ Z'⟦(1 : ℤ)⟧) (u : Y ⟶ Y') (v : Z ⟶ Z')
    (h : mapδ π f ≫ (π.map v)⟦(1 : ℤ)⟧' = π.map u ≫ mapδ π f') :
    f ≫ v⟦(1 : ℤ)⟧' = u ≫ f' := by
  apply π.map_injective
  have h1 := mapδ_naturality π f (f ≫ v⟦(1 : ℤ)⟧') (𝟙 _) v (by simp)
  rw [Functor.map_id, id_comp] at h1
  rw [← comp_mapδ, h1] at h
  dsimp [mapδ] at h
  exact (cancel_mono ((π.commShiftIso (1 : ℤ)).hom.app Z')).1 h

/-- `commShift_comm₃`, phrased with `mapδ`: a natural transformation compatible with the shift
intertwines the two `mapδ`s. -/
theorem mapδ_commShift {G₁ G₂ : C ⥤ D} [G₁.CommShift ℤ] [G₂.CommShift ℤ]
    (α : G₁ ⟶ G₂) [NatTrans.CommShift α ℤ] {Y Z : C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    mapδ G₁ f ≫ (α.app Z)⟦(1 : ℤ)⟧' = α.app Y ≫ mapδ G₂ f := by
  rw [mapδ, mapδ, Category.assoc]
  exact commShift_comm₃ α f

/-- **`mapδ` does not see the bracketing of a triple composite of functors.**  The two
`CategoryTheory.Functor.CommShift` structures on `(G₁ ⋙ G₂) ⋙ G₃` and on `G₁ ⋙ G₂ ⋙ G₃` are
*not* definitionally equal — each is built from the commutations of its own two factors — so
this has to be proved, which `CategoryTheory.NatTrans.CommShift.associator` does. -/
theorem mapδ_assoc (G₁ : C ⥤ D) (G₂ : D ⥤ E) {E' : Type u₉} [Category.{v₉} E'] [HasShift E' ℤ]
    (G₃ : E ⥤ E') [G₁.CommShift ℤ] [G₂.CommShift ℤ] [G₃.CommShift ℤ]
    {Y Z : C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    mapδ ((G₁ ⋙ G₂) ⋙ G₃) f = mapδ (G₁ ⋙ G₂ ⋙ G₃) f := by
  have h := mapδ_commShift (Functor.associator G₁ G₂ G₃).hom f
  simpa using h

end Mapδ

end CategoryTheory.Functor

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

/-- **The degreewise connecting morphism of the mapping-cone triangle is the snake-lemma
connecting morphism.**  For a short exact sequence `S` of cochain complexes, the connecting
morphism in cohomology of the triangle `S.X₁ ⟶ S.X₂ ⟶ mappingCone S.f ⟶ S.X₁⟦1⟧` is the
snake-lemma connecting morphism of `S`, precomposed with the cohomology of the quasi-isomorphism
`CochainComplex.mappingCone.descShortComplex S : mappingCone S.f ⟶ S.X₃`.

This is Mathlib's `CochainComplex.mappingCone.homologySequenceδ_triangleh` with the homotopy
category eliminated: that statement computes the connecting morphism of the image of the
triangle in `K(C)`, and the image determines it because
`HomotopyCategory.homologyFunctorFactors` is an isomorphism. -/
theorem homologyδOfTriangle_triangle_eq (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    CochainComplex.homologyδOfTriangle (triangle S.f) n₀ n₁ h =
      HomologicalComplex.homologyMap (descShortComplex S) n₀ ≫ hS.δ n₀ n₁ h := by
  have k₁ := homologySequenceδ_triangleh hS n₀ n₁ h
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj (triangle S.f) n₀ n₁ h] at k₁
  have k₂ := (cancel_epi ((HomotopyCategory.homologyFunctorFactors C (up ℤ) n₀).hom.app
    (mappingCone S.f))).1 k₁
  exact (cancel_mono ((HomotopyCategory.homologyFunctorFactors C (up ℤ) n₁).inv.app S.X₁)).1
    (k₂.trans (Category.assoc _ _ _).symm)

end CochainComplex.mappingCone

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

/-- **The connecting morphism of the image of the mapping-cone triangle, in terms of the one of
`DerivedCategory.triangleOfSES`.**  The third morphism of the image in the derived category of
the mapping-cone triangle of `S.f` is, by
`DerivedCategory.descShortComplex_triangleOfSESδ`, the composite of
`Q.map (CochainComplex.mappingCone.descShortComplex S)` with the connecting morphism of
`DerivedCategory.triangleOfSES`; the connecting morphisms in cohomology therefore differ by the
same factor. -/
theorem homologySequenceδ_mapTriangle_mappingCone_triangle (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    HomologySequence.δ (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle S.f)) n₀ n₁ h =
      (homologyFunctor C n₀).map (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
        HomologySequence.δ (triangleOfSES hS) n₀ n₁ h := by
  have e₁ : (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle S.f)).mor₃ =
      Q.map (CochainComplex.mappingCone.descShortComplex S) ≫ triangleOfSESδ hS :=
    (descShortComplex_triangleOfSESδ hS).symm
  exact (congrArg (fun (m : Q.obj (CochainComplex.mappingCone S.f) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧) ↦
      (homologyFunctor C 0).shiftMap m n₀ n₁ (by omega)) e₁).trans
    (Functor.shiftMap_comp' _ _ _ _ _ (by omega))

/-- **The snake-lemma connecting morphism of a short exact sequence of cochain complexes is the
connecting morphism of its distinguished triangle in the derived category.**  Read through the
identification `DerivedCategory.homologyFunctorFactors` of `Hⁿ` on the derived category with
`Hⁿ` of a complex, `CategoryTheory.ShortComplex.ShortExact.δ` of `S` is
`DerivedCategory.HomologySequence.δ` of `DerivedCategory.triangleOfSES S`.

Both sides are obtained from the mapping cone of `S.f`: the left by the snake lemma, the right
by the octahedron-free construction of `triangleOfSES`.  The comparison is the one Mathlib
proves in the homotopy category, transported along the localization. -/
theorem homologySequenceδ_triangleOfSES (n₀ n₁ : ℤ) (h : (up ℤ).Rel n₀ n₁) :
    (homologyFunctorFactors C n₀).hom.app S.X₃ ≫ hS.δ n₀ n₁ h =
      HomologySequence.δ (triangleOfSES hS) n₀ n₁ h ≫
        (homologyFunctorFactors C n₁).hom.app S.X₁ := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hA := CochainComplex.homologyFunctorFactors_hom_app_homologyδOfTriangle
    (CochainComplex.mappingCone.triangle S.f) n₀ n₁ h
  rw [CochainComplex.mappingCone.homologyδOfTriangle_triangle_eq hS n₀ n₁ h,
    homologySequenceδ_mapTriangle_mappingCone_triangle hS n₀ n₁ h] at hA
  refine (cancel_epi ((homologyFunctor C n₀).map
    (Q.map (CochainComplex.mappingCone.descShortComplex S)))).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    (((congrArg (fun z ↦ z ≫ hS.δ n₀ n₁ h)
        (homologyFunctorFactors_hom_naturality
          (CochainComplex.mappingCone.descShortComplex S) n₀)).trans
      ((Category.assoc _ _ _).trans hA)).trans (Category.assoc _ _ _))

end DerivedCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι ι' : Type*}
  {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')

/-- **`HomologicalComplex.extendOpcyclesIso` is natural in the complex.**  Mathlib records this
for cycles (`HomologicalComplex.extendCyclesIso_hom_naturality`) and for homology
(`HomologicalComplex.extendHomologyIso_hom_naturality`) but not for opcycles, which is the line
of the snake diagram at the source degree. -/
theorem extendOpcyclesIso_hom_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L)
    {i : ι} {i' : ι'} (hi : e.f i = i') :
    opcyclesMap (extendMap φ e) i' ≫ (L.extendOpcyclesIso e hi).hom =
      (K.extendOpcyclesIso e hi).hom ≫ opcyclesMap φ i := by
  simp [← cancel_epi ((K.extend e).pOpcycles i'), extendMap_f φ e hi]

/-- **The map from opcycles to cycles is compatible with extension along `e`.**  This is the
middle vertical map of the snake diagram; it is pinned down by
`HomologicalComplex.pOpcycles_opcyclesToCycles_iCycles`, which turns the claim into
`HomologicalComplex.extend_d_eq`. -/
theorem extendOpcyclesIso_hom_opcyclesToCycles (K : HomologicalComplex C c) {i j : ι}
    {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extendOpcyclesIso e hi).hom ≫ K.opcyclesToCycles i j =
      (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj).hom := by
  rw [← cancel_epi ((K.extend e).pOpcycles i'), ← cancel_mono (K.iCycles j), assoc, assoc,
    assoc, assoc, pOpcycles_extendOpcyclesIso_hom_assoc,
    pOpcycles_opcyclesToCycles_iCycles, extendCyclesIso_hom_iCycles,
    pOpcycles_opcyclesToCycles_iCycles_assoc, K.extend_d_eq e hi hj, assoc, assoc,
    Iso.inv_hom_id, comp_id]

end HomologicalComplex

namespace ComplexShape.Embedding

variable {C : Type u} [Category.{v} C] [Abelian C] {ι ι' : Type*}
  {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {S : ShortComplex (HomologicalComplex C c)}

/-- **Extending a short exact sequence of complexes along an embedding of complex shapes keeps
it short exact.**  Short exactness of a sequence of complexes is degreewise
(`HomologicalComplex.shortExact_of_degreewise_shortExact`), and in each degree the extension is
either a copy of the original sequence — through
`ComplexShape.Embedding.extendFunctorCompEvalIso` — or the zero sequence. -/
theorem shortExact_map_extendFunctor (hS : S.ShortExact) :
    (S.map (e.extendFunctor C)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun i' => ?_)
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    exact ShortComplex.shortExact_of_iso
      (S.mapNatIso (e.extendFunctorCompEvalIso C (i := i) rfl)).symm (hS.map _)
  · exact
      { mono_f := ⟨fun _ _ _ =>
          (HomologicalComplex.isZero_extend_X S.X₁ e i' (by tauto)).eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ =>
          (HomologicalComplex.isZero_extend_X S.X₃ e i' (by tauto)).eq_of_src _ _⟩
        exact := ShortComplex.exact_of_isZero_X₂ _
          (HomologicalComplex.isZero_extend_X S.X₂ e i' (by tauto)) }

end ComplexShape.Embedding

namespace HomologicalComplex.HomologySequence

variable {C : Type u} [Category.{v} C] [Abelian C] {ι ι' : Type*}
  {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {S : ShortComplex (HomologicalComplex C c)}

/-- **The morphism of snake diagrams from the extension of a short exact sequence of complexes
to the sequence itself.**  Its four lines are `HomologicalComplex.extendHomologyIso`,
`HomologicalComplex.extendOpcyclesIso`, `HomologicalComplex.extendCyclesIso` and
`HomologicalComplex.extendHomologyIso` again; the three commutations are the compatibility of
these isomorphisms with `homologyι`, with `opcyclesToCycles` and with `homologyπ`. -/
noncomputable def extendSnakeInputHom (hS : S.ShortExact) {i j : ι} (hij : c.Rel i j)
    {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') (hij' : c'.Rel i' j') :
    snakeInput (e.shortExact_map_extendFunctor hS) i' j' hij' ⟶ snakeInput hS i j hij where
  f₀ :=
    { τ₁ := (S.X₁.extendHomologyIso e hi).hom
      τ₂ := (S.X₂.extendHomologyIso e hi).hom
      τ₃ := (S.X₃.extendHomologyIso e hi).hom
      comm₁₂ := (extendHomologyIso_hom_naturality S.f e hi).symm
      comm₂₃ := (extendHomologyIso_hom_naturality S.g e hi).symm }
  f₁ :=
    { τ₁ := (S.X₁.extendOpcyclesIso e hi).hom
      τ₂ := (S.X₂.extendOpcyclesIso e hi).hom
      τ₃ := (S.X₃.extendOpcyclesIso e hi).hom
      comm₁₂ := (extendOpcyclesIso_hom_naturality e S.f hi).symm
      comm₂₃ := (extendOpcyclesIso_hom_naturality e S.g hi).symm }
  f₂ :=
    { τ₁ := (S.X₁.extendCyclesIso e hj).hom
      τ₂ := (S.X₂.extendCyclesIso e hj).hom
      τ₃ := (S.X₃.extendCyclesIso e hj).hom
      comm₁₂ := (extendCyclesIso_hom_naturality S.f e hj).symm
      comm₂₃ := (extendCyclesIso_hom_naturality S.g e hj).symm }
  f₃ :=
    { τ₁ := (S.X₁.extendHomologyIso e hj).hom
      τ₂ := (S.X₂.extendHomologyIso e hj).hom
      τ₃ := (S.X₃.extendHomologyIso e hj).hom
      comm₁₂ := (extendHomologyIso_hom_naturality S.f e hj).symm
      comm₂₃ := (extendHomologyIso_hom_naturality S.g e hj).symm }
  comm₀₁ := by ext <;> apply extendHomologyIso_hom_homologyι
  comm₁₂ := by ext <;> apply extendOpcyclesIso_hom_opcyclesToCycles
  comm₂₃ := by ext <;> exact (homologyπ_extendHomologyIso_hom _ e _).symm

/-- **The connecting morphism of the extension of a short exact sequence of complexes is the
connecting morphism of the sequence itself**, read through
`HomologicalComplex.extendHomologyIso`.  Both are the connecting morphism of a snake diagram,
and `extendSnakeInputHom` is a morphism between those diagrams. -/
theorem δ_extendFunctor (hS : S.ShortExact) {i j : ι} (hij : c.Rel i j)
    {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') (hij' : c'.Rel i' j') :
    (e.shortExact_map_extendFunctor hS).δ i' j' hij' ≫ (S.X₁.extendHomologyIso e hj).hom =
      (S.X₃.extendHomologyIso e hi).hom ≫ hS.δ i j hij :=
  ShortComplex.SnakeInput.naturality_δ (extendSnakeInputHom e hS hij hi hj hij')

end HomologicalComplex.HomologySequence

end
