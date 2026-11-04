module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Two out of three along a comparison of Mayer--Vietoris triangles

Stacks 0DJ9 globalises an affine-local base-change comparison by the induction principle of
Stacks 08DR and the Mayer--Vietoris triangle of a cover by two opens: writing `X = U ∪ V`, the
comparison over `X` is invertible once the comparisons over `U`, over `V` and over `U ∩ V` are.
This module proves that step for abstract triangulated functors.

The shape of a base-change comparison is a natural transformation `τ : F ⟶ P ⋙ G` — in the
application `F = Rf_* ⋙ Lg^*`, `P = L(g')^*` and `G = Rf'_*` — together with a morphism of
triangles `ψ` out of the image under `P` of a triangle in the source of `P`, which carries the
given map `L(g')^* K ⟶ K'`. The morphisms `τ.app T.objᵢ ≫ G.map ψ.homᵢ` then form a morphism of
triangles, the *twisted ladder*, as soon as its boundary square commutes, which it does when `τ`
is compatible with the shifts.

## Main definitions

* `Stacks.Cohomology.BaseChangeCover.comparisonLadder`: the morphism of triangles attached to
  `τ : F ⟶ P ⋙ G` and a morphism of triangles `ψ : P.mapTriangle.obj T ⟶ T'`.
* `Stacks.Cohomology.BaseChangeCover.coverMiddleMap`: the middle component of a morphism of
  Mayer--Vietoris triangles, assembled from one comparison map per leg of the cover.

## Main results

* `Stacks.Cohomology.BaseChangeCover.isIso_comp_app_obj₁`: two out of three along the ladder.
* `Stacks.Cohomology.BaseChangeCover.boundary_square_comp`: the boundary square of the ladder
  for a shift-compatible comparison.
* `Stacks.Cohomology.BaseChangeCover.isIso_comp_app_coverMiddleMap`: invertibility of the
  comparison at the middle vertex of a Mayer--Vietoris triangle is invertibility on each of the
  two legs of the cover separately.
* `Stacks.Cohomology.BaseChangeCover.coverSquare_one`, `coverSquare_two`: the two squares over
  the middle vertex follow from the four squares over the legs of the cover.

## Implementation notes

`(P.mapTriangle.obj T).obj₁` and `P.obj T.obj₁` are definitionally equal and not syntactically
equal, so every equational step is stated over plain objects and the triangle data is supplied
at the application site, in term mode.

The functor `P` need not preserve the biproduct `A ⊞ B` on the nose; being additive it sends
`CategoryTheory.Limits.biprod.total` to a decomposition of the identity of `P.obj (A ⊞ B)`, and
`hom_ext_of_map_biprod` and `isIso_of_diagonal` are the two consequences of that which the
biproduct bookkeeping needs.

## References

* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.BaseChangeCover

/-! ### The ladder of a shift-compatible comparison -/

section Ladder

variable {C C' D : Type*} [Category* C] [Category* C'] [Category* D]

section Square

variable {F : C ⥤ D} {P : C ⥤ C'} {G : C' ⥤ D}

/-- **One square of the ladder.** A naturality square of `τ : F ⟶ P ⋙ G` glued to a commuting
square in the target of `P`. Stated over plain objects, so that the components of a morphism of
triangles can be supplied at the application site. -/
public theorem naturality_square (τ : F ⟶ P ⋙ G) {X Y : C} (u : X ⟶ Y)
    {X' Y' : C'} (u' : X' ⟶ Y') (a : P.obj X ⟶ X') (b : P.obj Y ⟶ Y')
    (h : P.map u ≫ b = a ≫ u') :
    F.map u ≫ τ.app Y ≫ G.map b = (τ.app X ≫ G.map a) ≫ G.map u' := by
  have hn : F.map u ≫ τ.app Y = τ.app X ≫ G.map (P.map u) := τ.naturality u
  rw [← assoc, hn, assoc, ← G.map_comp, h, G.map_comp, assoc]

end Square

variable [HasShift C ℤ] [HasShift C' ℤ] [HasShift D ℤ]
variable {F : C ⥤ D} {P : C ⥤ C'} {G : C' ⥤ D} [F.CommShift ℤ] [P.CommShift ℤ] [G.CommShift ℤ]

/-- **The boundary square of a shift-compatible natural transformation.** Stated over the plain
spelling of the two functors, so that the rewrite is performed on small terms. -/
public theorem commShift_boundary_square {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] {Z W : C} (c : Z ⟶ W⟦(1 : ℤ)⟧) :
    (F₁.map c ≫ (F₁.commShiftIso (1 : ℤ)).hom.app W) ≫ (τ.app W)⟦(1 : ℤ)⟧' =
      τ.app Z ≫ F₂.map c ≫ (F₂.commShiftIso (1 : ℤ)).hom.app W := by
  rw [assoc, NatTrans.shift_app_comm τ (1 : ℤ) W, ← assoc, τ.naturality c, assoc]

/-- A morphism of triangles pushed forward along `G`, read on `(P ⋙ G).mapTriangle` rather than
on `P.mapTriangle ⋙ G.mapTriangle`. -/
public def pushTriangleMorphism {T : Triangle C} {T' : Triangle C'}
    (ψ : P.mapTriangle.obj T ⟶ T') :
    (P ⋙ G).mapTriangle.obj T ⟶ G.mapTriangle.obj T' :=
  (Functor.mapTriangleCompIso P G).hom.app T ≫ G.mapTriangle.map ψ

/-- The first component of the pushed-forward morphism of triangles. -/
public theorem pushTriangleMorphism_hom₁ {T : Triangle C} {T' : Triangle C'}
    (ψ : P.mapTriangle.obj T ⟶ T') :
    (pushTriangleMorphism (G := G) ψ).hom₁ = G.map ψ.hom₁ := by
  simp only [pushTriangleMorphism, Functor.comp_obj, triangleCategory_comp,
    TriangleMorphism.comp_hom₁, Functor.mapTriangleCompIso_hom_app_hom₁,
    Functor.mapTriangle_map_hom₁]
  exact Category.id_comp _

/-- The third component of the pushed-forward morphism of triangles. -/
public theorem pushTriangleMorphism_hom₃ {T : Triangle C} {T' : Triangle C'}
    (ψ : P.mapTriangle.obj T ⟶ T') :
    (pushTriangleMorphism (G := G) ψ).hom₃ = G.map ψ.hom₃ := by
  simp only [pushTriangleMorphism, Functor.comp_obj, triangleCategory_comp,
    TriangleMorphism.comp_hom₃, Functor.mapTriangleCompIso_hom_app_hom₃,
    Functor.mapTriangle_map_hom₃]
  exact Category.id_comp _

/-- **The boundary square of the ladder.** The shift compatibility of `τ` and the boundary
square of the pushed-forward morphism of triangles, joined over the plain spelling of the two
functors. -/
public theorem boundary_square_comp (τ : F ⟶ P ⋙ G) [NatTrans.CommShift τ ℤ]
    {T : Triangle C} {T' : Triangle C'} (ψ : P.mapTriangle.obj T ⟶ T') :
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (τ.app T.obj₁ ≫ G.map ψ.hom₁)⟦(1 : ℤ)⟧' =
      (τ.app T.obj₃ ≫ G.map ψ.hom₃) ≫
        (G.map T'.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T'.obj₁) := by
  have hm0 := (pushTriangleMorphism (G := G) ψ).comm₃
  rw [pushTriangleMorphism_hom₁, pushTriangleMorphism_hom₃] at hm0
  have hm : ((P ⋙ G).map T.mor₃ ≫ ((P ⋙ G).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
      (G.map ψ.hom₁)⟦(1 : ℤ)⟧' =
      G.map ψ.hom₃ ≫ (G.map T'.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T'.obj₁) := hm0
  have hb := commShift_boundary_square τ T.mor₃
  rw [(shiftFunctor D (1 : ℤ)).map_comp, ← assoc, hb, assoc, hm]
  exact (assoc _ _ _).symm

/-- **The ladder of a comparison twisted by a morphism of triangles.** For `τ : F ⟶ P ⋙ G` and
a morphism of triangles `ψ` out of the image of `T` under `P`, the morphisms
`τ.app T.objᵢ ≫ G.map ψ.homᵢ` form a morphism of triangles, provided the boundary square
commutes. The boundary square is a hypothesis rather than a consequence of shift compatibility
of `τ`, so that the ladder is available to a comparison whose shift compatibility is known only
at the objects in play; `boundary_square_comp` supplies it when `τ` is shift-compatible. -/
public def comparisonLadder (τ : F ⟶ P ⋙ G)
    {T : Triangle C} {T' : Triangle C'} (ψ : P.mapTriangle.obj T ⟶ T')
    (hbd : (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (τ.app T.obj₁ ≫ G.map ψ.hom₁)⟦(1 : ℤ)⟧' =
      (τ.app T.obj₃ ≫ G.map ψ.hom₃) ≫
        (G.map T'.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T'.obj₁)) :
    F.mapTriangle.obj T ⟶ G.mapTriangle.obj T' :=
  Triangle.homMk _ _ (τ.app T.obj₁ ≫ G.map ψ.hom₁) (τ.app T.obj₂ ≫ G.map ψ.hom₂)
    (τ.app T.obj₃ ≫ G.map ψ.hom₃)
    (naturality_square τ T.mor₁ T'.mor₁ ψ.hom₁ ψ.hom₂ ψ.comm₁)
    (naturality_square τ T.mor₂ T'.mor₂ ψ.hom₂ ψ.hom₃ ψ.comm₂) hbd

section Pretriangulated

variable [HasZeroObject C] [HasZeroObject C'] [HasZeroObject D]
  [Preadditive C] [Preadditive C'] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated C'] [Pretriangulated D]

/-- **Two out of three along the twisted ladder, at the first vertex.** If the comparison
twisted by `ψ` is invertible at the second and the third vertex, then it is invertible at the
first. -/
public theorem isIso_comp_app_obj₁ [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ P ⋙ G) {T : Triangle C} {T' : Triangle C'}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C') (ψ : P.mapTriangle.obj T ⟶ T')
    (hbd : (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (τ.app T.obj₁ ≫ G.map ψ.hom₁)⟦(1 : ℤ)⟧' =
      (τ.app T.obj₃ ≫ G.map ψ.hom₃) ≫
        (G.map T'.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T'.obj₁))
    (h₂ : IsIso (τ.app T.obj₂ ≫ G.map ψ.hom₂))
    (h₃ : IsIso (τ.app T.obj₃ ≫ G.map ψ.hom₃)) :
    IsIso (τ.app T.obj₁ ≫ G.map ψ.hom₁) :=
  Pretriangulated.isIso₁_of_isIso₂₃ (comparisonLadder τ ψ hbd)
    (F.map_distinguished T hT) (G.map_distinguished T' hT') h₂ h₃

end Pretriangulated

end Ladder

/-! ### Biproducts under an additive functor -/

/-- **An additive functor sends the biproduct decomposition of an identity to a decomposition of
an identity.** An additive functor need not preserve the biproduct `A ⊞ B` on the nose, but it
does send `CategoryTheory.Limits.biprod.total` to a decomposition of the identity of
`H.obj (A ⊞ B)`, and that is all the biproduct calculus below uses. -/
public theorem map_biprod_total {E E' : Type*} [Category* E] [Category* E']
    [Preadditive E] [Preadditive E'] (H : E ⥤ E') [H.Additive] (A B : E)
    [HasBinaryBiproduct A B] :
    H.map (biprod.fst : A ⊞ B ⟶ A) ≫ H.map (biprod.inl : A ⟶ A ⊞ B) +
      H.map (biprod.snd : A ⊞ B ⟶ B) ≫ H.map (biprod.inr : B ⟶ A ⊞ B) =
      𝟙 (H.obj (A ⊞ B)) := by
  rw [← H.map_comp, ← H.map_comp, ← H.map_add, biprod.total, H.map_id]

/-- **A morphism that is diagonal for two decompositions of the identity is invertible as soon
as both of its diagonal entries are.** Stated over bare decompositions of the two identities
rather than over biproducts, because the decompositions are what an additive functor supplies:
the image of a biproduct under an additive functor is not a biproduct on the nose. -/
public theorem isIso_of_diagonal {E : Type*} [Category* E] [Preadditive E]
    {X Y X₁ X₂ Y₁ Y₂ : E} (p₁ : X ⟶ X₁) (i₁ : X₁ ⟶ X) (p₂ : X ⟶ X₂) (i₂ : X₂ ⟶ X)
    (q₁ : Y ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (q₂ : Y ⟶ Y₂) (j₂ : Y₂ ⟶ Y)
    (hX : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 X) (hY : q₁ ≫ j₁ + q₂ ≫ j₂ = 𝟙 Y)
    (m : X ⟶ Y) (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) [IsIso a] [IsIso b]
    (hi₁ : i₁ ≫ m = a ≫ j₁) (hi₂ : i₂ ≫ m = b ≫ j₂)
    (hp₁ : m ≫ q₁ = p₁ ≫ a) (hp₂ : m ≫ q₂ = p₂ ≫ b) :
    IsIso m := by
  refine ⟨⟨q₁ ≫ inv a ≫ i₁ + q₂ ≫ inv b ≫ i₂, ?_, ?_⟩⟩
  · rw [Preadditive.comp_add, ← assoc m, ← assoc m, hp₁, hp₂]
    simpa using hX
  · simp only [Preadditive.add_comp, assoc, hi₁, hi₂]
    simpa using hY

/-! ### The two squares over the middle vertex of a Mayer--Vietoris triangle -/

section CoverSquares

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  (P : C ⥤ C') [P.Additive]

/-- **The two images of the biproduct inclusions are jointly epimorphic.** The decomposition of
the identity of `P.obj (A ⊞ B)` supplied by `map_biprod_total` separates any two morphisms out
of it. This is what makes the second cover square provable: that square compares two morphisms
out of `P.obj (A ⊞ B)`, where the biproduct is formed in the source category, so the
projections of the target biproduct do not separate them. -/
public theorem hom_ext_of_map_biprod {A B : C} [HasBinaryBiproduct A B] {Z : C'}
    (x y : P.obj (A ⊞ B) ⟶ Z)
    (h₁ : P.map (biprod.inl : A ⟶ A ⊞ B) ≫ x = P.map (biprod.inl : A ⟶ A ⊞ B) ≫ y)
    (h₂ : P.map (biprod.inr : B ⟶ A ⊞ B) ≫ x = P.map (biprod.inr : B ⟶ A ⊞ B) ≫ y) :
    x = y := by
  rw [← id_comp x, ← id_comp y, ← map_biprod_total P A B, Preadditive.add_comp,
    Preadditive.add_comp, assoc, assoc, assoc, assoc, h₁, h₂]

variable {A B : C} [HasBinaryBiproduct A B] {A' B' : C'} [HasBinaryBiproduct A' B']

/-- **The middle component of a morphism of Mayer--Vietoris triangles.** Given a comparison map
on each leg of the cover, the map on the middle vertex of the triangle: the leg maps read
through the projections of the source biproduct. -/
public def coverMiddleMap (bU : P.obj A ⟶ A') (bV : P.obj B ⟶ B') :
    P.obj (A ⊞ B) ⟶ A' ⊞ B' :=
  biprod.lift (P.map biprod.fst ≫ bU) (P.map biprod.snd ≫ bV)

variable (bU : P.obj A ⟶ A') (bV : P.obj B ⟶ B')

omit [P.Additive] in
/-- The first projection of the middle component. -/
public theorem coverMiddleMap_comp_fst :
    coverMiddleMap P bU bV ≫ biprod.fst = P.map biprod.fst ≫ bU :=
  biprod.lift_fst _ _

omit [P.Additive] in
/-- The second projection of the middle component. -/
public theorem coverMiddleMap_comp_snd :
    coverMiddleMap P bU bV ≫ biprod.snd = P.map biprod.snd ≫ bV :=
  biprod.lift_snd _ _

/-- The middle component restricted to the first leg of the cover. -/
public theorem map_inl_comp_coverMiddleMap :
    P.map (biprod.inl : A ⟶ A ⊞ B) ≫ coverMiddleMap P bU bV = bU ≫ biprod.inl := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp [coverMiddleMap_comp_fst, coverMiddleMap_comp_snd, ← P.map_comp_assoc]

/-- The middle component restricted to the second leg of the cover. -/
public theorem map_inr_comp_coverMiddleMap :
    P.map (biprod.inr : B ⟶ A ⊞ B) ≫ coverMiddleMap P bU bV = bV ≫ biprod.inr := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp [coverMiddleMap_comp_fst, coverMiddleMap_comp_snd, ← P.map_comp_assoc]

omit [P.Additive] in
/-- **The first cover square, from its two leg squares.** The square comparing the two
`biprod.lift` maps of a pair of Mayer--Vietoris triangles commutes as soon as it commutes on
each leg of the cover separately. -/
public theorem coverSquare_one {L : C} {L' : C'} (r₁ : L ⟶ A) (r₂ : L ⟶ B)
    (r₁' : L' ⟶ A') (r₂' : L' ⟶ B') (Ψ : P.obj L ⟶ L')
    (hr₁ : P.map r₁ ≫ bU = Ψ ≫ r₁') (hr₂ : P.map r₂ ≫ bV = Ψ ≫ r₂') :
    P.map (biprod.lift r₁ r₂) ≫ coverMiddleMap P bU bV = Ψ ≫ biprod.lift r₁' r₂' := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp [coverMiddleMap_comp_fst, coverMiddleMap_comp_snd, ← P.map_comp_assoc, hr₁, hr₂]

/-- **The second cover square, from its two leg squares.** The square comparing the two
`biprod.desc` maps of a pair of Mayer--Vietoris triangles commutes as soon as it commutes on
each leg of the cover separately. -/
public theorem coverSquare_two {W : C} {W' : C'} (d₁ : A ⟶ W) (d₂ : B ⟶ W)
    (d₁' : A' ⟶ W') (d₂' : B' ⟶ W') (c : P.obj W ⟶ W')
    (hd₁ : P.map d₁ ≫ c = bU ≫ d₁') (hd₂ : P.map d₂ ≫ c = bV ≫ d₂') :
    P.map (biprod.desc d₁ d₂) ≫ c = coverMiddleMap P bU bV ≫ biprod.desc d₁' d₂' := by
  refine hom_ext_of_map_biprod P _ _ ?_ ?_
  · rw [← assoc, ← P.map_comp, biprod.inl_desc, hd₁, ← assoc,
      map_inl_comp_coverMiddleMap, assoc, biprod.inl_desc]
  · rw [← assoc, ← P.map_comp, biprod.inr_desc, hd₂, ← assoc,
      map_inr_comp_coverMiddleMap, assoc, biprod.inr_desc]

section Middle

variable {D : Type*} [Category* D] [Preadditive D] {F : C ⥤ D} {G : C' ⥤ D}
  [F.Additive] [G.Additive]

/-- **Invertibility at the middle vertex is invertibility on each leg of the cover.** For a
natural transformation `τ : F ⟶ P ⋙ G`, the comparison `τ.app (A ⊞ B) ≫ G.map (coverMiddleMap
P bU bV)` is diagonal for the decompositions of the identities that `F` and `G` produce from
the two biproducts, so it is invertible as soon as its two diagonal entries
`τ.app A ≫ G.map bU` and `τ.app B ≫ G.map bV` are. -/
public theorem isIso_comp_app_coverMiddleMap (τ : F ⟶ P ⋙ G)
    (hU : IsIso (τ.app A ≫ G.map bU)) (hV : IsIso (τ.app B ≫ G.map bV)) :
    IsIso (τ.app (A ⊞ B) ≫ G.map (coverMiddleMap P bU bV)) := by
  have hnl : F.map (biprod.inl : A ⟶ A ⊞ B) ≫ τ.app (A ⊞ B) =
      τ.app A ≫ G.map (P.map (biprod.inl : A ⟶ A ⊞ B)) := τ.naturality _
  have hnr : F.map (biprod.inr : B ⟶ A ⊞ B) ≫ τ.app (A ⊞ B) =
      τ.app B ≫ G.map (P.map (biprod.inr : B ⟶ A ⊞ B)) := τ.naturality _
  have hnf : F.map (biprod.fst : A ⊞ B ⟶ A) ≫ τ.app A =
      τ.app (A ⊞ B) ≫ G.map (P.map (biprod.fst : A ⊞ B ⟶ A)) := τ.naturality _
  have hns : F.map (biprod.snd : A ⊞ B ⟶ B) ≫ τ.app B =
      τ.app (A ⊞ B) ≫ G.map (P.map (biprod.snd : A ⊞ B ⟶ B)) := τ.naturality _
  refine isIso_of_diagonal (F.map biprod.fst) (F.map biprod.inl)
    (F.map biprod.snd) (F.map biprod.inr) (G.map biprod.fst) (G.map biprod.inl)
    (G.map biprod.snd) (G.map biprod.inr) (map_biprod_total F A B)
    (map_biprod_total G A' B') _ (τ.app A ≫ G.map bU) (τ.app B ≫ G.map bV) ?_ ?_ ?_ ?_
  · rw [← assoc, hnl, assoc, ← G.map_comp, map_inl_comp_coverMiddleMap, G.map_comp, ← assoc]
  · rw [← assoc, hnr, assoc, ← G.map_comp, map_inr_comp_coverMiddleMap, G.map_comp, ← assoc]
  · rw [assoc, ← G.map_comp, coverMiddleMap_comp_fst, G.map_comp, ← assoc, ← hnf, assoc]
  · rw [assoc, ← G.map_comp, coverMiddleMap_comp_snd, G.map_comp, ← assoc, ← hns, assoc]

end Middle

end CoverSquares

/-! ### Mayer--Vietoris triangles and the induction step -/

section Triangles

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasShift C ℤ] [HasShift C' ℤ]

/-- **A triangle of Mayer--Vietoris shape.** The first map is a `biprod.lift` of two restriction
maps and the second a `biprod.desc` of two intersection maps. This is the shape of the triangle
produced by Stacks 08HZ out of a cover of the source by two opens. -/
public def coverTriangle {L A B W : C} [HasBinaryBiproduct A B] (r₁ : L ⟶ A) (r₂ : L ⟶ B)
    (d₁ : A ⟶ W) (d₂ : B ⟶ W) (δ : W ⟶ L⟦(1 : ℤ)⟧) : Triangle C :=
  Triangle.mk (biprod.lift r₁ r₂) (biprod.desc d₁ d₂) δ

variable (P : C ⥤ C') [P.Additive] [P.CommShift ℤ]
  {L A B W : C} [HasBinaryBiproduct A B] {L' A' B' W' : C'} [HasBinaryBiproduct A' B']
  (r₁ : L ⟶ A) (r₂ : L ⟶ B) (d₁ : A ⟶ W) (d₂ : B ⟶ W) (δ : W ⟶ L⟦(1 : ℤ)⟧)
  (r₁' : L' ⟶ A') (r₂' : L' ⟶ B') (d₁' : A' ⟶ W') (d₂' : B' ⟶ W') (δ' : W' ⟶ L'⟦(1 : ℤ)⟧)
  (Ψ : P.obj L ⟶ L') (bU : P.obj A ⟶ A') (bV : P.obj B ⟶ B') (c : P.obj W ⟶ W')

/-- **The morphism of Mayer--Vietoris triangles.** For two triangles of Mayer--Vietoris shape, a
comparison map on the first vertex, one on each leg of the cover and one on the last vertex
assemble into a morphism of triangles out of the image of the first triangle under `P`,
provided the four leg squares and the boundary square commute. -/
public def coverTriangleMap
    (hr₁ : P.map r₁ ≫ bU = Ψ ≫ r₁') (hr₂ : P.map r₂ ≫ bV = Ψ ≫ r₂')
    (hd₁ : P.map d₁ ≫ c = bU ≫ d₁') (hd₂ : P.map d₂ ≫ c = bV ≫ d₂')
    (hδ : (P.map δ ≫ (P.commShiftIso (1 : ℤ)).hom.app L) ≫ Ψ⟦(1 : ℤ)⟧' = c ≫ δ') :
    P.mapTriangle.obj (coverTriangle r₁ r₂ d₁ d₂ δ) ⟶ coverTriangle r₁' r₂' d₁' d₂' δ' :=
  Triangle.homMk _ _ Ψ (coverMiddleMap P bU bV) c
    (coverSquare_one P bU bV r₁ r₂ r₁' r₂' Ψ hr₁ hr₂)
    (coverSquare_two P bU bV d₁ d₂ d₁' d₂' c hd₁ hd₂) hδ

variable (hr₁ : P.map r₁ ≫ bU = Ψ ≫ r₁') (hr₂ : P.map r₂ ≫ bV = Ψ ≫ r₂')
  (hd₁ : P.map d₁ ≫ c = bU ≫ d₁') (hd₂ : P.map d₂ ≫ c = bV ≫ d₂')
  (hδ : (P.map δ ≫ (P.commShiftIso (1 : ℤ)).hom.app L) ≫ Ψ⟦(1 : ℤ)⟧' = c ≫ δ')

section Pretriangulated

variable {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
  [HasZeroObject C] [HasZeroObject C'] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated C'] [Pretriangulated D]
  {F : C ⥤ D} {G : C' ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]

include hr₁ hr₂ hd₁ hd₂ hδ in
/-- **The induction step of Stacks 0DJ9.** A comparison `τ : F ⟶ P ⋙ G` between triangulated
functors is invertible at the first vertex of a Mayer--Vietoris triangle as soon as it is
invertible on the two opens of the cover and on their intersection.

Read with `F = Rf_* ⋙ Lg^*`, `P = L(g')^*` and `G = Rf'_*`, the composite
`τ.app Z ≫ G.map ψ` is the composition `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K ⟶ Rf'_* K'` of Stacks
0DJ9, and the two triangles are the relative Mayer--Vietoris triangles of Stacks 08HZ attached
to a cover of the source by two opens. This is the step the induction of Stacks 08DR is run
with; what the hypotheses ask for is one comparison map per vertex, the four squares over the
legs of the cover, the boundary square of the comparison of the two connecting maps, and the
boundary square of the ladder itself. The latter is `boundary_square_comp` whenever `τ` is
compatible with the shifts.

This is the abstract form of the step; `isIso_derivedBaseChangeMap_comp_of_cover` is its
instance at the derived base change map of Stacks 08HY, and that is where the tag sits. -/
public theorem isIso_comp_app_cover [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ P ⋙ G)
    (hbd : (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
        (τ.app L ≫ G.map Ψ)⟦(1 : ℤ)⟧' =
      (τ.app W ≫ G.map c) ≫ (G.map δ' ≫ (G.commShiftIso (1 : ℤ)).hom.app L'))
    (hT : coverTriangle r₁ r₂ d₁ d₂ δ ∈ distTriang C)
    (hT' : coverTriangle r₁' r₂' d₁' d₂' δ' ∈ distTriang C')
    (hU : IsIso (τ.app A ≫ G.map bU)) (hV : IsIso (τ.app B ≫ G.map bV))
    (hW : IsIso (τ.app W ≫ G.map c)) :
    IsIso (τ.app L ≫ G.map Ψ) :=
  isIso_comp_app_obj₁ τ hT hT'
    (coverTriangleMap P r₁ r₂ d₁ d₂ δ r₁' r₂' d₁' d₂' δ' Ψ bU bV c hr₁ hr₂ hd₁ hd₂ hδ) hbd
    (isIso_comp_app_coverMiddleMap P bU bV τ hU hV) hW

include hr₁ hr₂ hd₁ hd₂ hδ in
/-- **The induction step of Stacks 0DJ9 for a shift-compatible comparison.** The boundary
square of the ladder is then automatic, being `boundary_square_comp`. -/
public theorem isIso_comp_app_cover_of_commShift [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ P ⋙ G) [NatTrans.CommShift τ ℤ]
    (hT : coverTriangle r₁ r₂ d₁ d₂ δ ∈ distTriang C)
    (hT' : coverTriangle r₁' r₂' d₁' d₂' δ' ∈ distTriang C')
    (hU : IsIso (τ.app A ≫ G.map bU)) (hV : IsIso (τ.app B ≫ G.map bV))
    (hW : IsIso (τ.app W ≫ G.map c)) :
    IsIso (τ.app L ≫ G.map Ψ) :=
  isIso_comp_app_cover P r₁ r₂ d₁ d₂ δ r₁' r₂' d₁' d₂' δ' Ψ bU bV c hr₁ hr₂ hd₁ hd₂ hδ τ
    (boundary_square_comp τ
      (coverTriangleMap P r₁ r₂ d₁ d₂ δ r₁' r₂' d₁' d₂' δ' Ψ bU bV c hr₁ hr₂ hd₁ hd₂ hδ))
    hT hT' hU hV hW

end Pretriangulated

end Triangles

end Stacks.Cohomology.BaseChangeCover

end
