module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectsExtension

/-!
# Splittings of truncated simplicial objects, and the degeneracies of a one-step extension

`Stacks.CategoryTheory.Hypercovering.exists_hypercovering_of_objects_in_of_extensionData` reduces
[Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV) to one piece of data: for an
`M`-truncated hypercovering `Y` carrying an auxiliary invariant, a term of
`CategoryTheory.SimplicialObject.Truncated.CoskExtensionData Y`, i.e. a degree-`M + 1` object, a
morphism from it into the matching object, and a degeneracy family along the epimorphisms out of
`⦋M + 1⦌` satisfying a cocone law and a face law. This file produces that term from a
**splitting** of `Y`, which is the invariant the source carries
([Stacks, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)).

The construction is the source's: the degenerate part of degree `M + 1` is the coproduct of the
nondegenerate parts of `Y` indexed by *all* the epimorphisms `⦋M + 1⦌ ⟶ ⦋m⦌` with `m ≤ M`, a
degeneracy along `e` sends the summand of `Y_x` at `η` to the summand at `e ≫ η`, and the morphism
to the matching object is, on the summand at `ε`, the face family `m ↦ Y(m ≫ ε)` read off the
nondegenerate part.

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.EpiOut`: the index type of the epimorphisms out of a
  simplex with target of dimension at most `M`.
* `CategoryTheory.SimplicialObject.Truncated.Splitting`: a splitting of an `M`-truncated
  simplicial object -- nondegenerate parts `N x`, inclusions `ι x : N x ⟶ Y_x`, and the
  requirement that in each degree the summands along the epimorphisms out of it form a coproduct
  decomposition. This is the truncated form of `CategoryTheory.SimplicialObject.Splitting`.
* `CategoryTheory.SimplicialObject.Truncated.coskLift`: the morphism into the matching object
  determined by a compatible face family. This is the converse of `coskFace` and the companion of
  `hom_ext_of_coskFace`.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.degenPart`,
  `Splitting.degenEpi`, `Splitting.degenLeg` and `Splitting.degenToMatching`: the degenerate part
  of degree `M + 1`, its degeneracies, and its morphism to the matching object.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.coskExtensionData`: the resulting
  `CoskExtensionData`.
* `Stacks.CategoryTheory.Hypercovering.hasCoproduct_degenFamily`: the coproduct the degenerate
  part is built from exists in `SR(C, X)`, the shape being transported along `Equiv.ulift`.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.coskFace_coskLift`: `coskLift` cuts out the face
  family it was built from.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.degenEpi_comp`: the degeneracies form a
  cocone along the epimorphisms out of `⦋M + 1⦌`.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.degenEpi_face`: a face after a degeneracy
  is computed inside `Y`.
* `Stacks.CategoryTheory.Hypercovering.isTruncatedHypercoveringOver_extend_splitting`: the
  induction step of Tag 0DAV, end to end -- a splitting of an `M`-truncated hypercovering by
  objects of `B`, together with a covering of the matching object by objects of `B` through which
  the degenerate part factors, extends it to an `(M + 1)`-truncated one.

## Implementation notes

* **No Eilenberg--Zilber normal form is used.** Indexing the degenerate part by the pairs
  `(ε, i)` with `i` a summand of `Y_m` breaks the cocone law
  `degenEpi (e ≫ g) = Y(g) ≫ degenEpi e`. Indexing by the **nondegenerate** parts instead, which
  is what a splitting provides, makes both sides of the cocone law the summand inclusion at the
  single index `e ≫ g ≫ η`, by associativity alone (`EpiOut.comp_comp`, which is `rfl`). A
  quotient to the latching set would be needed only to *prove* that a given `Y` is split; here
  splitness is the carried invariant, as in the source, so it is data and not an obligation.
* **The only compatibility a splitting has to assume is the colimit condition.** The summand
  inclusion at an index `η` is defined as `ι` followed by the action of `Y` on `η`, so
  `Splitting.incl_comp_map` -- the interaction of the summands with the simplicial structure -- is
  functoriality of `Y` and nothing else. In particular a splitting does *not* have to say how
  faces act on the nondegenerate parts: `Splitting.degenEpi_face` holds because
  `Splitting.degenLeg` is defined through the action of `Y` on the composite.
* **Universes.** `A : Type u` with `[Category.{v} A]`, both free; no universe is narrowed. The
  index type `EpiOut M S` is a `Type`, so an application in a category whose coproducts are
  indexed by a larger universe has to transport the shape along `Equiv.ulift`; the construction
  itself only asks for `HasCoproduct` of the one family it uses.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
* [Stacks Project, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] {M : ℕ}

/-- The index type of the epimorphisms out of a simplex `S` with target of dimension at most
`M`: a pair of an object `x` of the `M`-truncated simplex category and an epimorphism
`S ⟶ x.obj`. -/
def EpiOut (M : ℕ) (S : SimplexCategory) : Type :=
  Σ x : SimplexCategory.Truncated M, {e : S ⟶ x.obj // Epi e}

/-- The target of an index. -/
abbrev EpiOut.target {M : ℕ} {S : SimplexCategory} (j : EpiOut M S) :
    SimplexCategory.Truncated M := j.1

/-- The epimorphism of an index. -/
abbrev EpiOut.hom {M : ℕ} {S : SimplexCategory} (j : EpiOut M S) : S ⟶ j.target.obj := j.2.1

/-- The morphism of an index is an epimorphism. -/
instance EpiOut.epi_hom {M : ℕ} {S : SimplexCategory} (j : EpiOut M S) : Epi j.hom := j.2.2

/-- Precomposition of indices: an epimorphism `e : S ⟶ x.obj` and an index out of `x.obj`
compose to an index out of `S`. -/
abbrev EpiOut.comp {M : ℕ} {S : SimplexCategory} {x : SimplexCategory.Truncated M}
    (e : S ⟶ x.obj) [Epi e] (j : EpiOut M x.obj) : EpiOut M S :=
  ⟨j.target, e ≫ j.hom, epi_comp _ _⟩

/-- Index composition is associative, and on the nose: composition in `SimplexCategory` is
composition of the underlying monotone maps, which is associative by definition, and the
epimorphism witnesses are propositional. -/
theorem EpiOut.comp_comp {S : SimplexCategory} {x y : SimplexCategory.Truncated M}
    (e : S ⟶ x.obj) [Epi e] (g : x.obj ⟶ y.obj) [Epi g] (j : EpiOut M y.obj) :
    EpiOut.comp (e ≫ g) j = EpiOut.comp e (EpiOut.comp g j) :=
  rfl

/-- A **splitting** of an `M`-truncated simplicial object `Y`: objects `N x` of nondegenerate
parts together with inclusions `ι x : N x ⟶ Y_x`, such that in every degree `x` the family of
composites `N y ⟶ Y_y ⟶ Y_x` indexed by the epimorphisms `x.obj ⟶ y.obj` exhibits `Y_x` as the
coproduct of the nondegenerate parts. This is the truncated form of
`CategoryTheory.SimplicialObject.Splitting` and of the splitness of
[Stacks, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU). -/
structure Splitting (Y : SimplicialObject.Truncated A M) where
  /-- The nondegenerate part in each degree. -/
  N : SimplexCategory.Truncated M → A
  /-- The inclusion of the nondegenerate part. -/
  ι : ∀ x, N x ⟶ Y.obj (op x)
  /-- Every degree of `Y` is the coproduct of the nondegenerate parts along the epimorphisms out
  of it. -/
  isColimit (x : SimplexCategory.Truncated M) :
    IsColimit (Cofan.mk (f := fun j : EpiOut M x.obj ↦ N j.target) (Y.obj (op x))
      (fun j ↦ ι j.target ≫ Y.map (ObjectProperty.homMk j.hom).op))

namespace Splitting

variable {Y : SimplicialObject.Truncated A M} (S : Splitting Y)

/-- **The nondegenerate part of degree `k`, read into degree `x` along a morphism
`f : x.obj ⟶ k.obj`.** For `f` an epimorphism this is the summand inclusion of the splitting; for
`f` arbitrary it is the leg the degenerate part contributes to the matching object. One definition
serves both, and the single lemma `incl_comp_map` below is the only interaction between a
splitting and the simplicial structure that the construction needs. -/
def incl {x : SimplexCategory.Truncated M} (k : SimplexCategory.Truncated M)
    (f : x.obj ⟶ k.obj) : S.N k ⟶ Y.obj (op x) :=
  S.ι k ≫ Y.map (ObjectProperty.homMk f).op

/-- **Reading a summand through an action of `Y` is the summand along the composite.** This holds
by definition -- the summands are `ι` followed by the action of `Y` -- so a splitting assumes no
compatibility with the simplicial structure beyond its colimit condition, and in particular no
Eilenberg--Zilber normal form is used anywhere below. -/
theorem incl_comp_map {x y : SimplexCategory.Truncated M} (g : x.obj ⟶ y.obj)
    (k : SimplexCategory.Truncated M) (f : y.obj ⟶ k.obj) :
    S.incl k f ≫ Y.map (ObjectProperty.homMk g).op = S.incl k (g ≫ f) := by
  simp only [incl, Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

/-- The summand inclusion of a splitting at an index. -/
abbrev inj {x : SimplexCategory.Truncated M} (j : EpiOut M x.obj) : S.N j.target ⟶ Y.obj (op x) :=
  S.incl j.target j.hom

/-- Morphisms out of `Y_x` are equal if they agree on every summand inclusion. -/
private theorem hom_ext_inj {x : SimplexCategory.Truncated M} {T : A} (f g : Y.obj (op x) ⟶ T)
    (h : ∀ j : EpiOut M x.obj, S.inj j ≫ f = S.inj j ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (S.isColimit x) _ _ h

/-- The family of nondegenerate parts indexed by the epimorphisms out of `⦋M + 1⦌`. -/
abbrev degenFamily : EpiOut M ⦋M + 1⦌ → A := fun j ↦ S.N j.target

/-- The face family of the summand of the degenerate part indexed by `j`: the nondegenerate part
read into degree `y` along `m ≫ j.hom`. -/
abbrev degenLeg (j : EpiOut M ⦋M + 1⦌) (y : SimplexCategory.Truncated M)
    (m : y.obj ⟶ ⦋M + 1⦌) : S.N j.target ⟶ Y.obj (op y) :=
  S.incl j.target (m ≫ j.hom)

/-- `Splitting.degenLeg` satisfies the cone law, by functoriality of `Y`. -/
theorem degenLeg_comp (j : EpiOut M ⦋M + 1⦌) (x y : SimplexCategory.Truncated M)
    (g : x.obj ⟶ y.obj) (m : y.obj ⟶ ⦋M + 1⦌) :
    S.degenLeg j x (g ≫ m) = S.degenLeg j y m ≫ Y.map (ObjectProperty.homMk g).op := by
  rw [degenLeg, degenLeg, S.incl_comp_map g j.target (m ≫ j.hom), Category.assoc]

end Splitting

section Lift

variable [∀ F : (SimplexCategory.Truncated M)ᵒᵖ ⥤ A,
  (SimplexCategory.Truncated.inclusion M).op.HasPointwiseRightKanExtension F]

/-- **A compatible face family defines a morphism into the matching object.** The matching object
is a pointwise right Kan extension, hence the limit over the structured arrows into the truncated
simplex category, and `coskFace` reads off its cone legs; so a family `c` satisfying the cone law
of `coskFace_comp` is exactly a cone, and `coskLift` is the induced morphism. Together with
`hom_ext_of_coskFace` this identifies the morphisms into the matching object with the compatible
face families. -/
noncomputable def coskLift (Y : SimplicialObject.Truncated A M) {P : A}
    (c : ∀ x : SimplexCategory.Truncated M, (x.obj ⟶ ⦋M + 1⦌) → (P ⟶ Y.obj (op x)))
    (hc : ∀ (x y : SimplexCategory.Truncated M) (g : x.obj ⟶ y.obj) (m : y.obj ⟶ ⦋M + 1⦌),
      c x (g ≫ m) = c y m ≫ Y.map (ObjectProperty.homMk g).op) :
    P ⟶ matchingObj Y :=
  limit.lift (StructuredArrow.proj (op ⦋M + 1⦌) (SimplexCategory.Truncated.inclusion M).op ⋙ Y)
      { pt := P
        π :=
          { app := fun f ↦ c f.right.unop f.hom.unop
            naturality := fun f f' φ ↦ by
              have hφ : f'.hom.unop = φ.right.unop.hom ≫ f.hom.unop :=
                congrArg Quiver.Hom.unop (StructuredArrow.w φ).symm
              change 𝟙 P ≫ c f'.right.unop f'.hom.unop
                = c f.right.unop f.hom.unop ≫ Y.map φ.right
              rw [Category.id_comp, hφ, hc f'.right.unop f.right.unop φ.right.unop.hom]
              rfl } }
    ≫ ((SimplexCategory.Truncated.inclusion M).op.ranObjObjIsoLimit Y (op ⦋M + 1⦌)).inv

/-- `coskLift` cuts out the face family it was built from. -/
@[simp]
theorem coskFace_coskLift (Y : SimplicialObject.Truncated A M) {P : A}
    (c : ∀ x : SimplexCategory.Truncated M, (x.obj ⟶ ⦋M + 1⦌) → (P ⟶ Y.obj (op x)))
    (hc : ∀ (x y : SimplexCategory.Truncated M) (g : x.obj ⟶ y.obj) (m : y.obj ⟶ ⦋M + 1⦌),
      c x (g ≫ m) = c y m ≫ Y.map (ObjectProperty.homMk g).op)
    (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌) :
    coskFace Y (coskLift Y c hc) x m = c x m := by
  have key : ((SimplexCategory.Truncated.inclusion M).op.ranObjObjIsoLimit Y (op ⦋M + 1⦌)).inv
        ≫ ((Truncated.cosk M).obj Y).map m.op
        ≫ ((SimplexCategory.Truncated.inclusion M).op.ranCounit.app Y).app (op x)
      = limit.π (StructuredArrow.proj (op ⦋M + 1⦌) (SimplexCategory.Truncated.inclusion M).op ⋙ Y)
        (StructuredArrow.mk (Y := op x) m.op) :=
    (SimplexCategory.Truncated.inclusion M).op.ranObjObjIsoLimit_inv_π Y
      (op ⦋M + 1⦌) (StructuredArrow.mk (Y := op x) m.op)
  simp only [coskFace, coskLift]
  rw [Category.assoc, key]
  exact limit.lift_π _ _

end Lift

namespace Splitting

variable {Y : SimplicialObject.Truncated A M} (S : Splitting Y) [HasCoproduct S.degenFamily]

/-- **The degenerate part of degree `M + 1`** of a split `M`-truncated simplicial object: the
coproduct of the nondegenerate parts along *all* the epimorphisms out of `⦋M + 1⦌` with target of
dimension at most `M`. -/
noncomputable abbrev degenPart : A := ∐ S.degenFamily

/-- **The degeneracy along an epimorphism `e : ⦋M + 1⦌ ⟶ x.obj`**, with values in the degenerate
part of degree `M + 1`: on the summand of `Y_x` indexed by an epimorphism `η` out of `x.obj` it is
the summand inclusion of the degenerate part at `e ≫ η`. This is well defined because `Y_x` *is*
the coproduct of those summands, and it is the only possible choice, because in a split simplicial
object a degeneracy acts on the indices by precomposition. -/
noncomputable def degenEpi (x : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] : Y.obj (op x) ⟶ S.degenPart :=
  Cofan.IsColimit.desc (S.isColimit x) fun j ↦ Sigma.ι S.degenFamily (EpiOut.comp e j)

/-- The defining property of `Splitting.degenEpi`: it carries the summand of `Y_x` at `η` to the
summand of the degenerate part at `e ≫ η`. -/
@[simp]
theorem inj_comp_degenEpi (x : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] (j : EpiOut M x.obj) :
    S.inj j ≫ S.degenEpi x e = Sigma.ι S.degenFamily (EpiOut.comp e j) :=
  Cofan.IsColimit.fac (S.isColimit x) _ j

/-- **The degeneracies form a cocone along the epimorphisms out of `⦋M + 1⦌`.** This is the law
that fails when the degenerate part is indexed by the whole of `Y_x` instead of by the
nondegenerate parts, and it is the reason the construction needs a splitting. -/
theorem degenEpi_comp (x y : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] (g : x.obj ⟶ y.obj) [Epi g] :
    S.degenEpi y (e ≫ g) = Y.map (ObjectProperty.homMk g).op ≫ S.degenEpi x e := by
  refine S.hom_ext_inj _ _ fun j ↦ ?_
  rw [S.inj_comp_degenEpi, ← Category.assoc, inj, S.incl_comp_map g j.target j.hom]
  exact (S.inj_comp_degenEpi x e (EpiOut.comp g j)).symm

variable [∀ F : (SimplexCategory.Truncated M)ᵒᵖ ⥤ A,
  (SimplexCategory.Truncated.inclusion M).op.HasPointwiseRightKanExtension F]

/-- **The morphism from the degenerate part to the matching object.** On the summand indexed by
`j` its face family is `Splitting.degenLeg`, the only family compatible with the degeneracies. -/
noncomputable def degenToMatching : S.degenPart ⟶ matchingObj Y :=
  Sigma.desc fun j ↦ coskLift Y (S.degenLeg j) (S.degenLeg_comp j)

/-- The face family of `degenToMatching` on the summand indexed by `j` is
`Splitting.degenLeg j`. -/
@[simp]
theorem coskFace_degenToMatching (j : EpiOut M ⦋M + 1⦌) (y : SimplexCategory.Truncated M)
    (m : y.obj ⟶ ⦋M + 1⦌) :
    coskFace Y (Sigma.ι S.degenFamily j ≫ S.degenToMatching) y m = S.degenLeg j y m := by
  simp only [degenToMatching, Sigma.ι_comp_desc, coskFace_coskLift]

/-- **A face after a degeneracy is computed inside `Y`.** With the degenerate part as the source
and `Splitting.degenToMatching` as the morphism to the matching object, the face family cut out by
the latter composes with the degeneracies exactly as the simplicial identities demand. -/
theorem degenEpi_face (x y : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] (m : y.obj ⟶ ⦋M + 1⦌) :
    S.degenEpi x e ≫ coskFace Y S.degenToMatching y m
      = Y.map (ObjectProperty.homMk (m ≫ e)).op := by
  refine S.hom_ext_inj _ _ fun j ↦ ?_
  rw [← Category.assoc, S.inj_comp_degenEpi x e j, comp_coskFace, S.coskFace_degenToMatching,
    inj, S.incl_comp_map (m ≫ e) j.target j.hom]
  rfl

/-- **The one-step extension data of a split truncated simplicial object.** The degenerate part of
degree `M + 1`, the morphism it defines into the matching object, and the degeneracies along the
epimorphisms out of `⦋M + 1⦌`, with their cocone law and their compatibility with the faces. This
is the term `CategoryTheory.SimplicialObject.Truncated.CoskExtensionData` that
`Stacks.CategoryTheory.Hypercovering.exists_hypercovering_of_objects_in_of_extensionData` asks
for, before the degenerate part is pushed into a covering of the matching object by
`CoskExtensionData.ofFac`. -/
noncomputable def coskExtensionData : CoskExtensionData Y where
  pt := S.degenPart
  toMatching := S.degenToMatching
  degenEpi x e := S.degenEpi x e
  degenEpi_comp x y e _ g _ := S.degenEpi_comp x y e g
  degenEpi_face x y e _ m := S.degenEpi_face x y e m

/-- The point of `coskExtensionData` is the degenerate part. -/
@[simp]
theorem coskExtensionData_pt : S.coskExtensionData.pt = S.degenPart := rfl

/-- The morphism to the matching object of `coskExtensionData` is `degenToMatching`. -/
@[simp]
theorem coskExtensionData_toMatching :
    S.coskExtensionData.toMatching = S.degenToMatching := rfl

end Splitting

end CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {M : ℕ} {X : C}

universe w

/-- The coproduct the degenerate part is built from exists in `SR(C, X)`. The index type
`EpiOut M ⦋M + 1⦌` is a `Type` while the formal coproducts are indexed by `Type w`, so the shape
is transported along `Equiv.ulift`; nothing else is needed, because a formal coproduct completion
has all the coproducts of its index universe. -/
noncomputable instance hasCoproduct_degenFamily
    {Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M}
    (S : Splitting Y) : HasCoproduct S.degenFamily := by
  have : HasColimitsOfShape (Discrete (EpiOut M ⦋M + 1⦌)) (FormalCoproduct.{w} (Over X)) :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{w, 0}))
  infer_instance

/-- **The one-step extension of a split truncated hypercovering, end to end.** Let `Y` be an
`M`-truncated hypercovering of `X` by objects of `B` together with a splitting, and let
`u : P ⟶ (cosk_M sk_M Y)_{M + 1}` be a covering of the matching object by objects of `B` through
which the morphism from the degenerate part factors -- which is exactly what
`exists_isCoveringOver_objects_in` delivers. Then the one-step extension along `u` is an
`(M + 1)`-truncated hypercovering of `X` by objects of `B`.

This is Tag 0DAV's induction step granted the *splitness* of `Y` and the factorization: the
degeneracy family of the extension is `Splitting.degenEpi`. -/
theorem isTruncatedHypercoveringOver_extend_splitting
    [∀ (k : ℕ) (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ FormalCoproduct.{w} (Over X)),
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (J : Pretopology C) (B : Set C)
    {Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M}
    (hY : IsTruncatedHypercoveringOver.{w} J B M Y) (S : Splitting Y)
    {P : FormalCoproduct.{w} (Over X)} (u : P ⟶ matchingObj Y)
    (s : S.degenPart ⟶ P) (hsu : s ≫ u = S.degenToMatching)
    (hBP : ∀ i : P.I, (P.obj i).left ∈ B) (hu : IsCoveringOver J u) :
    IsTruncatedHypercoveringOver.{w} J B (M + 1)
      (S.coskExtensionData.ofFac s u hsu).toEpiExtensionData.toExtensionData.extend :=
  isTruncatedHypercoveringOver_extend_coskExtensionData J B hY _ hBP hu

end Stacks.CategoryTheory.Hypercovering

end
