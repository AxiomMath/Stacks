module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectsMatching

/-!
# One-step extension of a truncated hypercovering by objects in a prescribed collection

`Stacks.CategoryTheory.Hypercovering.exists_hypercovering_of_objects_in_of_step` reduces
[Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV) to a single one-step extension of
truncated hypercoverings by objects of a collection `B`, and
`exists_isCoveringOver_objects_in` proves its *covering* half: the matching object
`(cosk_M sk_M K)_{M + 1}` admits a covering `u : P ⟶ (cosk_M sk_M K)_{M + 1}` by objects of `B`
through which a prescribed morphism from the degenerate part factors.
`CategoryTheory.SimplicialObject.Truncated.ExtensionData` builds an `(M + 1)`-truncated simplicial
object out of a degree-`M + 1` object together with a face family and a degeneracy family. This
file joins the two: it turns such a covering into the face half of the extension data, and it shows
that the resulting extension is again a truncated hypercovering by objects of `B`.

Three things are proved, and the third is the one that was missing.

* The face family of the extension data is `coskFace Y u`, the family cut out by `u` from the cone
  legs of the matching object. `CoskExtensionData` packages extension data of exactly that shape,
  and `CoskExtensionData.ofFac` transports it along a factorization `s ≫ u = v` of its morphism to
  the matching object -- which is the shape in which `exists_isCoveringOver_objects_in` delivers
  its covering, so this is what lets the degeneracy family be built against the *degenerate part*
  `v` and then pushed forward to the *covering* `u`.
* `ExtensionData.truncCoskUnitTop_extend` identifies the canonical morphism of the extension in
  degree `M + 1` with `u` itself, up to the transports coming from `ExtensionData.trunc_extend`.
  The identification is forced, not chosen: the cone legs of the matching object are jointly monic
  (`hom_ext_of_coskFace`) and the two morphisms cut out the same face family.
* `trunc_map_truncCoskUnit` says the canonical morphism to a coskeleton commutes with truncation,
  so the clauses of `IsTruncatedHypercoveringOver` in degrees below `M + 1` are inherited by the
  extension from `Y`. Together with the previous item this gives
  `isTruncatedHypercoveringOver_extend`: the extension is an `(M + 1)`-truncated hypercovering by
  objects of `B` as soon as `u` is covering and the summands of its source lie in `B`.

**What is still missing** is the *degeneracy* family of the specific covering, i.e. a term of
`CoskExtensionData Y` (equivalently, the `degenEpi` field alone, since the face half is `coskFace`
and the two laws involving it are proved here). The source builds it from the degenerate part of
degree `M + 1` being *free* on the surjections `⦋M + 1⦌ ↠ ⦋m⦌`, indexed by the nondegenerate
indices in degree `m`; that needs the Eilenberg-Zilber normal form of the index simplicial set
together with the splitness of `Y` in the sense of
[Stacks, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU), and it is not done here. See
`CategoryTheory.SimplicialObject.Truncated.ExtensionData.degen_sigma_eq_degen_sigma` for the
reason splitness cannot be dispensed with. Accordingly no declaration here carries the tag `0DAV`.

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.CoskExtensionData`: one-step extension data for an
  `M`-truncated simplicial object whose face family is the one cut out by a morphism into the
  matching object, so that only the degeneracy family along epimorphisms has to be supplied.
* `CategoryTheory.SimplicialObject.Truncated.CoskExtensionData.ofFac`: such data transported along
  a factorization of its morphism to the matching object.
* `CategoryTheory.SimplicialObject.Truncated.CoskExtensionData.toEpiExtensionData`: the underlying
  epimorphism-only extension data, hence by
  `EpiExtensionData.toExtensionData` the full extension data and the extension itself.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.truncCoskUnitTop_extend`: the canonical
  morphism from the extension to the `M`-th coskeleton of its `M`-truncation is, in degree
  `M + 1`, the morphism the face family was built from.
* `CategoryTheory.SimplicialObject.Truncated.trunc_map_truncCoskUnit` and
  `truncCoskUnit_app_eq_of_trunc_eq`: the canonical morphism to a coskeleton commutes with
  truncation, in functor form and in the componentwise form a consumer uses.
* `Stacks.CategoryTheory.Hypercovering.isTruncatedHypercoveringOver_extend`: the one-step
  extension of a truncated hypercovering by objects of `B` along a covering of the matching
  object is again one.
* `Stacks.CategoryTheory.Hypercovering.exists_hypercovering_of_objects_in_of_extensionData`:
  Tag 0DAV granted only the degeneracy family, with an auxiliary invariant `Q` carried along the
  induction. `Q` is a parameter rather than a fixed predicate because the invariant the source
  uses is splitness, which is not part of `IsTruncatedHypercoveringOver`.

## Implementation notes

`ExtensionData.obj` is a dependent `if`, so the degree-`a` term of the extension is only *equal*
to the corresponding term of `Y`, never identical to it; and `ExtensionData.trunc_extend` is an
equality of functors. Both transports are handled by `subst`-style lemmas
(`coskFace_comp_eqToHom`, `truncCoskUnit_app_eq_of_trunc_eq`, `isCoveringOver_of_eq`,
`obj_left_mem_of_eq`, `isCoveringOver_terminal_from_of_eq`) which generalise the second functor or
object and then substitute, rather than by rewriting under `eqToHom`. This is deliberate: the
targets of `truncCoskUnitTop h D.extend` and of `u` are definitionally equal without being
syntactically equal, which is exactly the situation in which `rw` and `simp` refuse with a message
naming a pattern rather than the cause.

`trunc_map_truncCoskUnit` is proved from the uniqueness of lifts through a right Kan extension and
needs its `F'` and `α` arguments given explicitly: the natural type of the counit is an extension
along `(inclusion n).op` whereas the statement needs it read along `(incl n M).op`, and the two are
definitionally equal without being syntactically equal, so instance synthesis gets stuck on
metavariables unless both are pinned.

Like `ObjectsMatching.lean`, the first half of this file mentions no site and belongs with the
truncated simplicial object material; it sits here only because `truncCoskUnit` does. No universe
is narrowed: `A : Type u` with `[Category.{v} A]`, and `C : Type u` with `[Category.{v} C]` and a
free index universe `w` for the formal coproducts, as in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.Objects`.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
* [Stacks Project, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)
* [Stacks Project, Tag 0187](https://stacks.math.columbia.edu/tag/0187)
* [Stacks Project, Tag 01G3](https://stacks.math.columbia.edu/tag/01G3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject

universe w v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] {M : ℕ}

/-- The action of a one-step extension on a morphism from an `M`-truncated object into degree
`M + 1` is the face family, conjugated by the two object identifications of
`ExtensionData.obj`. -/
theorem ExtensionData.extend_map_homMk {Y : SimplicialObject.Truncated A M} (D : ExtensionData Y)
    (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌) :
    D.extend.map (ObjectProperty.homMk
        (X := (⟨x.obj, x.property.trans (Nat.le_succ M)⟩ : SimplexCategory.Truncated (M + 1)))
        (Y := ⟨⦋M + 1⦌, le_rfl⟩) m).op
      = eqToHom D.extend_obj_mk ≫ D.face x m
        ≫ eqToHom (D.obj_of_le (x := ⟨x.obj, x.property.trans (Nat.le_succ M)⟩)
            x.property).symm := by
  rw [D.extend_map, D.map_of_le_not_le _ _ _ x.property (by change ¬ M + 1 ≤ M; omega)]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

section Cosk

variable [∀ F : (SimplexCategory.Truncated M)ᵒᵖ ⥤ A,
  (SimplexCategory.Truncated.inclusion M).op.HasRightKanExtension F]

/-- Precomposing a morphism into the matching object before cutting out its face family is cutting
out the face family of the composite. -/
theorem comp_coskFace (Y : SimplicialObject.Truncated A M) {P Q : A} (s : Q ⟶ P)
    (u : P ⟶ matchingObj Y) (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌) :
    s ≫ coskFace Y u x m = coskFace Y (s ≫ u) x m := by
  simp only [coskFace, Category.assoc]

/-- The face family cut out by a morphism into the matching object is unchanged by transporting
that morphism along an equality of truncated simplicial objects, up to the induced identification
of the targets. -/
theorem coskFace_comp_eqToHom {Y Y' : SimplicialObject.Truncated A M} (h : Y = Y') {P : A}
    (u : P ⟶ matchingObj Y) (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌) :
    coskFace Y' (u ≫ eqToHom (congrArg matchingObj h)) x m
      = coskFace Y u x m ≫ eqToHom (Functor.congr_obj h (op x)) := by
  subst h
  simp

/-- One-step extension data for an `M`-truncated simplicial object `Y` in which the face family is
the one cut out by a morphism `toMatching` into the matching object and the degeneracy family is
prescribed only along the epimorphisms out of `⦋M + 1⦌`. This is the shape in which the data of a
one-step extension of a truncated hypercovering arises: `toMatching` is the covering of the
matching object and `degenEpi` carries the degeneracies. -/
structure CoskExtensionData (Y : SimplicialObject.Truncated A M) where
  /-- The object sitting in degree `M + 1`. -/
  pt : A
  /-- The morphism to the matching object out of which the whole face family is cut. -/
  toMatching : pt ⟶ matchingObj Y
  /-- The degeneracy data, prescribed only along the epimorphisms out of `⦋M + 1⦌`. -/
  degenEpi (x : SimplexCategory.Truncated M) (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] :
    Y.obj (op x) ⟶ pt
  /-- The degeneracy data is a cocone along the epimorphisms. -/
  degenEpi_comp (x y : SimplexCategory.Truncated M)
      (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] (g : x.obj ⟶ y.obj) [Epi g] :
    degenEpi y (e ≫ g) = Y.map (ObjectProperty.homMk g).op ≫ degenEpi x e
  /-- A face after a degeneracy along an epimorphism is computed inside `Y`. -/
  degenEpi_face (x y : SimplexCategory.Truncated M)
      (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) [Epi e] (m : y.obj ⟶ ⦋M + 1⦌) :
    degenEpi x e ≫ coskFace Y toMatching y m
      = Y.map (ObjectProperty.homMk (m ≫ e)).op

namespace CoskExtensionData

variable {Y : SimplicialObject.Truncated A M}

/-- The epimorphism-only one-step extension data underlying `CoskExtensionData`: the face family
is the one cut out by `toMatching`, and its cone law is `coskFace_comp`. -/
noncomputable def toEpiExtensionData (D : CoskExtensionData Y) : EpiExtensionData Y where
  pt := D.pt
  face := coskFace Y D.toMatching
  degenEpi := D.degenEpi
  face_comp := coskFace_comp Y D.toMatching
  degenEpi_comp := D.degenEpi_comp
  degenEpi_face := D.degenEpi_face

/-- **Transport of extension data along a factorization.** If the morphism to the matching object
of `D` factors as `s ≫ u`, then `u` carries extension data on the source of `u`, with the same
degeneracies followed by `s`. In the one-step extension of a truncated hypercovering the
degeneracy family is naturally built on the *degenerate part* `D.pt`, with `D.toMatching` the
morphism recording the degeneracies, while the clause to be verified is about the *covering* `u`;
this is what moves the data from the former to the latter. -/
noncomputable def ofFac (D : CoskExtensionData Y) {P : A} (s : D.pt ⟶ P)
    (u : P ⟶ matchingObj Y) (hsu : s ≫ u = D.toMatching) : CoskExtensionData Y where
  pt := P
  toMatching := u
  degenEpi x e := D.degenEpi x e ≫ s
  degenEpi_comp := by
    intro x y e _ g _
    rw [D.degenEpi_comp x y e g, Category.assoc]
  degenEpi_face := by
    intro x y e _ m
    rw [Category.assoc, comp_coskFace Y s u y m, hsu, D.degenEpi_face x y e m]

end CoskExtensionData

end Cosk

section Pointwise

variable [∀ (k : ℕ) (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A),
  (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]

/-- **The canonical morphism of a one-step extension is the morphism its faces came from.** If the
face family of `D` is the one cut out by `u : D.pt ⟶ matchingObj Y`, then the degree-`M + 1`
component of the canonical morphism from `D.extend` to the `M`-th coskeleton of its `M`-truncation
is `u`, conjugated by the identification of the degree-`M + 1` term of `D.extend` with `D.pt` and
by the identification of the two matching objects coming from `ExtensionData.trunc_extend`. The
cone legs of the matching object are jointly monic, so nothing is chosen here. -/
theorem ExtensionData.truncCoskUnitTop_extend {Y : SimplicialObject.Truncated A M}
    (D : ExtensionData Y) (u : D.pt ⟶ matchingObj Y)
    (hface : ∀ (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
      D.face x m = coskFace Y u x m) :
    truncCoskUnitTop (Nat.le_succ M) D.extend
      = eqToHom D.extend_obj_mk ≫ u
        ≫ eqToHom (congrArg matchingObj D.trunc_extend.symm) := by
  refine hom_ext_of_coskFace _ fun x m ↦ ?_
  rw [coskFace_truncCoskUnitTop, ← comp_coskFace, coskFace_comp_eqToHom D.trunc_extend.symm u x m,
    D.extend_map_homMk x m, hface x m]
  rfl

/-- **The canonical morphism to a coskeleton commutes with truncation.** Truncating the canonical
morphism from an `(M + 1)`-truncated simplicial object to the `n`-th coskeleton of its
`n`-truncation gives the canonical morphism of its `M`-truncation. Both sides lift the identity
through the same right Kan extension. -/
theorem trunc_map_truncCoskUnit {n M : ℕ} (hnM : n ≤ M) (hM : M ≤ M + 1) (hn : n ≤ M + 1)
    (Z : SimplicialObject.Truncated A (M + 1)) :
    (Truncated.trunc A (M + 1) M hM).map (truncCoskUnit hn Z)
      = truncCoskUnit hnM ((Truncated.trunc A (M + 1) M hM).obj Z) := by
  have := isRightKanExtension_truncation_cosk hnM
    ((Truncated.trunc A M n hnM).obj ((Truncated.trunc A (M + 1) M hM).obj Z))
  refine Functor.hom_ext_of_isRightKanExtension
    (L := (SimplexCategory.Truncated.incl n M hnM).op)
    ((Truncated.cosk n ⋙ truncation M).obj
      ((Truncated.trunc A M n hnM).obj ((Truncated.trunc A (M + 1) M hM).obj Z)))
    ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app
      ((Truncated.trunc A M n hnM).obj ((Truncated.trunc A (M + 1) M hM).obj Z))) _ _ ?_
  rw [truncCoskUnit_fac hnM]
  exact truncCoskUnit_fac hn Z

/-- The componentwise form of `trunc_map_truncCoskUnit` at an `M`-truncated object. -/
theorem truncCoskUnit_app_trunc {n M : ℕ} (hnM : n ≤ M) (hM : M ≤ M + 1) (hn : n ≤ M + 1)
    (Z : SimplicialObject.Truncated A (M + 1)) (x : SimplexCategory.Truncated M) :
    (truncCoskUnit hn Z).app (op ⟨x.obj, x.property.trans hM⟩)
      = (truncCoskUnit hnM ((Truncated.trunc A (M + 1) M hM).obj Z)).app (op x) :=
  congrArg (fun t ↦ NatTrans.app t (op x)) (trunc_map_truncCoskUnit hnM hM hn Z)

/-- `truncCoskUnit_app_trunc` with the `M`-truncation of `Z` identified with a given `M`-truncated
simplicial object. This is the form a consumer of `ExtensionData.trunc_extend` uses: the
identification is an equality of functors, so both the source and the target of the component have
to be transported. -/
theorem truncCoskUnit_app_eq_of_trunc_eq {n M : ℕ} (hnM : n ≤ M) (hM : M ≤ M + 1) (hn : n ≤ M + 1)
    (Z : SimplicialObject.Truncated A (M + 1)) {Y : SimplicialObject.Truncated A M}
    (hY : (Truncated.trunc A (M + 1) M hM).obj Z = Y) (x : SimplexCategory.Truncated M) :
    (truncCoskUnit hn Z).app (op ⟨x.obj, x.property.trans hM⟩)
      = eqToHom (Functor.congr_obj hY (op x))
        ≫ (truncCoskUnit hnM Y).app (op x)
        ≫ eqToHom (Functor.congr_obj (congrArg (fun W ↦ (Truncated.cosk n ⋙ truncation M).obj
            ((Truncated.trunc A M n hnM).obj W)) hY) (op x)).symm := by
  subst hY
  rw [truncCoskUnit_app_trunc hnM hM hn Z x]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end Pointwise

end CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Being a covering morphism of semi-representable objects is invariant under conjugating by
identifications of the source and the target. -/
theorem isCoveringOver_of_eq (J : Pretopology C) {X : C}
    {U U' V V' : FormalCoproduct.{w} (Over X)} (hU : U = U') (hV : V' = V) {f : U' ⟶ V'}
    (hf : IsCoveringOver J f) : IsCoveringOver J (eqToHom hU ≫ f ≫ eqToHom hV) := by
  subst hU hV
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hf

omit [HasPullbacks C] in
/-- Membership of the underlying objects of the summands in a prescribed collection transports
along an identification of semi-representable objects. -/
theorem obj_left_mem_of_eq {X : C} (B : Set C) {U V : FormalCoproduct.{w} (Over X)} (h : U = V)
    (hV : ∀ i : V.I, (V.obj i).left ∈ B) (i : U.I) : (U.obj i).left ∈ B := by
  subst h
  exact hV i

/-- The covering clause for the morphism to the terminal object transports along an identification
of semi-representable objects. -/
theorem isCoveringOver_terminal_from_of_eq (J : Pretopology C) {X : C}
    {U V : FormalCoproduct.{w} (Over X)} (h : U = V)
    (hV : IsCoveringOver J (terminal.from V)) : IsCoveringOver J (terminal.from U) := by
  subst h
  exact hV

/-- **The one-step extension of a truncated hypercovering by objects of `B`.** Let `Y` be an
`M`-truncated hypercovering of `X` by objects of `B` and let `D` be one-step extension data for
`Y` whose face family is the one cut out by a morphism `u` into the matching object. If `u` is a
covering and the summands of its source lie in `B`, then the extension `D.extend` is an
`(M + 1)`-truncated hypercovering of `X` by objects of `B`; its `M`-truncation is `Y` on the nose
by `ExtensionData.trunc_extend`.

The clauses below degree `M + 1` are inherited from `Y` because the canonical morphism to a
coskeleton commutes with truncation, and the clause in degree `M + 1` is the hypothesis on `u`
because the canonical morphism of the extension *is* `u` there. -/
theorem isTruncatedHypercoveringOver_extend (J : Pretopology C) (B : Set C)
    {X : C} {M : ℕ} {Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M}
    (hY : IsTruncatedHypercoveringOver.{w} J B M Y) (D : ExtensionData Y)
    (u : D.pt ⟶ matchingObj Y)
    (hface : ∀ (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
      D.face x m = coskFace Y u x m)
    (hBD : ∀ i : D.pt.I, (D.pt.obj i).left ∈ B) (hu : IsCoveringOver J u) :
    IsTruncatedHypercoveringOver.{w} J B (M + 1) D.extend := by
  refine ⟨?_, ?_, ?_⟩
  · intro a i
    by_cases ha : a.unop.obj.len ≤ M
    · exact obj_left_mem_of_eq B (D.obj_of_le ha) (fun i ↦ hY.1 (op ⟨a.unop.obj, ha⟩) i) i
    · exact obj_left_mem_of_eq B (D.obj_of_not_le ha) hBD i
  · exact isCoveringOver_terminal_from_of_eq J
      (D.obj_of_le (x := ⟨⦋0⦌, Nat.zero_le (M + 1)⟩) (Nat.zero_le M)) hY.2.1
  · intro n hn
    rcases Nat.lt_or_ge n M with hlt | hge
    · have hn' : n + 1 ≤ M := by omega
      rw [truncCoskUnit_app_eq_of_trunc_eq (Nat.le_of_succ_le hn') (Nat.le_succ M)
        (Nat.le_of_succ_le hn) D.extend D.trunc_extend ⟨⦋n + 1⦌, hn'⟩]
      exact isCoveringOver_of_eq J _ _ (hY.2.2 n hn')
    · obtain rfl : M = n := by omega
      have key : (truncCoskUnit (Nat.le_of_succ_le hn) D.extend).app (op ⟨⦋M + 1⦌, hn⟩)
          = eqToHom D.extend_obj_mk ≫ u
            ≫ eqToHom (congrArg matchingObj D.trunc_extend.symm) :=
        D.truncCoskUnitTop_extend u hface
      rw [key]
      exact isCoveringOver_of_eq J _ _ hu

/-- `isTruncatedHypercoveringOver_extend` for data in the packaged form `CoskExtensionData`, where
the face family is `coskFace` by construction. -/
theorem isTruncatedHypercoveringOver_extend_coskExtensionData (J : Pretopology C) (B : Set C)
    {X : C} {M : ℕ} {Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M}
    (hY : IsTruncatedHypercoveringOver.{w} J B M Y) (D : CoskExtensionData Y)
    (hBD : ∀ i : D.pt.I, (D.pt.obj i).left ∈ B)
    (hu : IsCoveringOver J D.toMatching) :
    IsTruncatedHypercoveringOver.{w} J B (M + 1)
      D.toEpiExtensionData.toExtensionData.extend :=
  isTruncatedHypercoveringOver_extend J B hY D.toEpiExtensionData.toExtensionData
    D.toMatching (fun _ _ ↦ rfl) hBD hu

/-- **Stacks Project, Tag 0DAV**, granted only the degeneracy family of the one-step extension. If
the objects of `B` cover every object of the site and every truncated hypercovering of `X` by
objects of `B` satisfying an auxiliary invariant `Q` admits one-step extension data whose face
family comes from a covering of the matching object by objects of `B` and which propagates `Q`,
then `X` admits a hypercovering all of whose summands lie in `B`.

The auxiliary invariant is a parameter because the invariant the source carries through this
induction is *splitness*
([Stacks, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)), which is not part of
`IsTruncatedHypercoveringOver` and which the degeneracy family genuinely needs: see
`CategoryTheory.SimplicialObject.Truncated.ExtensionData.degen_sigma_eq_degen_sigma`. Taking
`Q M _ = True` recovers the statement with no invariant. -/
theorem exists_hypercovering_of_objects_in_of_extensionData (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (X : C)
    (Q : (M : ℕ) → SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M → Prop)
    (base : ∀ Y₀ : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) 0,
      IsTruncatedHypercoveringOver.{w} J B 0 Y₀ → Q 0 Y₀)
    (step : ∀ (M : ℕ) (Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M),
      IsTruncatedHypercoveringOver.{w} J B M Y → Q M Y →
      ∃ (D : ExtensionData Y) (u : D.pt ⟶ matchingObj Y),
        (∀ (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
          D.face x m = coskFace Y u x m) ∧
          (∀ i : D.pt.I, (D.pt.obj i).left ∈ B) ∧ IsCoveringOver J u ∧ Q (M + 1) D.extend) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering J K ∧
        ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), ((K.obj (op ⦋n⦌)).obj i).left ∈ B := by
  obtain ⟨ι, V, f, hV, hf⟩ := hcover X
  obtain ⟨Y₀, hY₀⟩ := exists_isTruncatedHypercoveringOver_zero J B V f hV hf
  have hstep : ∀ (M : ℕ) (Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M),
      (IsTruncatedHypercoveringOver.{w} J B M Y ∧ Q M Y) →
      ∃ Z : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) (M + 1),
        (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} (Over X)) (M + 1) M).obj Z = Y ∧
          (IsTruncatedHypercoveringOver.{w} J B (M + 1) Z ∧ Q (M + 1) Z) := by
    intro M Y hY
    obtain ⟨D, u, hface, hBD, hu, hQ⟩ := step M Y hY.1 hY.2
    exact ⟨D.extend, D.trunc_extend,
      isTruncatedHypercoveringOver_extend J B hY.1 D u hface hBD hu, hQ⟩
  obtain ⟨K, hK⟩ := SimplicialObject.TruncatedTower.exists_simplicialObject_of_step
    (P := fun M Y ↦ IsTruncatedHypercoveringOver.{w} J B M Y ∧ Q M Y) Y₀
    ⟨hY₀, base Y₀ hY₀⟩ hstep
  refine ⟨K, ⟨(hK 0).1.2.1, fun n ↦ ?_⟩, fun n i ↦ (hK n).1.1 (op ⟨⦋n⦌, le_rfl⟩) i⟩
  have h := (hK (n + 1)).1.2.2 n le_rfl
  rwa [truncCoskUnit_app_eq_coskAdj_unit_app] at h

end Stacks.CategoryTheory.Hypercovering

end
