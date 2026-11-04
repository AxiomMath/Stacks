module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# `mapHomologyIso` for a composite of two functors

Let `S : ShortComplex C` and let `F : C ⥤ D` and `G : D ⥤ E` be functors preserving zero
morphisms, with `F` preserving the left homology of `S` and `G` the left homology of `S.map F`.
Mathlib provides the comparison isomorphism
`CategoryTheory.ShortComplex.mapHomologyIso : (S.map F).homology ≅ F.obj S.homology` and records
that it is natural in `S` (`CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality`), but
nothing relating the comparison for a composite `F ⋙ G` to the comparisons for `F` and for `G`.
This file supplies that composition law.

## Main results

* `CategoryTheory.Functor.preservesHomology_comp`: a composite of two functors which preserve
  homology preserves homology, which is what makes the hypotheses below available at a use site.
* `CategoryTheory.ShortComplex.mapHomologyIso_comp_inv`:
  `(S.mapHomologyIso (F ⋙ G)).inv = G.map (S.mapHomologyIso F).inv ≫
  ((S.map F).mapHomologyIso G).inv`.
* `CategoryTheory.ShortComplex.mapHomologyIso_comp_hom`: the same identity read on `hom`.
* `CategoryTheory.ShortComplex.mapHomologyIso_glue`: **the composition law and the naturality
  composed**, in the one arrangement a square of two homology comparisons reduces to. For
  `a : S' ⟶ S''` and a retraction pair `b : S'' ⟶ S.map R`, `b' : S.map R ⟶ S''` with
  `b ≫ b' = 𝟙`,

  > `P(H(a)) ≫ P(H(b)) ≫ P((S.mapHomologyIso R).hom) ≫ (S.mapHomologyIso (R ⋙ P)).inv ≫
  > H(P(b')) = (S'.mapHomologyIso P).inv ≫ H(P(a))`.

  Only the pointwise hypotheses are asked — `R` on `S`, `R ⋙ P` on `S`, `P` on `S.map R` and
  `P` on `S'` — and in particular no exactness of `P`.
* `CategoryTheory.ShortComplex.preservesLeftHomologyOf_map`: for `R` preserving homology, the
  pointwise hypothesis on `R ⋙ P` at `S` gives the one on `P` at `S.map R`, so a consumer of the
  two statements above need only supply the hypothesis on the composite.
* `CategoryTheory.ShortComplex.preservesLeftHomologyOf_comp`: the opposite direction — for `P`
  preserving homology, the pointwise hypothesis on `G` at `S` gives the one on `G ⋙ P` at `S`.
* `CategoryTheory.ShortComplex.mapHomologyIso_inv_natTrans`: **the comparison is natural in the
  *functor*.** For `τ : P ⟶ Q` between functors preserving the left homology of `S`,

  > `τ.app S.homology ≫ (S.mapHomologyIso Q).inv =
  > (S.mapHomologyIso P).inv ≫ homologyMap (S.mapNatTrans τ)`.

  Mathlib packages naturality only in the short complex; this is the functor-variable companion
  of `CategoryTheory.ShortComplex.mapHomologyIso_inv_naturality`, and it is the hinge of a square
  comparing two readings of homology across a change of the functor.

## Implementation notes

`S.mapHomologyIso F` is by definition `(S.homologyData.left.map F).homologyIso`, so the
composition law is an identity between the homology isomorphisms attached to the two left
homology data `S.homologyData.left.map (F ⋙ G)` and `(S.homologyData.left.map F).map G` of the
short complex `S.map (F ⋙ G)`.  These two data have the same underlying objects and maps but
are built from different limit and colimit data, so they are not equal; what identifies their
homology isomorphisms is the `CategoryTheory.ShortComplex.LeftHomologyMapData` for the identity
of `S.map (F ⋙ G)` whose two components are identities, through
`CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_comm`.

This is Mathlib-level infrastructure about Mathlib-only notions and belongs upstream, next to
`CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality` in
`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`.

`mapHomologyIso_inv_natTrans` is read off Mathlib's
`CategoryTheory.ShortComplex.LeftHomologyMapData.natTransApp`, the left homology map data for
`S.mapNatTrans τ` obtained by evaluating `τ`, whose `φH` is `τ` at the homology.  Mathlib's own
`CategoryTheory.ShortComplex.homologyMap_mapNatTrans` is that datum's `homologyMap_eq` and is
stated in a section carrying the hypotheses that `P` and `Q` preserve the **right** homology of
`S` as well as the left; only the left ones are used, and only the left ones are available where
the second functor is sections over an affine open, so the identity is taken from
`natTransApp` directly here.  The companion statement under exactness of both functors is
`CategoryTheory.ShortComplex.mapHomologyIso_hom_natTrans`
(`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequenceSecondPage.lean`), read on `hom`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

/-- The image of `parallelPair f 0` under `F` is `parallelPair (F.map f) 0`. -/
private def parallelPairCompIso {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {X Y : C} (f : X ⟶ Y) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] : parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- A composite of two functors which preserve homology preserves homology: the first functor
carries the kernel and the cokernel of a parallel pair to the kernel and the cokernel of the
image parallel pair, which the second functor then preserves.

This is the hypothesis `[(G ⋙ G').PreservesHomology]` that the composition laws below and in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeComparisonTransitivity.lean`
have to assume; Mathlib provides no instance for it, because `PreservesFiniteLimits` and
`PreservesFiniteColimits` are not closed under composition by instance search
(`CategoryTheory.Limits.comp_preservesFiniteLimits` is a lemma). -/
lemma preservesHomology_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E] (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] : (F ⋙ G).PreservesHomology where
  preservesKernels {X Y} f := by
    have : PreservesLimit (parallelPair f 0) F := PreservesHomology.preservesKernel F f
    have : PreservesLimit (parallelPair (F.map f) 0) G := PreservesHomology.preservesKernel G _
    have : PreservesLimit (parallelPair f 0 ⋙ F) G :=
      preservesLimit_of_iso_diagram G (parallelPairCompIso f F).symm
    exact comp_preservesLimit F G
  preservesCokernels {X Y} f := by
    have : PreservesColimit (parallelPair f 0) F := PreservesHomology.preservesCokernel F f
    have : PreservesColimit (parallelPair (F.map f) 0) G :=
      PreservesHomology.preservesCokernel G _
    have : PreservesColimit (parallelPair f 0 ⋙ F) G :=
      preservesColimit_of_iso_diagram G (parallelPairCompIso f F).symm
    exact comp_preservesColimit F G

end Functor

namespace ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [S.HasHomology] [(S.map F).HasHomology] [(S.map (F ⋙ G)).HasHomology]
  [((S.map F).map G).HasHomology]
  [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)]
  [(F ⋙ G).PreservesLeftHomologyOf S]

omit [(S.map F).HasHomology] in
/-- The homology isomorphism of the left homology data `S.homologyData.left.map (F ⋙ G)` of
`S.map (F ⋙ G)` agrees with that of `(S.homologyData.left.map F).map G`: the two data differ
only in their limit and colimit data, and the identity of `S.map (F ⋙ G)` is a left homology
map between them whose components are identities. -/
private theorem homologyIso_map_comp_hom :
    (S.homologyData.left.map (F ⋙ G)).homologyIso.hom =
      ((S.homologyData.left.map F).map G).homologyIso.hom := by
  let d : LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      (S.homologyData.left.map (F ⋙ G)) ((S.homologyData.left.map F).map G) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := (id_comp _).trans (comp_id _).symm
      commf' := by
        rw [LeftHomologyData.map_f', LeftHomologyData.map_f', LeftHomologyData.map_f']
        exact (comp_id _).trans (id_comp _).symm
      commπ := (comp_id _).trans (id_comp _).symm }
  have hcomm := d.homologyMap_comm
  rw [homologyMap_id, id_comp] at hcomm
  exact (comp_id _).symm.trans hcomm.symm

/-- **The composition law for `ShortComplex.mapHomologyIso`.**  The comparison between the
homology of `S.map (F ⋙ G)` and the image of the homology of `S` under `F ⋙ G` is the
comparison for `F`, pushed forward by `G`, followed by the comparison for `G` at `S.map F`. -/
theorem mapHomologyIso_comp_inv :
    (S.mapHomologyIso (F ⋙ G)).inv =
      G.map (S.mapHomologyIso F).inv ≫ ((S.map F).mapHomologyIso G).inv := by
  have hgoal : (S.mapHomologyIso (F ⋙ G)).inv =
      ((S.homologyData.left.map F).map G).homologyIso.inv :=
    (Iso.inv_eq_inv _ _).2 (homologyIso_map_comp_hom S F G)
  have hinv : ((S.map F).mapHomologyIso G).inv =
      G.map (S.homologyData.left.map F).homologyIso.hom ≫
        ((S.homologyData.left.map F).map G).homologyIso.inv :=
    congrArg Iso.inv ((S.homologyData.left.map F).mapHomologyIso_eq G)
  have hid : G.map (S.mapHomologyIso F).inv ≫
      G.map (S.homologyData.left.map F).homologyIso.hom =
      𝟙 (G.obj (S.homologyData.left.map F).H) :=
    (G.map_comp _ _).symm.trans
      ((congrArg G.map (S.homologyData.left.map F).homologyIso.inv_hom_id).trans (G.map_id _))
  refine hgoal.trans (Eq.trans ?_
    (congrArg (fun m => G.map (S.mapHomologyIso F).inv ≫ m) hinv).symm)
  exact ((congrArg (fun m => m ≫ ((S.homologyData.left.map F).map G).homologyIso.inv)
      hid).trans (id_comp _)).symm.trans (assoc _ _ _)

/-- **The composition law for `ShortComplex.mapHomologyIso`, read on `hom`.** -/
theorem mapHomologyIso_comp_hom :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  rw [← Iso.inv_comp_eq, ← Iso.eq_comp_inv, mapHomologyIso_comp_inv S F G,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, id_comp]

end ShortComplex

namespace ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  (S : ShortComplex C) (R : C ⥤ D) (P : D ⥤ E)
  [R.PreservesZeroMorphisms] [P.PreservesZeroMorphisms]
  {S' S'' : ShortComplex D} (a : S' ⟶ S'') (b : S'' ⟶ S.map R) (b' : S.map R ⟶ S'')

/-- **A pointwise homology hypothesis moves across a composition.** If `R` preserves homology and
`R ⋙ P` preserves the left homology of `S`, then `P` preserves the left homology of `S.map R`.

This is what makes the pointwise hypotheses of `mapHomologyIso_comp_inv` and of
`mapHomologyIso_glue` available from the hypothesis on the composite alone: a consumer who knows
only that `R ⋙ P` preserves the left homology of `S` — which is the shape Grothendieck's collapse
at the pair `(F, R ⋙ P)` asks for — does not have to inhabit the hypothesis at the intermediate
short complex separately.

The content is the converse direction of `CategoryTheory.Limits.comp_preservesLimit`: `R` carries
the kernel fork of `S.g` to a limit fork, `R ⋙ P` carries it to a limit fork, and
`CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` turns the pair into preservation by
`P` of the limit of the *image* diagram. The two diagram isomorphisms
`parallelPair φ 0 ⋙ R ≅ parallelPair (R.map φ) 0` are the ones `preservesHomology_comp` above also
uses. -/
lemma preservesLeftHomologyOf_map {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (S : ShortComplex C) (R : C ⥤ D) (P : D ⥤ E)
    [R.PreservesZeroMorphisms] [P.PreservesZeroMorphisms] [R.PreservesHomology]
    [S.HasLeftHomology] [(R ⋙ P).PreservesLeftHomologyOf S] :
    P.PreservesLeftHomologyOf (S.map R) := by
  have h := S.leftHomologyData
  have : PreservesLimit (parallelPair S.g 0) R :=
    Functor.PreservesHomology.preservesKernel R S.g
  have : PreservesColimit (parallelPair h.f' 0) R :=
    Functor.PreservesHomology.preservesCokernel R h.f'
  have : PreservesLimit (parallelPair S.g 0) (R ⋙ P) :=
    LeftHomologyData.IsPreservedBy.hg h (R ⋙ P)
  have : PreservesColimit (parallelPair h.f' 0) (R ⋙ P) :=
    LeftHomologyData.IsPreservedBy.hf' h (R ⋙ P)
  have : (h.map R).IsPreservedBy P := by
    refine { g := ?_, f' := ?_ }
    · have : PreservesLimit (parallelPair S.g 0 ⋙ R) P :=
        preservesLimit_of_preserves_limit_cone (isLimitOfPreserves R h.hi)
          (isLimitOfPreserves (R ⋙ P) h.hi)
      exact preservesLimit_of_iso_diagram P (Functor.parallelPairCompIso S.g R)
    · rw [LeftHomologyData.map_f' h R]
      have : PreservesColimit (parallelPair h.f' 0 ⋙ R) P :=
        preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves R h.hπ')
          (isColimitOfPreserves (R ⋙ P) h.hπ')
      exact preservesColimit_of_iso_diagram P (Functor.parallelPairCompIso h.f' R)
  exact Functor.PreservesLeftHomologyOf.mk' P (h.map R)

/-- **A pointwise homology hypothesis survives postcomposition with an exact functor.** If `G`
preserves the left homology of `S` and `P` preserves homology, then so does `G ⋙ P`.

This is the direction opposite to `preservesLeftHomologyOf_map`, and it is what makes the
hypotheses of `mapHomologyIso_comp_inv` and of Grothendieck's collapse at the pair `(F, G ⋙ P)`
available from the hypothesis on `G` alone: a consumer who has the pointwise hypothesis for
sections over an affine open, and reads the result over another ring by an exact restriction of
scalars, does not have to inhabit it again at the composite.

Mathlib provides no instance: `CategoryTheory.Limits.comp_preservesLimit` is a lemma, so the two
preservation hypotheses the left homology datum asks for have to be composed by hand, through the
diagram isomorphisms `parallelPair φ 0 ⋙ G ≅ parallelPair (G.map φ) 0` that
`CategoryTheory.Functor.preservesHomology_comp` above also uses. -/
lemma preservesLeftHomologyOf_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (S : ShortComplex C) (G : C ⥤ D) (P : D ⥤ E)
    [G.PreservesZeroMorphisms] [P.PreservesZeroMorphisms] [P.PreservesHomology]
    [S.HasLeftHomology] [G.PreservesLeftHomologyOf S] :
    (G ⋙ P).PreservesLeftHomologyOf S := by
  have h := S.leftHomologyData
  have : PreservesLimit (parallelPair S.g 0) G := LeftHomologyData.IsPreservedBy.hg h G
  have : PreservesColimit (parallelPair h.f' 0) G := LeftHomologyData.IsPreservedBy.hf' h G
  have : PreservesLimit (parallelPair S.g 0 ⋙ G) P := by
    have : PreservesLimit (parallelPair (G.map S.g) 0) P :=
      Functor.PreservesHomology.preservesKernel P _
    exact preservesLimit_of_iso_diagram P (Functor.parallelPairCompIso S.g G).symm
  have : PreservesColimit (parallelPair h.f' 0 ⋙ G) P := by
    have : PreservesColimit (parallelPair (G.map h.f') 0) P :=
      Functor.PreservesHomology.preservesCokernel P _
    exact preservesColimit_of_iso_diagram P (Functor.parallelPairCompIso h.f' G).symm
  have : h.IsPreservedBy (G ⋙ P) :=
    { g := comp_preservesLimit G P
      f' := comp_preservesColimit G P }
  exact Functor.PreservesLeftHomologyOf.mk' (G ⋙ P) h

/-- **The composition law and the naturality of `CategoryTheory.ShortComplex.mapHomologyIso`,
composed.** Let `a : S' ⟶ S''` be a map of short complexes of `D`, and let
`b : S'' ⟶ S.map R`, `b' : S.map R ⟶ S''` be a retraction pair, `b ≫ b' = 𝟙 S''`. Then

> `P(H(a)) ≫ P(H(b)) ≫ P((S.mapHomologyIso R).hom) ≫ (S.mapHomologyIso (R ⋙ P)).inv ≫
> H(P(b'))` is `(S'.mapHomologyIso P).inv ≫ H(P(a))`.

This is the arrangement a square comparing two readings of homology across a change of functors
reduces to: the composition law `mapHomologyIso_comp_inv` collapses the two middle factors to
`((S.map R).mapHomologyIso P).inv`, Mathlib's `mapHomologyIso_inv_naturality` at `a ≫ b` moves
it past the two leading factors, and `b ≫ b' = 𝟙` cancels what is left.

Only the **pointwise** homology hypotheses are asked — `R` on `S`, `R ⋙ P` on `S`, `P` on
`S.map R` and `P` on `S'`. Nothing of `P` beyond preservation of zero morphisms, and in
particular no exactness: that is what makes the statement available where the second functor is
sections over an affine open, which is not exact. -/
theorem mapHomologyIso_glue
    [S.HasHomology] [(S.map R).HasHomology] [(S.map (R ⋙ P)).HasHomology]
    [((S.map R).map P).HasHomology] [S'.HasHomology] [S''.HasHomology]
    [(S'.map P).HasHomology] [(S''.map P).HasHomology]
    [R.PreservesLeftHomologyOf S] [P.PreservesLeftHomologyOf (S.map R)]
    [(R ⋙ P).PreservesLeftHomologyOf S] [P.PreservesLeftHomologyOf S']
    (hb : b ≫ b' = 𝟙 S'') :
    P.map (homologyMap a) ≫ P.map (homologyMap b) ≫ P.map (S.mapHomologyIso R).hom ≫
        (S.mapHomologyIso (R ⋙ P)).inv ≫
        @homologyMap _ _ _ ((S.map R).map P) (S''.map P) (P.mapShortComplex.map b') _ _ =
      (S'.mapHomologyIso P).inv ≫
        @homologyMap _ _ _ (S'.map P) (S''.map P) (P.mapShortComplex.map a) _ _ := by
  have hcomp : P.map (S.mapHomologyIso R).hom ≫ (S.mapHomologyIso (R ⋙ P)).inv =
      ((S.map R).mapHomologyIso P).inv := by
    rw [mapHomologyIso_comp_inv S R P, ← P.map_comp_assoc, Iso.hom_inv_id, P.map_id, id_comp]
  have htail :
      @homologyMap _ _ _ (S'.map P) ((S.map R).map P) (P.mapShortComplex.map (a ≫ b)) _ _ ≫
        @homologyMap _ _ _ ((S.map R).map P) (S''.map P) (P.mapShortComplex.map b') _ _ =
      @homologyMap _ _ _ (S'.map P) (S''.map P) (P.mapShortComplex.map a) _ _ := by
    rw [← homologyMap_comp, ← Functor.map_comp, assoc, hb, comp_id]
  rw [← P.map_comp_assoc, ← homologyMap_comp, reassoc_of% hcomp, ← assoc,
    mapHomologyIso_inv_naturality (a ≫ b) P, assoc, htail]

end ShortComplex

namespace ShortComplex

/-- **`CategoryTheory.ShortComplex.mapHomologyIso` is natural in the functor.** For a natural
transformation `τ : P ⟶ Q` of functors preserving the left homology of `S`, the comparison of the
homology of the image with the image of the homology turns `τ` on homology into `τ` applied
degreewise to `S`:

> `τ.app S.homology ≫ (S.mapHomologyIso Q).inv =
> (S.mapHomologyIso P).inv ≫ homologyMap (S.mapNatTrans τ)`.

This is the functor-variable companion of `mapHomologyIso_inv_naturality`, and it is what a square
comparing two readings of homology across a change of the functor reduces to. Only the **left**
homology hypotheses are asked, and nothing of either functor beyond preservation of zero
morphisms — in particular no exactness, which is what makes the identity available where the
functors are sections over an affine open. -/
theorem mapHomologyIso_inv_natTrans {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (S : ShortComplex C) [S.HasHomology] {P Q : C ⥤ D}
    [P.PreservesZeroMorphisms] [Q.PreservesZeroMorphisms]
    [P.PreservesLeftHomologyOf S] [Q.PreservesLeftHomologyOf S]
    [(S.map P).HasHomology] [(S.map Q).HasHomology] (τ : P ⟶ Q) :
    τ.app S.homology ≫ (S.mapHomologyIso Q).inv =
      (S.mapHomologyIso P).inv ≫ homologyMap (S.mapNatTrans τ) := by
  have key : homologyMap (S.mapNatTrans τ) =
      (S.mapHomologyIso P).hom ≫ τ.app S.homology ≫ (S.mapHomologyIso Q).inv :=
    (LeftHomologyMapData.natTransApp S.homologyData.left τ).homologyMap_eq
  rw [key, Iso.inv_hom_id_assoc]

end ShortComplex

end CategoryTheory

end
