module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

/-!
# Stacks 0CPA: descending a morphism to the system of scheme-theoretic images

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms — an
`AlgebraicGeometry.Space.NoetherianLimitSystem`, Stacks 0CP6 — and let `f : X ⟶ Y` be a
morphism of algebraic spaces quasi-separated and of finite type over `B`. Let

```
X ⟶ W        Y ⟶ V
↓    ↓   and  ↓    ↓
B ⟶ B_{i₁}   B ⟶ B_{i₂}
```

be diagrams as in Stacks 0CP8, that is, `AlgebraicGeometry.Space.GoodDiagram`s `GX` and `GY`,
and let `X = lim_{i ≥ i₁} X_i` and `Y = lim_{i ≥ i₂} Y_i` be the limit descriptions of
Stacks 0CP9. Stacks 0CPA asserts that on a sufficiently late common tail `f` is the limit of a
morphism of the two inverse systems, and that such a morphism of inverse systems is unique on
all later tails.

Existence is the limit criterion for morphisms out of an inverse limit: `V ⟶ B_{i₂}` is
locally of finite presentation, being of finite type over a locally Noetherian algebraic space
(Stacks 06G4, part (1)), so the composite `X ⟶ Y ⟶ V` is already defined over a stage
`X_{i₀} ⟶ V`. For every later stage `i` the induced morphism `X_i ⟶ B_i ×_{B_{i₂}} V` then
factors through `Y_i`, because `Y_i` is the scheme-theoretic image of `Y ⟶ B_i ×_{B_{i₂}} V`
and `X_i` is the scheme-theoretic image of `X`: the inverse image of `Y_i` is a closed
subspace of `X_i` through which `X ⟶ X_i` factors, hence is all of `X_i` by the minimality of
the scheme-theoretic image, Stacks 082X.

Uniqueness is the companion half of the same limit criterion: two morphisms of systems
inducing `f` have components which agree after composing with the projection `X ⟶ X_i` and
after composing with `V ⟶ B_{i₂}`, so they agree after one transition morphism.

## Main definitions

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism` is a morphism `(f_i)_{i ≥ i₀}` of the
  image systems of two good diagrams on the common tail above a stage `i₀`, over the system
  `(B_i)_{i ≥ i₀}` and inducing a given morphism `f` in the limit.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.eq_top_of_range_imageCone_π_le`: a closed subspace of
  the scheme-theoretic image `X_{i'}` through which the factorization `X ⟶ X_{i'}` passes is
  all of `X_{i'}`.
* `AlgebraicGeometry.Space.GoodDiagram.exists_comp_stageImage_ι`: a morphism out of `X_{i'}`
  into a base-changed model of the second good diagram whose restriction to `X` is `f` followed
  by a stage map factors through the scheme-theoretic image `Y_{i''}`.
* `AlgebraicGeometry.Space.GoodDiagram.isLocallyOfFinitePresentation_modelMap`: the model of a
  good diagram is locally of finite presentation over its stage.
* `AlgebraicGeometry.Space.GoodDiagram.exists_systemMorphism` is **Stacks 0CPA, existence**:
  some common tail carries a morphism of the image systems inducing `f`.
* `AlgebraicGeometry.Space.GoodDiagram.eventually_eq_systemMorphism` is **Stacks 0CPA,
  eventual uniqueness**: two such morphisms of systems agree at every sufficiently late stage.

## Implementation notes

Both statements inherit the two hypotheses of the library's form of Stacks 0CP9,
`AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone`: that `X` is an algebraic space over
`S`, which Situation 0CP6 provides and which the good-diagram structure does not record, and
that the index type is small for the site. Neither is a hypothesis of the source; they are the
price of identifying `X` with the limit of its system of scheme-theoretic images.

Quasi-separatedness of `X` over `B` is a hypothesis of the source, and it is needed here for
the same reason: the members of the system of scheme-theoretic images of `X` must be
quasi-separated before the limit criterion applies to them, and a finite-type morphism to a
Noetherian algebraic space does not by itself have quasi-separated source. It enters in the
relative form of the source, `AlgebraicGeometry.Space.IsQuasiSeparated pX`, and is used
through
`AlgebraicGeometry.Space.GoodDiagram.imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated`.
Nothing is required of `Y` beyond the existence of the good diagram `GY`, since only the
system of `X` is used as a limit.

Uniqueness is proved by the injectivity half of the limit criterion for morphisms out of an
inverse limit, `AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving`, applied
to the two components composed with the projection `B_i ×_{B_{i₂}} V ⟶ V`. The source instead
forms the equalizer `E_i = Y_i ×_{Y_i ×_{B_i} Y_i} X_i`, shows that it is a monomorphism of
finite presentation and concludes by Stacks 0852; that argument is avoided here, and with it
the dependence on Stacks 0852, 03HK and 084P.

The index `i₀ ≥ max(i₁, i₂)` is produced by `exists_ge_ge`: the index type is only a preorder,
so it has no binary maximum. Eventual uniqueness is stated with an explicit index `i₃` rather
than as an eventuality along a filter, because the common tail `CategoryTheory.Over (op i₀)`
is a category and not a preorder.

The restriction of an image system to a later tail is composition with
`CategoryTheory.Over.map`; since `((Over.map u).obj j).left = j.left`, the two restricted
systems of `GX` and `GY` sit over the same stage `B_{j.left}` definitionally, which is what
makes the two equations of `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism` typecheck as
stated.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP7](https://stacks.math.columbia.edu/tag/0CP7)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 0CP2](https://stacks.math.columbia.edu/tag/0CP2)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace GoodDiagram

section SystemMorphisms

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_DescendingFiniteTypeMorphism
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
    {pY : Y ⟶ D.limitCone.pt}

/-! ### Two compatibilities of the image system -/

/-- The leg of the canonical cone of a good diagram at a stage, followed by the inclusion of
the scheme-theoretic image `X_{i'}` into the base-changed model, is the stage map
`X ⟶ B_{i'} ×_{B_i} W`. -/
@[reassoc]
lemma imageCone_π_ι (G : GoodDiagram B S hS hZ D pX) (j : Over (op G.index)) :
    (imageCone G).π.app j ≫ (stageImage G j).ι = stageMap G j :=
  toSchemeTheoreticImage_ι B S hS (stageMap G j)

/-- The transition morphism of the image system of a good diagram is compatible with the
inclusions of the scheme-theoretic images into the base-changed models. -/
@[reassoc]
lemma imageSystem_map_ι (G : GoodDiagram B S hS hZ D pX) {j k : Over (op G.index)}
    (a : j ⟶ k) :
    (imageSystem G).map a ≫ (stageImage G k).ι = (stageImage G j).ι ≫ stageTargetMap G a :=
  imageTransition_ι G a

/-! ### Factoring a morphism out of a scheme-theoretic image -/

/-- **Minimality of the scheme-theoretic image, read inside `X_{i'}`.** A closed subspace of
the scheme-theoretic image `X_{i'}` of a stage map through which the factorization `X ⟶ X_{i'}`
of that stage map passes is all of `X_{i'}`.

Pushing the closed subspace forward along the closed immersion `X_{i'} ⟶ B_{i'} ×_{B_i} W`
gives a closed subspace of the base-changed model through which the stage map factors, so
Stacks 082X puts `X_{i'}` inside it. -/
lemma eq_top_of_range_imageCone_π_le (G : GoodDiagram B S hS hZ D pX)
    (j : Over (op G.index)) {Z : Subfunctor ((imageSystem G).obj j)}
    (hZc : IsClosedSubspace B S hS Z)
    (hle : Subfunctor.range ((imageCone G).π.app j) ≤ Z) : Z = ⊤ := by
  have hcl : IsClosedSubspace B S hS (Subfunctor.range (Z.ι ≫ (stageImage G j).ι)) :=
    isClosedSubspace_range_of_isClosedImmersion B S hS _ hZc.1
      (isClosedImmersion_comp B S hS _ _ hZc.2 (isClosedSubspace_stageImage G j).2)
  have hfac : Subfunctor.lift ((imageCone G).π.app j) hle ≫ Z.ι ≫ (stageImage G j).ι =
      stageMap G j := by
    rw [← Category.assoc, Subfunctor.lift_ι, imageCone_π_ι]
  have hrange : Subfunctor.range (stageMap G j) ≤
      Subfunctor.range (Z.ι ≫ (stageImage G j).ι) := by
    have h := Subfunctor.range_comp_le (Subfunctor.lift ((imageCone G).π.app j) hle)
      (Z.ι ≫ (stageImage G j).ι)
    rwa [hfac] at h
  have himg := schemeTheoreticImageSubfunctor_le B S hS (stageMap G j) hcl hrange
  refine le_antisymm le_top ?_
  intro U x _
  obtain ⟨z, hz⟩ := himg U x.2
  have hzx : z.val = x := Subtype.ext hz
  exact hzx ▸ z.property

/-- **The factorization step of Stacks 0CPA.** Let `q` be a morphism from the scheme-theoretic
image `X_{i'}` of a stage map of `GX` into a base-changed model `B_{i''} ×_{B_{i₂}} V` of
`GY`, whose restriction along `X ⟶ X_{i'}` is `f` followed by the corresponding stage map of
`GY`. Then `q` factors through the scheme-theoretic image `Y_{i''}`.

The inverse image of `Y_{i''}` along `q` is a closed subspace of `X_{i'}` by Stacks 083Q, and
it contains the image of `X` because `Y_{i''}` contains the image of `Y`; so it is all of
`X_{i'}`. -/
lemma exists_comp_stageImage_ι (GX : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) (f : X ⟶ Y) (j : Over (op GX.index))
    (k : Over (op GY.index))
    (q : (imageSystem GX).obj j ⟶ pullback (D.system.map k.hom) GY.modelMap)
    (hq : (imageCone GX).π.app j ≫ q = f ≫ stageMap GY k) :
    ∃ m : (imageSystem GX).obj j ⟶ (imageSystem GY).obj k,
      m ≫ (stageImage GY k).ι = q := by
  have hpre : IsClosedSubspace B S hS ((stageImage GY k).preimage q) :=
    isClosedSubspace_preimage B S hS q _ (isAlgebraicSpace_stageTarget GY k)
      (imageSystem_isAlgebraicSpace GX j) (isClosedSubspace_stageImage GY k)
  have hle : Subfunctor.range ((imageCone GX).π.app j) ≤ (stageImage GY k).preimage q := by
    rintro U x ⟨y, rfl⟩
    have hy : q.app U (((imageCone GX).π.app j).app U y) =
        (stageMap GY k).app U (f.app U y) := by
      simpa using
        congrArg (fun m : X ⟶ pullback (D.system.map k.hom) GY.modelMap => m.app U y) hq
    change q.app U (((imageCone GX).π.app j).app U y) ∈ (stageImage GY k).obj U
    rw [hy]
    exact range_le_schemeTheoreticImageSubfunctor B S hS (stageMap GY k) U ⟨_, rfl⟩
  have hrange : Subfunctor.range q ≤ stageImage GY k :=
    (Subfunctor.preimage_eq_top_iff _ _).1 (eq_top_of_range_imageCone_π_le GX j hpre hle)
  exact ⟨Subfunctor.lift q hrange, Subfunctor.lift_ι _ _⟩

/-! ### Finite presentation of the model -/

/-- **The model of a good diagram is locally of finite presentation over its stage.** It is of
finite type by construction and the stage is a locally Noetherian algebraic space, so this is
Stacks 06G4, part (1). -/
lemma isLocallyOfFinitePresentation_modelMap (G : GoodDiagram B S hS hZ D pX) :
    IsLocallyOfFinitePresentation B S hS G.modelMap :=
  isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS G.model_isAlgebraicSpace
    (D.system_isAlgebraicSpace G.index) G.modelMap (D.noetherian G.index).2.2
    G.isFiniteType.1

/-! ### Morphisms of the image systems on a common tail -/

/-- **The morphism of inverse systems of Stacks 0CPA.** A morphism `(f_i)_{i ≥ i₀}` of the
image systems of two good diagrams, defined on the common tail of stages above `i₀`, whose
components lie over the stages `B_i` and whose limit is a given morphism `f : X ⟶ Y`. -/
structure SystemMorphism (GX : GoodDiagram B S hS hZ D pX) (GY : GoodDiagram B S hS hZ D pY)
    (f : X ⟶ Y) (i₀ : I) (hiX : GX.index ≤ i₀) (hiY : GY.index ≤ i₀) where
  /-- The components `f_i : X_i ⟶ Y_i`, natural in the stage `i ≥ i₀`. -/
  maps : (Over.map (homOfLE hiX).op ⋙ imageSystem GX) ⟶
    (Over.map (homOfLE hiY).op ⋙ imageSystem GY)
  /-- Each component `f_i` is a morphism over the stage `B_i`. -/
  over_base : ∀ j : Over (op i₀),
    maps.app j ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι ≫ pullback.fst _ _ =
      (stageImage GX ((Over.map (homOfLE hiX).op).obj j)).ι ≫ pullback.fst _ _
  /-- The limit of the components is `f`: each `f_i` is compatible with the canonical cones of
  the two image systems. -/
  induces : ∀ j : Over (op i₀),
    (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j) ≫ maps.app j =
      f ≫ (imageCone GY).π.app ((Over.map (homOfLE hiY).op).obj j)

/-- A morphism `t` out of a stage of the image system of `GX` which lies over the stage
`B_{i₂}` of `GY` and restricts to `f ≫ (Y ⟶ V)` on `X` assembles into a morphism of the image
systems on the tail above that stage: at every later stage it induces a morphism into the
base-changed model of `GY`, which factors through the scheme-theoretic image `Y_i`. Its
component at a stage, followed by the projection to the model `V`, is the transition morphism
to the given stage followed by `t`. -/
theorem exists_systemMorphism_of_stage_map (GX : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) (f : X ⟶ Y) (hf : f ≫ pY = pX) {i₀ : I}
    (hiX : GX.index ≤ i₀) (hiY : GY.index ≤ i₀)
    (t : (imageSystem GX).obj (Over.mk (homOfLE hiX).op) ⟶ GY.model)
    (ht : t ≫ GY.modelMap = (stageImage GX (Over.mk (homOfLE hiX).op)).ι ≫
      pullback.fst _ _ ≫ D.system.map (homOfLE hiY).op)
    (hlim : (imageCone GX).π.app (Over.mk (homOfLE hiX).op) ≫ t = f ≫ GY.toModel) :
    ∃ F : SystemMorphism GX GY f i₀ hiX hiY, ∀ j : Over (op i₀),
      F.maps.app j ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι ≫
          pullback.snd _ _ =
        (imageSystem GX).map (Over.homMk j.hom (Subsingleton.elim _ _) :
          (Over.map (homOfLE hiX).op).obj j ⟶ Over.mk (homOfLE hiX).op) ≫ t := by
  classical
  let aa (j : Over (op i₀)) :
      (Over.map (homOfLE hiX).op).obj j ⟶ Over.mk (homOfLE hiX).op :=
    Over.homMk j.hom (Subsingleton.elim _ _)
  have haa {j j' : Over (op i₀)} (v : j ⟶ j') :
      (Over.map (homOfLE hiX).op).map v ≫ aa j' = aa j :=
    (Over.forget (op GX.index)).map_injective (Subsingleton.elim _ _)
  let q (j : Over (op i₀)) : (imageSystem GX).obj ((Over.map (homOfLE hiX).op).obj j) ⟶
      pullback (D.system.map ((Over.map (homOfLE hiY).op).obj j).hom) GY.modelMap :=
    pullback.lift ((stageImage GX ((Over.map (homOfLE hiX).op).obj j)).ι ≫ pullback.fst _ _)
      ((imageSystem GX).map (aa j) ≫ t) (by
        simp only [Category.assoc, ht, imageSystem_map_ι_assoc, stageTargetMap_fst_assoc,
          ← D.system.map_comp]
        rfl)
  have hq (j : Over (op i₀)) :
      (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j) ≫ q j =
        f ≫ stageMap GY ((Over.map (homOfLE hiY).op).obj j) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [q, Category.assoc, pullback.lift_fst, imageCone_π_ι_assoc, stageMap_fst,
        Over.map_obj_left]
      rw [← Category.assoc, hf]
    · simp only [q, Category.assoc, pullback.lift_snd, stageMap_snd]
      rw [← Category.assoc, (imageCone GX).w (aa j), hlim]
  choose m hm using fun j : Over (op i₀) =>
    exists_comp_stageImage_ι GX GY f ((Over.map (homOfLE hiX).op).obj j)
      ((Over.map (homOfLE hiY).op).obj j) (q j) (hq j)
  have hqs (j : Over (op i₀)) :
      q j ≫ pullback.snd _ _ = (imageSystem GX).map (aa j) ≫ t :=
    pullback.lift_snd _ _ _
  have hn {j j' : Over (op i₀)} (v : j ⟶ j') :
      (imageSystem GX).map ((Over.map (homOfLE hiX).op).map v) ≫ m j' =
        m j ≫ (imageSystem GY).map ((Over.map (homOfLE hiY).op).map v) := by
    refine (cancel_mono (stageImage GY ((Over.map (homOfLE hiY).op).obj j')).ι).1 ?_
    rw [Category.assoc, hm, Category.assoc, imageSystem_map_ι, ← Category.assoc, hm]
    refine pullback.hom_ext ?_ ?_
    · simp only [q, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        imageSystem_map_ι_assoc, stageTargetMap_fst, Over.map_map_left]
    · rw [Category.assoc, Category.assoc, hqs j', stageTargetMap_snd, hqs j, ← Category.assoc,
        ← Functor.map_comp, haa]
  refine ⟨{ maps := { app := m, naturality := fun _ _ v => hn v }
            over_base := ?_
            induces := ?_ }, fun j => ?_⟩
  · intro j
    rw [← Category.assoc, hm j]
    simp only [q, pullback.lift_fst]
  · intro j
    refine (cancel_mono (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι).1 ?_
    rw [Category.assoc, hm, Category.assoc, imageCone_π_ι]
    exact hq j
  · change m j ≫ _ ≫ _ = _
    rw [← Category.assoc, hm j]
    exact pullback.lift_snd _ _ _

/-! ### Existence -/

/-- **Stacks 0CPA, existence.** In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `B` with `X` quasi-separated over `B`, and let `GX` and `GY` be diagrams as in
Stacks 0CP8 for `X` and for `Y`. Then some stage `i₀` above the indices of both diagrams
carries a morphism of the inverse systems of scheme-theoretic images on the tail above `i₀`,
over the system `(B_i)_{i ≥ i₀}`, whose limit is `f`.

The model `V ⟶ B_{i₂}` of `GY` is locally of finite presentation, so the composite
`X ⟶ Y ⟶ V` is defined over a stage `X_{i₀} ⟶ V` by the surjectivity half of the limit
criterion for morphisms out of an inverse limit; the components of the system morphism are the
factorizations through the scheme-theoretic images `Y_i` supplied by
`AlgebraicGeometry.Space.GoodDiagram.exists_comp_stageImage_ι`. The two hypotheses `hX` and
`hSize` are those of the library's Stacks 0CP9. -/
@[stacks 0CPA "existence"]
theorem exists_systemMorphism (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (GX : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) :
    ∃ (i₀ : I) (hiX : GX.index ≤ i₀) (hiY : GY.index ≤ i₀),
      Nonempty (SystemMorphism GX GY f i₀ hiX hiY) := by
  classical
  obtain ⟨i₁, hiX₁, hiY₁⟩ := exists_ge_ge GX.index GY.index
  have hsq : (f ≫ GY.toModel) ≫ GY.modelMap =
      (imageCone GX).π.app (Over.mk (homOfLE hiX₁).op) ≫
        (stageImage GX (Over.mk (homOfLE hiX₁).op)).ι ≫
          pullback.fst _ _ ≫ D.system.map (homOfLE hiY₁).op := by
    rw [imageCone_π_ι_assoc, stageMap_fst_assoc, D.limitCone.w, Category.assoc,
      ← GY.commutes, ← Category.assoc, hf]
  obtain ⟨j, t, k, a, a', hlim, hover⟩ :=
    exists_stage_map_of_relativelyLimitPreserving B S hS hZ
      (imageSystem GX) (imageCone GX) (isLimit_imageCone GX hX hSize)
      ((cardinal_mk_over_op_le GX.index).trans_lt hSize)
      (cardinal_mk_hom_over_op_lt B GX.index)
      (imageSystem_isAlgebraicSpace GX) (imageSystem_isQuasiCompactSpace GX)
      (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated GX hSize hX hXqs)
      (fun v => imageSystem_map_isAffineHom GX v) hX
      GY.model_isAlgebraicSpace (D.system_isAlgebraicSpace GY.index) GY.modelMap
      (isLocallyOfFinitePresentation_modelMap GY) (f ≫ GY.toModel)
      (Over.mk (homOfLE hiX₁).op)
      ((stageImage GX (Over.mk (homOfLE hiX₁).op)).ι ≫
        pullback.fst _ _ ≫ D.system.map (homOfLE hiY₁).op) hsq
  have ht : ((imageSystem GX).map a ≫ t) ≫ GY.modelMap =
      (stageImage GX k).ι ≫ pullback.fst _ _ ≫
        D.system.map (a'.left ≫ (homOfLE hiY₁).op) := by
    rw [hover, imageSystem_map_ι_assoc, stageTargetMap_fst_assoc, ← D.system.map_comp]
  exact ⟨k.left.unop, leOfHom k.hom.unop, leOfHom (a'.left ≫ (homOfLE hiY₁).op).unop,
    ⟨(exists_systemMorphism_of_stage_map GX GY f hf _ _ ((imageSystem GX).map a ≫ t) ht
      hlim).choose⟩⟩

/-! ### Eventual uniqueness -/

/-- The naturality of a morphism of image systems, read after the projection of the
base-changed model of `GY` to the model `V`. -/
private lemma systemMorphism_naturality_snd {GX : GoodDiagram B S hS hZ D pX}
    {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y} {i₀ : I} {hiX : GX.index ≤ i₀}
    {hiY : GY.index ≤ i₀} (F : SystemMorphism GX GY f i₀ hiX hiY) {j k : Over (op i₀)}
    (a : j ⟶ k) :
    (imageSystem GX).map ((Over.map (homOfLE hiX).op).map a) ≫ F.maps.app k ≫
        (stageImage GY ((Over.map (homOfLE hiY).op).obj k)).ι ≫ pullback.snd _ _ =
      F.maps.app j ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι ≫
        pullback.snd _ _ := by
  have hnat : (imageSystem GX).map ((Over.map (homOfLE hiX).op).map a) ≫ F.maps.app k =
      F.maps.app j ≫ (imageSystem GY).map ((Over.map (homOfLE hiY).op).map a) :=
    F.maps.naturality a
  rw [← Category.assoc, hnat, Category.assoc, imageSystem_map_ι_assoc, stageTargetMap_snd]

/-- Two morphisms of image systems whose components at one stage agree after the projection to
the model `V` of `GY` agree at every later stage: they agree over the base by construction,
and their components over the model are transported from the given stage by naturality. -/
private lemma eventually_eq_of_eq_snd {GX : GoodDiagram B S hS hZ D pX}
    {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y} {i₀ : I} {hiX : GX.index ≤ i₀}
    {hiY : GY.index ≤ i₀} (F G : SystemMorphism GX GY f i₀ hiX hiY) (k : Over (op i₀))
    (hk : F.maps.app k ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj k)).ι ≫
          pullback.snd _ _ =
        G.maps.app k ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj k)).ι ≫
          pullback.snd _ _) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ j : Over (op i₀), i₃ ≤ j.left.unop →
      F.maps.app j = G.maps.app j := by
  refine ⟨k.left.unop, leOfHom k.hom.unop, fun j hj => ?_⟩
  have a : j ⟶ k := Over.homMk (homOfLE hj).op (Subsingleton.elim _ _)
  refine (cancel_mono (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc]
    exact (F.over_base j).trans (G.over_base j).symm
  · rw [Category.assoc, Category.assoc, ← systemMorphism_naturality_snd F a,
      ← systemMorphism_naturality_snd G a, hk]

/-- **Stacks 0CPA, eventual uniqueness.** Two morphisms of the inverse systems of
scheme-theoretic images on the tail above a stage `i₀`, both inducing the same morphism
`f : X ⟶ Y` in the limit, have the same component at every sufficiently late stage.

Their components at the initial stage agree after composing with the projection `X ⟶ X_{i₀}`,
by the two compatibilities with the canonical cones, and after composing with the model
`V ⟶ B_{i₂}`, by the two equations over the base; so the injectivity half of the limit
criterion for morphisms out of an inverse limit makes them agree after one transition
morphism, and naturality propagates that to all later stages. The source's equalizer argument
is not used. -/
@[stacks 0CPA "eventual uniqueness"]
theorem eventually_eq_systemMorphism (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
    {i₀ : I} {hiX : GX.index ≤ i₀} {hiY : GY.index ≤ i₀}
    (F G : SystemMorphism GX GY f i₀ hiX hiY) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ j : Over (op i₀), i₃ ≤ j.left.unop →
      F.maps.app j = G.maps.app j := by
  classical
  let j₀ : Over (op i₀) := Over.mk (𝟙 (op i₀))
  let r : (imageSystem GX).obj ((Over.map (homOfLE hiX).op).obj j₀) ⟶ GY.model :=
    F.maps.app j₀ ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j₀)).ι ≫
      pullback.snd _ _
  let s : (imageSystem GX).obj ((Over.map (homOfLE hiX).op).obj j₀) ⟶ GY.model :=
    G.maps.app j₀ ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j₀)).ι ≫
      pullback.snd _ _
  have hlim : (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j₀) ≫ r =
      (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j₀) ≫ s := by
    simp only [r, s, ← Category.assoc, (F.induces j₀).trans (G.induces j₀).symm]
  have hbase : r ≫ GY.modelMap = s ≫ GY.modelMap := by
    simp only [r, s, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using congrArg
      (· ≫ D.system.map ((Over.map (homOfLE hiY).op).obj j₀).hom)
      ((F.over_base j₀).trans (G.over_base j₀).symm)
  obtain ⟨kk, u, hu⟩ :=
    exists_stage_eq_of_relativelyLimitPreserving B S hS hZ
      (imageSystem GX) (imageCone GX) (isLimit_imageCone GX hX hSize)
      ((cardinal_mk_over_op_le GX.index).trans_lt hSize)
      (cardinal_mk_hom_over_op_lt B GX.index)
      (imageSystem_isAlgebraicSpace GX) (imageSystem_isQuasiCompactSpace GX)
      (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated GX hSize hX hXqs)
      (fun v => imageSystem_map_isAffineHom GX v) hX
      GY.model_isAlgebraicSpace (D.system_isAlgebraicSpace GY.index) GY.modelMap
      (isLocallyOfFinitePresentation_modelMap GY)
      ((Over.map (homOfLE hiX).op).obj j₀) r s hlim hbase
  let j : Over (op i₀) := Over.mk u.left
  let e : (Over.map (homOfLE hiX).op).obj j ≅ kk :=
    Over.isoMk (Iso.refl _) (Subsingleton.elim _ _)
  let w : j ⟶ j₀ := Over.homMk u.left (Subsingleton.elim _ _)
  have he : e.hom ≫ u = (Over.map (homOfLE hiX).op).map w :=
    (Over.forget (op GX.index)).map_injective (Subsingleton.elim _ _)
  have hh : (imageSystem GX).map ((Over.map (homOfLE hiX).op).map w) ≫ r =
      (imageSystem GX).map ((Over.map (homOfLE hiX).op).map w) ≫ s := by
    rw [← he, Functor.map_comp, Category.assoc, Category.assoc, hu]
  refine eventually_eq_of_eq_snd F G j ?_
  rwa [← systemMorphism_naturality_snd F w, ← systemMorphism_naturality_snd G w]

end SystemMorphisms

end GoodDiagram

end AlgebraicGeometry.Space

end
