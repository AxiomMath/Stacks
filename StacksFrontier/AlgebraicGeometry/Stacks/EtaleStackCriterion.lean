module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafConditionSmallEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.Uniqueness

/-!
# The étale criterion for an algebraic stack (Stacks 076V)

Let `S` be a scheme of a big fppf site and let `𝒳` be a category fibred in groupoids over the
common underlying category of the big fppf and big étale sites of `S`. **Stacks 076V** says that
`𝒳` is an algebraic stack as soon as

1. `𝒳` is a stack in groupoids for the étale topology,
2. its diagonal is representable by algebraic spaces, and
3. there are a scheme `U` over `S` and a 1-morphism `(Sch/U) ⟶ 𝒳` which is representable by
   algebraic spaces, surjective and smooth.

Conditions (2) and (3) are, as the source's proof notes, independent of the topology, and they are
the corresponding clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` verbatim. What has to be
proved is that `𝒳` is a stack for the fppf topology.

## The argument

The proof is the source's. Write `𝒰 = (Sch/U)` and `f : 𝒰 ⟶ 𝒳` for the atlas.

* By condition (2) the self-intersection `𝒰 ×_𝒳 𝒰` is representable by an algebraic space `R`
  (Stacks 04T4 (1), through Stacks 045G), and Stacks 04T4 (4) puts a groupoid in algebraic spaces
  `G = (U, R, s, t, c)` on the pair
  (`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionGroupoid`). None of this uses a stack
  condition on `𝒳`. By condition (3) both projections of `G` are smooth (Stacks 04T5 (1)), so the
  fppf quotient stack `[U/R]` is an algebraic stack (Stacks 04TK) whose projection `U ⟶ [U/R]` is
  representable, surjective and smooth.
* The 1-morphism from the pointwise groupoid fibration `P` of `G` to `𝒳` is fully faithful, because
  the arrow space of `G` is the self-intersection; so the maps it induces on morphism presheaves
  are isomorphisms. By Stacks 06XH (2) every object of `𝒳` comes étale locally from `𝒰`, hence
  from `P`. So `𝒳` (after a universe lift) is the *étale* stackification of `P`.
* The morphism presheaves of `𝒳` are fppf sheaves, being algebraic spaces by condition (2); hence
  so are those of `P`, and the stackification map `P ⟶ [U/R]`, which is locally bijective on
  morphism presheaves for the fppf topology, is bijective on them. By Stacks 06XH (2) applied to
  the smooth projection of `[U/R]`, every object of `[U/R]` comes étale locally from `P`. So
  `[U/R]` — an fppf stack, hence an étale stack — is *also* an étale stackification of `P`.
* Two stackifications of one fibred category are equivalent over the site (the determinacy clause
  of Stacks 02ZN/02ZP). So `𝒳` is equivalent to the fppf stack `[U/R]`, and is itself an fppf stack
  by Stacks 042W.

This replaces the source's two-step comparison `[U/R]_étale ⟶ 𝒳` and `[U/R]_étale ⟶ [U/R]` by the
single comparison of two étale stackifications of `P`; the inputs are the same — the full
faithfulness of Stacks 04T4 (6) at the level of `P`, the étale-local sections of smooth surjections
(More on Morphisms 37.38.7, i.e. Stacks 055V, through Stacks 06XH (2)), and Stacks 04TK.

## Main results

* `CategoryTheory.Functor.IsStack.of_le`: a stack for a topology is a stack for every coarser one.
* `CategoryTheory.Functor.essImage_pullbackFiber_of_isHomLift`: for a target fibred in groupoids,
  a morphism `F a ⟶ x` over `k` puts the restriction of `x` along `k` in the essential image.
* `AlgebraicGeometry.Stack.isMorSheaf_of_isAlgebraicSpaceIsomPresheaf`: the morphism presheaves of
  a category fibred in groupoids whose isomorphism presheaves are algebraic spaces are fppf
  sheaves.
* `AlgebraicGeometry.Stack.isStack_of_isStack_etale_of_smoothAtlas`: the fppf stack condition.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale_of_smoothAtlas`:
  **Stacks 076V**.

## Implementation notes

Stacks 06XH (2) is `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift_of_representable`,
whose étale topology `AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS .etale` is the
localisation of `AlgebraicGeometry.etaleTopology` at `S` by definition.

The étale topology on the common underlying category is `AlgebraicGeometry.etaleTopology`
localised at `S`, as in `AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale`.
The étale stack hypothesis is the family-indexed `CategoryTheory.Functor.IsStackInGroupoids` of
Stacks 02ZI at the index universe `u + 1` of the families of the site, which is equivalent to the
sieve-indexed stack condition (`CategoryTheory.Functor.isStack_of_isStackInGroupoids`).

## References

* [Stacks Project, Tag 076V](https://stacks.math.columbia.edu/tag/076V)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 02ZP](https://stacks.math.columbia.edu/tag/02ZP)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/-! ### Two general facts about stacks -/

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The morphism-presheaf sheaf condition for a topology passes to every coarser topology. -/
private theorem isMorSheaf_of_le {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J J' : GrothendieckTopology 𝒮}
    (hJ : J' ≤ J) {U : 𝒮} {x y : p.Fiber U} (h : p.IsMorSheaf J U x y) :
    p.IsMorSheaf J' U x y := by
  rw [IsMorSheaf, isSheaf_iff_isSheaf_of_type] at h ⊢
  exact Presieve.isSheaf_of_le _ (Stacks.Sites.over_mono hJ U) h

/-- **A stack for a topology is a stack for every coarser topology.** A covering sieve of the
coarser topology covers for the finer one, so descent along it is effective, and a sheaf for the
finer localised topology is a sheaf for the coarser one. -/
theorem IsStack.of_le {p : 𝒳 ⥤ 𝒮} {J J' : GrothendieckTopology 𝒮} (hJ : J' ≤ J)
    (hp : p.IsStack J) : p.IsStack J' where
  isFibered := hp.isFibered
  isMorSheaf := by
    have := hp.isFibered
    exact fun U x y => isMorSheaf_of_le hJ (hp.isMorSheaf U x y)
  hasEffectiveDescent := by
    have := hp.isFibered
    intro U R hR D
    exact hp.hasEffectiveDescent R (hJ _ hR) D

variable {𝒜 : Type u₃} [Category.{v₃} 𝒜]

/-- **A morphism into an object over a given arrow puts the restriction in the essential image.**
Let `q` be fibred in groupoids and let `F` be a functor strictly over the base. If `F a ⟶ x` lies
over `k : V ⟶ U`, then the chosen restriction of `x` along `k` is isomorphic, in the fibre over
`V`, to the image of `a`: both are cartesian lifts of `k` with target `x`. This is the converse of
`CategoryTheory.Functor.exists_isHomLift_of_essImage`. -/
theorem essImage_pullbackFiber_of_isHomLift {p : 𝒜 ⥤ 𝒮} {q : 𝒳 ⥤ 𝒮} [q.IsPreFibered]
    (hq : q.IsFiberedInGroupoids) {F : 𝒜 ⥤ 𝒳} (hF : F ⋙ q = p) {U V : 𝒮} (x : q.Fiber U)
    (k : V ⟶ U) (a : 𝒜) (ha : p.obj a = V) (φ : F.obj a ⟶ x.1) (hφ : q.IsHomLift k φ) :
    (fiberFunctorOfCompEq hF V).essImage (pullbackFiber q x k) := by
  have : q.IsStronglyCartesian k φ := hq.isStronglyCartesian_homLift k φ
  exact ⟨Fiber.mk ha, ⟨fiberIsoOfCartesian (p := q)
    (z := (fiberFunctorOfCompEq hF V).obj (Fiber.mk ha)) (z' := pullbackFiber q x k) k φ
    (IsPreFibered.pullbackMap x.2 k)
    (IsStronglyCartesian.isCartesian_of_isStronglyCartesian q k φ)
    (IsPreFibered.pullbackMap.IsCartesian x.2 k)⟩⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphism presheaves are fppf sheaves when the diagonal is representable -/

/-- **The morphism presheaves are fpqc sheaves when the isomorphism presheaves are algebraic
spaces.** This is the argument of
`AlgebraicGeometry.Stack.isMorSheaf_fpqc_of_isAlgebraicStack`, which uses no part of algebraicity
beyond condition (2) of Stacks 045G: an algebraic space is an fpqc sheaf (Stacks 0APL), and the
sheaf condition passes through the universe lift and the iterated-slice equivalence. -/
theorem isMorSheaf_fpqc_of_isAlgebraicSpaceIsomPresheaf
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳)
    (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U) :
    haveI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    𝒳.val.p.IsMorSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) U x y := by
  have hfib : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hiso : Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap
        (BigFppfOver.toScheme B U.left.1 U.left.2)).toGrothendieck)
      (isomSpace B S hS 𝒳 U x y) := by
    obtain ⟨F, hF, ⟨i⟩⟩ := h𝒳 U x y
    have h0 := hF.isSheaf_fpqc
    rw [isSheaf_iff_isSheaf_of_type] at h0 ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1
      (Presieve.isSheaf_iso _ i (Presieve.isSheaf_comp_uliftFunctor _ h0))
  rw [BigFppfOver.fpqcTopology_eq_over] at hiso
  rw [Functor.IsMorSheaf, BigFppfOver.fpqcTopology_eq_over,
    ← Presheaf.isSheaf_of_iso_iff
      (isomPresheafIsoMorPresheaf 𝒳.val.p 𝒳.isFiberedInGroupoids x y),
    ← Presheaf.isSheaf_of_iso_iff
      ((Functor.associator (Over.iteratedSliceForward U).op
          (Over.iteratedSliceBackward U).op (𝒳.val.p.isomPresheaf x y)).symm ≪≫
        Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceEquiv U).unitIso)
          (𝒳.val.p.isomPresheaf x y) ≪≫
        (𝒳.val.p.isomPresheaf x y).leftUnitor)]
  have : (Over.iteratedSliceForward U).IsContinuous
      (((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over (B.obj hS)).over U)
      ((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over
        (B.obj (X := U.left.1) U.left.2)) :=
    inferInstanceAs ((Over.iteratedSliceForward U).IsContinuous
      (((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over (B.obj hS)).over U)
      ((Scheme.fpqcPrecoverage.comap B.inclusion).toGrothendieck.over U.left))
  exact (Over.iteratedSliceForward U).op_comp_isSheaf_of_isSheaf _ _ _ hiso

/-- **The morphism presheaves are fppf sheaves when the isomorphism presheaves are algebraic
spaces**: condition (2) of the fppf stack condition (Stacks 026F) for a category fibred in
groupoids satisfying condition (2) of Stacks 045G. The fppf topology is coarser than the fpqc
topology. -/
theorem isMorSheaf_of_isAlgebraicSpaceIsomPresheaf
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳)
    (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U) :
    haveI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    𝒳.val.p.IsMorSheaf (BigFppfOver.topology B S hS) U x y := by
  have hfib : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  refine Functor.isMorSheaf_of_le ?_
    (isMorSheaf_fpqc_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒳 h𝒳 U x y)
  rw [BigFppfOver.fpqcTopology_eq_over]
  exact Stacks.Sites.over_mono
    (Precoverage.toGrothendieck_mono B.precoverage_le_fpqcPrecoverage_comap) _

/-! ### The self-intersection groupoid of a smooth atlas is smooth -/

namespace SelfIntersection

variable {B S hS}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {F : 𝒰 ⟶ 𝒳}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 F.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- The source morphism of the self-intersection groupoid of Stacks 04T4 (4) is smooth when the
presenting 1-morphism is. This is the argument of
`AlgebraicGeometry.Stack.SelfIntersection.isSmooth_selfIntersectionPresentation_source`
(Stacks 04T5 (1)), which uses no stack condition on the target. -/
theorem isSmooth_selfIntersectionGroupoid_source
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF) :
    Space.IsSmooth B S hS
      (selfIntersectionGroupoid eU eR (isFiberedInSetoids_source eU)).source.hom :=
  (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF).mp hsmooth
    𝒰 ⟨U.obj, U.property, ⟨eU⟩⟩ F
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} F F))
    R.obj U.obj R.property U.property eR eU

/-- The target morphism of the self-intersection groupoid of Stacks 04T4 (4) is smooth when the
presenting 1-morphism is; the argument of
`AlgebraicGeometry.Stack.SelfIntersection.isSmooth_selfIntersectionPresentation_target`. -/
theorem isSmooth_selfIntersectionGroupoid_target
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF) :
    Space.IsSmooth B S hS
      (selfIntersectionGroupoid eU eR (isFiberedInSetoids_source eU)).target.hom :=
  (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF).mp hsmooth
    𝒰 ⟨U.obj, U.property, ⟨eU⟩⟩ F
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} F F)
    R.obj U.obj R.property U.property eR eU

end SelfIntersection

/-! ### The fppf stack condition, and Stacks 076V -/

section Criterion

variable {B S hS}

/-- **An étale stack with representable diagonal and a surjective smooth scheme atlas is a stack
for the fppf topology.** Let `𝒴` be a category fibred in groupoids over the big fppf site of `S`
which is a stack for the étale topology, whose diagonal is representable by algebraic spaces, and
which has a 1-morphism `f : (Sch/U) ⟶ 𝒴` from a scheme, representable by algebraic spaces,
surjective and smooth. Then `𝒴` is a stack for the fppf topology.

The universe lift of `𝒴` and the fppf quotient stack `[U/R]` of the self-intersection groupoid of
`f` are both étale stackifications of the pointwise groupoid fibration of that groupoid, hence
equivalent over the site (Stacks 02ZP); see the module documentation. -/
theorem isStack_of_isStack_etale_of_smoothAtlas
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hstack : 𝒴.val.p.IsStack ((etaleTopology B).over (B.obj hS)))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    (U : BigFppfOver B S hS) (f : schemeFibredCategory B S hS U ⟶ 𝒴)
    (hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hfprop : ∀ (V : BigFppfOver B S hS)
        (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map V.hom)
        (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory B S hS U).val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (let g := (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
         Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g)) :
    𝒴.val.p.IsStack (BigFppfOver.topology B S hS) := by
  classical
  let Jet := (etaleTopology B).over (B.obj hS)
  let Jf := BigFppfOver.topology B S hS
  have hle : Jet ≤ Jf := Space.etaleTopologyOver_le_topology B S hS
  -- The groupoid in algebraic spaces of the atlas (Stacks 04T4 (1) and (4)).
  let 𝒰 := schemeFibredCategory B S hS U
  let Usp : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let eU : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (Usp.obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation B S hS 𝒰 𝒴 f.hom
      (hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal.{u, u, u + 1, u, u, u, u}
        B S hS 𝒴 hdiag)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  let R : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒴 f.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p := eR₀
  let hsetU := SelfIntersection.isFiberedInSetoids_source eU
  let G := SelfIntersection.selfIntersectionGroupoid eU eR hsetU
  -- It is smooth (Stacks 04T5 (1)).
  have hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) f hfrep :=
    fun V y hy F hF he => (hfprop V y hy F hF he).2
  have hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS G :=
    ⟨SelfIntersection.isSmooth_selfIntersectionGroupoid_source eU eR hfrep hsmooth,
      SelfIntersection.isSmooth_selfIntersectionGroupoid_target eU eR hfrep hsmooth⟩
  -- The projection of the quotient stack is representable, surjective and smooth (Stacks 04TK).
  have hisom : QuotientStackIsomSheavesAlgebraic B S hS G := fun T x y =>
    isAlgebraicSpace_isomPresheaf B S hS _ G T x y
  let Pres := QuotientAtlas.presentation G
    (representable_quotientStackProjectionHom_of_isomPresheafAlgebraic G hisom)
  have hπsm := hasRelativeProperty_quotientStackProjectionHom_of_presentation.{u, u}
    (Space.smoothMorphismProperty B S hS) Pres hG.source
  have hπsurj := hasRelativeProperty_quotientStackProjectionHom_of_presentation.{u, u}
    (Space.surjectiveMorphismProperty B S hS) Pres (QuotientAtlas.isSurjective_source G)
  -- Étale-local lifts along both atlases (Stacks 06XH (2)). Their covering sieves are for
  -- `BigFppfOver.baseOverTopology B S hS .etale`, which is `Jet` by definition.
  have hYlift := exists_etaleCovering_fibre_lift_of_representable B S hS
    (quotientStackProjectionHom G) Pres.representable
    (fun V y hy F hF he => ⟨hπsurj V y hy F hF he, hπsm V y hy F hF he⟩)
  have hXlift := exists_etaleCovering_fibre_lift_of_representable B S hS f hfrep hfprop
  -- The three fibred categories and the two 1-morphisms out of the pointwise groupoid fibration.
  let P := Stack.quotientPrestack G
  let Xu := SelfIntersection.stackUlift 𝒴
  let Y := Stack.quotientStack G
  have hXugpd : Xu.p.IsFiberedInGroupoids :=
    BasedCategory.isFiberedInGroupoids_ulift 𝒴.val 𝒴.isFiberedInGroupoids
  have : Xu.p.IsFibered := hXugpd.isFibered
  have hYgpd : Y.p.IsFiberedInGroupoids := Stack.isFiberedInGroupoids_quotientStack G
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let FX := SelfIntersection.toStackUliftOfPointwise eU eR hsetU
  have hFX : P.p.IsFibredOneMorphism Xu.p FX :=
    SelfIntersection.isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU
  have hFY : P.p.IsFibredOneMorphism Y.p (Stack.toQuotientStack G) :=
    Stack.isFibredOneMorphism_toQuotientStack G
  -- The stack conditions.
  have hXu : Xu.p.IsStack Jet := BasedCategory.isStack_ulift 𝒴.val Jet hstack
  have hYf : Y.p.IsStack Jf := Stack.isStack_quotientStack G
  have hYet : Y.p.IsStack Jet := hYf.of_le hle
  -- Clause (1) of Stacks 02ZN for `P ⟶ 𝒴`: the comparison of morphism presheaves is an iso.
  have hGmor : ∀ (T : BigFppfOver B S hS) (a b : P.p.Fiber T),
      Presheaf.IsLocallyInjective (Jet.over T) (hFX.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (Jet.over T) (hFX.morPresheafMap a b) := by
    intro T a b
    have := SelfIntersection.isIso_morPresheafMap_toStackUliftOfPointwise eU eR hsetU T a b
    exact ⟨inferInstance, inferInstance⟩
  -- Clause (1) of Stacks 02ZN for `P ⟶ [U/R]`, at the étale topology: the comparison of
  -- morphism presheaves is locally bijective for the fppf topology between fppf sheaves.
  have hmor𝒴 : ∀ (T : BigFppfOver B S hS) (x y : 𝒴.val.p.Fiber T),
      𝒴.val.p.IsMorSheaf Jf T x y :=
    isMorSheaf_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒴
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).1 hdiag)
  have hmorXu : ∀ (T : BigFppfOver B S hS) (x y : Xu.p.Fiber T), Xu.p.IsMorSheaf Jf T x y :=
    (BasedCategory.uliftEquivalence 𝒴.val).isMorSheaf Jf hmor𝒴
  have hFmor : ∀ (T : BigFppfOver B S hS) (a b : P.p.Fiber T),
      Presheaf.IsLocallyInjective (Jet.over T) (hFY.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (Jet.over T) (hFY.morPresheafMap a b) := by
    intro T a b
    have := SelfIntersection.isIso_morPresheafMap_toStackUliftOfPointwise eU eR hsetU T a b
    have hPsheaf : Presheaf.IsSheaf (Jf.over T) (Functor.morPresheaf P.p a b) :=
      (Presheaf.isSheaf_of_iso_iff (asIso (hFX.morPresheafMap a b))).2 (hmorXu T _ _)
    obtain ⟨_, _⟩ := Stack.isLocallyBijective_toQuotientStack G T a b
    have : IsIso (hFY.morPresheafMap a b) :=
      Presheaf.isIso_of_isLocallyBijective (Jf.over T) _ hPsheaf (hYf.isMorSheaf T _ _)
    exact ⟨inferInstance, inferInstance⟩
  -- Clause (2) of Stacks 02ZN for `P ⟶ 𝒴`, at the étale topology.
  have hGobj : ∀ (T : BigFppfOver B S hS) (x : Xu.p.Fiber T), ∃ Rs ∈ Jet T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ T⦄, Rs.arrows k →
        (Functor.fiberFunctorOfCompEq hFX.comp_eq V).essImage
          (Functor.pullbackFiber Xu.p x k) := by
    intro T x
    obtain ⟨Rs, hRs, hlift⟩ := hXlift T ⟨(BasedCategory.uliftDown 𝒴.val).obj x.1, x.2⟩
    refine ⟨Rs, (hRs : Rs ∈ (etaleTopology B).over (B.obj hS) T), fun V k hk => ?_⟩
    obtain ⟨z, φ, hφ⟩ := hlift hk
    have hz : 𝒰.val.p.obj z = V :=
      (Functor.congr_obj f.hom.w z).symm.trans (IsHomLift.domain_eq 𝒴.val.p k φ)
    let a : P.obj := (Stack.quotientPrestackEquivalence G).functor.obj
      ⟨V, PresheafOfCategories.sectionOfObj eU z hz⟩
    have hc := SelfIntersection.isHomLift_representingComparisonIso (f := f.hom) eU z hz
    have hup : BasedCategory.uliftUp.{u, u + 1, u, u + 1, u + 1, u + 1} 𝒴.val ⋙ Xu.p =
        𝒴.val.p := rfl
    have : 𝒴.val.p.IsHomLift k
        ((SelfIntersection.representingComparisonIso (f := f.hom) eU z hz).hom ≫ φ) :=
      Functor.isHomLift_comp_of_isHomLift_id 𝒴.val.p _ φ k hc hφ
    have hlift' : Xu.p.IsHomLift k
        ((BasedCategory.uliftUp.{u, u + 1, u, u + 1, u + 1, u + 1} 𝒴.val).map
          ((SelfIntersection.representingComparisonIso (f := f.hom) eU z hz).hom ≫ φ)) :=
      Functor.isHomLift_map_of_comp_eq hup k _
    exact Functor.essImage_pullbackFiber_of_isHomLift hXugpd hFX.comp_eq x k a rfl _ hlift'
  -- Clause (2) of Stacks 02ZN for `P ⟶ [U/R]`, at the étale topology.
  have hFobj : ∀ (T : BigFppfOver B S hS) (y : Y.p.Fiber T), ∃ Rs ∈ Jet T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ T⦄, Rs.arrows k →
        (Functor.fiberFunctorOfCompEq hFY.comp_eq V).essImage
          (Functor.pullbackFiber Y.p y k) := by
    intro T y
    obtain ⟨Rs, hRs, hlift⟩ := hYlift T y
    refine ⟨Rs, (hRs : Rs ∈ (etaleTopology B).over (B.obj hS) T), fun V k hk => ?_⟩
    obtain ⟨z, φ, hφ⟩ := hlift hk
    have hφ' : Y.p.IsHomLift k φ := hφ
    let a : P.obj := ULiftHom.objUp.{u + 1, u + 1}
      ⟨(ULiftHom.objDown.{u + 1, u + 1} z).base,
        (ULiftHom.objDown.{u + 1, u + 1} z).fiber.as⟩
    have hd : Y.p.obj ((CatFiberedInGroupoids.homFunctor (quotientStackProjectionHom G)).obj z) =
        V := IsHomLift.domain_eq Y.p k φ
    have ha : P.p.obj a = V := (Functor.congr_obj hFY.comp_eq a).symm.trans hd
    exact Functor.essImage_pullbackFiber_of_isHomLift hYgpd hFY.comp_eq y k a ha φ hφ'
  -- The two étale stackifications are equivalent over the site (Stacks 02ZP).
  obtain ⟨E⟩ := Functor.Stackification.nonempty_isEquivalenceOver_extend
    (hG := hFX) (J := Jet) (hF := hFY) hGmor hGobj hFmor hFobj hXu hYet
  let e := (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (Functor.Stackification.extend_comp_eq hFX hFY hGmor hYet.isMorSheaf hGobj
      hYet.hasEffectiveDescent) E).toBasedEquivalence
  have hXuf : Xu.p.IsStack Jf := (BasedCategory.isStack_iff_of_equivalence e Jf).2 hYf
  exact (BasedCategory.isStack_ulift_iff 𝒴.val Jf).2 hXuf

/-- **Stacks 076V.** Let `S` be a scheme of a big fppf site and let `𝒳` be a category over the
common underlying category of the big fppf and big étale sites of `S` such that

1. `𝒳` is a stack in groupoids for the étale topology,
2. the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces, and
3. there are a scheme `U` over `S` and a 1-morphism `(Sch/U) ⟶ 𝒳` which is representable by
   algebraic spaces, surjective and smooth.

Then `𝒳` is an algebraic stack over `S` in the sense of Stacks 026O.

Conditions (2) and (3) are stated exactly as the corresponding clauses of
`AlgebraicGeometry.Stack.IsAlgebraicStack`, which, as the source's proof notes, are independent of
the topology; condition (1) is Stacks 02ZI for the étale topology localised at `S`, at the index
universe of the families of the site. The fppf stack clause is
`AlgebraicGeometry.Stack.isStack_of_isStack_etale_of_smoothAtlas`. -/
@[stacks 076V "the criterion, with hypotheses (2) and (3) in the topology-independent form of \
the corresponding clauses of Stacks 026O"]
theorem isAlgebraicStack_of_isStackInGroupoids_etale_of_smoothAtlas
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (hstack : 𝒳.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hS)))
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS
      (diagonalBasedFunctor B S hS (CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids)))
    (U : BigFppfOver B S hS)
    (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳)
    (hfrep : IsRepresentableByAlgebraicSpaces B S hS f)
    (hfprop : ∀ (V : BigFppfOver B S hS)
        (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
        (_hy : y ⋙ 𝒳.p = Over.map V.hom)
        (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory B S hS U).val.p 𝒳.p y f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (let g := (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
         Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g)) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  have hgpd := hstack.isFiberedInGroupoids
  have : 𝒳.p.IsFibered := hgpd.isFibered
  have hX : 𝒳.p.IsStack (BigFppfOver.topology B S hS) :=
    isStack_of_isStack_etale_of_smoothAtlas (CatFiberedInGroupoids.mk 𝒳 hgpd)
      (Functor.isStack_of_isStackInGroupoids hstack) hdiag U
      (Bicategory.InducedBicategory.mkHom f) hfrep hfprop
  exact ⟨hgpd, ⟨hX, hX.isStackInGroupoids hgpd⟩, hdiag, U, f, hfrep, hfprop⟩

end Criterion

end AlgebraicGeometry.Stack

end
