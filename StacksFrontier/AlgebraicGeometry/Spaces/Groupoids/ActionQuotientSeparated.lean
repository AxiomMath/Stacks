module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteGroupQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Separation properties of a quotient by a finite group action

Let a finite group `G` act on an object `V` of the big fppf site over a scheme `S`, so that no
nonidentity element fixes a point of `V` together with its residue field. The graph relation of
the action is then an étale equivalence relation and the quotient of `V` by `G` is an algebraic
space over `S`. Its diagonal is, after base change along the chart `h_{V ×_S V} ⟶ V/G ×_S V/G`,
the graph relation itself; so a property of scheme morphisms which is stable under base change
and fppf local at the target holds for the diagonal of the quotient as soon as it holds for the
graph relation. The graph relation is a disjoint union of graphs of automorphisms of `V`, which
reduces both separation properties of the quotient to the corresponding property of `V` over
`S`.

## Main results

* `AlgebraicGeometry.Space.presheaf_property_diag_actionQuotient_of_descent` transfers a
  base-change-stable, fppf-target-local property from the graph relation to the diagonal of the
  quotient.
* `AlgebraicGeometry.Space.isSeparatedOver_actionQuotient_of_descent`: the quotient of a
  separated object by such an action is separated over `S`.
* `AlgebraicGeometry.Space.isQuasiSeparatedOver_actionQuotient_of_descent`: the quotient of a
  quasi-separated object by such an action is quasi-separated over `S`.
* `AlgebraicGeometry.Space.isSeparatedOver_actionQuotient_unconditional` and
  `AlgebraicGeometry.Space.isQuasiSeparatedOver_actionQuotient_unconditional` are the same two
  conclusions with no descent hypothesis; they are the two parts of Stacks 02Z4.

## Implementation notes

Separatedness and quasi-separatedness of `V` over `S` are Mathlib's `IsSeparated` and
`QuasiSeparated` on the structure morphism of the underlying scheme over `S`; the conclusions
are the predicates of Stacks 02X5, `AlgebraicGeometry.Space.IsSeparatedOver` and
`AlgebraicGeometry.Space.IsQuasiSeparatedOver`, which test the corresponding property of
schemes on the diagonal after every representable base change. Both conclusions are therefore
instances of one transfer statement, taken at `AlgebraicGeometry.IsClosedImmersion` and at
`AlgebraicGeometry.QuasiCompact` respectively.

The graph relation is a closed immersion when `V` is separated because each graph
`(g, 1) : V ⟶ V ×_S V` is a base change of the diagonal of `V`, hence a finite monomorphism,
and the relation is monic as an equivalence relation; it is quasi-compact when `V` is
quasi-separated because each graph is then quasi-compact and the index group is finite, so the
induced map out of the disjoint union is quasi-compact. The second argument needs the index
type inside the scheme universe, which the smallness assumption on `G` provides.

That the quotient is an algebraic space is
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient`, which carries a hypothesis of
effective descent along the covering sieves of the site at the monomorphisms locally of finite
type. It is the only input of these statements that the source does not have, and it is carried
in the `…_of_descent` forms as the last explicit argument `hdesc`. That hypothesis is itself a
theorem, `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`,
so substituting it yields the two unconditional statements, which are where the tag sits.

## References

* [Stacks Project, Tag 02Z4](https://stacks.math.columbia.edu/tag/02Z4)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.Space

/-! ### The graph relation as a disjoint union of graphs -/

variable {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]
  (a : G →* Aut U)

/-- The graph relation restricted to the copy of `U` indexed by `g` is the graph of `g`. -/
private theorem sigmaι_comp_actionRelation (g : G) :
    Sigma.ι (fun _ : G => U) g ≫ actionRelation U G a = prod.lift (a g).asIso.hom (𝟙 U) := by
  apply prod.hom_ext <;>
    simp [actionRelation, actionRelationTarget, actionRelationSource]

/-- The underlying morphism of the graph relation is, through the identification of the relation
scheme with a disjoint union of copies of `U`, the morphism induced by the graphs of the
individual automorphisms. -/
private theorem actionRelation_left_eq :
    (actionRelation U G a).left = (actionRelationUnderlyingIso U G).hom ≫
      Sigma.desc fun g : G => (prod.lift (a g).asIso.hom (𝟙 U)).left := by
  let F : Discrete G ⥤ Over S := Discrete.functor fun _ : G => U
  have hcol : IsColimit ((Over.forget S).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (Over.forget S) (colimit.isColimit F)
  have heι (g : G) : (Over.forget S).map (Sigma.ι (fun _ : G => U) g) ≫
      (actionRelationUnderlyingIso U G).hom = Sigma.ι (fun _ : G => U.left) g := by
    rw [← actionRelationUnderlyingIso_inv_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine hcol.hom_ext fun g => ?_
  change (Over.forget S).map (Sigma.ι (fun _ : G => U) g.as) ≫ (actionRelation U G a).left =
    ((Over.forget S).map (Sigma.ι (fun _ : G => U) g.as) ≫
      (actionRelationUnderlyingIso U G).hom) ≫
      Sigma.desc fun g : G => (prod.lift (a g).asIso.hom (𝟙 U)).left
  rw [heι g.as, Sigma.ι_comp_desc]
  change (Sigma.ι (fun _ : G => U) g.as).left ≫ (actionRelation U G a).left = _
  rw [← Over.comp_left, sigmaι_comp_actionRelation]

/-! ### The graph relation of a separated object is a closed immersion -/

omit [Group G] [Small.{u} G] a in
/-- The graph of an automorphism of a separated object of `Over S` is a closed immersion: it is
the base change of the diagonal along `(f, 1)`. -/
private theorem graph_isClosedImmersion
    [_root_.AlgebraicGeometry.IsSeparated U.hom] (f : Aut U) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((Over.forget S).map (prod.lift f.asIso.hom (𝟙 U))) := by
  let d : U ⟶ U ⨯ U := prod.lift (𝟙 U) (𝟙 U)
  let p : (U ⨯ U).left ≅ pullback U.hom U.hom := Over.prodLeftIsoPullback U U
  have heqDiag : d.left ≫ p.hom = pullback.diagonal U.hom := by
    apply pullback.hom_ext <;>
      simp [p, d, Over.prodLeftIsoPullback_hom_fst, Over.prodLeftIsoPullback_hom_snd,
        ← Over.comp_left]
  have hd0 : _root_.AlgebraicGeometry.IsClosedImmersion (d.left ≫ p.hom) := by
    rw [heqDiag]
    infer_instance
  have hd : _root_.AlgebraicGeometry.IsClosedImmersion d.left :=
    IsClosedImmersion.of_comp d.left p.hom
  let e : U ⨯ U ≅ U ⨯ U := prod.mapIso f.asIso (Iso.refl U)
  have heq : d ≫ e.hom = prod.lift f.asIso.hom (𝟙 U) := by
    rw [prod.mapIso_hom]
    apply prod.hom_ext <;> simp [d]
  rw [Over.forget_map, ← heq, Over.comp_left]
  exact IsClosedImmersion.comp d.left ((Over.forget S).mapIso e).hom

/-- The graph relation of a finite group acting on a separated object with residue-field-faithful
stabilizers is a closed immersion: it is a finite monomorphism. -/
@[sga "3 IX 2.4" "partial", sga "3 V 4.1.3" "special case"]
private theorem actionRelation_isClosedImmersion [Finite G]
    (ha : ActsNontriviallyOnFixedResidueFields U G a)
    [_root_.AlgebraicGeometry.IsSeparated U.hom] :
    _root_.AlgebraicGeometry.IsClosedImmersion (actionRelation U G a).left := by
  have hfinite : _root_.AlgebraicGeometry.IsFinite (actionRelation U G a).left := by
    rw [actionRelation_left_eq]
    have hgraph (g : G) :
        _root_.AlgebraicGeometry.IsFinite ((prod.lift (a g).asIso.hom (𝟙 U)).left) :=
      ((IsClosedImmersion.iff_isFinite_and_mono _).mp (graph_isClosedImmersion U (a g))).1
    infer_instance
  have := actionRelation_isEtaleEquivalenceRelation U G a ha
  have hmono : Mono (actionRelation U G a) :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).1 inferInstance).1
  exact (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨hfinite, inferInstance⟩

/-! ### Transfer of a property from the graph relation to the diagonal of the quotient -/

/-- A base change of a binary product of two morphisms: if a morphism property relative to a
fully faithful functor holds for `f` and for `g`, it holds for `f ⨯ g`. -/
private theorem relative_prod_map {C D : Type*} [Category C] [Category D] [HasBinaryProducts D]
    (F : C ⥤ D) (P : MorphismProperty C) [F.Full] [F.Faithful]
    [P.IsStableUnderComposition] {X Y X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : P.relative F f) (hg : P.relative F g) : P.relative F (prod.map f g) := by
  let R : MorphismProperty D := P.relative F
  have : R.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange P
  have hsnd : IsPullback (prod.snd : Y ⨯ X' ⟶ X') (prod.map (𝟙 Y) g) g
      (prod.snd : Y ⨯ Y' ⟶ Y') :=
    IsPullback.mk' (by simp) (fun _ _ _ h₁ h₂ => prod.hom_ext
      (by simpa using congrArg (· ≫ prod.fst) h₂) h₁)
      (fun _ x y h =>
        ⟨prod.lift (y ≫ prod.fst) x, by simp, prod.hom_ext (by simp) (by simpa using h)⟩)
  simpa [prod.map_map] using MorphismProperty.comp_mem R _ _
    (R.of_isPullback (IsPullback.of_prod_fst_with_id f X') hf) (R.of_isPullback hsnd hg)

/-- The kernel pair of `q` sits in a pullback square over the diagonal of the target. -/
private theorem isPullback_diagonal_prod_of_kernelPair {C : Type*} [Category C]
    [HasBinaryProducts C] {R X F : C} (t s : R ⟶ X) (q : X ⟶ F)
    (hker : IsPullback t s q q) :
    IsPullback (t ≫ q) (prod.lift t s) (diag F) (prod.map q q) := by
  have hc : CommSq (t ≫ q) (prod.lift t s) (diag F) (prod.map q q) :=
    ⟨by apply prod.hom_ext <;> simp [hker.w]⟩
  apply IsPullback.of_isLimit' hc
  refine PullbackCone.IsLimit.mk hc.w
    (fun c => hker.lift (c.snd ≫ prod.fst) (c.snd ≫ prod.snd) ?_) ?_ ?_ ?_
  · have h₁' : c.fst = c.snd ≫ prod.fst ≫ q := by
      simpa using congrArg (· ≫ prod.fst) c.condition
    have h₂' : c.fst = c.snd ≫ prod.snd ≫ q := by
      simpa using congrArg (· ≫ prod.snd) c.condition
    simpa using h₁'.symm.trans h₂'
  · intro c
    simpa using (congrArg (· ≫ prod.fst) c.condition).symm
  · intro c
    apply prod.hom_ext <;> simp
  · intro c k _ hk₂
    apply hker.hom_ext
    · simpa using congrArg (· ≫ prod.fst) hk₂
    · simpa using congrArg (· ≫ prod.snd) hk₂

/-- A property relative to `yoneda` which is stable under composition passes from `q` to the
induced morphism `h_{X ⨯ X} ⟶ Q ⨯ Q`. -/
private theorem presheaf_prodComparison_comp_prod_map.{w, w'} {C : Type w} [Category.{w'} C]
    [HasBinaryProducts C] (P : MorphismProperty C) [P.IsStableUnderComposition] {X : C}
    {Q : Cᵒᵖ ⥤ Type w'} (q : yoneda.obj X ⟶ Q) (hq : P.presheaf q) :
    P.presheaf ((asIso (prodComparison yoneda X X)).hom ≫ prod.map q q) :=
  MorphismProperty.RespectsIso.precomp P.presheaf _ _ (relative_prod_map yoneda P q q hq hq)

variable (B : BigFppfSite.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)

/-- The image in schemes of the pair `(t, s)` of the site's relation scheme is, up to the product
comparison, the graph relation; so it inherits any isomorphism-invariant property of the latter. -/
private theorem toScheme_map_lift_siteActionRelation (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    [HasBinaryProducts (BigFppfOver B S hS)] (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : P (actionRelation (underlyingOver B hS V) G a).left) :
    P ((BigFppfOver.toScheme B S hS).map
      (prod.lift (siteActionRelationTarget G B hS V (contains_actionRelationScheme G B hS V a ha) a)
        (siteActionRelationSource G B hS V (contains_actionRelationScheme G B hS V a ha)))) := by
  let U := underlyingOver B hS V
  let hR := contains_actionRelationScheme G B hS V a ha
  let R := siteActionRelationScheme G B hS V hR
  let s := siteActionRelationSource G B hS V hR
  let t := siteActionRelationTarget G B hS V hR a
  let rsite : R ⟶ V ⨯ V := prod.lift t s
  let Fsite := BigFppfOver.toScheme B S hS
  have : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let post : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have : PreservesFiniteLimits post := PreservesFiniteLimits.overPost
  let postProd : post.obj (V ⨯ V) ≅ post.obj V ⨯ post.obj V := asIso (prodComparison post V V)
  let targetIso : Fsite.obj (V ⨯ V) ≅ (U ⨯ U).left := (Over.forget S).mapIso postProd
  have ht : post.map t = actionRelationTarget U G a := by ext; rfl
  have hs : post.map s = actionRelationSource U G := by ext; rfl
  have hpost : post.map rsite ≫ postProd.hom = actionRelation U G a := by
    apply prod.hom_ext
    · change (post.map rsite ≫ prodComparison post V V) ≫ prod.fst = _
      simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp, rsite, prod.lift_fst,
        ht, actionRelation]
      exact (prod.lift_fst _ _).symm
    · change (post.map rsite ≫ prodComparison post V V) ≫ prod.snd = _
      simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp, rsite, prod.lift_snd,
        hs, actionRelation]
      exact (prod.lift_snd _ _).symm
  have htarget : Fsite.map rsite ≫ targetIso.hom = (actionRelation U G a).left := by
    change (Over.forget S).map (post.map rsite) ≫ (Over.forget S).map postProd.hom = _
    rw [← Functor.map_comp, hpost]
    rfl
  exact (MorphismProperty.cancel_right_of_respectsIso P (Fsite.map rsite) targetIso.hom).mp
    (by rwa [htarget])

/-- **The transfer step behind Stacks 02Z4.** A property of scheme morphisms which is stable
under base change and fppf local at the target holds for the diagonal of the quotient of `V` by
the group action, after every representable base change, as soon as it holds for the underlying
morphism of the graph relation.

The chart `h_{V ×_S V} ⟶ V/G ×_S V/G` is surjective and étale, and the base change of the
diagonal of `V/G` along it is the graph relation; so this is Stacks 02WZ.

The hypothesis `hdesc` is the one carried by
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient`. -/
theorem presheaf_property_diag_actionQuotient_of_descent
    (G : Type v) [Group G] [Small.{u} G] (a : G →* Aut (underlyingOver B hS V))
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType))
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hP : P (actionRelation (underlyingOver B hS V) G a).left) :
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (diag (actionQuotient G B hS V a)) := by
  let hR := contains_actionRelationScheme G B hS V a ha
  let R := siteActionRelationScheme G B hS V hR
  let s := siteActionRelationSource G B hS V hR
  let t := siteActionRelationTarget G B hS V hR a
  have : IsEtaleEquivalenceRelation (relation B S hS s t) :=
    actionRelation_isEtaleEquivalenceRelation (underlyingOver B hS V) G a ha
  let Q := actionQuotient G B hS V a
  have hQalg : IsAlgebraicSpace B S hS Q := isAlgebraicSpace_actionQuotient G B hS V a ha hdesc
  have hrep : yoneda.relativelyRepresentable (quotientMap B S hS s t) :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t hQalg
  let q : yoneda.obj V ⟶ Q := quotientMap B S hS s t
  let Fsite := BigFppfOver.toScheme B S hS
  let Psurj := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Fsite
  let Petale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Fsite
  have : HasBinaryProducts (BigFppfOver B S hS) := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let c : yoneda.obj (V ⨯ V) ≅ yoneda.obj V ⨯ yoneda.obj V := asIso (prodComparison yoneda V V)
  let q₂ : yoneda.obj (V ⨯ V) ⟶ Q ⨯ Q := c.hom ≫ prod.map q q
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun f g (_ : Surjective f) (_ : Surjective g) => inferInstance⟩
  have : Psurj.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have : Petale.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have hdRep : yoneda.relativelyRepresentable (diag Q) := hQalg.diagonal_representable
  let rsite : R ⟶ V ⨯ V := prod.lift t s
  have hpair : prod.lift (yoneda.map t) (yoneda.map s) ≫ c.inv = yoneda.map rsite := by
    rw [Iso.comp_inv_eq]
    apply prod.hom_ext <;> simp [c, rsite, ← Functor.map_comp]
  have hpull : IsPullback (yoneda.map t ≫ q) (yoneda.map rsite) (diag Q) q₂ :=
    (isPullback_diagonal_prod_of_kernelPair (yoneda.map t) (yoneda.map s) q
      (quotientMap_isPullback B S hS s t)).of_iso
      (Iso.refl _) (Iso.refl _) c.symm (Iso.refl _) (by simp) hpair (by simp) (by simp [q₂])
  let e := yoneda.preimageIso (hpull.isoIsPullback _ _ (hdRep.isPullback q₂))
  have he : e.hom ≫ hdRep.snd q₂ = rsite :=
    yoneda.map_injective (by simp [e, hpull.isoIsPullback_hom_snd _ _ (hdRep.isPullback q₂)])
  have hrsite : P (Fsite.map rsite) := toScheme_map_lift_siteActionRelation B hS V G a ha P hP
  have hchosen : P (Fsite.map (hdRep.snd q₂)) :=
    (MorphismProperty.cancel_left_of_respectsIso P (Fsite.map e.hom) _).mp
      (by rwa [← Fsite.map_comp, he])
  exact (presheaf_inverseImage_iff_atlas_snd B S hS P (diag Q) hdRep (V ⨯ V) q₂
    (presheaf_prodComparison_comp_prod_map Psurj q (quotientMap_surjective B S hS s t hrep))
    (presheaf_prodComparison_comp_prod_map Petale q (quotientMap_etale B S hS s t hrep))).2
      hchosen

/-! ### The two separation properties of the quotient -/

/-- **Stacks 02Z4, separatedness, granted effective descent along the covering sieves of the
site.** The quotient of a separated object of the big fppf site over `S` by a finite group
action whose nonidentity stabilizers act nontrivially on residue fields is separated over `S`.

The hypothesis `hdesc` is the one carried by
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient`; the source has no such hypothesis. -/
theorem isSeparatedOver_actionQuotient_of_descent (G : Type v) [Group G] [Finite G]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    [_root_.AlgebraicGeometry.IsSeparated (underlyingOver B hS V).hom]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsSeparatedOver B S hS (actionQuotient G B hS V a) := by
  have : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact presheaf_property_diag_actionQuotient_of_descent B hS V G a ha hdesc
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (actionRelation_isClosedImmersion (underlyingOver B hS V) G a ha)

/-- **Stacks 02Z4, quasi-separatedness, granted effective descent along the covering sieves of
the site.** The quotient of a quasi-separated object of the big fppf site over `S` by a finite
group action whose nonidentity stabilizers act nontrivially on residue fields is quasi-separated
over `S`.

The hypothesis `hdesc` is the one carried by
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient`; the source has no such hypothesis. -/
theorem isQuasiSeparatedOver_actionQuotient_of_descent (G : Type v) [Group G] [Small.{u} G]
    [Finite G] (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    [QuasiSeparated (underlyingOver B hS V).hom]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsQuasiSeparatedOver B S hS (actionQuotient G B hS V a) := by
  have : MorphismProperty.IsLocalAtTarget (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact presheaf_property_diag_actionQuotient_of_descent B hS V G a ha hdesc
    (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
    (quasiCompact_actionRelation (underlyingOver B hS V) G a)

/-! ### The two separation properties, with no descent hypothesis -/

/-- **Stacks 02Z4, part (2).** Let a finite group `G` act on an object `V` of the big fppf site
over `S` so that no nonidentity element fixes a point of `V` together with its residue field. If
`V` is separated over `S`, then the quotient `V/G` is separated over `S`. -/
@[stacks 02Z4 "separated"]
theorem isSeparatedOver_actionQuotient_unconditional (G : Type v) [Group G] [Finite G]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    [_root_.AlgebraicGeometry.IsSeparated (underlyingOver B hS V).hom] :
    IsSeparatedOver B S hS (actionQuotient G B hS V a) :=
  isSeparatedOver_actionQuotient_of_descent B hS V G a ha
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- **Stacks 02Z4, part (1).** Let a finite group `G` act on an object `V` of the big fppf site
over `S` so that no nonidentity element fixes a point of `V` together with its residue field. If
`V` is quasi-separated over `S`, then the quotient `V/G` is quasi-separated over `S`. -/
@[stacks 02Z4 "quasi-separated"]
theorem isQuasiSeparatedOver_actionQuotient_unconditional (G : Type v) [Group G] [Finite G]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    [QuasiSeparated (underlyingOver B hS V).hom] :
    IsQuasiSeparatedOver B S hS (actionQuotient G B hS V a) :=
  isQuasiSeparatedOver_actionQuotient_of_descent B hS V G a ha
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

end AlgebraicGeometry.Space

end
