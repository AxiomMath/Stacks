module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartPresieves
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentationFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FiniteDisjointSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PresentationComparisonSquares
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.CategoryTheory.Sites.Modules.CoarserTopology

/-!
# The presentation of a quotient stack, and its charted points

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `𝒳 = [U/R]` be its quotient
stack, with canonical projection `x : 𝒮_U ⟶ [U/R]` (Stacks 044R) and canonical 2-morphism
`x ∘ s ⟶ x ∘ t` (Stacks 044S).  This file sets up the data in which Stacks 076S is stated and
the objects of `[U/R]` through which morphisms of modules on `[U/R]` are constructed.

**The data of Stacks 076S.**  The source and the target of `G` give two 2-commutative triangles of
1-morphisms out of the presentation `𝒮_R` of the arrow space, with common lower edge `x ∘ s`;
the second one through the inverse of the 2-morphism of Stacks 044S, which is what identifies
`(x ∘ s)^*ℱ|_{R_étale}` with `(x ∘ t)^*ℱ|_{R_étale}` in the source's diagram.  The comparison
maps of equation 076R of these two triangles are
`AlgebraicGeometry.Stack.quotientStackSourceComparison` and
`AlgebraicGeometry.Stack.quotientStackTargetComparison`, and the restriction
`ℱ ↦ x^*ℱ|_{U_étale}` is `AlgebraicGeometry.Stack.quotientStackObjectRestriction`.

**Charted points.**  A charted point is a point `a` of `U` over an affine object `T` of the site
together with an affine étale chart `W` of `U` through which it factors.  Its image in `[U/R]`
is the object presented by `a`, and these objects form a full subcategory of `[U/R]` which is
cover-dense for the fppf topology (`AlgebraicGeometry.Stack.isCoverDense_chartedPointFunctor`):
every object of `[U/R]` is fppf locally presented by a point of `U` (Stacks 044X), and every
point of `U` factors fppf locally through an affine étale chart.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackSourceLeg`,
  `AlgebraicGeometry.Stack.quotientStackTargetLeg` and `AlgebraicGeometry.Stack.quotientStackProj`:
  the 1-morphisms `s, t : 𝒮_R ⟶ 𝒮_U` and `x : 𝒮_U ⟶ [U/R]`.
* `AlgebraicGeometry.Stack.quotientStackTwoArrowIso`: the inverse of the 2-morphism of
  Stacks 044S, as a 2-isomorphism `x ∘ t ≅ x ∘ s`.
* `AlgebraicGeometry.Stack.quotientStackObjectRestriction` and
  `AlgebraicGeometry.Stack.quotientStackObjectRestrictionMap`: `ℱ ↦ x^*ℱ|_{U_étale}` on
  objects and on morphisms, for modules on the fppf site of `[U/R]`.
* `AlgebraicGeometry.Stack.quotientStackSourceComparison` and
  `AlgebraicGeometry.Stack.quotientStackTargetComparison`: the two comparison maps of
  equation 076R of the source's diagram.
* `AlgebraicGeometry.Stack.ChartedPoint` and `AlgebraicGeometry.Stack.chartedPointFunctor`: the
  charted points and their full embedding into `[U/R]`.

## Main results

* `AlgebraicGeometry.Stack.isCoverDense_chartedPointFunctor`: the charted points are cover-dense
  in `[U/R]` for the fppf topology.
* `AlgebraicGeometry.Stack.pointwiseSections_ext`: a section of a module over a presented object
  is determined by its restrictions along an fppf covering family of the base.
* `AlgebraicGeometry.Stack.quotientStackSource_comparisonMorphism` and
  `AlgebraicGeometry.Stack.quotientStackTarget_comparisonMorphism`: the morphisms of `[U/R]`
  inducing the two comparison maps on sections, computed in the pointwise groupoid fibration.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-! ### The data of Stacks 076S -/

/-- The 1-morphism `s : 𝒮_R ⟶ 𝒮_U` attached to the source of the groupoid (Stacks 0458). -/
noncomputable abbrev quotientStackSourceLeg : (fibredCategory C S hS G.arrows.obj).val.obj ⥤
    (fibredCategory C S hS G.objects.obj).val.obj :=
  (associatedMap C S hS G.source.hom).1.hom.toFunctor

/-- The 1-morphism `t : 𝒮_R ⟶ 𝒮_U` attached to the target of the groupoid (Stacks 0458). -/
noncomputable abbrev quotientStackTargetLeg : (fibredCategory C S hS G.arrows.obj).val.obj ⥤
    (fibredCategory C S hS G.objects.obj).val.obj :=
  (associatedMap C S hS G.target.hom).1.hom.toFunctor

/-- The canonical projection `x : 𝒮_U ⟶ [U/R]` of Stacks 044R, as a functor. -/
noncomputable abbrev quotientStackProj := (quotientStackProjection G).toFunctor

/-- The canonical projection is a 1-morphism of fibred categories. -/
theorem isFibredOneMorphism_quotientStackProj :
    (fibredCategory C S hS G.objects.obj).val.p.IsFibredOneMorphism (quotientStack G).p
      (quotientStackProj G) :=
  (isFiberedInGroupoids_quotientStack G).isFibredOneMorphism (quotientStackProjection G).w

/-- The composite `x ∘ s` is a 1-morphism of fibred categories. -/
theorem isFibredOneMorphism_quotientStackSourceProj :
    (fibredCategory C S hS G.arrows.obj).val.p.IsFibredOneMorphism (quotientStack G).p
      (quotientStackSourceLeg G ⋙ quotientStackProj G) :=
  (isFiberedInGroupoids_quotientStack G).isFibredOneMorphism
    (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom (quotientStackProjection G)).w

/-- Through the tautological presentations of `𝒮_R` and `𝒮_U` by scheme charts, the 1-morphism
`s` is postcomposition with the source map; the comparison is an identity. -/
noncomputable def quotientStackSourceChartIso :
    Space.schemeChartFunctor C S hS G.arrows.obj (fibredCategory C S hS G.arrows.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _) ⋙ quotientStackSourceLeg G ≅
      CostructuredArrow.map G.source.hom ⋙
        Space.schemeChartFunctor C S hS G.objects.obj (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl _) :=
  Iso.refl _

/-- Through the tautological presentations of `𝒮_R` and `𝒮_U` by scheme charts, the 1-morphism
`t` is postcomposition with the target map; the comparison is an identity. -/
noncomputable def quotientStackTargetChartIso :
    Space.schemeChartFunctor C S hS G.arrows.obj (fibredCategory C S hS G.arrows.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _) ⋙ quotientStackTargetLeg G ≅
      CostructuredArrow.map G.target.hom ⋙
        Space.schemeChartFunctor C S hS G.objects.obj (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl _) :=
  Iso.refl _

/-- The canonical 2-morphism `x ∘ s ⟶ x ∘ t` of Stacks 044S, as a natural transformation. -/
noncomputable def quotientStackTwoArrowNat : quotientStackSourceLeg G ⋙ quotientStackProj G ⟶
    quotientStackTargetLeg G ⋙ quotientStackProj G :=
  (quotientStackTwoArrow G).toNatTrans

/-- The components of the 2-morphism of Stacks 044S lie over identities. -/
theorem isHomLift_quotientStackTwoArrowNat (Y : (fibredCategory C S hS G.arrows.obj).val.obj) :
    (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj ((quotientStackSourceLeg G ⋙
        quotientStackProj G).obj Y)))
      ((quotientStackTwoArrowNat G).app Y) :=
  (quotientStackTwoArrow G).isHomLift' Y

/-- The 2-morphism of Stacks 044S is invertible: its components lie over identities in a
category fibred in groupoids. -/
instance isIso_quotientStackTwoArrowNat : IsIso (quotientStackTwoArrowNat G) := by
  have h : ∀ Y, IsIso ((quotientStackTwoArrowNat G).app Y) := by
    intro Y
    have := isHomLift_quotientStackTwoArrowNat G Y
    have := (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift
      (𝟙 ((quotientStack G).p.obj ((quotientStackSourceLeg G ⋙ quotientStackProj G).obj Y)))
          ((quotientStackTwoArrowNat G).app Y)
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := (quotientStack G).p)
      (f := 𝟙 ((quotientStack G).p.obj ((quotientStackSourceLeg G ⋙ quotientStackProj G).obj Y)))
          ((quotientStackTwoArrowNat G).app Y)
  exact NatIso.isIso_of_isIso_app _

/-- The 2-isomorphism `x ∘ t ≅ x ∘ s`, inverse of the 2-morphism of Stacks 044S.  It is the
2-morphism of the triangle through the target in the source's diagram. -/
noncomputable def quotientStackTwoArrowIso : quotientStackTargetLeg G ⋙ quotientStackProj G ≅
    quotientStackSourceLeg G ⋙ quotientStackProj G :=
  (asIso (quotientStackTwoArrowNat G)).symm

/-- A module on the fppf site of `[U/R]`, read on the coarser étale site; nothing changes but the
sheaf condition. -/
noncomputable abbrev quotientStackToEtale :
    SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf) ⥤
      SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
        (isFiberedInGroupoids_quotientStack G) .etale) :=
  Stacks.Sites.CoarserTopology.modulePushforward
    (BigFppfOver.associatedTopology_le_fppf C S hS (quotientStack G).p .etale) _

/-- **`ℱ ↦ x^*ℱ|_{U_étale}`.**  The restriction to the small étale site of `U` of the inverse image
of a module along the canonical projection `x : 𝒮_U ⟶ [U/R]`. -/
noncomputable abbrev quotientStackObjectRestriction
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf)) :=
  Space.etaleRestrictedModuleInverseImage C S hS (fibredCategory C S hS G.objects.obj).val.p
    (quotientStack G).p (fibredCategory C S hS G.objects.obj).property
    (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (quotientStackProj G) (isFibredOneMorphism_quotientStackProj G)
    ((quotientStackToEtale G).obj F)

/-- **`ψ ↦ x^*ψ|_{U_étale}`** on morphisms of modules on the fppf site of `[U/R]`. -/
noncomputable abbrev quotientStackObjectRestrictionMap
    {F H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf)} (ψ : F ⟶ H) :
    quotientStackObjectRestriction G F ⟶ quotientStackObjectRestriction G H :=
  Space.etaleRestrictedModuleInverseImageMap C S hS (fibredCategory C S hS G.objects.obj).val.p
    (quotientStack G).p (fibredCategory C S hS G.objects.obj).property
    (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (quotientStackProj G) (isFibredOneMorphism_quotientStackProj G)
    ((quotientStackToEtale G).map ψ)

/-- The comparison map `s_small^*(x^*ℱ|_{U_étale}) ⟶ (x ∘ s)^*ℱ|_{R_étale}` of equation 076R for
the triangle `x ∘ s = x ∘ s` through the source. -/
noncomputable abbrev quotientStackSourceComparison
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf)) :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS G.arrows.obj).property (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (quotientStackSourceLeg G) (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj
        G) (isFibredOneMorphism_quotientStackSourceProj G)
    (isFibredOneMorphism_quotientStackProj G) (Iso.refl _) G.source (quotientStackSourceChartIso G)
    (isFiberedInGroupoids_quotientStack G) (fun _ => IsHomLift.id rfl)
    (fun _ => IsHomLift.id rfl)
    ((quotientStackToEtale G).obj F)

/-- The comparison map `t_small^*(x^*ℱ|_{U_étale}) ⟶ (x ∘ s)^*ℱ|_{R_étale}` of equation 076R for
the triangle `x ∘ t ≅ x ∘ s` through the target and the inverse of the 2-morphism of
Stacks 044S. -/
noncomputable abbrev quotientStackTargetComparison
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf)) :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS G.arrows.obj).property (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (quotientStackTargetLeg G) (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj
        G) (isFibredOneMorphism_quotientStackSourceProj G)
    (isFibredOneMorphism_quotientStackProj G) (quotientStackTwoArrowIso G) G.target
        (quotientStackTargetChartIso G)
    (isFiberedInGroupoids_quotientStack G) (isHomLift_quotientStackTwoArrowNat G)
    (fun _ => IsHomLift.id rfl)
    ((quotientStackToEtale G).obj F)

/-- The modules on the fppf site of the quotient stack: `Mod(𝒪_{[U/R]})`. -/
abbrev QuotientStackModules :=
  SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
    (isFiberedInGroupoids_quotientStack G) .fppf)

/-- **`ℱ ↦ (x ∘ s)^*ℱ|_{R_étale}`**, the common target of the two comparison maps of
Stacks 076S. -/
noncomputable abbrev quotientStackArrowRestriction (F : QuotientStackModules G) :=
  Space.etaleRestrictedModuleInverseImage C S hS (fibredCategory C S hS G.arrows.obj).val.p
    (quotientStack G).p (fibredCategory C S hS G.arrows.obj).property
    (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (quotientStackSourceLeg G ⋙ quotientStackProj G) (isFibredOneMorphism_quotientStackSourceProj
        G) ((quotientStackToEtale G).obj F)

/-! ### Charted points -/

/-- The total category of the pointwise groupoid fibration of `G` (Stacks 044Q): its objects over
`T` are the `T`-points of `U` and its vertical arrows over `T` are the `T`-points of `R`. -/
abbrev PointwiseFibration :=
  (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj

/-- The arrow of the pointwise groupoid fibration from the restriction of a point `a` of `U` along
`h : T' ⟶ T` to `a`: it lies over `h` and its arrow is an identity. -/
noncomputable def pointwiseSpecial {T T' : BigFppfOver C S hS} (h : T' ⟶ T) (a : G.objects.obj.obj
    (op T)) :
    (⟨T', G.objects.obj.map h.op a⟩ : PointwiseFibration G) ⟶ ⟨T, a⟩ := ⟨h, 𝟙 _⟩

/-- A *charted point* of `U`: a point of `U` over an affine object `T` of the site, together
with an affine étale chart of `U` and a factorization of the point through it. -/
structure ChartedPoint where
  /-- The affine object of the site the point lives over. -/
  T : BigFppfOver C S hS
  hT : IsAffineOver C S hS T
  /-- The point of `U`. -/
  pt : G.objects.obj.obj (op T)
  /-- The affine étale chart of `U`. -/
  W : Space.SmallEtale C S hS G.objects.obj
  hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
  /-- The factorization of the point through the chart. -/
  g : T ⟶ (Space.SmallEtale.toOver C S hS G.objects.obj).obj W
  hpt : pt = G.objects.obj.map g.op (yonedaEquiv W.obj.hom)

variable {G} in
/-- The point of the pointwise groupoid fibration underlying a charted point. -/
noncomputable def ChartedPoint.toPoint (c : ChartedPoint G) : PointwiseFibration G := ⟨c.T, c.pt⟩

/-- The charted points, with the arrows of the pointwise groupoid fibration between their
points. -/
abbrev ChartedPointCat := InducedCategory (PointwiseFibration G) (ChartedPoint.toPoint (G := G))

/-- The full embedding of the charted points into the quotient stack. -/
noncomputable def chartedPointFunctor : ChartedPointCat G ⥤ (quotientStack G).obj :=
  inducedFunctor _ ⋙ pointwiseToQuotientStack G

/-- The embedding of the charted points into the quotient stack is full. -/
instance : (chartedPointFunctor G).Full := by
  have := (fullyFaithfulPointwiseToQuotientStack G).full
  exact inferInstanceAs (inducedFunctor _ ⋙ pointwiseToQuotientStack G).Full

/-- The embedding of the charted points into the quotient stack is faithful. -/
instance : (chartedPointFunctor G).Faithful := by
  have := (fullyFaithfulPointwiseToQuotientStack G).faithful
  exact inferInstanceAs (inducedFunctor _ ⋙ pointwiseToQuotientStack G).Faithful

/-- The image in `[U/R]` of an arrow of the pointwise groupoid fibration lies over its base. -/
theorem isHomLift_pointwiseToQuotientStack_map {w w' : PointwiseFibration G} (m : w ⟶ w') :
    (quotientStack G).p.IsHomLift m.base ((pointwiseToQuotientStack G).map m) := by
  have : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      m.base m := IsHomLift.map _ m
  exact Functor.isHomLift_map_of_comp_eq (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq
    m.base m

/-- The object of the pointwise groupoid fibration underlying an object of its universe lift. -/
def prestackObjDown (w : (quotientPrestack G).obj) : PointwiseFibration G :=
  ULiftHom.objDown.{u + 1, u + 1} w

/-- **The charted points are cover-dense in `[U/R]`.**  An object of `[U/R]` is fppf locally the
image of a point of `U` by Stacks 044X, and a point of `U` factors fppf locally through an
affine étale chart by `AlgebraicGeometry.Space.generate_affineChartPresieve_mem`. -/
theorem isCoverDense_chartedPointFunctor :
    (chartedPointFunctor G).IsCoverDense
      (BigFppfOver.associatedTopology C S hS (quotientStack G).p .fppf) := by
  refine ⟨fun y => ?_⟩
  rw [Functor.mem_inheritedTopology_iff_functorPushforward (quotientStack G).p
    (BigFppfOver.baseOverTopology C S hS .fppf) (isFiberedInGroupoids_quotientStack G)]
  show _ ∈ BigFppfOver.topology C S hS _
  obtain ⟨R, hR, hess⟩ := essImage_toQuotientStack G ((quotientStack G).p.obj y) ⟨y, rfl⟩
  refine (BigFppfOver.topology C S hS).superset_covering ?_
    ((BigFppfOver.topology C S hS).bind_covering
      (R := fun V k hk => Sieve.pullback (eqToHom (hess hk).choose.2.symm)
        (Sieve.generate (Space.affineChartPresieve C S hS G.objects
          (prestackObjDown G (hess hk).choose.1).fiber))) hR
      (fun V k hk => (BigFppfOver.topology C S hS).pullback_stable _
        (Space.generate_affineChartPresieve_mem C S hS G.objects _)))
  intro Y f hf
  obtain ⟨V, f₁, k, hk, hf₁, hfac⟩ := hf
  obtain ⟨V'', e, h, ⟨hV'', W, hW, g, hg⟩, hfac₁⟩ := hf₁
  have hiso := (hess hk).choose_spec
  revert h hg hfac₁ hiso
  generalize (hess hk).choose = w
  intro h hfac₁ hg hiso
  obtain ⟨iso⟩ := hiso
  obtain ⟨w, hwV⟩ := w
  let a := (prestackObjDown G w).fiber
  let c : ChartedPoint G := ⟨V'', hV'', G.objects.obj.map h.op a, W, hW, g, hg⟩
  let m₁ : (chartedPointFunctor G).obj c ⟶ (toQuotientStack G).obj w :=
    (pointwiseToQuotientStack G).map (pointwiseSpecial G h a)
  let m : (chartedPointFunctor G).obj c ⟶ y :=
    m₁ ≫ iso.hom.1 ≫ Functor.IsPreFibered.pullbackMap (p := (quotientStack G).p)
      (rfl : (quotientStack G).p.obj y = _) k
  refine ⟨_, m, e, ⟨{ obj := c, lift := 𝟙 _, map := m, fac := Category.id_comp _ }⟩, ?_⟩
  have h₁ : (quotientStack G).p.IsHomLift h m₁ :=
    isHomLift_pointwiseToQuotientStack_map G (pointwiseSpecial G h a)
  have h₂ : (quotientStack G).p.IsHomLift (𝟙 V) iso.hom.1 := iso.hom.2
  have h₃ : (quotientStack G).p.map m = h ≫ eqToHom hwV ≫ k := by
    simp only [m, Functor.map_comp, IsHomLift.fac' (quotientStack G).p h m₁,
      IsHomLift.fac' (quotientStack G).p (𝟙 V) iso.hom.1,
      IsHomLift.fac' (quotientStack G).p k (Functor.IsPreFibered.pullbackMap _ k)]
    simp only [eqToHom_trans_assoc, Category.id_comp, eqToHom_refl, Category.assoc]
    exact Category.id_comp _
  rw [h₃, ← hfac, show f₁ = e ≫ h ≫ eqToHom hwV by
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
      (congrArg (· ≫ eqToHom hwV) hfac₁).symm]
  simp only [Category.assoc]
  rfl

/-- **A section of a module over a presented object is determined locally on the base.**  Two
sections over the image of a point `w` which agree after restriction along the arrows
`AlgebraicGeometry.Stack.pointwiseSpecial` of a covering family of the base of `w` are equal. -/
theorem pointwiseSections_ext
    (H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf))
    (w : PointwiseFibration G) {P : Presieve w.base}
    (hP : Sieve.generate P ∈ BigFppfOver.topology C S hS w.base)
    {σ τ : H.val.obj (op ((pointwiseToQuotientStack G).obj w))}
    (h : ∀ ⦃V : BigFppfOver C S hS⦄ (k : V ⟶ w.base), P k →
      H.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k w.fiber)).op σ =
        H.val.map ((pointwiseToQuotientStack G).map (pointwiseSpecial G k w.fiber)).op τ) :
    σ = τ := by
  have hmem := Functor.functorPullback_mem_inheritedTopology (quotientStack G).p
    (BigFppfOver.baseOverTopology C S hS .fppf) ((pointwiseToQuotientStack G).obj w) hP
  refine (H.isSheaf_sections.isSheafFor _ hmem).isSeparatedFor.ext ?_
  intro z f hf
  obtain ⟨V, e, k, hk, hfac⟩ := hf
  let m := (pointwiseToQuotientStack G).map (pointwiseSpecial G k w.fiber)
  have hm : (quotientStack G).p.IsHomLift k m :=
    isHomLift_pointwiseToQuotientStack_map G (pointwiseSpecial G k w.fiber)
  have hl : (quotientStack G).p.IsHomLift (e ≫ k) f := by
    rw [hfac]
    exact IsHomLift.map _ f
  obtain ⟨f', ⟨-, hf'⟩, -⟩ := @Functor.IsStronglyCartesian.universal_property' _ _ _ _
    (quotientStack G).p _ _ _ _ k m
    ((isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift k m) z e f hl
  show H.val.map f.op σ = H.val.map f.op τ
  rw [← hf']
  exact (H.val.map_comp_apply m.op f'.op σ).trans
    ((congrArg (H.val.map f'.op) (h k hk)).trans (H.val.map_comp_apply m.op f'.op τ).symm)

/-! ### Points of charts and chart diagrams -/

/-- The point of the pointwise groupoid fibration given by an étale chart of `U`: its image in
`[U/R]` is `x(u_U W)`. -/
noncomputable abbrev chartPoint (W : Space.SmallEtale C S hS G.objects.obj) : PointwiseFibration G
    :=
  ⟨(Space.SmallEtale.toOver C S hS G.objects.obj).obj W, yonedaEquiv W.obj.hom⟩

/-- The point `s ∘ v` of `U` given by an étale chart `v` of `R`: its image in `[U/R]` is
`(x ∘ s)(u_R V)`. -/
noncomputable abbrev arrowChartPoint (V : Space.SmallEtale C S hS G.arrows.obj) :
    PointwiseFibration G :=
  ⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj V,
    G.source.hom.app _ (yonedaEquiv V.obj.hom)⟩

/-- The coefficient homomorphism of an étale chart restriction is the identity on sections over a
chart, up to the identification of the underlying objects. -/
private theorem etaleChartStructureHom_apply_heq {U : AlgebraicSpaces C S hS} {𝒰 𝒳 : Type*}
    [Category 𝒰] [Category 𝒳] (p : 𝒰 ⥤ BigFppfOver C S hS) (r : 𝒳 ⥤ BigFppfOver C S hS)
    (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) (W : Space.SmallEtale C S hS U.1)
    (c : (Space.structureRingSheaf C S hS U).obj.obj (op W)) :
    HEq ((Space.etaleChartStructureHom C S hS p r hp hr eU f hf).hom.app (op W) c) c := by
  rw [Space.etaleChartStructureHom_app]
  have key : ∀ {X Y : BigFppfOver C S hS} (e : X = Y)
      (c : (BigFppfOver.structureSheaf C S hS).obj.obj (op Y)),
      HEq ((BigFppfOver.structureSheaf C S hS).obj.map (eqToHom e).op c) c := by
    rintro X Y rfl c
    rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
    exact HEq.rfl
  exact key _ c

/-- The identification of structure sheaves along `x` at an étale chart of `U` is the identity. -/
theorem quotientStackProj_chartStructureHom_apply (W : Space.SmallEtale C S hS G.objects.obj)
    (c : (Space.structureRingSheaf C S hS G.objects).obj.obj (op W)) :
    (Space.etaleChartStructureHom C S hS (fibredCategory C S hS G.objects.obj).val.p
      (quotientStack G).p (fibredCategory C S hS G.objects.obj).property
      (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
      (quotientStackProj G) (isFibredOneMorphism_quotientStackProj G)).hom.app (op W) c = c :=
  eq_of_heq (etaleChartStructureHom_apply_heq _ _ _ _ _ _ _ W c)

/-- The identification of structure sheaves along `x ∘ s` at an étale chart of `R` is the
identity. -/
theorem quotientStackSourceProj_chartStructureHom_apply (V : Space.SmallEtale C S hS G.arrows.obj)
    (c : (Space.structureRingSheaf C S hS G.arrows).obj.obj (op V)) :
    (Space.etaleChartStructureHom C S hS (fibredCategory C S hS G.arrows.obj).val.p
      (quotientStack G).p (fibredCategory C S hS G.arrows.obj).property
      (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
      (quotientStackSourceLeg G ⋙ quotientStackProj G) (isFibredOneMorphism_quotientStackSourceProj
          G)).hom.app (op V) c = c :=
  eq_of_heq (etaleChartStructureHom_apply_heq _ _ _ _ _ _ _ V c)

variable {G}

/-- The arrow from the point of a charted point to the point of its chart: it lies over the
factorization and its arrow is an identity. -/
noncomputable def ChartedPoint.special (c : ChartedPoint G) : c.toPoint ⟶ chartPoint G c.W :=
  ⟨c.g, eqToHom c.hpt⟩

/-- The restriction of a charted point along a morphism from an affine object. -/
noncomputable def ChartedPoint.restrict (c : ChartedPoint G) {T' : BigFppfOver C S hS}
    (k : T' ⟶ c.T) (hT' : IsAffineOver C S hS T') : ChartedPoint G where
  T := T'
  hT := hT'
  pt := G.objects.obj.map k.op c.pt
  W := c.W
  hW := c.hW
  g := k ≫ c.g
  hpt := by rw [c.hpt, op_comp, FunctorToTypes.map_comp_apply]

/-- The point of a restricted charted point is the restricted point. -/
theorem ChartedPoint.restrict_toPoint (c : ChartedPoint G) {T' : BigFppfOver C S hS}
    (k : T' ⟶ c.T) (hT' : IsAffineOver C S hS T') :
    (c.restrict k hT').toPoint = ⟨T', G.objects.obj.map k.op c.pt⟩ := rfl

/-- Restricting a charted point and then mapping to its chart is mapping to the chart. -/
theorem ChartedPoint.special_restrict (c : ChartedPoint G) {T' : BigFppfOver C S hS}
    (k : T' ⟶ c.T) (hT' : IsAffineOver C S hS T') :
    pointwiseSpecial G k c.pt ≫ c.special = (c.restrict k hT').special := by
  apply pointwiseHom_ext G.toGroupoidInFunctors
  · rfl
  · refine (pointwiseComp_arrow_of_left_identity G.toGroupoidInFunctors _ _ ?_).trans ?_
    · exact evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ rfl
    · show G.toGroupoidInFunctors.arrows.map k.op
          (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ (eqToHom c.hpt)).1 =
        (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ (eqToHom (c.restrict k hT').hpt)).1
      refine (congrArg (G.toGroupoidInFunctors.arrows.map k.op)
        (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ c.hpt)).trans ?_
      refine (Deformation.evalMap_identity G.toGroupoidInFunctors k.op c.pt).trans ?_
      exact (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ _).symm

variable (G)

/-- The point of a chart of `X` mapped by `a : X ⟶ U` is the restriction of the point of a chart
of `U`, for a commutative square of charts. -/
theorem chartDiagram_point_eq {X : AlgebraicSpaces C S hS} (a : X.1 ⟶ G.objects.obj)
    (V : Space.SmallEtale C S hS X.1) (W : Space.SmallEtale C S hS G.objects.obj)
    (g : (Space.SmallEtale.toOver C S hS X.1).obj V ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
    (hg : V.obj.hom ≫ a = yoneda.map g ≫ W.obj.hom) :
    a.app _ (yonedaEquiv V.obj.hom) = G.objects.obj.map g.op (yonedaEquiv W.obj.hom) := by
  rw [← yonedaEquiv_comp, hg, ← yonedaEquiv_naturality]

/-- The arrow of the pointwise groupoid fibration underlying a commutative square of étale charts
over `a : X ⟶ U`: it lies over the vertical morphism and its arrow is an identity. -/
noncomputable def chartDiagramPoint {X : AlgebraicSpaces C S hS} (a : X.1 ⟶ G.objects.obj)
    (V : Space.SmallEtale C S hS X.1) (W : Space.SmallEtale C S hS G.objects.obj)
    (g : (Space.SmallEtale.toOver C S hS X.1).obj V ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
    (hg : V.obj.hom ≫ a = yoneda.map g ≫ W.obj.hom) :
    (⟨(Space.SmallEtale.toOver C S hS X.1).obj V, a.app _ (yonedaEquiv V.obj.hom)⟩ :
      PointwiseFibration G) ⟶ chartPoint G W :=
  ⟨g, eqToHom (chartDiagram_point_eq G a V W g hg)⟩

/-- **The comparison morphism of the triangle through the source**, on a commutative square of
charts over `s`, is the image in `[U/R]` of the arrow of the pointwise fibration underlying it. -/
theorem quotientStackSource_comparisonMorphism (d : Space.ChartDiagram C S hS G.arrows.obj
    G.objects.obj
      G.source.hom) :
    Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
      (fibredCategory C S hS G.objects.obj).val.p
      (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl
          _)
      (quotientStackSourceLeg G) (quotientStackSourceLeg G ⋙ quotientStackProj G)
          (quotientStackProj G) (Iso.refl _) G.source (quotientStackSourceChartIso G) d =
    (pointwiseToQuotientStack G).map (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm) := by
  unfold Space.comparisonMorphism Space.comparisonChartHom
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  show (pointwiseToQuotientStack G).map ((pointwiseObjectInclusion G).map _) = _
  congr 1

/-- **The comparison morphism of the triangle through the target**, on a commutative square of
charts over `t`, is the image in `[U/R]` of the arrow given by the point of `R` of the chart,
followed by the arrow underlying the square. -/
theorem quotientStackTarget_comparisonMorphism (d : Space.ChartDiagram C S hS G.arrows.obj
    G.objects.obj
      G.target.hom) :
    ∃ g : arrowChartPoint G d.U ⟶
        ⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U,
          G.target.hom.app _ (yonedaEquiv d.U.obj.hom)⟩,
      g.base = 𝟙 _ ∧
      (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ g.fiber).1 = yonedaEquiv d.U.obj.hom ∧
      Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (quotientStackTargetLeg G) (quotientStackSourceLeg G ⋙ quotientStackProj G)
            (quotientStackProj G) (quotientStackTwoArrowIso G) G.target
                (quotientStackTargetChartIso G) d =
      (pointwiseToQuotientStack G).map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm) := by
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := quotientStackTwoArrow_app G
    ((Space.restrictionFunctor C S hS G.arrows.obj (fibredCategory C S hS G.arrows.obj).val.p
      (StacksRepresentableCFG.EquivalenceOver.refl _)).obj d.U)
  refine ⟨g, hg₁, hg₂, ?_⟩
  unfold Space.comparisonMorphism Space.comparisonChartHom
  refine Eq.trans ?_ ((pointwiseToQuotientStack G).map_comp g _).symm
  have h1 : (quotientStackTwoArrowIso G).inv.app ((Space.restrictionFunctor C S hS G.arrows.obj
      (fibredCategory C S hS G.arrows.obj).val.p
      (StacksRepresentableCFG.EquivalenceOver.refl _)).obj d.U) =
      (pointwiseToQuotientStack G).map g := eq_of_heq hg₃
  rw [h1]
  congr 1

end AlgebraicGeometry.Stack

end
