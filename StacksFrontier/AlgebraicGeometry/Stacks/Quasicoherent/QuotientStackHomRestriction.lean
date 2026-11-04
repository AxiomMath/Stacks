module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartExtension

/-!
# Maps out of a quasi-coherent module on a quotient stack (Stacks 076S)

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` whose source and target are flat
and locally of finite presentation, let `𝒳 = [U/R]` be its quotient stack and `x` the object of
`𝒳` over `U`.  Stacks 076S says that for a quasi-coherent `𝒪_𝒳`-module `ℱ` and an arbitrary
`𝒪_𝒳`-module `ℋ` the map

```
Hom_{𝒪_𝒳}(ℱ, ℋ) ⟶ Hom_{𝒪_U}(x^*ℱ|_{U_étale}, x^*ℋ|_{U_étale}),   ψ ↦ x^*ψ|_{U_étale}
```

is injective, and that its image consists of exactly those `φ` which fit into a commutative
diagram

```
s^*(x^*ℱ|_U) ⟶ (x ∘ s)^*ℱ|_R = (x ∘ t)^*ℱ|_R ⟵ t^*(x^*ℱ|_U)
     | s^*φ                                        | t^*φ
     v                                             v
s^*(x^*ℋ|_U) ⟶ (x ∘ s)^*ℋ|_R = (x ∘ t)^*ℋ|_R ⟵ t^*(x^*ℋ|_U)
```

of modules on `R_étale`, whose horizontal arrows are the comparison maps of equation 076R (here
`s^* = s_small^*`, `t^* = t_small^*`, `·|_U = ·|_{U_étale}` and `·|_R = ·|_{R_étale}`).

**The statement.**  `AlgebraicGeometry.Stack.quotientStackObjectRestrictionMap_injective_and_range`
is the whole lemma.  "Gives rise to a commutative diagram" is read as: there is a morphism `χ` of
modules on `R_étale`, the middle vertical arrow, making both squares commute.  The identification
`(x ∘ s)^*ℱ|_{R_étale} = (x ∘ t)^*ℱ|_{R_étale}` is carried by the 2-morphism of Stacks 044S: the
right-hand comparison map is the one of the triangle `x ∘ t ≅ x ∘ s`, so both comparison maps
land in `(x ∘ s)^*ℱ|_{R_étale}`.  The modules are the sheaves of modules on the fppf site of
`𝒳` (Stacks 06WB) and quasi-coherence is that of Stacks 06WG.  The hypotheses that `s` and `t`
are flat and locally of finite presentation are those of the source; as in the source, the
proof does not use them (they serve there to make `𝒳` an algebraic stack, Stacks 06FI).

**The proof.**  The source reduces to the pointwise quotient `[U/_pR]` and reads `ℱ` through the
quasi-coherent module on the groupoid that Stacks 06WT attaches to it.  Here the same argument
is run directly on `[U/R]`, through its full subcategory of *charted points*
(`AlgebraicGeometry.Stack.ChartedPoint`): points of `U` over affine objects, factored through
affine étale charts of `U`.  It is cover-dense for the fppf topology, and since `ℱ` is
quasi-coherent its sections over a charted point are the base change of its sections over the
chart.  So a morphism `ψ` is determined by `x^*ψ|_{U_étale}` (injectivity), and a compatible `φ`
defines a linear map over each charted point which, by the compatibility of the squares, is
natural for every arrow of `𝒳` between charted points
(`AlgebraicGeometry.Stack.chartedExtension_naturality`); a cover-dense full subcategory then
glues these to a morphism of sheaves on `𝒳` (`CategoryTheory.Functor.IsCoverDense.sheafHom`),
which is linear and restricts to `φ`.  That the image of every `ψ` is compatible is the
naturality of the comparison maps of equation 076R in the module,
`AlgebraicGeometry.Space.comparison_etaleRestrictedHom`.

## Main results

* `AlgebraicGeometry.Stack.quotientStackObjectRestrictionMap_injective_and_range`:
  **Stacks 076S**.
* `AlgebraicGeometry.Stack.quotientStackObjectRestrictionMap_injective`: injectivity, for an
  arbitrary groupoid in algebraic spaces.
* `AlgebraicGeometry.Stack.chartedGluedHom` and
  `AlgebraicGeometry.Stack.quotientStackObjectRestrictionMap_chartedGluedHom`: the morphism of
  modules glued from a compatible `φ`, and that it restricts to `φ`.

## References

* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

section Glue

attribute [local instance] FibredSite.objModule

variable {F H : QuotientStackModules G} (φ : quotientStackObjectRestriction G F ⟶
    quotientStackObjectRestriction G H) (χ : quotientStackArrowRestriction G F ⟶
        quotientStackArrowRestriction G H)
  (hF : F.IsQuasicoherentOnSite)

/-- Sections of a module on `[U/R]` restrict along a composite in two steps. -/
private theorem map_comp_op_apply_of_eq (M : QuotientStackModules G) {a b c : (quotientStack G).obj}
    {k : a ⟶ c} {f : a ⟶ b} {g : b ⟶ c} (h : k = f ≫ g) (z : M.val.obj (op c)) :
    M.val.map k.op z = M.val.map f.op (M.val.map g.op z) := by
  subst h
  exact M.val.map_comp_apply _ _ z

/-- **The extensions over charted points are natural** for every arrow of `[U/R]` between charted
points.  Both sides are semilinear and agree on restrictions of sections over the chart of the
target, where they are `AlgebraicGeometry.Stack.chartedExtension_naturality`. -/
theorem chartedExtension_map
    (hsqs : quotientStackSourceComparison G F ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ quotientStackSourceComparison G H)
    (hsqt : quotientStackTargetComparison G F ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ quotientStackTargetComparison G H)
    {c₁ c₂ : ChartedPointCat G} (m : c₁ ⟶ c₂)
    (σ : F.val.obj (op ((chartedPointFunctor G).obj c₂))) :
    chartedExtension φ hF c₁ (F.val.map ((chartedPointFunctor G).map m).op σ) =
      H.val.map ((chartedPointFunctor G).map m).op (chartedExtension φ hF c₂ σ) := by
  let τ : FibredSite.objRing C S hS (quotientStack G).p ((chartedPointFunctor G).obj c₂) →+*
      FibredSite.objRing C S hS (quotientStack G).p ((chartedPointFunctor G).obj c₁) :=
    ((FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf).obj.map ((chartedPointFunctor G).map m).op).hom
  let L₁ : F.val.obj (op ((chartedPointFunctor G).obj c₂)) →ₛₗ[τ]
      H.val.obj (op ((chartedPointFunctor G).obj c₁)) :=
    { toFun := fun t => chartedExtension φ hF c₁ (F.val.map ((chartedPointFunctor G).map m).op t)
      map_add' := fun a b => (congrArg (chartedExtension φ hF c₁)
        (map_add (F.val.map ((chartedPointFunctor G).map m).op).hom a b)).trans (map_add _ _ _)
      map_smul' := fun r a => (congrArg (chartedExtension φ hF c₁)
        (F.val.map_smul ((chartedPointFunctor G).map m).op r a)).trans (map_smul _ _ _) }
  let L₂ : F.val.obj (op ((chartedPointFunctor G).obj c₂)) →ₛₗ[τ]
      H.val.obj (op ((chartedPointFunctor G).obj c₁)) :=
    { toFun := fun t => H.val.map ((chartedPointFunctor G).map m).op (chartedExtension φ hF c₂ t)
      map_add' := fun a b => (congrArg (H.val.map ((chartedPointFunctor G).map m).op)
        (map_add (chartedExtension φ hF c₂) a b)).trans (map_add _ _ _)
      map_smul' := fun r a => (congrArg (H.val.map ((chartedPointFunctor G).map m).op)
        (map_smul (chartedExtension φ hF c₂) r a)).trans
        (H.val.map_smul ((chartedPointFunctor G).map m).op r _) }
  have := FibredSite.semilinearMap_ext_of_restriction F hF c₂.chartMap c₂.hW c₂.hT
    (θ₁ := L₁) (θ₂ := L₂) (fun x => by
      show chartedExtension φ hF c₁ (F.val.map ((chartedPointFunctor G).map m).op
          (F.val.map c₂.chartMap.op x)) =
        H.val.map ((chartedPointFunctor G).map m).op (chartedExtension φ hF c₂
          (F.val.map c₂.chartMap.op x))
      rw [chartedExtension_chartMap]
      have hm : (chartedPointFunctor G).map m = (pointwiseToQuotientStack G).map m.hom := rfl
      rw [hm]
      have hq : (pointwiseToQuotientStack G).map (m.hom ≫ c₂.special) =
          (pointwiseToQuotientStack G).map m.hom ≫ c₂.chartMap :=
        (pointwiseToQuotientStack G).map_comp _ _
      have e1 := map_comp_op_apply_of_eq F hq x
      have e2 := map_comp_op_apply_of_eq H hq (chartSectionValue φ c₂.W x)
      refine (congrArg (chartedExtension φ hF c₁) e1.symm).trans (Eq.trans ?_ e2)
      exact chartedExtension_naturality φ χ hF hsqs hsqt c₁ c₂.hW _ x)
  exact LinearMap.congr_fun this σ

variable (G) in
/-- The fppf topology of the quotient stack, inherited from the big fppf site (Stacks 06TP). -/
noncomputable abbrev quotientStackFppfTopology := BigFppfOver.associatedTopology C S hS
    (quotientStack G).p .fppf

/-- The charted points are cover-dense, as an instance. -/
instance : (chartedPointFunctor G).IsCoverDense (quotientStackFppfTopology G) :=
    isCoverDense_chartedPointFunctor G

/-- The sheaf of sets of sections of a module on the fppf site of `[U/R]`. -/
noncomputable abbrev quotientStackSectionsSheaf (M : QuotientStackModules G) : Sheaf
    (quotientStackFppfTopology G) (Type u) :=
  ⟨M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}, M.isSheaf_sections⟩

/-- A section of a module on `[U/R]` is determined by its restrictions to charted points. -/
theorem quotientStackSections_ext (M : QuotientStackModules G) {y : (quotientStack G).obj} {σ τ :
    M.val.obj (op y)}
    (h : ∀ ⦃c : ChartedPointCat G⦄ (f : (chartedPointFunctor G).obj c ⟶ y),
      M.val.map f.op σ = M.val.map f.op τ) : σ = τ :=
  Functor.IsCoverDense.ext (chartedPointFunctor G) (quotientStackSectionsSheaf M) y h

variable (hsqs : quotientStackSourceComparison G F ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ quotientStackSourceComparison G H)
    (hsqt : quotientStackTargetComparison G F ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ quotientStackTargetComparison G H)

/-- The extensions over the charted points, as a morphism of abelian presheaves on the charted
points. -/
noncomputable def chartedExtensionTrans :
    (chartedPointFunctor G).op ⋙ F.val.presheaf ⟶ (chartedPointFunctor G).op ⋙ H.val.presheaf where
  app c := AddCommGrpCat.ofHom (chartedExtension φ hF c.unop).toAddMonoidHom
  naturality c₁ c₂ m := by
    ext σ
    exact chartedExtension_map φ χ hF hsqs hsqt m.unop σ

/-- The morphism of abelian presheaves on `[U/R]` glued from the extensions over the charted
points along the cover-dense full subcategory of charted points. -/
noncomputable def chartedGluedPresheafHom : F.val.presheaf ⟶ H.val.presheaf :=
  (Functor.IsCoverDense.restrictHomEquivHom (G := chartedPointFunctor G) (K :=
      quotientStackFppfTopology G)
    (ℱ' := ⟨H.val.presheaf, H.isSheaf⟩)) (chartedExtensionTrans φ χ hF hsqs hsqt)

/-- Over a charted point, the glued morphism is the extension. -/
theorem chartedGluedPresheafHom_app (c : ChartedPointCat G)
    (σ : F.val.obj (op ((chartedPointFunctor G).obj c))) :
    (chartedGluedPresheafHom φ χ hF hsqs hsqt).app (op ((chartedPointFunctor G).obj c)) σ =
      chartedExtension φ hF c σ := by
  have h := Functor.IsCoverDense.sheafHom_restrict_eq (G := chartedPointFunctor G) (K :=
      quotientStackFppfTopology G)
    (ℱ' := ⟨H.val.presheaf, H.isSheaf⟩) (chartedExtensionTrans φ χ hF hsqs hsqt)
  exact congrArg (fun f => f σ) (congrArg (fun t => (t.app (op c)).hom) h)

/-- Naturality of the glued morphism, on sections. -/
theorem chartedGluedPresheafHom_naturality {y y' : (quotientStack G).obj} (f : y' ⟶ y)
    (σ : F.val.obj (op y)) :
    (chartedGluedPresheafHom φ χ hF hsqs hsqt).app (op y') (F.val.map f.op σ) =
      H.val.map f.op ((chartedGluedPresheafHom φ χ hF hsqs hsqt).app (op y) σ) :=
  NatTrans.naturality_apply (chartedGluedPresheafHom φ χ hF hsqs hsqt) f.op σ

/-- The glued morphism is linear: it is so over charted points, and those cover. -/
theorem chartedGluedPresheafHom_smul (y : (quotientStack G).obj)
    (r : (FibredSite.ringStructureSheafCore C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) .fppf).obj.obj (op y))
    (σ : F.val.obj (op y)) :
    (chartedGluedPresheafHom φ χ hF hsqs hsqt).app (op y) (r • σ) =
      r • (chartedGluedPresheafHom φ χ hF hsqs hsqt).app (op y) σ := by
  refine quotientStackSections_ext H (fun c f => ?_)
  rw [← chartedGluedPresheafHom_naturality, F.val.map_smul]
  refine Eq.trans ?_ (H.val.map_smul f.op r _).symm
  rw [← chartedGluedPresheafHom_naturality]
  refine (chartedGluedPresheafHom_app φ χ hF hsqs hsqt c _).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => _ • t) (chartedGluedPresheafHom_app φ χ hF hsqs hsqt c
      _)).symm
  exact map_smul (chartedExtension φ hF c) _ _

/-- **The morphism of modules glued from a compatible `φ`.** -/
noncomputable def chartedGluedHom : F ⟶ H :=
  ⟨PresheafOfModules.homMk (chartedGluedPresheafHom φ χ hF hsqs hsqt)
    (fun y r σ => chartedGluedPresheafHom_smul φ χ hF hsqs hsqt y.unop r σ)⟩

/-- The sections of the glued morphism of modules. -/
theorem chartedGluedHom_app (y : (quotientStack G).obj) (σ : F.val.obj (op y)) :
    (chartedGluedHom φ χ hF hsqs hsqt).val.app (op y) σ =
      (chartedGluedPresheafHom φ χ hF hsqs hsqt).app (op y) σ := rfl

/-- The point of a chart is the restriction of the point of a chart it maps to. -/
theorem chartPointHom_eq {W₁ W₂ : Space.SmallEtale C S hS G.objects.obj} (i : W₁ ⟶ W₂) :
    yonedaEquiv W₁.obj.hom = G.objects.obj.map i.hom.left.op (yonedaEquiv W₂.obj.hom) := by
  rw [yonedaEquiv_naturality]
  exact congrArg yonedaEquiv (CostructuredArrow.w i.hom).symm

variable (G) in
/-- The arrow of the pointwise groupoid fibration underlying a morphism of étale charts of `U`. -/
noncomputable def chartPointHom {W₁ W₂ : Space.SmallEtale C S hS G.objects.obj} (i : W₁ ⟶ W₂) :
    chartPoint G W₁ ⟶ chartPoint G W₂ :=
  ⟨i.hom.left, eqToHom (chartPointHom_eq i)⟩

/-- `φ` is natural for morphisms of étale charts of `U`, on sections. -/
theorem chartSectionValue_naturality {W₁ W₂ : Space.SmallEtale C S hS G.objects.obj} (i : W₁ ⟶ W₂)
    (t : F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G W₂)))) :
    chartSectionValue φ W₁ (F.val.map ((pointwiseToQuotientStack G).map (chartPointHom G i)).op t) =
      H.val.map ((pointwiseToQuotientStack G).map (chartPointHom G i)).op (chartSectionValue φ W₂
          t) := by
  have h := congrArg (fun f => f.hom t) (φ.val.naturality i.op)
  have e : (pointwiseToQuotientStack G).map (chartPointHom G i) =
      (Space.etaleChartToFibred C S hS (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _) (quotientStackProj G)).map i := rfl
  rw [e]
  exact h

/-- Over the image of an étale chart of `U`, the glued morphism is `φ`.  An affine open cover of
the chart reduces this to charted points, where the glued morphism is the extension. -/
theorem chartedGluedHom_chart (W : Space.SmallEtale C S hS G.objects.obj)
    (t : F.val.obj (op ((pointwiseToQuotientStack G).obj (chartPoint G W)))) :
    (chartedGluedPresheafHom φ χ hF hsqs hsqt).app (op ((pointwiseToQuotientStack G).obj
      (chartPoint G W))) t = chartSectionValue φ W t := by
  obtain ⟨J, V, π, hV, hπ, hcov, -⟩ := BigFppfOver.exists_affine_open_cover' C S hS
    ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
  refine pointwiseSections_ext G H (chartPoint G W)
    (P := fun T' k => IsAffineOver C S hS T' ∧ ∃ (j : J) (e : T' ⟶ V j), e ≫ π j = k)
    ((BigFppfOver.topology C S hS).superset_covering ?_
      (BigFppfOver.generate_affine_mem C S hS hcov)) (fun T' k hk => ?_)
  · rintro T'' k ⟨T', e₁, e₂, ⟨he₂, hT'⟩, rfl⟩
    obtain ⟨T₃, e₃, e₄, ⟨j⟩, rfl⟩ := he₂
    exact ⟨T', e₁, e₃ ≫ π j, ⟨hT', j, e₃, rfl⟩, rfl⟩
  obtain ⟨hT', j, e, rfl⟩ := hk
  have hπj : Space.IsEtaleChart C S hS G.objects.obj
      (CostructuredArrow.mk (yoneda.map (π j) ≫ W.obj.hom)) := by
    have := hπ j
    exact Space.etale_comp_of_scheme C S hS (π j) W.obj.hom inferInstance W.property
  let Wj : Space.SmallEtale C S hS G.objects.obj := ⟨_, hπj⟩
  let ι : Wj ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk (π j) rfl)
  let c : ChartedPoint G := ⟨T', hT', G.objects.obj.map (e ≫ π j).op (yonedaEquiv W.obj.hom),
    Wj, hV j, e, by
      rw [op_comp, FunctorToTypes.map_comp_apply]
      exact congrArg (G.objects.obj.map e.op) (chartPointHom_eq ι).symm⟩
  have hsp : pointwiseSpecial G (e ≫ π j) (yonedaEquiv W.obj.hom) =
      c.special ≫ chartPointHom G ι := by
    apply pointwiseHom_ext G.toGroupoidInFunctors
    · rfl
    · refine Eq.trans ?_ (pointwiseArrow_comp_of_right G _ _
        (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ (chartPointHom_eq ι))).symm
      exact (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ c.hpt).symm
  let sp := (pointwiseToQuotientStack G).map (pointwiseSpecial G (e ≫ π j)
      (yonedaEquiv W.obj.hom))
  let m := (pointwiseToQuotientStack G).map (chartPointHom G ι)
  have hsp' : sp = c.chartMap ≫ m :=
    (congrArg (pointwiseToQuotientStack G).map hsp).trans
      ((pointwiseToQuotientStack G).map_comp _ _)
  refine (chartedGluedPresheafHom_naturality φ χ hF hsqs hsqt sp t).symm.trans ?_
  refine (chartedGluedPresheafHom_app φ χ hF hsqs hsqt c (F.val.map sp.op t)).trans ?_
  rw [map_comp_op_apply_of_eq F hsp']
  refine (chartedExtension_chartMap φ hF c (F.val.map m.op t)).trans ?_
  rw [chartSectionValue_naturality]
  exact (map_comp_op_apply_of_eq H hsp' _).symm

/-- **The glued morphism restricts to `φ`.** -/
theorem quotientStackObjectRestrictionMap_chartedGluedHom : quotientStackObjectRestrictionMap G
    (chartedGluedHom φ χ hF hsqs hsqt) = φ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  exact chartedGluedHom_chart φ χ hF hsqs hsqt W.unop t

end Glue

section Restriction

attribute [local instance] FibredSite.objModule

variable {F H : QuotientStackModules G} (hF : F.IsQuasicoherentOnSite)

/-- A morphism of modules is, over a charted point, the extension of its restriction to `U`. -/
theorem app_eq_chartedExtension (ψ : F ⟶ H) (c : ChartedPoint G)
    (σ : F.val.obj (op ((chartedPointFunctor G).obj c))) :
    ψ.val.app (op ((chartedPointFunctor G).obj c)) σ =
      chartedExtension (quotientStackObjectRestrictionMap G ψ) hF c σ := by
  let L : F.val.obj (op ((chartedPointFunctor G).obj c)) →ₗ[
      FibredSite.objRing C S hS (quotientStack G).p ((chartedPointFunctor G).obj c)]
      H.val.obj (op ((chartedPointFunctor G).obj c)) :=
    { toFun := fun x => ψ.val.app (op ((chartedPointFunctor G).obj c)) x
      map_add' := map_add (ψ.val.app (op ((chartedPointFunctor G).obj c))).hom
      map_smul' := (ψ.val.app (op ((chartedPointFunctor G).obj c))).hom.map_smul }
  have := FibredSite.semilinearMap_ext_of_restriction F hF c.chartMap c.hW c.hT (θ₁ := L)
    (θ₂ := chartedExtension (quotientStackObjectRestrictionMap G ψ) hF c) (fun x => by
      rw [chartedExtension_chartMap]
      exact PresheafOfModules.naturality_apply ψ.val c.chartMap.op x)
  exact LinearMap.congr_fun this σ

include hF in
/-- **Injectivity in Stacks 076S**: a morphism out of a quasi-coherent module on `[U/R]` is
determined by its restriction `x^*ψ|_{U_étale}`, for every groupoid in algebraic spaces. -/
theorem quotientStackObjectRestrictionMap_injective {ψ₁ ψ₂ : F ⟶ H} (h :
    quotientStackObjectRestrictionMap G ψ₁ = quotientStackObjectRestrictionMap G ψ₂) :
    ψ₁ = ψ₂ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun y => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun σ => ?_)
  refine quotientStackSections_ext H (fun c f => ?_)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  refine (app_eq_chartedExtension hF ψ₁ c _).trans ?_
  refine Eq.trans ?_ (app_eq_chartedExtension hF ψ₂ c _).symm
  rw [h]

end Restriction

/-- **`ψ ↦ (x ∘ s)^*ψ|_{R_étale}`** on morphisms of modules on the fppf site of `[U/R]`. -/
noncomputable abbrev quotientStackArrowRestrictionMap {F H : QuotientStackModules G} (ψ : F ⟶ H) :
    quotientStackArrowRestriction G F ⟶ quotientStackArrowRestriction G H :=
  Space.etaleRestrictedModuleInverseImageMap C S hS (fibredCategory C S hS G.arrows.obj).val.p
    (quotientStack G).p (fibredCategory C S hS G.arrows.obj).property
    (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (quotientStackSourceLeg G ⋙ quotientStackProj G) (isFibredOneMorphism_quotientStackSourceProj
        G) ((quotientStackToEtale G).map ψ)

/-- The square through the source commutes for the restriction of a morphism of modules: the
comparison map of equation 076R is natural in the module. -/
theorem quotientStackSource_square_restrictionMap {F H : QuotientStackModules G} (ψ : F ⟶ H) :
    quotientStackSourceComparison G F ≫ quotientStackArrowRestrictionMap ψ =
      (Space.modulePullback C S hS G.source).map (quotientStackObjectRestrictionMap G ψ) ≫
          quotientStackSourceComparison G H :=
  (Space.comparison_etaleRestrictedHom C S hS (quotientStack G).p
      (fibredCategory C S hS G.arrows.obj).val.p (fibredCategory C S hS G.objects.obj).val.p
      (fibredCategory C S hS G.arrows.obj).property (fibredCategory C S hS G.objects.obj).property
      (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (quotientStackSourceLeg G)
          (quotientStackTargetLeg G) (quotientStackProj G)
      (quotientStackSourceLeg G ⋙ quotientStackProj G) (isFibredOneMorphism_quotientStackProj G)
          (isFibredOneMorphism_quotientStackSourceProj G)
      (Iso.refl _) (quotientStackTwoArrowIso G) G.source G.target (quotientStackSourceChartIso G)
          (quotientStackTargetChartIso G)
      (fun _ => IsHomLift.id rfl) (isHomLift_quotientStackTwoArrowNat G) (fun _ => IsHomLift.id rfl)
      (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).map ψ)).1

/-- The square through the target commutes for the restriction of a morphism of modules. -/
theorem quotientStackTarget_square_restrictionMap {F H : QuotientStackModules G} (ψ : F ⟶ H) :
    quotientStackTargetComparison G F ≫ quotientStackArrowRestrictionMap ψ =
      (Space.modulePullback C S hS G.target).map (quotientStackObjectRestrictionMap G ψ) ≫
          quotientStackTargetComparison G H :=
  (Space.comparison_etaleRestrictedHom C S hS (quotientStack G).p
      (fibredCategory C S hS G.arrows.obj).val.p (fibredCategory C S hS G.objects.obj).val.p
      (fibredCategory C S hS G.arrows.obj).property (fibredCategory C S hS G.objects.obj).property
      (isFiberedInGroupoids_quotientStack G) (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (quotientStackSourceLeg G)
          (quotientStackTargetLeg G) (quotientStackProj G)
      (quotientStackSourceLeg G ⋙ quotientStackProj G) (isFibredOneMorphism_quotientStackProj G)
          (isFibredOneMorphism_quotientStackSourceProj G)
      (Iso.refl _) (quotientStackTwoArrowIso G) G.source G.target (quotientStackSourceChartIso G)
          (quotientStackTargetChartIso G)
      (fun _ => IsHomLift.id rfl) (isHomLift_quotientStackTwoArrowNat G) (fun _ => IsHomLift.id rfl)
      (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).map ψ)).2

/-- **Stacks 076S.**  Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` whose source
and target are flat and locally of finite presentation, let `𝒳 = [U/R]` be the quotient stack and
`x` the object of `𝒳` over `U` (the canonical projection of Stacks 044R).  Let `ℱ` be a
quasi-coherent `𝒪_𝒳`-module and `ℋ` any `𝒪_𝒳`-module.  Then the map
`Hom_{𝒪_𝒳}(ℱ, ℋ) ⟶ Hom_{𝒪_U}(x^*ℱ|_{U_étale}, x^*ℋ|_{U_étale})`, `ψ ↦ x^*ψ|_{U_étale}`, is
injective, and its image consists of exactly those `φ` which give rise to a commutative diagram
of modules on `R_étale`: there is a morphism `χ : (x ∘ s)^*ℱ|_{R_étale} ⟶ (x ∘ s)^*ℋ|_{R_étale}`
with `c_s(ℱ) ≫ χ = s_small^*φ ≫ c_s(ℋ)` and `c_t(ℱ) ≫ χ = t_small^*φ ≫ c_t(ℋ)`, where `c_s` and
`c_t` are the comparison maps of equation 076R of the triangles through the source and through
the target, the latter carried by the 2-morphism of Stacks 044S which identifies
`(x ∘ t)^*ℱ|_{R_étale}` with `(x ∘ s)^*ℱ|_{R_étale}`. -/
@[stacks 076S]
theorem quotientStackObjectRestrictionMap_injective_and_range
    (_hsflat : Space.IsFlat C S hS G.source.hom) (_htflat : Space.IsFlat C S hS G.target.hom)
    (_hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (_htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom)
    (F : FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G))
    (H : QuotientStackModules G) :
    Function.Injective (fun ψ : F.obj ⟶ H => quotientStackObjectRestrictionMap G ψ) ∧
      ∀ φ : quotientStackObjectRestriction G F.obj ⟶ quotientStackObjectRestriction G H,
        (∃ ψ : F.obj ⟶ H, quotientStackObjectRestrictionMap G ψ = φ) ↔
          ∃ χ, quotientStackSourceComparison G F.obj ≫ χ =
              (Space.modulePullback C S hS G.source).map φ ≫ quotientStackSourceComparison G H ∧
            quotientStackTargetComparison G F.obj ≫ χ =
              (Space.modulePullback C S hS G.target).map φ ≫ quotientStackTargetComparison G H := by
  refine ⟨fun ψ₁ ψ₂ h => quotientStackObjectRestrictionMap_injective F.property h,
    fun φ => ⟨?_, ?_⟩⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨quotientStackArrowRestrictionMap ψ, quotientStackSource_square_restrictionMap ψ,
      quotientStackTarget_square_restrictionMap ψ⟩
  · rintro ⟨χ, hs, ht⟩
    exact ⟨chartedGluedHom φ χ F.property hs ht,
      quotientStackObjectRestrictionMap_chartedGluedHom φ χ F.property hs ht⟩

end AlgebraicGeometry.Stack

end
