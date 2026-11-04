module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.BigSitePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Transition morphisms between glued étale quotients

Two instances of the construction of `AlgebraicGeometry.Space.GluedEtaleQuotient` — `V/R` and
`V'/R'` — together with compatible maps `U' ⟶ U`, `W' ⟶ W` and `V' ⟶ V` induce maps
`Q' ⟶ Q`, `R' ⟶ R` and `V'/R' ⟶ V/R`. When `W' = W ×_U U'` and `W' = W ×_V V'`, the square
of relations over the source maps is cartesian (Stacks 07SV) and hence so is the square of
quotient maps (Stacks 07S3): `V' = V ×_{V/R} V'/R'`.

When moreover `V' ⟶ V` is affine, so is `V'/R' ⟶ V/R`.

## Main definitions

* `AlgebraicGeometry.Space.GluedEtaleQuotient.kernelMap`: the induced map `Q' ⟶ Q` of kernel pairs.
* `AlgebraicGeometry.Space.GluedEtaleQuotient.relationMap`: the induced map `R' ⟶ R` of relations.
* `AlgebraicGeometry.Space.GluedEtaleQuotient.quotientHom`: the induced map `V'/R' ⟶ V/R` of
  quotients.

## Main results

* `AlgebraicGeometry.Space.GluedEtaleQuotient.qmap_quotientHom`: compatibility with the
  quotient maps.
* `AlgebraicGeometry.Space.GluedEtaleQuotient.isPullback_qmap_quotientHom`: the square of quotient
  maps is cartesian when the square of relations over the source maps is.
* `AlgebraicGeometry.Space.GluedEtaleQuotient.isPullback_relationMap`: the square of relations
  over the source maps is cartesian when `W' = W ×_U U'` and `W' = W ×_V V'`.
* `AlgebraicGeometry.Space.GluedEtaleQuotient.isAffineHom_quotientHom`: the map of quotients is
  affine when `V' ⟶ V` is.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SV](https://stacks.math.columbia.edu/tag/07SV)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.GluedEtaleQuotient

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {U U' : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  {W V W' V' : BigFppfOver B (⊤_ Scheme.{u}) hZ}
  (w : yoneda.obj W ⟶ U)
  (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w)
  (ι : W ⟶ V) [AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)]
  (w' : yoneda.obj W' ⟶ U')
  (hw' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w')
  (ι' : W' ⟶ V') [AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι')]
  (u : U' ⟶ U) (ω : W' ⟶ W) (v : V' ⟶ V)
  (hwu : w' ≫ u = yoneda.map ω ≫ w) (hιv : ι' ≫ v = ω ≫ ι)

include hwu in
/-- **The induced map of kernel pairs** `Q' = W' ×_{U'} W' ⟶ Q = W ×_U W`. -/
noncomputable def kernelMap : kernelObj w' hw' ⟶ kernelObj w hw :=
  hw.rep.lift' (kp₁ w' hw' ≫ ω) (kp₂ w' hw' ≫ ω) (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      Category.assoc, ← hwu, ← Category.assoc, ← Category.assoc, (isPullback_kernel w' hw').w])

/-- The induced map of kernel pairs commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem kernelMap_kp₁ : kernelMap w hw w' hw' u ω hwu ≫ kp₁ w hw = kp₁ w' hw' ≫ ω :=
  hw.rep.lift'_fst _ _ _

/-- The induced map of kernel pairs commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem kernelMap_kp₂ : kernelMap w hw w' hw' u ω hwu ≫ kp₂ w hw = kp₂ w' hw' ≫ ω :=
  hw.rep.lift'_snd _ _ _

/-- The induced map of kernel pairs commutes with the diagonals `W' ⟶ Q'` and `W ⟶ Q`. -/
@[reassoc (attr := simp)]
theorem diag_kernelMap : diag w' hw' ≫ kernelMap w hw w' hw' u ω hwu = ω ≫ diag w hw := by
  apply hw.rep.hom_ext' <;> simp

include hιv in
/-- **The induced map of relations** `R' = V' ⊔_{W'} Q' ⟶ R = V ⊔_W Q`. -/
noncomputable def relationMap : relationObj w' hw' ι' ⟶ relationObj w hw ι :=
  homOfScheme (pushout.desc
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map v ≫
      pushout.inl ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw)))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kernelMap w hw w' hw' u ω hwu) ≫
      pushout.inr ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (diag w hw)))
    (by
      rw [← Category.assoc, ← Category.assoc,
        ← (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_comp,
        ← (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_comp, hιv,
        diag_kernelMap, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        pushout.condition]))

/-- On the chart `V'`, the induced map of relations is `v : V' ⟶ V`. -/
@[reassoc (attr := simp)]
theorem inlV_relationMap :
    inlV w' hw' ι' ≫ relationMap w hw ι w' hw' ι' u ω v hwu hιv = v ≫ inlV w hw ι := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  simp only [relationMap, toScheme_map_homOfScheme, pushout.inl_desc]

/-- On the chart `Q'`, the induced map of relations is the induced map of kernel pairs. -/
@[reassoc (attr := simp)]
theorem inrQ_relationMap :
    inrQ w' hw' ι' ≫ relationMap w hw ι w' hw' ι' u ω v hwu hιv =
      kernelMap w hw w' hw' u ω hwu ≫ inrQ w hw ι := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  simp only [relationMap, toScheme_map_homOfScheme, pushout.inr_desc]

/-- Two morphisms out of the relation object agree as soon as they agree on the two charts. -/
theorem relation_hom_ext {Z : BigFppfOver B (⊤_ Scheme.{u}) hZ} {a b : relationObj w hw ι ⟶ Z}
    (hl : inlV w hw ι ≫ a = inlV w hw ι ≫ b) (hr : inrQ w hw ι ≫ a = inrQ w hw ι ≫ b) :
    a = b := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  apply pushout.hom_ext
  · have := congrArg (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map hl
    rwa [Functor.map_comp, Functor.map_comp, toScheme_map_homOfScheme] at this
  · have := congrArg (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map hr
    rwa [Functor.map_comp, Functor.map_comp, toScheme_map_homOfScheme] at this

/-- The induced map of relations commutes with the source maps `R' ⟶ V'` and `R ⟶ V`. -/
@[reassoc (attr := simp)]
theorem relationMap_src :
    relationMap w hw ι w' hw' ι' u ω v hwu hιv ≫ src w hw ι = src w' hw' ι' ≫ v := by
  apply relation_hom_ext w' hw' ι'
  · simp
  · simp [hιv]

/-- The induced map of relations commutes with the target maps `R' ⟶ V'` and `R ⟶ V`. -/
@[reassoc (attr := simp)]
theorem relationMap_tgt :
    relationMap w hw ι w' hw' ι' u ω v hwu hιv ≫ tgt w hw ι = tgt w' hw' ι' ≫ v := by
  apply relation_hom_ext w' hw' ι'
  · simp
  · simp [hιv]

/-! ### The induced map of quotients -/

/-- The relation maps commute with the source maps, in the category of schemes over the base. -/
theorem relationMap_source :
    (Over.post B.inclusion).map (relationMap w hw ι w' hw' ι' u ω v hwu hιv) ≫
        (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι)).source =
      (relation B (⊤_ Scheme.{u}) hZ (src w' hw' ι') (tgt w' hw' ι')).source ≫
        (Over.post B.inclusion).map v := by
  simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, relationMap_src]

/-- The relation maps commute with the target maps, in the category of schemes over the base. -/
theorem relationMap_target :
    (Over.post B.inclusion).map (relationMap w hw ι w' hw' ι' u ω v hwu hιv) ≫
        (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι)).target =
      (relation B (⊤_ Scheme.{u}) hZ (src w' hw' ι') (tgt w' hw' ι')).target ≫
        (Over.post B.inclusion).map v := by
  simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, relationMap_tgt]

/-- **The induced map of quotients** `V'/R' ⟶ V/R`, as a morphism of sheaves. -/
noncomputable abbrev quotientSheafHom :=
  Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
    (Over.post B.inclusion) (relation B (⊤_ Scheme.{u}) hZ (src w' hw' ι') (tgt w' hw' ι'))
    (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι))
    ((Over.post B.inclusion).map (relationMap w hw ι w' hw' ι' u ω v hwu hιv))
    ((Over.post B.inclusion).map v) (relationMap_source w hw ι w' hw' ι' u ω v hwu hιv)
    (relationMap_target w hw ι w' hw' ι' u ω v hwu hιv)

/-- **The induced map of quotients** `V'/R' ⟶ V/R`. -/
noncomputable abbrev quotientHom : quotient w' hw' ι' ⟶ quotient w hw ι :=
  (quotientSheafHom w hw ι w' hw' ι' u ω v hwu hιv).hom

/-- The quotient map evaluated at a point of the site is the class of that point. -/
theorem qmap_app {T' : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : T' ⟶ V) :
    (qmap w hw ι).app (op T') f =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
        (Over.post B.inclusion) (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι))).app
        (op T') ((Over.post B.inclusion).map f) := by
  show (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
      (Over.post B.inclusion) (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι))).obj.map
        f.op ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
          (Over.post B.inclusion) (relation B (⊤_ Scheme.{u}) hZ (src w hw ι)
            (tgt w hw ι))).app (op V) (𝟙 ((Over.post B.inclusion).obj V))) = _
  exact (NatTrans.naturality_apply (Stacks.Groupoids.toQuotientSheaf
    (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Over.post B.inclusion)
    (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι))) (op f)
    (𝟙 ((Over.post B.inclusion).obj V))).symm

/-- **The induced map of quotients commutes with the quotient maps.** -/
@[reassoc]
theorem qmap_quotientHom :
    qmap w' hw' ι' ≫ quotientHom w hw ι w' hw' ι' u ω v hwu hιv =
      yoneda.map v ≫ qmap w hw ι := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  show (quotientHom w hw ι w' hw' ι' u ω v hwu hιv).app _ ((qmap w' hw' ι').app _ (𝟙 V')) =
    (qmap w hw ι).app _ v
  rw [qmap_app, qmap_app]
  have h := congrArg (fun m => m.app (op V') ((Over.post B.inclusion).map (𝟙 V')))
    (Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap
      (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Over.post B.inclusion)
      (relation B (⊤_ Scheme.{u}) hZ (src w' hw' ι') (tgt w' hw' ι'))
      (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι))
      ((Over.post B.inclusion).map (relationMap w hw ι w' hw' ι' u ω v hwu hιv))
      ((Over.post B.inclusion).map v) (relationMap_source w hw ι w' hw' ι' u ω v hwu hιv)
      (relationMap_target w hw ι w' hw' ι' u ω v hwu hιv))
  simp only [NatTrans.comp_app, types_comp_apply, CategoryTheory.Functor.map_id] at h
  rw [CategoryTheory.Functor.map_id]
  refine h.trans ?_
  congr 2

/-! ### The cartesian square of quotient maps -/

/-- The functor of points of an object of the site, read through the inclusion into schemes over
the base, is its Yoneda presheaf. -/
noncomputable def pointsIso (X : BigFppfOver B (⊤_ Scheme.{u}) hZ) :
    yoneda.obj X ≅
      Stacks.Groupoids.points (Over.post B.inclusion) ((Over.post B.inclusion).obj X) :=
  NatIso.ofComponents (fun T => Equiv.toIso
      ((Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion)).homEquiv
        (X := T.unop) (Y := X)))
    (fun f => by
      ext x
      exact ((Over.post B.inclusion).map_comp f.unop x).symm)

/-- The quotient map `V ⟶ V/R` is the canonical map to the quotient sheaf, precomposed with the
identification of the Yoneda presheaf of `V` with its functor of points. -/
theorem qmap_eq : qmap w hw ι = (pointsIso V).hom ≫
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
      (Over.post B.inclusion) (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι)) := by
  ext T f
  exact qmap_app w hw ι f

include hιv in
/-- **The square of quotient maps is cartesian** as soon as the square of relations over the
source maps is (Stacks 07S3). -/
theorem isPullback_qmap_quotientHom
    (hcart : IsPullback
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (relationMap w hw ι w' hw' ι' u ω v hwu hιv))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (src w' hw' ι'))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (src w hw ι))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map v)) :
    IsPullback (qmap w' hw' ι') (yoneda.map v) (quotientHom w hw ι w' hw' ι' u ω v hwu hιv)
      (qmap w hw ι) := by
  let J := BigFppfOver.topology B (⊤_ Scheme.{u}) hZ
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := inferInstance
  have hcart' : IsPullback ((Over.post B.inclusion).map
        (relationMap w hw ι w' hw' ι' u ω v hwu hιv))
      (relation B (⊤_ Scheme.{u}) hZ (src w' hw' ι') (tgt w' hw' ι')).source
      (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι)).source
      ((Over.post B.inclusion).map v) := by
    simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
    exact IsPullback.of_map_of_faithful (Over.forget _) hcart
  have h := Stacks.Groupoids.isPullback_toQuotientSheaf_of_subcanonical J (Over.post B.inclusion)
    (relation B (⊤_ Scheme.{u}) hZ (src w' hw' ι') (tgt w' hw' ι'))
    (relation B (⊤_ Scheme.{u}) hZ (src w hw ι) (tgt w hw ι))
    ((Over.post B.inclusion).map (relationMap w hw ι w' hw' ι' u ω v hwu hιv))
    ((Over.post B.inclusion).map v) (relationMap_source w hw ι w' hw' ι' u ω v hwu hιv)
    (relationMap_target w hw ι w' hw' ι' u ω v hwu hιv) hcart'
  refine h.of_iso (pointsIso V').symm (Iso.refl _) (pointsIso V).symm (Iso.refl _) ?_
    (by
      ext T f
      show (Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion)).preimage
          (f ≫ (Over.post B.inclusion).map v) =
        (Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion)).preimage f ≫ v
      apply (Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion)).map_injective
      rw [Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_comp,
        Functor.FullyFaithful.map_preimage])
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]) ?_ <;>
  rw [Iso.refl_hom, Category.comp_id, qmap_eq, Iso.symm_hom, Iso.inv_hom_id_assoc]

/-! ### The cartesian squares, from `W' = W ×_U U'` and `W' = W ×_V V'` -/

/-- **The square of kernel pairs over the first projections is cartesian** as soon as
`W' = W ×_U U'`, that is, `(W ×_U W) ×_W W' = W' ×_{U'} W'`. -/
theorem isPullback_kernelMap (hWU : IsPullback (yoneda.map ω) w' w u) :
    IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kernelMap w hw w' hw' u ω hwu))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w' hw'))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (kp₁ w hw))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ω) := by
  have H' : IsPullback (yoneda.map (kernelMap w hw w' hw' u ω hwu) ≫ yoneda.map (kp₂ w hw))
      (yoneda.map (kp₁ w' hw')) w (yoneda.map ω ≫ w) := by
    rw [← CategoryTheory.Functor.map_comp, kernelMap_kp₂, CategoryTheory.Functor.map_comp, ← hwu]
    exact (isPullback_kernel w' hw').flip.paste_horiz hWU
  have h₀ : yoneda.map (kernelMap w hw w' hw' u ω hwu) ≫ yoneda.map (kp₁ w hw) =
      yoneda.map (kp₁ w' hw') ≫ yoneda.map ω := by
    rw [← CategoryTheory.Functor.map_comp, kernelMap_kp₁, CategoryTheory.Functor.map_comp]
  have hY : IsPullback (yoneda.map (kernelMap w hw w' hw' u ω hwu)) (yoneda.map (kp₁ w' hw'))
      (yoneda.map (kp₁ w hw)) (yoneda.map ω) :=
    H'.of_right h₀ (isPullback_kernel w hw).flip
  exact (IsPullback.of_map yoneda (kernelMap_kp₁ _ _ _ _ _ _ _) hY).map _

include hιv in
/-- **The square of relations over the source maps is cartesian** (Stacks 07SV), as soon as
`W' = W ×_U U'` and `W' = W ×_V V'`. -/
theorem isPullback_relationMap (hWU : IsPullback (yoneda.map ω) w' w u)
    (hWV : IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ω)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι')
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map v)) :
    IsPullback
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (relationMap w hw ι w' hw' ι' u ω v hwu hιv))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (src w' hw' ι'))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (src w hw ι))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map v) := by
  rw [toScheme_map_homOfScheme, toScheme_map_homOfScheme]
  refine isPullback_gluedRelationSource_of_isPullback hWV
    (isPullback_kernelMap w hw w' hw' u ω hwu hWU)
    (by rw [← (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_comp, diag_kp₁,
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_id])
    (by rw [← (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_comp,
      ← (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_comp, diag_kernelMap])
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (GluedRelation.inl_fst _ _ _ _) (GluedRelation.inr_fst _ _ _ _)
    (GluedRelation.inl_fst _ _ _ _) (GluedRelation.inr_fst _ _ _ _) ?_ ?_
  · simp only [relationMap, toScheme_map_homOfScheme, pushout.inl_desc]
  · simp only [relationMap, toScheme_map_homOfScheme, pushout.inr_desc]

/-! ### Affineness of the transition morphisms -/

/-- The quotient map `V ⟶ V/R` is étale. -/
theorem isEtale_qmap : IsEtale B (⊤_ Scheme.{u}) hZ (qmap w hw ι) :=
  (isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ _).mpr (qmap_etale w hw ι)

/-- The quotient map `V ⟶ V/R` is surjective. -/
theorem isSurjective_qmap : IsSurjective B (⊤_ Scheme.{u}) hZ (qmap w hw ι) :=
  isSurjective_of_presheafSurjective B (⊤_ Scheme.{u}) hZ _ (qmap_surjective w hw ι)

include hιv in
/-- **The transition morphism of quotients is affine** when the transition morphism `V' ⟶ V` of
charts is (Stacks 03WG: the base change along the surjective étale chart `V ⟶ V/R` is
`V' ⟶ V`). -/
theorem isAffineHom_quotientHom (hWU : IsPullback (yoneda.map ω) w' w u)
    (hWV : IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ω)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι')
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map v))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map v)] :
    IsAffineHom B (⊤_ Scheme.{u}) hZ (quotientHom w hw ι w' hw' ι' u ω v hwu hιv) := by
  have hsq := isPullback_qmap_quotientHom w hw ι w' hw' ι' u ω v hwu hιv
    (isPullback_relationMap w hw ι w' hw' ι' u ω v hwu hιv hWU hWV)
  have hv : IsAffineHom B (⊤_ Scheme.{u}) hZ (yoneda.map v) := by
    have := inverseImage_isStableUnderBaseChange B (⊤_ Scheme.{u}) hZ
      (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance
    apply isAffineHom_of_presheaf
    exact (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))).mpr
      (show _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map v)
        from inferInstance)
  have hsnd : pullback.snd (quotientHom w hw ι w' hw' ι' u ω v hwu hιv) (qmap w hw ι) =
      hsq.isoPullback.inv ≫ yoneda.map v := by
    rw [IsPullback.isoPullback_inv_snd]
  have key := (isAffineHom_tfae_of_isAlgebraicSpace B (⊤_ Scheme.{u}) hZ
    (quotientHom w hw ι w' hw' ι' u ω v hwu hιv) (isAlgebraicSpace_quotient w' hw' ι')
    (isAlgebraicSpace_quotient w hw ι)).out 4 2
  refine key.mp ⟨V, qmap w hw ι, isSurjective_qmap w hw ι, isEtale_qmap w hw ι, ?_⟩
  rw [hsnd]
  exact isAffineHom_comp B (⊤_ Scheme.{u}) hZ _ _ (isAffineHom_of_isIso _) hv

end AlgebraicGeometry.Space.GluedEtaleQuotient

end
