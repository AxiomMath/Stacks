module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleQuotientTransition

/-!
# The inverse system of glued étale quotients

An inverse system of the data of `AlgebraicGeometry.Space.GluedEtaleQuotient` — algebraic spaces
`Uⱼ`, étale charts `Wⱼ ⟶ Uⱼ` and open immersions `Wⱼ ⊆ Vⱼ`, with cartesian transition squares —
induces an inverse system of algebraic spaces `Xⱼ = Vⱼ/Rⱼ` with affine transition morphisms and
cartesian squares `V_{j'} = Vⱼ ×_{Xⱼ} X_{j'}`.

## Main definitions

* `AlgebraicGeometry.Space.GluedEtaleQuotient.System`: the data.
* `AlgebraicGeometry.Space.GluedEtaleQuotient.System.quotients`: the inverse system of quotients.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.GluedEtaleQuotient

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An inverse system of glued étale data** over a category `J`. -/
structure System (J : Type u) [Category.{u} J] where
  /-- The bases `Uⱼ`. -/
  base : J ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u
  /-- The charts `Wⱼ`. -/
  chart : J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ
  /-- The ambient objects `Vⱼ`. -/
  ambient : J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ
  /-- The étale maps `Wⱼ ⟶ Uⱼ`. -/
  toBase : chart ⋙ yoneda ⟶ base
  /-- The open immersions `Wⱼ ⟶ Vⱼ`. -/
  incl : chart ⟶ ambient
  /-- The maps `Wⱼ ⟶ Uⱼ` are étale. -/
  etale (j : J) : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf (toBase.app j)
  /-- The maps `Wⱼ ⟶ Vⱼ` are open immersions. -/
  isOpenImmersion (j : J) : AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (incl.app j))
  /-- `W_{j'} = Wⱼ ×_{Uⱼ} U_{j'}`. -/
  isPullback_base {a b : J} (g : a ⟶ b) :
    IsPullback (yoneda.map (chart.map g)) (toBase.app a) (toBase.app b) (base.map g)
  /-- `W_{j'} = Wⱼ ×_{Vⱼ} V_{j'}`, as schemes. -/
  isPullback_ambient {a b : J} (g : a ⟶ b) :
    IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (chart.map g))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (incl.app a))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (incl.app b))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (ambient.map g))
  /-- The transition morphisms of the ambient objects are affine. -/
  isAffineHom_ambient {a b : J} (g : a ⟶ b) : _root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (ambient.map g))

namespace System

variable {B hZ} {J : Type u} [Category.{u} J] (D : System B hZ J)

attribute [instance] System.isOpenImmersion

/-- Naturality of the étale maps `Wⱼ ⟶ Uⱼ` along a morphism `a ⟶ b` of `J`. -/
theorem toBase_naturality {a b : J} (g : a ⟶ b) :
    D.toBase.app a ≫ D.base.map g = yoneda.map (D.chart.map g) ≫ D.toBase.app b :=
  (D.toBase.naturality g).symm

/-- Naturality of the open immersions `Wⱼ ⟶ Vⱼ` along a morphism `a ⟶ b` of `J`. -/
theorem incl_naturality {a b : J} (g : a ⟶ b) :
    D.incl.app a ≫ D.ambient.map g = D.chart.map g ≫ D.incl.app b :=
  (D.incl.naturality g).symm

/-- The quotient at a stage. -/
abbrev stage (j : J) : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u :=
  quotient (D.toBase.app j) (D.etale j) (D.incl.app j)

/-- The quotient map at a stage. -/
abbrev stageMap (j : J) : yoneda.obj (D.ambient.obj j) ⟶ D.stage j :=
  qmap (D.toBase.app j) (D.etale j) (D.incl.app j)

/-- The transition morphism of quotients. -/
abbrev transition {a b : J} (g : a ⟶ b) : D.stage a ⟶ D.stage b :=
  quotientHom (D.toBase.app b) (D.etale b) (D.incl.app b) (D.toBase.app a) (D.etale a)
    (D.incl.app a) (D.base.map g) (D.chart.map g) (D.ambient.map g)
    (D.toBase_naturality g) (D.incl_naturality g)

/-- The transition morphism of quotients is compatible with the quotient maps `Vⱼ ⟶ Xⱼ`. -/
@[reassoc]
theorem stageMap_transition {a b : J} (g : a ⟶ b) :
    D.stageMap a ≫ D.transition g = yoneda.map (D.ambient.map g) ≫ D.stageMap b :=
  qmap_quotientHom _ _ _ _ _ _ _ _ _ _ _

/-- Two morphisms out of a stage into a sheaf agree once they agree after the quotient map. -/
theorem stage_hom_ext (j : J) {Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hZs : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) Z)
    {a b : D.stage j ⟶ Z} (h : D.stageMap j ≫ a = D.stageMap j ≫ b) : a = b :=
  hom_ext_of_surjectiveEtale _ _ _ (isPullback_qmap _ _ _) (isAlgebraicSpace_quotient _ _ _)
    (qmap_surjective _ _ _) (qmap_etale _ _ _) hZs h

/-- **The inverse system of quotients** `Xⱼ = Vⱼ/Rⱼ`. -/
def quotients : J ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u where
  obj := D.stage
  map := D.transition
  map_id j := by
    refine D.stage_hom_ext j (isAlgebraicSpace_quotient _ _ _).isSheaf ?_
    rw [stageMap_transition, Category.comp_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp {a b c} g h := by
    refine D.stage_hom_ext a (isAlgebraicSpace_quotient _ _ _).isSheaf ?_
    rw [stageMap_transition, stageMap_transition_assoc, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc, stageMap_transition]

/-- Each quotient `Xⱼ = Vⱼ/Rⱼ` is an algebraic space. -/
theorem isAlgebraicSpace_quotients (j : J) :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.quotients.obj j) :=
  isAlgebraicSpace_quotient _ _ _

/-- **The stage charts form cartesian squares** `V_a = V_b ×_{X_b} X_a`. -/
theorem isPullback_stageMap {a b : J} (g : a ⟶ b) :
    IsPullback (D.stageMap a) (yoneda.map (D.ambient.map g)) (D.quotients.map g)
      (D.stageMap b) :=
  isPullback_qmap_quotientHom _ _ _ _ _ _ _ _ _ _ _
    (isPullback_relationMap _ _ _ _ _ _ _ _ _ _ _ (D.isPullback_base g)
      (D.isPullback_ambient g))

/-- The quotient map at a stage, typed with the system of quotients as target. -/
abbrev chartMap (j : J) : yoneda.obj (D.ambient.obj j) ⟶ D.quotients.obj j := D.stageMap j

/-- The transition morphisms of the system of quotients are compatible with the quotient maps
`Vⱼ ⟶ Xⱼ`. -/
@[reassoc]
theorem chartMap_transition {a b : J} (g : a ⟶ b) :
    D.chartMap a ≫ D.quotients.map g = yoneda.map (D.ambient.map g) ≫ D.chartMap b :=
  D.stageMap_transition g

/-- The square `V_a = V_b ×_{X_b} X_a` formed by the quotient maps and the transition morphisms is
cartesian. -/
theorem isPullback_chartMap {a b : J} (g : a ⟶ b) :
    IsPullback (D.chartMap a) (yoneda.map (D.ambient.map g)) (D.quotients.map g)
      (D.chartMap b) :=
  D.isPullback_stageMap g

/-- **The transition morphisms of the system of quotients are affine.** -/
theorem isAffineHom_quotients {a b : J} (g : a ⟶ b) :
    IsAffineHom B (⊤_ Scheme.{u}) hZ (D.quotients.map g) :=
  have := D.isAffineHom_ambient g
  isAffineHom_quotientHom _ _ _ _ _ _ _ _ _ _ _ (D.isPullback_base g) (D.isPullback_ambient g)

/-! ### The inverse system of relations -/

/-- The relation map of a transition. -/
abbrev relTransition {a b : J} (g : a ⟶ b) :
    relationObj (D.toBase.app a) (D.etale a) (D.incl.app a) ⟶
      relationObj (D.toBase.app b) (D.etale b) (D.incl.app b) :=
  relationMap (D.toBase.app b) (D.etale b) (D.incl.app b) (D.toBase.app a) (D.etale a)
    (D.incl.app a) (D.base.map g) (D.chart.map g) (D.ambient.map g)
    (D.toBase_naturality g) (D.incl_naturality g)

/-- **The inverse system of relations** `Rⱼ`. -/
def relations : J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ where
  obj j := relationObj (D.toBase.app j) (D.etale j) (D.incl.app j)
  map := D.relTransition
  map_id j := by
    apply relation_hom_ext
    · rw [inlV_relationMap, Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
    · rw [inrQ_relationMap, Category.comp_id]
      conv_rhs => rw [← Category.id_comp (inrQ _ _ _)]
      congr 1
      apply (D.etale j).rep.hom_ext'
      · simp
      · simp
  map_comp {a b c} g h := by
    apply relation_hom_ext
    · rw [inlV_relationMap, inlV_relationMap_assoc, inlV_relationMap,
        CategoryTheory.Functor.map_comp, Category.assoc]
    · rw [inrQ_relationMap, inrQ_relationMap_assoc, inrQ_relationMap, ← Category.assoc]
      congr 1
      apply (D.etale c).rep.hom_ext'
      · simp [CategoryTheory.Functor.map_comp]
      · simp [CategoryTheory.Functor.map_comp]

/-- The source maps of the relations, as a natural transformation. -/
def srcNat : D.relations ⟶ D.ambient where
  app j := src (D.toBase.app j) (D.etale j) (D.incl.app j)
  naturality _ _ g := relationMap_src _ _ _ _ _ _ _ _ _ (D.toBase_naturality g)
    (D.incl_naturality g)

/-- The target maps of the relations, as a natural transformation. -/
def tgtNat : D.relations ⟶ D.ambient where
  app j := tgt (D.toBase.app j) (D.etale j) (D.incl.app j)
  naturality _ _ g := relationMap_tgt _ _ _ _ _ _ _ _ _ (D.toBase_naturality g)
    (D.incl_naturality g)

/-- The square `R_a = R_b ×_{V_b} V_a` formed by the transition morphisms and the source maps of
the relations is cartesian, as schemes. -/
theorem isPullback_relations {a b : J} (g : a ⟶ b) :
    IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.relations.map g))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.srcNat.app a))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.srcNat.app b))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.ambient.map g)) :=
  isPullback_relationMap _ _ _ _ _ _ _ _ _ (D.toBase_naturality g) (D.incl_naturality g)
    (D.isPullback_base g) (D.isPullback_ambient g)

/-- The quotient maps, as a natural transformation. -/
def stageMapNat : D.ambient ⋙ yoneda ⟶ D.quotients where
  app := D.stageMap
  naturality _ _ g := (D.stageMap_transition g).symm

end System

end AlgebraicGeometry.Space.GluedEtaleQuotient

end
