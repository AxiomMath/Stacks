module

public import Mathlib.FieldTheory.FinTrdeg
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg
public import StacksFrontier.RingTheory.TranscendenceDegree.ResidueField
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Zero-dimensional algebraic spaces over a field

Let `X` be a nonempty algebraic space locally of finite type over a field `k`. Four conditions
on `X` are considered: that its point space `|X|` is discrete, that `|X|` has Krull dimension
zero, that `X` has dimension zero as an algebraic space, and that `X → Spec k` is locally
quasi-finite. The first, third and fourth are equivalent, the first implies the second, and the
second implies the first as soon as `|X|` is Kolmogorov.

## Main definitions

* `AlgebraicGeometry.Space.FiniteTypeOverField` is the standing situation: a nonempty algebraic
  space locally of finite type over a field, together with its structure morphism.
* `AlgebraicGeometry.Space.FiniteTypeOverField.FinitePoints`,
  `DiscretePoints`, `ZeroTopologicalDimension`, `ZeroDimension` and
  `LocallyQuasiFiniteOverField` are
  conditions (1) to (5) of Stacks 0ACA.

## Main results

* `AlgebraicGeometry.Space.FiniteTypeOverField.discretePoints_iff_zeroDimension` compares
  conditions (2) and (4).
* `AlgebraicGeometry.Space.FiniteTypeOverField.zeroDimension_iff_locallyQuasiFinite` compares
  conditions (4) and (5).
* `AlgebraicGeometry.Space.FiniteTypeOverField.zeroTopologicalDimension_of_discretePoints`
  derives condition (3) from condition (2).
* `AlgebraicGeometry.Space.FiniteTypeOverField.discretePoints_of_zeroTopologicalDimension`
  derives condition (2) from condition (3) for a Kolmogorov point space.

## Implementation notes

An algebraic space over `Spec k` is a presheaf on the big fppf site over `Spec k` together with
its structure morphism to the presheaf represented by the base. The topology on its points is
the one of Stacks 03BX, `AlgebraicGeometry.Space.pointTopology`, made a local instance here.
Both dimensions take values in `WithBot ℕ∞`; nonemptiness of the point space is what rules out
the value `⊥` in the zero-dimensional conditions.

The implication from condition (3) carries the hypothesis that `|X|` is `T0`. It cannot be
dropped: the standard non-decent algebraic space `𝔸¹_ℚ/ℤ` is locally of finite type over `ℚ`,
its point space is the quotient of `|𝔸¹_ℚ|` by the translation action of `ℤ`, and the only
invariant open subsets of `𝔸¹_ℚ` are `∅` and `𝔸¹_ℚ` — so the point space carries the
indiscrete topology on more than one point. It therefore has exactly one irreducible closed
subset and so Krull dimension zero, while being neither discrete nor zero-dimensional as an
algebraic space. The deduction `(3) ⟹ (4)` in the source uses that two points with different
transcendence degrees are distinct, which bounds the dimension of `|X|` from below only when
distinct points have distinct closures.

## References

* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The standing situation -/

/-- A nonempty algebraic space locally of finite type over a field, together with its structure
morphism to the spectrum of that field. -/
structure FiniteTypeOverField where
  /-- The base field. -/
  k : Type u
  /-- Its field structure. -/
  [field : Field k]
  /-- The chosen big fppf site. -/
  B : BigFppfSite.{u}
  /-- The spectrum of the base field belongs to the site. -/
  base_mem : B.Contains (Spec (.of k))
  /-- The algebraic space together with its structure morphism to the base. -/
  X : Over (yoneda.obj (Over.mk (𝟙 (B.obj base_mem))))
  /-- The presheaf is an algebraic space. -/
  isAlgebraicSpace : IsAlgebraicSpace B (Spec (.of k)) base_mem X.left
  /-- The point space is nonempty. -/
  nonempty : Nonempty (points B (Spec (.of k)) base_mem X.left)
  /-- The structure morphism is locally of finite type. -/
  locallyOfFiniteType : IsLocallyOfFiniteType B (Spec (.of k)) base_mem X.hom

attribute [instance] FiniteTypeOverField.field

namespace FiniteTypeOverField

/-- Condition (1) of Stacks 0ACA: the point space is finite. -/
abbrev FinitePoints (D : FiniteTypeOverField.{u}) : Prop :=
  Finite (points D.B (Spec (.of D.k)) D.base_mem D.X.left)

/-- Condition (2) of Stacks 0ACA: the point space is discrete. -/
abbrev DiscretePoints (D : FiniteTypeOverField.{u}) : Prop :=
  DiscreteTopology (points D.B (Spec (.of D.k)) D.base_mem D.X.left)

/-- Condition (3) of Stacks 0ACA: the point space has Krull dimension zero. -/
noncomputable abbrev ZeroTopologicalDimension (D : FiniteTypeOverField.{u}) : Prop :=
  topologicalKrullDim (points D.B (Spec (.of D.k)) D.base_mem D.X.left) = (0 : WithBot ℕ∞)

/-- Condition (4) of Stacks 0ACA: the algebraic space has dimension zero. -/
noncomputable abbrev ZeroDimension (D : FiniteTypeOverField.{u}) : Prop :=
  dimension D.B (Spec (.of D.k)) D.base_mem D.X.left D.isAlgebraicSpace = (0 : WithBot ℕ∞)

/-- Condition (5) of Stacks 0ACA: the structure morphism is locally quasi-finite. -/
abbrev LocallyQuasiFiniteOverField (D : FiniteTypeOverField.{u}) : Prop :=
  IsLocallyQuasiFinite D.B (Spec (.of D.k)) D.base_mem D.X.hom

/-! ### Étale charts over the base field -/

/-- The morphism of the site under an étale chart of the algebraic space, read as a chart of
the structure morphism over the base. -/
noncomputable def baseChartMap (D : FiniteTypeOverField.{u})
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left) :
    U ⟶ Over.mk (𝟙 (D.B.obj D.base_mem)) :=
  yonedaEquiv (a ≫ D.X.hom)

/-- The chart `baseChartMap D U a` composed with the identity of the base is the composite of
`a` with the structure morphism. -/
lemma baseChartMap_commutes (D : FiniteTypeOverField.{u})
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left) :
    yoneda.map (baseChartMap D U a) ≫ 𝟙 _ = a ≫ D.X.hom := by
  apply yonedaEquiv.injective
  simp only [Category.comp_id, yonedaEquiv_yoneda_map, baseChartMap]

/-- The identity of the presheaf represented by the base is étale. -/
lemma etale_id_base (D : FiniteTypeOverField.{u}) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf
      (𝟙 (yoneda.obj (Over.mk (𝟙 (D.B.obj D.base_mem))))) := by
  let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have : HasPullbacks D.B.Schemes := inferInstance
  have : PreservesLimitsOfShape WalkingCospan T := by apply comp_preservesLimitsOfShape
  have : Q.IsStableUnderBaseChange := ⟨fun hs hg ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale.{u}) (hs.map T) hg⟩
  simpa using (MorphismProperty.relative_map_iff (F := yoneda) (P := Q)).2
    (show Etale (T.map (𝟙 (Over.mk (𝟙 (D.B.obj D.base_mem))))) by infer_instance)

/-- An étale chart of an algebraic space locally of finite type over a field is itself locally
of finite type over that field. -/
private lemma baseChartMap_locallyOfFiniteType (D : FiniteTypeOverField.{u})
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a) :
    LocallyOfFiniteType ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).map
      (baseChartMap D U a)) :=
  D.locallyOfFiniteType U (Over.mk (𝟙 (D.B.obj D.base_mem))) a (𝟙 _)
    (baseChartMap D U a) ha (etale_id_base D) (baseChartMap_commutes D U a)

/-- The pointed pair of étale charts determined by an étale chart of the algebraic space
together with a field-valued point above the given point. -/
private noncomputable def baseEtaleChartForPoint (D : FiniteTypeOverField.{u})
    (x : points D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a)
    (p : FieldValuedPoint D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U))
    (hp : pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
      (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) = x) :
    EtaleChartAtPoint D.B (Spec (.of D.k)) D.base_mem D.X.hom x where
  U := U
  V := Over.mk (𝟙 (D.B.obj D.base_mem))
  a := a
  b := 𝟙 _
  h := baseChartMap D U a
  a_etale := ha
  b_etale := etale_id_base D
  comm := baseChartMap_commutes D U a
  representative := p
  point := IsLocalRing.closedPoint p.carrier
  maps_to := hp

/-- The scheme point selected by `baseEtaleChartForPoint` is the one selected by the
field-valued representative. -/
private lemma baseEtaleChartForPoint_sourcePoint (D : FiniteTypeOverField.{u})
    (x : points D.B (Spec (.of D.k)) D.base_mem D.X.left)
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a)
    (p : FieldValuedPoint D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U))
    (hp : pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
      (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) = x) :
    (baseEtaleChartForPoint D x U a ha p hp).sourcePoint D.B (Spec (.of D.k)) D.base_mem =
      schemePoint D.B (Spec (.of D.k)) D.base_mem U p := rfl

/-- The transcendence degree at a point of a morphism of algebraic spaces is unique. -/
private theorem hasTranscendenceDegreeAt_unique (D : FiniteTypeOverField.{u})
    (x : points D.B (Spec (.of D.k)) D.base_mem D.X.left) {r s : ℕ∞}
    (hr : HasTranscendenceDegreeAt D.B (Spec (.of D.k)) D.base_mem D.X.hom x r)
    (hs : HasTranscendenceDegreeAt D.B (Spec (.of D.k)) D.base_mem D.X.hom x s) : r = s := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint D.B (Spec (.of D.k)) D.base_mem D.isAlgebraicSpace
    (isAlgebraicSpace_yoneda D.B (Spec (.of D.k)) D.base_mem
      (Over.mk (𝟙 (D.B.obj D.base_mem)))) D.X.hom x
  exact MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique (hr c) (hs c)

/-! ### Transcendence degree over the base field -/

/-- For a scheme over a field, the transcendence degree of a residue field over the base field
is the transcendence degree over the residue field of the image point. -/
private theorem trdeg_residueField_eq_of_base_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    let K := (Spec (.of k)).residueField (f x)
    let L := X.residueField x
    letI : Algebra k K :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom).toAlgebra
    letI : Algebra K L := (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra k L :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.trdeg k L = Algebra.trdeg K L := by
  dsimp only
  let K := (Spec (.of k)).residueField (f x)
  let L := X.residueField x
  let α := ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom
  let : Algebra k K := α.toAlgebra
  let : Algebra K L := (f.residueFieldMap x).hom.toAlgebra
  let β := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom
  let : Algebra k L := β.toAlgebra
  let I := (f x).asIdeal
  let : I.IsPrime := (f x).2
  let e₁ : k ≃ₐ[k] I.ResidueField := I.algEquivResidueFieldOfField
  let e₂ : I.ResidueField ≃+* K :=
    (Scheme.Spec.residueFieldIso (.of k) (f x)).commRingCatIsoToRingEquiv.symm
  let e : k ≃+* K := e₁.toRingEquiv.trans e₂
  have he : e.toRingHom = α := RingHom.ext fun z ↦ by
    dsimp [e, α, e₂]
    rw [Ideal.algEquivResidueFieldOfField_apply]
    show (CommRingCat.Hom.hom
      (CommRingCat.ofHom (algebraMap k (f x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of k) (f x)).inv)) z = _
    have h := congrArg CommRingCat.Hom.hom
      (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) (f x))
    rw [h]
    rfl
  let eK : k ≃ₐ[k] K :=
    { toRingEquiv := e
      commutes' := by
        intro z
        show e.toRingHom z = α z
        exact congrArg (fun g : k →+* K => g z) he }
  have hmap (z : k) : Algebra.linearMap k K z = eK z := by
    show algebraMap k K z = eK z
    simp
  have : Module.Finite k K := .of_surjective (Algebra.linearMap k K)
    fun y ↦ ⟨eK.symm y, (hmap _).trans (eK.apply_symm_apply y)⟩
  have halg : Algebra.IsAlgebraic k K := .of_finite k K
  have htower : IsScalarTower k K L := .of_algebraMap_eq fun z ↦ by
    show β z = (f.residueFieldMap x).hom
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom z)
    exact (Scheme.Γevaluation_naturality_apply f x
      ((Scheme.ΓSpecIso (.of k)).inv.hom z)).symm
  rw [← trdeg_add_eq k K (A := L), trdeg_eq_zero_iff.mpr halg, zero_add]

/-- The germ of a morphism of schemes over a field has the residue-field transcendence degree
computed on the whole source. -/
private theorem hasResidueFieldTrdeg_of_schemeMap (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (x : X) :
    let V := (⊤ : X.Opens).toScheme
    let v : V := ⟨x, by simp⟩
    letI : Algebra k (V.residueField v) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (X.topIso.hom ≫ f).appTop ≫ V.Γevaluation v).hom.toAlgebra
    MorphismOfGerms.HasResidueFieldTranscendenceDegree
      (Cardinal.toENat (Algebra.trdeg k (V.residueField v)))
      (MorphismOfGerms.ofSchemeHom f x) := by
  dsimp only
  let V := (⊤ : X.Opens).toScheme
  let v : V := ⟨x, by simp⟩
  let : Algebra k (V.residueField v) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (X.topIso.hom ≫ f).appTop ≫ V.Γevaluation v).hom.toAlgebra
  let g : MorphismOfGerms.Representative ⟨X, x⟩ ⟨Spec (.of k), f x⟩ :=
    { source := ⊤
      mem_source := by simp
      hom := X.topIso.hom ≫ f
      map_point := rfl }
  exact ⟨g, rfl, congrArg Cardinal.toENat (trdeg_residueField_eq_of_base_field k g.hom v).symm⟩

/-! ### Specializations and the dimension of the charts -/

private lemma exists_ne_specialization_of_positive_topologicalKrullDim (Y : Type u)
    [TopologicalSpace Y] [QuasiSober Y] (hY : (0 : WithBot ℕ∞) < topologicalKrullDim Y) :
    ∃ x y : Y, x ⤳ y ∧ x ≠ y := by
  change (0 : WithBot ℕ∞) < Order.krullDim (TopologicalSpace.IrreducibleCloseds Y) at hY
  obtain ⟨A, B, hAB⟩ := Order.krullDim_pos_iff.mp hY
  have hx := B.isIrreducible'.isGenericPoint_genericPoint B.isClosed'
  have hy := A.isIrreducible'.isGenericPoint_genericPoint A.isClosed'
  refine ⟨_, _, hx.specializes (hAB.le hy.mem), fun h ↦ hAB.ne ?_⟩
  apply TopologicalSpace.IrreducibleCloseds.ext
  show A.carrier = B.carrier
  rw [← hy.def, ← hx.def, h]

/-- The transcendence degree at the image of a point of an étale chart is the transcendence
degree of the residue field of that point over the base field. -/
private theorem hasTranscendenceDegreeAt_chartPoint (D : FiniteTypeOverField.{u})
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a)
    (u : (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) :
    let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
    let f := T.map (baseChartMap D U a)
    let V := (⊤ : (T.obj U).Opens).toScheme
    let v : V := ⟨u, by simp⟩
    letI : Algebra D.k (V.residueField v) :=
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫
        ((T.obj U).topIso.hom ≫ f).appTop ≫ V.Γevaluation v).hom.toAlgebra
    let p := schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u
    let x := pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
      (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U))
    HasTranscendenceDegreeAt D.B (Spec (.of D.k)) D.base_mem D.X.hom x
      (Cardinal.toENat (Algebra.trdeg D.k (V.residueField v))) := by
  dsimp only
  let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
  let f := T.map (baseChartMap D U a)
  let V := (⊤ : (T.obj U).Opens).toScheme
  let v : V := ⟨u, by simp⟩
  let : Algebra D.k (V.residueField v) :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      ((T.obj U).topIso.hom ≫ f).appTop ≫ V.Γevaluation v).hom.toAlgebra
  let p := schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u
  let x := pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
    (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U))
  let r := Cardinal.toENat (Algebra.trdeg D.k (V.residueField v))
  let Q := @MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r
  have hlocal := hasResidueFieldTrdeg_of_schemeMap D.k (T.obj U) f u
  let c := baseEtaleChartForPoint D x U a ha p rfl
  have hc : c.sourcePoint D.B (Spec (.of D.k)) D.base_mem = u :=
    schemePointRepresentative_point D.B (Spec (.of D.k)) D.base_mem U u
  have hsome : HoldsOnSomeEtaleChartAtPoint D.B (Spec (.of D.k)) D.base_mem Q D.X.hom x := by
    refine ⟨c, ?_⟩
    show Q (MorphismOfGerms.ofSchemeHom (T.map c.h) (c.sourcePoint D.B (Spec (.of D.k))
      D.base_mem))
    rw [hc]
    exact hlocal
  exact (holdsOnEveryEtaleChartAtPoint_iff_some D.B (Spec (.of D.k)) D.base_mem Q
    (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r)
    D.isAlgebraicSpace (isAlgebraicSpace_yoneda D.B (Spec (.of D.k)) D.base_mem
      (Over.mk (𝟙 (D.B.obj D.base_mem)))) D.X.hom x).mpr hsome

/-- A nontrivial specialization inside an étale chart has distinct images in the point
space. -/
private lemma pointsMap_ne_of_nontrivial_specialization (D : FiniteTypeOverField.{u})
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a)
    (u u' : (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U)
    (huu' : u ⤳ u') (hne : u ≠ u') :
    pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
        ((schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u).class
          D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) ≠
      pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
        ((schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u').class
          D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) := by
  let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
  let f := T.map (baseChartMap D U a)
  let V := (⊤ : (T.obj U).Opens).toScheme
  let v : V := (T.obj U).topIso.inv u
  let v' : V := (T.obj U).topIso.inv u'
  let : Algebra D.k (V.residueField v) :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      ((T.obj U).topIso.hom ≫ f).appTop ≫ V.Γevaluation v).hom.toAlgebra
  let : Algebra D.k (V.residueField v') :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      ((T.obj U).topIso.hom ≫ f).appTop ≫ V.Γevaluation v').hom.toAlgebra
  let p := schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u
  let p' := schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u'
  let x := pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
    (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U))
  let x' := pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
    (p'.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U))
  let r := Cardinal.toENat (Algebra.trdeg D.k (V.residueField v))
  let s := Cardinal.toENat (Algebra.trdeg D.k (V.residueField v'))
  have hr : HasTranscendenceDegreeAt D.B (Spec (.of D.k)) D.base_mem D.X.hom x r :=
    hasTranscendenceDegreeAt_chartPoint D U a ha u
  have hs : HasTranscendenceDegreeAt D.B (Spec (.of D.k)) D.base_mem D.X.hom x' s :=
    hasTranscendenceDegreeAt_chartPoint D U a ha u'
  by_contra hxx'
  have hrs := hasTranscendenceDegreeAt_unique D x' ((show x = x' from hxx') ▸ hr) hs
  let g : V ⟶ Spec (.of D.k) := (T.obj U).topIso.hom ≫ f
  have : LocallyOfFiniteType f := baseChartMap_locallyOfFiniteType D U a ha
  have : LocallyOfFiniteType (T.obj U).topIso.hom := inferInstance
  have : LocallyOfFiniteType g := by
    dsimp only [g, V]
    exact locallyOfFiniteType_comp (T.obj U).topIso.hom f
  have hvv' : v ⤳ v' := huu'.map (Scheme.Hom.continuous (T.obj U).topIso.inv)
  have hvne : v ≠ v' := fun heq ↦ hne ((T.obj U).topIso.inv.injective heq)
  have htr := trdeg_residueField_lt_of_specialization D.k V g hvv' hvne
  have hfin' : Algebra.trdeg D.k (V.residueField v') < Cardinal.aleph0 :=
    finTrdeg_iff_trdeg.mp (residueField_finTrdeg D.k g v')
  have hfin : Algebra.trdeg D.k (V.residueField v) < Cardinal.aleph0 :=
    finTrdeg_iff_trdeg.mp (residueField_finTrdeg D.k g v)
  exact (Cardinal.toENat_strictMonoOn hfin'.le hfin.le htr).ne hrs.symm

/-! ### Elementary facts about the Krull dimension of a topological space -/

private lemma topologicalKrullDim_nonneg_of_nonempty {Y : Type*} [TopologicalSpace Y]
    [Nonempty Y] : (0 : WithBot ℕ∞) ≤ topologicalKrullDim Y := by
  have : Nonempty (TopologicalSpace.IrreducibleCloseds Y) :=
    ⟨⟨closure {Classical.arbitrary Y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  show (0 : WithBot ℕ∞) ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds Y)
  exact_mod_cast Order.krullDim_nonneg

@[ega "0 14.1.12" "dim(X) = 0", ega "0 14.1.9" "sufficiency"]
private lemma topologicalKrullDim_eq_zero_of_discrete_nonempty {Y : Type*}
    [TopologicalSpace Y] [DiscreteTopology Y] [Nonempty Y] : topologicalKrullDim Y = 0 :=
  le_antisymm (topologicalKrullDim_zero_of_discreteTopology Y)
    topologicalKrullDim_nonneg_of_nonempty

private lemma irreducibleCloseds_eq_of_le_of_topologicalKrullDim_eq_zero {Y : Type*}
    [TopologicalSpace Y] {A B : TopologicalSpace.IrreducibleCloseds Y} (hAB : A ≤ B)
    (hY : topologicalKrullDim Y = 0) : A = B := by
  by_contra hne
  have hone : (1 : WithBot ℕ∞) ≤ topologicalKrullDim Y := by
    show (1 : WithBot ℕ∞) ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds Y)
    exact_mod_cast Order.one_le_krullDim_iff.mpr ⟨A, B, lt_of_le_of_ne hAB hne⟩
  rw [hY] at hone
  norm_num at hone

private lemma topologicalKrullDimAt_eq_zero_of_discrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology Y] (y : Y) : topologicalKrullDimAt Y y = 0 := by
  have : Nonempty Y := ⟨y⟩
  exact le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim y).trans_eq
    topologicalKrullDim_eq_zero_of_discrete_nonempty) (topologicalKrullDimAt_nonneg y)

/-! ### Comparing the four conditions -/

private lemma dimensionAtPoint_nonneg (D : FiniteTypeOverField.{u})
    (x : points D.B (Spec (.of D.k)) D.base_mem D.X.left) :
    (0 : WithBot ℕ∞) ≤
      dimensionAtPoint D.B (Spec (.of D.k)) D.base_mem D.X.left D.isAlgebraicSpace x := by
  unfold dimensionAtPoint
  apply le_sInf
  rintro d ⟨U, a, ha, p, hp, rfl⟩
  exact topologicalKrullDimAt_nonneg _

/-- The point space has no nontrivial specializations. -/
private abbrev NoNontrivialSpecialization (D : FiniteTypeOverField.{u}) : Prop :=
  ∀ x y : points D.B (Spec (.of D.k)) D.base_mem D.X.left, x ⤳ y → x = y

private lemma noNontrivialSpecialization_of_discretePoints (D : FiniteTypeOverField.{u})
    (hD : D.DiscretePoints) : NoNontrivialSpecialization D := by
  have : DiscreteTopology (points D.B (Spec (.of D.k)) D.base_mem D.X.left) := hD
  exact fun x y hxy ↦ hxy.eq

private lemma noNontrivialSpecialization_of_zeroTopologicalDimension
    (D : FiniteTypeOverField.{u})
    (hT0 : T0Space (points D.B (Spec (.of D.k)) D.base_mem D.X.left))
    (hD : D.ZeroTopologicalDimension) : NoNontrivialSpecialization D := by
  have := hT0
  intro x y hxy
  let A : TopologicalSpace.IrreducibleCloseds
      (points D.B (Spec (.of D.k)) D.base_mem D.X.left) :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : TopologicalSpace.IrreducibleCloseds
      (points D.B (Spec (.of D.k)) D.base_mem D.X.left) :=
    ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : B ≤ A := by
    show closure ({y} : Set _) ⊆ closure ({x} : Set _)
    exact specializes_iff_closure_subset.mp hxy
  have hEq := irreducibleCloseds_eq_of_le_of_topologicalKrullDim_eq_zero hAB hD
  have hclosure : closure ({x} : Set _) = closure ({y} : Set _) :=
    (congrArg TopologicalSpace.IrreducibleCloseds.carrier hEq).symm
  exact T0Space.t0 (inseparable_iff_closure_eq.mpr hclosure)

/-- With no nontrivial specialization on the point space, every étale chart has Krull dimension
at most zero. -/
private lemma chart_topologicalKrullDim_le_zero_of_noSpecialization
    (D : FiniteTypeOverField.{u}) (hno : NoNontrivialSpecialization D)
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a) :
    topologicalKrullDim ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) ≤ 0 := by
  let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
  by_contra hdim
  obtain ⟨u, u', huu', hne⟩ :=
    exists_ne_specialization_of_positive_topologicalKrullDim (T.obj U) (lt_of_not_ge hdim)
  have himages := pointsMap_ne_of_nontrivial_specialization D U a ha u u' huu' hne
  let p := schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u
  let p' := schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u'
  let f := pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
  have hcont : Continuous f := continuous_pointsMap D.B (Spec (.of D.k)) D.base_mem a
  let h := schemePointsHomeomorph D.B (Spec (.of D.k)) D.base_mem U
  have hu : h (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) = u :=
    schemePointRepresentative_point D.B (Spec (.of D.k)) D.base_mem U u
  have hu' : h (p'.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) = u' :=
    schemePointRepresentative_point D.B (Spec (.of D.k)) D.base_mem U u'
  have hsource : (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) ⤳
      (p'.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) := by
    have hmap := huu'.map h.symm.continuous
    rwa [← hu, ← hu', Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at hmap
  exact himages (hno _ _ (hsource.map hcont))

private lemma chartLocalKrullDim_eq_zero_of_noSpecialization (D : FiniteTypeOverField.{u})
    (hno : NoNontrivialSpecialization D)
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a)
    (u : (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) :
    topologicalKrullDimAt
      ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) u = 0 :=
  le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim u).trans
    (chart_topologicalKrullDim_le_zero_of_noSpecialization D hno U a ha))
    (topologicalKrullDimAt_nonneg u)

private lemma zeroDimension_iff_forall_dimensionAtPoint_eq_zero
    (D : FiniteTypeOverField.{u}) :
    D.ZeroDimension ↔ ∀ x : points D.B (Spec (.of D.k)) D.base_mem D.X.left,
      dimensionAtPoint D.B (Spec (.of D.k)) D.base_mem D.X.left D.isAlgebraicSpace x = 0 := by
  constructor
  · intro hD x
    refine le_antisymm ?_ (dimensionAtPoint_nonneg D x)
    rw [← show (⨆ y : points D.B (Spec (.of D.k)) D.base_mem D.X.left,
      dimensionAtPoint D.B (Spec (.of D.k)) D.base_mem D.X.left D.isAlgebraicSpace y) = 0
        from hD]
    exact le_iSup_of_le x le_rfl
  · intro hx
    show (⨆ x : points D.B (Spec (.of D.k)) D.base_mem D.X.left,
      dimensionAtPoint D.B (Spec (.of D.k)) D.base_mem D.X.left D.isAlgebraicSpace x) = 0
    refine le_antisymm (iSup_le fun x ↦ (hx x).le) ?_
    obtain ⟨x⟩ := D.nonempty
    rw [← hx x]
    exact le_iSup_of_le x le_rfl

private theorem zeroDimension_of_noNontrivialSpecialization (D : FiniteTypeOverField.{u})
    (hno : NoNontrivialSpecialization D) : D.ZeroDimension := by
  refine (zeroDimension_iff_forall_dimensionAtPoint_eq_zero D).mpr fun x ↦ ?_
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point D.B (Spec (.of D.k)) D.base_mem
    D.X.left D.isAlgebraicSpace x
  exact (dimensionAtPoint_eq_of_etale_chart D.B (Spec (.of D.k)) D.base_mem D.X.left
    D.isAlgebraicSpace x U a ha p hp).trans
    (chartLocalKrullDim_eq_zero_of_noSpecialization D hno U a ha
      (schemePoint D.B (Spec (.of D.k)) D.base_mem U p))

private lemma chartLocalKrullDim_eq_zero_of_zeroDimension (D : FiniteTypeOverField.{u})
    (hD : D.ZeroDimension) (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem)
    (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a)
    (u : (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) :
    topologicalKrullDimAt
      ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) u = 0 := by
  let p := schemePointRepresentative D.B (Spec (.of D.k)) D.base_mem U u
  let x := pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
    (p.class D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U))
  have hx := (zeroDimension_iff_forall_dimensionAtPoint_eq_zero D).mp hD x
  have hchart := dimensionAtPoint_eq_of_etale_chart D.B (Spec (.of D.k)) D.base_mem D.X.left
    D.isAlgebraicSpace x U a ha p rfl
  rw [schemePointRepresentative_point] at hchart
  exact hchart.symm.trans hx

private lemma topologicalKrullDim_chart_le_zero_of_zeroDimension (D : FiniteTypeOverField.{u})
    (hD : D.ZeroDimension) (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem)
    (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a) :
    topologicalKrullDim ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) ≤ 0 := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun u ↦ ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  exact (chartLocalKrullDim_eq_zero_of_zeroDimension D hD U a ha u).le

/-- An étale chart of Krull dimension at most zero is discrete. -/
private lemma discrete_chart_of_topologicalKrullDim_le_zero (D : FiniteTypeOverField.{u})
    (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem) (a : yoneda.obj U ⟶ D.X.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a)
    (hdim : topologicalKrullDim
      ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) ≤ 0) :
    DiscreteTopology ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) := by
  let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
  have : LocallyOfFiniteType (T.map (baseChartMap D U a)) :=
    baseChartMap_locallyOfFiniteType D U a ha
  have : IsLocallyNoetherian (T.obj (Over.mk (𝟙 (D.B.obj D.base_mem)))) := by
    show IsLocallyNoetherian (Spec (.of D.k))
    infer_instance
  have : IsLocallyNoetherian (T.obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map (baseChartMap D U a))
  have : IsLocallyArtinian (T.obj U) := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  infer_instance

/-- If every étale chart of the algebraic space has Krull dimension at most zero, its point
space is discrete. -/
private lemma discretePoints_of_chart_topologicalKrullDim_le_zero (D : FiniteTypeOverField.{u})
    (hchart : ∀ (U : BigFppfOver D.B (Spec (.of D.k)) D.base_mem)
      (a : yoneda.obj U ⟶ D.X.left),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem)).presheaf a →
      topologicalKrullDim ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) ≤ 0) :
    D.DiscretePoints := by
  obtain ⟨U, a, hsurj, ha⟩ := D.isAlgebraicSpace.exists_atlas
  have : DiscreteTopology ((BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem).obj U) :=
    discrete_chart_of_topologicalKrullDim_le_zero D U a ha (hchart U a ha)
  have : DiscreteTopology (points D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U)) :=
    (schemePointsHomeomorph D.B (Spec (.of D.k)) D.base_mem U).discreteTopology_iff.mpr
      inferInstance
  let f := pointsMap D.B (Spec (.of D.k)) D.base_mem (yoneda.obj U) a
  have hfopen := isOpenMap_pointsMap_of_etale D.B (Spec (.of D.k)) D.base_mem
    D.isAlgebraicSpace U a ha
  have hfsurj := (surjective_iff_surjective_pointsMap D.B (Spec (.of D.k)) D.base_mem
    D.X.left D.isAlgebraicSpace U a).mp hsurj
  refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
  rw [← Set.image_preimage_eq {x} hfsurj]
  exact hfopen _ (isOpen_discrete _)

/-! ### The equivalences -/

/-- The point space of a nonempty algebraic space
locally of finite type over a field is discrete exactly when the algebraic space has
dimension zero. -/
@[stacks 0ACA "(2) <=> (4) <=> (5), the dim = 0 form: (2) <=> (4) for a nonempty space"]
theorem discretePoints_iff_zeroDimension (D : FiniteTypeOverField.{u}) :
    D.DiscretePoints ↔ D.ZeroDimension := by
  exact ⟨fun h ↦ zeroDimension_of_noNontrivialSpecialization D
    (noNontrivialSpecialization_of_discretePoints D h), fun h ↦
    discretePoints_of_chart_topologicalKrullDim_le_zero D
      (topologicalKrullDim_chart_le_zero_of_zeroDimension D h)⟩

/-- If the point space is discrete then it has
Krull dimension zero. -/
@[stacks 0ACA "the arrow into (3): (2) => (3), in the dim = 0 form"]
theorem zeroTopologicalDimension_of_discretePoints (D : FiniteTypeOverField.{u})
    (hD : D.DiscretePoints) : D.ZeroTopologicalDimension := by
  have : DiscreteTopology (points D.B (Spec (.of D.k)) D.base_mem D.X.left) := hD
  have : Nonempty (points D.B (Spec (.of D.k)) D.base_mem D.X.left) := D.nonempty
  exact topologicalKrullDim_eq_zero_of_discrete_nonempty

/-- If the point space is `T0` and has Krull dimension zero, then it is discrete. The hypothesis
that the point space is `T0` cannot be dropped. -/
@[stacks 0ACA "corrected part (3) => (2), the sharp form: |X| Kolmogorov"]
theorem discretePoints_of_zeroTopologicalDimension (D : FiniteTypeOverField.{u})
    (hT0 : T0Space (points D.B (Spec (.of D.k)) D.base_mem D.X.left))
    (hD : D.ZeroTopologicalDimension) : D.DiscretePoints := by
  exact discretePoints_of_chart_topologicalKrullDim_le_zero D
    (chart_topologicalKrullDim_le_zero_of_noSpecialization D
      (noNontrivialSpecialization_of_zeroTopologicalDimension D hT0 hD))

/-- A nonempty algebraic space locally of finite type
over a field has dimension zero exactly when its structure morphism is locally
quasi-finite. -/
@[stacks 0ACA "(2) <=> (4) <=> (5), the dim = 0 form: (4) <=> (5) for a nonempty space"]
theorem zeroDimension_iff_locallyQuasiFinite (D : FiniteTypeOverField.{u}) :
    D.ZeroDimension ↔ D.LocallyQuasiFiniteOverField := by
  constructor
  · intro hD U V a b h ha hb hcomm
    let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
    have hft : LocallyOfFiniteType (T.map h) := D.locallyOfFiniteType U V a b h ha hb hcomm
    have : DiscreteTopology (T.obj U) := discrete_chart_of_topologicalKrullDim_le_zero D U a ha
      (topologicalKrullDim_chart_le_zero_of_zeroDimension D hD U a ha)
    exact ⟨hft, locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ ↦
      isDiscrete_iff_discreteTopology.mpr inferInstance⟩
  · intro hD
    refine (zeroDimension_iff_forall_dimensionAtPoint_eq_zero D).mpr fun x ↦ ?_
    obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point D.B (Spec (.of D.k)) D.base_mem
      D.X.left D.isAlgebraicSpace x
    let c := baseEtaleChartForPoint D x U a ha p hp
    let T := BigFppfOver.toScheme D.B (Spec (.of D.k)) D.base_mem
    let f : T.obj c.U ⟶ T.obj c.V := T.map c.h
    have hpair := hD c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
    have : LocallyOfFiniteType f := hpair.1
    have : LocallyQuasiFinite f := hpair.2
    have : Subsingleton (T.obj c.V) := by
      show Subsingleton (Spec (.of D.k))
      infer_instance
    let u := c.sourcePoint D.B (Spec (.of D.k)) D.base_mem
    have hset : f ⁻¹' ({f u} : Set (T.obj c.V)) = Set.univ :=
      Set.eq_univ_of_forall fun z ↦ Subsingleton.elim (f z) (f u)
    have hpre : _root_.IsDiscrete (Set.univ : Set (T.obj c.U)) := by
      rw [← hset]
      exact locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mp hpair.2 (f u)
    have : DiscreteTopology (↥(Set.univ : Set (T.obj c.U))) :=
      _root_.isDiscrete_iff_discreteTopology.mp hpre
    have : DiscreteTopology (T.obj c.U) :=
      (Homeomorph.Set.univ (T.obj c.U)).discreteTopology_iff.mp inferInstance
    exact (dimensionAtPoint_eq_of_etale_chart D.B (Spec (.of D.k)) D.base_mem D.X.left
      D.isAlgebraicSpace x c.U c.a c.a_etale c.representative c.maps_to).trans
      (topologicalKrullDimAt_eq_zero_of_discrete u)

end FiniteTypeOverField

end AlgebraicGeometry.Space

end
