module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimitOfSize
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRepresentation

/-!
# Affine models of Situation 0DKU over an affine chart

Let `D` be Situation 0DKU.  This file compares two representations of base changes of the
inverse system along affine charts `z : yoneda Z ⟶ Y₀` and `z' = yoneda u ≫ z` with
`u : Z' ⟶ Z`: the representing objects of the second are the fibre products of those of the first
with `Z'` over `Z`, so on global sections they are pushouts of rings.  Under
`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit` the global sections of a
representation form a filtered colimit.  When `X₀` is itself an affine algebraic space,
represented by `Z'`, the stages `Xᵢ` and the limit `X` of `D` are represented by the
representation along `X₀ ⟶ Y₀`.

## Main definitions

* `AffineBaseChangeRepresentation.mapOfComp`: the morphism from the representation along `z'`
  to the representation along `z`.
* `AffineBaseChangeRepresentation.sectionsFunctor`: the rings of global sections of a
  representation, as a system over the stages.

## Main results

* `AffineBaseChangeRepresentation.isPullback_mapOfComp` and `isPushout_sections_mapOfComp`:
  the squares of representing objects are cartesian, and their rings of global sections are
  pushouts.
* `AffineBaseChangeRepresentation.isColimitSections`: under `IsSchemeLimit` the rings of global
  sections form a colimit.
* `RelativeDescentSituation.stageModelIso` and `limitModelIso`: when `X₀ ≅ yoneda Z'` the
  stages and the limit of `D` are the represented presheaves of a representation along
  `X₀ ⟶ Y₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I}

/-- A cartesian square of representing objects over affine charts has a pushout square of rings
of global sections, as soon as the corner `W` is affine. -/
private theorem isPushout_sections_of_isPullback_yoneda {Z Z' : BigAffineFppf B S hS}
    {W W' : BigFppfOver B S hS} {a : W' ⟶ W} {b : W' ⟶ (BigAffineFppf.inclusion B S hS).obj Z'}
    {q : W ⟶ (BigAffineFppf.inclusion B S hS).obj Z}
    {u : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj Z}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map q) (yoneda.map u)) :
    IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop
      ((BigFppfOver.toScheme B S hS).map u).appTop ((BigFppfOver.toScheme B S hS).map a).appTop
      ((BigFppfOver.toScheme B S hS).map b).appTop := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    Z.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Z')) :=
    Z'.property
  exact isPushout_appTop_of_isPullback
    (Stack.ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda h)

namespace AffineBaseChangeRepresentation

variable {Z : BigAffineFppf B S hS}
  {z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.Y.obj (op D.i₀)}
  (R : D.AffineBaseChangeRepresentation Z z)

/-- Two morphisms into a representing object agree when they agree after the two projections. -/
theorem hom_ext {i : D.LaterIndex} {T : BigFppfOver B S hS} {a b : T ⟶ R.W.obj (op i)}
    (hp : yoneda.map a ≫ R.p i = yoneda.map b ≫ R.p i) (hq : a ≫ R.q i = b ≫ R.q i) :
    a = b := by
  apply yoneda.map_injective
  refine (R.isPullback i).hom_ext hp ?_
  rw [← Functor.map_comp, ← Functor.map_comp, hq]

/-- Two morphisms into the vertex agree when they agree after the two projections. -/
theorem hom_ext_pt {T : BigFppfOver B S hS} {a b : T ⟶ R.c.pt}
    (hp : yoneda.map a ≫ R.pc = yoneda.map b ≫ R.pc) (hq : a ≫ R.qc = b ≫ R.qc) : a = b := by
  apply yoneda.map_injective
  refine R.isPullback_pt.hom_ext hp ?_
  rw [← Functor.map_comp, ← Functor.map_comp, hq]

section MapOfComp

variable {Z' : BigAffineFppf B S hS}
  {z' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ⟶ D.Y.obj (op D.i₀)}
  (R' : D.AffineBaseChangeRepresentation Z' z')
  (u : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj Z)
  (hu : yoneda.map u ≫ z = z')

include hu in
/-- The square from the representing object along `z'` into `Yᵢ` and `Z` commutes over `Y₀`. -/
theorem mapOfComp_condition (i : D.LaterIndex) :
    R'.p i ≫ D.Y.map (homOfLE i.2).op = yoneda.map (R'.q i ≫ u) ≫ z := by
  rw [Functor.map_comp, Category.assoc, hu]
  exact (R'.isPullback i).w

/-- The morphism from the representing object of `Yᵢ ×_{Y₀} Z'` to that of `Yᵢ ×_{Y₀} Z`. -/
def mapOfComp (i : D.LaterIndex) : R'.W.obj (op i) ⟶ R.W.obj (op i) :=
  yoneda.preimage ((R.isPullback i).lift (R'.p i) (yoneda.map (R'.q i ≫ u))
    (mapOfComp_condition R' u hu i))

/-- `mapOfComp` commutes with the projections to `Yᵢ`. -/
theorem mapOfComp_p (i : D.LaterIndex) :
    yoneda.map (R.mapOfComp R' u hu i) ≫ R.p i = R'.p i := by
  rw [mapOfComp, Functor.map_preimage, IsPullback.lift_fst]

/-- `mapOfComp` followed by the projection to `Z` is the projection to `Z'` followed by `u`. -/
theorem mapOfComp_q (i : D.LaterIndex) :
    R.mapOfComp R' u hu i ≫ R.q i = R'.q i ≫ u := by
  apply yoneda.map_injective
  rw [Functor.map_comp, mapOfComp, Functor.map_preimage, IsPullback.lift_snd]

/-- **The representing objects along `z'` are the fibre products with `Z'` over `Z`.** -/
theorem isPullback_yoneda_mapOfComp (i : D.LaterIndex) :
    IsPullback (yoneda.map (R.mapOfComp R' u hu i)) (yoneda.map (R'.q i))
      (yoneda.map (R.q i)) (yoneda.map u) := by
  refine IsPullback.of_right ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, mapOfComp_q])
    (R.isPullback i)
  rw [mapOfComp_p, hu]
  exact R'.isPullback i

/-- The representing schemes along `z'` are the fibre products with `Z'` over `Z`. -/
theorem isPullback_mapOfComp (i : D.LaterIndex) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (R.mapOfComp R' u hu i))
      ((BigFppfOver.toScheme B S hS).map (R'.q i))
      ((BigFppfOver.toScheme B S hS).map (R.q i)) ((BigFppfOver.toScheme B S hS).map u) :=
  Stack.ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda
    (R.isPullback_yoneda_mapOfComp R' u hu i)

/-- **The rings of global sections of the representing objects along `z'` are pushouts.** -/
theorem isPushout_sections_mapOfComp (i : D.LaterIndex) :
    IsPushout ((BigFppfOver.toScheme B S hS).map (R.q i)).appTop
      ((BigFppfOver.toScheme B S hS).map u).appTop
      ((BigFppfOver.toScheme B S hS).map (R.mapOfComp R' u hu i)).appTop
      ((BigFppfOver.toScheme B S hS).map (R'.q i)).appTop := by
  have := R.isAffine_W i
  exact isPushout_sections_of_isPullback_yoneda (R.isPullback_yoneda_mapOfComp R' u hu i)

/-- The morphisms `mapOfComp` are compatible with the transition maps. -/
theorem mapOfComp_naturality {i j : D.LaterIndex} (h : i ≤ j) :
    R'.W.map (homOfLE h).op ≫ R.mapOfComp R' u hu i =
      R.mapOfComp R' u hu j ≫ R.W.map (homOfLE h).op := by
  refine R.hom_ext ?_ ?_
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, mapOfComp_p,
      R.map_p, ← Category.assoc, mapOfComp_p, R'.map_p]
  · rw [Category.assoc, Category.assoc, mapOfComp_q, R.map_q, mapOfComp_q, ← Category.assoc,
      R'.map_q]

/-- The morphism between the vertices. -/
def mapOfCompPt : R'.c.pt ⟶ R.c.pt :=
  yoneda.preimage (R.isPullback_pt.lift R'.pc (yoneda.map (R'.qc ≫ u)) (by
    rw [Functor.map_comp, Category.assoc, hu]
    exact R'.isPullback_pt.w))

/-- `mapOfCompPt` commutes with the projections to the limit of the `Yᵢ`. -/
theorem mapOfCompPt_p : yoneda.map (R.mapOfCompPt R' u hu) ≫ R.pc = R'.pc := by
  rw [mapOfCompPt, Functor.map_preimage, IsPullback.lift_fst]

/-- `mapOfCompPt` followed by the projection to `Z` is the projection to `Z'` followed by `u`. -/
theorem mapOfCompPt_q : R.mapOfCompPt R' u hu ≫ R.qc = R'.qc ≫ u := by
  apply yoneda.map_injective
  rw [Functor.map_comp, mapOfCompPt, Functor.map_preimage, IsPullback.lift_snd]

/-- `mapOfCompPt` and the morphisms `mapOfComp` commute with the cone projections. -/
theorem mapOfCompPt_π (i : D.LaterIndex) :
    R'.c.π.app (op i) ≫ R.mapOfComp R' u hu i = R.mapOfCompPt R' u hu ≫ R.c.π.app (op i) := by
  refine R.hom_ext ?_ ?_
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, mapOfComp_p,
      R.π_p, ← Category.assoc, mapOfCompPt_p, R'.π_p]
  · rw [Category.assoc, Category.assoc, mapOfComp_q, R.π_q, mapOfCompPt_q, ← Category.assoc,
      R'.π_q]

/-- The vertex of the representation along `z'` is the fibre product of the vertex along `z`
with `Z'` over `Z`. -/
theorem isPullback_yoneda_mapOfCompPt :
    IsPullback (yoneda.map (R.mapOfCompPt R' u hu)) (yoneda.map R'.qc)
      (yoneda.map R.qc) (yoneda.map u) := by
  refine IsPullback.of_right ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, mapOfCompPt_q])
    R.isPullback_pt
  rw [mapOfCompPt_p, hu]
  exact R'.isPullback_pt

/-- When both vertices are affine, the ring of global sections of the vertex along `z'` is the
pushout of that of the vertex along `z` with the global sections of `Z'`. -/
theorem isPushout_sections_mapOfCompPt
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R.c.pt)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R'.c.pt)] :
    IsPushout ((BigFppfOver.toScheme B S hS).map R.qc).appTop
      ((BigFppfOver.toScheme B S hS).map u).appTop
      ((BigFppfOver.toScheme B S hS).map (R.mapOfCompPt R' u hu)).appTop
      ((BigFppfOver.toScheme B S hS).map R'.qc).appTop := by
  exact isPushout_sections_of_isPullback_yoneda (R.isPullback_yoneda_mapOfCompPt R' u hu)

end MapOfComp

section Sections

/-- The rings of global sections of the representing objects, as a system over the stages. -/
abbrev sectionsFunctor : D.LaterIndex ⥤ CommRingCat.{u} :=
  (R.W ⋙ BigFppfOver.toScheme B S hS).rightOp ⋙ Scheme.Γ

/-- The cocone of global sections with vertex the global sections of the vertex. -/
abbrev sectionsCocone : Cocone R.sectionsFunctor :=
  Scheme.Γ.mapCocone (coconeRightOpOfCone ((BigFppfOver.toScheme B S hS).mapCone R.c))

/-- **Under `IsSchemeLimit` the global sections of a representation form a colimit of rings.** -/
def isColimitSections (hR : IsLimit ((BigFppfOver.toScheme B S hS).mapCone R.c)) :
    IsColimit R.sectionsCocone := by
  haveI : ∀ i : D.LaterIndex,
      IsAffine ((R.W ⋙ BigFppfOver.toScheme B S hS).rightOp.obj i).unop := fun i =>
    R.isAffine_W i
  exact isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone _ hR)

end Sections

end AffineBaseChangeRepresentation

section Model

variable (D) {Z' : BigAffineFppf B S hS}
  (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ D.X₀)
  (R : D.AffineBaseChangeRepresentation Z' (e₀.hom ≫ D.p₀))

/-- The representing object along `X₀ ⟶ Y₀` at stage `j` gives a cartesian square over
`D.p₀`. -/
theorem stageModel_isPullback (j : D.LaterIndex) :
    IsPullback (R.p j) (yoneda.map (R.q j) ≫ e₀.hom) (D.Y.map (homOfLE j.2).op) D.p₀ :=
  (R.isPullback j).of_iso (Iso.refl _) (Iso.refl _) e₀ (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp)

/-- The vertex of the representation along `X₀ ⟶ Y₀` gives a cartesian square of the limit `Y`
over `D.p₀`. -/
theorem limitModel_isPullback :
    IsPullback R.pc (yoneda.map R.qc ≫ e₀.hom) (D.limitCone.π.app (op D.i₀)) D.p₀ :=
  R.isPullback_pt.of_iso (Iso.refl _) (Iso.refl _) e₀ (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp)

/-- **The stages of a situation with affine `X₀` are represented**: the representing object of
`Yⱼ ×_{Y₀} X₀` represents `Xⱼ`. -/
def stageModelIso (j : D.LaterIndex) : yoneda.obj (R.W.obj (op j)) ≅ D.Xᵢ j.1 j.2 :=
  (D.stageModel_isPullback e₀ R j).isoIsPullback _ _ (D.stage_isPullback j.1 j.2)

/-- **The limit of a situation with affine `X₀` is represented.** -/
def limitModelIso : yoneda.obj R.c.pt ≅ D.X :=
  (D.limitModel_isPullback e₀ R).isoIsPullback _ _ D.limit_isPullback

/-- `stageModelIso` followed by `D.toYᵢ` is the projection of the representation to `Yⱼ`. -/
@[reassoc (attr := simp)]
theorem stageModelIso_hom_toYᵢ (j : D.LaterIndex) :
    (D.stageModelIso e₀ R j).hom ≫ D.toYᵢ j.1 j.2 = R.p j :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `stageModelIso` followed by `D.toX₀` is the projection of the representation to `X₀`. -/
@[reassoc (attr := simp)]
theorem stageModelIso_hom_toX₀ (j : D.LaterIndex) :
    (D.stageModelIso e₀ R j).hom ≫ D.toX₀ j.1 j.2 = yoneda.map (R.q j) ≫ e₀.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- `limitModelIso` followed by `D.toLimit` is the projection of the vertex to the limit of the
`Yᵢ`. -/
@[reassoc (attr := simp)]
theorem limitModelIso_hom_toLimit :
    (D.limitModelIso e₀ R).hom ≫ D.toLimit = R.pc :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `limitModelIso` followed by `D.toInitial` is the projection of the vertex to `X₀`. -/
@[reassoc (attr := simp)]
theorem limitModelIso_hom_toInitial :
    (D.limitModelIso e₀ R).hom ≫ D.toInitial = yoneda.map R.qc ≫ e₀.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The representations of the stages are compatible with the transitions. -/
theorem stageModelIso_hom_fᵢⱼ {j k : D.LaterIndex} (h : j ≤ k) :
    (D.stageModelIso e₀ R k).hom ≫ D.fᵢⱼ j.1 k.1 j.2 k.2 h =
      yoneda.map (R.W.map (homOfLE h).op) ≫ (D.stageModelIso e₀ R j).hom := by
  refine (D.stage_isPullback j.1 j.2).hom_ext ?_ ?_
  · rw [Category.assoc, D.fᵢⱼ_toYᵢ, stageModelIso_hom_toYᵢ_assoc, Category.assoc,
      stageModelIso_hom_toYᵢ, R.map_p]
    rfl
  · rw [Category.assoc, D.fᵢⱼ_toX₀, stageModelIso_hom_toX₀, Category.assoc,
      stageModelIso_hom_toX₀, ← Category.assoc, ← Functor.map_comp, R.map_q]

/-- The representation of the limit is compatible with the projections. -/
theorem limitModelIso_hom_fᵢ (j : D.LaterIndex) :
    (D.limitModelIso e₀ R).hom ≫ D.fᵢ j.1 j.2 =
      yoneda.map (R.c.π.app (op j)) ≫ (D.stageModelIso e₀ R j).hom := by
  refine (D.stage_isPullback j.1 j.2).hom_ext ?_ ?_
  · rw [Category.assoc, D.fᵢ_toYᵢ, limitModelIso_hom_toLimit_assoc, Category.assoc,
      stageModelIso_hom_toYᵢ, R.π_p]
  · rw [Category.assoc, D.fᵢ_toX₀, limitModelIso_hom_toInitial, Category.assoc,
      stageModelIso_hom_toX₀, ← Category.assoc, ← Functor.map_comp, R.π_q]

end Model

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
