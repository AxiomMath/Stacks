module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimit

/-!
# Affine base changes of the inverse system of Situation 0DKU

Let `D` be Situation 0DKU and `z : yoneda Z ⟶ Y₀` an affine object of the site over the chosen
stage. The transition morphisms of `D` are affine, so each base change `Yᵢ ×_{Y₀} Z`, `i ≥ i₀`, is
represented by an affine object of the site; when the projection `Y ⟶ Y₀` is affine so is
`Y ×_{Y₀} Z`. This file chooses those representing objects and assembles them into an
`AlgebraicGeometry.Space.RelativeDescentSituation.AffineBaseChangeRepresentation`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.stageRepFunctor`: the inverse system of the
  objects representing the base changes `Yᵢ ×_{Y₀} Z`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.limitRepCone`: the cone over it formed by the
  object representing `Y ×_{Y₀} Z`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.affineBaseChangeRepresentation`: the chosen
  representation of the base changes along `z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

section Construction

variable (Z : BigAffineFppf B S hS)
  (z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.Y.obj (op D.i₀))

/-- For stages `i ≤ j` at or beyond `i₀`, the transition `Yⱼ ⟶ Yᵢ` followed by `Yᵢ ⟶ Y₀` is
`Yⱼ ⟶ Y₀`. -/
theorem stage_map_comp {i j : D.LaterIndex} (h : i ≤ j) :
    D.Y.map (homOfLE h).op ≫ D.Y.map (homOfLE i.2).op = D.Y.map (homOfLE j.2).op := by
  rw [← D.Y.map_comp]
  rfl

/-- For every stage `i` at or beyond `i₀`, the base change `Yᵢ ×_{Y₀} Z` is represented by an
affine object of the site. -/
theorem exists_stageRep (i : D.LaterIndex) :
    ∃ (W : BigAffineFppf B S hS)
      (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ D.Y.obj (op i.1))
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ (BigAffineFppf.inclusion B S hS).obj Z),
      IsPullback p (yoneda.map q) (D.Y.map (homOfLE i.2).op) z :=
  D.transition_isAffine D.i₀ i.1 i.2 Z z

/-- The affine object of the site representing `Yᵢ ×_{Y₀} Z`. -/
def stageRepObj (i : D.LaterIndex) : BigAffineFppf B S hS :=
  (D.exists_stageRep Z z i).choose

/-- The projection of the representing object to `Yᵢ`. -/
def stageRepP (i : D.LaterIndex) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.stageRepObj Z z i)) ⟶ D.Y.obj (op i.1) :=
  (D.exists_stageRep Z z i).choose_spec.choose

/-- The projection of the representing object to `Z`. -/
def stageRepQ (i : D.LaterIndex) :
    (BigAffineFppf.inclusion B S hS).obj (D.stageRepObj Z z i) ⟶
      (BigAffineFppf.inclusion B S hS).obj Z :=
  (D.exists_stageRep Z z i).choose_spec.choose_spec.choose

/-- The representing object, with its two projections, is a pullback of `Yᵢ ⟶ Y₀` along `z`. -/
theorem stageRep_isPullback (i : D.LaterIndex) :
    IsPullback (D.stageRepP Z z i) (yoneda.map (D.stageRepQ Z z i)) (D.Y.map (homOfLE i.2).op) z :=
  (D.exists_stageRep Z z i).choose_spec.choose_spec.choose_spec

/-- The transition morphism between the representing objects, for `i ≤ j`. -/
def stageRepMap {i j : D.LaterIndex} (h : i ≤ j) :
    (BigAffineFppf.inclusion B S hS).obj (D.stageRepObj Z z j) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.stageRepObj Z z i) :=
  yoneda.preimage ((D.stageRep_isPullback Z z i).lift (D.stageRepP Z z j ≫ D.Y.map (homOfLE h).op)
    (yoneda.map (D.stageRepQ Z z j)) (by
      rw [Category.assoc, D.stage_map_comp h]
      exact (D.stageRep_isPullback Z z j).w))

/-- The transition morphism is compatible with the projections to `Yⱼ` and `Yᵢ`. -/
theorem stageRepMap_p {i j : D.LaterIndex} (h : i ≤ j) :
    yoneda.map (D.stageRepMap Z z h) ≫ D.stageRepP Z z i =
      D.stageRepP Z z j ≫ D.Y.map (homOfLE h).op := by
  rw [stageRepMap, Functor.map_preimage, IsPullback.lift_fst]

/-- The transition morphism commutes with the projections to `Z`. -/
theorem stageRepMap_q {i j : D.LaterIndex} (h : i ≤ j) :
    D.stageRepMap Z z h ≫ D.stageRepQ Z z i = D.stageRepQ Z z j := by
  apply yoneda.map_injective
  rw [Functor.map_comp, stageRepMap, Functor.map_preimage, IsPullback.lift_snd]

/-- Two morphisms into the object representing `Yᵢ ×_{Y₀} Z` are equal when they agree after
both projections. -/
theorem stageRepMap_ext {i : D.LaterIndex} {T : BigFppfOver B S hS}
    {a b : T ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stageRepObj Z z i)}
    (hp : yoneda.map a ≫ D.stageRepP Z z i = yoneda.map b ≫ D.stageRepP Z z i)
    (hq : a ≫ D.stageRepQ Z z i = b ≫ D.stageRepQ Z z i) : a = b := by
  apply yoneda.map_injective
  refine (D.stageRep_isPullback Z z i).hom_ext hp ?_
  rw [← Functor.map_comp, ← Functor.map_comp, hq]

/-- The representing objects, as an inverse system indexed by the stages at or beyond `i₀`. -/
def stageRepFunctor : D.LaterIndexᵒᵖ ⥤ BigFppfOver B S hS where
  obj i := (BigAffineFppf.inclusion B S hS).obj (D.stageRepObj Z z i.unop)
  map f := D.stageRepMap Z z (leOfHom f.unop)
  map_id i := by
    refine D.stageRepMap_ext Z z ?_ ?_
    · rw [stageRepMap_p, CategoryTheory.Functor.map_id, Category.id_comp,
        show (homOfLE (leOfHom (𝟙 i).unop)).op = 𝟙 (op i.unop.1) from Subsingleton.elim _ _,
        D.Y.map_id, Category.comp_id]
    · rw [stageRepMap_q, Category.id_comp]
  map_comp f g := by
    refine D.stageRepMap_ext Z z ?_ ?_
    · rw [stageRepMap_p, Functor.map_comp, Category.assoc, stageRepMap_p, ← Category.assoc,
        stageRepMap_p, Category.assoc, ← D.Y.map_comp]
      rfl
    · rw [stageRepMap_q, Category.assoc, stageRepMap_q, stageRepMap_q]

/-- The projection of the limit `Y` to `Yᵢ` followed by `Yᵢ ⟶ Y₀` is the projection to `Y₀`. -/
theorem limitCone_π_comp (i : D.LaterIndex) :
    D.limitCone.π.app (op i.1) ≫ D.Y.map (homOfLE i.2).op = D.limitCone.π.app (op D.i₀) :=
  D.limitCone.w (homOfLE i.2).op

variable (hπ : IsAffineHom B S hS (D.limitCone.π.app (op D.i₀)))
include hπ

/-- When `Y ⟶ Y₀` is affine, the base change `Y ×_{Y₀} Z` is represented by an affine object of
the site. -/
theorem exists_limitRep :
    ∃ (W : BigAffineFppf B S hS)
      (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ D.limitCone.pt)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ (BigAffineFppf.inclusion B S hS).obj Z),
      IsPullback p (yoneda.map q) (D.limitCone.π.app (op D.i₀)) z :=
  hπ Z z

/-- The affine object of the site representing `Y ×_{Y₀} Z`. -/
def limitRepObj : BigAffineFppf B S hS := (D.exists_limitRep Z z hπ).choose

/-- Its projection to `Y`. -/
def limitRepP :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.limitRepObj Z z hπ)) ⟶ D.limitCone.pt :=
  (D.exists_limitRep Z z hπ).choose_spec.choose

/-- Its projection to `Z`. -/
def limitRepQ :
    (BigAffineFppf.inclusion B S hS).obj (D.limitRepObj Z z hπ) ⟶
      (BigAffineFppf.inclusion B S hS).obj Z :=
  (D.exists_limitRep Z z hπ).choose_spec.choose_spec.choose

/-- The representing object of `Y ×_{Y₀} Z`, with its two projections, is a pullback of
`Y ⟶ Y₀` along `z`. -/
theorem limitRep_isPullback :
    IsPullback (D.limitRepP Z z hπ) (yoneda.map (D.limitRepQ Z z hπ))
      (D.limitCone.π.app (op D.i₀)) z :=
  (D.exists_limitRep Z z hπ).choose_spec.choose_spec.choose_spec

/-- The projection of the representing object of the limit to that of a stage. -/
def limitRepπ (i : D.LaterIndex) :
    (BigAffineFppf.inclusion B S hS).obj (D.limitRepObj Z z hπ) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.stageRepObj Z z i) :=
  yoneda.preimage ((D.stageRep_isPullback Z z i).lift
    (D.limitRepP Z z hπ ≫ D.limitCone.π.app (op i.1)) (yoneda.map (D.limitRepQ Z z hπ)) (by
      rw [Category.assoc, D.limitCone_π_comp i]
      exact (D.limitRep_isPullback Z z hπ).w))

/-- The projection `limitRepπ` is compatible with the projections to `Y` and `Yᵢ`. -/
theorem limitRepπ_p (i : D.LaterIndex) :
    yoneda.map (D.limitRepπ Z z hπ i) ≫ D.stageRepP Z z i =
      D.limitRepP Z z hπ ≫ D.limitCone.π.app (op i.1) := by
  rw [limitRepπ, Functor.map_preimage, IsPullback.lift_fst]

/-- The projection `limitRepπ` commutes with the projections to `Z`. -/
theorem limitRepπ_q (i : D.LaterIndex) :
    D.limitRepπ Z z hπ i ≫ D.stageRepQ Z z i = D.limitRepQ Z z hπ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, limitRepπ, Functor.map_preimage, IsPullback.lift_snd]

/-- The cone of the representing objects. -/
def limitRepCone : Cone (D.stageRepFunctor Z z) where
  pt := (BigAffineFppf.inclusion B S hS).obj (D.limitRepObj Z z hπ)
  π :=
    { app i := D.limitRepπ Z z hπ i.unop
      naturality i j f := by
        refine D.stageRepMap_ext Z z ?_ ?_
        · dsimp [stageRepFunctor]
          rw [Category.id_comp, Functor.map_comp, Category.assoc, stageRepMap_p,
            ← Category.assoc, limitRepπ_p, limitRepπ_p, Category.assoc,
            ← D.limitCone.w (homOfLE (show (unop j).1 ≤ (unop i).1 from leOfHom f.unop)).op]
          rfl
        · dsimp [stageRepFunctor]
          rw [Category.id_comp, Category.assoc, stageRepMap_q, limitRepπ_q, limitRepπ_q] }

/-- **The chosen representation of the base changes along `z`.** -/
def affineBaseChangeRepresentation : D.AffineBaseChangeRepresentation Z z where
  W := D.stageRepFunctor Z z
  c := D.limitRepCone Z z hπ
  p i := D.stageRepP Z z i
  q i := D.stageRepQ Z z i
  isPullback i := D.stageRep_isPullback Z z i
  map_p _ _ h := D.stageRepMap_p Z z h
  map_q _ _ h := D.stageRepMap_q Z z h
  pc := D.limitRepP Z z hπ
  qc := D.limitRepQ Z z hπ
  isPullback_pt := D.limitRep_isPullback Z z hπ
  π_p i := D.limitRepπ_p Z z hπ i
  π_q i := D.limitRepπ_q Z z hπ i

end Construction

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
