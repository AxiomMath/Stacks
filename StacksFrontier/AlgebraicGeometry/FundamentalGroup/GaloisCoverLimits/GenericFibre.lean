module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.ResidueFibreLimit
public import StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.LimitDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.NormalApproximation

/-!
# Pointed Galois covers of the fibre of a limit come from a stage

Let `φ : A ⟶ B` be a morphism of cofiltered systems of schemes, with limit cones `cA`, `cB`
and a morphism `p : cA.pt ⟶ cB.pt` of the vertices, such that every square
`cA.pt ⟶ A j, cB.pt ⟶ B j` is cartesian. For a point `s` of `cB.pt`, the fibre of `p` at `s` is
the limit of the fibres of the `φ j` at the images of `s`
(`Stacks.AlgebraicGeometry.Fibres.fiberConeIsLimit`). This file shows that the projections of
that limit are flat, surjective and quasi-compact, and descends to a stage a finite étale Galois
cover of the fibre of `p` together with a rational point over a section. This is the descent of
`Z ⟶ X_η` and of its rational point in the proof of [Stacks, Tag 0EZJ].

## Main results

* `AlgebraicGeometry.GaloisCoverLimits.ptFiberConeMap_isPullback`: the projection from the fibre
  of the limit to the fibre of a stage is a base change of the map of residue fields.
* `AlgebraicGeometry.GaloisCoverLimits.exists_pointed_galoisCover_model`: the descent of a
  pointed finite étale Galois cover of the fibre of the limit.

## References

* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace GaloisCoverLimits



section Fibres

variable {J : Type u} [Category.{u} J] {A B : J ⥤ Scheme.{u}} (φ : A ⟶ B) (cB : Cone B)
  (s : cB.pt)

/-- If the transition morphisms of `A` and `B` are affine, so are the transition morphisms of
the diagram of fibres at the images of `s`. -/
instance [∀ {i j : J} (g : i ⟶ j), IsAffineHom (A.map g)]
    [∀ {i j : J} (g : i ⟶ j), IsAffineHom (B.map g)] {i j : J} (g : i ⟶ j) :
    IsAffineHom ((ptFiberDiagram φ cB s).map g) := by
  have : IsAffineHom (Spec.map (ptResidueTransition B cB s g)) := inferInstance
  exact Stacks.AlgebraicGeometry.Fibres.isAffineHom_pullback_map (φ.app i) _ (φ.app j) _ (A.map g)
    (Spec.map (ptResidueTransition B cB s g)) (B.map g) (φ.naturality g).symm
    ((ptResidueSpecι B cB s).naturality g).symm

/-- If `φ j` is quasi-compact, the fibre of `φ j` at the image of `s` is quasi-compact. -/
instance [∀ j, QuasiCompact (φ.app j)] (j : J) : CompactSpace ((ptFiberDiagram φ cB s).obj j) :=
  inferInstanceAs (CompactSpace (pullback (φ.app j)
    ((B.obj j).fromSpecResidueField (cB.π.app j s)) : Scheme.{u}))

/-- If `φ j` is quasi-separated, the fibre of `φ j` at the image of `s` is quasi-separated. -/
instance [∀ j, QuasiSeparated (φ.app j)] (j : J) :
    QuasiSeparatedSpace ((ptFiberDiagram φ cB s).obj j) :=
  have : QuasiSeparatedSpace (pullback (φ.app j)
      ((B.obj j).fromSpecResidueField (cB.π.app j s)) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (φ.app j)
      ((B.obj j).fromSpecResidueField (cB.π.app j s)))
  inferInstanceAs (QuasiSeparatedSpace (pullback (φ.app j)
    ((B.obj j).fromSpecResidueField (cB.π.app j s)) : Scheme.{u}))

variable (cA : Cone A) (p : cA.pt ⟶ cB.pt) (hp : ∀ j, cA.π.app j ≫ φ.app j = p ≫ cB.π.app j)

/-- If a map into a pullback has cartesian outer rectangle with its first projection, it is a
pullback square with the second projection. -/
private theorem isPullback_snd_of_comp_fst {P Q R S T : Scheme.{u}} {f : R ⟶ T} {g : S ⟶ T}
    (m : P ⟶ pullback f g) (u : P ⟶ Q) (v : Q ⟶ S)
    (h : IsPullback (m ≫ pullback.fst f g) u f (v ≫ g)) (hm : m ≫ pullback.snd f g = u ≫ v) :
    IsPullback m u (pullback.snd f g) v :=
  h.of_right hm (IsPullback.of_hasPullback f g)

/-- **The projections of the fibre of the limit are base changes.** If the squares of the
limit cones are cartesian, the projection from the fibre of `p` at `s` to the fibre of a stage
at the image of `s` is the base change of the map of residue fields. -/
theorem ptFiberConeMap_isPullback (hsq : ∀ j, IsPullback (cA.π.app j) p (φ.app j) (cB.π.app j))
    (j : J) :
    IsPullback (ptFiberConeMap φ cB s cA p hp j) (pullback.snd p (cB.pt.fromSpecResidueField s))
      (pullback.snd (φ.app j) ((ptResidueSpecι B cB s).app j)) (ptResidueSpecProj B cB s j) := by
  refine isPullback_snd_of_comp_fst _ _ _ ?_ (ptFiberConeMap_snd φ cB s cA p hp j)
  rw [ptFiberConeMap_fst φ cB s cA p hp, ptResidueSpecProj_comp B cB s]
  exact (IsPullback.of_hasPullback p (cB.pt.fromSpecResidueField s)).paste_horiz (hsq j)

/-- If the squares of the limit cones are cartesian, the projection from the fibre of `p` at `s`
to the fibre of a stage is flat. -/
theorem flat_fiberConeMap (hsq : ∀ j, IsPullback (cA.π.app j) p (φ.app j) (cB.π.app j))
    (j : J) : Flat (ptFiberConeMap φ cB s cA p hp j) :=
  MorphismProperty.of_isPullback (ptFiberConeMap_isPullback φ cB s cA p hp hsq j).flip
    inferInstance

/-- If the squares of the limit cones are cartesian, the projection from the fibre of `p` at `s`
to the fibre of a stage is surjective. -/
theorem surjective_fiberConeMap (hsq : ∀ j, IsPullback (cA.π.app j) p (φ.app j) (cB.π.app j))
    (j : J) : Surjective (ptFiberConeMap φ cB s cA p hp j) :=
  MorphismProperty.of_isPullback (ptFiberConeMap_isPullback φ cB s cA p hp hsq j).flip
    inferInstance

/-- If the squares of the limit cones are cartesian, the projection from the fibre of `p` at `s`
to the fibre of a stage is quasi-compact. -/
theorem quasiCompact_fiberConeMap
    (hsq : ∀ j, IsPullback (cA.π.app j) p (φ.app j) (cB.π.app j)) (j : J) :
    QuasiCompact (ptFiberConeMap φ cB s cA p hp j) :=
  MorphismProperty.of_isPullback (ptFiberConeMap_isPullback φ cB s cA p hp hsq j).flip
    inferInstance

/-! ### Sections -/

/-- The rational point of the fibre of the stage `j` given by a section. -/
def fiberSec (σA : ∀ j, B.obj j ⟶ A.obj j) (hσA : ∀ j, σA j ≫ φ.app j = 𝟙 _) (j : J) :
    (ptResidueSpecDiagram B cB s).obj j ⟶ (ptFiberDiagram φ cB s).obj j :=
  pullback.lift ((ptResidueSpecι B cB s).app j ≫ σA j) (𝟙 _) (by
    rw [Category.assoc, hσA, Category.comp_id, Category.id_comp])

variable (σA : ∀ j, B.obj j ⟶ A.obj j) (hσA : ∀ j, σA j ≫ φ.app j = 𝟙 _)

/-- The rational point `fiberSec` is a section of the projection of the fibre to the spectrum of
the residue field. -/
theorem fiberSec_res (j : J) :
    fiberSec φ cB s σA hσA j ≫ pullback.snd (φ.app j) ((ptResidueSpecι B cB s).app j) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The composite of `fiberSec` with the projection of the fibre to `A j` is the composite of the
point of `B j` with the section `σA j`. -/
theorem fiberSec_incl (j : J) :
    fiberSec φ cB s σA hσA j ≫ pullback.fst (φ.app j) ((ptResidueSpecι B cB s).app j) =
      (ptResidueSpecι B cB s).app j ≫ σA j :=
  pullback.lift_fst _ _ _

/-- The rational points of the fibres given by a section are compatible with the transition
morphisms. -/
theorem fiberSec_naturality (hnat : ∀ {i j : J} (g : i ⟶ j), B.map g ≫ σA j = σA i ≫ A.map g)
    {i j : J} (g : i ⟶ j) :
    (ptResidueSpecDiagram B cB s).map g ≫ fiberSec φ cB s σA hσA j =
      fiberSec φ cB s σA hσA i ≫ (ptFiberDiagram φ cB s).map g := by
  have hE : (ptResidueSpecDiagram B cB s).map g ≫ (ptResidueSpecι B cB s).app j =
      (ptResidueSpecι B cB s).app i ≫ B.map g :=
    specMap_ptResidueTransition_fromSpecResidueField B cB s g
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fiberSec_incl, Category.assoc, ptFiberDiagram_map_fst φ cB s,
      ← Category.assoc (fiberSec φ cB s σA hσA i), fiberSec_incl, ← Category.assoc, hE,
      Category.assoc, Category.assoc, hnat]
  · rw [Category.assoc, fiberSec_res, Category.assoc, ptFiberDiagram_map_snd φ cB s,
      ← Category.assoc, fiberSec_res, Category.comp_id, Category.id_comp]

/-- The rational point of the fibre of the limit given by a section. -/
def limSec (σ : cB.pt ⟶ cA.pt) (hσ : σ ≫ p = 𝟙 _) :
    Spec (cB.pt.residueField s) ⟶ pullback p (cB.pt.fromSpecResidueField s) :=
  pullback.lift (cB.pt.fromSpecResidueField s ≫ σ) (𝟙 (Spec (cB.pt.residueField s))) (by
    simp [hσ])

/-- The rational point of the fibre of the limit maps to the rational points of the fibres of
the stages. -/
theorem limSec_fiberConeMap (σ : cB.pt ⟶ cA.pt) (hσ : σ ≫ p = 𝟙 _)
    (hlim : ∀ j, σ ≫ cA.π.app j = cB.π.app j ≫ σA j) (j : J) :
    limSec cB s cA p σ hσ ≫ ptFiberConeMap φ cB s cA p hp j =
      ptResidueSpecProj B cB s j ≫ fiberSec φ cB s σA hσA j := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ptFiberConeMap_fst φ cB s cA p hp, Category.assoc, fiberSec_incl,
      ← Category.assoc, limSec, pullback.lift_fst, Category.assoc, hlim, ← Category.assoc,
      ← ptResidueSpecProj_comp B cB s, Category.assoc]
  · rw [Category.assoc, ptFiberConeMap_snd φ cB s cA p hp, Category.assoc, fiberSec_res,
      ← Category.assoc, limSec, pullback.lift_snd, Category.id_comp, Category.comp_id]

end Fibres

/-! ### Descent of a pointed Galois cover -/

/-- A morphism from the limit to a scheme locally of finite presentation over a stage, lying
over a given morphism from the stage, comes from a later stage. -/
theorem exists_point_at_stage {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {V X : Scheme.{u}} (f : V ⟶ X) [LocallyOfFinitePresentation f]
    (σ : D.obj i ⟶ X) (z : c.pt ⟶ V) (hz : z ≫ f = c.π.app i ≫ σ) :
    ∃ (j : I) (e : j ⟶ i) (w : D.obj j ⟶ V), w ≫ f = D.map e ≫ σ := by
  let z' := pullback.lift z (c.π.app i) hz
  obtain ⟨j, e, w, -, hw⟩ := NormalApproximation.exists_factor_from_stage D c hc i
    (pullback.snd f σ) z' (pullback.lift_snd _ _ _)
  exact ⟨j, e, w ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition,
    ← Category.assoc, hw]⟩

/-- A morphism of Galois covers into `V`, equivariant for the actions, lifts equivariantly into
the base change of `V`. -/
private theorem action_comp_lift_baseChange {W S T : Scheme.{u}} {G : Type v} [Group G]
    [Finite G] (q : T ⟶ S) (V : FiniteEtaleGaloisCover S G)
    (hconn : ConnectedSpace ((finiteEtaleBaseChange q).obj V.obj).left)
    (Z : FiniteEtaleGaloisCover W G) (P : Z.obj.left ⟶ V.obj.left) (r : W ⟶ T)
    (h : P ≫ V.obj.hom = (Z.obj.hom ≫ r) ≫ q)
    (hPact : ∀ g, (Z.action g).hom.left ≫ P = P ≫ (V.action g).hom.left) (g : Gᵐᵒᵖ) :
    (Z.action g).hom.left ≫ pullback.lift P (Z.obj.hom ≫ r) h =
      pullback.lift P (Z.obj.hom ≫ r) h ≫ ((V.baseChange q hconn).action g).hom.left := by
  have hL₁ := pullback.lift_fst P (Z.obj.hom ≫ r) h
  have hL₂ := pullback.lift_snd P (Z.obj.hom ≫ r) h
  apply pullback.hom_ext
  · exact ((Category.assoc _ _ _).trans ((congrArg _ hL₁).trans (hPact g))).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (FiniteEtaleGaloisCover.baseChange_action_fst q V hconn g)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hL₁)))).symm
  · have hV : ((V.baseChange q hconn).action g).hom.left ≫ pullback.snd V.obj.hom q =
        pullback.snd V.obj.hom q := MorphismProperty.Over.w ((V.baseChange q hconn).action g).hom
    have hZ : (Z.action g).hom.left ≫ Z.obj.hom = Z.obj.hom :=
      MorphismProperty.Over.w (Z.action g).hom
    exact ((Category.assoc _ _ _).trans ((congrArg _ hL₂).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hZ)))).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hV).trans hL₂)).symm

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {A B : J ⥤ Scheme.{u}} (φ : A ⟶ B)
  (cB : Cone B) (s : cB.pt) (cA : Cone A) (p : cA.pt ⟶ cB.pt)
  (hp : ∀ j, cA.π.app j ≫ φ.app j = p ≫ cB.π.app j)

/-- **A pointed Galois cover of the fibre of a limit comes from a stage.** Let the squares of
the limit cones be cartesian, the transition morphisms affine and the `φ j` quasi-compact and
quasi-separated, and let `σ` be a section of `p` compatible with sections `σA j` of the `φ j`. A
finite étale Galois cover of the fibre of `p` at `s` with a rational point over the point given
by `σ` is, equivariantly, the base change of a finite étale Galois cover of the fibre of a stage
with a rational point over the point given by `σA`. -/
theorem exists_pointed_galoisCover_model (hA : IsLimit cA) (hB : IsLimit cB)
    [∀ {i j : J} (g : i ⟶ j), IsAffineHom (A.map g)]
    [∀ {i j : J} (g : i ⟶ j), IsAffineHom (B.map g)]
    [∀ j, QuasiCompact (φ.app j)] [∀ j, QuasiSeparated (φ.app j)]
    (hsq : ∀ j, IsPullback (cA.π.app j) p (φ.app j) (cB.π.app j))
    (σA : ∀ j, B.obj j ⟶ A.obj j) (hσA : ∀ j, σA j ≫ φ.app j = 𝟙 _)
    (hnat : ∀ {i j : J} (g : i ⟶ j), B.map g ≫ σA j = σA i ≫ A.map g)
    (σ : cB.pt ⟶ cA.pt) (hσ : σ ≫ p = 𝟙 _)
    (hlim : ∀ j, σ ≫ cA.π.app j = cB.π.app j ≫ σA j)
    {G : Type v} [Group G] [Finite G]
    (Z : FiniteEtaleGaloisCover (pullback p (cB.pt.fromSpecResidueField s)) G)
    (z : Spec (cB.pt.residueField s) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = limSec cB s cA p σ hσ) :
    ∃ (j : J) (V : FiniteEtaleGaloisCover ((ptFiberDiagram φ cB s).obj j) G)
      (P : Z.obj.left ⟶ V.obj.left) (w : (ptResidueSpecDiagram B cB s).obj j ⟶ V.obj.left),
      IsPullback P Z.obj.hom V.obj.hom (ptFiberConeMap φ cB s cA p hp j) ∧
      (∀ g, (Z.action g).hom.left ≫ P = P ≫ (V.action g).hom.left) ∧
      w ≫ V.obj.hom = fiberSec φ cB s σA hσA j := by
  let F := ptFiberDiagram φ cB s
  let a := ptFiberCone φ cB s cA p hp
  have h₁ : ∀ j, Flat (a.π.app j) := flat_fiberConeMap φ cB s cA p hp hsq
  have h₂ : ∀ j, Surjective (a.π.app j) := surjective_fiberConeMap φ cB s cA p hp hsq
  have h₃ : ∀ j, QuasiCompact (a.π.app j) := quasiCompact_fiberConeMap φ cB s cA p hp hsq
  obtain ⟨i, V, P, hP, hPact⟩ :=
    exists_galoisCover_model F a (isLimitPtFiberCone φ cB s cA p hp hA hB) Z
  have hV₁ : IsFinite V.obj.hom := V.obj.prop.1
  have hV₂ : Etale V.obj.hom := V.obj.prop.2
  let Zh : Z.obj.left ⟶ pullback p (cB.pt.fromSpecResidueField s) := Z.obj.hom
  have hP2 : IsPullback P Zh V.obj.hom (ptFiberConeMap φ cB s cA p hp i) := hP
  have hzP : (z ≫ P) ≫ V.obj.hom =
      ptResidueSpecProj B cB s i ≫ fiberSec φ cB s σA hσA i := by
    rw [Category.assoc, hP2.w, ← Category.assoc]
    show (z ≫ Z.obj.hom) ≫ _ = _
    rw [hz]
    exact limSec_fiberConeMap φ cB s cA p hp σA hσA σ hσ hlim i
  obtain ⟨j, e, w₀, hw₀⟩ := exists_point_at_stage (ptResidueSpecDiagram B cB s)
    (ptResidueSpecCone B cB s) (isLimitPtResidueSpecCone B cB s hB) i V.obj.hom
    (fiberSec φ cB s σA hσA i) (z ≫ P) hzP
  have hnatj : ptFiberConeMap φ cB s cA p hp j ≫ (ptFiberDiagram φ cB s).map e =
      ptFiberConeMap φ cB s cA p hp i := ptFiberConeMap_naturality φ cB s cA p hp e
  let P' : Z.obj.left ⟶ pullback V.obj.hom ((ptFiberDiagram φ cB s).map e) :=
    pullback.lift P (Zh ≫ ptFiberConeMap φ cB s cA p hp j) (by
      rw [Category.assoc, hnatj, hP2.w])
  have hP'₁ : P' ≫ pullback.fst V.obj.hom ((ptFiberDiagram φ cB s).map e) = P :=
    pullback.lift_fst _ _ _
  have hP'₂ : P' ≫ pullback.snd V.obj.hom ((ptFiberDiagram φ cB s).map e) =
      Zh ≫ ptFiberConeMap φ cB s cA p hp j := pullback.lift_snd _ _ _
  have hP' : IsPullback P' Zh (pullback.snd V.obj.hom ((ptFiberDiagram φ cB s).map e))
      (ptFiberConeMap φ cB s cA p hp j) :=
    isPullback_snd_of_comp_fst _ _ _ (by rwa [hP'₁, hnatj]) hP'₂
  have hP's : Surjective P' := MorphismProperty.of_isPullback hP'.flip (h₂ j)
  have hconn : ConnectedSpace ((finiteEtaleBaseChange ((ptFiberDiagram φ cB s).map e)).obj
      V.obj).left :=
    Function.Surjective.connectedSpace hP's.surj P'.continuous
  let V' := V.baseChange ((ptFiberDiagram φ cB s).map e) hconn
  let w : (ptResidueSpecDiagram B cB s).obj j ⟶ V'.obj.left :=
    pullback.lift w₀ (fiberSec φ cB s σA hσA j)
      (hw₀.trans (fiberSec_naturality φ cB s σA hσA hnat e))
  exact ⟨j, V', P', w, hP',
    action_comp_lift_baseChange _ V hconn Z P _ _ hPact, pullback.lift_snd _ _ _⟩

end GaloisCoverLimits

end AlgebraicGeometry

end
