module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Polynomial.Subring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantNorm
public import StacksFrontier.AlgebraicGeometry.Groupoids.IntegralInvariantHelpers
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-!
# Integrality of an affine groupoid scheme over its invariant functions

Let `G` be a groupoid scheme with affine object and arrow schemes whose source and target maps
are both finite locally free. Then every global function on the object scheme is integral over
the ring of invariant functions.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isIntegral_invariantRing`: the object ring is integral over
  the invariant ring.

## References

* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### The affine line over a scheme and its global functions -/

/-- The integral model of the affine line. -/
private abbrev affineLineModel : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial (ULift.{u} PUnit) (ULift.{u} ℤ)))

/-- The structure morphism of the affine line over `S`. -/
private abbrev affineLineProjection (S : Scheme.{u}) :
    AffineSpace (ULift.{u} PUnit) S ⟶ S :=
  AffineSpace (ULift.{u} PUnit) S ↘ S

/-- The affine line over `X` is the base change along `f : X ⟶ S` of the affine line over
`S`. -/
private def affineLineBaseChangeIso {S X : Scheme.{u}} (f : X ⟶ S) :
    pullback f (affineLineProjection S) ≅ AffineSpace (ULift.{u} PUnit) X :=
  (AffineSpace.isPullback_map (n := ULift.{u} PUnit) f).flip.isoPullback.symm

private theorem affineLineBaseChangeIso_hom_over {S X : Scheme.{u}} (f : X ⟶ S) :
    (affineLineBaseChangeIso f).hom ≫ (AffineSpace (ULift.{u} PUnit) X ↘ X) =
      pullback.fst f (affineLineProjection S) :=
  (Iso.inv_comp_eq _).mpr
    (AffineSpace.isPullback_map (n := ULift.{u} PUnit) f).flip.isoPullback_hom_fst.symm

private theorem affineLineBaseChangeIso_hom_toSpecMvPoly {S X : Scheme.{u}} (f : X ⟶ S) :
    (affineLineBaseChangeIso f).hom ≫ AffineSpace.toSpecMvPoly (ULift.{u} PUnit) X =
      pullback.snd f (affineLineProjection S) ≫
        AffineSpace.toSpecMvPoly (ULift.{u} PUnit) S := by
  rw [← AffineSpace.map_toSpecMvPoly (n := ULift.{u} PUnit) f, ← Category.assoc]
  congr 1
  exact (Iso.inv_comp_eq _).mpr
    (AffineSpace.isPullback_map (n := ULift.{u} PUnit) f).flip.isoPullback_hom_snd.symm

/-- Identifying a pullback of the affine line over `S` with the affine line over `X` is
compatible with the projection to `X`. -/
private theorem isoPullback_comp_affineLineBaseChangeIso_over {S X P : Scheme.{u}} {f : X ⟶ S}
    {fst : P ⟶ X} {snd : P ⟶ AffineSpace (ULift.{u} PUnit) S}
    (h : IsPullback fst snd f (affineLineProjection S)) :
    (h.isoPullback.hom ≫ (affineLineBaseChangeIso f).hom) ≫
      (AffineSpace (ULift.{u} PUnit) X ↘ X) = fst := by
  rw [Category.assoc, affineLineBaseChangeIso_hom_over, h.isoPullback_hom_fst]

/-- Identifying a pullback of the affine line over `S` with the affine line over `X` is
compatible with the coordinate map to `Spec ℤ[x]`. -/
private theorem isoPullback_comp_affineLineBaseChangeIso_toSpecMvPoly {S X P : Scheme.{u}}
    {f : X ⟶ S} {fst : P ⟶ X} {snd : P ⟶ AffineSpace (ULift.{u} PUnit) S}
    (h : IsPullback fst snd f (affineLineProjection S)) :
    (h.isoPullback.hom ≫ (affineLineBaseChangeIso f).hom) ≫
      AffineSpace.toSpecMvPoly (ULift.{u} PUnit) X =
      snd ≫ AffineSpace.toSpecMvPoly (ULift.{u} PUnit) S := by
  rw [Category.assoc, affineLineBaseChangeIso_hom_toSpecMvPoly, ← Category.assoc,
    h.isoPullback_hom_snd]

/-! ### Base change of a groupoid scheme to the affine line -/

/-- The object scheme of the base change of `G` to the affine line is the affine line over the
object scheme of `G`. -/
private def baseChangeObjectsIso {S : Scheme.{u}} (G : GroupoidScheme S)
    (bc : BaseChange (affineLineProjection S) G) :
    bc.groupoid.objects.left ≅ AffineSpace (ULift.{u} PUnit) G.objects.left :=
  bc.isPullback_objects.isoPullback ≪≫ affineLineBaseChangeIso G.objects.hom

/-- The arrow scheme of the base change of `G` to the affine line is the affine line over the
arrow scheme of `G`. -/
private def baseChangeArrowsIso {S : Scheme.{u}} (G : GroupoidScheme S)
    (bc : BaseChange (affineLineProjection S) G) :
    bc.groupoid.arrows.left ≅ AffineSpace (ULift.{u} PUnit) G.arrows.left :=
  bc.isPullback_arrows.isoPullback ≪≫ affineLineBaseChangeIso G.arrows.hom

private theorem baseChange_objects_isAffine {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] (bc : BaseChange (affineLineProjection S) G) :
    IsAffine bc.groupoid.objects.left :=
  IsAffine.of_isIso (baseChangeObjectsIso G bc).hom

private theorem baseChange_arrows_isAffine {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.arrows.left] (bc : BaseChange (affineLineProjection S) G) :
    IsAffine bc.groupoid.arrows.left :=
  IsAffine.of_isIso (baseChangeArrowsIso G bc).hom

/-- Global functions on the object scheme of the base change of `G` to the affine line, read as
polynomials over the object ring of `G`. -/
private def baseChangeObjectsSectionsEquiv {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] (bc : BaseChange (affineLineProjection S) G) :
    Γ(bc.groupoid.objects.left, ⊤) ≃+* Polynomial Γ(G.objects.left, ⊤) :=
  (asIso (Scheme.Γ.map (baseChangeObjectsIso G bc).inv.op)).commRingCatIsoToRingEquiv.trans
    (affineLineSectionsEquiv (X := G.objects.left))

/-- Global functions on the arrow scheme of the base change of `G` to the affine line, read as
polynomials over the arrow ring of `G`. -/
private def baseChangeArrowsSectionsEquiv {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.arrows.left] (bc : BaseChange (affineLineProjection S) G) :
    Γ(bc.groupoid.arrows.left, ⊤) ≃+* Polynomial Γ(G.arrows.left, ⊤) :=
  (asIso (Scheme.Γ.map (baseChangeArrowsIso G bc).inv.op)).commRingCatIsoToRingEquiv.trans
    (affineLineSectionsEquiv (X := G.arrows.left))

/-- A structure map of the base-changed groupoid is the affine-space functor applied to the
corresponding structure map of `G`. -/
private theorem baseChange_comm {S : Scheme.{u}} (G : GroupoidScheme S)
    (bc : BaseChange (affineLineProjection S) G) (k : G.arrows ⟶ G.objects)
    (k' : bc.groupoid.arrows ⟶ bc.groupoid.objects)
    (hk : bc.projection.mapArrows.left ≫ k.left =
      k'.left ≫ bc.projection.mapObjects.left) :
    k'.left ≫ (baseChangeObjectsIso G bc).hom =
      (baseChangeArrowsIso G bc).hom ≫ AffineSpace.map (ULift.{u} PUnit) k.left := by
  have hobjfst : (baseChangeObjectsIso G bc).hom ≫
      (AffineSpace (ULift.{u} PUnit) G.objects.left ↘ G.objects.left) =
      bc.projection.mapObjects.left :=
    isoPullback_comp_affineLineBaseChangeIso_over bc.isPullback_objects
  have harrfst : (baseChangeArrowsIso G bc).hom ≫
      (AffineSpace (ULift.{u} PUnit) G.arrows.left ↘ G.arrows.left) =
      bc.projection.mapArrows.left :=
    isoPullback_comp_affineLineBaseChangeIso_over bc.isPullback_arrows
  have hobjsnd : (baseChangeObjectsIso G bc).hom ≫
      AffineSpace.toSpecMvPoly (ULift.{u} PUnit) G.objects.left =
      bc.groupoid.objects.hom ≫ AffineSpace.toSpecMvPoly (ULift.{u} PUnit) S :=
    isoPullback_comp_affineLineBaseChangeIso_toSpecMvPoly bc.isPullback_objects
  have harrsnd : (baseChangeArrowsIso G bc).hom ≫
      AffineSpace.toSpecMvPoly (ULift.{u} PUnit) G.arrows.left =
      bc.groupoid.arrows.hom ≫ AffineSpace.toSpecMvPoly (ULift.{u} PUnit) S :=
    isoPullback_comp_affineLineBaseChangeIso_toSpecMvPoly bc.isPullback_arrows
  refine pullback.hom_ext ?_ ?_
  · show (k'.left ≫ (baseChangeObjectsIso G bc).hom) ≫
        (AffineSpace (ULift.{u} PUnit) G.objects.left ↘ G.objects.left) =
      ((baseChangeArrowsIso G bc).hom ≫ AffineSpace.map _ k.left) ≫
        (AffineSpace (ULift.{u} PUnit) G.objects.left ↘ G.objects.left)
    rw [Category.assoc, hobjfst, Category.assoc, AffineSpace.map_over, ← Category.assoc,
      harrfst]
    exact hk.symm
  · show (k'.left ≫ (baseChangeObjectsIso G bc).hom) ≫
        AffineSpace.toSpecMvPoly (ULift.{u} PUnit) G.objects.left =
      ((baseChangeArrowsIso G bc).hom ≫ AffineSpace.map _ k.left) ≫
        AffineSpace.toSpecMvPoly (ULift.{u} PUnit) G.objects.left
    rw [Category.assoc, hobjsnd, ← Category.assoc, Over.w, Category.assoc,
      AffineSpace.map_toSpecMvPoly, harrsnd]

/-- Under the polynomial descriptions of the base-changed coordinate rings, a structure map of
the base-changed groupoid acts coefficientwise. -/
private theorem baseChangeSections_map {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    (bc : BaseChange (affineLineProjection S) G) (k : G.arrows ⟶ G.objects)
    (k' : bc.groupoid.arrows ⟶ bc.groupoid.objects)
    (hk : bc.projection.mapArrows.left ≫ k.left =
      k'.left ≫ bc.projection.mapObjects.left)
    (x : Γ(bc.groupoid.objects.left, ⊤)) :
    baseChangeArrowsSectionsEquiv G bc (k'.left.appTop x) =
      (baseChangeObjectsSectionsEquiv G bc x).map k.left.appTop.hom := by
  have hc := baseChange_comm G bc k k' hk
  have hi : (baseChangeArrowsIso G bc).inv ≫ k'.left =
      AffineSpace.map (ULift.{u} PUnit) k.left ≫ (baseChangeObjectsIso G bc).inv := by
    apply (cancel_mono (baseChangeObjectsIso G bc).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hc, Iso.inv_hom_id_assoc]
  have hs := congrArg (fun g => Scheme.Hom.appTop g x) hi
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hs
  show affineLineSectionsEquiv (X := G.arrows.left)
      ((baseChangeArrowsIso G bc).inv.appTop (k'.left.appTop x)) = _
  rw [hs]
  have hm := RingHom.congr_fun (affineLineSectionsEquiv_map k.left)
    (baseChangeObjectsSectionsEquiv G bc x)
  change affineLineSectionsEquiv (X := G.arrows.left)
      ((AffineSpace.map (ULift.{u} PUnit) k.left).appTop
        ((affineLineSectionsEquiv (X := G.objects.left)).symm
          (affineLineSectionsEquiv (X := G.objects.left)
            ((baseChangeObjectsIso G bc).inv.appTop x)))) = _ at hm
  rwa [RingEquiv.symm_apply_apply] at hm

private theorem baseChange_source_isFiniteLocallyFree {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] (bc : BaseChange (affineLineProjection S) G) :
    IsFiniteLocallyFree bc.groupoid.source.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback bc.source_isPullback inferInstance

/-! ### Integrality over the invariant ring -/

/-- For an affine groupoid scheme with finite locally free source and target, the ring of global
functions on the object scheme is integral over its subring of invariant functions. -/
@[stacks 03BJ, sga "3 V 4.1" "more general"]
theorem isIntegral_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] :
    (Subring.subtype (invariantRing G)).IsIntegral := by
  classical
  intro x
  obtain ⟨bc⟩ := exists_baseChange (affineLineProjection S) G
  have : IsAffine bc.groupoid.objects.left := baseChange_objects_isAffine G bc
  have : IsAffine bc.groupoid.arrows.left := baseChange_arrows_isAffine G bc
  have : IsFiniteLocallyFree bc.groupoid.source.left :=
    baseChange_source_isFiniteLocallyFree G bc
  let A' := Γ(bc.groupoid.objects.left, ⊤)
  let B' := Γ(bc.groupoid.arrows.left, ⊤)
  let s : A' →+* B' := sourceMap bc.groupoid
  let t : A' →+* B' := targetMap bc.groupoid
  let eO := baseChangeObjectsSectionsEquiv G bc
  let eA := baseChangeArrowsSectionsEquiv G bc
  let z : A' := eO.symm Polynomial.X
  let a : A' := eO.symm (Polynomial.C x)
  let y : A' := 1 - a * z
  let : Algebra A' B' := s.toAlgebra
  obtain ⟨hfin, hproj, hinv⟩ := det_lmul_targetMap_mem_invariantRing bc.groupoid y
  have : Module.Finite A' B' := hfin
  have : Module.Projective A' B' := hproj
  let d := ProjectiveDeterminant.det (Algebra.lmul A' B' (t y))
  let p : Polynomial Γ(G.objects.left, ⊤) := eO d
  have hs (v : A') : eA (s v) = (eO v).map G.source.left.appTop.hom :=
    baseChangeSections_map G bc G.source bc.groupoid.source
      (congrArg Over.Hom.left bc.projection.map_source) v
  have ht (v : A') : eA (t v) = (eO v).map G.target.left.appTop.hom :=
    baseChangeSections_map G bc G.target bc.groupoid.target
      (congrArg Over.Hom.left bc.projection.map_target) v
  have hz : s z = t z := by
    apply eA.injective
    rw [hs, ht]
    simp [z]
  have hpInv : p.map G.source.left.appTop.hom = p.map G.target.left.appTop.hom := by
    rw [← hs d, ← ht d]
    exact congrArg eA hinv
  have hlin : Algebra.lmul A' B' (t y) =
      LinearMap.id + (-z) • Algebra.lmul A' B' (t a) := by
    ext v
    show t y * v = v + s (-z) * (t a * v)
    dsimp only [y]
    rw [map_sub, map_one, map_mul, ← hz, map_neg]
    ring
  have hp0 : p.coeff 0 = 1 := by
    have hh : (Polynomial.constantCoeff.comp eO.toRingHom) (-z) = 0 := by simp [z]
    have hd := ProjectiveDeterminant.map_det_id_add_smul_eq_one
      (Polynomial.constantCoeff.comp eO.toRingHom) (-z) hh (Algebra.lmul A' B' (t a))
    rwa [← hlin] at hd
  let ε : B' →+* A' := bc.groupoid.identity.left.appTop.hom
  have hεs : ε.comp s = RingHom.id A' :=
    appTop_comp_of_section _ _ (congrArg Over.Hom.left bc.groupoid.source_identity)
  have hεt : ε.comp t = RingHom.id A' :=
    appTop_comp_of_section _ _ (congrArg Over.Hom.left bc.groupoid.target_identity)
  let e : B' →ₐ[A'] A' := { __ := ε, commutes' := fun r => RingHom.congr_fun hεs r }
  have hdiv : y ∣ d := by
    have hd := ProjectiveDeterminant.map_dvd_det_lmul e (t y)
    rwa [show e (t y) = y from RingHom.congr_fun hεt y] at hd
  have hpdiv : 1 - Polynomial.C x * Polynomial.X ∣ p := by
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨eO q, ?_⟩
    show eO d = _
    rw [hq, map_mul]
    congr 1
    simp only [y, map_sub, map_one, map_mul, a, z, RingEquiv.apply_symm_apply]
  obtain ⟨N, hmonic, hroot⟩ := Polynomial.monic_relation_of_divisor x p hp0 hpdiv
  refine RingHom.isIntegral_of_monic_polynomial_invariant _ _ x (p.reflect N) hmonic hroot ?_
  show (p.reflect N).map G.source.left.appTop.hom =
    (p.reflect N).map G.target.left.appTop.hom
  rw [← Polynomial.reflect_map, ← Polynomial.reflect_map, hpInv]

end AlgebraicGeometry.GroupoidScheme

end

end
