module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Polynomial.Subring
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.IntegralInvariantHelpers
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineNorm
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integrality of the object ring over the invariant ring

Let `G` be a groupoid scheme whose object and arrow schemes are affine and whose source and
target maps are finite locally free. Then the ring of global functions on the object scheme is
integral over its subring of invariant functions `AlgebraicGeometry.invariantRing`.

## Main results

* `AlgebraicGeometry.isIntegral_over_invariantRing`: the ring of global functions on the object
  scheme of an affine groupoid scheme with finite locally free source and target is integral
  over the subring of invariant functions.

## References

* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Morphisms

/-- The integral model of the affine line, the spectrum of the polynomial ring on a one-element
index type. -/
private def lineModel : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial (ULift.{u} PUnit) (ULift.{u} ℤ)))

/-- The projection of the affine line over `S` to `S`. -/
private def lineProjection (S : Scheme.{u}) :
    AffineSpace (ULift.{u} PUnit) S ⟶ S :=
  pullback.fst (terminal.from S) (terminal.from lineModel)

/-- Base changing the affine line over `S` along `f : X ⟶ S` gives the affine line over `X`. -/
private def lineBaseChangeIso {S X : Scheme.{u}} (f : X ⟶ S) :
    pullback f (lineProjection S) ≅ AffineSpace (ULift.{u} PUnit) X := by
  change pullback f (pullback.fst (terminal.from S) (terminal.from lineModel)) ≅
    pullback (terminal.from X) (terminal.from lineModel)
  exact pullbackRightPullbackFstIso (terminal.from S) (terminal.from lineModel) f ≪≫
    pullback.congrHom (terminalIsTerminal.hom_ext _ _) rfl

/-- The comparison isomorphism for the affine line is compatible with the projections to the
base. -/
private theorem lineBaseChangeIso_hom_fst {S X : Scheme.{u}} (f : X ⟶ S) :
    (lineBaseChangeIso f).hom ≫
      (AffineSpace (ULift.{u} PUnit) X ↘ X) =
    pullback.fst f (lineProjection S) := by
  unfold AffineSpace
  have h : f ≫ terminal.from S = terminal.from X := terminalIsTerminal.hom_ext _ _
  change (pullbackRightPullbackFstIso (terminal.from S) (terminal.from lineModel) f).hom ≫
      (pullback.congrHom h rfl).hom ≫
        pullback.fst (terminal.from X) (terminal.from lineModel) = _
  have hcongr : (pullback.congrHom h rfl).hom ≫
      pullback.fst (terminal.from X) (terminal.from lineModel) =
      pullback.fst (f ≫ terminal.from S) (terminal.from lineModel) := by
    rw [pullback.congrHom_hom]
    dsimp only [pullback.map]
    rw [pullback.lift_fst]
    simp
  rw [hcongr]
  exact pullbackRightPullbackFstIso_hom_fst _ _ _

/-- The comparison isomorphism for the affine line is compatible with the maps to the integral
model. -/
private theorem lineBaseChangeIso_hom_snd {S X : Scheme.{u}} (f : X ⟶ S) :
    (lineBaseChangeIso f).hom ≫
      AffineSpace.toSpecMvPoly (ULift.{u} PUnit) X =
    pullback.snd f (lineProjection S) ≫
      AffineSpace.toSpecMvPoly (ULift.{u} PUnit) S := by
  unfold AffineSpace AffineSpace.toSpecMvPoly
  have h : f ≫ terminal.from S = terminal.from X := terminalIsTerminal.hom_ext _ _
  change (pullbackRightPullbackFstIso (terminal.from S) (terminal.from lineModel) f).hom ≫
      (pullback.congrHom h rfl).hom ≫
        pullback.snd (terminal.from X) (terminal.from lineModel) = _
  have hcongr : (pullback.congrHom h rfl).hom ≫
      pullback.snd (terminal.from X) (terminal.from lineModel) =
      pullback.snd (f ≫ terminal.from S) (terminal.from lineModel) := by
    rw [pullback.congrHom_hom]
    dsimp only [pullback.map]
    rw [pullback.lift_snd]
    simp
  rw [hcongr]
  exact pullbackRightPullbackFstIso_hom_snd _ _ _

/-- The comparison of a pullback along the projection of the affine line with the affine line
over the base is compatible with the projection to the base. -/
private theorem isoPullback_lineBaseChangeIso_fst {S X P : Scheme.{u}} {f : X ⟶ S}
    {p : P ⟶ X} {q : P ⟶ AffineSpace (ULift.{u} PUnit) S}
    (h : IsPullback p q f (lineProjection S)) :
    (h.isoPullback ≪≫ lineBaseChangeIso f).hom ≫
      (AffineSpace (ULift.{u} PUnit) X ↘ X) = p := by
  rw [Iso.trans_hom, Category.assoc, lineBaseChangeIso_hom_fst, h.isoPullback_hom_fst]

/-- The comparison of a pullback along the projection of the affine line with the affine line
over the base is compatible with the maps to the integral model. -/
private theorem isoPullback_lineBaseChangeIso_snd {S X P : Scheme.{u}} {f : X ⟶ S}
    {p : P ⟶ X} {q : P ⟶ AffineSpace (ULift.{u} PUnit) S}
    (h : IsPullback p q f (lineProjection S)) :
    (h.isoPullback ≪≫ lineBaseChangeIso f).hom ≫
      AffineSpace.toSpecMvPoly (ULift.{u} PUnit) X =
    q ≫ AffineSpace.toSpecMvPoly (ULift.{u} PUnit) S := by
  rw [Iso.trans_hom, Category.assoc, lineBaseChangeIso_hom_snd, ← Category.assoc,
    h.isoPullback_hom_snd]

/-- A chosen base change of a groupoid scheme along the projection of the affine line. -/
private def lineBaseChange {S : Scheme.{u}} (G : GroupoidScheme S) :
    GroupoidScheme.BaseChange (lineProjection S) G :=
  Classical.choice (GroupoidScheme.exists_baseChange (lineProjection S) G)

/-- The source map of a base-changed groupoid scheme is the base change of the source map. -/
private theorem lineBaseChange_source_isPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (lineBaseChange G).projection.mapArrows.left
      (lineBaseChange G).groupoid.source.left G.source.left
      (lineBaseChange G).projection.mapObjects.left := by
  have hcomm : (lineBaseChange G).projection.mapArrows.left ≫ G.source.left =
      (lineBaseChange G).groupoid.source.left ≫
        (lineBaseChange G).projection.mapObjects.left := by
    simpa using congrArg Over.Hom.left (lineBaseChange G).projection.map_source
  have houter : IsPullback (lineBaseChange G).projection.mapArrows.left
      ((lineBaseChange G).groupoid.source.left ≫ (lineBaseChange G).groupoid.objects.hom)
      (G.source.left ≫ G.objects.hom) (lineProjection S) := by
    simpa only [← Category.assoc, Over.w] using (lineBaseChange G).isPullback_arrows
  exact ((lineBaseChange G).isPullback_objects.paste_vert_iff hcomm).mp houter

/-- The object scheme of the base change along the affine line is the affine line over the
object scheme. -/
private def lineBaseChangeObjectsIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (lineBaseChange G).groupoid.objects.left ≅
      AffineSpace (ULift.{u} PUnit) G.objects.left :=
  (lineBaseChange G).isPullback_objects.isoPullback ≪≫ lineBaseChangeIso G.objects.hom

/-- The arrow scheme of the base change along the affine line is the affine line over the arrow
scheme. -/
private def lineBaseChangeArrowsIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (lineBaseChange G).groupoid.arrows.left ≅
      AffineSpace (ULift.{u} PUnit) G.arrows.left :=
  (lineBaseChange G).isPullback_arrows.isoPullback ≪≫ lineBaseChangeIso G.arrows.hom

/-- The object ring of the base change along the affine line is the polynomial ring over the
object ring. -/
private def lineBaseChangeObjectsSectionsEquiv {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] :
    Γ((lineBaseChange G).groupoid.objects.left, ⊤) ≃+* Polynomial Γ(G.objects.left, ⊤) :=
  (asIso (Scheme.Γ.map (lineBaseChangeObjectsIso G).inv.op)).commRingCatIsoToRingEquiv.trans
    (affineLineSectionsEquiv (X := G.objects.left))

/-- The arrow ring of the base change along the affine line is the polynomial ring over the
arrow ring. -/
private def lineBaseChangeArrowsSectionsEquiv {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.arrows.left] :
    Γ((lineBaseChange G).groupoid.arrows.left, ⊤) ≃+* Polynomial Γ(G.arrows.left, ⊤) :=
  (asIso (Scheme.Γ.map (lineBaseChangeArrowsIso G).inv.op)).commRingCatIsoToRingEquiv.trans
    (affineLineSectionsEquiv (X := G.arrows.left))

/-- A structure map of the base-changed groupoid scheme is identified, under the comparison
isomorphisms with affine lines, with the affine line over the corresponding structure map. -/
private theorem lineBaseChange_comm {S : Scheme.{u}} (G : GroupoidScheme S)
    (f : G.arrows ⟶ G.objects)
    (f' : (lineBaseChange G).groupoid.arrows ⟶ (lineBaseChange G).groupoid.objects)
    (hf : (lineBaseChange G).projection.mapArrows.left ≫ f.left =
      f'.left ≫ (lineBaseChange G).projection.mapObjects.left) :
    f'.left ≫ (lineBaseChangeObjectsIso G).hom =
      (lineBaseChangeArrowsIso G).hom ≫
        AffineSpace.map (ULift.{u} PUnit) f.left := by
  have hobjfst : (lineBaseChangeObjectsIso G).hom ≫ _ = _ :=
    isoPullback_lineBaseChangeIso_fst (lineBaseChange G).isPullback_objects
  have harrfst : (lineBaseChangeArrowsIso G).hom ≫ _ = _ :=
    isoPullback_lineBaseChangeIso_fst (lineBaseChange G).isPullback_arrows
  have hobjsnd : (lineBaseChangeObjectsIso G).hom ≫ _ = _ :=
    isoPullback_lineBaseChangeIso_snd (lineBaseChange G).isPullback_objects
  have harrsnd : (lineBaseChangeArrowsIso G).hom ≫ _ = _ :=
    isoPullback_lineBaseChangeIso_snd (lineBaseChange G).isPullback_arrows
  apply pullback.hom_ext
  · change (f'.left ≫ (lineBaseChangeObjectsIso G).hom) ≫
        (AffineSpace (ULift.{u} PUnit) G.objects.left ↘ G.objects.left) =
      ((lineBaseChangeArrowsIso G).hom ≫ AffineSpace.map _ f.left) ≫
        (AffineSpace (ULift.{u} PUnit) G.objects.left ↘ G.objects.left)
    rw [Category.assoc, hobjfst, Category.assoc, AffineSpace.map_over,
      ← Category.assoc, harrfst]
    exact hf.symm
  · change (f'.left ≫ (lineBaseChangeObjectsIso G).hom) ≫
        AffineSpace.toSpecMvPoly (ULift.{u} PUnit) G.objects.left =
      ((lineBaseChangeArrowsIso G).hom ≫ AffineSpace.map _ f.left) ≫
        AffineSpace.toSpecMvPoly (ULift.{u} PUnit) G.objects.left
    rw [Category.assoc, hobjsnd, ← Category.assoc, Over.w,
      Category.assoc, AffineSpace.map_toSpecMvPoly, harrsnd]

/-- On global functions, a structure map of the base-changed groupoid scheme is the
coefficientwise map induced by the corresponding structure map. -/
private theorem lineBaseChangeSections_map {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    (f : G.arrows ⟶ G.objects)
    (f' : (lineBaseChange G).groupoid.arrows ⟶ (lineBaseChange G).groupoid.objects)
    (hf : (lineBaseChange G).projection.mapArrows.left ≫ f.left =
      f'.left ≫ (lineBaseChange G).projection.mapObjects.left)
    (x : Γ((lineBaseChange G).groupoid.objects.left, ⊤)) :
    lineBaseChangeArrowsSectionsEquiv G (f'.left.appTop x) =
      (lineBaseChangeObjectsSectionsEquiv G x).map f.left.appTop.hom := by
  have hi : (lineBaseChangeArrowsIso G).inv ≫ f'.left =
      AffineSpace.map (ULift.{u} PUnit) f.left ≫ (lineBaseChangeObjectsIso G).inv := by
    apply (cancel_mono (lineBaseChangeObjectsIso G).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [lineBaseChange_comm G f f' hf, Iso.inv_hom_id_assoc]
  have hs := congrArg (fun g => Scheme.Hom.appTop g x) hi
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hs
  change affineLineSectionsEquiv (X := G.arrows.left)
      ((lineBaseChangeArrowsIso G).inv.appTop (f'.left.appTop x)) = _
  rw [hs]
  have hm := RingHom.congr_fun (affineLineSectionsEquiv_map f.left)
    (lineBaseChangeObjectsSectionsEquiv G x)
  change affineLineSectionsEquiv (X := G.arrows.left)
      ((AffineSpace.map (ULift.{u} PUnit) f.left).appTop
        ((affineLineSectionsEquiv (X := G.objects.left)).symm
          (affineLineSectionsEquiv (X := G.objects.left)
            ((lineBaseChangeObjectsIso G).inv.appTop x)))) = _ at hm
  rwa [RingEquiv.symm_apply_apply] at hm

/-- The source map of the base change along the affine line is finite locally free. -/
private theorem lineBaseChange_source_isFiniteLocallyFree {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFiniteLocallyFree G.source.left] :
    IsFiniteLocallyFree (lineBaseChange G).groupoid.source.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => IsFiniteLocallyFree f)
    (lineBaseChange_source_isPullback G) inferInstance

/-- The object scheme of the base change along the affine line is affine. -/
private theorem lineBaseChange_objects_isAffine {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] :
    IsAffine (lineBaseChange G).groupoid.objects.left := by
  let : IsAffine (AffineSpace (ULift.{u} PUnit) G.objects.left) := inferInstance
  exact (IsAffine.iff_of_isIso (lineBaseChangeObjectsIso G).hom).mpr inferInstance

/-- The determinant of an endomorphism of a finite projective module may be computed as the
determinant of a matrix after stabilizing along a split injection into a finite free module. -/
private theorem det_eq_det_toMatrix'_stabilization
    {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (φ : M →ₗ[R] M) {n : ℕ} (q : (Fin n → R) →ₗ[R] M)
    (i : M →ₗ[R] (Fin n → R)) (hqi : q.comp i = LinearMap.id) :
    ProjectiveDeterminant.det φ =
      (LinearMap.toMatrix' (LinearMap.id + i.comp ((φ - LinearMap.id).comp q))).det := by
  rw [LinearMap.det_toMatrix', ← ProjectiveDeterminant.det_eq_linearMap_det_of_basis
    (Pi.basisFun R (Fin n)), ProjectiveDeterminant.det_one_add_comp_comm]
  congr 1
  rw [LinearMap.comp_assoc, hqi, LinearMap.comp_id]
  abel

/-- An endomorphism of a finite projective module has an adjugate: a second endomorphism whose
composite with it is multiplication by the determinant. -/
private theorem exists_adjugate_projective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (φ : M →ₗ[R] M) :
    ∃ ψ : M →ₗ[R] M, φ.comp ψ = ProjectiveDeterminant.det φ • LinearMap.id := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let : Subsingleton M := Module.subsingleton R M
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨n, q, i, _, _, hqi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let F := LinearMap.id + i.comp ((φ - LinearMap.id).comp q)
  let A := LinearMap.toMatrix' F
  let adj := Matrix.toLin' A.adjugate
  have hF : F.comp adj = A.det • LinearMap.id := by
    apply LinearMap.toMatrix'.injective
    simpa [A, adj, LinearMap.toMatrix'_comp] using Matrix.mul_adjugate A
  have hqF : q.comp F = φ.comp q := by
    dsimp [F]
    rw [LinearMap.comp_add, LinearMap.comp_id, ← LinearMap.comp_assoc, hqi,
      LinearMap.id_comp, LinearMap.sub_comp, LinearMap.id_comp]
    abel
  have hdet : A.det = ProjectiveDeterminant.det φ := by
    exact (det_eq_det_toMatrix'_stabilization φ q i hqi).symm
  refine ⟨q.comp (adj.comp i), ?_⟩
  ext x
  change φ (q (adj (i x))) = ProjectiveDeterminant.det φ • x
  calc
    _ = q (F (adj (i x))) := LinearMap.congr_fun hqF.symm _
    _ = q (A.det • i x) := congrArg q (LinearMap.congr_fun hF (i x))
    _ = _ := by
      rw [map_smul, hdet]
      exact congrArg (ProjectiveDeterminant.det φ • ·) (LinearMap.congr_fun hqi x)

/-- The determinant of the identity plus a multiple of a scalar becomes `1` under any ring map
killing that scalar. -/
private theorem map_det_one_add_smul
    {R T M : Type*} [CommRing R] [CommRing T] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (h : R →+* T) (r : R) (hr : h r = 0) (φ : M →ₗ[R] M) :
    h (ProjectiveDeterminant.det (LinearMap.id + r • φ)) = 1 := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (ProjectiveDeterminant.det _) 1, map_one]
  obtain ⟨n, q, i, _, _, hqi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  rw [det_eq_det_toMatrix'_stabilization _ q i hqi]
  have heq : LinearMap.id + i.comp (((LinearMap.id + r • φ) - LinearMap.id).comp q) =
      LinearMap.id + r • (i.comp (φ.comp q)) := by
    simp only [add_sub_cancel_left, LinearMap.smul_comp, LinearMap.comp_smul]
  rw [heq, h.map_det]
  have hm : h.mapMatrix (LinearMap.toMatrix' (LinearMap.id + r • (i.comp (φ.comp q)))) = 1 := by
    ext j k
    simp [RingHom.mapMatrix_apply, hr, LinearMap.toMatrix'_apply, Matrix.one_apply]
  rw [hm, Matrix.det_one]

/-- A retraction of a finite projective algebra sends each element to a divisor of its norm. -/
private theorem norm_dvd_of_retraction
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] (e : B →ₐ[R] R) (b : B) :
    e b ∣ ProjectiveDeterminant.det (Algebra.lmul R B b) := by
  obtain ⟨ψ, hψ⟩ := exists_adjugate_projective (Algebra.lmul R B b)
  refine ⟨e (ψ 1), ?_⟩
  simpa using (congrArg (fun f : B →ₗ[R] B => e (f 1)) hψ).symm

/-- For an affine groupoid scheme with finite locally free source and target, the ring of global
functions on the object scheme is integral over its subring of invariant functions. -/
@[stacks 03BJ, sga "3 V 4.1" "more general"]
theorem isIntegral_over_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] :
    (invariantRing G).subtype.IsIntegral := by
  classical
  intro x
  let bc := lineBaseChange G
  let A' := Γ(bc.groupoid.objects.left, ⊤)
  let B' := Γ(bc.groupoid.arrows.left, ⊤)
  let s : A' →+* B' := sourceMap bc.groupoid
  let t : A' →+* B' := targetMap bc.groupoid
  let eO := lineBaseChangeObjectsSectionsEquiv G
  let eA := lineBaseChangeArrowsSectionsEquiv G
  let z : A' := eO.symm Polynomial.X
  let a : A' := eO.symm (Polynomial.C x)
  let y : A' := 1 - a * z
  let : IsAffine bc.groupoid.objects.left := lineBaseChange_objects_isAffine G
  let : IsFiniteLocallyFree bc.groupoid.source.left :=
    lineBaseChange_source_isFiniteLocallyFree G
  let : Algebra A' B' := s.toAlgebra
  obtain ⟨hfin, hproj, hinv⟩ := norm_targetMap_mem_invariantRing bc.groupoid y
  let : Module.Finite A' B' := hfin
  let : Module.Projective A' B' := hproj
  let d := ProjectiveDeterminant.det (Algebra.lmul A' B' (t y))
  let p : Polynomial Γ(G.objects.left, ⊤) := eO d
  have hs (v : A') : eA (s v) = (eO v).map G.source.left.appTop.hom :=
    lineBaseChangeSections_map G G.source bc.groupoid.source
      (congrArg Over.Hom.left bc.projection.map_source) v
  have ht (v : A') : eA (t v) = (eO v).map G.target.left.appTop.hom :=
    lineBaseChangeSections_map G G.target bc.groupoid.target
      (congrArg Over.Hom.left bc.projection.map_target) v
  have hz : s z = t z := by
    apply eA.injective
    rw [hs, ht]
    simp [z]
  have hdinv : s d = t d := hinv
  have hpInv : p.map G.source.left.appTop.hom = p.map G.target.left.appTop.hom := by
    rw [← hs d, ← ht d]
    exact congrArg eA hdinv
  have hlin : Algebra.lmul A' B' (t y) =
      LinearMap.id + (-z) • Algebra.lmul A' B' (t a) := by
    ext v
    change t y * v = v + s (-z) * (t a * v)
    dsimp only [y]
    rw [map_sub, map_one, map_mul, ← hz, map_neg]
    ring
  have hp0 : p.coeff 0 = 1 := by
    let h : A' →+* Γ(G.objects.left, ⊤) := Polynomial.constantCoeff.comp eO.toRingHom
    have hd := map_det_one_add_smul h (-z) (by simp [h, z]) (Algebra.lmul A' B' (t a))
    rwa [← hlin] at hd
  let ε : B' →+* A' := bc.groupoid.identity.left.appTop.hom
  have hεs : ε.comp s = RingHom.id A' :=
    appTop_comp_of_section _ _ (congrArg Over.Hom.left bc.groupoid.source_identity)
  have hεt : ε.comp t = RingHom.id A' :=
    appTop_comp_of_section _ _ (congrArg Over.Hom.left bc.groupoid.target_identity)
  let e : B' →ₐ[A'] A' :=
    { __ := ε
      commutes' := fun r => RingHom.congr_fun hεs r }
  have hdiv : y ∣ d := by
    have hd := norm_dvd_of_retraction e (t y)
    have he : e (t y) = y := RingHom.congr_fun hεt y
    rwa [he] at hd
  have hpdiv : 1 - Polynomial.C x * Polynomial.X ∣ p := by
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨eO q, ?_⟩
    change eO d = _
    rw [hq, map_mul]
    congr 1
    simp only [y, map_sub, map_one, map_mul, a, z, RingEquiv.apply_symm_apply]
  obtain ⟨N, hmonic, hroot⟩ := Polynomial.monic_relation_of_divisor x p hp0 hpdiv
  apply RingHom.isIntegral_of_monic_polynomial_invariant _ _ x (p.reflect N) hmonic hroot
  change (p.reflect N).map G.source.left.appTop.hom =
    (p.reflect N).map G.target.left.appTop.hom
  rw [← Polynomial.reflect_map, ← Polynomial.reflect_map, hpInv]

end AlgebraicGeometry

end

end
