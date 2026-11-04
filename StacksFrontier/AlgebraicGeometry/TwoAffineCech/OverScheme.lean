module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.OpenLocus
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FGSubalgebraBaseChange
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ZeroSchemeIdeal
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology and base change for invertible modules on a family of two-affine schemes

Let `k` be a field and `X` a proper `k`-scheme covered by two affine opens. For a `k`-scheme `T`
and an invertible module `L` on `X_T = X ×_k T`, the locus of points `t ∈ T` at which
`H¹(X_t, L_t) = 0` and `dim H⁰(X_t, L_t) = r` is open, and the fibre Euler characteristic
`t ↦ dim H⁰(X_t, L_t) - dim H¹(X_t, L_t)` is locally constant.

The proof is local on `T`. Over an affine open `Spec A ⊆ T` the module descends to a finitely
generated, hence Noetherian, `k`-subalgebra `A' ⊆ A` (Tag 0B8W (2)), where the two-term Čech
complex has a finite projective model; the fibre cohomology is compatible with base change, so the
loci over `Spec A` are inverse images of the loci over `Spec A'`.

## Main results

* `Stacks.TwoAffineCech.isOpen_setOf_fibreCohomology_of_isPullback`.
* `Stacks.TwoAffineCech.isLocallyConstant_fibreEuler_of_isPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.FibreCohomology

universe u

namespace Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- An invertible module in the spelling of the ampleness theory is invertible in the spelling of
Tag 0B8W. -/
theorem isInvertible_of_isInvertibleModule {Y : Scheme.{u}} (M : Y.Modules)
    [h : Stacks.Ample.IsInvertibleModule Y M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M := h

/-! ### The affine case over a finitely generated algebra -/

section FG

variable {A : Type u} [CommRing A] [Algebra k A]

include hU hUaff in
/-- **The affine case.** Over `Spec A` for a `k`-algebra `A`, the fibre locus with vanishing `H¹`
and `r`-dimensional `H⁰` of an invertible module on `X_A` is open. -/
theorem isOpen_setOf_fibreCohomology_affine
    (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).Modules)
    [Stacks.Ample.IsInvertibleModule _ L] (r : ℕ) :
    IsOpen {x : Spec (.of A) |
      Module.finrank ((Spec (.of A)).residueField x)
          (fibreCohomology (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX) L x 1)
        = 0 ∧
      Module.finrank ((Spec (.of A)).residueField x)
          (fibreCohomology (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX) L x 0)
        = r} := by
  have : CompactSpace X := ⟨QuasiCompact.isCompact_preimage (f := fX) _ isOpen_univ isCompact_univ⟩
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  obtain ⟨A', hA', L', hL', p, hp₁, hp₂, ⟨e⟩⟩ :=
    Stacks.FGSubalgebraLimit.exists_fg_subalgebra_isInvertible_pullback_iso X fX L
      (isInvertible_of_isInvertibleModule L)
  set fA := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX
  set fA' := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX
  set pA' := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX
  have hsqA' : IsPullback fA' pA' (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX :=
    IsPullback.of_hasPullback _ _
  have hcomp : Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A')) =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    rw [← Spec.map_comp]; rfl
  have hbig : IsPullback (p ≫ pA') fA fX
      (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A'))) := by
    rw [hp₂, hcomp]; exact (IsPullback.of_hasPullback _ _).flip
  have hsq : IsPullback p fA fA' (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom)) :=
    IsPullback.of_right hbig hp₁ hsqA'.flip
  have : IsProper fA' := MorphismProperty.of_isPullback hsqA'.flip inferInstance
  have : IsSeparated fA' := MorphismProperty.of_isPullback hsqA'.flip inferInstance
  have : IsAffineHom pA' := MorphismProperty.of_isPullback hsqA' (isAffineHom_of_isAffine _)
  have : Algebra.FiniteType k A' := (Subalgebra.fg_iff_finiteType _).1 hA'
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing k A'
  have : IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX) :=
    LocallyOfFiniteType.isLocallyNoetherian fA'
  have : L'.IsFinitePresentation := @Stacks.Divisors.isFinitePresentation_of_isInvertible _ L' hL'
  have : L'.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation L' inferInstance
  have : L'.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L').1
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L' :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L').mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L' hL')
  have : Flat fA' := MorphismProperty.of_isPullback hsqA'.flip inferInstance
  have hflat : IsFlatOver fA'.toLRSHom.toShHom L' :=
    AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree fA' L'
  have hU' : (⊤ : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX).Opens) =
      ⨆ i, pA' ⁻¹ᵁ U i := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]
  have hUaff' : ∀ i, IsAffineOpen (pA' ⁻¹ᵁ U i) := fun i => (hUaff i).preimage pA'
  have hO := isOpen_setOf_fibreCohomology fA' (fun i => pA' ⁻¹ᵁ U i) L' hU' hUaff' hflat r
  have hL : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have htr (x : Spec (.of A)) (n : ℕ) :=
    finrank_fibreCohomology_eq_of_isPullback fA' L' p fA _ hsq L e x n
  have : {x : Spec (.of A) |
      Module.finrank ((Spec (.of A)).residueField x) (fibreCohomology fA L x 1) = 0 ∧
      Module.finrank ((Spec (.of A)).residueField x) (fibreCohomology fA L x 0) = r} =
      (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom)).base ⁻¹'
        {x' : Spec (.of A') |
          Module.finrank ((Spec (.of A')).residueField x') (fibreCohomology fA' L' x' 1) = 0 ∧
          Module.finrank ((Spec (.of A')).residueField x') (fibreCohomology fA' L' x' 0) = r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [htr x 1, htr x 0]
  rw [this]
  exact hO.preimage (Spec.map _).continuous

include hU hUaff in
/-- **The affine case of local constancy.** Over `Spec A` for a `k`-algebra `A`, the fibre Euler
characteristic of an invertible module on `X_A` is locally constant. -/
@[ega "III 7.9.4" "special case"]
theorem isLocallyConstant_fibreEuler_affine
    (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX).Modules)
    [Stacks.Ample.IsInvertibleModule _ L] :
    IsLocallyConstant fun x : Spec (.of A) =>
      (Module.finrank ((Spec (.of A)).residueField x)
          (fibreCohomology (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX) L x 0)
        : ℤ) -
      Module.finrank ((Spec (.of A)).residueField x)
          (fibreCohomology (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX)
            L x 1) := by
  have : CompactSpace X := ⟨QuasiCompact.isCompact_preimage (f := fX) _ isOpen_univ isCompact_univ⟩
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  obtain ⟨A', hA', L', hL', p, hp₁, hp₂, ⟨e⟩⟩ :=
    Stacks.FGSubalgebraLimit.exists_fg_subalgebra_isInvertible_pullback_iso X fX L
      (isInvertible_of_isInvertibleModule L)
  set fA := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) fX
  set fA' := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX
  set pA' := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX
  have hsqA' : IsPullback fA' pA' (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX :=
    IsPullback.of_hasPullback _ _
  have hcomp : Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A')) =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    rw [← Spec.map_comp]; rfl
  have hbig : IsPullback (p ≫ pA') fA fX
      (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A'))) := by
    rw [hp₂, hcomp]; exact (IsPullback.of_hasPullback _ _).flip
  have hsq : IsPullback p fA fA' (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom)) :=
    IsPullback.of_right hbig hp₁ hsqA'.flip
  have : IsProper fA' := MorphismProperty.of_isPullback hsqA'.flip inferInstance
  have : IsSeparated fA' := MorphismProperty.of_isPullback hsqA'.flip inferInstance
  have : IsAffineHom pA' := MorphismProperty.of_isPullback hsqA' (isAffineHom_of_isAffine _)
  have : Algebra.FiniteType k A' := (Subalgebra.fg_iff_finiteType _).1 hA'
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing k A'
  have : IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX) :=
    LocallyOfFiniteType.isLocallyNoetherian fA'
  have : L'.IsFinitePresentation := @Stacks.Divisors.isFinitePresentation_of_isInvertible _ L' hL'
  have : L'.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation L' inferInstance
  have : L'.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L').1
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L' :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L').mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L' hL')
  have : Flat fA' := MorphismProperty.of_isPullback hsqA'.flip inferInstance
  have hflat : IsFlatOver fA'.toLRSHom.toShHom L' :=
    AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree fA' L'
  have hU' : (⊤ : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) fX).Opens) =
      ⨆ i, pA' ⁻¹ᵁ U i := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]
  have hUaff' : ∀ i, IsAffineOpen (pA' ⁻¹ᵁ U i) := fun i => (hUaff i).preimage pA'
  have hO := isLocallyConstant_fibreCohomology_euler fA' (fun i => pA' ⁻¹ᵁ U i) L' hU' hUaff' hflat
  have hL : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have htr (x : Spec (.of A)) (n : ℕ) :=
    finrank_fibreCohomology_eq_of_isPullback fA' L' p fA _ hsq L e x n
  have : (fun x : Spec (.of A) =>
      (Module.finrank ((Spec (.of A)).residueField x) (fibreCohomology fA L x 0) : ℤ) -
      Module.finrank ((Spec (.of A)).residueField x) (fibreCohomology fA L x 1)) =
      (fun x' : Spec (.of A') =>
        (Module.finrank ((Spec (.of A')).residueField x') (fibreCohomology fA' L' x' 0) : ℤ) -
        Module.finrank ((Spec (.of A')).residueField x') (fibreCohomology fA' L' x' 1)) ∘
        (Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom)).base := by
    funext x
    simp only [Function.comp_apply]
    rw [htr x 1, htr x 0]
  rw [this]
  exact hO.comp_continuous (Spec.map _).continuous

end FG

/-! ### An arbitrary base -/

section General

variable {T XT : Scheme.{u}} (a : T ⟶ Spec (.of k)) (gT : XT ⟶ X) (fT : XT ⟶ T)
  (hT : IsPullback gT fT fX a) (L : XT.Modules) [Stacks.Ample.IsInvertibleModule XT L]

include hT in
/-- The base change `fT : XT ⟶ T` of the proper morphism `fX` along `a : T ⟶ Spec k` is proper. -/
theorem isProper_of_isPullback : IsProper fT := MorphismProperty.of_isPullback hT inferInstance

omit [IsProper fX] in
include hT in
/-- The local chart used to reduce to the affine case: an open immersion from an affine scheme
through every point, and the base change of the family to it. -/
theorem exists_affineChart (x : T) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R) (ι : Spec (.of R) ⟶ T)
      (_ : IsOpenImmersion ι) (y : Spec (.of R))
      (q : pullback (Spec.map (CommRingCat.ofHom (algebraMap k R))) fX ⟶ XT),
      ι y = x ∧ IsPullback q (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) fX)
        fT ι := by
  obtain ⟨R', ι, hι, y, hy⟩ := Scheme.exists_Spec_apply_eq x
  let R : Type u := R'
  let ι' : Spec (.of R) ⟶ T := ι
  let φ : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (ι' ≫ a)
  let : Algebra k R := φ.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap k R)) = ι' ≫ a := by
    show Spec.map (CommRingCat.ofHom φ.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let q := hT.lift (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k R))) fX)
    (pullback.fst _ fX ≫ ι') (by rw [← pullback.condition, hmap, Category.assoc])
  refine ⟨R, inferInstance, this, ι', hι, y, q, hy, ?_⟩
  have hbig : IsPullback (q ≫ gT)
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) fX) fX (ι' ≫ a) := by
    rw [hT.lift_fst, ← hmap]
    exact (IsPullback.of_hasPullback _ _).flip
  exact IsPullback.of_right hbig (hT.lift_snd _ _ _) hT

include hU hUaff hT in
/-- **The fibre locus with vanishing `H¹` and `r`-dimensional `H⁰` is open**, for an invertible
module on any base change of `X`. -/
theorem isOpen_setOf_fibreCohomology_of_isPullback (r : ℕ) :
    IsOpen {t : T |
      Module.finrank (T.residueField t) (fibreCohomology fT L t 1) = 0 ∧
      Module.finrank (T.residueField t) (fibreCohomology fT L t 0) = r} := by
  have : IsProper fT := isProper_of_isPullback fX a gT fT hT
  have : L.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨R, _, _, ι, hι, y, q, hy, hsq⟩ := exists_affineChart fX a gT fT hT x
  have hO := isOpen_setOf_fibreCohomology_affine fX U hU hUaff (A := R)
    ((Scheme.Modules.pullback q).obj L) r
  set S := {t : T |
      Module.finrank (T.residueField t) (fibreCohomology fT L t 1) = 0 ∧
      Module.finrank (T.residueField t) (fibreCohomology fT L t 0) = r}
  have heq : ι.base ⁻¹' S = {z : Spec (.of R) |
      Module.finrank ((Spec (.of R)).residueField z)
          (fibreCohomology (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) fX)
            ((Scheme.Modules.pullback q).obj L) z 1) = 0 ∧
      Module.finrank ((Spec (.of R)).residueField z)
          (fibreCohomology (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) fX)
            ((Scheme.Modules.pullback q).obj L) z 0) = r} := by
    ext z
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq]
    rw [finrank_fibreCohomology_eq_of_isPullback fT L q _ ι hsq _ (Iso.refl _) z 1,
      finrank_fibreCohomology_eq_of_isPullback fT L q _ ι hsq _ (Iso.refl _) z 0]
  refine ⟨ι.base '' (ι.base ⁻¹' S), Set.image_preimage_subset _ _, ?_, ⟨y, ?_, hy⟩⟩
  · exact ι.isOpenEmbedding.isOpenMap _ (by rwa [heq])
  · rwa [Set.mem_preimage, hy]

include hU hUaff hT in
/-- **The fibre Euler characteristic is locally constant**, for an invertible module on any base
change of `X`. -/
theorem isLocallyConstant_fibreEuler_of_isPullback :
    IsLocallyConstant fun t : T =>
      (Module.finrank (T.residueField t) (fibreCohomology fT L t 0) : ℤ) -
        Module.finrank (T.residueField t) (fibreCohomology fT L t 1) := by
  have : IsProper fT := isProper_of_isPullback fX a gT fT hT
  have : L.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨R, _, _, ι, hι, y, q, hy, hsq⟩ := exists_affineChart fX a gT fT hT x
  have hO := isLocallyConstant_fibreEuler_affine fX U hU hUaff (A := R)
    ((Scheme.Modules.pullback q).obj L)
  obtain ⟨V, hV, hyV, hVc⟩ := (IsLocallyConstant.iff_exists_open _).mp hO y
  refine ⟨ι.base '' V, ι.isOpenEmbedding.isOpenMap _ hV, ⟨y, hyV, hy⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have h := hVc z hz
  rwa [finrank_fibreCohomology_eq_of_isPullback fT L q _ ι hsq _ (Iso.refl _) z 1,
    finrank_fibreCohomology_eq_of_isPullback fT L q _ ι hsq _ (Iso.refl _) z 0,
    finrank_fibreCohomology_eq_of_isPullback fT L q _ ι hsq _ (Iso.refl _) y 1,
    finrank_fibreCohomology_eq_of_isPullback fT L q _ ι hsq _ (Iso.refl _) y 0, hy] at h

end General

end Stacks.TwoAffineCech
