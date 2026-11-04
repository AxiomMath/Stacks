module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorRestrictPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AzumayaRankCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.RankEtaleDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerEndAlgebra
public import StacksFrontier.AlgebraicGeometry.RingedSpaceModuleSpellings
public import StacksFrontier.CategoryTheory.Monoidal.RankOnePointImage

/-!
# The class of an Azumaya algebra of rank `d ^ 2` is annihilated by `d`

This file proves [Stacks, Tag 0A2L]: for a scheme `S` and an Azumaya `𝒪_S`-algebra `𝒜` whose
underlying sheaf of modules is finite locally free of rank `d ^ 2`, the class of `𝒜` in the
Brauer group `Br(S)` satisfies `[𝒜] ^ d = 1`.

The reduction `Stacks.EtaleCohomology.BrauerScheme.
brauerClass_pow_eq_one_of_isTrivialClass_natTensorPow` leaves one statement open: that the
`d`-fold tensor power `𝒜^{⊗ d}` has trivial Brauer class, i.e. is the endomorphism algebra of a
finite locally free sheaf of modules of positive rank. That is Saltman's construction, and this
file assembles it.

On a member `U_i` of a trivialising étale covering — one on which the matrix size is exactly `d`,
`Stacks.EtaleCohomology.BrauerScheme.exists_etaleCover_matrixAlgebra_of_rank` — the trivialisation
`𝒜|_{U_i} ≅ Mat_d(𝒪_{U_i})` reads Saltman's projector `altProjFree` as a point of `𝒜^{⊗ d}`,
`Stacks.EtaleCohomology.BrauerScheme.saltmanPoint`. Two trivialisations of the same algebra read
it as the *same* point (`curry'_altProjFree_comp_natTensorPowTrivIso_inv`), and restriction
carries the point of a trivialisation to the point of the restricted trivialisation
(`restrictPoint_saltmanPoint`), so the family of local points is a descent datum and
`AlgebraicGeometry.existsUnique_glue_point` glues it to a global point `p` of `𝒜^{⊗ d}`.

The subobject `𝓗 = p · 𝒜^{⊗ d}` — the image of left multiplication by `p` — is then the sheaf of
modules wanted. Locally it is the free sheaf of rank `d ^ d`: pullback commutes with the image
(`CategoryTheory.Mon.mapImageLeftMulIso`), the local point is Saltman's point, and the image of
left multiplication by Saltman's point is the free sheaf itself
(`CategoryTheory.MonoidalClosed.imageLeftMulCurry'Iso`), because the projector factors as a split
epimorphism followed by a split monomorphism. Finite local freeness of rank `d ^ d` therefore
descends (`isFiniteLocallyFreeOfRank_of_etale_cover`), which also gives the positive rank, and
the representation `𝒜^{⊗ d} ⟶ 𝓗om(𝓗, 𝓗)` is an isomorphism because it is so locally
(`CategoryTheory.MonoidalClosed.isIso_imageRep_curry'`) and isomorphy descends
(`isIso_of_isIso_algebraPullback_cover`).

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.isTrivialClass_natTensorPow_of_rank`: **the `d`-fold tensor
  power of an Azumaya algebra of rank `d ^ 2` has trivial Brauer class**, `d ≥ 1`.
* `Stacks.EtaleCohomology.BrauerScheme.brauerClass_pow_eq_one_of_rank`: **[Stacks, Tag 0A2L].**

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

/-- **Sheaves of `𝒪_S`-modules form an abelian category**, at the spelling `ModuleSheaf S` of
this namespace: this is `AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules` at the
structure sheaf `Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf`, which instance synthesis does
not reach on its own because `ModuleSheaf S` reduces to that spelling and not to the
`ringCatSheaf` one the global instances of
`Stacks.RingedSpaceModules` are stated at. It is what makes the images below exist. -/
local instance abelianModuleSheaf (S : Scheme.{u}) : Abelian (ModuleSheaf S) :=
  AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)

variable {S : Scheme.{u}}

/-- **The `(n+1)`-fold tensor power of an Azumaya `𝒪_S`-algebra whose underlying sheaf of modules
is finite locally free of rank `(n+1) ^ 2` has trivial Brauer class.** This is Saltman's
construction; see the module docstring. -/
theorem isTrivialClass_natTensorPow_of_rank {A : AlgebraSheaf S} (hA : IsAzumaya A) {n : ℕ}
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) A.X ((n + 1) ^ 2)) :
    IsTrivialClass (Stacks.TensorPowers.natTensorPow A (n + 1)) := by
  classical
  obtain ⟨𝒰, htriv⟩ := exists_etaleCover_matrixAlgebra_of_rank hA hrank
  set P := Stacks.TensorPowers.natTensorPow A (n + 1) with hP
  have M : ∀ i, (algebraPullback (𝒰.f i)).obj A ≅ matrixAlgebra (𝒰.X i) (n + 1) :=
    fun i => (htriv i).some
  have hPrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S)
      (P).X (((n + 1) ^ 2) ^ (n + 1)) :=
    isFiniteLocallyFreeOfRank_natTensorPow_X A hrank (n + 1)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S)
      (P).X :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (P).X (((n + 1) ^ 2) ^ (n + 1))
  -- the local Saltman points glue
  have hq : ∀ i j, AlgebraicGeometry.restrictPoint
        (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f i)
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl (saltmanPoint (𝒰.f i) (M i))
      = AlgebraicGeometry.restrictPoint
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f j)
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm
        (saltmanPoint (𝒰.f j) (M j)) := fun i j =>
    (restrictPoint_saltmanPoint _ _ _ _ (M i)).trans
      ((saltmanPoint_eq _ _ _).trans (restrictPoint_saltmanPoint _ _ _ _ (M j)).symm)
  -- quasi-coherence of the tensor power, from its local freeness
  have hlf : SheafOfModules.IsLocallyFree (P).X :=
    inferInstance
  have hqc : SheafOfModules.IsQuasicoherent (P).X :=
    inferInstance
  obtain ⟨p, hp, -⟩ := @AlgebraicGeometry.existsUnique_glue_point S
    (P).X hqc 𝒰
    (fun i => saltmanPoint (𝒰.f i) (M i)) hq
  -- the image of left multiplication by the glued point
  have : (image (Mon.leftMul (P) p)).IsQuasicoherent :=
    @AlgebraicGeometry.isQuasicoherent_image S _ _ _ hqc hqc
  set H := image (Mon.leftMul P p) with hH
  -- pullback along the étale cover members preserves finite limits and colimits
  have hE : ∀ i, AlgebraicGeometry.Etale (𝒰.f i) := (etaleCover_spec 𝒰).2
  have : ∀ i, PreservesFiniteLimits (modulePullback (𝒰.f i)) := fun i =>
    have := hE i
    preservesFiniteLimits_modulePullback (𝒰.f i)
  have : ∀ i, PreservesFiniteColimits (modulePullback (𝒰.f i)) := fun i =>
    have := hE i
    preservesFiniteColimits_modulePullback (𝒰.f i)
  -- it is locally the free sheaf of rank `(n+1) ^ (n+1)`
  have hmp : ∀ i, Mon.mapPoint (modulePullback (𝒰.f i))
        (C := P) p ≫
        (pullbackTrivIso (𝒰.f i) (M i)).hom.hom
      = MonoidalClosed.curry' (altProjFree (𝒰.X i) (n + 1)) := fun i =>
    (congrArg (fun z => z ≫ (pullbackTrivIso (𝒰.f i) (M i)).hom.hom) (hp i)).trans
      (saltmanPoint_comp_pullbackTrivIso_hom (𝒰.f i) (M i))
  have hlocal : ∀ i, Nonempty ((modulePullback (𝒰.f i)).obj
        (image (Mon.leftMul (P) p)) ≅
      freeModule (𝒰.X i) (ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)))) := by
    intro i
    exact ⟨Mon.mapImageLeftMulIso (modulePullback (𝒰.f i)) p ≪≫
      Mon.imageIsoLeft (pullbackTrivIso (𝒰.f i) (M i)) (hmp i) ≪≫
      (MonoidalClosed.imageLeftMulCurry'Iso (altPointFree (𝒰.X i) (n + 1))
        (altCovecFree (𝒰.X i) (n + 1)) (altCoordPointFree (𝒰.X i) (n + 1))
        (altCoordCovecFree (𝒰.X i) (n + 1))
        (altPointFree_comp_altCoordCovecFree (𝒰.X i) (n + 1))
        (altCoordPointFree_comp_altCovecFree (𝒰.X i) (n + 1))).symm⟩
  have hHrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S)
      (image (Mon.leftMul (P) p))
      ((n + 1) ^ (n + 1)) :=
    isFiniteLocallyFreeOfRank_of_etale_cover inferInstance 𝒰 fun i =>
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hlocal i).some.symm
        (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv _
          ((n + 1) ^ (n + 1))
          (Equiv.ulift.trans (Fintype.equivFinOfCardEq (by simp))))
  have hHfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S)
      (image (Mon.leftMul (P) p)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (image (Mon.leftMul (P) p)) ((n + 1) ^ (n + 1))
  have hHpos : HasPositiveRank
      (image (Mon.leftMul (P) p)) :=
    hasPositiveRank_of_rank (by positivity) hHrank
  -- the representation is an isomorphism, because it is so locally
  have : HasRightDual
      (image (Mon.leftMul (P) p)) :=
    (nonempty_hasRightDual_of_isFiniteLocallyFree hHfree).some
  have hiso : IsIso (Mon.imageRep (P) p) := by
    refine isIso_of_isIso_algebraPullback_cover 𝒰
      (Mon.imageRep (P) p) fun i => ?_
    refine (Mon.isIso_mapMon_imageRep_iff
      (C := P) (modulePullback (𝒰.f i)) p).2 ?_
    have hD : IsIso (Mon.imageRep
        (MonoidalClosed.internalEnd
          (freeModule (𝒰.X i) (ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)))))
        (MonoidalClosed.curry' (altProjFree (𝒰.X i) (n + 1)))) :=
      MonoidalClosed.isIso_imageRep_curry' (altPointFree (𝒰.X i) (n + 1))
        (altCovecFree (𝒰.X i) (n + 1)) (altCoordPointFree (𝒰.X i) (n + 1))
        (altCoordCovecFree (𝒰.X i) (n + 1))
        (altPointFree_comp_altCoordCovecFree (𝒰.X i) (n + 1))
        (altCoordPointFree_comp_altCovecFree (𝒰.X i) (n + 1))
    have hcomp : IsIso ((pullbackTrivIso (𝒰.f i) (M i)).hom ≫
        Mon.imageRep (MonoidalClosed.internalEnd
            (freeModule (𝒰.X i) (ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)))))
          (MonoidalClosed.curry' (altProjFree (𝒰.X i) (n + 1)))) := inferInstance
    have : IsIso (Mon.imageRep ((algebraPullback (𝒰.f i)).obj
          (P))
          (Mon.mapPoint (modulePullback (𝒰.f i))
            (C := P) p) ≫
        (MonoidalClosed.internalEndCongr
          (Mon.imageIsoLeft (pullbackTrivIso (𝒰.f i) (M i)) (hmp i))).hom) :=
      Eq.mp (congrArg IsIso
        (Mon.imageRep_naturality (pullbackTrivIso (𝒰.f i) (M i)) (hmp i))) hcomp
    exact IsIso.of_isIso_comp_right _
      (MonoidalClosed.internalEndCongr
        (Mon.imageIsoLeft (pullbackTrivIso (𝒰.f i) (M i)) (hmp i))).hom
  exact ⟨image (Mon.leftMul (P) p), hHfree, hHpos,
    ⟨asIso (Mon.imageRep (P) p)⟩⟩

/-- **The class in `Br(S)` of an Azumaya `𝒪_S`-algebra whose underlying sheaf of modules is
finite locally free of rank `d ^ 2` is annihilated by `d`.**

This is [Stacks, Tag 0A2L]. The case `d = 0` is `pow_zero`; for `d ≥ 1` the reduction
`Stacks.EtaleCohomology.BrauerScheme.brauerClass_pow_eq_one_of_isTrivialClass_natTensorPow`
leaves exactly Saltman's construction,
`Stacks.EtaleCohomology.BrauerScheme.isTrivialClass_natTensorPow_of_rank`. -/
@[stacks 0A2L]
theorem brauerClass_pow_eq_one_of_rank (A : Azumaya S) {d : ℕ}
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) A.1.X (d ^ 2)) :
    brauerClass A ^ d = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pow_zero]
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos hd).symm⟩
  exact brauerClass_pow_eq_one_of_isTrivialClass_natTensorPow A (n + 1)
    (isTrivialClass_natTensorPow_of_rank A.2 hrank)

end Stacks.EtaleCohomology.BrauerScheme

end

end
