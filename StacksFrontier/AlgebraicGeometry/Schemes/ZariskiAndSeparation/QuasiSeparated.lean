module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute

/-!
# Characterizations of quasi-separated morphisms

A morphism of schemes is quasi-separated exactly when the intersection of two affine opens of
the source lying over a common affine open of the base is quasi-compact, equivalently a finite
union of affine opens; and it is enough to check this on one affine open covering of the base
together with one affine open covering of each preimage.

## Main results

* `AlgebraicGeometry.quasiSeparated_iff_isCompact_inf` and
  `AlgebraicGeometry.quasiSeparated_iff_finite_iSup_affineOpens`: **Stacks 01KO**, the
  equivalence of conditions (1) and (2), with the intersection expressed both as a compact set
  and, as in the source, as a finite union of affine opens.
* `AlgebraicGeometry.quasiSeparated_of_openCover` and
  `AlgebraicGeometry.quasiSeparated_of_isOpenCover`: **Stacks 01KO**, condition (3) implies
  condition (1), stated for `Scheme.OpenCover`s and for families of opens.
* `AlgebraicGeometry.exists_isOpenCover_of_quasiSeparated`: **Stacks 01KO**, condition (1)
  implies condition (3).
* `AlgebraicGeometry.quasiSeparatedSpace_opens_iff`: an open subscheme is a quasi-separated
  space exactly when the affine opens it contains meet in compact sets.

## Implementation notes

Condition (1) of the source is Mathlib's definition `AlgebraicGeometry.QuasiSeparated`, the
diagonal being quasi-compact. No `List.TFAE` statement is given: condition (3) quantifies over
index types, so a disjunct for it would have to pin their universes, and the three implications
are stated separately instead.

The `HasAffineProperty` lemmas are applied with their instance argument supplied by name
(`instHasAffinePropertyQuasiSeparated…`, `instHasAffinePropertyQuasiCompact…`), because at this
Mathlib pin those instances are not found by instance synthesis; the same workaround is used in
`StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RelativeProjFiniteType`.

The step of the source's proof that the fibre products `V_j ×_{U_i} V_{j'}` form an affine open
covering of `X ×_S X` (Stacks 01JS) is already carried out inside
`AlgebraicGeometry.HasAffineProperty.diagonal_of_openCover`.

## References

* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe w v u

/-! ### Transporting opens along the inclusion of an open subscheme -/

section Transport

variable {X : Scheme.{u}}

/-- An open contained in `W` is the image of its preimage in the open subscheme `W`. -/
private lemma ι_image_preimage_of_le {W U : X.Opens} (h : U ≤ W) : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]

/-- An open contained in `W` is affine exactly when its preimage in `W` is. -/
private lemma isAffineOpen_preimage_ι_iff {W U : X.Opens} (h : U ≤ W) :
    IsAffineOpen (W.ι ⁻¹ᵁ U) ↔ IsAffineOpen U := by
  rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι, ι_image_preimage_of_le h]

/-- Compactness of the intersection of two opens of an open subscheme is the same question as
compactness of the intersection of their images, the inclusion being an embedding. -/
private lemma isCompact_inf_image_iff (W : X.Opens) (A B : W.toScheme.Opens) :
    IsCompact ((A : Set W.toScheme) ∩ (B : Set W.toScheme)) ↔
      IsCompact (((W.ι ''ᵁ A) ⊓ (W.ι ''ᵁ B) : X.Opens) : Set X) := by
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff,
    Set.image_inter W.ι.isOpenEmbedding.injective]
  rfl

/-- For opens `U`, `V` contained in `W`, compactness of the intersection of their preimages in
`W` is the same as compactness of `U ⊓ V`. -/
private lemma isCompact_inf_preimage_iff {W U V : X.Opens} (hU : U ≤ W) (hV : V ≤ W) :
    IsCompact ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) ∩ (W.ι ⁻¹ᵁ V : W.toScheme.Opens) : Set W.toScheme) ↔
      IsCompact ((U ⊓ V : X.Opens) : Set X) := by
  rw [isCompact_inf_image_iff, ι_image_preimage_of_le hU, ι_image_preimage_of_le hV]

end Transport

/-- An open subscheme `W` of `X` is a quasi-separated space exactly when any two affine opens of
`X` contained in `W` meet in a compact set. -/
public theorem quasiSeparatedSpace_opens_iff {X : Scheme.{u}} (W : X.Opens) :
    QuasiSeparatedSpace W.toScheme ↔
      ∀ U ≤ W, ∀ V ≤ W, IsAffineOpen U → IsAffineOpen V →
        IsCompact ((U ⊓ V : X.Opens) : Set X) := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  constructor
  · intro H U hU V hV hUa hVa
    exact (isCompact_inf_preimage_iff hU hV).mp
      (H ⟨_, (isAffineOpen_preimage_ι_iff hU).mpr hUa⟩
         ⟨_, (isAffineOpen_preimage_ι_iff hV).mpr hVa⟩)
  · intro H A B
    exact (isCompact_inf_image_iff W A.1 B.1).mpr
      (H _ (W.ι_image_le A.1) _ (W.ι_image_le B.1) (A.2.image_of_isOpenImmersion _)
        (B.2.image_of_isOpenImmersion _))

/-- A morphism is quasi-separated exactly when the preimage of every affine open of the base is
a quasi-separated space. -/
public theorem quasiSeparated_iff_forall_affineOpens {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔ ∀ W : S.affineOpens, QuasiSeparatedSpace (f ⁻¹ᵁ W.1).toScheme :=
  @HasAffineProperty.iff_of_iSup_eq_top @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)
    instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
    _ _ _ _ id (iSup_affineOpens_eq_top S)

/-! ### Conditions (1) and (2) -/

/-- A morphism `f : X ⟶ S` is quasi-separated if and only if for every pair of affine opens `U`,
`V` of `X` which map into a common affine open `W` of `S`, the intersection `U ∩ V` is
quasi-compact. -/
@[stacks 01KO "conditions (1) and (2)"]
public theorem quasiSeparated_iff_isCompact_inf {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∀ (W : S.Opens), IsAffineOpen W → ∀ U ≤ f ⁻¹ᵁ W, ∀ V ≤ f ⁻¹ᵁ W,
        IsAffineOpen U → IsAffineOpen V → IsCompact ((U ⊓ V : X.Opens) : Set X) := by
  rw [quasiSeparated_iff_forall_affineOpens]
  simp only [quasiSeparatedSpace_opens_iff, Scheme.affineOpens, Subtype.forall,
    Set.mem_ofPred_eq]

/-- A morphism `f : X ⟶ S` is quasi-separated if and only if for every pair of affine opens `U`,
`V` of `X` which map into a common affine open of `S`, the intersection `U ∩ V` is a finite union
of affine opens of `X`. -/
@[stacks 01KO "condition (2), as a finite union of affine opens"]
public theorem quasiSeparated_iff_finite_iSup_affineOpens {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔
      ∀ (W : S.Opens), IsAffineOpen W → ∀ U ≤ f ⁻¹ᵁ W, ∀ V ≤ f ⁻¹ᵁ W,
        IsAffineOpen U → IsAffineOpen V →
        ∃ s : Set X.affineOpens, s.Finite ∧ (U ⊓ V : X.Opens) = ⨆ i ∈ s, (i : X.Opens) := by
  rw [quasiSeparated_iff_isCompact_inf]
  simp only [isCompact_iff_finite_and_eq_biUnion_affineOpens]

/-! ### Condition (3) -/

/-- Given an affine open covering `𝒰` of `S` and, for each `i`, an affine open covering `𝒱 i` of
`f ⁻¹ U i`, if every fibre product `V j ×_{U i} V k` is quasi-compact then `f` is
quasi-separated. -/
@[stacks 01KO "condition (3) implies (1)"]
public theorem quasiSeparated_of_openCover {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Scheme.OpenCover.{v} S) [∀ i, IsAffine (𝒰.X i)]
    (𝒱 : ∀ i, Scheme.OpenCover.{w} (pullback f (𝒰.f i))) [∀ i j, IsAffine ((𝒱 i).X j)]
    (h : ∀ i j k, CompactSpace (pullback ((𝒱 i).f j) ((𝒱 i).f k) : Scheme.{u})) :
    QuasiSeparated f := by
  rw [quasiSeparated_eq_diagonal_is_quasiCompact]
  exact @HasAffineProperty.diagonal_of_openCover @QuasiCompact _
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
    _ _ f 𝒰 _ 𝒱 _ h

/-- Given an affine open covering `S = ⋃ i, W i` and for each `i` an affine open covering
`f ⁻¹ (W i) = ⋃ j, V i j`, if each intersection `V i j ∩ V i k` is quasi-compact then `f` is
quasi-separated. -/
@[stacks 01KO "condition (3) implies (1), for families of opens"]
public theorem quasiSeparated_of_isOpenCover {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type*} (W : ι → S.Opens) (hW : IsOpenCover W) (hWaff : ∀ i, IsAffineOpen (W i))
    {κ : ι → Type*} (V : ∀ i, κ i → X.Opens) (hV : ∀ i, ⨆ j, V i j = f ⁻¹ᵁ W i)
    (hVaff : ∀ i j, IsAffineOpen (V i j))
    (hVcompact : ∀ i j k, IsCompact ((V i j ⊓ V i k : X.Opens) : Set X)) :
    QuasiSeparated f := by
  have hle : ∀ i j, V i j ≤ f ⁻¹ᵁ W i := fun i j ↦ (hV i) ▸ le_iSup (V i) j
  refine @HasAffineProperty.of_iSup_eq_top @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)
    instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
    _ _ f ι (fun i ↦ ⟨W i, hWaff i⟩) hW (fun i ↦ ?_)
  refine Scheme.quasiSeparatedSpace_of_isOpenCover
    (fun j ↦ (f ⁻¹ᵁ W i).ι ⁻¹ᵁ V i j) ?_ (fun j ↦ (isAffineOpen_preimage_ι_iff (hle i j)).mpr
      (hVaff i j)) (fun j k ↦ ?_)
  · refine IsOpenCover.mk ?_
    rw [← Scheme.Hom.preimage_iSup, hV i, Scheme.Opens.ι_preimage_self]
  · exact (isCompact_inf_preimage_iff (hle i j) (hle i k)).mpr (hVcompact i j k)

/-- A quasi-separated morphism admits an affine open covering of the base and an affine open
covering of each preimage whose pairwise intersections are quasi-compact; one may take all the
affine opens there are. -/
@[stacks 01KO "condition (1) implies (3)"]
public theorem exists_isOpenCover_of_quasiSeparated {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiSeparated f] :
    ∃ (ι : Type u) (W : ι → S.Opens), IsOpenCover W ∧ (∀ i, IsAffineOpen (W i)) ∧
      ∃ (κ : ι → Type u) (V : ∀ i, κ i → X.Opens),
        (∀ i, ⨆ j, V i j = f ⁻¹ᵁ W i) ∧ (∀ i j, IsAffineOpen (V i j)) ∧
        (∀ i j k, IsCompact ((V i j ⊓ V i k : X.Opens) : Set X)) := by
  refine ⟨S.affineOpens, fun i ↦ i.1, iSup_affineOpens_eq_top S, fun i ↦ i.2,
    fun i ↦ (f ⁻¹ᵁ (i : S.Opens)).toScheme.affineOpens,
    fun i j ↦ (f ⁻¹ᵁ (i : S.Opens)).ι ''ᵁ j.1, fun i ↦ ?_, fun i j ↦ ?_, fun i j k ↦ ?_⟩
  · rw [← Scheme.Hom.image_iSup, iSup_affineOpens_eq_top, Scheme.Opens.ι_image_top]
  · exact j.2.image_of_isOpenImmersion _
  · exact (quasiSeparated_iff_isCompact_inf f).mp ‹_› i.1 i.2 _
      (Scheme.Opens.ι_image_le _ _) _ (Scheme.Opens.ι_image_le _ _)
      (j.2.image_of_isOpenImmersion _) (k.2.image_of_isOpenImmersion _)

end AlgebraicGeometry

end
