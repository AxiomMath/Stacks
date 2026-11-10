module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.NormalClosure
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.Nagata.Shrink
public import StacksFrontier.RingTheory.Regular.SingularLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The regular locus of a one-dimensional Nagata scheme is open, with discrete complement

Let `X` be a reduced Nagata scheme with `topologicalKrullDim X = 1`.  Then the regular locus
of `X` is open, every point outside it is closed, and the singular locus carries the discrete
induced topology.  These are the topological inputs to
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2).

## Main results

* `isJ2_of_isNagataRing_of_krullDimLE_one`: a Nagata ring of Krull dimension at most one is
  J-2, hence J-1, so its regular locus is open in its spectrum.
* `isRegularLocalRing_localization_primeIdealOf_iff` identifies the ring-theoretic and
  scheme-theoretic descriptions of the regular locus over an affine open.
* `isOpen_regularLocus` and `discreteTopology_singularLocus` are the two conclusions.
* `isClosed_singleton_of_not_mem_regularLocus`: a singular point of a reduced scheme of
  dimension at most one is a closed point.

## Implementation notes

Openness is proved locally rather than through a J-2 condition on the scheme: for each point
one takes a Nagata affine open neighbourhood, notes that its ring of sections has Krull
dimension at most one (because the dimension of a subspace does not exceed that of the
ambient space, and the spectrum of the sections is homeomorphic to the affine open), and
transports the ring-theoretic openness along the homeomorphism.  The stalk at a point of an
affine open is the localization of the sections at the corresponding prime
(`IsAffineOpen.isLocalization_stalk`), which is what identifies the two regular loci.

Discreteness then follows from finiteness of the singular locus on each affine open: the
singular locus is closed, a Noetherian sober space decomposes a closed set into finitely many
irreducible closed pieces, and each piece is a single point because its generic point is a
singular point and so closed.

The scheme-theoretic hypotheses are carried as plain arguments rather than as instances.

## References

* [Stacks Project, Section 33.41 (Tag 0C1Q)](https://stacks.math.columbia.edu/tag/0C1Q)
* [Stacks Project, Tag 07PJ](https://stacks.math.columbia.edu/tag/07PJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

/-! ### The ring-theoretic input -/

/-- A regular ring is J-0: its regular locus is everything. -/
public theorem isJ0_of_isRegularRing (R : Type u) [CommRing R] [IsRegularRing R]
    [Nontrivial R] : IsJ0 R :=
  ⟨Set.univ, isOpen_univ, Set.univ_nonempty,
    fun p _ => IsRegularRing.isRegularLocalRing_localization p.asIdeal⟩

/-- A Nagata ring of Krull dimension at most one is J-2.

Alias of `_root_.isJ2_of_isNagataRing_of_krullDimLE_one`. -/
public alias isJ2_of_isNagataRing_of_krullDimLE_one :=
  _root_.isJ2_of_isNagataRing_of_krullDimLE_one

/-! ### From the ring-theoretic regular locus to the scheme-theoretic one -/

/-- A point of an affine open is regular exactly when the localization of the ring of sections
at the corresponding prime is a regular local ring: the two descriptions of the regular locus
agree. -/
public theorem isRegularLocalRing_localization_primeIdealOf_iff (X : Scheme.{u})
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.val) :
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) ↔
      x ∈ regularLocus X := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let _ := U.2.isLocalization_stalk ⟨x, hxU⟩
  have e := (IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)
    (X.presheaf.stalk x)).toRingEquiv
  exact ⟨fun h => @IsRegularLocalRing.of_ringEquiv _ _ h _ _ e,
    fun h => @IsRegularLocalRing.of_ringEquiv _ _ h _ _ e.symm⟩

/-- If the ring of sections of an affine open is J-1, the regular locus of the scheme is open
over that affine open. -/
public theorem isOpen_regularLocus_inter_affineOpen (X : Scheme.{u}) (U : X.affineOpens)
    (hJ : IsJ1 Γ(X, U.val)) : IsOpen (regularLocus X ∩ (U.val : Set X)) := by
  have hpre : (Subtype.val : U.val → X) ⁻¹' regularLocus X =
      (fun y : U.val => U.2.primeIdealOf y) ⁻¹'
        {p : PrimeSpectrum Γ(X, U.val) |
          IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
    ext y
    exact (isRegularLocalRing_localization_primeIdealOf_iff X U y.1 y.2).symm
  have hopen : IsOpen ((Subtype.val : U.val → X) ⁻¹' regularLocus X) := by
    rw [hpre]
    exact hJ.preimage U.2.isoSpec.hom.base.hom.continuous
  have hset : regularLocus X ∩ (U.val : Set X) =
      (Subtype.val : U.val → X) '' ((Subtype.val : U.val → X) ⁻¹' regularLocus X) := by
    rw [Set.inter_comm]
    exact (Subtype.image_preimage_coe _ _).symm
  rw [hset]
  exact U.val.isOpen.isOpenMap_subtype_val _ hopen

/-! ### Openness of the regular locus -/

/-- The ring of sections of an affine open of a one-dimensional Nagata scheme has Krull
dimension at most one. -/
public theorem ringKrullDim_affineOpen_le_one (X : Scheme.{u}) (U : X.affineOpens)
    (hdim : topologicalKrullDim X = 1) : ringKrullDim Γ(X, U.val) ≤ 1 := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    U.2.isoSpec.hom.homeomorph.isHomeomorph).symm.le.trans
      ((topologicalKrullDim_subspace_le X U.val).trans hdim.le)

/-- **The regular locus of a reduced one-dimensional Nagata scheme is open.** -/
@[ega "IV 7.8.3" "(iv), special case"]
public theorem isOpen_regularLocus (X : Scheme.{u}) (hX : IsNagataScheme X)
    (hdim : topologicalKrullDim X = 1) : IsOpen (regularLocus X) := by
  have hJ1 : ∀ x : X, IsJ1 Γ(X, ((hX x).choose : X.affineOpens).val) := by
    intro x
    have _ : Ring.KrullDimLE 1 Γ(X, ((hX x).choose : X.affineOpens).val) :=
      Ring.krullDimLE_iff.mpr (ringKrullDim_affineOpen_le_one X (hX x).choose hdim)
    exact isJ2_of_isNagataRing_of_krullDimLE_one _ (hX x).choose_spec.2 _
  have hcover : regularLocus X =
      ⋃ x : X, regularLocus X ∩ ((((hX x).choose : X.affineOpens).val : X.Opens) : Set X) := by
    refine Set.eq_of_subset_of_subset (fun z hz => ?_)
      (Set.iUnion_subset fun _ => Set.inter_subset_left)
    exact Set.mem_iUnion.mpr ⟨z, hz, (hX z).choose_spec.1⟩
  rw [hcover]
  exact isOpen_iUnion fun x => isOpen_regularLocus_inter_affineOpen X (hX x).choose (hJ1 x)

/-! ### Discreteness of the singular locus -/

/-- Every generic point of a reduced scheme is a regular point. -/
@[ega "IV 6.13.4" "partial"]
public theorem mem_regularLocus_of_mem_genericPoints (X : Scheme.{u}) [IsReduced X]
    (x : X) (hx : x ∈ genericPoints X) : x ∈ regularLocus X := by
  change IsRegularLocalRing (X.presheaf.stalk x)
  let _ : Field (X.presheaf.stalk x) :=
    (AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents X x hx).toField
  infer_instance

/-- Every singular point of a reduced scheme of dimension at most one is a closed point. -/
public theorem isClosed_singleton_of_not_mem_regularLocus (X : Scheme.{u}) [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : x ∉ regularLocus X) :
    IsClosed ({x} : Set X) := by
  let cl (z : X) : IrreducibleCloseds X :=
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  let C := cl x
  have hxGeneric : x ∉ genericPoints X := fun hxg =>
    hx (mem_regularLocus_of_mem_genericPoints X x hxg)
  have hCnotMax : ¬ IsMax C := by
    intro hmax
    have hcomponent : closure ({x} : Set X) ∈ irreducibleComponents X := by
      refine ⟨isIrreducible_singleton.closure, ?_⟩
      intro s hs hxs
      exact subset_closure.trans (hmax (hxs.trans subset_closure :
        C ≤ (⟨closure s, hs.closure, isClosed_closure⟩ : IrreducibleCloseds X)))
    let η := genericPoints.ofComponent ⟨closure ({x} : Set X), hcomponent⟩
    have hη : IsGenericPoint η.1 (closure ({x} : Set X)) :=
      genericPoints.isGenericPoint_ofComponent _
    have hxη : IsGenericPoint x (closure ({x} : Set X)) := isGenericPoint_closure
    exact hxGeneric ((hη.eq hxη) ▸ η.2)
  have hCmin : IsMin C := by
    have hdim' : Order.krullDim (IrreducibleCloseds X) ≤ 1 := by
      simpa [topologicalKrullDim] using hdim
    exact (Order.krullDim_le_one_iff.mp hdim' C).resolve_right hCnotMax
  apply isClosed_of_closure_subset
  intro y hy
  have hle : closure ({y} : Set X) ⊆ closure ({x} : Set X) :=
    closure_minimal (fun z hz => (Set.mem_singleton_iff.mp hz) ▸ hy) isClosed_closure
  have heq : cl y = C := hCmin.eq_of_le hle
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hyx : y ⤳ x := specializes_iff_closure_subset.mpr
    (congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) heq).ge
  exact Set.mem_singleton_iff.mpr ((hxy.antisymm hyx).eq.symm)

/-- An affine open of a reduced one-dimensional Nagata scheme contains only finitely many
singular points. -/
public theorem finite_singularLocus_inter_affineOpen (X : Scheme.{u}) [IsReduced X]
    (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ((Subtype.val : V → X) ⁻¹' (regularLocus X)ᶜ).Finite := by
  have hLN : IsLocallyNoetherian X :=
    (isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme X).mp hX |>.1
  have hNR : IsNoetherianRing Γ(X, V) :=
    IsLocallyNoetherian.component_noetherian (⟨V, hV⟩ : X.affineOpens)
  have hNS : NoetherianSpace ↥V := AlgebraicGeometry.noetherianSpace_of_isAffineOpen V hV
  have hQS : QuasiSober ↥V := V.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  have hSclosed : IsClosed ((Subtype.val : V → X) ⁻¹' (regularLocus X)ᶜ) :=
    IsClosed.preimage continuous_subtype_val (isOpen_regularLocus X hX hdim).isClosed_compl
  obtain ⟨F, hFfin, hFclosed, hFirr, hFcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hSclosed
  have hFfinite : ∀ T ∈ F, T.Finite := by
    intro T hT
    obtain ⟨η, hη⟩ := QuasiSober.sober (hFirr T hT) (hFclosed T hT)
    have hηS : η ∈ (Subtype.val : V → X) ⁻¹' (regularLocus X)ᶜ := by
      rw [hFcover]
      exact Set.mem_sUnion.mpr ⟨T, hT, hη.mem⟩
    have hηclosed : IsClosed ({η} : Set V) := by
      rw [show ({η} : Set V) = Subtype.val ⁻¹' ({η.1} : Set X) by
        ext z
        exact ⟨congrArg Subtype.val, Subtype.ext⟩]
      exact (isClosed_singleton_of_not_mem_regularLocus X hdim.le η.1 hηS).preimage
        continuous_subtype_val
    exact hη.def.symm.trans (closure_eq_iff_isClosed.mpr hηclosed) ▸ Set.finite_singleton η
  rw [hFcover]
  exact hFfin.sUnion hFfinite

/-- **The singular locus of a reduced one-dimensional Nagata scheme is discrete.** -/
public theorem discreteTopology_singularLocus (X : Scheme.{u}) [IsReduced X]
    (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) :
    DiscreteTopology (singularLocus X) := by
  classical
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x.1) isOpen_univ
  have hVfin : ((Subtype.val : V.1 → X) ⁻¹' (regularLocus X)ᶜ).Finite :=
    finite_singularLocus_inter_affineOpen X hX hdim V hVaff
  let F : Set X := (V : Set X) ∩ (regularLocus X)ᶜ
  have hFfin : F.Finite := by
    convert hVfin.image Subtype.val using 1
    ext y
    simp [F]
  have hFother_closed : IsClosed (F \ {x.1}) := by
    rw [show F \ {x.1} = ⋃ y ∈ F \ {x.1}, ({y} : Set X) by ext y; simp]
    refine hFfin.sdiff.isClosed_biUnion fun y hy => ?_
    exact isClosed_singleton_of_not_mem_regularLocus X hdim.le y hy.1.2
  have hW : (Subtype.val ⁻¹' ((V : Set X) \ (F \ {x.1}))) = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      by_contra h
      exact hy.2 ⟨⟨hy.1, y.2⟩, fun h' => h (Subtype.ext (Set.mem_singleton_iff.mp h'))⟩
    · rintro rfl
      exact ⟨hxV, by simp [F]⟩
  rw [← hW]
  exact (V.isOpen.sdiff hFother_closed).preimage continuous_subtype_val

end Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

end
