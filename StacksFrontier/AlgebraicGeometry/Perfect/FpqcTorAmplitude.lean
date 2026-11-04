module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles

/-!
# Locally finite Tor dimension descends along an fpqc covering of schemes

Let `{f_i : Y_i ⟶ X}` be a family of morphisms of schemes lying in
`AlgebraicGeometry.Scheme.fpqcPrecoverage X` and let `E` be an object of `D(𝒪_X)` whose derived
pullback `Lf_i^*E` is perfect for every member. Then `E` locally has finite Tor dimension, with
no further hypothesis; and if moreover `E` is pseudo-coherent then `E` is perfect. That is the
Tor-amplitude half of the converse of Stacks 09UG, together with the assembly of the two halves
through Stacks 08CQ.

## Main results

* `hasFiniteTorDimension_restrict_of_strict_model`: an open carrying a strictly perfect model for
  `E` has finite Tor dimension, and so does every smaller open.
* `exists_cover_hasFiniteTorDimension_of_isPerfect`: a perfect object has an open cover such that
  every open contained in a member of it has finite Tor dimension.
* `exists_finite_cover_hasTorAmplitude_of_isPerfect_of_isCompact`: a quasi-compact open has a
  finite cover by opens carrying one Tor-amplitude interval.
* `exists_hasFiniteTorDimension_of_forall_isPerfect_derivedPullback`: every point of `X` has an
  open neighbourhood on which `E` has finite Tor dimension.
* `locallyHasFiniteTorDimension_of_forall_isPerfect_derivedPullback`: `E` locally has finite Tor
  dimension, the Tor-amplitude half of the converse of Stacks 09UG.
* `isPerfect_of_isPseudoCoherent_of_forall_isPerfect_derivedPullback`: a pseudo-coherent `E` whose
  derived pullbacks are perfect is perfect.

## Implementation notes

The derived categories are the standard ones, fixed by a local instance at priority `2000`. The
locally small model is a global instance and is the one instance search finds at the default
priority, while `Stacks.Cohomology.PerfectComplexTriangles.strict_model_of_le` and
`Stacks.Cohomology.TorAmplitude.FlatDescent.hasTorAmplitude_iff_forall_derivedPullback` are
stated at the standard model.

## References

* [Stacks Project, Tag 09UG](https://stacks.math.columbia.edu/tag/09UG)
* [Stacks Project, Tag 09UD](https://stacks.math.columbia.edu/tag/09UD)
* [Stacks Project, Tag 09UE](https://stacks.math.columbia.edu/tag/09UE)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 03L7](https://stacks.math.columbia.edu/tag/03L7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.PseudoCoherence (restrictModules)
open StrictlyPerfect (OXMod IsStrictlyPerfect)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u v

attribute [local instance 2000] _root_.HasDerivedCategory.standard

namespace Stacks.Cohomology.TorAmplitude

variable {X : RingedSpace.{u, u}}

/-- **An open subspace carrying a strictly perfect model has finite Tor dimension**, and so does
every smaller open subspace: if `P` is a strictly perfect complex on `U` whose image in the
derived category is isomorphic to the restriction of `K`, then the restriction of `K` to any open
`W ≤ U` has finite Tor dimension. -/
theorem hasFiniteTorDimension_restrict_of_strict_model
    {U W : Opens X.carrier} (hWU : W ≤ U) (K : DerivedCategory (OXMod.{u, u} X))
    (P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (eP : DerivedCategory.Q.obj P ≅ (restrictModules X U).mapDerivedCategory.obj K) :
    HasFiniteTorDimension (X.restrict W.isOpenEmbedding)
      ((restrictModules X W).mapDerivedCategory.obj K) := by
  obtain ⟨P', hP', ⟨eP'⟩⟩ := Stacks.Cohomology.PerfectComplexTriangles.strict_model_of_le hWU K
    P hP eP
  obtain ⟨a, b, -, hz⟩ := exists_bounds_of_isStrictlyPerfect P' hP'
  exact ⟨a, b, Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative
    _ a b P' (fun j =>
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isFlat_of_isDirectSummandOfFiniteFree _
        (hP'.directSummand j)) hz eP'⟩

/-- **A perfect object has an open cover every open subset of whose members has finite Tor
dimension**: there is an open cover `U : I → Opens X.carrier` of `X` such that the restriction of
`K` to any open `W ≤ U i` has finite Tor dimension. -/
theorem exists_cover_hasFiniteTorDimension_of_isPerfect
    (K : DerivedCategory (OXMod.{u, u} X)) (hK : IsPerfect K) :
    ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
      ∀ (i : I) (W : Opens X.carrier), W ≤ U i →
        HasFiniteTorDimension (X.restrict W.isOpenEmbedding)
          ((restrictModules X W).mapDerivedCategory.obj K) := by
  obtain ⟨Fc, hFc, ⟨eE⟩⟩ := hK
  obtain ⟨I, U, hsup, hmod⟩ := hFc
  refine ⟨I, U, hsup, fun i W hWU => ?_⟩
  obtain ⟨P, hP, f, hf⟩ := hmod i
  have hqi : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  refine hasFiniteTorDimension_restrict_of_strict_model hWU K P hP ?_
  exact (@asIso _ _ _ _ (DerivedCategory.Q.map f) hqi) ≪≫
    ((restrictModules X (U i)).mapDerivedCategoryFactors.app Fc).symm ≪≫
    (restrictModules X (U i)).mapDerivedCategory.mapIso eE

/-- **A quasi-compact open subspace of the space of a perfect object has a finite open cover
carrying a single Tor-amplitude interval**: for `V` quasi-compact there are finitely many opens
`W t ≤ V` covering `V` and integers `A`, `B` such that the restriction of `K` to each `W t` has
Tor amplitude in `[A, B]`. -/
theorem exists_finite_cover_hasTorAmplitude_of_isPerfect_of_isCompact
    (K : DerivedCategory (OXMod.{u, u} X)) (hK : IsPerfect K)
    (V : Opens X.carrier) (hV : IsCompact (V : Set X.carrier)) :
    ∃ (T : Type u) (_ : Fintype T) (W : T → Opens X.carrier) (A B : ℤ),
      (∀ t, W t ≤ V) ∧ (⋃ t, (W t : Set X.carrier)) = (V : Set X.carrier) ∧
      ∀ t, HasTorAmplitude (X.restrict (W t).isOpenEmbedding)
        ((restrictModules X (W t)).mapDerivedCategory.obj K) A B := by
  classical
  obtain ⟨I, U, hsup, hfin⟩ := exists_cover_hasFiniteTorDimension_of_isPerfect K hK
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun i : I => (U i : Set X.carrier))
    (fun i => (U i).isOpen) (by
      intro y hy
      have : y ∈ ((⊤ : Opens X.carrier) : Set X.carrier) := Set.mem_univ y
      rw [← hsup, Opens.coe_iSup] at this
      exact this)
  refine ⟨{i : I // i ∈ s}, inferInstance, fun t => V ⊓ U t.1, ?_⟩
  have key : ∀ t : {i : I // i ∈ s}, HasFiniteTorDimension
      (X.restrict (V ⊓ U t.1).isOpenEmbedding)
      ((restrictModules X (V ⊓ U t.1)).mapDerivedCategory.obj K) :=
    fun t => hfin t.1 _ inf_le_right
  choose a b hab using key
  refine ⟨-(Finset.univ.sup fun t => max (a t).natAbs (b t).natAbs : ℕ),
    (Finset.univ.sup fun t => max (a t).natAbs (b t).natAbs : ℕ), fun t => inf_le_left, ?_,
    fun t => ?_⟩
  · refine Set.Subset.antisymm (Set.iUnion_subset fun t => ?_) ?_
    · exact fun y hy => hy.1
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hs hy)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, ⟨hy, hyi⟩⟩
  · have hle : max (a t).natAbs (b t).natAbs ≤
        Finset.univ.sup fun t => max (a t).natAbs (b t).natAbs :=
      Finset.le_sup (f := fun t => max (a t).natAbs (b t).natAbs) (Finset.mem_univ t)
    have h1 : (a t).natAbs ≤ Finset.univ.sup fun t => max (a t).natAbs (b t).natAbs :=
      (le_max_left _ _).trans hle
    have h2 : (b t).natAbs ≤ Finset.univ.sup fun t => max (a t).natAbs (b t).natAbs :=
      (le_max_right _ _).trans hle
    exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} (hab t) (by omega) (by omega)

end Stacks.Cohomology.TorAmplitude

namespace Stacks.Cohomology.PerfectComplexes.FpqcDescent

open Stacks.Cohomology.TorAmplitude

variable {S : Scheme.{u}}

/-- **Finite Tor dimension near every point.** Let `{f_i : Y_i ⟶ S}` be a family of morphisms of
schemes in `AlgebraicGeometry.Scheme.fpqcPrecoverage S` and let `E` be an object of `D(𝒪_S)`
whose derived pullback to every member is perfect. Then every point of `S` has an open
neighbourhood on which `E` has finite Tor dimension. -/
theorem exists_hasFiniteTorDimension_of_forall_isPerfect_derivedPullback
    {I : Type v} (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ S)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage S)
    (E : DerivedCategory (OXMod.{u, u} S.toRingedSpace))
    (hE : ∀ i, IsPerfect (X := (Y i).toRingedSpace)
      ((derivedPullback (f i).toLRSHom.toShHom).obj E))
    (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ HasFiniteTorDimension (S.toRingedSpace.restrict U.isOpenEmbedding)
      ((restrictModules S.toRingedSpace U).mapDerivedCategory.obj E) := by
  classical
  have hflat : ∀ i, Flat (f i) := fun i =>
    Stacks.Cohomology.PseudoCoherence.FpqcDescent.flat_of_mem_fpqcPrecoverage Y f hf i
  obtain ⟨U, hUaff, hxU, n, a, V, hVaff, hVcov⟩ :=
    Stacks.Cohomology.PseudoCoherence.FpqcDescent.exists_affineOpen_affine_images_cover Y f hf x
  refine ⟨U, hxU, ?_⟩
  choose T hT W A B hWle hWcov hWamp using fun j : Fin n =>
    exists_finite_cover_hasTorAmplitude_of_isPerfect_of_isCompact
      ((derivedPullback (f (a j)).toLRSHom.toShHom).obj E) (hE (a j)) (V j) (hVaff j).isCompact
  set N : ℕ := Finset.univ.sup fun j : Fin n => max (A j).natAbs (B j).natAbs
  have hAB : ∀ j : Fin n, ∀ t : T j, HasTorAmplitude
      ((Y (a j)).toRingedSpace.restrict (W j t).isOpenEmbedding)
      ((restrictModules (Y (a j)).toRingedSpace (W j t)).mapDerivedCategory.obj
        ((derivedPullback (f (a j)).toLRSHom.toShHom).obj E)) (-(N : ℤ)) (N : ℤ) := by
    intro j t
    have hle : max (A j).natAbs (B j).natAbs ≤ N :=
      Finset.le_sup (f := fun j : Fin n => max (A j).natAbs (B j).natAbs) (Finset.mem_univ j)
    have h1 : (A j).natAbs ≤ N := (le_max_left _ _).trans hle
    have h2 : (B j).natAbs ≤ N := (le_max_right _ _).trans hle
    exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} (hWamp j t) (by omega) (by omega)
  have hVU : ∀ j : Fin n, V j ≤ (f (a j)) ⁻¹ᵁ U := by
    intro j y hy
    change (f (a j)).base y ∈ (U : Set S)
    rw [← hVcov]
    exact Set.mem_iUnion.mpr ⟨j, ⟨y, hy, rfl⟩⟩
  have hWU : ∀ t : Σ j : Fin n, T j, W t.1 t.2 ≤ (f (a t.1)) ⁻¹ᵁ U := fun t =>
    (hWle t.1 t.2).trans (hVU t.1)
  refine ⟨-(N : ℤ), (N : ℤ), ?_⟩
  refine (Stacks.Cohomology.TorAmplitude.FlatDescent.hasTorAmplitude_iff_forall_derivedPullback
    (X := fun t : Σ j : Fin n, T j =>
      (Scheme.Opens.toScheme (W t.1 t.2)).toLocallyRingedSpace)
    (Y := U.toScheme.toLocallyRingedSpace)
    (fun t => ((f (a t.1)).resLE U (W t.1 t.2) (hWU t)).toLRSHom) ?_
    (fun t => Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _) _
    (-(N : ℤ)) (N : ℤ)).mpr ?_
  · intro y
    have hy : (U.ι) y ∈ (⋃ j, (f (a j)) '' (V j : Set (Y (a j)))) := by
      rw [hVcov]
      exact y.2
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    have hz' : z ∈ (⋃ t, (W j t : Set (Y (a j)))) := by rw [hWcov j]; exact hz
    obtain ⟨t, hzt⟩ := Set.mem_iUnion.mp hz'
    refine ⟨⟨j, t⟩, ⟨z, hzt⟩, Subtype.ext ?_⟩
    change (((f (a j)).resLE U (W j t) (hWU ⟨j, t⟩)) ≫ U.ι) ⟨z, hzt⟩ = U.ι y
    rw [Scheme.Hom.resLE_comp_ι]
    exact hzy
  · intro t
    refine FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} (hAB t.1 t.2) ?_
    exact AlgebraicGeometry.RingedSpace.derivedPullbackRestrictIso
      (f (a t.1)).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom (f (a t.1))) U (W t.1 t.2)
      ((f (a t.1)).resLE U (W t.1 t.2) (hWU t)).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.resLE_square (f (a t.1)) U (W t.1 t.2)
        (hWU t)) E

/-- **The Tor-amplitude half of the converse of Stacks 09UG.** If the derived pullback of
`E ∈ D(𝒪_S)` to every member of a family of morphisms of schemes in
`AlgebraicGeometry.Scheme.fpqcPrecoverage S` is perfect, then `E` locally has finite Tor dimension
in the sense of Stacks 08CG. -/
theorem locallyHasFiniteTorDimension_of_forall_isPerfect_derivedPullback
    {I : Type v} (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ S)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage S)
    (E : DerivedCategory (OXMod.{u, u} S.toRingedSpace))
    (hE : ∀ i, IsPerfect (X := (Y i).toRingedSpace)
      ((derivedPullback (f i).toLRSHom.toShHom).obj E)) :
    LocallyHasFiniteTorDimension S.toRingedSpace E := by
  choose U hxU hfin using
    exists_hasFiniteTorDimension_of_forall_isPerfect_derivedPullback Y f hf E hE
  refine ⟨S.carrier, U, ?_, hfin⟩
  refine top_unique fun x _ => ?_
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- **A pseudo-coherent object whose derived pullbacks to an fpqc covering are perfect is
perfect.** Let `{f_i : Y_i ⟶ S}` lie in `AlgebraicGeometry.Scheme.fpqcPrecoverage S`, let
`E ∈ D(𝒪_S)` be pseudo-coherent and let every derived pullback `Lf_i^*E` be perfect. Then `E` is
perfect. -/
theorem isPerfect_of_isPseudoCoherent_of_forall_isPerfect_derivedPullback
    {I : Type v} (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ S)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage S)
    (E : DerivedCategory (OXMod.{u, u} S.toRingedSpace))
    (hpc : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
      (X := S.toRingedSpace) E)
    (hE : ∀ i, IsPerfect (X := (Y i).toRingedSpace)
      ((derivedPullback (f i).toLRSHom.toShHom).obj E)) :
    IsPerfect E :=
  isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension E hpc
    (locallyHasFiniteTorDimension_of_forall_isPerfect_derivedPullback Y f hf E hE)

example (E : DerivedCategory (OXMod.{u, u} S.toRingedSpace)) (hE : IsPerfect E) :
    LocallyHasFiniteTorDimension S.toRingedSpace E :=
  locallyHasFiniteTorDimension_of_forall_isPerfect_derivedPullback (fun _ : PUnit.{1} => S)
    (fun _ => 𝟙 S)
    (by rw [Presieve.ofArrows_pUnit]; exact Scheme.Hom.singleton_mem_fpqcPrecoverage (𝟙 S)) E
    fun _ => AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (Scheme.Hom.toLRSHom (𝟙 S)).toShHom E hE

example (E : DerivedCategory (OXMod.{u, u} S.toRingedSpace)) (hE : IsPerfect E) : IsPerfect E :=
  isPerfect_of_isPseudoCoherent_of_forall_isPerfect_derivedPullback (fun _ : PUnit.{1} => S)
    (fun _ => 𝟙 S)
    (by rw [Presieve.ofArrows_pUnit]; exact Scheme.Hom.singleton_mem_fpqcPrecoverage (𝟙 S)) E
    (isPseudoCoherent_of_isPerfect E hE)
    fun _ => AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (Scheme.Hom.toLRSHom (𝟙 S)).toShHom E hE

end Stacks.Cohomology.PerfectComplexes.FpqcDescent

end
