module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty

/-!
# Checking locality of a property of schemes on affine morphisms

A property of schemes which is local in the Zariski topology is local in a finer topology
as soon as it can be checked on morphisms of *affine* schemes: it must ascend along a
morphism of affine schemes of the relevant kind, and descend along a surjective one.

The five topologies of the source are fpqc, fppf, étale, smooth and syntomic, with the
corresponding classes of morphisms flat, flat of finite presentation, étale, smooth and
syntomic.

## Main results

* `AlgebraicGeometry.isLocal_zariskiPrecoverage_of_openCover` reduces Zariski locality,
  the standing hypothesis of the five criteria, to a statement about open subschemes and
  open covers.
* `AlgebraicGeometry.isLocal_fpqcPrecoverage_of_affine` is the fpqc case.
* `AlgebraicGeometry.isLocal_fppfPrecoverage_of_affine` is the fppf case.
* `AlgebraicGeometry.isLocal_etalePrecoverage_of_affine` is the étale case.
* `AlgebraicGeometry.isLocal_smoothPrecoverage_of_affine` is the smooth case.
* `AlgebraicGeometry.isLocal_syntomicPrecoverage_of_affine` is the syntomic case.

## Implementation notes

Four of the five topologies are given by `AlgebraicGeometry.Scheme.precoverage` applied to
the class of covering morphisms, and the criterion is proved once for any class which is
stable under base change, Zariski local at the source and universally open. The fpqc
precoverage carries the extra quasi-compactness condition on the covering family and is
handled separately; there the finite refinement provided by
`AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact` replaces the
openness argument.

The fppf hypotheses are stated with `AlgebraicGeometry.FinitePresentation`, as in the
source, whereas Mathlib's fppf precoverage uses local finite presentation; on a morphism of
affine schemes the two agree.

## References

* [Stacks Project, Tag 0349](https://stacks.math.columbia.edu/tag/0349)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A property of schemes invariant under isomorphism is Zariski local as soon as it
passes to open subschemes and can be read off any open cover by open subschemes. -/
theorem isLocal_zariskiPrecoverage_of_openCover (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsClosedUnderIsomorphisms P]
    (hOpen : ∀ {X : Scheme.{u}} (U : X.Opens), P X → P U.toScheme)
    (hCover : ∀ {X : Scheme.{u}} (U : X → X.Opens), IsOpenCover U →
      (∀ x, P (U x).toScheme) → P X) :
    ObjectProperty.IsLocal P Scheme.zariskiPrecoverage := by
  refine ObjectProperty.IsLocal.mk_of_zeroHypercover fun X 𝒰 => ?_
  have hdata : (∀ x : X, ∃ i, x ∈ Set.range (𝒰.f i).base) ∧
      ∀ i, IsOpenImmersion (𝒰.f i) := by
    simpa [Scheme.zariskiPrecoverage] using 𝒰.mem₀
  let V : 𝒰.I₀ → X.Opens := fun i => (𝒰.f i).opensRange
  have he (i : 𝒰.I₀) : 𝒰.X i ≅ (V i).toScheme :=
    have : IsOpenImmersion (𝒰.f i) := hdata.2 i
    IsOpenImmersion.isoOfRangeEq (𝒰.f i) (V i).ι (by simp [V])
  let j : X → 𝒰.I₀ := fun x => Classical.choose (hdata.1 x)
  exact ⟨fun hX i => ObjectProperty.IsClosedUnderIsomorphisms.of_iso (he i).symm
      (hOpen (V i) hX),
    fun hU => hCover (fun x => V (j x))
      (TopologicalSpace.IsOpenCover.mk (top_le_iff.mp fun x _ =>
        Opens.mem_iSup.mpr ⟨x, Classical.choose_spec (hdata.1 x)⟩))
      fun x => ObjectProperty.IsClosedUnderIsomorphisms.of_iso (he (j x)) (hU (j x))⟩

/-- A Zariski-local property of schemes passes to an open subscheme. -/
private lemma objectProperty_of_isOpenImmersion (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    {V X : Scheme.{u}} (i : V ⟶ X) (hi : IsOpenImmersion i) (hX : P X) : P V := by
  have := hi
  exact (ObjectProperty.iff_of_zeroHypercover (X.affineCover.add i)).mp hX none

/-- A Zariski-local property of schemes holds for an affine scheme covered by the open
images of a family of morphisms from affine schemes along which it descends. -/
private lemma objectProperty_of_affine_covering_family (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (M : MorphismProperty Scheme.{u}) [M.IsStableUnderBaseChange]
    (hOpen : ∀ {V U : Scheme.{u}} (f : V ⟶ U), M f → UniversallyOpen f)
    (hDesc : ∀ {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (f : V ⟶ U),
      M f → Surjective f → P V → P U)
    {U : Scheme.{u}} [IsAffine U] {ι : Type*} {V : ι → Scheme.{u}}
    (hAffine : ∀ i, IsAffine (V i))
    (f : ∀ i, V i ⟶ U) (hM : ∀ i, M (f i)) (hV : ∀ i, P (V i))
    (hCover : ∀ x : U, ∃ i y, f i y = x) : P U := by
  have instOpen (i : ι) : UniversallyOpen (f i) := hOpen (f i) (hM i)
  let O (i : ι) : U.Opens := ⟨Set.range (f i), (f i).isOpenMap.isOpen_range⟩
  have hO : IsOpenCover O :=
    TopologicalSpace.IsOpenCover.mk (top_le_iff.mp fun x _ => Opens.mem_iSup.mpr (hCover x))
  let 𝒪 : U.OpenCover := U.openCoverOfIsOpenCover O hO
  refine (ObjectProperty.iff_of_zeroHypercover 𝒪).2 fun i => ?_
  refine (ObjectProperty.iff_of_zeroHypercover ((𝒪.X i).affineCover)).2 fun j => ?_
  let a : (𝒪.X i).affineCover.X j ⟶ U := (𝒪.X i).affineCover.f j ≫ 𝒪.f i
  have hsurj : Surjective (pullback.fst a (f i)) := by
    refine ⟨fun w => ?_⟩
    obtain ⟨v, hv⟩ : a w ∈ Set.range (f i) := ((𝒪.X i).affineCover.f j w).property
    obtain ⟨z, hzW, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := a) (g := f i) w v hv.symm
    exact ⟨z, hzW⟩
  have : IsAffine (V i) := hAffine i
  have : IsAffineHom a := isAffineHom_of_isAffine a
  exact hDesc (pullback.fst a (f i)) (MorphismProperty.pullback_fst a (f i) (hM i)) hsurj
    (objectProperty_of_isOpenImmersion P (pullback.snd a (f i)) inferInstance (hV i))

/-- The ascent half of the criterion: a Zariski-local property of schemes which ascends
along morphisms of affine schemes in `M` ascends along every morphism in `M`. -/
private lemma objectProperty_of_morphismProperty (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (M : MorphismProperty Scheme.{u}) [M.IsStableUnderBaseChange]
    [IsZariskiLocalAtSource M]
    (hAsc : ∀ {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (f : V ⟶ U),
      M f → P U → P V)
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hMf : M f) (hX : P X) : P Y := by
  let 𝒰 := X.affineCover
  refine ObjectProperty.of_zeroHypercover (𝒰.pullback₁ f) fun i => ?_
  have : IsAffine (𝒰.X i) := Scheme.isAffine_affineCover X i
  let Z := pullback f (𝒰.f i)
  refine ObjectProperty.of_zeroHypercover Z.affineCover fun j => ?_
  exact hAsc _ (IsZariskiLocalAtSource.comp (MorphismProperty.pullback_snd f (𝒰.f i) hMf)
    (Z.affineCover.f j)) ((ObjectProperty.iff_of_zeroHypercover 𝒰).mp hX i)

/-- The descent half of the criterion: a Zariski-local property of schemes which descends
along surjective morphisms of affine schemes in `M` descends from any `M`-cover. -/
private lemma objectProperty_of_cover (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (M : MorphismProperty Scheme.{u}) [M.IsStableUnderBaseChange]
    [IsZariskiLocalAtSource M]
    (hOpen : ∀ {V U : Scheme.{u}} (f : V ⟶ U), M f → UniversallyOpen f)
    (hDesc : ∀ {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (f : V ⟶ U),
      M f → Surjective f → P V → P U)
    {X : Scheme.{u}} (E : X.Cover (Scheme.precoverage M))
    (hPX : ∀ i, P (E.X i)) : P X := by
  let 𝒰 := X.affineCover
  refine ObjectProperty.of_zeroHypercover 𝒰 fun a => ?_
  let E' := Precoverage.ZeroHypercover.pullback₁ (𝒰.f a) E
  let A (i : E'.I₀) := (E'.X i).affineCover
  let V (p : Σ i, (A i).I₀) := (A p.1).X p.2
  let g (p : Σ i, (A i).I₀) : V p ⟶ 𝒰.X a := (A p.1).f p.2 ≫ E'.f p.1
  have hV (p : Σ i, (A i).I₀) : P (V p) :=
    objectProperty_of_isOpenImmersion P ((A p.1).f p.2) ((A p.1).map_prop p.2)
      (objectProperty_of_isOpenImmersion P (pullback.snd (𝒰.f a) (E.f p.1))
        (MorphismProperty.pullback_snd _ _ inferInstance) (hPX p.1))
  have hM (p : Σ i, (A i).I₀) : M (g p) := by
    have hMi : M (E'.f p.1) := MorphismProperty.pullback_fst _ _ (E.map_prop p.1)
    exact IsZariskiLocalAtSource.comp hMi ((A p.1).f p.2)
  have hCover (x : 𝒰.X a) : ∃ p w, g p w = x := by
    obtain ⟨i, z, hz⟩ := Scheme.Cover.exists_eq E' x
    obtain ⟨j, w, hw⟩ := (E'.X i).affineCover.exists_eq z
    exact ⟨⟨i, j⟩, w, show E'.f i ((A i).f j w) = x by rw [hw, hz]⟩
  exact objectProperty_of_affine_covering_family P M hOpen hDesc (U := 𝒰.X a)
    (ι := Σ i, (A i).I₀) (V := V)
    (fun p => Scheme.isAffine_affineCover (E'.X p.1) p.2) g hM hV hCover

/-- A Zariski-local property of schemes is local for the precoverage of a class `M` of
morphisms which is stable under base change, Zariski local at the source and universally
open, provided it ascends along morphisms of affine schemes in `M` and descends along the
surjective ones. -/
private theorem isLocal_precoverage_of_affine (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (M : MorphismProperty Scheme.{u}) [M.IsStableUnderBaseChange]
    [IsZariskiLocalAtSource M]
    (hOpen : ∀ {V U : Scheme.{u}} (f : V ⟶ U), M f → UniversallyOpen f)
    (hAsc : ∀ {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (f : V ⟶ U),
      M f → P U → P V)
    (hDesc : ∀ {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (f : V ⟶ U),
      M f → Surjective f → P V → P U) :
    ObjectProperty.IsLocal P (Scheme.precoverage M) where
  of_iso := ObjectProperty.IsClosedUnderIsomorphisms.of_iso
  component {X R} hR {Y} f hf hX :=
    objectProperty_of_morphismProperty P M hAsc f (hR.2 hf) hX
  of_presieve {X R} hR h := by
    obtain ⟨E, rfl⟩ :=
      (Precoverage.mem_iff_exists_zeroHypercover (J := Scheme.precoverage M)).mp hR
    exact objectProperty_of_cover P M hOpen hDesc E fun i => h (E.presieve₀_f i)

/-- The range of an open subscheme followed by a morphism is the image of the open. -/
lemma range_ι_comp {X Y : Scheme.{u}} (U : X.Opens) (f : X ⟶ Y) :
    Set.range (U.ι ≫ f) = f '' (U : Set X) := by
  ext x
  simp only [Scheme.Hom.comp_apply, Set.mem_range, Set.mem_image, SetLike.mem_coe]
  exact ⟨fun ⟨y, hy⟩ => ⟨y.1, y.2, hy⟩, fun ⟨y, hy, hyx⟩ => ⟨⟨y, hy⟩, by simpa using hyx⟩⟩

/-- **Stacks Project, Tag 0349.** A Zariski-local property of schemes which ascends along
flat morphisms of affine schemes and descends along the surjective ones is fpqc local. -/
@[stacks 0349 "fpqc case"]
theorem isLocal_fpqcPrecoverage_of_affine (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (ascends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Flat f → P S → P X)
    (descends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Flat f → Surjective f → P X → P S) :
    ObjectProperty.IsLocal P Scheme.fpqcPrecoverage where
  of_iso := ObjectProperty.IsClosedUnderIsomorphisms.of_iso
  component {X R} hR {Y} f hf hX :=
    have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    objectProperty_of_morphismProperty P @Flat ascends f (hR.2.2 hf) hX
  of_presieve {X R} hR h := by
    obtain ⟨E, rfl⟩ :=
      (Precoverage.mem_iff_exists_zeroHypercover (J := Scheme.fpqcPrecoverage)).mp hR
    let E : X.Cover Scheme.fpqcPrecoverage := E
    have : QuasiCompactCover E.toPreZeroHypercover :=
      Scheme.presieve₀_mem_qcPrecoverage_iff.mp hR.1
    let 𝒰 := X.affineCover
    refine ObjectProperty.of_zeroHypercover 𝒰 fun a => ?_
    let E' := Precoverage.ZeroHypercover.pullback₁ (𝒰.f a) E
    have : IsAffine (𝒰.X a) := Scheme.isAffine_affineCover X a
    have : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Flat : MorphismProperty Scheme.{u}) (𝒰.f a) :=
      ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    have : QuasiCompactCover E'.toPreZeroHypercover :=
      inferInstanceAs (QuasiCompactCover ((E.toPreZeroHypercover).pullback₁ (𝒰.f a)))
    have hCompact : IsCompact ((⊤ : Opens (𝒰.X a)) : Set (𝒰.X a)) := isCompact_univ
    obtain ⟨n, idx, Wopen, hWopen, hWcover⟩ :=
      QuasiCompactCover.exists_isAffineOpen_of_isCompact E'.toPreZeroHypercover hCompact
    let W (j : Fin n) : Scheme.{u} := (Wopen j).toScheme
    let g (j : Fin n) : W j ⟶ 𝒰.X a := (Wopen j).ι ≫ E'.f (idx j)
    have instAff (j : Fin n) : IsAffine (W j) := hWopen j
    have hWP (j : Fin n) : P (W j) :=
      objectProperty_of_isOpenImmersion P (Wopen j).ι inferInstance
        (objectProperty_of_isOpenImmersion P (pullback.snd (𝒰.f a) (E.f (idx j)))
          (MorphismProperty.pullback_snd _ _ inferInstance) (h (E.presieve₀_f (idx j))))
    have instFlat (j : Fin n) : Flat (g j) :=
      MorphismProperty.comp_mem _ _ _ inferInstance
        (MorphismProperty.pullback_fst (𝒰.f a) (E.f (idx j)) (hR.2.2 (E.presieve₀_f (idx j))))
    have hRanges : (⋃ j, Set.range (g j)) = Set.univ := by
      calc
        (⋃ j, Set.range (g j))
            = ⋃ j, E'.f (idx j) '' (Wopen j : Set (E'.X (idx j))) := by
          simp only [g, W, range_ι_comp]
        _ = (⊤ : Opens (𝒰.X a)) := hWcover
        _ = Set.univ := by simp
    exact descends (Sigma.desc g) inferInstance
      (Surjective.sigmaDesc_of_union_range_eq_univ hRanges)
      ((ObjectProperty.iff_of_zeroHypercover (AlgebraicGeometry.sigmaOpenCover W)).2 hWP)

/-- **Stacks Project, Tag 0349.** A Zariski-local property of schemes which ascends along
flat morphisms of finite presentation of affine schemes and descends along the surjective
ones is fppf local. -/
@[stacks 0349 "fppf case"]
theorem isLocal_fppfPrecoverage_of_affine (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (ascends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Flat f → FinitePresentation f → P S → P X)
    (descends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Flat f → FinitePresentation f → Surjective f → P X → P S) :
    ObjectProperty.IsLocal P Scheme.fppfPrecoverage := by
  have : MorphismProperty.IsStableUnderBaseChange
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := @Flat) (Q := @LocallyOfFinitePresentation)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    (Q := RingHom.FinitePresentation)
  have : IsZariskiLocalAtSource
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsLocalAtSource.inf (@Flat) (@LocallyOfFinitePresentation)
  refine isLocal_precoverage_of_affine P (@Flat ⊓ @LocallyOfFinitePresentation)
    (fun f hf => ?_) (fun f hf hU => ?_) (fun f hf hsurj hV => ?_)
  · have : Flat f := hf.1
    have : LocallyOfFinitePresentation f := hf.2
    infer_instance
  · exact ascends f hf.1 ⟨hf.2, inferInstance, inferInstance⟩ hU
  · exact descends f hf.1 ⟨hf.2, inferInstance, inferInstance⟩ hsurj hV

/-- **Stacks Project, Tag 0349.** A Zariski-local property of schemes which ascends along
étale morphisms of affine schemes and descends along the surjective ones is étale local. -/
@[stacks 0349 "étale case"]
theorem isLocal_etalePrecoverage_of_affine (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (ascends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Etale f → P S → P X)
    (descends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Etale f → Surjective f → P X → P S) :
    ObjectProperty.IsLocal P Scheme.etalePrecoverage := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  exact isLocal_precoverage_of_affine P @Etale
    (fun f hf => have : Etale f := hf; inferInstance) ascends descends

/-- **Stacks Project, Tag 0349.** A Zariski-local property of schemes which ascends along
smooth morphisms of affine schemes and descends along the surjective ones is smooth
local. -/
@[stacks 0349 "smooth case"]
theorem isLocal_smoothPrecoverage_of_affine (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (ascends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Smooth f → P S → P X)
    (descends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Smooth f → Surjective f → P X → P S) :
    ObjectProperty.IsLocal P (Scheme.precoverage @Smooth) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  exact isLocal_precoverage_of_affine P @Smooth
    (fun f hf => have : Smooth f := hf; inferInstance) ascends descends

/-- **Stacks Project, Tag 0349.** A Zariski-local property of schemes which ascends along
syntomic morphisms of affine schemes and descends along the surjective ones is syntomic
local. -/
@[stacks 0349 "syntomic case"]
theorem isLocal_syntomicPrecoverage_of_affine (P : ObjectProperty Scheme.{u})
    [ObjectProperty.IsLocal P Scheme.zariskiPrecoverage]
    (ascends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Syntomic f → P S → P X)
    (descends : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S),
      Syntomic f → Surjective f → P X → P S) :
    ObjectProperty.IsLocal P (Scheme.precoverage @Syntomic) :=
  isLocal_precoverage_of_affine P @Syntomic (fun _ hf => universallyOpen_of_syntomic hf)
    ascends descends

end AlgebraicGeometry
