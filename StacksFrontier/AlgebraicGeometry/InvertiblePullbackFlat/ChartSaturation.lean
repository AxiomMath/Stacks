module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartFromGenerators

/-!
# The chart of Tag 0BD7: the non-generating locus is closed and saturated

The last two paragraphs of [Stacks, Tag 0BD7] produce the chart of the descent. Having found a
meromorphic function `g` on the base with `φ^*(g) s` generating `ℒ` at one point of the fibre
`φ^{-1}(y)`, the source sets

> `Z ⊂ X` the set of points `z` such that `φ^*(g) s` does not generate `ℒ_z`

and then says: *the arguments above show that `Z` is closed and that `Z = φ^{-1}(T)` for some
subset `T ⊂ Y` with `y ∉ T`*; if `T` is closed then `Y ∖ T` is the wanted neighbourhood of `y`.
The chart is therefore **not chosen** — it is the image of the complement of `Z`, and the
containment `φ^{-1}(Y ∖ T) ⊆ {φ^*(g) s generates}` that a chart datum needs holds by
construction rather than by a choice. The two things genuinely owed are the two words *closed*
and *saturated*, and this file supplies them:

* **closed** is the complement of `Stacks.SheafOfModules.isOpen_generatingLocus`, which is the
  openness clause of [Stacks, Tag 01CY] for a section defined on an *open* rather than globally
  — the form Tag 0BD7 needs, since `φ^*(g) s` is regular only near the fibre and is never a
  global section;
* **saturated** is `Stacks.InvertiblePullback.mem_generatingLocus_of_mem_fiber`: the generating
  locus of one member of a family of sections is a union of fibres. Its proof is the source's
  own fibre-irreducibility argument. Given `z` in the locus of `t i` and `z'` in the same fibre,
  the penultimate paragraph supplies *some* `t j` generating at `z'`; the two generating loci are
  open and both meet the fibre, so by irreducibility of the fibre they meet each other inside it,
  at a point `x''`; and the uniqueness of the generator at `x''` identifies the two loci along
  the whole fibre, so `z'` lies in the locus of `t i` as well.

Closedness and saturation together, through hypothesis (4) of the tag and
`AlgebraicGeometry.isClosed_of_isClosed_preimage_of_flat` (Tag 02JY and Tag 01UA), give the chart
datum of `StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartFromGenerators.lean`: see
`Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections`, whose conclusion is exactly
the `chart`/`gen` pair that
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isIntegral_fiber` consumes. The
family `t` with its existence and uniqueness properties — the penultimate paragraph, whose
ring-theoretic core is `Ideal.exists_isUnit_mul_eq_of_isDomain_fiber` and
`Module.FaithfullyFlat.associated_of_algebraMap_eq_isUnit_mul` — and the transition units are
constructed in `StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyAgreement.lean`.

## Main definitions

* `Stacks.SheafOfModules.generatingLocus`: the set of points at which a section of `ℒ` defined on
  an open `U` generates the stalk; its complement is the source's `Z`. A point outside `U`
  counts as a point where the section does not generate, which is what makes the complement of
  the locus the source's `Z` for a section that is only generically defined.

## Main results

* `Stacks.SheafOfModules.nonvanishingLocus_eq_generatingLocus`: for a global section the locus is
  `Stacks.SheafOfModules.nonvanishingLocus`, so this is one notion and not a second encoding.
* `Stacks.SheafOfModules.isOpen_generatingLocus`: **`Z` is closed.**
* `Stacks.SheafOfModules.generatingLocus_smul_of_isUnit`: multiplying the section by a unit does
  not move the locus — the source's "`g` and `g'` differ by an element of `𝒪_{Y, y}^*`, hence
  `φ^*(g) s` generates where `φ^*(g') s` does".
* `Stacks.SheafOfModules.mem_generatingLocus_of_grpGerm_eq_smul`: the same read on one stalk —
  a section whose germ at a point is a unit multiple of the germ of a generating section
  generates there too.
* `Stacks.SheafOfModules.mem_generatingLocus_iff_of_restrictₛₗ_eq_smul`: the previous result in
  the form the fibre argument consumes — two sections whose restrictions to a common open differ
  by a unit have the same locus inside that open.
* `Stacks.InvertiblePullback.isIrreducible_preimage_singleton_of_isIntegral_fiber`: the tag's
  integrality hypothesis on the fibres, read as irreducibility of `φ^{-1}(y)` as a subset of `X`.
* `Stacks.InvertiblePullback.mem_generatingLocus_of_mem_fiber`: **`Z` is saturated.**
* `Stacks.InvertiblePullback.preimage_image_generatingLocus`: saturation restated as
  `Z = φ^{-1}(T)`, with `T` the image.
* `Stacks.InvertiblePullback.exists_chart_coe_preimage_eq_generatingLocus`: the chart, with the
  equation `φ^{-1}(chart y) = {φ^*(g_y) s generates}` that makes the containment free.
* `Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections`: the chart datum of
  `ChartFromGenerators.lean`.

## Implementation notes

The statements below take as hypotheses the family `t` of candidate generators together with its
existence property `hex` and its uniqueness property `hagree`; these are produced by the
penultimate paragraph of the proof.

`Stacks.SheafOfModules.isOpen_generatingLocus` generalises
`Stacks.SheafOfModules.isOpen_nonvanishingLocus`, the openness clause of Tag 01CY for a global
section; `Stacks.SheafOfModules.nonvanishingLocus_eq_generatingLocus` records that the two loci
are the same set.

The uniqueness hypothesis `hagree` is stated as *agreement of the two loci along the fibre*
rather than as "the two meromorphic functions differ by a unit of `𝒪_{Y, y}`". That is the
weakest form the fibre argument consumes, and it is not the whole of the source's uniqueness
statement: `Stacks.SheafOfModules.mem_generatingLocus_iff_of_restrictₛₗ_eq_smul` is the bridge
from a unit relation to `hagree`, so the two halves of the source's sentence are separated here —
the unit is produced by the ring theory of `StalkGenerator.lean`, and only its consequence for
the loci is used topologically.

Three spellings are forced rather than cosmetic. The restriction of a section is written with
`PresheafOfModules.restrictₛₗ` and not `PresheafOfModules.map`, because `L.val.map i` lands in
`(ModuleCat.restrictScalars _).obj (L.val.obj (op W))` and `generatingLocus` cannot even be
applied to such a term; this is the same forcing recorded in `SectionGenerator.lean`. The
germ-of-a-restriction equation is used as a *term* (`▸` on a `have` with a declared type) and not
by `rw`, which fails on it. And the pairing criterion
`Stacks.SheafOfModules.mem_generatingLocus_iff_exists_tensorPairing` takes the trivialization `ψ`
as an argument so that `isOpen_generatingLocus` can *apply* it: the `ψ` obtained from
`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit` is typed at the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf` spelling of the ring sheaf
rather than at `structureSheafRing X`, and an application crosses that gap where a `rw` inside
the proof does not.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 02JY](https://stacks.math.columbia.edu/tag/02JY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (L : SheafOfModules.{u} (structureSheafRing X))

/-- **The generating locus of a section defined on an open.** The set of points `z` at which the
germ of `t ∈ ℒ(U)` generates the stalk `ℒ_z`, that is, does not lie in `𝔪_z ℒ_z`. Points outside
`U` are not in the locus, so the complement of this set is the set `Z` of the last paragraph of
[Stacks, Tag 0BD7]: there the section `φ^*(g) s` is a meromorphic section, regular only on a
neighbourhood of the fibre, and a point at which it is not even defined is a point at which it
does not generate. -/
def generatingLocus {U : Opens X.carrier} (t : L.val.obj (op U)) : Set X.carrier :=
  {z | ∃ hz : z ∈ U, grpGerm X L.val z U hz t ∉
    maximalIdeal (ringStalk X z) • (⊤ : Submodule (ringStalk X z) (grpStalk X L.val z))}

/-- Membership in the generating locus, from the germ condition at a point of the domain. -/
theorem mem_generatingLocus {U : Opens X.carrier} {t : L.val.obj (op U)} {z : X.carrier}
    (hz : z ∈ U) (h : grpGerm X L.val z U hz t ∉
      maximalIdeal (ringStalk X z) • (⊤ : Submodule (ringStalk X z) (grpStalk X L.val z))) :
    z ∈ generatingLocus L t := ⟨hz, h⟩

/-- The generating locus of a section over `U` is contained in `U`. -/
theorem generatingLocus_le {U : Opens X.carrier} (t : L.val.obj (op U)) :
    generatingLocus L t ⊆ (U : Set X.carrier) := fun _ h => h.elim fun hz _ => hz

/-- The germ condition at a point of the generating locus, stated against an arbitrary proof that
the point lies in the domain. -/
theorem notMem_maximalIdeal_smul_of_mem_generatingLocus {U : Opens X.carrier}
    {t : L.val.obj (op U)} {z : X.carrier} (h : z ∈ generatingLocus L t) (hz : z ∈ U) :
    grpGerm X L.val z U hz t ∉
      maximalIdeal (ringStalk X z) • (⊤ : Submodule (ringStalk X z) (grpStalk X L.val z)) :=
  h.elim fun _ h' => h'

/-- **The generating locus of a global section is its nonvanishing locus.** So
`Stacks.SheafOfModules.generatingLocus` generalises
`Stacks.SheafOfModules.nonvanishingLocus` off global sections rather than re-encoding it. -/
theorem nonvanishingLocus_eq_generatingLocus (s : L.sections) :
    nonvanishingLocus L s = generatingLocus L (s.eval (op ⊤)) := by
  ext z
  exact ⟨fun h => ⟨Opens.mem_top z, h⟩, fun h => h.elim fun _ h' => h'⟩

/-- The germ of a restricted section at a point of the smaller open is the section's germ. -/
private theorem grpGerm_restrictₛₗ {X : RingedSpace.{u, u}}
    (L : SheafOfModules.{u} (structureSheafRing X)) {U W : Opens X.carrier}
    (hWU : W ≤ U) (t : L.val.obj (op U)) (z : X.carrier) (hz : z ∈ W) :
    grpGerm X L.val z W hz (L.val.restrictₛₗ (homOfLE hWU).op t)
      = grpGerm X L.val z U (hWU hz) t :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf (homOfLE hWU) z hz t

/-- Restricting a section cuts its generating locus down by the smaller open. -/
theorem generatingLocus_restrictₛₗ {U W : Opens X.carrier} (hWU : W ≤ U) (t : L.val.obj (op U)) :
    generatingLocus L (L.val.restrictₛₗ (homOfLE hWU).op t)
      = generatingLocus L t ∩ (W : Set X.carrier) := by
  ext z
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨⟨hWU hz, (grpGerm_restrictₛₗ L hWU t z hz) ▸ h⟩, hz⟩
  · rintro ⟨h, hz⟩
    exact ⟨hz, (grpGerm_restrictₛₗ L hWU t z hz).symm ▸
      notMem_maximalIdeal_smul_of_mem_generatingLocus L h (hWU hz)⟩

/-- **Multiplying a section by a unit does not move its generating locus.** This is the use the
last paragraph of [Stacks, Tag 0BD7] makes of its uniqueness statement: two meromorphic functions
`g` and `g'` on the base differing by a unit give sections `φ^*(g) s` and `φ^*(g') s` generating
`ℒ` at the same points. -/
theorem generatingLocus_smul_of_isUnit {U : Opens X.carrier} {c : X.presheaf.obj (op U)}
    (hc : IsUnit c) (t : L.val.obj (op U)) :
    generatingLocus L (c • t) = generatingLocus L t := by
  have key : ∀ (z : X.carrier) (hz : z ∈ U),
      (grpGerm X L.val z U hz (c • t) ∈
        maximalIdeal (ringStalk X z) • (⊤ : Submodule (ringStalk X z) (grpStalk X L.val z))) ↔
      (grpGerm X L.val z U hz t ∈
        maximalIdeal (ringStalk X z) • (⊤ : Submodule (ringStalk X z) (grpStalk X L.val z))) := by
    intro z hz
    rw [Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul]
    exact Submodule.smul_mem_iff_of_isUnit _ (hc.map (ringGerm X z U hz))
  ext z
  exact ⟨fun h => h.elim fun hz h' => ⟨hz, fun hm => h' ((key z hz).mpr hm)⟩,
    fun h => h.elim fun hz h' => ⟨hz, fun hm => h' ((key z hz).mp hm)⟩⟩

/-- **Generating at a point is a property of the germ, up to a unit.** A section whose germ at
`z` is a unit multiple of the germ of a section generating there generates there too. This is
`Stacks.SheafOfModules.generatingLocus_smul_of_isUnit` read on one stalk, which is the shape the
penultimate paragraph of [Stacks, Tag 0BD7] produces: an identity between germs at one point,
with no common open on which the two sections are both defined. -/
theorem mem_generatingLocus_of_grpGerm_eq_smul {U U' : Opens X.carrier}
    {t : L.val.obj (op U)} {t' : L.val.obj (op U')} {z : X.carrier}
    (hz : z ∈ U) (hz' : z ∈ U') {u : ringStalk X z} (hu : IsUnit u)
    (h : grpGerm X L.val z U hz t = u • grpGerm X L.val z U' hz' t')
    (ht' : z ∈ generatingLocus L t') :
    z ∈ generatingLocus L t :=
  mem_generatingLocus L hz fun hm =>
    notMem_maximalIdeal_smul_of_mem_generatingLocus L ht' hz'
      ((Submodule.smul_mem_iff_of_isUnit _ hu).mp (h ▸ hm))

/-- **Two sections whose restrictions to a common open differ by a unit generate at the same
points of that open.** The bridge from the source's uniqueness statement — "`g` and `g'` differ
multiplicatively by an element of `𝒪_{Y, y}^*`" — to the agreement hypothesis consumed by
`Stacks.InvertiblePullback.mem_generatingLocus_of_mem_fiber`: the fibre over `y` is contained in
the preimage of a neighbourhood of `y` on which the unit is defined, and inside that preimage the
two loci coincide. -/
theorem mem_generatingLocus_iff_of_restrictₛₗ_eq_smul
    {U U' W : Opens X.carrier} {t : L.val.obj (op U)} {t' : L.val.obj (op U')}
    (hWU : W ≤ U) (hWU' : W ≤ U') {c : X.presheaf.obj (op W)} (hc : IsUnit c)
    (hcc : L.val.restrictₛₗ (homOfLE hWU).op t = c • L.val.restrictₛₗ (homOfLE hWU').op t')
    {z : X.carrier} (hz : z ∈ W) :
    z ∈ generatingLocus L t ↔ z ∈ generatingLocus L t' := by
  have h3 : generatingLocus L t ∩ (W : Set X.carrier)
      = generatingLocus L t' ∩ (W : Set X.carrier) := by
    rw [← generatingLocus_restrictₛₗ L hWU t, ← generatingLocus_restrictₛₗ L hWU' t', hcc,
      generatingLocus_smul_of_isUnit L hc]
  exact ⟨fun h => ((Set.ext_iff.mp h3 z).mp ⟨h, hz⟩).1,
    fun h => ((Set.ext_iff.mp h3 z).mpr ⟨h, hz⟩).1⟩

section Pairing

variable {N : SheafOfModules.{u} (structureSheafRing X)}

/-- **The generating locus through a trivialization.** A point lies in the generating locus of
`t ∈ ℒ(U)` exactly when `t` pairs with some section of `𝒩` to the unit section on a neighbourhood
of the point inside `U`. This is
`Stacks.SheafOfModules.mem_nonvanishingLocus_iff` for a section defined on an open.

The trivialization is an explicit argument: `Stacks.SheafOfModules.isOpen_generatingLocus`
obtains it at the `Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf` spelling
of the ring sheaf, which an application of this lemma crosses and a rewrite inside its proof does
not. -/
theorem mem_generatingLocus_iff_exists_tensorPairing
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      (L)).obj (N)) ≅ SheafOfModules.unit (structureSheafRing X))
    {U : Opens X.carrier} (t : L.val.obj (op U)) (z : X.carrier) :
    z ∈ generatingLocus L t ↔
      ∃ (W : Opens X.carrier) (_ : z ∈ W) (hWU : W ≤ U) (b : N.val.obj (op W)),
        tensorPairing ψ W (L.val.restrictₛₗ (homOfLE hWU).op t) b = unitSection X W := by
  constructor
  · rintro ⟨hzU, hz⟩
    exact exists_le_tensorPairing_eq_unitSection ψ t z hzU hz
  · rintro ⟨W, hzW, hWU, b, hab⟩
    refine ⟨hWU hzW, ?_⟩
    have hne := notMem_smul_of_tmul_eq_one (stalkPairing ψ z)
      (grpGerm X L.val z W hzW (L.val.restrictₛₗ (homOfLE hWU).op t))
      (grpGerm X N.val z W hzW b) (by
        rw [stalkPairing_germ, hab]
        exact map_one (ringGerm X z W hzW))
    exact grpGerm_restrictₛₗ L hWU t z hzW ▸ hne

end Pairing

/-- **The generating locus is open**, equivalently the set `Z` of the last paragraph of
[Stacks, Tag 0BD7] is closed. This is the openness clause of [Stacks, Tag 01CY] for a section
defined on an open rather than globally, which is the form Tag 0BD7 needs: there the section
`φ^*(g) s` is regular only on a neighbourhood of the fibre. -/
theorem isOpen_generatingLocus [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U)) : IsOpen (generatingLocus L t) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨W, hzW, hWU, b, hab⟩ := (mem_generatingLocus_iff_exists_tensorPairing L ψ t z).mp hz
  exact ⟨W, fun y hy =>
    (mem_generatingLocus_iff_exists_tensorPairing L ψ t y).mpr ⟨W, hy, hWU, b, hab⟩,
    W.isOpen, hzW⟩

/-- **A section generating at every point of an open is a chart generator over it.** The form in
which `Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections` hands its chart to the
descent: the open is the whole generating locus, so no containment has to be checked. -/
theorem nonempty_generatorSections_of_coe_eq_generatingLocus
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U)) (W : Opens X.carrier)
    (hW : (W : Set X.carrier) = generatingLocus L t) :
    Nonempty (GeneratorSections X L W) := by
  have hWU : W ≤ U := fun _ hz => generatingLocus_le L t (hW.subset hz)
  exact ⟨generatorSectionsOfForallGermNotMemMaximalIdeal L t W hWU fun z hz =>
    notMem_maximalIdeal_smul_of_mem_generatingLocus L (hW.subset hz) (hWU hz)⟩

end Stacks.SheafOfModules

namespace Stacks.InvertiblePullback

open Stacks.SheafOfModules

variable {X Y : Scheme.{u}}

/-- **An integral fibre is an irreducible subset of the source.** Hypothesis (2) of
[Stacks, Tag 0BD7] is integrality of the fibres of `φ`; what the chart argument uses is that
`φ^{-1}(y)`, as a subspace of `X`, is irreducible, which is the range of the closed immersion of
the scheme-theoretic fibre. -/
theorem isIrreducible_preimage_singleton_of_isIntegral_fiber (f : X ⟶ Y) (y : Y)
    [AlgebraicGeometry.IsIntegral (f.fiber y)] : IsIrreducible (f.base ⁻¹' {y}) := by
  rw [← f.range_fiberι y, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (f.fiber y)).image (f.fiberι y).base
    (f.fiberι y).continuous.continuousOn

variable (f : X ⟶ Y) (L : X.Modules)
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
  {ι : Type*} {V : ι → Opens X.toRingedSpace.carrier} (t : ∀ i, L.val.obj (op (V i)))
  (hex : ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i))
  (hirr : ∀ y : Y, IsIrreducible (f.base ⁻¹' {y}))
  (hagree : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∀ z : X.toRingedSpace.carrier, f.base z = f.base x →
        (z ∈ generatingLocus L (t i) ↔ z ∈ generatingLocus L (t j)))

include hex hirr hagree in
/-- **The generating locus is saturated: the set `Z` of [Stacks, Tag 0BD7] is a union of
fibres.** If `φ^*(g_i) s` generates `ℒ` at `z` then it generates `ℒ` at every point of the fibre
through `z`.

This is the fibre-irreducibility argument of the source. The hypotheses are the two properties
the penultimate paragraph of that proof establishes for the family: `hex`, that *some* member of
the family generates at each point of `X`, and `hagree`, that two members generating at a common
point of a fibre generate at the same points of that fibre. Given `z` in the locus of `t i` and
`z'` in the same fibre, `hex` supplies a `t j` generating at `z'`; the two loci are open
(`Stacks.SheafOfModules.isOpen_generatingLocus`) and meet the fibre at `z` and at `z'`
respectively, so irreducibility of the fibre produces a point `x''` of the fibre lying in both;
and `hagree` at `x''` then transfers `z' ∈ generatingLocus L (t j)` to
`z' ∈ generatingLocus L (t i)`. -/
theorem mem_generatingLocus_of_mem_fiber (i : ι) {z z' : X.toRingedSpace.carrier}
    (hzz : f.base z = f.base z') (hz : z ∈ generatingLocus L (t i)) :
    z' ∈ generatingLocus L (t i) := by
  obtain ⟨j, hz'⟩ := hex z'
  obtain ⟨x, hxF, hxi, hxj⟩ := (hirr (f.base z')).2 _ _
    (isOpen_generatingLocus L (t i)) (isOpen_generatingLocus L (t j))
    ⟨z, hzz, hz⟩ ⟨z', rfl, hz'⟩
  exact (hagree i j x hxi hxj z' hxF.symm).mpr hz'

include hex hirr hagree in
/-- **Saturation as `Z = φ^{-1}(T)`.** The generating locus is the preimage of its image, so its
complement — the source's `Z` — is the preimage of a subset `T` of the base. -/
theorem preimage_image_generatingLocus (i : ι) :
    f.base ⁻¹' (f.base '' generatingLocus L (t i)) = generatingLocus L (t i) :=
  Set.Subset.antisymm
    (fun _ ⟨_, hw, hwz⟩ => mem_generatingLocus_of_mem_fiber f L t hex hirr hagree i hwz hw)
    (Set.subset_preimage_image _ _)

include hex hirr hagree in
/-- **The chart of [Stacks, Tag 0BD7].** For `φ` flat with nonempty fibres and quasi-compact or
locally of finite type over a locally Noetherian base — hypotheses (3) and (4) of the tag — every
point `y` of the base has an open neighbourhood whose preimage *is* the generating locus of one
member of the family.

The chart is `Y ∖ T` for `T` the image of the source's `Z`: `Z` is closed because the generating
locus is open, and `φ^{-1}(T) = Z` because the locus is saturated, so `T` is closed by
`AlgebraicGeometry.isClosed_of_isClosed_preimage_of_flat` (Tag 02JY in the quasi-compact case,
Tag 01UA in the finite type case). The equation in the conclusion is the point: the containment
`φ^{-1}(chart y) ⊆ {generates}` that a chart datum needs is an equality here, obtained rather
than chosen. -/
theorem exists_chart_coe_preimage_eq_generatingLocus [IsLocallyNoetherian Y] [Flat f]
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    ∃ chart : Y → Y.Opens, (∀ y, y ∈ chart y) ∧
      ∀ y, ∃ i, ((f ⁻¹ᵁ chart y : X.Opens) : Set X.toRingedSpace.carrier)
        = generatingLocus L (t i) := by
  classical
  have key : ∀ y : Y, ∃ (A : Y.Opens) (_ : y ∈ A) (i : ι),
      ((f ⁻¹ᵁ A : X.Opens) : Set X.toRingedSpace.carrier) = generatingLocus L (t i) := by
    intro y
    obtain ⟨x0⟩ := hfiber y
    have hfx : f.fiberι y x0 ∈ f.base ⁻¹' {y} := by
      rw [← f.range_fiberι y]
      exact ⟨x0, rfl⟩
    obtain ⟨i, hi⟩ := hex (f.fiberι y x0)
    have hopen : IsOpen (f.base '' generatingLocus L (t i)) := by
      rw [← isClosed_compl_iff]
      refine isClosed_of_isClosed_preimage_of_flat f hfiber hfinite ?_
      rw [Set.preimage_compl, preimage_image_generatingLocus f L t hex hirr hagree i]
      exact (isOpen_generatingLocus L (t i)).isClosed_compl
    exact ⟨⟨f.base '' generatingLocus L (t i), hopen⟩, ⟨_, hi, hfx⟩, i,
      preimage_image_generatingLocus f L t hex hirr hagree i⟩
  choose A hA i hi using key
  exact ⟨A, hA, fun y => ⟨i y, hi y⟩⟩

include hex hirr hagree in
/-- **The chart datum of [Stacks, Tag 0BD7].** The conclusion is exactly the `chart` and `gen`
arguments of
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isIntegral_fiber`. -/
theorem exists_chart_nonempty_generatorSections [IsLocallyNoetherian Y] [Flat f]
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    ∃ chart : Y → Y.Opens, (∀ y, y ∈ chart y) ∧
      ∀ y, Nonempty (GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ chart y)) := by
  obtain ⟨chart, hmem, hpre⟩ :=
    exists_chart_coe_preimage_eq_generatingLocus f L t hex hirr hagree hfiber hfinite
  refine ⟨chart, hmem, fun y => ?_⟩
  obtain ⟨i, hi⟩ := hpre y
  exact nonempty_generatorSections_of_coe_eq_generatingLocus L (t i) _ hi

end Stacks.InvertiblePullback

end
