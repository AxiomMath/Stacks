module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.AffineFormalOpenBasis
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinitionCutOut
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimitFppf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimitIff
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionLocality
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionPoints

/-!
# `h_𝔛` is a colimit along thickenings iff `𝔛` has a fundamental system of ideals of definition

**Stacks 0AIW** concludes: the formal algebraic space `h_𝔛` associated to a quasi-compact formal
scheme `𝔛` à la EGA is a colimit of schemes as in Lemma 0AIU — a colimit in fppf sheaves,
`McQuillanFormalScheme.IsFppfColimitOfThickenings` — if and only if there exists a fundamental
system of ideals of definition for `𝔛`. The source deduces it from the corresponding statement of
Remark 0AIV for formal schemes in the sense of McQuillan
(`AlgebraicGeometry.McQuillanFormalScheme`
`.isFppfColimitOfThickenings_iff_exists_isFundamentalSystem`)
and the eventual ideals of definition. This file assembles the deduction.

* A formal scheme à la EGA is one in the sense of McQuillan
  (`AlgebraicGeometry.IsFormalScheme.isMcQuillanFormalScheme`), and its weak affine formal open
  subschemes are exactly its affine formal open subschemes
  (`AlgebraicGeometry.IsFormalScheme.isWeakAffineFormalOpen_eq`): a weak affine formal open is
  quasi-compact, hence covered by finitely many affine formal opens inside it, so the sections over
  it are pre-admissible and the weakly admissible ring of a chart is admissible.
* Given the colimit, Remark 0AIV produces a nonempty directed fundamental system of weak ideals of
  definition cut out by their sections over the affine formal opens; the members below a suitable
  one are ideals of definition over every affine formal open
  (`exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isCutOutOn`).
* Conversely a fundamental system of ideals of definition is one of weak ideals of definition.

The "only if" direction holds with the source's definitions, for arbitrary ideal sheaves. The
source defines an ideal of definition sectionwise (`IdealSheaf.IsIdealOfDefinitionOn`), without the
EGA requirement that it be `I^Δ` over an affine formal open `Spf A`. In the "if" direction the
ideals of definition are taken among those cut out by their sections over the affine formal opens
(`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.IsCutOutOn`), the analogue of that
requirement: they are the ideal sheaves `ℐ` for which `(𝔛, 𝒪_𝔛/ℐ)` is the thickening of `h_𝔛` that
the source attaches to `ℐ`. For arbitrary ideal sheaves the source's argument fails at both of its
steps (`exists_isWeakIdealOfDefinitionOn_forall_thickening_ideal_ne` for the correspondence and
`not_forall_exists_isIdealOfDefinitionOn_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn` for the
eventual ideals of definition), and the "if" direction itself is false for them
(`AlgebraicGeometry.FormalScheme.not_forall_isFppfColimitOfThickenings_of_exists`, through the
twisted double `AlgebraicGeometry.TwistedDouble.𝔛`).

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.isPreAdmissible_iSup`: the sections over a
  finite union of opens with pre-admissible sections are pre-admissible.
* `AlgebraicGeometry.IsFormalScheme.isAffineFormalOpen_of_isWeakAffineFormalOpen`.
* `AlgebraicGeometry.FormalScheme.isFppfColimitOfThickenings_iff`: **Stacks 0AIW**, the final
  conclusion, with the colimit in fppf sheaves.
* `AlgebraicGeometry.FormalScheme`
  `.exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFppfColimitOfThickenings`: its "only if"
  direction for arbitrary ideal sheaves.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopologicalRing

namespace AlgebraicGeometry

universe u

/-- The sections over a finite union of opens are pre-admissible as soon as the sections over the
members are: the intersection of the preimages of ideals of definition of the members is open,
and its powers are small because a neighbourhood of zero over the union contains the sections
whose restrictions to the members lie in given neighbourhoods of zero there. -/
theorem LocallyTopologicallyRingedSpace.isPreAdmissible_iSup {X : LTRS.{u}} {ι : Type u}
    [Finite ι] (U : ι → Opens X) (hU : ∀ i, IsPreAdmissible (X.presheaf.obj (op (U i))).α) :
    IsPreAdmissible (X.presheaf.obj (op (iSup U))).α := by
  classical
  choose J hJ using hU
  let res : ∀ i, (X.presheaf.obj (op (iSup U))).α →+* (X.presheaf.obj (op (U i))).α :=
    fun i => (X.presheaf.map (homOfLE (le_iSup U i)).op).1
  refine ⟨⨅ i, (J i).comap (res i), ?_, fun N hN => ?_⟩
  · rw [Submodule.coe_iInf]
    exact isOpen_iInter_of_finite fun i =>
      (hJ i).1.preimage (X.presheaf.map (homOfLE (le_iSup U i)).op).2
  · obtain ⟨W, hW, hWN⟩ := IdealSheaf.exists_forall_restrict_mem_subset U hN
    choose n hn using fun i => (hJ i).2 (W i) (hW i)
    obtain ⟨m, hm⟩ := Finite.exists_le n
    refine ⟨m, fun x hx => hWN x fun i => hn i ?_⟩
    have hx' : res i x ∈ (Ideal.map (res i) (⨅ i, (J i).comap (res i))) ^ m := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    exact Ideal.pow_le_pow_right (hm i)
      (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (iInf_le _ i)) m hx')

/-- An ideal of definition pulls back to an ideal of definition along a ring isomorphism which is a
homeomorphism. -/
theorem _root_.TopologicalRing.isIdealOfDefinition_comap_of_homeomorph {R S : Type u} [CommRing R]
    [TopologicalSpace R] [CommRing S] [TopologicalSpace S] (e : R ≃+* S) (h : R ≃ₜ S)
    (he : ∀ r, h r = e r) {J : Ideal S} (hJ : IsIdealOfDefinition J) :
    IsIdealOfDefinition (J.comap e.toRingHom) := by
  have hcont : Continuous (e : R → S) := h.continuous.congr he
  refine ⟨hJ.1.preimage hcont, fun N hN => ?_⟩
  have hN' : (h '' N) ∈ nhds (0 : S) := by
    have h0 : h 0 = 0 := by rw [he, map_zero]
    rw [← h0]
    exact h.isOpenMap.image_mem_nhds hN
  obtain ⟨n, hn⟩ := hJ.2 _ hN'
  refine ⟨n, fun r hr => ?_⟩
  have hmem : e r ∈ J ^ n := Ideal.le_comap_pow e.toRingHom n hr
  obtain ⟨r', hr', hr'e⟩ := hn hmem
  rw [he] at hr'e
  rwa [← e.injective hr'e]

/-- **A weak affine formal open subscheme of a formal scheme à la EGA is an affine formal open
subscheme.** It is quasi-compact, so finitely many affine formal open subschemes inside it cover
it, and the sections over it are therefore pre-admissible; the weakly admissible ring of a chart
is then admissible, and its McQuillan formal spectrum is its formal spectrum. -/
theorem IsFormalScheme.isAffineFormalOpen_of_isWeakAffineFormalOpen {X : LTRS.{u}}
    (hX : IsFormalScheme X) {W : Opens X} (hW : IsWeakAffineFormalOpen X W) :
    IsAffineFormalOpen X W := by
  classical
  choose U hUW hxU hU using fun x : W => hX.exists_isAffineFormalOpen_mem_le x.property
  obtain ⟨s, hs⟩ := hW.isCompact.elim_finite_subcover (fun x : W => (U x : Set X))
    (fun x => (U x).isOpen) fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hsup : ⨆ x : s, U x = W := by
    refine le_antisymm (iSup_le fun x => hUW x) fun x hx => ?_
    obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact (le_iSup (fun y : s => U y) ⟨y, hys⟩) hxy
  have hpre : IsPreAdmissible (X.presheaf.obj (op W)).α := by
    rw [← hsup]
    exact LocallyTopologicallyRingedSpace.isPreAdmissible_iSup (fun x : s => U x)
      fun x => isPreAdmissible_of_isAffineFormalOpen (hU x)
  obtain ⟨B, hlin, hB, ⟨e⟩⟩ := hW
  let χ : X.restrict W ≅ spfwLTRS B.α hB.1 := ltrsIsoOfPresheafedSpaceIso e
  obtain ⟨J, hJ⟩ := hpre
  have hBpre : IsPreAdmissible B.α :=
    ⟨_, TopologicalRing.isIdealOfDefinition_comap_of_homeomorph
      (weakChartSectionsRingEquiv B.α hB χ)
      (weakChartSectionsHomeomorph B.α hB χ) (fun _ => rfl) hJ⟩
  exact ⟨B, hlin, ⟨hBpre, hB.2.2, hB.2.1⟩, ⟨e ≪≫ (spfIsoSpfw B.α hBpre).symm⟩⟩

/-- On a formal scheme à la EGA the weak affine formal open subschemes are exactly the affine
formal open subschemes. -/
theorem IsFormalScheme.isWeakAffineFormalOpen_eq {X : LTRS.{u}} (hX : IsFormalScheme X) :
    IsWeakAffineFormalOpen X = IsAffineFormalOpen X :=
  funext fun _ => propext ⟨hX.isAffineFormalOpen_of_isWeakAffineFormalOpen,
    fun hW => hW.isWeakAffineFormalOpen⟩

/-- A formal scheme à la EGA, as a formal scheme in the sense of McQuillan
(`IsFormalScheme.isMcQuillanFormalScheme`). -/
def FormalScheme.toMcQuillanFormalScheme (X : FormalScheme.{u}) : McQuillanFormalScheme.{u} :=
  ⟨X.obj, X.property.isMcQuillanFormalScheme⟩

open LocallyTopologicallyRingedSpace in
/-- The Zariski form of `FormalScheme.isFppfColimitOfThickenings_iff`, through the auxiliary
notion `McQuillanFormalScheme.IsColimitOfThickenings` of Remark 0AIV in this library. -/
theorem FormalScheme.isColimitOfThickenings_iff (X : FormalScheme.{u}) [CompactSpace ↥X.obj] :
    X.toMcQuillanFormalScheme.IsColimitOfThickenings ↔ ∃ 𝒮 : Set (IdealSheaf X.obj),
      (∀ I ∈ 𝒮, I.IsCutOutOn (IsAffineFormalOpen X.obj)) ∧
        IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X.obj) := by
  have hX : IsFormalScheme X.obj := X.property
  have hclass : IsWeakAffineFormalOpen X.toMcQuillanFormalScheme.obj = IsAffineFormalOpen X.obj :=
    hX.isWeakAffineFormalOpen_eq
  refine ⟨fun h => ?_, fun ⟨𝒮, hC, hfund⟩ => ?_⟩
  · obtain ⟨𝒮, hne, hdir, hC, hfund⟩ :=
      IdealSheaf.exists_isFundamentalSystem_of_isColimitOfThickenings h
    rw [hclass] at hC hfund
    obtain ⟨𝒮', h𝒮', -, -, hfund'⟩ :=
      exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isCutOutOn hX 𝒮 hne hdir hfund hC
    exact ⟨𝒮', fun I hI => hC I (h𝒮' hI), hfund'⟩
  · refine (McQuillanFormalScheme.isColimitOfThickenings_iff _).mpr ⟨𝒮, ?_, ?_⟩
    · rw [hclass]
      exact hC
    · rw [hclass]
      exact
        isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_isFundamentalSystemOfIdealsOfDefinitionOn
          hfund

open LocallyTopologicallyRingedSpace in
/-- **Stacks 0AIW, the "only if" direction, for arbitrary ideal sheaves.** If the functor of points
`h_𝔛` of a quasi-compact formal scheme `𝔛` à la EGA is a colimit of schemes along thickenings in
fppf sheaves, as in Stacks 0AIU, then `𝔛` has a fundamental system of ideals of definition, with
the definitions of the source: ideal sheaves whose ideals of sections over every affine formal open
are ideals of definition, and a neighbourhood basis of zero there. -/
@[stacks 0AIW "the direction from colimit to fundamental system: for 𝔛 quasi-compact, if h_𝔛 \
is a colimit of schemes as in Lemma 0AIU (colimit in fppf sheaves) then there exists a \
fundamental system of ideals of definition for 𝔛, for ideal sheaves in the source's generality"]
theorem FormalScheme.exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFppfColimitOfThickenings
    (X : FormalScheme.{u}) [CompactSpace ↥X.obj]
    (h : X.toMcQuillanFormalScheme.IsFppfColimitOfThickenings) :
    ∃ 𝒮 : Set (IdealSheaf X.obj),
      IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X.obj) :=
  (X.isColimitOfThickenings_iff.mp
    ((McQuillanFormalScheme.isFppfColimitOfThickenings_iff _).mp h)).imp fun _ => And.right

open LocallyTopologicallyRingedSpace in
/-- **Stacks 0AIW.** The functor of points `h_𝔛` of a quasi-compact formal scheme `𝔛` à la EGA is a
colimit of schemes along thickenings in fppf sheaves, as in Stacks 0AIU, if and only if `𝔛` has a
fundamental system of ideals of definition cut out by their sections over the affine formal opens.

This is the corrected form of the remark. The "only if" direction holds without the cut-out
condition
(`FormalScheme.exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFppfColimitOfThickenings`).
The source's definition of an ideal of definition is sectionwise and does not ask for the cut-out
condition (the analogue of `ℐ|_𝔘 = ℐ(𝔘)^Δ` in EGA), and with it the "if" direction is false
(`FormalScheme.not_forall_isFppfColimitOfThickenings_of_exists`). -/
@[stacks 0AIW "corrected form: for 𝔛 quasi-compact, h_𝔛 is a colimit of schemes as in Lemma \
0AIU (colimit in fppf sheaves) iff there exists a fundamental system of ideals of definition for 𝔛 \
cut out by their sections over the affine formal opens (erratum in errata.md); the direction from \
fundamental system to colimit as printed is false: see \
FormalScheme.not_forall_isFppfColimitOfThickenings_of_exists; the direction from colimit to \
fundamental system holds for arbitrary ideal sheaves, \
exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFppfColimitOfThickenings"]
theorem FormalScheme.isFppfColimitOfThickenings_iff (X : FormalScheme.{u}) [CompactSpace ↥X.obj] :
    X.toMcQuillanFormalScheme.IsFppfColimitOfThickenings ↔ ∃ 𝒮 : Set (IdealSheaf X.obj),
      (∀ I ∈ 𝒮, I.IsCutOutOn (IsAffineFormalOpen X.obj)) ∧
        IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X.obj) :=
  (McQuillanFormalScheme.isFppfColimitOfThickenings_iff _).trans X.isColimitOfThickenings_iff

end AlgebraicGeometry

end
