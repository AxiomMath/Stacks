module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFormalSpectrumAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautNotRepresentable
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf

/-!
# Stacks 0AN5 for a formal spectrum which is an affine formal algebraic space

Let `S` be a scheme and `φ : A → B` a continuous map of weakly admissible topological rings over
`S`. **Stacks 0AN5** says that the following are equivalent: (1) `Spf(φ)` is representable by
algebraic spaces, (2) `Spf(φ)` is representable (by schemes), (3) `φ` is taut.

In the source the formal spectrum is, by Definition 0AIF, *the affine formal algebraic space*
`Spf(A) = colim Spec(A/I)`, and an affine formal algebraic space (Definition 0AI7) satisfies the
set-theoretic condition of Remark 0AIS: some object `U` of `(Sch/S)_fppf` surjects onto it. The
proof of Stacks 0AN5 uses this — its equivalence (1) ⟺ (2) is Lemma 0AKN, a statement about
morphisms of affine formal algebraic spaces. In this library `formalSpectrum` is the colimit
alone, and whether it is an affine formal algebraic space is a property of the chosen site. This
file proves the tag with that property of `Spf(B)` as in the source, and nothing else: no
regularity of the cutoff of the site, no countability, no bound on the stages, and no
hypothesis on `Spf(A)`.

The input it needs is that the set-theoretic condition bounds the ring. If `h_U ⟶ Spf(B)` is an
epimorphism of sheaves, then precomposition with it is injective on morphisms into the affine
line `𝔸¹_S`; every `b ∈ B` defines such a morphism `Spf(B) ⟶ 𝔸¹_S` (the function `b` on each
stage `Spec(B/K)`), and different elements give different morphisms because `B` is separated.
Morphisms `h_U ⟶ 𝔸¹_S` are the global functions on `U`. So `#B ≤ #Γ(U, 𝒪_U) ≤ 2 ^ size U`,
which is below the cutoff because `U` is an object of the site and the cutoff is a strong limit
(`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_satisfiesSetTheoreticCondition_formalSpectrum`).
A ring below the cutoff has all its stages, and their coproduct, in the site
(`AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff`), which is the size bound that
the implication (3) ⟹ (2) consumes
(`AlgebraicGeometry.FormalSpace.relative_isAffineHom_formalSpectrumMap_of_isTaut`).

So for a weakly admissible `B` the three conditions "`Spf(B)` is an affine formal algebraic
space", "`Spf(B)` satisfies the set-theoretic condition of Remark 0AIS" and "the coproduct of the
stages of `Spf(B)` is an object of the site" (the proviso of Remark 0AIE) are equivalent
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum_iff_hasLargeSite`).

Without the property the statement is false over a site whose cutoff is singular
(`AlgebraicGeometry.FormalSpace.exists_isTaut_not_relativelyRepresentable_of_cof_lt`); the target
ring of that counterexample is one whose formal spectrum is not an affine formal algebraic space
(`AlgebraicGeometry.FormalSpace.exists_not_isAffineFormalAlgebraicSpace_formalSpectrum_of_cof_lt`).

## Main results

* `AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_satisfiesSetTheoreticCondition_formalSpectrum`:
  a weakly admissible ring whose formal spectrum satisfies the set-theoretic condition of
  Remark 0AIS has cardinality below the cutoff of the site.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum_iff_hasLargeSite`.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_isAffineFormalAlgebraicSpace`:
  **Stacks 0AN5**.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section AffineLine

variable {C : Type u} [CommRing C] [TopologicalSpace C]

/-- An element `c` of `C`, as a function on the stage `Spec (C ⧸ K)` of `Spf C`: the morphism
from that stage to the affine line over `S` given by the residue class of `c`. -/
def stageToAffineLine (E : QuotientSystem B S hS C) (c : C)
    (K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K }) :
    (BigAffineFppf.inclusion B S hS).obj (E.stage K) ⟶ Space.affineLineBigFppfOver B S hS :=
  Space.affineLineChartPoints B S hS _
    ((Scheme.ΓSpecIso (CommRingCat.of (C ⧸ K.1))).inv.hom (Ideal.Quotient.mk K.1 c))

/-- The functions `c` on the stages of `Spf C` are compatible with the transition morphisms. -/
theorem transition_comp_stageToAffineLine (E : QuotientSystem B S hS C) (c : C)
    {J L : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K }} (h : J.1 ≤ L.1) :
    (BigAffineFppf.inclusion B S hS).map (E.transition h) ≫ stageToAffineLine B S hS E c J =
      stageToAffineLine B S hS E c L := by
  refine (Space.affineLineChartPoints_natural B S hS _ _).symm.trans ?_
  refine congrArg (Space.affineLineChartPoints B S hS _) ?_
  show ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (C ⧸ J.1))).inv.hom (Ideal.Quotient.mk J.1 c)) =
    (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ L.1))).inv.hom (Ideal.Quotient.mk L.1 c)
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

/-- An element `c` of `C` as a morphism from `Spf C` to the affine line over `S`: the colimit of
the functions `c` on the stages. -/
def formalSpectrumToAffineLine (E : QuotientSystem B S hS C) (c : C) :
    formalSpectrum E ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      (Space.affineLineBigFppfOver B S hS) :=
  colimit.desc (formalSpectrumDiagram E)
    { pt := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (Space.affineLineBigFppfOver B S hS)
      ι :=
        { app := fun K => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            (stageToAffineLine B S hS E c (OrderDual.ofDual K))
          naturality := fun K L f => by
            refine Eq.trans ?_ (Category.comp_id _).symm
            exact ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).symm.trans
              (congrArg _ (transition_comp_stageToAffineLine B S hS E c
                (J := OrderDual.ofDual L) (L := OrderDual.ofDual K) (leOfHom f))) } }

/-- The morphism `formalSpectrumToAffineLine` restricted to the stage `Spec(C/K)` of `Spf C` is
the function `c` on that stage. -/
theorem formalSpectrumInclusion_comp_formalSpectrumToAffineLine (E : QuotientSystem B S hS C)
    (c : C) (K : OrderDual { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K }) :
    formalSpectrumInclusion E K ≫ formalSpectrumToAffineLine B S hS E c =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (stageToAffineLine B S hS E c (OrderDual.ofDual K)) :=
  colimit.ι_desc _ _

variable [IsTopologicalRing C] [IsLinearTopology C C]

/-- **Different elements of a weakly admissible ring are different functions on its formal
spectrum.** Two elements of `C` defining the same morphism `Spf C ⟶ 𝔸¹_S` agree modulo every
weak ideal of definition, hence agree, `C` being separated and the weak ideals of definition a
fundamental system of neighbourhoods of `0`. -/
theorem formalSpectrumToAffineLine_injective (hC : TopologicalRing.IsWeaklyAdmissible C)
    (E : QuotientSystem B S hS C) :
    Function.Injective (formalSpectrumToAffineLine B S hS E) := by
  intro c c' h
  have hK : ∀ K : Ideal C, TopologicalRing.IsWeakIdealOfDefinition K → c - c' ∈ K := by
    intro K hK
    have h1 := congrArg (fun φ => formalSpectrumInclusion E (OrderDual.toDual ⟨K, hK⟩) ≫ φ) h
    simp only [formalSpectrumInclusion_comp_formalSpectrumToAffineLine] at h1
    have h2 := (Space.affineLineChartPoints B S hS _).injective
      ((sheafifiedYonedaFF B S hS).map_injective h1)
    change (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ K))).inv.hom (Ideal.Quotient.mk K c) =
      (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ K))).inv.hom (Ideal.Quotient.mk K c') at h2
    have h3 : Ideal.Quotient.mk K c = Ideal.Quotient.mk K c' := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ K))).hom.hom h2
      rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
    exact Ideal.Quotient.eq.mp h3
  have _ : T2Space C := hC.2.2
  have hsp : (c - c') ⤳ 0 := by
    rw [specializes_iff_pure]
    intro s hs
    obtain ⟨K, hK', hKs⟩ :=
      (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).mem_iff.mp hs
    exact Filter.mem_pure.mpr (hKs (hK K hK'))
  exact sub_eq_zero.mp hsp.eq

/-- **The set-theoretic condition of Remark 0AIS bounds the ring.** Let `C` be a weakly
admissible topological ring over `S` whose formal spectrum satisfies the set-theoretic condition
of Stacks 0AIS, so that the sheaf `h_U` of some object `U` of the site surjects onto `Spf C`. Then
`#C` is below the size cutoff of the site.

Precomposition with the surjection `h_U ⟶ Spf C` is injective on morphisms to the affine line
`𝔸¹_S`, an element of `C` is such a morphism out of `Spf C`
(`AlgebraicGeometry.FormalSpace.formalSpectrumToAffineLine`), different elements giving
different morphisms (`AlgebraicGeometry.FormalSpace.formalSpectrumToAffineLine_injective`), and
the morphisms `h_U ⟶ 𝔸¹_S` are the global functions on `U`
(`AlgebraicGeometry.Space.affineLineChartPoints`). So `#C ≤ #Γ(U, 𝒪_U) ≤ 2 ^ size U`, which is
below the cutoff because `U` lies in the site and the cutoff is a strong limit. -/
theorem mk_lt_cutoff_of_satisfiesSetTheoreticCondition_formalSpectrum
    (hC : TopologicalRing.IsWeaklyAdmissible C) (E : QuotientSystem B S hS C)
    (hE : SatisfiesSetTheoreticCondition B S hS (formalSpectrum E)) : #C < B.cutoff := by
  obtain ⟨U, -, hU, -, ⟨eU⟩, -, f, hf, -⟩ := hE
  have _ := hf
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let L := Space.affineLineBigFppfOver B S hS
  let Ψ := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  let eU' : hU ≅ J.uliftYoneda.{u + 1}.obj U :=
    (fullyFaithfulSheafToPresheaf J _).preimageIso eU
  let F : C → Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := fun c =>
    (Space.affineLineChartPoints B S hS U).symm (ULift.down
      (J.uliftYonedaEquiv (eU'.inv ≫ f ≫ formalSpectrumToAffineLine B S hS E c ≫ Ψ.hom.app L)))
  have hF : Function.Injective F := by
    intro c c' h
    apply formalSpectrumToAffineLine_injective B S hS hC E
    have h1 := J.uliftYonedaEquiv.injective
      (ULift.ext ((Space.affineLineChartPoints B S hS U).symm.injective h))
    simpa only [cancel_epi, cancel_mono] using h1
  calc #C ≤ #Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := mk_le_of_injective hF
    _ ≤ 2 ^ ((BigFppfOver.toScheme B S hS).obj U).size :=
        Scheme.mk_sections_le_two_pow_size _ ⊤
    _ < B.cutoff := B.cutoff_isStrongPrelimit U.left.property

/-- A weakly admissible topological ring over `S` whose formal spectrum satisfies the
set-theoretic condition of Remark 0AIS has the coproduct of all its stages `Spec (C ⧸ K)` in
the site: the ring is below the cutoff by
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_satisfiesSetTheoreticCondition_formalSpectrum`,
and then so is that coproduct (`AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff`). -/
theorem hasLargeSite_of_satisfiesSetTheoreticCondition_formalSpectrum
    (hC : TopologicalRing.IsWeaklyAdmissible C) (E : QuotientSystem B S hS C)
    (hE : SatisfiesSetTheoreticCondition B S hS (formalSpectrum E)) : E.HasLargeSite :=
  hasLargeSite_of_mk_lt_cutoff E
    (mk_lt_cutoff_of_satisfiesSetTheoreticCondition_formalSpectrum B S hS hC E hE)

/-- **When the formal spectrum is an affine formal algebraic space.** For a weakly admissible
topological ring `C` over `S` the following are equivalent:

* `Spf C` is an affine formal algebraic space (Definitions 0AIF and 0AI7);
* the coproduct `∐_K Spec (C ⧸ K)` of its stages is an object of the site, the proviso under
  which Remark 0AIE and observation (1) of Remark 0AIS obtain the set-theoretic condition.

Forwards this is
`AlgebraicGeometry.FormalSpace.hasLargeSite_of_satisfiesSetTheoreticCondition_formalSpectrum`,
backwards `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`. -/
theorem isAffineFormalAlgebraicSpace_formalSpectrum_iff_hasLargeSite
    (hC : TopologicalRing.IsWeaklyAdmissible C) (E : QuotientSystem B S hS C) :
    IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) ↔ E.HasLargeSite :=
  ⟨fun h => hasLargeSite_of_satisfiesSetTheoreticCondition_formalSpectrum B S hS hC E h.1,
    isAffineFormalAlgebraicSpace_formalSpectrum hC E⟩

end AffineLine

section Tfae

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Stacks 0AN5.** Let `S` be a scheme and `φ : A ⟶ C` a continuous homomorphism of weakly
admissible topological rings over `S`, the formal spectrum `Spf C` being an affine formal
algebraic space as in Definition 0AIF. The following are equivalent:

1. `Spf φ : Spf C ⟶ Spf A` is representable by algebraic spaces;
2. `Spf φ` is representable (by objects of the site);
3. `φ` is taut.

*The hypothesis `hE`.* Definition 0AIF of the source defines `Spf(B)` to be "the affine formal
algebraic space `colim Spec(B/I)`", and an affine formal algebraic space satisfies, by
Definition 0AI7, the set-theoretic condition of Remark 0AIS; the source's proof of (1) ⟺ (2)
is Lemma 0AKN, a statement about morphisms of affine formal algebraic spaces. In this library
`formalSpectrum E` is the colimit alone, and `hE` records that it is an affine formal algebraic
space in the sense of Definition 0AI7 (`AlgebraicGeometry.IsAffineFormalAlgebraicSpace`). This
is the source's own notion of `Spf(B)`, not an extra condition: for weakly admissible `C` it is
equivalent to the coproduct of the stages lying in the site
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum_iff_hasLargeSite`),
the proviso of Remark 0AIE. Nothing is asked of `Spf A`, of the cutoff of the site, or of the
stages of either ring.

*Why it cannot be dropped.* Over a site whose cutoff is singular there are taut homomorphisms
with `Spf φ` not representable
(`AlgebraicGeometry.FormalSpace.exists_isTaut_not_relativelyRepresentable_of_cof_lt`), and the
formal spectrum of the target of such a homomorphism is not an affine formal algebraic space
(`AlgebraicGeometry.FormalSpace.exists_not_isAffineFormalAlgebraicSpace_formalSpectrum_of_cof_lt`).

*Proof.* (1) ⟹ (3) is
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap` and
(2) ⟹ (1) is
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`, both
with no set-theoretic input. (3) ⟹ (2) is
`AlgebraicGeometry.FormalSpace.relative_isAffineHom_formalSpectrumMap_of_isTaut`: a point of
`Spf A` out of an affine object factors through a stage `Spec(A/I)` (Stacks 0AIA), over which the
base change is `Spec(C/J(I))` with `J(I)` the closure of `φ(I)C`, open by tautness; the charts
over the affine opens of an arbitrary test object glue inside the site because each stage of
`Spf C` is bounded by the coproduct of all of them, an object of the site by `hE`. -/
@[stacks 0AN5 "the equivalence of (1), (2) and (3), with Spf(B) an affine formal algebraic \
space as in Definition 0AIF"]
theorem formalSpectrumMap_tfae_of_isAffineFormalAlgebraicSpace
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (hE : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E)) (f : ContinuousHom D E) :
    List.TFAE
      [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom,
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
          (formalSpectrumMap hA f),
        RingHom.IsTaut f.toRingHom] :=
  formalSpectrumMap_tfae_of_imp_relativelyRepresentable B S hS hA hC D E f fun hf =>
    (relative_isAffineHom_formalSpectrumMap_of_isTaut hA hC
      (hasLargeSite_of_satisfiesSetTheoreticCondition_formalSpectrum B S hS hC E hE.1)
      f hf).rep

end Tfae

/-- **Over a site with singular cutoff, a formal spectrum need not be an affine formal algebraic
space.** Over a big fppf site whose size cutoff is singular there are a scheme `S` of the site
and a weakly admissible topological ring `C` over `S` whose formal spectrum is not an affine
formal algebraic space. The ring is the target of the taut homomorphism of
`AlgebraicGeometry.FormalSpace.exists_isTaut_not_relativelyRepresentable_of_cof_lt`, whose formal
spectrum map is not representable; were `Spf C` an affine formal algebraic space,
`AlgebraicGeometry.FormalSpace.formalSpectrumMap_tfae_of_isAffineFormalAlgebraicSpace` would make
it representable. -/
theorem exists_not_isAffineFormalAlgebraicSpace_formalSpectrum_of_cof_lt
    (hsing : B.cutoff.ord.cof < B.cutoff) :
    ∃ (S : Scheme.{u}) (hS : B.Contains S) (C : Type u) (_ : CommRing C)
      (_ : TopologicalSpace C) (_ : IsTopologicalRing C) (_ : IsLinearTopology C C)
      (_ : TopologicalRing.IsWeaklyAdmissible C) (E : QuotientSystem B S hS C),
      ¬ IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) := by
  obtain ⟨S, hS, A, _, _, _, _, C, _, _, _, _, hA, hC, D, E, f, htaut, hnot⟩ :=
    exists_isTaut_not_relativelyRepresentable_of_cof_lt B hsing
  refine ⟨S, hS, C, inferInstance, inferInstance, inferInstance, inferInstance, hC, E,
    fun h => hnot ?_⟩
  exact ((formalSpectrumMap_tfae_of_isAffineFormalAlgebraicSpace B S hS hA hC D E h f).out 3 2).mp
    htaut


end AlgebraicGeometry.FormalSpace

end
