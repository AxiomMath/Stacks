module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSheafCriterion

/-!
# The pullback of a small étale sheaf to the big fppf site of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `X` an algebraic space of `T`.
Write `π_X` for the morphism from the big étale topos of `X` to its small étale topos, `ε_X` for
the change of topology from the big fppf topos of `X` to its big étale topos, and
`a_X = π_X ∘ ε_X` (Stacks 0DGI). For a sheaf `F` on the small étale site of `X` the big étale
sheaf `π_X⁻¹F` is already an fppf sheaf, so `a_X⁻¹F = ε_X⁻¹π_X⁻¹F` is `π_X⁻¹F` read as an fppf
sheaf. This gives part (1) of Stacks 0DGF:
`ε_{X,*}a_X⁻¹F = π_X⁻¹F` and `a_{X,*}a_X⁻¹F = F`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.inverseImage_isSheafFor_of_isFpqcCovering`: `π_X⁻¹F`
  satisfies the sheaf condition for every fpqc covering family of the slice over `X` (the fpqc
  clause of Stacks 0DG7).
* `AlgebraicGeometry.BigFppfSpaceSite.isSheaf_bigToSmallEtale_inverseImage`: `π_X⁻¹F`, read on
  the big fppf slice at `X`, is a sheaf for the big fppf topology of `X`.
* `BigFppfSpaceSite.fppfToSmallEtale_inverseImage_comp_fppfToBigEtale_pushforwardIso`:
  `ε_{X,*} ∘ a_X⁻¹ ≅ π_X⁻¹`, the first clause of Stacks 0DGF (1).
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleMorphism_unit` and
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_inverseImage_comp_pushforwardIso`:
  the unit `F ⟶ a_{X,*}a_X⁻¹F` is an isomorphism, so `a_{X,*} ∘ a_X⁻¹ ≅ 𝟭`, the second clause
  of Stacks 0DGF (1); hence `a_X⁻¹` is fully faithful
  (`AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_inverseImage_fullyFaithful`).

## Implementation notes

The proof of the fpqc sheaf condition combines étale descent for
`π_X⁻¹F` with the reduction of the fpqc sheaf condition to finite affine fpqc coverings and the
fpqc sheaf condition for schemes (Stacks 09XN). The fppf sheaf condition follows because an fppf
covering is an fpqc covering (Stacks 0DFQ) and fpqc coverings are stable under base change: every
chosen fppf covering family of the site, lifted to the slice over `X`, generates a sieve of the
finest topology for which `π_X⁻¹F` is a sheaf.

Both isomorphisms of part (1) are inverses of adjunction units: the unit of `ε_X⁻¹ ⊣ ε_{X,*}` at
`π_X⁻¹F` and the unit of `a_X⁻¹ ⊣ a_{X,*}` at `F`. Their invertibility at an fppf sheaf is
`AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToBigEtaleMorphism_unit_app_of_isSheaf` and
`AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleMorphism_unit_app_of_isSheaf`.

## References

* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
* [Stacks Project, Tag 0DGF](https://stacks.math.columbia.edu/tag/0DGF)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) (X : T.Spaces)
  (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1)))

/-- **The fpqc sheaf condition for `π_X⁻¹F`** (Stacks 0DG7). `π_X⁻¹F` satisfies the sheaf
condition for every family of the slice over `X` whose underlying family of algebraic spaces is
an fpqc covering. -/
theorem inverseImage_isSheafFor_of_isFpqcCovering {U : Over X} {I : Type v} {V : I → Over X}
    (f : ∀ i, V i ⟶ U) (hf : Space.IsFpqcCovering T.fppfSite S T.fppf_mem
      (fun i ↦ (f i).left.hom)) :
    Presieve.IsSheafFor ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj
      (Presieve.ofArrows V f) :=
  Space.isSheafFor_of_isFpqcCovering (isEtaleSheafOver_inverseImage T X F)
    (isAffineFpqcSheafOver_inverseImage T X F) f hf

/-- An fpqc covering family of the slice over `X` generates a covering sieve of the finest
topology for which `π_X⁻¹F` is a sheaf: its base change along any morphism of the slice is again
an fpqc covering family, for which the sheaf condition holds. -/
theorem ofArrows_mem_finestTopologySingle_inverseImage {U : Over X} {I : Type v}
    {V : I → Over X} (f : ∀ i, V i ⟶ U)
    (hf : Space.IsFpqcCovering T.fppfSite S T.fppf_mem (fun i ↦ (f i).left.hom)) :
    Sieve.ofArrows V f ∈
      Sheaf.finestTopologySingle ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj U := by
  intro W g
  rw [← Sieve.ofArrows_eq_pullback_of_isPullback f
    fun i ↦ (Space.sliceFiberProduct_isPullback T.fppfSite S T.fppf_mem X (f i) g).flip]
  exact (Presieve.isSheafFor_iff_generate _).mp
    (inverseImage_isSheafFor_of_isFpqcCovering T X F _
      (Space.isFpqcCovering_pullback T.fppfSite S T.fppf_mem (fun i ↦ (f i).left) g.left hf))

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The chosen fppf covering families of a big fppf site of algebraic spaces, packaged as a
coverage: a base change of a chosen covering is refined by a chosen covering, which is the base
change axiom of the site. -/
def fppfSpaceCoverage : Coverage T.Spaces where
  toPrecoverage := T.precoverage
  pullback := by
    intro Y Z f R hR
    obtain ⟨E, rfl, hE⟩ := (T.mem_precoverage_iff).mp hR
    obtain ⟨P, p, q, hpq, hP⟩ := T.isSite.2.2 ⟨Y, E⟩ hE Z f
    refine ⟨Presieve.ofArrows P q, ⟨⟨E.I₀, P, q⟩, rfl, hP⟩, ?_⟩
    rintro W g ⟨i⟩
    exact ⟨E.X i, p i, E.f i, ⟨i⟩, (hpq i).w⟩

/-- The big fppf topology of algebraic spaces is generated by the coverage
`AlgebraicGeometry.Space.fppfSpaceCoverage`. -/
theorem fppfSpaceCoverage_toGrothendieck : (fppfSpaceCoverage T).toGrothendieck = T.topology :=
  (Coverage.toGrothendieck_toPrecoverage (fppfSpaceCoverage T)).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigFppfSpaceSite

/-- The sieve generated by a family of morphisms into the underlying object of a slice object,
read in the slice, is generated by the same family lifted to the slice. -/
private theorem overEquiv_symm_generate_presieve₀ {C : Type*} [Category C] {X : C}
    {U : Over X} (E : PreZeroHypercover.{v} U.left) :
    (Sieve.overEquiv U).symm (Sieve.generate E.presieve₀) =
      Sieve.ofArrows (fun i ↦ (Over.mk (E.f i ≫ U.hom) : Over X))
        (fun i ↦ (Over.homMk (E.f i) : Over.mk (E.f i ≫ U.hom) ⟶ U)) := by
  ext Z g
  rw [Sieve.overEquiv_symm_iff]
  constructor
  · rintro ⟨W, p, c, ⟨i⟩, hpc⟩
    refine ⟨Over.mk (E.f i ≫ U.hom), Over.homMk p ?_, Over.homMk (E.f i), ⟨i⟩,
      Over.OverMorphism.ext hpc⟩
    show p ≫ E.f i ≫ U.hom = Z.hom
    rw [← Category.assoc, hpc, Over.w g]
  · rintro ⟨W, p, c, ⟨i⟩, hpc⟩
    exact ⟨E.X i, p.left, E.f i, ⟨i⟩, congrArg CommaMorphism.left hpc⟩

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- **`π_X⁻¹F` is an fppf sheaf.** For a sheaf `G` on the small étale site of an algebraic space
`X`, the big étale sheaf `π_X⁻¹G`, read on the big fppf slice at `X`, is a sheaf for the big
fppf topology of `X` (the fppf clause of Stacks 0DG7). -/
theorem isSheaf_bigToSmallEtale_inverseImage (X : T.Spaces)
    (G : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      (Type (u + 1))) :
    Presheaf.IsSheaf (BigFppfSpaceOver.topology T X)
      ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).functor.op ⋙
        ((E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage.obj G).obj) := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let P := ((E'.bigToSmallEtaleMorphism X).inverseImage.obj G).obj
      show Presheaf.IsSheaf (BigFppfSpaceOver.topology T' X) P
      rw [isSheaf_iff_isSheaf_of_type]
      have hle : BigFppfSpaceOver.topology T' X ≤ Sheaf.finestTopologySingle P := by
        show T'.topology.over X ≤ _
        rw [← Space.fppfSpaceCoverage_toGrothendieck T']
        exact over_le_of_coverage (Space.fppfSpaceCoverage T') X _ fun Y R hR ↦ by
          obtain ⟨E₀, rfl, hE₀⟩ := (BigFppfSpaceSite.mem_precoverage_iff T').mp hR
          rw [overEquiv_symm_generate_presieve₀]
          exact E'.ofArrows_mem_finestTopologySingle_inverseImage X G _
            (Space.isFpqcCovering_of_isFppfCovering _ _ _ _ _ hE₀.1)
      intro Y R hR
      simpa using hle Y hR Y (𝟙 Y)

/-- The unit of `ε_X⁻¹ ⊣ ε_{X,*}`, whiskered with `π_X⁻¹`, is an isomorphism. -/
private theorem isIso_whiskerLeft_fppfToBigEtale_unit (X : T.Spaces) :
    IsIso (Functor.whiskerLeft (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage
      (fppfToBigEtaleMorphism T E h X).adj.unit) := by
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun G ↦
    isIso_fppfToBigEtaleMorphism_unit_app_of_isSheaf T E h X _
      (isSheaf_bigToSmallEtale_inverseImage T E h X G)

/-- **The unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism**: `F ⟶ a_{X,*}a_X⁻¹F` is invertible for
every sheaf `F` on the small étale site of `X`. -/
theorem isIso_fppfToSmallEtaleMorphism_unit (X : T.Spaces) :
    IsIso (fppfToSmallEtaleMorphism T E h X).adj.unit := by
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun G ↦
    isIso_fppfToSmallEtaleMorphism_unit_app_of_isSheaf T E h X G
      (isSheaf_bigToSmallEtale_inverseImage T E h X G)

/-- `a_X⁻¹` is fully faithful, its unit being an isomorphism. -/
def fppfToSmallEtale_inverseImage_fullyFaithful (X : T.Spaces) :
    (fppfToSmallEtaleMorphism T E h X).inverseImage.FullyFaithful :=
  haveI := isIso_fppfToSmallEtaleMorphism_unit T E h X
  (fppfToSmallEtaleMorphism T E h X).adj.fullyFaithfulLOfIsIsoUnit

/-- `a_X⁻¹` is full. -/
instance (X : T.Spaces) : (fppfToSmallEtaleMorphism T E h X).inverseImage.Full :=
  (fppfToSmallEtale_inverseImage_fullyFaithful T E h X).full

/-- `a_X⁻¹` is faithful. -/
instance (X : T.Spaces) : (fppfToSmallEtaleMorphism T E h X).inverseImage.Faithful :=
  (fppfToSmallEtale_inverseImage_fullyFaithful T E h X).faithful

/-- **Stacks 0DGF (1), first clause**: `ε_{X,*}a_X⁻¹F = π_X⁻¹F`, naturally in the sheaf `F` on
the small étale site of `X`. The isomorphism is the inverse of the unit
`π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹F` of `ε_X⁻¹ ⊣ ε_{X,*}`, invertible because `π_X⁻¹F` is an fppf
sheaf. -/
def fppfToSmallEtale_inverseImage_comp_fppfToBigEtale_pushforwardIso (X : T.Spaces) :
    (fppfToSmallEtaleMorphism T E h X).inverseImage ⋙ (fppfToBigEtaleMorphism T E h X).pushforward ≅
      (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage :=
  haveI : ∀ G, IsIso ((Functor.whiskerLeft
      (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage
      (fppfToBigEtaleMorphism T E h X).adj.unit).app G) := fun G ↦
    isIso_fppfToBigEtaleMorphism_unit_app_of_isSheaf T E h X _
      (isSheaf_bigToSmallEtale_inverseImage T E h X G)
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage
      (fppfToBigEtaleMorphism T E h X).adj.unit)
  (asIso (Functor.whiskerLeft (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage
      (fppfToBigEtaleMorphism T E h X).adj.unit)).symm

/-- **Stacks 0DGF (1), second clause**: `a_{X,*}a_X⁻¹F = F`, naturally in the sheaf `F` on the
small étale site of `X`. The isomorphism is the inverse of the unit of `a_X⁻¹ ⊣ a_{X,*}`. -/
def fppfToSmallEtale_inverseImage_comp_pushforwardIso (X : T.Spaces) :
    (fppfToSmallEtaleMorphism T E h X).inverseImage ⋙
        (fppfToSmallEtaleMorphism T E h X).pushforward ≅
      𝟭 _ :=
  haveI := isIso_fppfToSmallEtaleMorphism_unit T E h X
  (asIso (fppfToSmallEtaleMorphism T E h X).adj.unit).symm

/-- **Part (1) of Stacks 0DGF, as one statement.** For a sheaf `F` on the small étale site of
an algebraic space `X`, the canonical maps `π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹F = ε_{X,*}a_X⁻¹F` and
`F ⟶ a_{X,*}a_X⁻¹F` are isomorphisms, naturally in `F`: these are the units of
`ε_X⁻¹ ⊣ ε_{X,*}` at `π_X⁻¹F` and of `a_X⁻¹ ⊣ a_{X,*}` at `F`. -/
theorem isIso_fppfToBigEtale_unit_whiskerLeft_and_isIso_fppfToSmallEtale_unit (X : T.Spaces) :
    IsIso (Functor.whiskerLeft (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage
        (fppfToBigEtaleMorphism T E h X).adj.unit) ∧
      IsIso (fppfToSmallEtaleMorphism T E h X).adj.unit := by
  exact ⟨isIso_whiskerLeft_fppfToBigEtale_unit T E h X,
    isIso_fppfToSmallEtaleMorphism_unit T E h X⟩

end AlgebraicGeometry.BigFppfSpaceSite

end
