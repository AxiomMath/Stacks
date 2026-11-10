module

public import StacksFrontier.AlgebraicGeometry.BasisRoute.Basic
public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Consumers
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent

/-!
# Stacks Tag 01VN, reduced to one statement about an absolute `Proj`

`StacksFrontier/AlgebraicGeometry/BasisRoute/Basic.lean` proves the content of Stacks Tag
01VN on a hypothesis — `Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion` — that asks for
an ambient scheme `P` over `S`, an invertible `𝒪_P`-module `M` whose nonvanishing opens form a
basis for the topology of `p⁻¹(V)` for every affine open `V` of `S`, and an immersion `i : X ⟶ P`
over `S` with `L ≅ i^* M`. Its own documentation records the remaining input as *a value of*
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, which the glueing assertion of Stacks
Tag 01NR would produce and which nothing in the library constructs, for any graded algebra.

**The construction is not needed.** Stacks Tag 01VM
asks for an immersion into `𝐏(E)` whose `𝒪(1)` is *the* twist of the projective bundle, and
the statement of Tag 01OB gives that twist as the degree-`n` piece of
the relative `Proj` twists of the statement of Tag 01NR — which are a `sorry` **definition**
there, so that twist is unconstructed data and a hypothesis stated with it would make the
statement depend on that unproved definition. A statement quantified over an *arbitrary* twist datum
is therefore the
faithful reading, and it is the one the Tag 01NR and Tag 01O4 material in this repository is
already written at; it is also *weaker* as a hypothesis, so the theorem proved here is stronger
than the one stated with that twist. Nothing has to be built.

What was genuinely missing is the passage from the affine chart of the relative `Proj` to the
preimage of its affine open. The twist datum identifies the restriction of its degree-`n` piece
along the chart with the absolute twist `𝒪(n)` on `Proj(A(V))` (`ChartData.chartIso`), but that
restriction is `AlgebraicGeometry.Scheme.Modules.restrict`, a *pushforward* along the inverse of
`Scheme.Hom.appIso`, while the ampleness development speaks of
`RingedSpaceModuleAdjunction.modulePullback`; and clause (3) of Stacks Tag 01Q3 had no transport
along an isomorphism of modules or of schemes. So the sentence "given `D : TwistData A` plus the
local basis clause on each affine open of `S`, Stacks Tag 01VN follows with no further input" is
optimistic by three bridges, all three of which are below.

## Main definitions

* `Stacks.Tag01VNChartBasis.chartTwistIso`: under the chart identification
  `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`, the absolute twist `𝒪(1)` on
  the chart is the restriction of the glued degree-one twist, in the module-pullback spelling.
* `Stacks.Tag01VNChartBasis.HasRelativeVeryAmpleTwist`: relative very ampleness, Stacks Tag 01VM,
  in library vocabulary, with the twist taken as an arbitrary twist datum of `Sym(E)`.
* `Stacks.Tag01VNChartBasis.ProjOneBasisClause`: **the one absolute input that remains.**

## Main results

* `Stacks.Tag01VNChartBasis.isBasisNonvanishing_of_iso` and `isBasisNonvanishing_pullback_iso`:
  clause (3) of Stacks Tag 01Q3 transports along an isomorphism of invertible modules, and along
  an isomorphism of schemes.
* `Stacks.Tag01VNChartBasis.isBasisNonvanishing_preimage_of_chart`: **the chart passage.** Clause
  (3) for `𝒪(1)` on `Proj(A(V))` gives clause (3) for the glued degree-one twist on `p⁻¹(V)`.
* `Stacks.Tag01VNChartBasis.hasRelativeBasisImmersion_of_twistData`: hence a twist datum, an
  immersion over the base and the absolute clause give
  `Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion`.
* `Stacks.Tag01VNChartBasis.isRelativelyAmple_of_hasRelativeVeryAmpleTwist`: **the content of
  Stacks Tag 01VN, on `ProjOneBasisClause` as its only premise.**

## What is not done

**`ProjOneBasisClause` is not proved, and no `stacks` attribute is attached.** It says that for a
graded ring `𝒜` generated in degree one over `𝒜 0`, the opens `(Proj 𝒜)_s`, for `s` a global
section of a positive tensor power of `𝒪(1)`, form a basis for the topology. Two halves, both
with their inputs identified and neither assembled here:

1. the opens `D₊(a)`, for `a` homogeneous of positive degree, form a basis — Mathlib's
  `ProjectiveSpectrum.isTopologicalBasis_basic_opens` together with
  `ProjectiveSpectrum.basicOpen_eq_union_of_projection` and, to force positive degree,
  `Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne`;
2. `(Proj 𝒜)_{degreeSection 𝒜 d a} = D₊(a)` for `a : 𝒜 d`, together with
  `tensorPowModule (Proj 𝒜) (𝒪(1)) d ≅ 𝒪(d)`. The second of these is the hypothesis `htw` of
  `Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute.exists_epi_coproduct_twistingSheaf_of_isCoherent`,
  so it is needed by two statements at once; its ingredients are
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin` and the
  addition law `Stacks.Ample.tensorPowModuleAddIso`, and what is missing is the induction over
  degrees. For the first, the degree-one case of the nonvanishing identification is available:
  `Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection` exhibits
  `degreeSection 𝒮 1 f` as a free generator of `𝒪(1)` on every open of `D₊(f)`.

Tag 01VN's covering set is its own theorem, and the theorem below carries `ProjOneBasisClause` as
a hypothesis the statement of Tag 01VN does not have, so the tag is not attached. Tags 01VM and 01OB
are not asserted either: `HasRelativeVeryAmpleTwist` is a hypothesis
here, not a definition offered as Tag 01VM's, and nothing about the projective bundle's
functoriality in `E` is proved.

## References

* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry

universe u w

namespace Stacks.Tag01VNChartBasis

/-! ### Clause (3) of Stacks Tag 01Q3 is invariant under isomorphism of modules -/

/-- **Clause (3) of Stacks Tag 01Q3 transports along an isomorphism of invertible
`𝒪_X`-modules.** -/
theorem isBasisNonvanishing_of_iso {X : Scheme.{u}} {M N : X.Modules}
    [IsInvertibleModule X M] [IsInvertibleModule X N] (e : M ≅ N)
    (h : Stacks.AmpleTheory.IsBasisNonvanishing X M) :
    Stacks.AmpleTheory.IsBasisNonvanishing X N := by
  intro x U hx
  obtain ⟨n, hn, s, hxs, hsU⟩ := h x U hx
  set g := Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso X M N e n with hg
  have hEq : Stacks.AmpleTheory.powNonvanishingOpen X N n ((g.hom.app ⊤) s) =
      Stacks.AmpleTheory.powNonvanishingOpen X M n s := by
    apply TopologicalSpace.Opens.ext
    rw [Stacks.AmpleTheory.coe_powNonvanishingOpen, Stacks.AmpleTheory.coe_powNonvanishingOpen,
      nonvanishingLocus_congr g s]
  exact ⟨n, hn, (g.hom.app ⊤) s, hEq ▸ hxs, hEq ▸ hsU⟩

/-- **Clause (3) transports along an isomorphism of schemes.** -/
theorem isBasisNonvanishing_pullback_iso {X Y : Scheme.{u}} (e : X ≅ Y) (L : Y.Modules)
    [IsInvertibleModule Y L] (h : Stacks.AmpleTheory.IsBasisNonvanishing Y L) :
    Stacks.AmpleTheory.IsBasisNonvanishing X
      ((modulePullback e.hom.toLRSHom.toShHom).obj L) :=
  Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback e.hom L
    (Scheme.homeoOfIso e).isEmbedding h
    (Stacks.NonvanishingPullback.sectionPullbackCompatible e.hom L)


/-! ### The chart of a relative `Proj` carries clause (3) to the preimage of an affine open -/

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **Under the chart identification, the absolute twist `𝒪(1)` on `Proj(A(V))` is the
restriction of the glued degree-one twist to `p⁻¹(V)`.**

The identification of the two schemes is the twist-datum-free
`Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`, and the move between the two
restrictions is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.restrictIsoOfIsoOver`.
What this adds is the two passages between `AlgebraicGeometry.Scheme.Modules.restrict`, which is
a pushforward along the inverse of `AlgebraicGeometry.Scheme.Hom.appIso`, and
`RingedSpaceModuleAdjunction.modulePullback`, which is the spelling the ampleness development is
written in; they are `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
def chartTwistIso (D : TwistData A) (V : S.Opens) (hV : IsAffineOpen V) :
    (Scheme.Modules.pullback (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).obj
        (twistingSheaf (A.grading V) 1) ≅
      (Scheme.Modules.pullback ((relativeProj A).toBase ⁻¹ᵁ V).ι).obj (D.algebra.piece 1) :=
  letI := D.chartData.chart_isOpenImmersion V hV
  ((Scheme.Modules.restrictFunctorIsoPullback
        (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).app
      (twistingSheaf (A.grading V) 1)).symm ≪≫
    (Scheme.Modules.restrictFunctor
        (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).mapIso
      (D.chartData.chartIso V hV 1).symm ≪≫
    AlgebraicGeometry.ProjectiveSpectrum.Proj.restrictIsoOfIsoOver (D.algebra.piece 1)
      ((relativeProj A).chart V hV) ((relativeProj A).toBase ⁻¹ᵁ V)
      (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV)
      (RelativeProjTwistQcoh.chartIsoPreimage_hom_comp V hV) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).toBase ⁻¹ᵁ V).ι).app
      (D.algebra.piece 1)


/-! ### Clause (3) on the preimage of an affine open, from the chart -/

/-- **Clause (3) of Stacks Tag 01Q3 for the glued degree-one twist on the preimage of an affine
open, from the same clause for `𝒪(1)` on the affine chart.** -/
theorem isBasisNonvanishing_preimage_of_chart (D : TwistData A)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (V : S.Opens) (hV : IsAffineOpen V)
    (hbasis :
      letI := TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin
        (A.grading V) (hgen V hV) 1
      Stacks.AmpleTheory.IsBasisNonvanishing (AlgebraicGeometry.Proj (A.grading V))
        (twistingSheaf (A.grading V) 1)) :
    letI : IsInvertibleModule (relativeProj A).scheme (D.algebra.piece 1) :=
      TwistMapsInvertible.twistData_isInvertible D hgen 1
    letI : IsInvertibleModule ((relativeProj A).toBase ⁻¹ᵁ V).toScheme
        ((modulePullback ((relativeProj A).toBase ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
          (D.algebra.piece 1)) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback
        ((relativeProj A).toBase ⁻¹ᵁ V).ι (D.algebra.piece 1)
    Stacks.AmpleTheory.IsBasisNonvanishing ((relativeProj A).toBase ⁻¹ᵁ V).toScheme
      ((modulePullback ((relativeProj A).toBase ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        (D.algebra.piece 1)) := by
  have : IsInvertibleModule (relativeProj A).scheme (D.algebra.piece 1) :=
    TwistMapsInvertible.twistData_isInvertible D hgen 1
  have := TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin
    (A.grading V) (hgen V hV) 1
  have : IsInvertibleModule ((relativeProj A).toBase ⁻¹ᵁ V).toScheme
      ((Scheme.Modules.pullback (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).obj
        (twistingSheaf (A.grading V) 1)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback
      (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom
      (twistingSheaf (A.grading V) 1)
  have : IsInvertibleModule ((relativeProj A).toBase ⁻¹ᵁ V).toScheme
      ((modulePullback ((relativeProj A).toBase ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        (D.algebra.piece 1)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback
      ((relativeProj A).toBase ⁻¹ᵁ V).ι (D.algebra.piece 1)
  exact isBasisNonvanishing_of_iso (chartTwistIso D V hV)
    (isBasisNonvanishing_pullback_iso (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV)
      _ hbasis)


/-! ### The hypothesis of Stacks Tag 01VN from a twist datum on the relative `Proj` -/

/-- **The hypothesis of `isRelativelyAmple_of_hasRelativeBasisImmersion` from a twist datum.** -/
theorem hasRelativeBasisImmersion_of_twistData {X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (D : TwistData A)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (hbasis : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      letI := TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin
        (A.grading V) (hgen V hV) 1
      Stacks.AmpleTheory.IsBasisNonvanishing (AlgebraicGeometry.Proj (A.grading V))
        (twistingSheaf (A.grading V) 1))
    (i : X ⟶ (relativeProj A).scheme) (him : IsImmersion i)
    (hover : i ≫ (relativeProj A).toBase = f)
    (e : L ≅ (modulePullback i.toLRSHom.toShHom).obj (D.algebra.piece 1)) :
    Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion f L :=
  ⟨(relativeProj A).scheme, (relativeProj A).toBase, D.algebra.piece 1,
    TwistMapsInvertible.twistData_isInvertible D hgen 1, i, him, hover,
    fun V hV => isBasisNonvanishing_preimage_of_chart D hgen V hV (hbasis V hV), ⟨e⟩⟩

/-! ### Stacks Tag 01VN -/

/-- **Relative very ampleness, Stacks Tag 01VM, in library vocabulary**, with the twist on the
projective bundle taken as an arbitrary twist datum of `Sym(E)`. -/
def HasRelativeVeryAmpleTwist {X S' : Scheme.{u}} (f : X ⟶ S') (L : X.Modules) : Prop :=
  ∃ (E : S'.Modules) (hE : E.IsQuasicoherent),
    letI := hE
    ∃ (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)))
      (i : X ⟶ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E))).scheme),
      IsImmersion i ∧
        i ≫ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E))).toBase = f ∧
        Nonempty (L ≅ (modulePullback i.toLRSHom.toShHom).obj (D.algebra.piece 1))

/-- **The one absolute input left**: clause (3) of Stacks Tag 01Q3 for `𝒪(1)` on the `Proj` of a
graded ring generated in degree one over its degree-zero part. -/
def ProjOneBasisClause : Prop :=
  ∀ {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set R)) = ⊤),
    letI := TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin 𝒜 hgen 1
    Stacks.AmpleTheory.IsBasisNonvanishing (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)

/-- **Stacks Tag 01VN on the one absolute input.** -/
theorem isRelativelyAmple_of_hasRelativeVeryAmpleTwist (hclause : ProjOneBasisClause.{u, u})
    {X S' : Scheme.{u}} (f : X ⟶ S') (L : X.Modules) [IsInvertibleModule X L]
    (hf : QuasiCompact f) (hL : HasRelativeVeryAmpleTwist f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨E, hE, D, i, him, hover, ⟨e⟩⟩ := hL
  have := hE
  exact Stacks.RelativeAmpleBasisRoute.isRelativelyAmple_of_hasRelativeBasisImmersion f L hf
    (hasRelativeBasisImmersion_of_twistData f L D
      (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E _)
      (fun V hV => hclause _
        (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E _ V hV))
      i him hover e)


/-! ### Faithfulness against the statement of Tag 01VN, and the hypothesis that survives

The statement of Tag 01VN takes a morphism of schemes `f : X ⟶ S`, a module `L : X.Modules`,
quasi-compactness `hf : QuasiCompact f` and relative very ampleness `hL` of `L` over `S` in the
sense of Tag 01VM, whose first component is invertibility of `L` in the sense of Tag 01CS, and
concludes that `L` is relatively ample in the sense of Tag 01VH. The example below is the theorem
above written in that statement's binder order. Every binder
of that statement is present and in position: `f`, `L`, invertibility of `L` (which the statement
extracts
from the first component of its hypothesis and this file carries as an instance argument, the
same trade `Stacks.RelativeAmple.IsRelativelyAmple` makes), `hf`, and the relative-very-ampleness
hypothesis. The conclusion is `Stacks.RelativeAmple.IsRelativelyAmple`, which carries the
Tag 01VH attribute and is the tagged definition verbatim with `Stacks.Ample.IsAmple` in place of
the ampleness predicate of the statement of Tag 01PS.

**`hclause` is a hypothesis the statement of Tag 01VN does not have**, so the tag is not
attached. It is the only one: the example takes nothing else beyond that statement's binders. -/
example (hclause : ProjOneBasisClause.{u, u}) {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f) (hL : HasRelativeVeryAmpleTwist f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_hasRelativeVeryAmpleTwist hclause f L hf hL

end Stacks.Tag01VNChartBasis

end
