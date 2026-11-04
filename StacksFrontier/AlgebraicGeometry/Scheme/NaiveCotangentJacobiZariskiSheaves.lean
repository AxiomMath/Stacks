module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentBaseChangeHomology
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkJacobiZariski
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# Three assertions of the six-term sequence of Stacks 0E1Y and 0E1Z

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space, with
canonical maps `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` and `g : NL_{C/A} ⟶ NL_{C/B}`.  The composite
`c₁ ≫ g` is null homotopic, so on cohomology sheaves

`H^j(NL_{B/A} ⊗_B C) ⟶ H^j(NL_{C/A}) ⟶ H^j(NL_{C/B})`

is a complex of sheaves of `C`-modules for every `j`.  This file proves that it is **exact** for
`j = 0` and for `j = -1`, that is, at the two nodes `H⁰(NL_{C/A})` and `H^{-1}(NL_{C/A})` of the
six-term sequence of Stacks 0E1Y, and that `H⁰(g)` is **surjective**, which is the final `⟶ 0`
of that sequence; and it transports all three assertions to a pair of composable morphisms of
ringed spaces, where they are the exactness of the six-term sequence of Stacks 0E1Z at
`H⁰(NL_{X/Z})`, at `H^{-1}(NL_{X/Z})` and at `H⁰(NL_{X/Y})`.

Exactness of a sequence of sheaves of modules is a stalkwise condition
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact`), the stalk functor is exact
so it commutes with cohomology (`CategoryTheory.ShortComplex.homologyFunctorIso`), and at a stalk
the three complexes are the naive cotangent complexes of the canonical presentations of the stalk
rings (Stacks 0D09) and the two maps the ring-level comparison maps, whose exactness at the
middle node is Algebra, Lemma 00S2 — this is
`Stacks.NaiveCotangentStalkJacobiZariski.exists_cycle_stalk` and `exists_add_d_stalk`.

Nothing here is about the other two assertions of the six-term sequence, its exactness at
`H^{-1}(NL_{C/B})` and at `H⁰(NL_{B/A} ⊗_B C)`: those need the connecting map and with it the
comparison of `NL_{B/A} ⊗_B C` with the shifted cone in degree `0`, and they are proved in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm` on top of
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`.

## Main definitions

* `Stacks.SheafOfModules.spaceJacobiZariskiHomologySequence`: the complex of sheaves of
  `C`-modules `H^j(NL_{B/A} ⊗_B C) ⟶ H^j(NL_{C/A}) ⟶ H^j(NL_{C/B})`, for sheaves of rings on a
  topological space.
* `Stacks.SheafOfModules.ringedSpaceJacobiZariskiHomologySequence`: the complex
  `H^j(f^*NL_{Y/Z}) ⟶ H^j(NL_{X/Z}) ⟶ H^j(NL_{X/Y})`, for a pair of composable morphisms of
  ringed spaces.  Its first map is the one induced by
  `Stacks.NaiveCotangentCompositionTriangle.pulledNaiveCotangentMap`, written out.

## Main results

* `Stacks.SheafOfModules.homologyMap_spaceBaseChange_comp_relative`: the sequence is a complex,
  because `c₁ ≫ g` is null homotopic.
* `Stacks.SheafOfModules.exact_spaceJacobiZariskiHomologySequence_zero` and
  `exact_spaceJacobiZariskiHomologySequence_negOne`: **the six-term sequence of Stacks 0E1Y is
  exact at `H⁰(NL_{C/A})` and at `H^{-1}(NL_{C/A})`.**
* `Stacks.SheafOfModules.exact_ringedSpaceJacobiZariskiHomologySequence_zero` and
  `exact_ringedSpaceJacobiZariskiHomologySequence_negOne`: **the six-term sequence of Stacks 0E1Z
  is exact at `H⁰(NL_{X/Z})` and at `H^{-1}(NL_{X/Z})`.**
* `Stacks.SheafOfModules.epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero` and
  `epi_homologyMap_ringedSpaceRelativeNaiveCotangentComplexMap_zero`: **the final `⟶ 0` of the
  six-term sequence of Stacks 0E1Y, respectively of Stacks 0E1Z** — the canonical map `g` is
  surjective on `H⁰`.  Epimorphy is stalkwise, and at a stalk this is the surjectivity clause of
  Algebra, Lemma 00S2 over the canonical presentations.
* `Stacks.SheafOfModules.epi_homologyMap_spaceNaiveCotangentConeMap_negOne` and
  `epi_homologyMap_ringedSpaceNaiveCotangentConeMap_negOne`: **the canonical map `c` of
  Stacks 0E1Y, respectively of Stacks 0E1Z, to the shifted cone is surjective on `H^{-1}`**, which
  is half of the comparison the other two assertions of the six-term sequence rest on.  In degree
  `-1` the projection of the shifted cone is a monomorphism
  (`Stacks.SheafOfModules.mono_homologyMap_pShift_negOne`), so exactness at `H^{-1}(NL_{C/A})`
  already forces it; in degree `0` it is not, and the other half — that `H⁰(c)` is an
  isomorphism — is
  `Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`, in
  `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentConeHomologyZero`.
* `AlgebraicGeometry.SheafOfModules.exact_homologyShortComplex_of_forall_stalk`: the stalkwise
  criterion the two 0E1Y statements are proved with, and
  `AlgebraicGeometry.SheafOfModules.stalkHomologyShortComplexIso`, the identification of the
  stalk of a sequence of cohomology sheaves with the sequence of cohomologies of the stalks.

## Implementation notes

The two stalkwise inputs are stated elementwise rather than as `ShortComplex.Exact`, because
that is the form in which the ring-level sequence delivers them;
`HomologicalComplex.exact_homologyMap_of_exists_cycle` and
`HomologicalComplex.exact_homologyMap_of_exists_add_d` turn them into exactness of the sequence
of homology modules of the three complexes of stalks.  Both ask for the vanishing of one of the
three differentials next to the degree in question, which holds because all three complexes
vanish outside degrees `-1` and `0`.

`AlgebraicGeometry.SheafOfModules.stalkHomologyShortComplexIso` takes both zero-composite proofs
as arguments, so that neither of the two short complexes it compares has to be built before the
other.  Its two squares are the naturality of `CategoryTheory.ShortComplex.homologyFunctorIso` at
the two chain maps: the `i`-th short complex of a stalk complex and the stalk short complex of the
`i`-th short complex are literally the same short complex, as recorded in
`StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic`.

The transport to Stacks 0E1Z composes the first map with the identification
`Stacks.SheafOfModules.pulledNaiveCotangentComparison` of Stacks 08TM, which is an isomorphism;
precomposing with an isomorphism does not change the image of a map, which is the content of the
isomorphism of short complexes used there.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), the ring-level six-term
  sequence.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex.
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG), exactness is stalkwise.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of the
  naive cotangent complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **The stalk of a sequence of cohomology sheaves is the sequence of cohomologies of the
stalks.**  For morphisms `φ : K ⟶ L` and `ψ : L ⟶ M` of complexes of sheaves of `𝒪`-modules whose
composite induces zero on cohomology in degree `j`, the complex of stalks at `x` of

`H^j(K) ⟶ H^j(L) ⟶ H^j(M)`

is the complex `H^j(K_x) ⟶ H^j(L_x) ⟶ H^j(M_x)` of the three complexes of stalks.

The stalk functor is exact, so it commutes with cohomology; the identification is
`CategoryTheory.ShortComplex.homologyFunctorIso` and the two squares are its naturality. -/
def stalkHomologyShortComplexIso {K L M : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ}
    (φ : K ⟶ L) (ψ : L ⟶ M) (j : ℤ) (x : X)
    (hzero : HomologicalComplex.homologyMap φ j ≫ HomologicalComplex.homologyMap ψ j = 0)
    (hstalk : HomologicalComplex.homologyMap
          (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) j ≫
        HomologicalComplex.homologyMap
          (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) j = 0) :
    ShortComplex.mk
        (HomologicalComplex.homologyMap
          (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) j)
        (HomologicalComplex.homologyMap
          (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) j) hstalk ≅
      (ShortComplex.mk (HomologicalComplex.homologyMap φ j)
        (HomologicalComplex.homologyMap ψ j) hzero).map (stalkFunctor 𝒪 x) :=
  ShortComplex.isoMk
    ((ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x)).app (K.sc j))
    ((ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x)).app (L.sc j))
    ((ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x)).app (M.sc j))
    ((ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x)).hom.naturality
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) j).map φ)).symm
    ((ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x)).hom.naturality
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) j).map ψ)).symm

/-- **A sequence of cohomology sheaves which is exact at every stalk is exact.**  This is the
stalk criterion for exactness, Stacks 01AG, read on the cohomology sheaves of complexes of
sheaves of modules through `stalkHomologyShortComplexIso`. -/
theorem exact_homologyShortComplex_of_forall_stalk
    {K L M : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ} (φ : K ⟶ L) (ψ : L ⟶ M) (j : ℤ)
    (hzero : HomologicalComplex.homologyMap φ j ≫ HomologicalComplex.homologyMap ψ j = 0)
    (hstalk : ∀ x : X, HomologicalComplex.homologyMap
          (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) j ≫
        HomologicalComplex.homologyMap
          (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) j = 0)
    (hexact : ∀ x : X, (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) j)
      (HomologicalComplex.homologyMap
        (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) j)
      (hstalk x)).Exact) :
    (ShortComplex.mk (HomologicalComplex.homologyMap φ j)
      (HomologicalComplex.homologyMap ψ j) hzero).Exact :=
  (exact_iff_stalkFunctor_map_exact _).2 fun x =>
    ShortComplex.exact_of_iso (stalkHomologyShortComplexIso 𝒪 φ ψ j x hzero (hstalk x)) (hexact x)

end AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafOfModules

open Stacks.NaiveCotangentStalkJacobiZariski
open AlgebraicGeometry.SheafOfModules (stalkFunctor)

/-! ### Sheaves of rings on a topological space -/

section Space

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C)

/-- **On cohomology sheaves the composite `c₁ ≫ g` of the two canonical maps of Stacks 0E1Y is
zero**, since it is null homotopic
(`Stacks.SheafOfModules.baseChangeRelativeNullHomotopy`). -/
theorem homologyMap_spaceBaseChange_comp_relative (j : ℤ) :
    HomologicalComplex.homologyMap (spaceBaseChangeNaiveCotangentMap A B C a b) j ≫
        HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) j = 0 := by
  have hcomp := HomologicalComplex.homologyMap_comp
    (baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
    (relativeNaiveCotangentComplexMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b) j
  have hhom := (baseChangeRelativeNullHomotopy.{u, u, u} (Opens.grothendieckTopology T) A B C a
    b).homologyMap_eq j
  have hzero := HomologicalComplex.homologyMap_zero
    (baseChangeNaiveCotangentComplex.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b) (i := j)
  exact hcomp.symm.trans (hhom.trans hzero)

/-- The same for the three complexes of stalks at a point. -/
theorem homologyMap_stalk_spaceBaseChange_comp_relative (z : T) (j : ℤ) :
    HomologicalComplex.homologyMap
        (((stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (spaceBaseChangeNaiveCotangentMap A B C a b)) j ≫
      HomologicalComplex.homologyMap
        (((stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (spaceRelativeNaiveCotangentComplexMap A B C a b)) j = 0 := by
  have hcomp := HomologicalComplex.homologyMap_comp
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
      (baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b))
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
      (relativeNaiveCotangentComplexMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b)) j
  have hfunc := CategoryTheory.Functor.map_comp
    ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ))
    (baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
    (relativeNaiveCotangentComplexMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
  have hhom := ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomotopy
    (baseChangeRelativeNullHomotopy.{u, u, u} (Opens.grothendieckTopology T) A B C a
      b)).homologyMap_eq j
  have hmapzero := CategoryTheory.Functor.map_zero
    ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ))
    (baseChangeNaiveCotangentComplex.{u, u, u} (Opens.grothendieckTopology T) A B C a b)
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b)
  have hzero := HomologicalComplex.homologyMap_zero
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (baseChangeNaiveCotangentComplex.{u, u, u} (Opens.grothendieckTopology T) A B C a b))
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C b)) (i := j)
  exact hcomp.symm.trans ((congrArg (fun φ => HomologicalComplex.homologyMap φ j) hfunc.symm).trans
    (hhom.trans ((congrArg (fun φ => HomologicalComplex.homologyMap φ j) hmapzero).trans hzero)))

/-- **The sequence of cohomology sheaves of Stacks 0E1Y in degree `j`**:
`H^j(NL_{B/A} ⊗_B C) ⟶ H^j(NL_{C/A}) ⟶ H^j(NL_{C/B})`, a complex of sheaves of `C`-modules
because `c₁ ≫ g` is null homotopic. -/
abbrev spaceJacobiZariskiHomologySequence (j : ℤ) :
    ShortComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C)) :=
  ShortComplex.mk
    (HomologicalComplex.homologyMap (spaceBaseChangeNaiveCotangentMap A B C a b) j)
    (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) j)
    (homologyMap_spaceBaseChange_comp_relative A B C a b j)

/-- **Stacks 0E1Y, exactness at `H^{-1}(NL_{C/A})`.**  For morphisms `A ⟶ B ⟶ C` of sheaves of
commutative rings on a topological space the sequence

`H^{-1}(NL_{B/A} ⊗_B C) ⟶ H^{-1}(NL_{C/A}) ⟶ H^{-1}(NL_{C/B})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E1Y "exactness of the six-term sequence of cohomology sheaves at the node \
H^{-1}(NL_{C/A}), for the maps induced by the two canonical maps c_1 and g"]
theorem exact_spaceJacobiZariskiHomologySequence_negOne :
    (spaceJacobiZariskiHomologySequence A B C a b (-1)).Exact := by
  refine AlgebraicGeometry.SheafOfModules.exact_homologyShortComplex_of_forall_stalk
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C)
    (spaceBaseChangeNaiveCotangentMap A B C a b)
    (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1)
    (homologyMap_spaceBaseChange_comp_relative A B C a b (-1))
    (fun z => homologyMap_stalk_spaceBaseChange_comp_relative A B C a b z (-1)) fun z => ?_
  exact HomologicalComplex.exact_homologyMap_of_exists_cycle
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (spaceBaseChangeNaiveCotangentMap A B C a b))
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (spaceRelativeNaiveCotangentComplexMap A B C a b)) (-1) 0 (-2)
    (by rw [CochainComplex.next]; ring) (by rw [CochainComplex.prev]; ring)
    ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) B C b (-2)
        (by decide) (by decide))).eq_of_src _ _)
    (homologyMap_stalk_spaceBaseChange_comp_relative A B C a b z (-1))
    fun y hy hg => exists_cycle_stalk A B C a b z y hy hg

/-- **Stacks 0E1Y, exactness at `H⁰(NL_{C/A})`.**  For morphisms `A ⟶ B ⟶ C` of sheaves of
commutative rings on a topological space the sequence

`H⁰(NL_{B/A} ⊗_B C) ⟶ H⁰(NL_{C/A}) ⟶ H⁰(NL_{C/B})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E1Y "exactness of the six-term sequence of cohomology sheaves at the node \
H^0(NL_{C/A}), for the maps induced by the two canonical maps c_1 and g"]
theorem exact_spaceJacobiZariskiHomologySequence_zero :
    (spaceJacobiZariskiHomologySequence A B C a b 0).Exact := by
  refine AlgebraicGeometry.SheafOfModules.exact_homologyShortComplex_of_forall_stalk
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C)
    (spaceBaseChangeNaiveCotangentMap A B C a b)
    (spaceRelativeNaiveCotangentComplexMap A B C a b) 0
    (homologyMap_spaceBaseChange_comp_relative A B C a b 0)
    (fun z => homologyMap_stalk_spaceBaseChange_comp_relative A B C a b z 0) fun z => ?_
  exact HomologicalComplex.exact_homologyMap_of_exists_add_d
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (spaceBaseChangeNaiveCotangentMap A B C a b))
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (spaceRelativeNaiveCotangentComplexMap A B C a b)) (-1) 0 1
    (by rw [CochainComplex.prev]; ring) (by rw [CochainComplex.next]; ring)
    ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (CategoryTheory.Functor.map_isZero
        (towerExtendScalars.{u, u, u} (Opens.grothendieckTopology T) B C b)
        (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A B a 1
          (by decide) (by decide)))).eq_of_tgt _ _)
    (homologyMap_stalk_spaceBaseChange_comp_relative A B C a b z 0)
    fun y hy => exists_add_d_stalk A B C a b z y hy

/-! ### The comparison with the shifted cone in degree `-1` -/

/-- **The connecting morphism `H^{-2}(NL_{C/B}) ⟶ H^{-1}(C(g)[-1])` of the cone is zero**, its
source being a zero object: the naive cotangent complex has no cohomology in degree `-2`. -/
theorem spaceNaiveCotangentConeHomologyConnecting_negTwo_eq_zero :
    spaceNaiveCotangentConeHomologyConnecting A B C a b (-2) (-1) (by ring) = 0 :=
  (naiveCotangentComplex_isZero_homology.{u, u, u} (Opens.grothendieckTopology T) B C b (-2)
    (by decide) (by decide)).eq_of_src _ _

/-- **The projection `H^{-1}(C(g)[-1]) ⟶ H^{-1}(NL_{C/A})` of the shifted cone is a
monomorphism**: the long exact sequence of the cone has a zero object to its left in that
degree. -/
theorem mono_homologyMap_pShift_negOne :
    Mono (HomologicalComplex.homologyMap
      (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) (-1)) :=
  (ShortComplex.exact_iff_mono _
      (spaceNaiveCotangentConeHomologyConnecting_negTwo_eq_zero A B C a b)).1
    (spaceNaiveCotangentCone_homology_exact_cone A B C a b (-2) (-1) (by ring))

/-- **Stacks 0E1Y: the canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` is surjective on
`H^{-1}`.**  This is half of the comparison the six-term exact sequence of Stacks 0E1Y rests on;
the other half, that `H⁰(c)` is an isomorphism, is
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`.

With the projection of the shifted cone onto `NL_{C/A}` the composite is `c₁`, whose image on
`H^{-1}` is the kernel of `H^{-1}(g)` by
`Stacks.SheafOfModules.exact_spaceJacobiZariskiHomologySequence_negOne`; that kernel is also the
image of the projection, by the long exact sequence of the cone, and the projection is a
monomorphism in that degree. -/
theorem epi_homologyMap_spaceNaiveCotangentConeMap_negOne :
    Epi (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) (-1)) := by
  have := mono_homologyMap_pShift_negOne A B C a b
  exact CategoryTheory.epi_of_exact_of_exact_of_mono _ _ _ _
    (spaceNaiveCotangentConeMap_homologyMap_comp_pShift A B C a b (-1))
    (homologyMap_spaceBaseChange_comp_relative A B C a b (-1))
    (CochainComplex.homologyMap_pShift_comp_homologyMap
      (spaceRelativeNaiveCotangentComplexMap A B C a b) (-2) (-1) (by ring))
    (exact_spaceJacobiZariskiHomologySequence_negOne A B C a b)
    (spaceNaiveCotangentCone_homology_exact_source A B C a b (-2) (-1) (by ring))

/-! ### The final `⟶ 0` of the sequence -/

/-- **Stacks 0E1Y, the final `⟶ 0` of the six-term sequence**: the canonical map
`g : NL_{C/A} ⟶ NL_{C/B}` is surjective on `H⁰`, that is, the sequence of cohomology sheaves is
exact at `H⁰(NL_{C/B})`.

Epimorphy is stalkwise, and at a stalk this is the surjectivity clause of Algebra, Lemma 00S2
over the canonical presentations of the stalk rings. -/
@[stacks 0E1Y "the final `-> 0` of the six-term sequence of cohomology sheaves, that is, its \
exactness at H^0(NL_{C/B}): the map induced by the canonical map g is surjective"]
theorem epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero :
    Epi (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) 0) := by
  refine (AlgebraicGeometry.SheafOfModules.epi_homologyMap_iff_forall_stalk
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C)
    (spaceRelativeNaiveCotangentComplexMap A B C a b) 0).2 fun z => ?_
  exact HomologicalComplex.epi_homologyMap_of_epi_opcyclesMap _ 0 1
    (by rw [CochainComplex.next]; ring)
    ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b) 1
        (by decide) (by decide))).eq_of_tgt _ _)
    ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) B C b 1
        (by decide) (by decide))).eq_of_tgt _ _)
    (HomologicalComplex.epi_opcyclesMap_of_surjective _ (-1) 0
      (by rw [CochainComplex.prev]; ring) fun y => exists_add_d_relative_stalk A B C a b z y)

end Space

/-! ### Ringed spaces -/

section RingedSpace

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` induces an isomorphism nowhere; what is an
isomorphism is the identification `Stacks.SheafOfModules.pulledNaiveCotangentComparison` of
Stacks 08TM out of which it is built, and that is what this records on cohomology sheaves. -/
instance isIso_homologyMap_pulledNaiveCotangentComparison (j : ℤ) :
    IsIso (HomologicalComplex.homologyMap (pulledNaiveCotangentComparison f g).hom j) :=
  ⟨HomologicalComplex.homologyMap (pulledNaiveCotangentComparison f g).inv j,
    by rw [← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id,
      HomologicalComplex.homologyMap_id],
    by rw [← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
      HomologicalComplex.homologyMap_id]⟩

/-- **On cohomology sheaves the composite of the two canonical maps of Stacks 0E1Z is zero.**
The first is the identification of Stacks 08TM followed by the canonical map `c₁` of the tower
`(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`, whose composite with the canonical map `g` of that tower is null
homotopic. -/
theorem homologyMap_ringedSpaceBaseChange_comp_relative (j : ℤ) :
    HomologicalComplex.homologyMap ((pulledNaiveCotangentComparison f g).hom ≫
          spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g) (inverseImageMiddleRing f)
            X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) j ≫
        HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
          (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
          (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) j = 0 :=
  (congrArg (fun t => t ≫ HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) j)
      (HomologicalComplex.homologyMap_comp (pulledNaiveCotangentComparison f g).hom
        (spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g) (inverseImageMiddleRing f)
          X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) j)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => HomologicalComplex.homologyMap
            (pulledNaiveCotangentComparison f g).hom j ≫ t)
          (homologyMap_spaceBaseChange_comp_relative (inverseImageBaseRing f g)
            (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
            (ringedSpaceStructureMap f) j)).trans (Limits.comp_zero)))

/-- **The sequence of cohomology sheaves of Stacks 0E1Z in degree `j`**:
`H^j(f^*NL_{Y/Z}) ⟶ H^j(NL_{X/Z}) ⟶ H^j(NL_{X/Y})`.  The first map is induced by the canonical
map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` of Stacks 0E1Z, which is the identification of Stacks 08TM followed
by the canonical map `c₁` of the tower `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`
(`Stacks.NaiveCotangentCompositionTriangle.pulledNaiveCotangentMap`), and the second by the
canonical map `g` of that tower. -/
abbrev ringedSpaceJacobiZariskiHomologySequence (j : ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.homologyMap ((pulledNaiveCotangentComparison f g).hom ≫
      spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g) (inverseImageMiddleRing f)
        X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) j)
    (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
      (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
      (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) j)
    (homologyMap_ringedSpaceBaseChange_comp_relative f g j)

/-- The sequence of Stacks 0E1Z is the sequence of Stacks 0E1Y for the tower
`(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X` with its first term transported along the isomorphism of
Stacks 08TM. -/
def ringedSpaceJacobiZariskiHomologySequenceIso (j : ℤ) :
    ringedSpaceJacobiZariskiHomologySequence f g j ≅
      spaceJacobiZariskiHomologySequence (inverseImageBaseRing f g) (inverseImageMiddleRing f)
        X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f) j :=
  ShortComplex.isoMk
    (asIso (HomologicalComplex.homologyMap (pulledNaiveCotangentComparison f g).hom j))
    (Iso.refl _) (Iso.refl _)
    ((HomologicalComplex.homologyMap_comp (pulledNaiveCotangentComparison f g).hom
          (spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g)
            (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
            (ringedSpaceStructureMap f)) j).symm.trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Stacks 0E1Z, exactness at `H^{-1}(NL_{X/Z})`.**  For composable morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` the sequence

`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E1Z "exactness of the six-term sequence of cohomology sheaves at the node \
H^{-1}(NL_{X/Z}), for the maps induced by the canonical maps f^*NL_{Y/Z} -> NL_{X/Z} and \
NL_{X/Z} -> NL_{X/Y}"]
theorem exact_ringedSpaceJacobiZariskiHomologySequence_negOne :
    (ringedSpaceJacobiZariskiHomologySequence f g (-1)).Exact :=
  ShortComplex.exact_of_iso (ringedSpaceJacobiZariskiHomologySequenceIso f g (-1)).symm
    (exact_spaceJacobiZariskiHomologySequence_negOne (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f))

/-- **Stacks 0E1Z, exactness at `H⁰(NL_{X/Z})`.**  For composable morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` the sequence

`H⁰(f^*NL_{Y/Z}) ⟶ H⁰(NL_{X/Z}) ⟶ H⁰(NL_{X/Y})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E1Z "exactness of the six-term sequence of cohomology sheaves at the node \
H^0(NL_{X/Z}), for the maps induced by the canonical maps f^*NL_{Y/Z} -> NL_{X/Z} and \
NL_{X/Z} -> NL_{X/Y}"]
theorem exact_ringedSpaceJacobiZariskiHomologySequence_zero :
    (ringedSpaceJacobiZariskiHomologySequence f g 0).Exact :=
  ShortComplex.exact_of_iso (ringedSpaceJacobiZariskiHomologySequenceIso f g 0).symm
    (exact_spaceJacobiZariskiHomologySequence_zero (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f))

/-- **Stacks 0E1Z: the canonical map `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` is surjective on
`H^{-1}`.**  It is the identification of Stacks 08TM, an isomorphism, followed by the canonical
map of Stacks 0E1Y for the tower `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`, which is surjective on `H^{-1}`
by `Stacks.SheafOfModules.epi_homologyMap_spaceNaiveCotangentConeMap_negOne`. -/
theorem epi_homologyMap_ringedSpaceNaiveCotangentConeMap_negOne :
    Epi (HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) (-1)) := by
  have := epi_homologyMap_spaceNaiveCotangentConeMap_negOne (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)
  have hcomp : HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) (-1) =
      HomologicalComplex.homologyMap (pulledNaiveCotangentComparison f g).hom (-1) ≫
        HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f)) (-1) :=
    HomologicalComplex.homologyMap_comp _ _ (-1)
  rw [hcomp]
  infer_instance

/-- **Stacks 0E1Z, the final `⟶ 0` of the six-term sequence**: the canonical map
`NL_{X/Z} ⟶ NL_{X/Y}` is surjective on `H⁰`, that is, the sequence of cohomology sheaves is exact
at `H⁰(NL_{X/Y})`.  This is the statement of Stacks 0E1Y for the tower
`(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`. -/
@[stacks 0E1Z "the final `-> 0` of the six-term sequence of cohomology sheaves, that is, its \
exactness at H^0(NL_{X/Y}): the map induced by the canonical map NL_{X/Z} -> NL_{X/Y} is \
surjective"]
theorem epi_homologyMap_ringedSpaceRelativeNaiveCotangentComplexMap_zero :
    Epi (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
      (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
      (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) 0) :=
  epi_homologyMap_spaceRelativeNaiveCotangentComplexMap_zero (inverseImageBaseRing f g)
    (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)

end RingedSpace

end Stacks.SheafOfModules

end

end
