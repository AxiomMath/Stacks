module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToSequenceIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagSheaf

/-!
# The cohomology spectral sequence of a simplicial site (Stacks 09WJ)

Let `S` be a simplicial-site situation (Stacks 09WE), with total site `C_total` and component
sites `C_n`, and let `K` be an object of `D^+(C_total)`. Stacks 09WJ asserts a spectral sequence
`(E_r, d_r)` with

```
E_1^{p,q} = H^q(C_p, K_p),   d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}
```

converging to `H^{p+q}(C_total, K)`, **functorial in `K`**. This file builds it.

`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceTagSheaf.lean` builds the
same statement for an abelian sheaf `F` on the total site, i.e. for `K = F[0]`, with
functoriality in `F` over the category of abelian sheaves. Here the functoriality is over
`D^+(C_total)`, as the source asks.

## The construction

The spectral sequence of the double complex

```
A^{q,p} = Γ(C_p, Z^q_p)
```

of a cochain complex `Z^•` of abelian sheaves on the total site is already functorial in `Z^•`
over the category of complexes: `CategoryTheory.SimplicialSiteSituation.complexSpectralSequence`.
Read from its first page it kills homotopies, because the complex of Stacks 0D77 is additive and
a filtered homotopy of double complexes induces the same maps on the pages from the first on
(`HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂`), so it descends to the
homotopy category and in particular to `K^+(C_total)`.

The passage from `K^+(C_total)` to `D^+(C_total)` is the **right derived functor** of that
functor along `DerivedCategory.Plus.Qh`. It exists for any functor out of `K^+(C_total)`, the
inclusion of the bounded below homotopy category of complexes of injectives being a right
derivability structure, and its unit is invertible exactly at a bounded below complex of
injectives. So the value at `K` *is* the spectral sequence of the double complex
`A^{q,p} = Γ(C_p, I^q_p)` of the source's proof, for `I^•` any bounded below complex of
injectives representing `K` -- and it is a functor of `K` on the nose, with no choice of
resolution anywhere in its definition.

The first page and the abutment are then read off that description.

* The first page is identified by the uniqueness of right derived functors: reading the first
  page in the bidegree `(p, q)` out of the spectral sequence of a bounded below complex `Z^•` is
  `H^q(Γ(C_p, Z^•_p))` (`plusPageOneNatIso`, which is
  `CategoryTheory.SimplicialSiteSituation.pageOneIsoComponentSections` with its naturality), and
  that functor is also what `R^q Γ(C_p, (-)_p)` derives. Restriction to `C_p` is exact
  (Stacks 09WG (7)) and preserves injectives (Stacks 09WH), so `R^q Γ(C_p, (-)_p)` is the sheaf
  cohomology `H^q(C_p, K_p)` of the restriction.
* The abutment is read at one bounded below complex of injectives `I^•` representing `K`, which
  exists and is enough because the statement is a proposition: the filtration of `Tot(A^{•,•})`
  by the simplicial coordinate is degreewise finite, so Stacks 012W gives convergence onto
  `H^n(Tot(A^{•,•}))`; the comparison of Stacks 0133 identifies that with
  `H^n(Γ(C_total, I^•))`; and the unit of the right derived functor of `Γ(C_total, -)`
  identifies that with `H^n(C_total, K)`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.derivedSpectralSequence`: **the spectral sequence of
  Stacks 09WJ**, as a functor on `D^+(C_total)`.
* `CategoryTheory.SimplicialSiteSituation.componentDerivedCohomologyFunctor`: `H^q(C_p, K_p)`,
  the sheaf cohomology on the component site of the restriction of an object of `D^+(C_total)`.
* `CategoryTheory.SimplicialSiteSituation.totalDerivedCohomologyFunctor`: `H^n(C_total, K)`.
* `CategoryTheory.SimplicialSiteSituation.complexSpectralSequence`,
  `homotopySpectralSequence`, `plusSpectralSequence`: the spectral sequence of the double
  complex as a functor of a cochain complex, of its homotopy class, and of a bounded below
  homotopy class.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedSpectralSequence_pageOneIso`:
  **`E_1^{p,q} = H^q(C_p, K_p)`**, naturally in `K`.
* `CategoryTheory.SimplicialSiteSituation.isZero_derivedPageOne_d_of_ne`:
  **`d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`**, i.e. the differential of the first page out of
  `(p, q)` is zero into every bidegree other than `(p + 1, q)`.
* `CategoryTheory.SimplicialSiteSituation.derivedSpectralSequence_abutsTo`: **the spectral
  sequence abuts to `H^{p+q}(C_total, K)`**.
* `CategoryTheory.SimplicialSiteSituation.isIso_derivedSpectralSequenceUnit_app`: the spectral
  sequence at `K` is the spectral sequence of the double complex `A^{q,p} = Γ(C_p, I^q_p)` of a
  bounded below complex of injectives representing `K`.

## Implementation notes

The spectral sequence is presented from its first page, as a
`CohomologicalSpectralSequence Ab.{u} 1`, and that is forced: the zeroth page of the double
complex's spectral sequence is not homotopy invariant, so a functor of `K` cannot carry it. The
source's `(E_r, d_r)_{r ≥ 0}` is read from `r = 1`, which is where its display lives; the pages
below are available for a complex, before the passage to the derived category, as
`CategoryTheory.SimplicialSiteSituation.sectionsSpectralSequence`. This is the presentation of
the topological analogue `Stacks.Topology.Simplicial.cohomologySpectralSequence` of
Stacks 09W6 and of the abelian-sheaf case in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceTagSheaf.lean`.

`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceBoundedBelow.lean`
supplies the convergence and the comparison of Stacks 0133 for a complex bounded below in an
arbitrary degree; the versions in the two files below this one assume vanishing in the negative
degrees, which a complex of injectives representing an object of `D^+(C_total)` need not satisfy.

Nothing here carries a hypothesis about Stacks 09WG (6). The identification of the summand
inclusions of its sum formula on underlying sheaves of sets — which the integral resolution of
Stacks 09WI used to take as an assumption — is proved for an arbitrary simplicial-site situation
by `CategoryTheory.SimplicialSiteSituation.summandForgetCompatibility`, so the three modules
this one builds on state their results unconditionally and so does it.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 0D77](https://stacks.math.columbia.edu/tag/0D77)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

attribute [local instance] HasDerivedCategory.standard

/-! ### The spectral sequence of a complex of abelian sheaves, read from its first page -/

/-- **The spectral sequence of the double complex `A^{q,p} = Γ(C_p, Z^q_p)`, as a functor of the
cochain complex `Z^•`**, presented from its first page. -/
def complexSpectralSequence :
    CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ ⥤ CohomologicalSpectralSequence Ab.{u} 1 where
  obj Z := (S.sectionsSpectralSequence Z).shiftStart zero_le_one
  map φ := CategoryTheory.SpectralSequence.shiftStartMap
    (HomologicalComplex₂.spectralSequenceMap₂
      (S.sectionsDoubleComplexFunctor.map φ)) zero_le_one
  map_id Z := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    rw [CategoryTheory.Functor.map_id, HomologicalComplex₂.spectralSequenceMap₂_id]
    rfl
  map_comp φ ψ := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex₂.spectralSequenceMap₂_comp]
    rfl

/-- **Homotopic morphisms of complexes induce the same morphism of spectral sequences**, from the
first page on: the complex of Stacks 0D77 is additive, so it carries a homotopy to a homotopy of
total complexes compatible with the filtration by the simplicial coordinate. -/
theorem complexSpectralSequence_map_eq_of_homotopy
    {Z W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ} {φ ψ : Z ⟶ W} (H : Homotopy φ ψ) :
    S.complexSpectralSequence.map φ = S.complexSpectralSequence.map ψ :=
  CategoryTheory.SpectralSequence.hom_ext fun r hr =>
    HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (HomologicalComplex₂.filteredHomotopy₂_of_homotopy
        (S.cechSectionsComplexZ.mapHomotopy H)) (show (1 : ℤ) ≤ r by omega)

/-- **The spectral sequence of a complex of abelian sheaves descends to the homotopy
category.** -/
def homotopySpectralSequence :
    HomotopyCategory (Sheaf S.totalTopology Ab.{u}) (ComplexShape.up ℤ) ⥤
      CohomologicalSpectralSequence Ab.{u} 1 :=
  CategoryTheory.Quotient.lift (homotopic (Sheaf S.totalTopology Ab.{u}) (ComplexShape.up ℤ))
    S.complexSpectralSequence
    fun _ _ _ _ h => S.complexSpectralSequence_map_eq_of_homotopy h.some

/-- The spectral sequence of the double complex, as a functor on the bounded below homotopy
category of abelian sheaves on the total site. -/
abbrev plusSpectralSequence :
    HomotopyCategory.Plus (Sheaf S.totalTopology Ab.{u}) ⥤
      CohomologicalSpectralSequence Ab.{u} 1 :=
  HomotopyCategory.Plus.ι (Sheaf S.totalTopology Ab.{u}) ⋙ S.homotopySpectralSequence

/-! ### The spectral sequence of an object of `D^+(C_total)` -/

/-- **Stacks 09WJ, the spectral sequence.** For an object `K` of `D^+(C_total)` there is a
cohomological spectral sequence, functorial in `K`: the right derived functor, along the
localization of the bounded below homotopy category at the quasi-isomorphisms, of the spectral
sequence of the double complex `A^{q,p} = Γ(C_p, Z^q_p)` read from its first page.

A bounded below complex of injectives `I^•` representing `K` is exactly an object at which the
unit of this right derived functor is invertible
(`isIso_derivedSpectralSequenceUnit_app`), so the value at `K` *is* the spectral sequence of the
double complex `A^{q,p} = Γ(C_p, I^q_p)` of the source's proof. -/
@[stacks 09WJ "the spectral sequence for K in D^+(C_total), as a functor of K"]
def derivedSpectralSequence :
    DerivedCategory.Plus (Sheaf S.totalTopology Ab.{u}) ⥤
      CohomologicalSpectralSequence Ab.{u} 1 :=
  S.plusSpectralSequence.totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Sheaf S.totalTopology Ab.{u}))

/-- The unit of the right derived functor `derivedSpectralSequence`: the comparison of the
spectral sequence of a bounded below complex with the one attached to the object it represents in
`D^+(C_total)`. -/
def derivedSpectralSequenceUnit :
    S.plusSpectralSequence ⟶
      DerivedCategory.Plus.Qh ⋙ S.derivedSpectralSequence :=
  S.plusSpectralSequence.totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Sheaf S.totalTopology Ab.{u}))

/-- `derivedSpectralSequence`, with unit `derivedSpectralSequenceUnit`, is a right derived functor
of `plusSpectralSequence` with respect to the quasi-isomorphisms. -/
instance isRightDerivedFunctor_derivedSpectralSequence :
    S.derivedSpectralSequence.IsRightDerivedFunctor
      S.derivedSpectralSequenceUnit
      (HomotopyCategory.Plus.quasiIso (Sheaf S.totalTopology Ab.{u})) := by
  dsimp only [derivedSpectralSequence, derivedSpectralSequenceUnit]
  infer_instance

/-- **The unit is invertible at a bounded below complex of injective abelian sheaves.** This is
the statement that the spectral sequence of Stacks 09WJ at an object `K` of `D^+(C_total)` is the
spectral sequence of the double complex `A^{q,p} = Γ(C_p, I^q_p)` of any bounded below complex of
injectives `I^•` representing `K`, which is how the source constructs it. -/
instance isIso_derivedSpectralSequenceUnit_app
    (M : HomotopyCategory.Plus (Sheaf S.totalTopology Ab.{u}))
    [∀ i : ℤ, Injective (M.obj.as.X i)] :
    IsIso (S.derivedSpectralSequenceUnit.app M) :=
  inferInstance

/-! ### The first page -/

/-- Reading off the term of the first page in a fixed bidegree. -/
abbrev pageOneEval (p q : ℤ) : CohomologicalSpectralSequence Ab.{u} 1 ⥤ Ab.{u} :=
  CategoryTheory.SpectralSequence.pageFunctor Ab.{u} _ 1 1 le_rfl ⋙
    HomologicalComplex.eval Ab.{u} _ (p, q)

/-- **`E_1^{n,q} = H^q(Γ(C_n, Z^•_n))`, naturally in the complex `Z^•`.** This is
`CategoryTheory.SimplicialSiteSituation.pageOneIsoComponentSections` with its naturality. -/
def complexPageOneNatIso (n : ℕ) (q : ℤ) :
    S.complexSpectralSequence ⋙ pageOneEval (n : ℤ) q ≅
      (S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) q :=
  NatIso.ofComponents
    (fun Z =>
      HomologicalComplex₂.isoOnePageTotalFiltration₂ (S.sectionsDoubleComplex Z) _
          (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) (n : ℤ) q ≪≫
        (S.columnHomologyNatIso n q).app Z)
    fun {_ _} φ =>
      square_comp
        (HomologicalComplex₂.isoOnePageTotalFiltration₂_naturality_functor
          (S.sectionsDoubleComplexFunctor.map φ) (n : ℤ) q)
        ((S.columnHomologyNatIso n q).hom.naturality φ)

/-- The spectral sequence on the homotopy category is induced by the one on complexes. -/
def quotientCompHomotopySpectralSequenceIso :
    HomotopyCategory.quotient (Sheaf S.totalTopology Ab.{u}) (ComplexShape.up ℤ) ⋙
        S.homotopySpectralSequence ≅ S.complexSpectralSequence :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- **`E_1^{n,q} = H^q(Γ(C_n, Z^•_n))` on the homotopy category.** Both sides of
`complexPageOneNatIso` kill homotopies, so the identification descends. -/
def homotopyPageOneNatIso (n : ℕ) (q : ℤ) :
    S.homotopySpectralSequence ⋙ pageOneEval (n : ℤ) q ≅
      (S.componentSectionsFunctor ⦋n⦌).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor Ab.{u} (ComplexShape.up ℤ) q :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight S.quotientCompHomotopySpectralSequenceIso
        (pageOneEval (n : ℤ) q) ≪≫
      S.complexPageOneNatIso n q ≪≫
      Functor.isoWhiskerLeft
        ((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.homologyFunctorFactors Ab.{u} (ComplexShape.up ℤ) q).symm ≪≫
      Functor.isoWhiskerRight
        (((S.componentSectionsFunctor ⦋n⦌).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).symm)
        (HomotopyCategory.homologyFunctor Ab.{u} (ComplexShape.up ℤ) q))

/-- The `q`-th homology of the image in `D^+(Ab)` of a bounded below complex of abelian groups is
its `q`-th cohomology. -/
def plusQhHomologyIso (q : ℤ) :
    DerivedCategory.Plus.Qh (C := Ab.{u}) ⋙ DerivedCategory.Plus.homologyFunctor Ab.{u} q ≅
      HomotopyCategory.Plus.ι Ab.{u} ⋙
        HomotopyCategory.homologyFunctor Ab.{u} (ComplexShape.up ℤ) q :=
  Functor.isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh Ab.{u})
      (DerivedCategory.homologyFunctor Ab.{u} q) ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι Ab.{u})
      (DerivedCategory.homologyFunctorFactorsh Ab.{u} q)

/-- **`E_1^{n,q} = H^q(Γ(C_n, Z^•_n))` on the bounded below homotopy category**, with the
right-hand side read as the `q`-th homology of the image of `Γ(C_n, (-)_n)` applied degreewise in
the bounded below derived category of abelian groups. That is the source functor of the unit of
the right derived functor of `Γ(C_n, (-)_n)`, which is what makes the comparison of the two
right derived functors below possible. -/
def plusPageOneNatIso (n : ℕ) (q : ℤ) :
    S.plusSpectralSequence ⋙ pageOneEval (n : ℤ) q ≅
      (S.componentSectionsFunctor ⦋n⦌).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor Ab.{u} q :=
  Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι (Sheaf S.totalTopology Ab.{u}))
      (S.homotopyPageOneNatIso n q) ≪≫
    Functor.isoWhiskerLeft ((S.componentSectionsFunctor ⦋n⦌).mapHomotopyCategoryPlus)
      (plusQhHomologyIso q).symm

section PageOne

variable (n : ℕ) (q : ℤ)

/-- Reading the first page in a fixed bidegree out of the spectral sequence of Stacks 09WJ is the
right derived functor of reading it out of the spectral sequence of a bounded below complex: the
unit is invertible at a complex of injectives, and `pageOneEval` carries an isomorphism to an
isomorphism. -/
instance isRightDerivedFunctor_derivedSpectralSequence_comp_pageOneEval :
    (S.derivedSpectralSequence ⋙ pageOneEval (n : ℤ) q).IsRightDerivedFunctor
      (Functor.whiskerRight S.derivedSpectralSequenceUnit (pageOneEval (n : ℤ) q))
      (HomotopyCategory.Plus.quasiIso (Sheaf S.totalTopology Ab.{u})) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (S.plusSpectralSequence ⋙ pageOneEval (n : ℤ) q)).isRightDerivedFunctor_of_isIso
    _ fun _ => by rw [Functor.whiskerRight_app]; infer_instance

/-- The `q`-th homology of the right derived functor of `Γ(C_n, (-)_n)` is the right derived
functor of the `q`-th cohomology of the complex of sections. -/
instance isRightDerivedFunctor_componentSections_comp_homologyFunctor :
    ((S.componentSectionsFunctor ⦋n⦌).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor Ab.{u} q).IsRightDerivedFunctor
      (Functor.whiskerRight (S.componentSectionsFunctor ⦋n⦌).rightDerivedFunctorPlusUnith
        (DerivedCategory.Plus.homologyFunctor Ab.{u} q))
      (HomotopyCategory.Plus.quasiIso (Sheaf S.totalTopology Ab.{u})) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      ((S.componentSectionsFunctor ⦋n⦌).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
        DerivedCategory.Plus.homologyFunctor Ab.{u} q)).isRightDerivedFunctor_of_isIso
    _ fun _ => by rw [Functor.whiskerRight_app]; infer_instance

/-- **`E_1^{n,q} = R^q Γ(C_n, K_n)`.** The first page of the spectral sequence of Stacks 09WJ at
`(n, q)` is the `q`-th homology of the right derived functor of `Γ(C_n, (-)_n)`, naturally in the
object of `D^+(C_total)`.

Both sides are right derived functors of the same functor on the bounded below homotopy category
-- `Z^• ↦ H^q(Γ(C_n, Z^•_n))`, which is `plusPageOneNatIso` -- so they agree by the uniqueness of
right derived functors. -/
def derivedPageOneNatIso :
    S.derivedSpectralSequence ⋙ pageOneEval (n : ℤ) q ≅
      (S.componentSectionsFunctor ⦋n⦌).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor Ab.{u} q :=
  Functor.rightDerivedNatIso _ _
    (Functor.whiskerRight S.derivedSpectralSequenceUnit (pageOneEval (n : ℤ) q))
    (Functor.whiskerRight (S.componentSectionsFunctor ⦋n⦌).rightDerivedFunctorPlusUnith
      (DerivedCategory.Plus.homologyFunctor Ab.{u} q))
    (HomotopyCategory.Plus.quasiIso (Sheaf S.totalTopology Ab.{u}))
    (S.plusPageOneNatIso n q)

/-- **`H^q(C_n, K_n)`**: the `q`-th cohomology on the component site `C_n` of the restriction to
`C_n` of an object of `D^+(C_total)`. Restriction is exact (Stacks 09WG (7)), so it induces a
functor on the bounded below derived categories, and `H^q(C_n, -)` is the `q`-th homology of the
right derived functor of `Γ(C_n, -)`. -/
def componentDerivedCohomologyFunctor :
    DerivedCategory.Plus (Sheaf S.totalTopology Ab.{u}) ⥤ Ab.{u} :=
  (S.restrictAb ⦋n⦌).mapDerivedCategoryPlus ⋙
    (Sheaf.Γ (S.componentTopology ⦋n⦌) Ab.{u}).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor Ab.{u} q

/-- **Stacks 09WG (7) and Stacks 09WH on `D^+`**: the `q`-th homology of the right derived
functor of `Γ(C_n, (-)_n)` is the sheaf cohomology `H^q(C_n, K_n)` of the restriction.

Restriction to the component carries an injective abelian sheaf to an injective one (Stacks
09WH), hence to an object right acyclic for `Γ(C_n, -)`, so the composition isomorphism of
Stacks 015M applies; and restriction being exact (Stacks 09WG (7)) its right derived functor is
the induced functor on `D^+`. -/
def rightDerivedComponentSectionsPlusNatIso :
    (S.componentSectionsFunctor ⦋n⦌).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor Ab.{u} q ≅
      S.componentDerivedCohomologyFunctor n q :=
  Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic (S.restrictAb ⦋n⦌)
        (Sheaf.Γ (S.componentTopology ⦋n⦌) Ab.{u})
        (fun I hI => letI := hI; Functor.rightAcyclic_of_injective _
          ((S.restrictAb ⦋n⦌).obj I)) ≪≫
      Functor.isoWhiskerRight
        (S.restrictAb ⦋n⦌).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (Sheaf.Γ (S.componentTopology ⦋n⦌) Ab.{u}).rightDerivedFunctorPlus)
    (DerivedCategory.Plus.homologyFunctor Ab.{u} q)

/-- **Stacks 09WJ, the first page.** `E_1^{p,q} = H^q(C_p, K_p)`: the first page of the spectral
sequence of Stacks 09WJ at `(p, q)` is the sheaf cohomology on the component site `C_p` of the
restriction of `K` to `C_p`, naturally in the object `K` of `D^+(C_total)`.

Together with `isZero_derivedPageOne_d_of_ne`, which pins the shape of
`d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`, this is the first page and the first differential of
Stacks 09WJ. -/
@[stacks 09WJ "the first page E_1^{p,q} = H^q(C_p, K_p) for K in D^+(C_total), naturally in K"]
def derivedSpectralSequence_pageOneIso :
    S.derivedSpectralSequence ⋙ pageOneEval (n : ℤ) q ≅
      S.componentDerivedCohomologyFunctor n q :=
  S.derivedPageOneNatIso n q ≪≫ S.rightDerivedComponentSectionsPlusNatIso n q

end PageOne

/-! ### The first differential -/

/-- **Stacks 09WJ, the first differential.** `d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`: the
differential of the first page out of the bidegree `(p, q)` lands in the bidegree `(p + 1, q)`,
every other component being zero. Together with the type of
`CategoryTheory.SimplicialSiteSituation.derivedSpectralSequence`, which provides
`d (p, q) (p + 1, q) : E_1^{p,q} ⟶ E_1^{p+1,q}`, this is the shape of `d_1` that Stacks 09WJ
asserts. -/
@[stacks 09WJ "the first differential d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q} for K in D^+(C_total)"]
theorem isZero_derivedPageOne_d_of_ne (K : DerivedCategory.Plus (Sheaf S.totalTopology Ab.{u}))
    (p q p' q' : ℤ) (h : (p', q') ≠ (p + 1, q)) :
    ((S.derivedSpectralSequence.obj K).page 1 le_rfl).d (p, q) (p', q') = 0 := by
  refine HomologicalComplex.shape _ _ _ fun hc => h ?_
  have hc : (p, q) + ((1 : ℤ), 1 - (1 : ℤ)) = (p', q') := hc
  rw [← hc]
  simp

/-! ### The abutment is the cohomology of the total site -/

/-- **`H^n(C_total, K)`**: the sheaf cohomology of the total site, the `n`-th homology of the
right derived functor of `Γ(C_total, -)` on `D^+(C_total)`. -/
abbrev totalDerivedCohomologyFunctor (n : ℤ) :
    DerivedCategory.Plus (Sheaf S.totalTopology Ab.{u}) ⥤ Ab.{u} :=
  (Sheaf.Γ S.totalTopology Ab.{u}).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor Ab.{u} n

/-- **`H^n(Γ(C_total, I^•)) ≅ H^n(C_total, K)`** for a bounded below complex of injectives `I^•`
representing `K`: the unit of the right derived functor of `Γ(C_total, -)` is invertible at a
complex of injectives. -/
def totalSectionsHomologyIsoDerived (M : HomotopyCategory.Plus (Sheaf S.totalTopology Ab.{u}))
    [∀ i : ℤ, Injective (M.obj.as.X i)] (n : ℤ) :
    (S.totalSectionsComplex M.obj.as).homology n ≅
      (S.totalDerivedCohomologyFunctor n).obj (DerivedCategory.Plus.Qh.obj M) :=
  ((HomotopyCategory.homologyFunctorFactors Ab.{u} (ComplexShape.up ℤ) n).app
        (((Sheaf.Γ S.totalTopology Ab.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M.obj.as)).symm ≪≫
    ((plusQhHomologyIso n).app
      ((Sheaf.Γ S.totalTopology Ab.{u}).mapHomotopyCategoryPlus.obj M)).symm ≪≫
    asIso ((DerivedCategory.Plus.homologyFunctor Ab.{u} n).map
      ((Sheaf.Γ S.totalTopology Ab.{u}).rightDerivedFunctorPlusUnith.app M))

/-- **The convergence at a bounded below complex of injectives.** The spectral sequence of
Stacks 09WJ at the object represented by a bounded below complex of injectives `I^•` abuts to
`H^{p+q}(C_total, I^•)`.

It is the spectral sequence of the double complex `A^{q,p} = Γ(C_p, I^q_p)`, because the unit of
the right derived functor is invertible at `I^•`; that one abuts to `H^n(Tot(A^{•,•}))` because
the filtration by the simplicial coordinate is degreewise finite (Stacks 012W); the comparison of
Stacks 0133 identifies `H^n(Tot(A^{•,•}))` with `H^n(Γ(C_total, I^•))`; and the unit of the right
derived functor of `Γ(C_total, -)` identifies that with `H^n(C_total, I^•)`. -/
theorem derivedSpectralSequence_abutsTo_of_injective
    (M : HomotopyCategory.Plus (Sheaf S.totalTopology Ab.{u}))
    [∀ i : ℤ, Injective (M.obj.as.X i)] :
    CategoryTheory.SpectralSequence.AbutsTo
      (S.derivedSpectralSequence.obj (DerivedCategory.Plus.Qh.obj M))
      (fun n => (S.totalDerivedCohomologyFunctor n).obj (DerivedCategory.Plus.Qh.obj M)) := by
  obtain ⟨n₀, hn₀⟩ : CochainComplex.plus (Sheaf S.totalTopology Ab.{u}) M.obj.as := by
    have hp := M.property
    rwa [show M.obj = (HomotopyCategory.quotient _ _).obj M.obj.as from rfl,
      HomotopyCategory.plus_quotient_obj_iff] at hp
  have hzero : ∀ q : ℤ, q < n₀ → IsZero (M.obj.as.X q) := fun q hq =>
    CochainComplex.isZero_of_isStrictlyGE M.obj.as n₀ q hq
  have habuts : CategoryTheory.SpectralSequence.AbutsTo
      (S.complexSpectralSequence.obj M.obj.as)
      (fun n => (S.totalDerivedCohomologyFunctor n).obj (DerivedCategory.Plus.Qh.obj M)) :=
    ((S.sectionsSpectralSequence_abutsTo_total_of_isZero M.obj.as n₀ hzero).of_iso
      fun n =>
        (S.sectionsComparisonHomologyIso_of_isZero M.obj.as n₀ hzero
          (fun q => inferInstance) n).symm ≪≫
          S.totalSectionsHomologyIsoDerived M n).shiftStart zero_le_one
  have e₁ : S.complexSpectralSequence.obj M.obj.as ≅
      S.derivedSpectralSequence.obj (DerivedCategory.Plus.Qh.obj M) :=
    (S.quotientCompHomotopySpectralSequenceIso.app M.obj.as).symm ≪≫
      @asIso _ _ _ _ (S.derivedSpectralSequenceUnit.app M)
        (S.isIso_derivedSpectralSequenceUnit_app M)
  exact habuts.ofSequenceIso e₁

/-- **Stacks 09WJ, the convergence.** The spectral sequence of Stacks 09WJ abuts to
`H^{p+q}(C_total, K)`: its infinity page at `(p, q)` is the `p`-th graded piece of a finite
filtration of the sheaf cohomology of the total site in degree `p + q`.

Every object of `D^+(C_total)` is represented by a bounded below complex of injective abelian
sheaves -- the inclusion of the bounded below homotopy category of complexes of injectives into
`D^+(C_total)` is essentially surjective -- and at such a complex the convergence is
`derivedSpectralSequence_abutsTo_of_injective`. -/
@[stacks 09WJ "the abutment H^{p+q}(C_total, K) for K in D^+(C_total)"]
theorem derivedSpectralSequence_abutsTo
    (K : DerivedCategory.Plus (Sheaf S.totalTopology Ab.{u})) :
    CategoryTheory.SpectralSequence.AbutsTo (S.derivedSpectralSequence.obj K)
      (fun n => (S.totalDerivedCohomologyFunctor n).obj K) := by
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (InjectiveObject.ι (Sheaf S.totalTopology Ab.{u})).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh) K
  exact ((S.derivedSpectralSequence_abutsTo_of_injective
        ((InjectiveObject.ι (Sheaf S.totalTopology Ab.{u})).mapHomotopyCategoryPlus.obj Y)).of_iso
      fun n => (S.totalDerivedCohomologyFunctor n).mapIso e).ofSequenceIso
    (S.derivedSpectralSequence.mapIso e)

end CategoryTheory.SimplicialSiteSituation

end
