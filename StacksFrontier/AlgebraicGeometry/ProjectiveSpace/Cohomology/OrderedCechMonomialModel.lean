module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechWeightSplitting
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.OrderedChartIndexing
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups

/-!
# The ordered Čech complex of a twist on projective space is the monomial complex

Let `R` be a commutative ring and let `ℙⁿ_R = Proj R[T₀, …, Tₙ]` be covered by the `n + 1`
standard coordinate opens `D₊(Tᵢ)`. For a strictly increasing tuple `i₀ < ⋯ < i_p` of coordinate
indices the corresponding intersection of charts is the standard open `D₊(T_{i₀} ⋯ T_{i_p})`, so
the degree-`p` term of the ordered Čech complex of `𝒪(d)` is
$$ \prod_{i_0 < \cdots < i_p} \Gamma\bigl(D_+(T_{i_0} \cdots T_{i_p}), \mathcal{O}(d)\bigr), $$
and each factor is the free `R`-module on the degree-`d` Laurent monomials that are regular
outside `{i₀, …, i_p}`. This file identifies the ordered Čech cochains of the standard cover with
the explicit monomial cochains `Stacks.ProjectiveSpace.Cohomology.laurentCechCochains`, degree by
degree and compatibly with the differentials; it is the comparison of [Stacks, Tag 01XU] with the
combinatorial complex whose homology is computed in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/MiddleDegrees.lean`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.interChartAddEquiv`: a tuple with distinct entries selects a
  chart intersection, and the sections of `𝒪(d)` over it are the monomial chart of the set of
  values of the tuple.
* `Stacks.ProjectiveSpace.Cohomology.twistOrdFamilyAddEquiv`: the ordered Čech cochains, as the
  dependent product of the monomial charts over the strictly increasing tuples.
* `Stacks.ProjectiveSpace.Cohomology.twistOrdCochainEquiv`: **the degree-`p` ordered Čech cochains
  of `𝒪(d)` for the standard cover are the degree-`p` monomial Čech cochains.**

## Main results

* `Stacks.ProjectiveSpace.Cohomology.inter_eq_basicOpen_chartDenom`: the intersection of standard
  charts selected by a tuple with distinct entries is the standard open of the product of the
  corresponding coordinates.
* `Stacks.ProjectiveSpace.Cohomology.coe_twistOrdCochainEquiv_apply`: the monomial cochain
  attached to an ordered Čech cochain has, at the set of values of a tuple, the chart
  identification of the Čech component at that tuple.
* `Stacks.ProjectiveSpace.Cohomology.coe_ordInterChartAddEquiv_restr`: restriction of a section of
  `𝒪(d)` between two chart intersections is invisible in the ambient module of all Laurent
  coefficient families.
* `Stacks.ProjectiveSpace.Cohomology.twistOrdCochainEquiv_ordD`: **the identification carries the
  ordered Čech differential to the monomial Čech differential.**

## Implementation notes

**No `eqToHom`.** The equality of opens between a Čech chart intersection and the standard open of
a chart denominator is consumed as an inequality in each direction, through
`Stacks.Cohomology.Basis.res`; `Stacks.ProjectiveSpace.Cohomology.resAddEquivOfEq` packages the
two directions as an isomorphism of groups of sections, using only that restricting twice is
restricting once and that restricting along the identity does nothing.

**Why the proofs are in term mode.** Every statement below that mentions a Čech term crosses the
seam between `AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf`, which is a
`TopCat.Sheaf`, and the sheaf over `TopologicalSpace.Opens.grothendieckTopology` that the Čech
cochain groups are stated over. The two are definitionally equal but not at the transparency level
at which `rewrite` checks its motive, so `Eq.trans`, `congrArg` and `Subtype.ext` are used instead
of `rewrite` on such goals, and the restriction lemmas are applied as terms. No heartbeat option
is raised anywhere in this file.

**Where the submodules become invisible.** The monomial chart attached to a tuple depends on the
tuple, so statements about a value of the identification are phrased after coercion into the
ambient module `(Fin (n + 1) → ℤ) →₀ R` of all Laurent coefficient families, exactly as in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/OrderedChartIndexing.lean`. The chart
inclusions that the Čech differential is built from are identities there.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis (res res_id res_res)
open Stacks.Cohomology.CechSheaf (abSections)
open Stacks.ProjectiveCohomology (basicOpenXAtUniverse chartIndices polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### Chart intersections and chart denominators -/

/-- The chart denominator of the set of values of an injective tuple is the product of the
corresponding coordinates. -/
theorem chartDenom_image_univ (R : Type u) [CommRing R] (n p : ℕ)
    (f : Fin (p + 1) → Fin (n + 1)) (hf : Function.Injective f) :
    chartDenom R n (Finset.image f Finset.univ) = ∏ j, MvPolynomial.X (f j) := by
  rw [chartDenom, Finset.prod_image (fun a _ b _ h => hf h)]

/-- **The intersection of standard charts selected by a tuple with distinct entries is the
standard open of its chart denominator.** -/
theorem inter_eq_basicOpen_chartDenom (R : Type u) [CommRing R] (n p : ℕ)
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) (hx : Function.Injective (chartIndices x)) :
    CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
        (basicOpenXAtUniverse R n) x
      = ProjectiveSpectrum.basicOpen (polyGrading R n)
          (chartDenom R n (Finset.image (chartIndices x) Finset.univ)) := by
  rw [chartDenom_image_univ R n p _ hx]
  exact Stacks.ProjectiveCohomology.iInf_projectiveSpectrum_basicOpen_X R (chartIndices x)

/-- The set of values of a tuple indexed by a nonempty type is nonempty. -/
theorem image_univ_nonempty {n p : ℕ} (f : Fin (p + 1) → Fin (n + 1)) :
    (Finset.image f Finset.univ).Nonempty :=
  ⟨f 0, Finset.mem_image.2 ⟨0, Finset.mem_univ 0, rfl⟩⟩

/-- Omitting a position of a tuple shrinks its set of values. -/
theorem image_univ_succAbove_subset {n p : ℕ} (f : Fin (p + 2) → Fin (n + 1))
    (j : Fin (p + 2)) :
    Finset.image (f ∘ j.succAbove) Finset.univ ⊆ Finset.image f Finset.univ := by
  intro a ha
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 ha
  exact Finset.mem_image.2 ⟨j.succAbove k, Finset.mem_univ _, hk⟩

/-- Lifting a tuple of coordinate indices to the universe the standard cover is indexed in
preserves strict monotonicity, and `Stacks.ProjectiveCohomology.chartIndices` undoes it. -/
theorem strictMono_chartIndices {n p : ℕ} {x : Fin (p + 1) → ULift.{u} (Fin (n + 1))}
    (hx : StrictMono x) : StrictMono (chartIndices x) := fun _ _ h => hx h

/-! ### The Čech term at a tuple, as a monomial chart -/

/-- Restriction along an equality of open subsets, as an isomorphism of groups of sections. The
two inequalities the equality provides give mutually inverse restriction maps. -/
def resAddEquivOfEq {X : Type u} [TopologicalSpace X]
    (Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {W W' : Opens X} (h : W = W') :
    ToType (Q.obj (op W)) ≃+ ToType (Q.obj (op W')) where
  toFun := res Q h.ge
  invFun := res Q h.le
  left_inv s := (res_res Q h.le h.ge s).trans (res_id Q s)
  right_inv s := (res_res Q h.ge h.le s).trans (res_id Q s)
  map_add' _ _ := map_add _ _ _

/-- The degree-`p` Čech term of `𝒪(d)` at a tuple of coordinate indices: the sections of `𝒪(d)`
over the intersection of the standard charts the tuple selects. -/
abbrev twistInterSections (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {p : ℕ}
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) : Type u :=
  ToType ((abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)).obj
    (op (CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n) x)))

/-- **The Čech term at a tuple with distinct entries is the monomial chart of its set of
values.** The chart intersection is the standard open of the chart denominator, whose sections
of `𝒪(d)` are the free `R`-module on the degree-`d` Laurent monomials regular outside the set of
values of the tuple. -/
def interChartAddEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {p : ℕ}
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) (hx : Function.Injective (chartIndices x)) :
    twistInterSections R n d x ≃+ twistChart R n d (Set.range (chartIndices x)) :=
  (resAddEquivOfEq _ (inter_eq_basicOpen_chartDenom R n p x hx)).trans
    ((chartSectionsAddEquivTwistChart R n d (Finset.image (chartIndices x) Finset.univ)
        (image_univ_nonempty _)).trans
      (LinearEquiv.ofEq _ _ (congrArg (twistChart R n d)
        (coe_image_univ_eq_range (chartIndices x)))).toAddEquiv)

/-- The identification of a Čech term with a monomial chart, read in the ambient module of all
Laurent coefficient families: restrict the section to the standard open of the chart denominator
and read off its coordinates in the monomial basis. -/
theorem coe_interChartAddEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) (hx : Function.Injective (chartIndices x))
    (u : twistInterSections R n d x) :
    ((interChartAddEquiv R n d x hx u : twistChart R n d (Set.range (chartIndices x))) :
        (Fin (n + 1) → ℤ) →₀ R)
      = ((chartSectionsAddEquivTwistChart R n d (Finset.image (chartIndices x) Finset.univ)
            (image_univ_nonempty (chartIndices x))
            (res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
              (inter_eq_basicOpen_chartDenom R n p x hx).ge u) :
          twistChart R n d (↑(Finset.image (chartIndices x) Finset.univ) :
            Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R) :=
  rfl

/-- The identification of the Čech terms at a strictly increasing Čech index of the standard
cover. -/
def ordInterChartAddEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (i : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) p) :
    twistInterSections R n d i.1 ≃+ twistChart R n d (Set.range (chartIndices i.1)) :=
  interChartAddEquiv R n d i.1 (strictMono_chartIndices i.2).injective

/-- The chart intersection at a strictly increasing Čech index is the standard open of its chart
denominator. -/
private theorem ord_inter_eq_basicOpen_chartDenom (R : Type u) [CommRing R] (n : ℕ) {p : ℕ}
    (i : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) p) :
    CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
        (basicOpenXAtUniverse R n) i.1
      = ProjectiveSpectrum.basicOpen (polyGrading R n)
          (chartDenom R n (Finset.image (chartIndices i.1) Finset.univ)) :=
  inter_eq_basicOpen_chartDenom R n p i.1 (strictMono_chartIndices i.2).injective

/-- **Restriction of a section of `𝒪(d)` between two chart intersections is invisible in the
ambient module.** Through the identification of the Čech terms with the monomial charts the
restriction map of `𝒪(d)` from a chart intersection to a smaller one is the inclusion of monomial
charts, which does not move Laurent coefficient families. -/
theorem coe_ordInterChartAddEquiv_restr (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {q r : ℕ}
    (k : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) q)
    (l : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) r)
    (hkl : Finset.image (chartIndices k.1) Finset.univ
      ⊆ Finset.image (chartIndices l.1) Finset.univ)
    (h : CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
          (basicOpenXAtUniverse R n) l.1
        ≤ CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
          (basicOpenXAtUniverse R n) k.1)
    (u : twistInterSections R n d k.1) :
    ((ordInterChartAddEquiv R n d r l
          (CechCochains.restr (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
            (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) h u) :
        twistChart R n d (Set.range (chartIndices l.1))) : (Fin (n + 1) → ℤ) →₀ R)
      = ((ordInterChartAddEquiv R n d q k u :
          twistChart R n d (Set.range (chartIndices k.1))) : (Fin (n + 1) → ℤ) →₀ R) := by
  have hres :
      res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
          (ord_inter_eq_basicOpen_chartDenom R n l).ge
          (CechCochains.restr (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
            (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) h u)
        = res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
            (basicOpen_chartDenom_le R n (Finset.image (chartIndices k.1) Finset.univ)
              (Finset.image (chartIndices l.1) Finset.univ) hkl)
            (res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
              (ord_inter_eq_basicOpen_chartDenom R n k).ge u) :=
    (res_res _ _ h u).trans (res_res _ _ _ u).symm
  refine (coe_interChartAddEquiv R n d r l.1 _ _).trans ?_
  refine Eq.trans ?_ (coe_interChartAddEquiv R n d q k.1 _ u).symm
  refine Eq.trans (congrArg Subtype.val
    ((congrArg (chartSectionsAddEquivTwistChart R n d
        (Finset.image (chartIndices l.1) Finset.univ)
        (image_univ_nonempty (chartIndices l.1))) hres).trans
      (chartSectionsAddEquivTwistChart_map_homOfLE R n d
        (Finset.image (chartIndices k.1) Finset.univ)
        (Finset.image (chartIndices l.1) Finset.univ)
        (image_univ_nonempty (chartIndices k.1)) hkl _))) ?_
  exact Submodule.coe_inclusion _ _

/-! ### The ordered Čech cochains, as the monomial cochains -/

/-- A strictly increasing tuple of coordinate indices, lifted to a Čech index of the standard
cover. -/
def ordIndexUp (n p : ℕ) (i : OrdTuple n p) :
    CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) p :=
  ⟨fun j => ULift.up (i.1 j), fun _ _ h => i.2 h⟩

/-- A Čech index of the standard cover, read as a strictly increasing tuple of coordinate
indices. -/
def ordIndexDown (n p : ℕ) (i : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) p) :
    OrdTuple n p :=
  ⟨chartIndices i.1, strictMono_chartIndices i.2⟩

/-- **The degree-`p` ordered Čech cochains of `𝒪(d)` for the standard cover are the dependent
product of the monomial charts over the strictly increasing tuples `Fin (p + 1) → Fin (n + 1)`.**
Componentwise this is `Stacks.ProjectiveSpace.Cohomology.interChartAddEquiv`; the index types
differ only by the universe lift of the coordinate indices. -/
def twistOrdFamilyAddEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ) :
    CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
        (basicOpenXAtUniverse R n)
        (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p
      ≃+ ((i : OrdTuple n p) → twistChart R n d (Set.range i.1)) where
  toFun s i := ordInterChartAddEquiv R n d p (ordIndexUp n p i) (s (ordIndexUp n p i))
  invFun f i := (ordInterChartAddEquiv R n d p i).symm (f (ordIndexDown n p i))
  left_inv s := funext fun i => (ordInterChartAddEquiv R n d p i).symm_apply_apply (s i)
  right_inv f := funext fun i =>
    (ordInterChartAddEquiv R n d p (ordIndexUp n p i)).apply_symm_apply (f i)
  map_add' s t := funext fun i =>
    map_add (ordInterChartAddEquiv R n d p (ordIndexUp n p i)) (s _) (t _)

/-- **The degree-`p` ordered Čech cochains of the standard cover of `ℙⁿ_R` with coefficients in
`𝒪(d)` are the degree-`p` Čech cochains of the monomial model.** A Čech cochain goes to the
Laurent coefficient family whose value at a `(p + 1)`-element set of coordinate indices is the
component of the cochain at the increasing enumeration of that set, read in the monomial basis of
the corresponding chart. -/
def twistOrdCochainEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ) :
    CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
        (basicOpenXAtUniverse R n)
        (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p
      ≃+ laurentCechCochains R n d p :=
  (twistOrdFamilyAddEquiv R n d p).trans (ordChartEquiv R n d p).toAddEquiv.symm

/-- Reindexing the monomial cochain attached to an ordered Čech cochain returns the family of its
components. -/
theorem ordChartEquiv_twistOrdCochainEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n)
      (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p) :
    ordChartEquiv R n d p (twistOrdCochainEquiv R n d p s) = twistOrdFamilyAddEquiv R n d p s :=
  (ordChartEquiv R n d p).apply_symm_apply _

/-- **The value of the monomial cochain attached to an ordered Čech cochain.** At the set of
values of a strictly increasing tuple it is the chart identification of the component of the
cochain at that tuple. -/
theorem coe_twistOrdCochainEquiv_apply (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n)
      (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p)
    (i : OrdTuple n p) :
    ((twistOrdCochainEquiv R n d p s : laurentCechCochains R n d p) : LaurentCochain R n)
        (Finset.image i.1 Finset.univ)
      = ((ordInterChartAddEquiv R n d p (ordIndexUp n p i) (s (ordIndexUp n p i)) :
          twistChart R n d (Set.range i.1)) : (Fin (n + 1) → ℤ) →₀ R) :=
  (coe_ordChartEquiv_apply (twistOrdCochainEquiv R n d p s) i).symm.trans
    (congrArg Subtype.val
      (congrFun (ordChartEquiv_twistOrdCochainEquiv R n d p s) i))

/-! ### The differential -/

/-- Coercing a signed sum of chart elements into the ambient module of Laurent coefficient
families is the signed sum of the coercions. -/
theorem coe_sum_zsmul (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {m : ℕ}
    (S : Set (Fin (n + 1))) (c : Fin m → ℤ) (w : Fin m → twistChart R n d S) :
    ((∑ j, c j • w j : twistChart R n d S) : (Fin (n + 1) → ℤ) →₀ R)
      = ∑ j, c j • (w j : (Fin (n + 1) → ℤ) →₀ R) :=
  (map_sum (twistChart R n d S).subtype _ Finset.univ).trans
    (Finset.sum_congr rfl fun j _ => map_zsmul (twistChart R n d S).subtype (c j) (w j))

/-- **The identification of the Čech cochains with the monomial cochains carries the ordered Čech
differential to the monomial Čech differential.** With
`Stacks.ProjectiveSpace.Cohomology.twistOrdCochainEquiv` this identifies the ordered Čech complex
of the standard cover of `ℙⁿ_R` for `𝒪(d)` with the combinatorial complex of monomial charts, term
by term and map by map. -/
theorem twistOrdCochainEquiv_ordD (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n)
      (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p) :
    twistOrdCochainEquiv R n d (p + 1)
        (CechCochains.ordD (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
          (basicOpenXAtUniverse R n)
          (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p s)
      = laurentCechDiffRestrict R n d p (twistOrdCochainEquiv R n d p s) := by
  refine (ordChartEquiv R n d (p + 1)).injective
    ((ordChartEquiv_twistOrdCochainEquiv R n d (p + 1) _).trans
      (funext fun i => Subtype.ext ?_))
  have hd : CechCochains.ordD (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
        (basicOpenXAtUniverse R n)
        (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p s
        (ordIndexUp n (p + 1) i)
      = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          CechCochains.restr (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
            (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
            (CechCochains.inter_le_omit (basicOpenXAtUniverse R n)
              (ordIndexUp n (p + 1) i).1 j)
            (s (ordIndexUp n p ⟨i.1 ∘ j.succAbove,
              i.2.comp (Fin.strictMono_succAbove j)⟩)) :=
    rfl
  refine Eq.trans (congrArg Subtype.val
    ((congrArg (ordInterChartAddEquiv R n d (p + 1) (ordIndexUp n (p + 1) i)) hd).trans
      ((map_sum (ordInterChartAddEquiv R n d (p + 1) (ordIndexUp n (p + 1) i)) _
          Finset.univ).trans
        (Finset.sum_congr rfl fun j _ =>
          map_zsmul (ordInterChartAddEquiv R n d (p + 1) (ordIndexUp n (p + 1) i)) _ _)))) ?_
  refine Eq.trans (coe_sum_zsmul R n d (Set.range i.1) _ _) ?_
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_)
    (coe_ordChartEquiv_laurentCechDiffRestrict (twistOrdCochainEquiv R n d p s) i).symm
  refine congrArg (fun z : (Fin (n + 1) → ℤ) →₀ R => ((-1 : ℤ) ^ (j : ℕ)) • z) ?_
  refine Eq.trans (coe_ordInterChartAddEquiv_restr R n d
    (ordIndexUp n p ⟨i.1 ∘ j.succAbove, i.2.comp (Fin.strictMono_succAbove j)⟩)
    (ordIndexUp n (p + 1) i) (image_univ_succAbove_subset i.1 j)
    (CechCochains.inter_le_omit (basicOpenXAtUniverse R n) (ordIndexUp n (p + 1) i).1 j) _) ?_
  exact congrArg Subtype.val
    (congrFun (ordChartEquiv_twistOrdCochainEquiv R n d p s).symm
      ⟨i.1 ∘ j.succAbove, i.2.comp (Fin.strictMono_succAbove j)⟩)

end Stacks.ProjectiveSpace.Cohomology

end
