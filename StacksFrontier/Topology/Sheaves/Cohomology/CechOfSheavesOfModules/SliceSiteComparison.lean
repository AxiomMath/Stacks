module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingHomotopyEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# The Čech complex over a slice site is the explicit Čech complex of the cover

Let `X` be a topological space carrying a sheaf of rings `R`, let `V` be an open subset, let
`U : ι → Opens X` be a cover of `V` and let `I` be a sheaf of `R`-modules. There are two
Čech complexes in play.

* The **slice model** `Stacks.Cohomology.CechSheaf.cechComplex V U hU I` is
  `CategoryTheory.cechComplexFunctor` of the family `coverObject U hU` of objects of the slice
  category `Over V`, applied to the presheaf of `R(V)`-modules of sections on `Over V`. It is a
  complex of `R(V)`-modules, and it is the complex the comparison from Čech cohomology to
  derived sections is built on, hence the one [Stacks, Tag 01XD] is stated for.
* The **explicit model** `Stacks.Cech.cechComplex U ℱ` has for its degree-`p` term the group of
  families `s_{i_0 … i_p} ∈ ℱ(U_{i_0} ∩ … ∩ U_{i_p})` and the alternating sum of the face
  restrictions for its differential. All of the alternating and ordered theory — Tags 01FH,
  01FJ, 01FM — and its comparison with `CategoryTheory.cechComplexFunctor` on the site
  `Opens X` are stated for that model.

This file identifies the two, as cochain complexes of abelian groups: the comparison sends a
cochain of the slice model to the family of its components, which is a bijection in each degree
and commutes with the two differentials.

## Main definitions

* `abCechComplex`: the slice model, read as a complex of abelian groups.
* `toCochainFun` and `toCochain`: taking the family of components of a cochain of the slice
  model, as a function and as a morphism of abelian groups.
* `abCechComplexIso`: the isomorphism of cochain complexes between the slice model, read in
  abelian groups, and the explicit model.
* `abCechComplexFunctorIso`: the same, continued to `CategoryTheory.cechComplexFunctor` on the
  site `Opens X`.
* `alternatingCechInclusionToAbCechComplex`: the canonical inclusion of the alternating Čech
  complex of Tag 01FH into the slice model.
* `cechHomologyCochainIso`: the resulting identification of Čech cohomologies.

## Main results

* `toCochainFun_injective` and `toCochainFun_surjective`: a cochain of the slice model is
  exactly a family of sections over the intersections.
* `toCochainFun_md`: taking components turns the slice differential into the explicit Čech
  differential of Tag 01FJ.
* `alternatingCechInclusionToAbCechComplex_homotopyEquivalence`: Tag 01FM for the slice
  model. For a linearly ordered index type the inclusion of the alternating Čech complex into
  the slice model is a homotopy equivalence, so an alternating or ordered Čech computation
  computes the cohomology of the slice model.
* `alternatingCechHomologyIso`: the cohomology of the alternating Čech complex is the abelian
  group underlying the module-valued Čech cohomology of the slice model.
* `isZero_cechComplex_homology_iff`: the module-valued Čech cohomology of the slice model
  vanishes exactly when the explicit Čech cohomology does.

## Implementation notes

Everything is read off the element-level description of the slice model already available in
`StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing`:
`mcomp` takes components, `mmk` builds a cochain from prescribed components, `mcech_ext` says a
cochain is determined by its components and `mcomp_md` computes the differential
componentwise. The only arithmetic added here is one restriction along
`Stacks.Cech.cechComplexInter_eq`, the identification of the categorical product of the selected
opens with their infimum: the slice model is indexed by the former and the explicit model by the
latter. `res_ge_res_le` and `res_le_res_ge` absorb that restriction, which is why no `eqToHom`
appears.

The comparison is stated in abelian groups rather than in `R(V)`-modules because the explicit
model is a complex of abelian groups: its degree-`p` term is a plain product of groups of
sections, carrying no `R(V)`-action. Nothing is lost for the cohomology, since
`forget₂ (ModuleCat R(V)) AddCommGrpCat` preserves homology: `homologyForgetIso` identifies the
homology of `abCechComplex` with the abelian group underlying the homology of the slice model,
and `isZero_cechComplex_homology_iff` transports vanishing in both directions.

The index type is taken in the universe of the module values. The explicit cochain group is a
product over the tuples of indices, so it lives in the maximum of the two universes, and the
degree-`p` terms of the two models can only be compared when that maximum is the universe of
the module values — the same constraint `Stacks.Cech.cechComplexObjIso` carries.

Two elaboration hazards. `CechCochains.Cochain` is a `def`, so `rw` cannot see through an
application of a cochain to a tuple; the file therefore carries
`attribute [local implicit_reducible]` on both `CechCochains.Cochain` and `cechComplex`. And
`cechComplex` takes a `UnivLE` instance argument: when its explicit arguments are postponed,
instance search for `UnivLE.{?u, ?v}` assigns the module universe to be `0`, after which the
complex has the wrong type and the error names an unrelated metavariable. Applying the
universes explicitly, as in `cechComplex.{uX, uR, uM, uM}`, is the cure.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res res_id res_res res_zero res_sum res_zsmul)

universe uX uR uM

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize
attribute [local implicit_reducible] CechCochains.Cochain
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.cechComplex

namespace Stacks.Cohomology.CechSheaf

noncomputable section

variable {Y : Type uX} [TopologicalSpace Y]

/-- Restricting a section along an equality of opens and back changes nothing. -/
theorem res_ge_res_le (Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{uM}) {W W' : Opens Y} (h : W = W')
    (s : ToType (Q.obj (op W'))) : res Q h.ge (res Q h.le s) = s :=
  (res_res Q h.ge h.le s).trans (res_id _ _)

/-- Restricting a section along an equality of opens and back changes nothing. -/
theorem res_le_res_ge (Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{uM}) {W W' : Opens Y} (h : W = W')
    (s : ToType (Q.obj (op W))) : res Q h.le (res Q h.ge s) = s :=
  (res_res Q h.le h.ge s).trans (res_id _ _)

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uM}
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R)

/-! ### The slice model, read in abelian groups -/

/-- The module-valued Čech complex of the cover, read as a complex of abelian groups. -/
abbrev abCechComplex : CochainComplex AddCommGrpCat.{uM} ℕ :=
  ((forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (cechComplex.{uX, uR, uM, uM} V U hU I)

/-- Taking components of a cochain of the module-valued Čech complex is additive. -/
theorem mcomp_add {n : ℕ}
    (s t : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 1) → ι) :
    mcomp V U hU I (s + t) x = mcomp V U hU I s x + mcomp V U hU I t x :=
  (congrArg (res (abSections I) (inter_coverObject_left V U hU x).ge)
      (map_add (ConcreteCategory.hom
        (π (coverObject U hU) (sectionsPresheaf V I) n x)) s t)).trans
    (map_add _ _ _)

/-! ### Taking components -/

/-- The family of components of a cochain of the module-valued Čech complex, read as a Čech
cochain of the explicit model of Tag 01FJ: the component at a tuple is a section of `I` over
the intersection of the members of the cover selected by that tuple. -/
def toCochainFun {n : ℕ}
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n)) :
    CechCochains.Cochain (X := TopCat.of X) U (abSections I) n :=
  fun x => res (abSections I) (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x).ge
    (mcomp V U hU I s x)

/-- The value of `toCochainFun` at a tuple is the component of the cochain there. -/
theorem toCochainFun_apply {n : ℕ}
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 1) → ι) :
    toCochainFun V U hU I s x =
      res (abSections I) (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x).ge
        (mcomp V U hU I s x) :=
  rfl

/-- **A cochain of the slice model is determined by its components.** -/
theorem toCochainFun_injective {n : ℕ} :
    Function.Injective (toCochainFun V U hU I (n := n)) := by
  intro s t h
  refine mcech_ext V U hU I s t fun x => ?_
  have h2 := congrArg
    (res (abSections I) (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x).le)
    (congrFun h x)
  rwa [toCochainFun_apply, toCochainFun_apply,
    res_le_res_ge (abSections I) (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x),
    res_le_res_ge (abSections I) (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x)] at h2

/-- **Every family of sections over the intersections is the family of components of a cochain
of the slice model.** -/
theorem toCochainFun_surjective {n : ℕ} :
    Function.Surjective (toCochainFun V U hU I (n := n)) := fun f =>
  ⟨mmk V U hU I fun x =>
      res (abSections I) (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x).le (f x),
    funext fun x =>
      (congrArg (res (abSections I) (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x).ge)
          (mcomp_mmk V U hU I _ x)).trans
        (res_ge_res_le (abSections I)
          (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x) (f x))⟩

/-- **Taking components, degreewise.** The morphism of abelian groups sending a cochain of the
slice model to the family of its components over the intersections. -/
def toCochain (n : ℕ) :
    (abCechComplex V U hU I).X n ⟶
      AddCommGrpCat.of (CechCochains.Cochain (X := TopCat.of X) U (abSections I) n) :=
  AddCommGrpCat.ofHom
    { toFun := toCochainFun V U hU I
      map_zero' := funext fun x =>
        (congrArg (res (abSections I) _) (mcomp_zero V U hU I x)).trans (res_zero _ _)
      map_add' := fun s t => funext fun x =>
        (congrArg (res (abSections I) _) (mcomp_add V U hU I s t x)).trans (map_add _ _ _) }

/-- The underlying function of `toCochain` is `toCochainFun`. -/
theorem toCochain_apply (n : ℕ)
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n)) :
    ConcreteCategory.hom (toCochain V U hU I n) s = toCochainFun V U hU I s :=
  rfl

/-- Taking components is an isomorphism in every degree. -/
instance isIso_toCochain (n : ℕ) : IsIso (toCochain V U hU I n) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨toCochainFun_injective V U hU I, toCochainFun_surjective V U hU I⟩

/-! ### The two differentials -/

/-- **Taking components turns the slice differential into the explicit Čech differential.**
Both are the alternating sum, over the omitted index, of the restrictions of the components. -/
theorem toCochainFun_md {n : ℕ}
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (y : Fin (n + 2) → ι) :
    toCochainFun V U hU I (md V U hU I s) y =
      CechCochains.cechD (X := TopCat.of X) U (abSections I) n (toCochainFun V U hU I s) y := by
  have hR : CechCochains.cechD (X := TopCat.of X) U (abSections I) n (toCochainFun V U hU I s) y =
      ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
        res (abSections I) (CechCochains.inter_le_omit (X := TopCat.of X) U y a)
          (toCochainFun V U hU I s (y ∘ a.succAbove)) := rfl
  rw [hR, toCochainFun_apply,
    show mcomp V U hU I (md V U hU I s) y = _ from mcomp_md V U hU I s y, res_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [res_zsmul, res_res, toCochainFun_apply, res_res]

/-- **Taking components is a morphism of complexes.** -/
theorem toCochain_comm (n : ℕ) :
    toCochain V U hU I n ≫
        AddCommGrpCat.ofHom (CechCochains.cechD (X := TopCat.of X) U (abSections I) n) =
      (abCechComplex V U hU I).d n (n + 1) ≫ toCochain V U hU I (n + 1) :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun s => funext fun y =>
    (toCochainFun_md V U hU I s y).symm

/-! ### The bridge -/

/-- **The slice model is the explicit Čech complex.** The module-valued Čech complex of the
cover, read as a complex of abelian groups, is isomorphic as a cochain complex to the explicit
Čech complex of Tag 01FJ; in each degree the isomorphism takes a cochain to the family of its
components over the intersections. -/
def abCechComplexIso :
    abCechComplex V U hU I ≅ Stacks.Cech.cechComplex (X := TopCat.of X) U (abSections I) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => asIso (toCochain V U hU I n))
    fun n m hnm => by
      obtain rfl : n + 1 = m := hnm
      rw [Stacks.Cech.cechComplex_d]
      exact toCochain_comm V U hU I n

/-- In each degree the bridge is `toCochain`. -/
@[simp]
theorem abCechComplexIso_hom_f (n : ℕ) :
    (abCechComplexIso V U hU I).hom.f n = toCochain V U hU I n :=
  rfl

/-- **The slice model is Mathlib's Čech complex on the site `Opens X`.** -/
def abCechComplexFunctorIso :
    abCechComplex V U hU I ≅
      (CategoryTheory.cechComplexFunctor U).obj (abSections I) :=
  abCechComplexIso V U hU I ≪≫
    Stacks.Cech.cechComplexIso (X := TopCat.of X) U (abSections I)

/-- **Tag 01FH for the slice model.** The canonical inclusion of the alternating Čech complex
into the module-valued Čech complex of the cover, read in abelian groups. -/
def alternatingCechInclusionToAbCechComplex :
    Stacks.Cech.alternatingCechComplex (X := TopCat.of X) U (abSections I) ⟶
      abCechComplex V U hU I :=
  Stacks.Cech.alternatingCechInclusion (X := TopCat.of X) U (abSections I) ≫
    (abCechComplexIso V U hU I).inv

/-- **Tag 01FM for the slice model.** For a linearly ordered index type the inclusion of the
alternating Čech complex into the module-valued Čech complex of the cover is a homotopy
equivalence; so an alternating — equivalently, by Tag 01FJ, an ordered — Čech computation
computes the cohomology of the slice model. -/
theorem alternatingCechInclusionToAbCechComplex_homotopyEquivalence [LinearOrder ι] :
    (HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.up ℕ))
      (alternatingCechInclusionToAbCechComplex V U hU I) := by
  obtain ⟨e, he⟩ := Stacks.Cech.alternatingCechInclusion_homotopyEquivalence (X := TopCat.of X) U
    (abSections I)
  refine ⟨e.trans (HomotopyEquiv.ofIso (abCechComplexIso V U hU I).symm), ?_⟩
  rw [HomotopyEquiv.trans_hom, he]
  rfl

/-! ### Čech cohomology -/

/-- The Čech cohomology of the slice model, read in abelian groups, is the Čech cohomology of
the explicit model, in every degree. -/
def abCechHomologyIso (p : ℕ) :
    (abCechComplex V U hU I).homology p ≅
      (Stacks.Cech.cechComplex (X := TopCat.of X) U (abSections I)).homology p :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{uM} (ComplexShape.up ℕ) p).mapIso
    (abCechComplexIso V U hU I)

/-- Forgetting the module structure commutes with taking the cohomology of the slice model. -/
def homologyForgetIso (p : ℕ) :
    (abCechComplex V U hU I).homology p ≅
      (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).obj
        ((cechComplex V U hU I).homology p) :=
  ShortComplex.mapHomologyIso ((cechComplex V U hU I).sc p)
    (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM})

/-- **The Čech cohomology of the two models agrees.** The abelian group underlying the
module-valued Čech cohomology of the cover is the Čech cohomology of the explicit model. -/
def cechHomologyCochainIso (p : ℕ) :
    (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).obj
        ((cechComplex V U hU I).homology p) ≅
      (Stacks.Cech.cechComplex (X := TopCat.of X) U (abSections I)).homology p :=
  (homologyForgetIso V U hU I p).symm ≪≫ abCechHomologyIso V U hU I p

/-- The alternating inclusion into the slice model induces an isomorphism on cohomology. -/
instance isIso_homologyMap_alternatingCechInclusionToAbCechComplex [LinearOrder ι] (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (alternatingCechInclusionToAbCechComplex V U hU I) p) := by
  obtain ⟨e, he⟩ := alternatingCechInclusionToAbCechComplex_homotopyEquivalence V U hU I
  rw [← he]
  exact (e.toHomologyIso p).isIso_hom

/-- **The alternating Čech complex computes the module-valued Čech cohomology of the cover.**
For a linearly ordered index type the cohomology of the alternating Čech complex of Tag 01FH is
the abelian group underlying the module-valued Čech cohomology of the slice model, in every
degree. This is what lets an alternating -- equivalently, by Tag 01FJ, an ordered -- Čech
computation be fed into the comparison of [Stacks, Tag 01XD]. -/
def alternatingCechHomologyIso [LinearOrder ι] (p : ℕ) :
    (Stacks.Cech.alternatingCechComplex (X := TopCat.of X) U (abSections I)).homology p ≅
      (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).obj
        ((cechComplex V U hU I).homology p) :=
  asIso (HomologicalComplex.homologyMap
      (alternatingCechInclusionToAbCechComplex V U hU I) p) ≪≫
    homologyForgetIso V U hU I p

/-- **The two Čech cohomologies vanish together.** -/
theorem isZero_cechComplex_homology_iff (p : ℕ) :
    IsZero ((cechComplex V U hU I).homology p) ↔
      IsZero ((Stacks.Cech.cechComplex (X := TopCat.of X) U (abSections I)).homology p) :=
  ⟨fun h => (Functor.map_isZero _ h).of_iso (cechHomologyCochainIso V U hU I p).symm,
    fun h => ModuleCat.isZero_iff_subsingleton.mpr
      (AddCommGrpCat.subsingleton_of_isZero (h.of_iso (cechHomologyCochainIso V U hU I p)))⟩

end

end Stacks.Cohomology.CechSheaf

end
