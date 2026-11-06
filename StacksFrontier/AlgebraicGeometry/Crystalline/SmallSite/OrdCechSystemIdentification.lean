module

public import StacksFrontier.Algebra.Category.Grp.Products
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechCoverComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OrdCechRestrictCover
public import StacksFrontier.CategoryTheory.Limits.ConstantTowerSections

/-!
# The two Čech complexes of [Stacks, Tag 07MN] are the same complex

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OrdCechRestrictCover.lean` instantiates the
lifted alternating Čech theory at a restriction cover of an object of `Cris(X/S)` and proves that
the resulting *ordered* Čech complex `restrictCechComplexOrd` computes the Čech cohomology of that
covering family.  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechCoverComplex.lean`
writes down the double complex of [Stacks, Tag 07MN], whose bottom row is the alternating Čech
module `ordCechModule` of the modules `M_{λ_0 … λ_n} = lim_e Γ(T(α)_e, F)` of a carried Čech
system.  **Those were two unrelated objects**, and that is what kept the instantiation from
reaching the remark: the first is built from the sections of `F` over the restrictions themselves,
the second from limits over the level filtration of a Čech system.

This file identifies them.  The identification is not a hypothesis: the Čech system whose towers
are the restrictions is *constructed* here, `restrictCechSystem`, and for it the two complexes are
isomorphic with nothing assumed.

## Main definitions and results

* `restrictCechSystem` — **the Čech system of a restriction cover**: the tower attached to a tuple
  `α` of indices is constant at the restriction of `A` to the intersection of the corresponding
  opens, and the transition morphisms are the restrictions along the inclusions of the
  intersections.  This is the first
  `Crystalline.GlobalCrystallineSituation.SmallSite.CechSystem` constructed anywhere; the one
  [Stacks, Tag 07MM] forms, out of divided power envelopes, remains carried data.
* `restrictTupleSectionsIso` — **its module `M_α` is the group of sections of `F` over the
  restriction**: the limit over the level filtration collapses because the filtration is constant
  (`CategoryTheory.Limits.constLimitIso`), and `restrictTupleSectionsIso_restriction` says the
  collapse carries the restriction maps `M_{α ∘ φ} ⟶ M_α` of the system to the restriction maps of
  `F`.
* `ordCechπ`, `ordCechLift` and `ordCechModule_hom_ext` — the product description of
  `ordCechModule`, named so that compositions with it are stated at `ordCechModule` itself.
* `ordCechDiff` — **the alternating Čech differential of the modules `M_β` of a Čech system**, the
  differential the double complex of [Stacks, Tag 07MN] is required to have in the Čech direction;
  `cechDifferential_zero_eq_restriction` and `ordCechDiff_eq_cechDifferential` — that it *is* that
  differential, read on the bottom row through the `m = 0` identification `ordCechTermZeroIso`.
* `ordDeRhamSystemSingle` and `isZero_ordDeRhamSystemSingle_complex_X` — **an
  `...SmallSite.OrdDeRhamSystem` over an arbitrary Čech system**, the degenerate one whose local
  complexes sit in degree zero.  That structure had no term anywhere, so the predicates built on
  it were not known to be about anything, and the hypothesis `hlen` of
  `...SmallSite.isZero_cohomologyFunctor_of_computesOrdCechCohomology` had no producer.  These are
  not the remark's de Rham complexes; see "What this does not do".
* `restrictOrdCechModuleIso` — **degreewise: the ordered Čech cochain group of a restriction cover
  is the alternating Čech module of the Čech system of that cover**, and
  `cechDiffOrd_comp_restrictOrdCechModuleIso` — the identification commutes with the two
  differentials.
* `restrictOrdCechSystemComplex` and `restrictOrdCechComplexIso` — **the bottom row of the double
  complex of [Stacks, Tag 07MN] for a restriction cover, as a complex, and its isomorphism with
  `restrictCechComplexOrd`.**  The identity `d ∘ d = 0` for the bottom row is obtained from that
  isomorphism rather than recomputed.
* `restrictOrdCechSystemHomologyIso` and `restrictOrdCechSystemCohomologyIso` — **the bottom row of
  the double complex of [Stacks, Tag 07MN] for a restriction cover computes the Čech cohomology of
  that covering family, in every degree.**

## What this does not do

**[Stacks, Tag 07MN] is not proved and no tag attribute is placed.**  What the remark asserts is
that the *total* complex of its double complex computes `RΓ(Cris(X/S), F)`; what is proved here is
that the bottom row of that double complex is the ordered Čech complex of the covering, whose
cohomology is the Čech cohomology of the covering family.  Three things stand between the two:

* passing from Čech cohomology of a covering family to the cohomology of the covered object is
  [Stacks, Tag 03F7], and `Cris(X/S)` has no terminal object while the `RΓ(Cris(X/S), -)` of the
  remark is the global `...SmallSite.cohomologyFunctor`.  [Stacks, Tag 03F7] is applied to the
  restriction covers in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OrdCechCoveredObject.lean`, where
  `...SmallSite.restrictOrdCechOverCohomologyIso` lands the ordered Čech complex of such a cover
  on `H^j(Cris(X/S)/A, F)`; two things keep that from composing with the isomorphisms below.
  The covered object is still an object and not the site: the remaining step is isolated there
  into `hΓ : globalSections S ≅ sectionsFunctorOver S A` and discharged only at a terminal
  object.  And the index universes differ: `CechSystem` fixes `Λ` in `Type u`, whereas the
  covering families of `Cris(X/S)` — hence the statements of that file — are indexed by
  `Type (u + 1)`, so composing across the ULift asks for a reindexing isomorphism of ordered
  Čech complexes that the library does not have;
* the remark's de Rham direction: the local completed de Rham complexes `M_β ⊗̂_{D_β} Ω^*_{D_β}`
  are still carried as an `...SmallSite.OrdDeRhamSystem`.  `ordDeRhamSystemSingle` constructs one,
  but the degenerate one, concentrated in degree zero; the remark's own complexes have the
  connection of [Stacks, Tag 07JH] as differential and are not built anywhere in this library
  (item 4 of the "What is and is not proved" section of `CechCoverComplex.lean`);
* the remark's other inputs [Stacks, Tag 07JH] and [Stacks, Tag 07LG], which are proved elsewhere
  (`...SmallSite.crystalPairFunctor_isEquivalence`,
  `...SmallSite.crystalPairDeRhamComplex_computesCohomology`) and not used here.  The vanishing
  clause of [Stacks, Tag 07LM] is `...SmallSite.vanishing07LM` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Vanishing07LMProof.lean`, proved for every
  sheaf of `𝒪_{X/S}`-modules satisfying conditions (1) and (2) of [Stacks, Tag 07JN].  What the
  remark takes from the tag, the agreement of `RΓ` of `F` and of `F ⊗ Ω^*_{X/S}`, is
  `...SmallSite.stacks07LM` of `SmallSite/Proposition07LM.lean`, for every crystal in
  quasi-coherent modules; it is not connected to the Čech system of this file.

The Čech system constructed here is also *not* the one [Stacks, Tag 07MM] forms: its towers are
constant, whereas the remark's are the truncations `Spec(D_α/p^e D_α)` of a `p`-adically completed
divided power envelope, for which the limit over `e` is a genuine completion.  What the
construction shows is that the shape of the bottom row of the remark's double complex is the shape
of the ordered Čech complex of the covering, with nothing assumed; it does not produce the
remark's own system, for which see items 1--3 of the "What is and is not proved" section of
`CechCoverComplex.lean`.

## References

* [Stacks Project, Tag 01FK](https://stacks.math.columbia.edu/tag/01FK)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 07MM](https://stacks.math.columbia.edu/tag/07MM)
* [Stacks Project, Tag 07MN](https://stacks.math.columbia.edu/tag/07MN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.CategoryTheory.CechComplex

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open _root_.Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}} {Λ : Type u}

/-! ### The Čech system of a restriction cover -/

/-- **The Čech system of a restriction cover of an object of `Cris(X/S)`.**  The tower attached to
a tuple `α = (λ_0, …, λ_n)` of indices is *constant* at the restriction of `A` to the intersection
`V_{λ_0} ∩ ⋯ ∩ V_{λ_n}` of the corresponding opens of the ambient scheme, and the transition
morphism along a simplex map is the restriction along the inclusion of intersections.

Both functor laws come from the corresponding laws for the reindexing morphisms of the
intersections, `...CechComplex.interMap_id` and `...CechComplex.interMap_comp`.

This is a `Crystalline.GlobalCrystallineSituation.SmallSite.CechSystem` that is *constructed*, as
against the one [Stacks, Tag 07MM] forms out of divided power envelopes, which stays carried
data.  Its towers being constant, its modules `M_α` are plain groups of sections and not
completions; see the module documentation. -/
def restrictCechSystem (A : CrystallineThickening S)
    (V : Λ → A.obj.thickening.target.scheme.Opens) : CechSystem S Λ where
  obj n α := (Functor.const ℕ).obj ((restrictOpenFunctor A).obj (inter V α))
  map φ α := (Functor.const ℕ).map
    ((restrictOpenFunctor A).map (interMap V α fun j => φ.toOrderHom j))
  map_id n α :=
    (congrArg (fun g => (Functor.const ℕ).map ((restrictOpenFunctor A).map g))
        (interMap_id V α)).trans
      (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
  map_comp ψ φ α :=
    (congrArg (fun g => (Functor.const ℕ).map ((restrictOpenFunctor A).map g))
        (interMap_comp V α (fun j => (SimplexCategory.Hom.toOrderHom φ) j)
          fun j => (SimplexCategory.Hom.toOrderHom ψ) j)).trans
      (by rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; rfl)

/-- The tower of `restrictCechSystem A V` at a tuple `α` is constant at the restriction of `A` to
the intersection `inter V α`. -/
@[simp]
theorem restrictCechSystem_obj (A : CrystallineThickening S)
    (V : Λ → A.obj.thickening.target.scheme.Opens) (n : SimplexCategory)
    (α : Fin (n.len + 1) → Λ) :
    (restrictCechSystem A V).obj n α =
      (Functor.const ℕ).obj ((restrictOpenFunctor A).obj (inter V α)) :=
  rfl

/-! ### The modules of the system are plain groups of sections -/

section Sections

variable (A : CrystallineThickening S) (V : Λ → A.obj.thickening.target.scheme.Opens)
  (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- **The module `M_α` of the Čech system of a restriction cover is the group of sections of `F`
over the restriction of `A` to the intersection of the tuple.**  The limit over the level
filtration that defines `...SmallSite.CechSystem.tupleSections` collapses, the filtration being
constant. -/
def restrictTupleSectionsIso {n : SimplexCategory} (α : Fin (n.len + 1) → Λ) :
    (restrictCechSystem A V).tupleSections F α ≅
      F.obj (op ((restrictOpenFunctor A).obj (inter V α))) :=
  constLimitIso _ F

/-- **The identification of the modules carries the restriction maps `M_{α ∘ φ} ⟶ M_α` of the Čech
system to the restriction maps of `F` along the inclusions of the Čech intersections.**  This is
what makes `restrictTupleSectionsIso` an identification of the whole system of modules and not
only of the individual groups. -/
theorem restrictTupleSectionsIso_restriction {m n : SimplexCategory} (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) :
    (restrictCechSystem A V).restriction F φ α ≫ (restrictTupleSectionsIso A V F α).hom =
      (restrictTupleSectionsIso A V F (fun j => α (φ.toOrderHom j))).hom ≫
        F.map ((restrictOpenFunctor A).map (interMap V α fun j => φ.toOrderHom j)).op :=
  constLimitIso_naturality F _

/-- `restrictTupleSectionsIso_restriction` with both isomorphisms inverted, which is the form the
comparison of the Čech differentials uses. -/
theorem restrictTupleSectionsIso_inv_comp_restriction {m n : SimplexCategory} (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) :
    (restrictTupleSectionsIso A V F (fun j => α (φ.toOrderHom j))).inv ≫
        (restrictCechSystem A V).restriction F φ α =
      F.map ((restrictOpenFunctor A).map (interMap V α fun j => φ.toOrderHom j)).op ≫
        (restrictTupleSectionsIso A V F α).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact restrictTupleSectionsIso_restriction A V F φ α

end Sections

/-! ### The Čech differential of the modules of a Čech system -/

section Diff

variable [LinearOrder Λ] (T : CechSystem S Λ)
  (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The projection of the alternating Čech module `⨁_{λ_0 < ⋯ < λ_n} M_{λ_0 … λ_n}` onto the
factor at a strictly increasing tuple. -/
def ordCechπ (n : ℕ) (β : OrdCechTuple Λ n) :
    ordCechModule T F n ⟶ T.tupleSections F β.1 :=
  Pi.π _ β

/-- The map into the alternating Čech module determined by a family of maps into the modules
`M_β`. -/
def ordCechLift {Z : AddCommGrpCat.{u + 1}} {n : ℕ}
    (f : ∀ β : OrdCechTuple Λ n, Z ⟶ T.tupleSections F β.1) : Z ⟶ ordCechModule T F n :=
  Pi.lift f

/-- The map `ordCechLift T F f` followed by the projection at `β` is `f β`. -/
@[reassoc (attr := simp)]
theorem ordCechLift_comp_ordCechπ {Z : AddCommGrpCat.{u + 1}} {n : ℕ}
    (f : ∀ β : OrdCechTuple Λ n, Z ⟶ T.tupleSections F β.1) (β : OrdCechTuple Λ n) :
    ordCechLift T F f ≫ ordCechπ T F n β = f β :=
  Pi.lift_comp_π f β

/-- Two maps into the alternating Čech module agree as soon as they agree after composing with
every projection. -/
theorem ordCechModule_hom_ext {Z : AddCommGrpCat.{u + 1}} {n : ℕ}
    {f g : Z ⟶ ordCechModule T F n}
    (h : ∀ β : OrdCechTuple Λ n, f ≫ ordCechπ T F n β = g ≫ ordCechπ T F n β) : f = g :=
  Pi.hom_ext _ _ h

/-- **The restriction map `M_{β ∘ δ_i} ⟶ M_β`** of a Čech system along omitting the `i`-th index
of a strictly increasing tuple, with its source spelled by
`...SmallSite.OrdCechTuple.omit`. -/
def ordCechRestriction (n : ℕ) (β : OrdCechTuple Λ (n + 1)) (i : Fin (n + 2)) :
    T.tupleSections F (β.omit i).1 ⟶ T.tupleSections F β.1 :=
  T.restriction F (SimplexCategory.δ i) β.1

/-- **The alternating Čech differential of the modules `M_{λ_0 … λ_n}` of a Čech system**, the
usual alternating sum `∑_i (-1)^i` of the restriction maps along the inclusions obtained by
omitting one index of a strictly increasing tuple.

This is the first differential of the double complex of [Stacks, Tag 07MN], read on its bottom
row: that is `ordCechDiff_eq_cechDifferential`.  No identity `d ∘ d = 0` is asserted here, and
none is needed to name the differential; for a restriction cover it is
`restrictOrdCechSystemComplex`, where it is obtained from the identification with the ordered Čech
complex of the cover. -/
def ordCechDiff (n : ℕ) : ordCechModule T F n ⟶ ordCechModule T F (n + 1) :=
  ordCechLift T F fun β : OrdCechTuple Λ (n + 1) =>
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      (ordCechπ T F n (β.omit i) ≫ ordCechRestriction T F n β i)

/-- The component of `ordCechDiff T F n` at a strictly increasing tuple `β` is the alternating sum
over `i` of the projection at `β.omit i` followed by the restriction map along omitting `i`. -/
@[reassoc (attr := simp)]
theorem ordCechDiff_comp_ordCechπ (n : ℕ) (β : OrdCechTuple Λ (n + 1)) :
    ordCechDiff T F n ≫ ordCechπ T F (n + 1) β =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (ordCechπ T F n (β.omit i) ≫ ordCechRestriction T F n β i) :=
  ordCechLift_comp_ordCechπ T F _ β

/-- Precomposing `ordCechDiff_comp_ordCechπ` with any map `g` into the alternating Čech module. -/
private theorem comp_ordCechDiff_comp_ordCechπ {Z : AddCommGrpCat.{u + 1}} {n : ℕ}
    (g : Z ⟶ ordCechModule T F n) (β : OrdCechTuple Λ (n + 1)) :
    g ≫ ordCechDiff T F n ≫ ordCechπ T F (n + 1) β =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (g ≫ ordCechπ T F n (β.omit i) ≫ ordCechRestriction T F n β i) := by
  simp [Preadditive.comp_sum]

/-! ### The de Rham system of a Čech system is inhabited -/

/-- **The degenerate de Rham system of a Čech system**: every local complex is concentrated in
degree zero, at the module `M_β` itself, and the face maps are the restriction maps of the system.

This is *not* the de Rham system of [Stacks, Tag 07MN], whose local complexes are the `p`-adically
completed de Rham complexes `M_β ⊗̂_{D_β} Ω^*_{D_β}` of a crystal with its connection; those are
not constructed anywhere in this library, for the reasons in item 4 of the "What is and is not
proved" section of `CechCoverComplex.lean`.  What it does show is that
`...SmallSite.OrdDeRhamSystem` is inhabited over *every* Čech system — it had no term anywhere —
so that the structures built on it are not vacuous, and that the hypothesis `hlen` of
`...SmallSite.isZero_cohomologyFunctor_of_computesOrdCechCohomology` has a producer, at `e = 0`:
`isZero_ordDeRhamSystemSingle_complex_X`. -/
def ordDeRhamSystemSingle : OrdDeRhamSystem T F where
  complex n β :=
    (HomologicalComplex.single AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) 0).obj
      (T.tupleSections F β.1)
  zeroIso n β := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _
  face n β i :=
    (HomologicalComplex.single AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) 0).map
      (ordCechRestriction T F n β i)
  face_zero n β i := by
    rw [HomologicalComplex.single_map_f_self]
    rfl

/-- **The local complexes of the degenerate de Rham system vanish in every positive degree.**
This is the hypothesis `hlen` of
`...SmallSite.isZero_cohomologyFunctor_of_computesOrdCechCohomology` read at `e = 0`. -/
theorem isZero_ordDeRhamSystemSingle_complex_X (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ)
    (hm : 0 < m) : IsZero (((ordDeRhamSystemSingle T F).complex n β).X m) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (T.tupleSections F β.1) m
    (by omega)

/-- The projection of the term `M^{n, m}` of the double complex of [Stacks, Tag 07MN] onto the
factor at a strictly increasing tuple. -/
def ordCechTermπ (K : OrdDeRhamSystem T F) (n m : ℕ) (β : OrdCechTuple Λ n) :
    ordCechTerm K n m ⟶ (K.complex n β).X m :=
  Pi.π _ β

/-- The Čech differential the structure `...SmallSite.OrdCechTotalComparison` prescribes, with its
projections named by `ordCechTermπ`. -/
theorem cechDifferential' [Finite Λ] {K : OrdDeRhamSystem T F}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (C : OrdCechTotalComparison K G)
    (n m : ℕ) (β : OrdCechTuple Λ (n + 1)) :
    (C.double.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f (m : ℤ) ≫ (C.termIso (n + 1) m).hom ≫
        ordCechTermπ T F K (n + 1) m β =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((C.termIso n m).hom ≫ ordCechTermπ T F K n m (β.omit i) ≫ (K.face n β i).f m) :=
  C.cechDifferential n m β

/-- The `m = 0` identification of [Stacks, Tag 07MN] is componentwise the degree-zero
identification of the local de Rham complexes with the modules `M_β`. -/
@[reassoc]
theorem ordCechTermZeroIso_hom_comp_ordCechπ (K : OrdDeRhamSystem T F) (n : ℕ)
    (β : OrdCechTuple Λ n) :
    (ordCechTermZeroIso K n).hom ≫ ordCechπ T F n β =
      ordCechTermπ T F K n 0 β ≫ (K.zeroIso n β).hom :=
  Pi.mapIso_hom_π _ β

/-- `...SmallSite.OrdDeRhamSystem.face_zero` with the restriction map named by
`ordCechRestriction`. -/
theorem face_zero' (K : OrdDeRhamSystem T F) (n : ℕ) (β : OrdCechTuple Λ (n + 1))
    (i : Fin (n + 2)) :
    (K.face n β i).f 0 ≫ (K.zeroIso (n + 1) β).hom =
      (K.zeroIso n (β.omit i)).hom ≫ ordCechRestriction T F n β i :=
  K.face_zero n β i

/-- **The first differential of the double complex of [Stacks, Tag 07MN] is, componentwise on the
bottom row, the alternating sum of the restriction maps `M_{β ∘ δ_i} ⟶ M_β` of the Čech
system.**  This is the structure's own Čech differential at de Rham degree zero, with the
degree-zero identification `...SmallSite.OrdDeRhamSystem.zeroIso` substituted on both sides. -/
theorem cechDifferential_zero_eq_restriction [Finite Λ] {K : OrdDeRhamSystem T F}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (C : OrdCechTotalComparison K G)
    (n : ℕ) (β : OrdCechTuple Λ (n + 1)) :
    (C.double.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f ((0 : ℕ) : ℤ) ≫ (C.termIso (n + 1) 0).hom ≫
        ordCechTermπ T F K (n + 1) 0 β ≫ (K.zeroIso (n + 1) β).hom =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((C.termIso n 0).hom ≫ ordCechTermπ T F K n 0 (β.omit i) ≫
          (K.zeroIso n (β.omit i)).hom ≫ ordCechRestriction T F n β i) := by
  rw [reassoc_of% (cechDifferential' T F C n 0 β), Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp, Category.assoc, Category.assoc, face_zero' T F K n β i]

/-- **The bottom row of the double complex of [Stacks, Tag 07MN] carries the alternating Čech
differential of the modules `M_β` of [Stacks, Tag 07MM].**  The `m = 0` row of the double complex
is the alternating Čech module by `ordCechTermZeroIso`, and under that identification the
differential the structure `...SmallSite.OrdCechTotalComparison` prescribes in the Čech direction
is `ordCechDiff`.

Together with `restrictOrdCechComplexIso` this is the identification the module documentation is
about: the bottom row of the remark's double complex, for a restriction cover, is the ordered Čech
complex of that cover. -/
theorem ordCechDiff_eq_cechDifferential [Finite Λ] {K : OrdDeRhamSystem T F}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (C : OrdCechTotalComparison K G)
    (n : ℕ) :
    (C.double.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).f ((0 : ℕ) : ℤ) ≫ (C.termIso (n + 1) 0).hom ≫
        (ordCechTermZeroIso K (n + 1)).hom =
      (C.termIso n 0).hom ≫ (ordCechTermZeroIso K n).hom ≫ ordCechDiff T F n := by
  refine ordCechModule_hom_ext T F fun β => ?_
  have := comp_ordCechDiff_comp_ordCechπ T F
    ((C.termIso n 0).hom ≫ (ordCechTermZeroIso K n).hom) β
  rw [Category.assoc, Category.assoc, ordCechTermZeroIso_hom_comp_ordCechπ,
    cechDifferential_zero_eq_restriction T F C n β]
  simp only [Category.assoc] at this ⊢
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ordCechTermZeroIso_hom_comp_ordCechπ_assoc]

end Diff

/-! ### The two complexes -/

section Identification

variable [LinearOrder Λ] (A : CrystallineThickening S)
  (V : Λ → A.obj.thickening.target.scheme.Opens)
  (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

omit [LinearOrder Λ] in
/-- `restrictTupleSectionsIso_inv_comp_restriction` at a face of a strictly increasing tuple,
which is the shape the Čech differential presents it in. -/
theorem restrictTupleSectionsIso_inv_comp_restriction_omit [LinearOrder Λ] {n : ℕ}
    (β : OrdCechTuple Λ (n + 1)) (i : Fin (n + 2)) :
    (restrictTupleSectionsIso A V F (β.omit i).1).inv ≫
        ordCechRestriction (restrictCechSystem A V) F n β i =
      F.map ((restrictOpenFunctor A).map
          (interMap V β.1 fun j => (SimplexCategory.δ i).toOrderHom j)).op ≫
        (restrictTupleSectionsIso A V F β.1).inv :=
  restrictTupleSectionsIso_inv_comp_restriction A V F (SimplexCategory.δ i) β.1

/-- **Degreewise: the ordered Čech cochain group of a restriction cover is the alternating Čech
module of the Čech system of that cover.**  Two steps: the modules of the system are the groups of
sections of `F` over the restrictions, `restrictTupleSectionsIso`, and the categorical product
over the strictly increasing tuples is the group of functions on them,
`AddCommGrpCat.piIsoPi`. -/
def restrictOrdCechModuleIso (n : ℕ) :
    AddCommGrpCat.of (Alternating.CechCochainOrd ((restrictOpenFunctor A).op ⋙ F) V n) ≅
      ordCechModule (restrictCechSystem A V) F n :=
  ((Pi.mapIso fun β : OrdCechTuple Λ n => restrictTupleSectionsIso A V F β.1) ≪≫
    AddCommGrpCat.piIsoPi.{u, u + 1}
      fun β : OrdCechTuple Λ n =>
        F.obj (op ((restrictOpenFunctor A).obj (inter V β.1)))).symm

/-- The component of `restrictOrdCechModuleIso A V F n` at a strictly increasing tuple `β` is
evaluation at `β` followed by the inverse of `restrictTupleSectionsIso A V F β.1`. -/
@[reassoc (attr := simp)]
theorem restrictOrdCechModuleIso_hom_comp_ordCechπ (n : ℕ) (β : OrdCechTuple Λ n) :
    (restrictOrdCechModuleIso A V F n).hom ≫ ordCechπ (restrictCechSystem A V) F n β =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ β) ≫
        (restrictTupleSectionsIso A V F β.1).inv := by
  show ((AddCommGrpCat.piIsoPi fun γ : OrdCechTuple Λ n =>
        F.obj (op ((restrictOpenFunctor A).obj (inter V γ.1)))).inv ≫
      (Pi.mapIso fun γ : OrdCechTuple Λ n => restrictTupleSectionsIso A V F γ.1).inv) ≫
        Pi.π _ β = _
  rw [Category.assoc, Pi.mapIso_inv_π, ← Category.assoc,
    AddCommGrpCat.piIsoPi_inv_comp_π]

/-- **The identification commutes with the two differentials**: the ordered Čech differential of
the restriction cover, `...CechComplex.Alternating.cechDiffOrd`, is the alternating Čech
differential `ordCechDiff` of the modules of the Čech system of that cover.

This, with `restrictOrdCechModuleIso`, is the identification of the two complexes. -/
theorem cechDiffOrd_comp_restrictOrdCechModuleIso (n : ℕ) :
    AddCommGrpCat.ofHom (Alternating.cechDiffOrd ((restrictOpenFunctor A).op ⋙ F) V n) ≫
        (restrictOrdCechModuleIso A V F (n + 1)).hom =
      (restrictOrdCechModuleIso A V F n).hom ≫ ordCechDiff (restrictCechSystem A V) F n := by
  refine ordCechModule_hom_ext (restrictCechSystem A V) F fun β => ?_
  have key : ∀ i : Fin (n + 2),
      (restrictOrdCechModuleIso A V F n).hom ≫ ordCechπ (restrictCechSystem A V) F n (β.omit i) ≫
          ordCechRestriction (restrictCechSystem A V) F n β i =
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ (β.omit i)) ≫
          F.map ((restrictOpenFunctor A).map
              (interMap V β.1 fun j => (SimplexCategory.δ i).toOrderHom j)).op ≫
            (restrictTupleSectionsIso A V F β.1).inv := fun i => by
    rw [← Category.assoc, restrictOrdCechModuleIso_hom_comp_ordCechπ, Category.assoc,
      restrictTupleSectionsIso_inv_comp_restriction_omit]
    rfl
  rw [Category.assoc, restrictOrdCechModuleIso_hom_comp_ordCechπ, Category.assoc,
    comp_ordCechDiff_comp_ordCechπ, Finset.sum_congr rfl fun i _ => by rw [key i]]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  refine Eq.trans ?_ (Stacks.CechSite.hom_sum_apply Finset.univ _ s).symm
  show ((restrictTupleSectionsIso A V F β.1).inv).hom
      (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        Alternating.tres ((restrictOpenFunctor A).op ⋙ F) V (Fin.succAbove i) β.1
          (s (β.omit i))) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]; rfl

/-! ### The bottom row of [Stacks, Tag 07MN] as a complex -/

/-- The differential of the ordered Čech complex `restrictCechComplexOrd A V F` in degree `n` is
the ordered Čech differential `...CechComplex.Alternating.cechDiffOrd`. -/
theorem restrictCechComplexOrd_d (n : ℕ) :
    (CrystallineThickening.restrictCechComplexOrd.{u, u + 1, u} A V F).d n (n + 1) =
      AddCommGrpCat.ofHom (Alternating.cechDiffOrd ((restrictOpenFunctor A).op ⋙ F) V n) :=
  Alternating.cechCochainComplexOrd_d _ _ n

/-- **The bottom row of the double complex of [Stacks, Tag 07MN], for the Čech system of a
restriction cover, as a cochain complex**: in degree `n` the alternating Čech module
`⨁_{λ_0 < ⋯ < λ_n} M_{λ_0 … λ_n}`, with `ordCechDiff` as differential.

The identity `d ∘ d = 0` is *not* recomputed: it is transported from the ordered Čech complex of
the cover along `cechDiffOrd_comp_restrictOrdCechModuleIso`. -/
def restrictOrdCechSystemComplex : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  CochainComplex.of (fun n => ordCechModule (restrictCechSystem A V) F n)
    (fun n => ordCechDiff (restrictCechSystem A V) F n) fun n => by
      have hDD : AddCommGrpCat.ofHom
            (Alternating.cechDiffOrd ((restrictOpenFunctor A).op ⋙ F) V n) ≫
          AddCommGrpCat.ofHom
            (Alternating.cechDiffOrd ((restrictOpenFunctor A).op ⋙ F) V (n + 1)) = 0 := by
        rw [← restrictCechComplexOrd_d A V F n, ← restrictCechComplexOrd_d A V F (n + 1)]
        exact (CrystallineThickening.restrictCechComplexOrd.{u, u + 1, u}
          A V F).d_comp_d n (n + 1) (n + 2)
      rw [← Iso.cancel_iso_hom_left (restrictOrdCechModuleIso A V F n), comp_zero,
        ← Category.assoc, ← cechDiffOrd_comp_restrictOrdCechModuleIso, Category.assoc,
        ← cechDiffOrd_comp_restrictOrdCechModuleIso, ← Category.assoc, hDD, zero_comp]

/-- The term of `restrictOrdCechSystemComplex A V F` in degree `n` is the alternating Čech module
of `restrictCechSystem A V`. -/
@[simp]
theorem restrictOrdCechSystemComplex_X (n : ℕ) :
    (restrictOrdCechSystemComplex A V F).X n = ordCechModule (restrictCechSystem A V) F n :=
  rfl

/-- The differential of `restrictOrdCechSystemComplex A V F` in degree `n` is `ordCechDiff`. -/
@[simp]
theorem restrictOrdCechSystemComplex_d (n : ℕ) :
    (restrictOrdCechSystemComplex A V F).d n (n + 1) =
      ordCechDiff (restrictCechSystem A V) F n :=
  CochainComplex.of_d _ _ n

/-- **The ordered Čech complex of a restriction cover of an object of `Cris(X/S)` is the bottom row
of the double complex of [Stacks, Tag 07MN] for the Čech system of that cover.** -/
def restrictOrdCechComplexIso :
    CrystallineThickening.restrictCechComplexOrd.{u, u + 1, u} A V F ≅
      restrictOrdCechSystemComplex A V F :=
  HomologicalComplex.Hom.isoOfComponents (fun n => restrictOrdCechModuleIso A V F n)
    fun i j hij => by
      obtain rfl : j = i + 1 := hij.symm
      rw [restrictCechComplexOrd_d, restrictOrdCechSystemComplex_d]
      exact (cechDiffOrd_comp_restrictOrdCechModuleIso A V F i).symm

/-- **The bottom row of the double complex of [Stacks, Tag 07MN] for a restriction cover has, in
every degree, the cohomology of the ordered Čech complex of that cover.** -/
def restrictOrdCechSystemHomologyIso (j : ℕ) :
    (restrictOrdCechSystemComplex A V F).homology j ≅
      (CrystallineThickening.restrictCechComplexOrd.{u, u + 1, u} A V F).homology j :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) j).mapIso
    (restrictOrdCechComplexIso A V F).symm

/-- **The bottom row of the double complex of [Stacks, Tag 07MN] for a restriction cover computes
the Čech cohomology of that covering family, in every degree.**

This is as far as the step of [Stacks, Tag 07MN] left as "insert future reference here" reaches:
`...CrystallineThickening.restrictOrdCechCohomologyIso` lands the ordered Čech complex of the
cover on the Čech cohomology of the covering family, and `restrictOrdCechComplexIso` says that
complex is the remark's bottom row.  Passing from there to `RΓ(Cris(X/S), F)` needs
[Stacks, Tag 03F7] and the remark's de Rham direction; the former is applied to these covers in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OrdCechCoveredObject.lean`, at an index
type in `Type (u + 1)` and landing on the cohomology of the covered object.  See the module
documentation for what still separates the two. -/
def restrictOrdCechSystemCohomologyIso (j : ℕ) :
    (restrictOrdCechSystemComplex A V F).homology j ≅
      Stacks.CechSite.cechCohomology (restrictOpenHypercover A V) F j :=
  restrictOrdCechSystemHomologyIso A V F j ≪≫
    CrystallineThickening.restrictOrdCechCohomologyIso.{u, u + 1, u} A V F j

end Identification

end Crystalline.GlobalCrystallineSituation.SmallSite

end
