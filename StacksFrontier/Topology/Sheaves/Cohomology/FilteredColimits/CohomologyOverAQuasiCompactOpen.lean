module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.CechComplexOfAFiniteFamily
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.DegreeInduction
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen

/-!
# Cohomology over a quasi-compact open commutes with filtered colimits (Stacks 01FF)

Let `X` be a topological space with a basis of quasi-compact opens whose pairwise intersections
are quasi-compact, let `O_X` be a sheaf of rings on `X` and let `U` be a quasi-compact open.
Stacks 01FF says that for every filtered system `F` of `O_X`-modules and every degree `q` the
canonical map `colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism.

The induction on `q` that proves this is carried out, for an arbitrary cohomological δ-functor,
in `StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit` and plugged into the
cohomology δ-functor in `StacksDraft.Ch20.Sec18.Tag01FFColimit`; it reduces the tag to two
inputs.  The degree-zero input, Stacks 009F for sheaves of modules, is
`StacksDraft.Ch20.Sec18.Tag01FFSections`.  This file supplies the second input, the vanishing
`Hⁿ⁺¹(U, colimᵢ Iᵢ) = 0` for a filtered system of injectives, and concludes the tag.

## The vanishing

Take for `B` the set of *all* quasi-compact opens of `X` — a basis, by (H1) — and for `Cov` the
set of finite open covers by quasi-compact opens of a quasi-compact open.  Then

* every finite intersection of members of a cover in `Cov` is again quasi-compact, by (H2)
  (`isCompact_coe_iInf`), so `Cov` satisfies the hypothesis `hCovBasis` of Stacks 01EW;
* every open cover of a quasi-compact open is refined by a member of `Cov` covering it, which is
  conclusion (C3) of Stacks 0069 (`exists_compactCover_refines`); and
* the positive-degree Čech cohomology of `colimᵢ Iᵢ` vanishes for every cover in `Cov`
  (`cechCohomologyIsZero_colimit`).

Stacks 01EW then gives the vanishing of `Hⁿ⁺¹(U, colimᵢ Iᵢ)` for every `U ∈ B`.

The third point is where the two halves of the argument meet.  The Čech complex of a *finite*
cover commutes with colimits of presheaves (Stacks 0A37,
`preservesColimitsOfShape_cechComplexFunctor`), but a colimit of sheaves of modules is *not*
computed as a colimit of presheaves — except on the quasi-compact opens, by Stacks 009F.  Since
all the opens occurring in the Čech complex of a cover in `Cov` are quasi-compact, the two facts
combine: `preservesColimitsOfShape_cechComplexFunctor_comp` shows that the functor sending a
sheaf of modules to the Čech complex of its underlying presheaf preserves filtered colimits.  The
Čech complexes at the stages are acyclic in positive degrees, because an injective sheaf of
modules is flasque (Stacks 01EP) and a flasque sheaf has no higher Čech cohomology (Stacks 09SZ);
and a filtered colimit of complexes acyclic in a positive degree is acyclic there (Stacks 00DB,
`exactAt_succ_of_isColimit`).

## Main results

* `Stacks.Cohomology.Vanishing.isZero_Hfunctor_succ_obj_colimit_of_injective`: the vanishing
  input of Stacks 01FF.
* `Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact`: **Stacks 01FF**.

## Implementation notes

The universes are all equal; see the implementation notes of
`StacksDraft.Ch20.Sec18.Tag01FFColimit` for why the three-universe form in which the tag is
stated in the source is out of reach of the long exact sequence and of Stacks 01EW as they
stand.  Stacks 01FF has no universe content, so this is a faithful restatement.

**The tag carries no typeclass hypothesis.**  With the space, the ring sheaf and the modules all
in the same universe, `HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}`, its
`WEqualsLocallyBijective` companion and `EnoughInjectives (SheafOfModules.{u} R)` are all plain
instances: the site of opens of a space in `Type u` is `u`-small, so Mathlib's
`SheafOfModules.instIsGrothendieckAbelian` applies and
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` is a global instance.  Nothing beyond the
tag's own hypotheses — a basis of quasi-compact opens, quasi-compact pairwise intersections, a
quasi-compact `U` and a filtered index category — is assumed.
(`SheafOfModules.enoughInjectives_of_univLE` would also do the injectives, at `UnivLE.{u, u}`;
it is not needed here and is not imported.)

The *auxiliary* vanishing lemma keeps the two sheafification hypotheses as binders, which is a
performance matter and not a mathematical one: dropping them makes the `HasColimit E` of its own
conclusion re-derive sheafification from scratch and exceed the 20000-heartbeat
`synthInstance` budget, which `set_option` is not available to raise.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (OpenCover CechCohomologyIsZero compactOpens)

universe u

namespace Stacks.Cohomology.Vanishing

/-! ### Finite intersections of quasi-compact opens -/

/-- **A nonempty finite infimum of quasi-compact opens is quasi-compact**, by (H2). -/
theorem isCompact_coe_finsetInf {X : Type u} [TopologicalSpace X]
    (hInter : QuasiSeparatedSpace X) {κ : Type*} (f : κ → Opens X)
    (hf : ∀ k, IsCompact (f k : Set X)) {s : Finset κ} (hs : s.Nonempty) :
    IsCompact ((s.inf f : Opens X) : Set X) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a
  | cons a s ha hs ih =>
    rw [Finset.inf_cons, Opens.coe_inf]
    exact hInter.inter_isCompact _ _ (f a).isOpen (hf a) (s.inf f).isOpen ih

/-- **A finite, nonempty intersection of quasi-compact opens is quasi-compact.**  This is the
form in which the Čech complex of a cover by quasi-compact opens needs (H2): its degree-`n` term
is a product over the tuples `x : Fin (n + 1) → ι` of the sections over `⨅ k, U (x k)`, and the
index type `Fin (n + 1)` is never empty. -/
theorem isCompact_coe_iInf {X : Type u} [TopologicalSpace X]
    (hInter : QuasiSeparatedSpace X) {m : ℕ} (f : Fin (m + 1) → Opens X)
    (hf : ∀ k, IsCompact (f k : Set X)) :
    IsCompact ((⨅ k, f k : Opens X) : Set X) := by
  rw [← Finset.inf_univ_eq_iInf]
  exact isCompact_coe_finsetInf hInter f hf Finset.univ_nonempty

/-! ### The basis and the covers -/

/-- The set of finite open covers of a quasi-compact open by quasi-compact opens: the collection
`Cov` of Stacks 01EW used here.  Finiteness is what makes the Čech complex commute with
colimits, and quasi-compactness of the members is what makes Stacks 009F apply on all the opens
occurring in it. -/
def compactCovers (X : Type u) [TopologicalSpace X] : Set (OpenCover X) :=
  {W | Finite W.ι ∧ IsCompact (W.carrier : Set X) ∧ ∀ i, IsCompact (W.obj i : Set X)}

/-- **The quasi-compact opens form a basis**, which is hypothesis (H1) read through
`TopologicalSpace.Opens.IsBasis`: a basis of quasi-compact opens is in particular contained in
the set of all quasi-compact opens, and a set of opens containing a basis is a basis. -/
theorem isBasis_compactOpens {X : Type u} [TopologicalSpace X]
    (hBasis : PrespectralSpace X) :
    Opens.IsBasis (compactOpens X) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨t, htB, hxt, htV⟩ := hBasis.isTopologicalBasis.exists_subset_of_mem_open hx V.isOpen
  exact ⟨⟨t, hBasis.isTopologicalBasis.isOpen htB⟩, htB.2, hxt, htV⟩

/-- **The covers in `compactCovers` satisfy the hypothesis `hCovBasis` of Stacks 01EW**: the open
they cover, their members, and all the intersections occurring in their Čech complex are
quasi-compact. -/
theorem compactCovers_mem_compactOpens {X : Type u} [TopologicalSpace X]
    (hInter : QuasiSeparatedSpace X) (W : OpenCover X) (hW : W ∈ compactCovers X) :
    W.carrier ∈ compactOpens X ∧ (∀ i, W.obj i ∈ compactOpens X) ∧
      ∀ (p : ℕ) (s : Fin (p + 1) → W.ι), (⨅ k, W.obj (s k)) ∈ compactOpens X :=
  ⟨hW.2.1, hW.2.2, fun _ s => isCompact_coe_iInf hInter (fun k => W.obj (s k)) fun _ => hW.2.2 _⟩

/-- **The covers in `compactCovers` are cofinal**, which is conclusion (C3) of Stacks 0069: every
open cover of a quasi-compact open `U` is refined by a finite cover of `U` by quasi-compact
opens.

The refinement produced by `hasCofinalCompactRefinements_of_isCompact_isOpen` is indexed by a
`Finset` of a type in `Type 0`, which is lifted to `Type u` because `OpenCover.ι` lives
there. -/
theorem exists_compactCover_refines {X : Type u} [TopologicalSpace X]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X) (U : Opens X)
    (hU : IsCompact (U : Set X)) (V : OpenCover X) (hV : V.carrier = U) :
    ∃ W ∈ compactCovers X, W.carrier = U ∧ W.Refines V := by
  obtain ⟨ι, Jf, W, hWopen, hWcomp, hWeq, -, hWref⟩ :=
    hasCofinalCompactRefinements_of_isCompact_isOpen hBasis hInter U.isOpen hU
      (fun i => ((V.obj i : Opens X) : Set X)) (fun i => (V.obj i).isOpen)
      (by
        intro x hx
        have hxV : x ∈ (⨆ i, V.obj i : Opens X) := by rwa [V.iSup_eq, hV]
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxV
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨{ ι := ULift.{u, 0} { j // j ∈ Jf }
            carrier := U
            obj := fun j => ⟨W j.down.1, hWopen _ j.down.2⟩
            iSup_eq := ?_ },
    ⟨Finite.of_equiv _ Equiv.ulift.symm, hU, fun j => hWcomp _ j.down.2⟩, rfl, hV.symm, ?_⟩
  · apply Opens.ext
    rw [Opens.coe_iSup, hWeq]
    ext x
    simp
  · exact fun j => hWref _ j.down.2

/-! ### The Čech complex of a quasi-compact cover commutes with filtered colimits -/

section Cech

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {I : Type u} [SmallCategory I] [IsFiltered I]

/-- **A finite product of sections functors over quasi-compact opens preserves filtered
colimits.**  The degree-`n` term of the Čech complex of a cover is the functor `piEval` of Stacks
0A37 applied to the family of the intersections occurring in it; precomposed with the forgetful
functor from sheaves of modules it becomes `F ↦ ∏ t, Γ(V t, F)`.

Each factor preserves filtered colimits by Stacks 009F for modules, because `V t` is
quasi-compact; and a *finite* product of abelian groups is a coproduct, so the product of the
factors preserves them too.  This is the step at which the finiteness of the cover is used. -/
theorem preservesColimitsOfShape_piEval_comp
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (T : Type u) [Finite T] (V : T → Opens X) (hV : ∀ t, IsCompact (V t : Set X)) :
    PreservesColimitsOfShape I
      (SheafOfModules.toSheaf.{u} R ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          CechColimit.piEval (A := AddCommGrpCat.{u}) T V) := by
  have hwhisk : PreservesColimitsOfShape I
      (SheafOfModules.toSheaf.{u} R ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          (Functor.whiskeringLeft (Discrete T) (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
            (Discrete.functor fun t => op (V t))) :=
    preservesColimitsOfShape_of_evaluation _ I fun t =>
      Sections.preservesColimitsOfShape_secF_of_isCompact R hBasis hInter (V t.as) (hV t.as)
  have hsigma : PreservesColimitsOfShape I
      ((SheafOfModules.toSheaf.{u} R ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⋙
          CechColimit.sigmaEval (A := AddCommGrpCat.{u}) T V) :=
    comp_preservesColimitsOfShape
      (SheafOfModules.toSheaf.{u} R ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          (Functor.whiskeringLeft (Discrete T) (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
            (Discrete.functor fun t => op (V t)))
      (colim : (Discrete T ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf.{u} R ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (CechColimit.piEvalIsoSigmaEval (A := AddCommGrpCat.{u}) T V).symm)

/-- **The Čech complex of a finite cover by quasi-compact opens, as a functor on sheaves of
modules, preserves filtered colimits.**  Colimits of cochain complexes are computed degreewise,
and the degree-`n` term is the finite product of the sections over the intersections occurring in
the cover, all of which are quasi-compact. -/
theorem preservesColimitsOfShape_cechComplexFunctor_comp
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (W : OpenCover X) (hW : W ∈ compactCovers X) :
    PreservesColimitsOfShape I
      (SheafOfModules.toSheaf.{u} R ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          cechComplexFunctor (A := AddCommGrpCat.{u}) W.obj) := by
  have := hW.1
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n => ?_
  exact preservesColimitsOfShape_piEval_comp R hBasis hInter (Fin (n + 1) → W.ι)
    (inter W.obj) fun x => by
      rw [inter_eq_iInf]
      exact isCompact_coe_iInf hInter (fun k => W.obj (x k)) fun k => hW.2.2 _

/-- **The positive-degree Čech cohomology of a filtered colimit of injectives vanishes**, for
every finite cover by quasi-compact opens.

The Čech complex of the colimit is the colimit of the Čech complexes
(`preservesColimitsOfShape_cechComplexFunctor_comp`); each of those is acyclic in positive
degrees, because an injective sheaf of modules is flasque (Stacks 01EP) and a flasque sheaf has
vanishing higher Čech cohomology (Stacks 09SZ); and a filtered colimit of complexes acyclic in a
positive degree is acyclic there (Stacks 00DB). -/
theorem cechCohomologyIsZero_colimit
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (W : OpenCover X) (hW : W ∈ compactCovers X) (E : I ⥤ SheafOfModules.{u} R)
    (hE : ∀ i, Injective (E.obj i)) (n : ℕ) (hn : 0 < n) :
    CechCohomologyIsZero R (colimit E) W n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hpres := preservesColimitsOfShape_cechComplexFunctor_comp R hBasis hInter W hW (I := I)
  change IsZero (((cechComplexFunctor W.obj).obj
    ((SheafOfModules.toSheaf R).obj (colimit E)).obj).homology (m + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine CechColimit.exactAt_succ_of_isColimit
    (isColimitOfPreserves (SheafOfModules.toSheaf.{u} R ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        cechComplexFunctor (A := AddCommGrpCat.{u}) W.obj) (colimit.isColimit E)) m fun i => ?_
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have := hE i
  exact FlasqueCech.isZero_cechComplex_homology_of_isFlasque
    (BasisCycles.topSheaf R (E.obj i)) (⨆ k, W.obj k) W.obj rfl (m + 1) (Nat.succ_pos m)

end Cech

/-! ### The vanishing input of Stacks 01FF, and the tag -/

/-- **The vanishing input of Stacks 01FF.**  Let `X` have a basis of quasi-compact opens whose
pairwise intersections are quasi-compact, let `U` be a quasi-compact open and let `E` be a
filtered system of *injective* `O_X`-modules.  Then `Hⁿ⁺¹(U, colimᵢ Eᵢ) = 0` for every `n`.

This is Stacks 01EW applied to the basis of all quasi-compact opens and the collection of finite
covers by quasi-compact opens: those covers are cofinal by Stacks 0069, their Čech complexes have
only quasi-compact opens in them, and the positive-degree Čech cohomology of the colimit for such
a cover vanishes. -/
theorem isZero_Hfunctor_succ_obj_colimit_of_injective
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X))
    (E : I ⥤ SheafOfModules.{u} R) (hE : ∀ i, Injective (E.obj i)) (n : ℕ) :
    IsZero ((Hfunctor R U (n + 1)).obj (colimit E)) :=
  BasisCycles.isZero_hgroup_of_cech_isZero_on_basis R (colimit E) (compactOpens X)
    (isBasis_compactOpens hBasis) (compactCovers X)
    (compactCovers_mem_compactOpens hInter)
    (fun V hV => exists_compactCover_refines hBasis hInter V hV)
    (fun W hW p hp => cechCohomologyIsZero_colimit R hBasis hInter W hW E hE p hp)
    U hU (n + 1) (Nat.succ_pos n)

/-- **Stacks 01FF.**  Let `X` be a topological space with a basis of quasi-compact opens whose
pairwise intersections are quasi-compact, let `O_X` be a sheaf of rings on `X` and let `U` be a
quasi-compact open of `X`.  Then for every filtered system `F` of `O_X`-modules and every degree
`q` the canonical map `colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism.

The proof is the induction of the source on `q`, carried out for an arbitrary cohomological
δ-functor in `CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero` and specialized to
the cohomology δ-functor in
`Stacks.Cohomology.Colimit.isIso_colimit_post_Hfunctor_of_preservesColimitsOfShape`.  Its two
inputs are Stacks 009F for sheaves of modules
(`Stacks.Cohomology.Sections.preservesColimitsOfShape_secF_of_isCompact`) and the vanishing
`isZero_Hfunctor_succ_obj_colimit_of_injective` above.

The hypotheses are exactly the tag's: sheafification of abelian presheaves on the site of opens,
its characterization by local bijectivity, and enough injectives in `SheafOfModules.{u} R` are
all instances at these universes, so none of them is assumed. -/
@[stacks 01FF]
theorem isIso_colimit_post_Hfunctor_of_isCompact
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ SheafOfModules.{u} R)
    (U : Opens X) (hU : IsCompact (U : Set X)) (q : ℕ) :
    IsIso (colimit.post F (Hfunctor R U q)) :=
  have : PreservesColimitsOfShape I (secF R U : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) :=
    Sections.preservesColimitsOfShape_secF_of_isCompact R hBasis hInter U hU
  Colimit.isIso_colimit_post_Hfunctor_of_preservesColimitsOfShape R U
    (fun E hE n => isZero_Hfunctor_succ_obj_colimit_of_injective R hBasis hInter U hU E hE n) F q

end Stacks.Cohomology.Vanishing

end
