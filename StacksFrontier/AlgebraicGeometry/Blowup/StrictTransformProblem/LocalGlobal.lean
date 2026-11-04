module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenBase
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformProblem.Situation
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Product
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# The local-global reduction of the strict-transform problem

This is the third observation of [Stacks, Tag 080Y]: *if the property `P` is local on the base,
then so is the strict-transform problem.* Concretely, if every point of `S` has a quasi-compact
open neighbourhood `W` over which the problem for `F_W/X_W/W` is solvable, then the problem for
`F/X/S` is solvable.

## Main definitions

* `AlgebraicGeometry.StrictTransformProblem.restrict`: the strict-transform problem restricted to
  a quasi-compact open of the base. This is the triple `F_W/X_W/W` of the source.
* `AlgebraicGeometry.StrictTransformProblem.transform`: the strict-transform problem after a
  `U`-admissible blowup, i.e. the transformed triple as a strict-transform problem in its own
  right.

## Main results

* `AlgebraicGeometry.StrictTransformProblem.isSolvable_of_local`: **[Stacks, Tag 080Y], the
  local-global reduction.**

## Implementation notes

**The shape of the locality hypothesis.** The source reads "Suppose that `P` is local on `S`: if
`S = ⋃ S_i` is a finite open covering by quasi-compact opens and `P` holds for
`F_{S_i}/X_{S_i}/S_i` then `P` holds for `F/X/S`". That is a statement about the property `P`,
not about the given triple, and the proof uses it on the *blown-up* base; so the hypothesis is
quantified over every strict-transform problem carrying the same property. The index type of the
cover is a `Type` with `Finite`, which is the weakest form that the proof consumes: the cover it
builds is indexed by `Fin n`.

**The two realizations of the blowup.** `AlgebraicGeometry.StrictTransformProblem.IsSolvable` and
the stability field are phrased with `Stacks.Blowup.strictTransformMap` and
`Stacks.Blowup.strictTransformModule`, which live over `Stacks.Blowup.blowUp`, whereas
[Stacks, Tag 080I] and [Stacks, Tag 080A] are available over `AlgebraicGeometry.blowUp`. The two
are compared once and for all by
`AlgebraicGeometry.StrictTransformProblem.p_strictTransform_iff`, which is an application of the
isomorphism-invariance of `P` to `Stacks.Blowup.strictTransformIso`,
`AlgebraicGeometry.blowUpIso` and `Stacks.Blowup.pullbackStrictTransformModuleIso`; everything
after it happens over `AlgebraicGeometry.blowUp`.

**The proof.** Choose a finite subcover `V 0, …, V (n-1)` of quasi-compact opens with a solution
`I i` over each, extend each centre to a `U`-admissible centre `A i` on `S`
([Stacks, Tag 080M], `Stacks.Blowup.exists_idealSheafData_comap_eq`) and take `K = ∏ A i`. On
`V i` the centre `K` becomes `I i · J i` with `J i = ∏_{j ≠ i} A j|_{V i}`, so the blowup of `V i`
in `K|_{V i}` is the blowup in `I i` followed by the blowup in the inverse image of `J i`
([Stacks, Tag 080A]). The first step already has `P`; the second step preserves it, because the
stability field of the problem applies to the transformed triple with the inverse image of `J i`
as its centre — a finitely presented centre avoiding the inverse image of `U`. By
[Stacks, Tag 080I] the composite is the strict transform in `K|_{V i}`, and by
`AlgebraicGeometry.exists_strictTransformBlowUp_iso_restrict` that is the restriction to the
inverse image of `V i` of the strict transform in `K`. The inverse images of the `V i` cover the
blowup of `S` in `K`, so locality of `P` gives `P` for the strict transform in `K`.

## References

* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace StrictTransformProblem

/-! ### The two realizations of the blowup -/

/-- **The property of the transformed triple does not depend on which realization of the blowup
is used.** `Stacks.Blowup.strictTransformMap` and `Stacks.Blowup.strictTransformModule` are built
over `Stacks.Blowup.blowUp`, while `AlgebraicGeometry.strictTransformToBlowUp` and
`AlgebraicGeometry.strictTransformBlowUpModule` are built over `AlgebraicGeometry.blowUp`; the
two triples are isomorphic, so a property invariant under isomorphism cannot tell them apart. -/
public theorem p_strictTransform_iff (D : StrictTransformProblem.{u}) {Y T : Scheme.{u}}
    (g : Y ⟶ T) (G : Y.Modules) (ℐ : T.IdealSheafData) :
    D.P (Stacks.Blowup.strictTransformMap g ℐ) (Stacks.Blowup.strictTransformModule g ℐ G) ↔
      D.P (strictTransformToBlowUp g ℐ) (strictTransformBlowUpModule g ℐ G) :=
  (D.invariant_under_iso (strictTransformToBlowUp g ℐ) (Stacks.Blowup.strictTransformMap g ℐ)
    (strictTransformBlowUpModule g ℐ G) (Stacks.Blowup.strictTransformModule g ℐ G)
    (Stacks.Blowup.strictTransformIso g ℐ) (blowUpIso ℐ)
    (by
      rw [Stacks.Blowup.strictTransformIso_hom_strictTransformMap]
      simp only [strictTransformToBlowUp, Category.assoc])
    (Stacks.Blowup.pullbackStrictTransformModuleIso g ℐ G).symm).symm

/-! ### Restricting the problem to an open of the base -/

/-- **The strict-transform problem on a quasi-compact open of the base.** This is the triple
`F_W/X_W/W` of [Stacks, Tag 080Y]: the base change of the morphism and of the module along the
open immersion, with the distinguished open replaced by its inverse image. -/
public def restrict (D : StrictTransformProblem.{u}) (W : D.S.Opens)
    (hW : IsCompact (W : Set D.S)) : StrictTransformProblem.{u} where
  S := W.toScheme
  compactSpace := isCompact_iff_compactSpace.mp hW
  quasiSeparatedSpace := W.ι.isOpenEmbedding.quasiSeparatedSpace
  X := Limits.pullback D.f W.ι
  f := pullback.snd D.f W.ι
  F := (Scheme.Modules.pullback (pullback.fst D.f W.ι)).obj D.F
  quasicoherent := inferInstance
  U := W.ι ⁻¹ᵁ D.U
  compact_U := by
    letI : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
    rw [W.ι.isEmbedding.isCompact_iff]
    change IsCompact (W.ι.base '' (W.ι.base ⁻¹' (D.U : Set D.S)))
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    simpa [Set.inter_comm] using IsCompact.inter_of_isOpen hW D.compact_U W.2 D.U.2
  P := D.P
  invariant_under_iso := D.invariant_under_iso
  stable := by
    intro Y T _ _ g G _ p hV I hI hdisj hP
    exact D.stable g G (p ≫ W.ι) hV I hI hdisj hP

/-- The property of the restricted problem is the property of the original problem. -/
@[simp]
public lemma restrict_P (D : StrictTransformProblem.{u}) (W : D.S.Opens)
    (hW : IsCompact (W : Set D.S)) : @(D.restrict W hW).P = @D.P :=
  rfl

/-! ### Transforming the problem by an admissible blowup -/

/-- **The transformed strict-transform problem.** The strict transform of the triple along the
blowup of the base in a finitely presented centre, as a strict-transform problem over the blowup.
The distinguished open is the inverse image of the original one, which is what makes the
stability of the property apply again. -/
public def transform (D : StrictTransformProblem.{u}) (C : D.S.IdealSheafData)
    (hC : FinitePresentation C.subschemeι) : StrictTransformProblem.{u} where
  S := blowUp C
  compactSpace :=
    haveI : IsProper (blowUpToBase C) :=
      isProper_blowUpToBase_of_fg C ((finitePresentation_subschemeι_iff_isFiniteType C).mp hC)
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase C)
  quasiSeparatedSpace :=
    haveI : IsProper (blowUpToBase C) :=
      isProper_blowUpToBase_of_fg C ((finitePresentation_subschemeι_iff_isFiniteType C).mp hC)
    quasiSeparatedSpace_of_quasiSeparated (blowUpToBase C)
  X := Stacks.StrictTransform.scheme D.f (blowUpToBase C) (exceptionalIdeal C)
  f := strictTransformToBlowUp D.f C
  F := strictTransformBlowUpModule D.f C D.F
  quasicoherent := inferInstance
  U := blowUpToBase C ⁻¹ᵁ D.U
  compact_U :=
    haveI : IsProper (blowUpToBase C) :=
      isProper_blowUpToBase_of_fg C ((finitePresentation_subschemeι_iff_isFiniteType C).mp hC)
    QuasiCompact.isCompact_preimage (f := blowUpToBase C) _ D.U.2 D.compact_U
  P := D.P
  invariant_under_iso := D.invariant_under_iso
  stable := by
    intro Y T _ _ g G _ p hV I hI hdisj hP
    exact D.stable g G (p ≫ blowUpToBase C) hV I hI hdisj hP

/-- The property of the transformed problem is the property of the original problem. -/
@[simp]
public lemma transform_P (D : StrictTransformProblem.{u}) (C : D.S.IdealSheafData)
    (hC : FinitePresentation C.subschemeι) : @(D.transform C hC).P = @D.P :=
  rfl


/-! ### The local step -/

/-- The blowup of a finitely presented centre is proper over the base. -/
private theorem isProper_blowUpToBase_of_finitePresentation {X : Scheme.{u}}
    (C : X.IdealSheafData) (hC : FinitePresentation C.subschemeι) :
    IsProper (blowUpToBase C) :=
  isProper_blowUpToBase_of_fg C ((finitePresentation_subschemeι_iff_isFiniteType C).mp hC)

/-- A finite product of finitely presented centres is finitely presented. -/
private theorem finitePresentation_prod_subschemeι {X : Scheme.{u}} {ι : Type*}
    (s : Finset ι) (A : ι → X.IdealSheafData)
    (hA : ∀ i, FinitePresentation (A i).subschemeι) : FinitePresentation (s.prod A).subschemeι :=
  (finitePresentation_subschemeι_iff_isFiniteType _).mpr
    (Stacks.Blowup.isFiniteType_prod s A fun i ↦
      (finitePresentation_subschemeι_iff_isFiniteType (A i)).mp (hA i))

/-- A set disjoint from the support of a centre has preimage disjoint from the support of the
inverse image of the centre. -/
private theorem disjoint_preimage_support_comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (J : X.IdealSheafData)
    {s : Set X} (h : Disjoint s (J.support : Set X)) :
    Disjoint (f.base ⁻¹' s) ((J.comap f).support : Set Y) := by
  rw [Scheme.IdealSheafData.support_comap]
  exact h.preimage f.base

/-- **The transformed problem has the property over the inverse image of an open on which the
centre factors through a solved centre.** Let `V` be a quasi-compact open of the base on which
the global centre `K` becomes a product `I · J` with `I` a centre whose strict transform already
has `P` and `J` a finitely presented centre avoiding `U`. Then the strict transform in `K`, read
over the inverse image of `V`, has `P`. -/
private theorem p_restrict_transform (D : StrictTransformProblem.{u}) (V : D.S.Opens)
    (hV : IsCompact (V : Set D.S)) (Il Jl : V.toScheme.IdealSheafData)
    (hIlfp : FinitePresentation Il.subschemeι) (hJlfp : FinitePresentation Jl.subschemeι)
    (hJldisj : Disjoint ((V.ι ⁻¹ᵁ D.U : V.toScheme.Opens) : Set V.toScheme)
      (Jl.support : Set V.toScheme))
    (K : D.S.IdealSheafData) (hKl : K.comap V.ι = Il * Jl)
    (hIlP : D.P (strictTransformToBlowUp (pullback.snd D.f V.ι) Il)
      (strictTransformBlowUpModule (pullback.snd D.f V.ι) Il
        ((Scheme.Modules.pullback (pullback.fst D.f V.ι)).obj D.F))) :
    D.P (pullback.snd (strictTransformToBlowUp D.f K)
        (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι)
      ((Scheme.Modules.pullback (pullback.fst (strictTransformToBlowUp D.f K)
        (blowUpToBase K ⁻¹ᵁ V : (blowUp K).Opens).ι)).obj
        (strictTransformBlowUpModule D.f K D.F)) := by
  have := isProper_blowUpToBase_of_finitePresentation Il hIlfp
  let : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  let : QuasiSeparatedSpace V.toScheme := V.ι.isOpenEmbedding.quasiSeparatedSpace
  let : CompactSpace (blowUp Il) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Il)
  let : QuasiSeparatedSpace (blowUp Il) :=
    quasiSeparatedSpace_of_quasiSeparated (blowUpToBase Il)
  have hMfp : FinitePresentation (Jl.comap (blowUpToBase Il)).subschemeι :=
    finitePresentation_comap_subschemeι Jl (blowUpToBase Il) hJlfp
  have hUV : IsCompact ((V.ι ⁻¹ᵁ D.U : V.toScheme.Opens) : Set V.toScheme) :=
    (D.restrict V hV).compact_U
  have hUVbl : IsCompact ((((blowUpToBase Il) ≫ V.ι) ⁻¹ᵁ D.U : (blowUp Il).Opens) :
      Set (blowUp Il)) :=
    QuasiCompact.isCompact_preimage (f := blowUpToBase Il) _ (V.ι ⁻¹ᵁ D.U).2 hUV
  have hMdisj : Disjoint ((((blowUpToBase Il) ≫ V.ι) ⁻¹ᵁ D.U : (blowUp Il).Opens) :
        Set (blowUp Il))
      (((Jl.comap (blowUpToBase Il)).support) : Set (blowUp Il)) :=
    disjoint_preimage_support_comap _ Jl hJldisj
  have hP2 := D.stable (strictTransformToBlowUp (pullback.snd D.f V.ι) Il)
    (strictTransformBlowUpModule (pullback.snd D.f V.ι) Il
      ((Scheme.Modules.pullback (pullback.fst D.f V.ι)).obj D.F))
    (blowUpToBase Il ≫ V.ι) hUVbl (Jl.comap (blowUpToBase Il)) hMfp hMdisj hIlP
  have hP3 := (D.p_strictTransform_iff (strictTransformToBlowUp (pullback.snd D.f V.ι) Il)
    (strictTransformBlowUpModule (pullback.snd D.f V.ι) Il
      ((Scheme.Modules.pullback (pullback.fst D.f V.ι)).obj D.F))
    (Jl.comap (blowUpToBase Il))).mp hP2
  obtain ⟨k, hk, ⟨hkF⟩⟩ := exists_strictTransformBlowUpModule_iso_comp
    (pullback.snd D.f V.ι) Il (Il * Jl) (Jl.comap (blowUpToBase Il))
    (supportSet_mul_eq_union_image_comap Il Jl) (blowUpMulIso Il Jl)
    ((Scheme.Modules.pullback (pullback.fst D.f V.ι)).obj D.F)
  have hP4 := (D.invariant_under_iso _ _ _ _ k
    ((Over.forget V.toScheme).mapIso (blowUpMulIso Il Jl)) hk.symm hkF).mp hP3
  have hP5 : D.P (strictTransformToBlowUp (pullback.snd D.f V.ι) (K.comap V.ι))
      (strictTransformBlowUpModule (pullback.snd D.f V.ι) (K.comap V.ι)
        ((Scheme.Modules.pullback (pullback.fst D.f V.ι)).obj D.F)) := by
    rw [hKl]
    exact hP4
  obtain ⟨eT, eY, hmap, ⟨hmod⟩⟩ := exists_strictTransformBlowUp_iso_restrict D.f K V D.F
  exact (D.invariant_under_iso _ _ _ _ eY eT hmap hmod).mp hP5

/-! ### The local-global reduction -/

/-- **[Stacks, Tag 080Y], the local-global reduction.** Suppose the property `P` is local on the
base: for every strict-transform problem with that property, if the base is covered by finitely
many quasi-compact opens over each of which the restricted triple has `P`, then the triple itself
has `P`. Then the strict-transform problem is local on the base too: if every point of `S` has a
quasi-compact open neighbourhood over which the problem is solvable, the problem is solvable. -/
@[stacks 080Y "the local-global reduction, the remark's third paragraph; the locality of P on \
the base is the hypothesis the remark states it under"]
public theorem isSolvable_of_local (D : StrictTransformProblem.{u})
    (hP : ∀ E : StrictTransformProblem.{u}, @E.P = @D.P →
      ∀ {ι : Type} [Finite ι] (W : ι → E.S.Opens) (hW : ∀ i, IsCompact (W i : Set E.S)),
        (⋃ i, (W i : Set E.S)) = Set.univ →
        (∀ i, (E.restrict (W i) (hW i)).P (E.restrict (W i) (hW i)).f
          (E.restrict (W i) (hW i)).F) →
        E.P E.f E.F)
    (hlocal : ∀ s : D.S, ∃ (W : D.S.Opens) (hW : IsCompact (W : Set D.S)),
      s ∈ (W : Set D.S) ∧ (D.restrict W hW).IsSolvable) :
    D.IsSolvable := by
  classical
  choose W hWc hWmem hWsol using hlocal
  have hcover : (Set.univ : Set D.S) ⊆ ⋃ s, (W s : Set D.S) := fun s _ ↦
    Set.mem_iUnion.mpr ⟨s, hWmem s⟩
  obtain ⟨t, ht⟩ := (isCompact_univ (X := D.S)).elim_finite_subcover
    (fun s ↦ (W s : Set D.S)) (fun s ↦ (W s).isOpen) hcover
  have hVc : ∀ i : Fin t.card, IsCompact ((W ((t.equivFin.symm i) : D.S)) : Set D.S) :=
    fun i ↦ hWc _
  have hVcover : (⋃ i : Fin t.card, ((W ((t.equivFin.symm i) : D.S)) : Set D.S)) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun s ↦ ?_
    obtain ⟨s', hs't, hsW⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ s))
    exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨s', hs't⟩, by simpa using hsW⟩
  choose Iloc hIfp hIdisj hIP using fun i : Fin t.card ↦ hWsol ((t.equivFin.symm i) : D.S)
  choose A hAfp hAdisj hAcomap using fun i : Fin t.card ↦
    Stacks.Blowup.exists_idealSheafData_comap_eq D.U (W ((t.equivFin.symm i) : D.S))
      D.compact_U (hVc i) (Iloc i) (hIfp i) (hIdisj i)
  have hKfp := finitePresentation_prod_subschemeι Finset.univ A hAfp
  have hKdisj : Disjoint (D.U : Set D.S) ((Finset.univ.prod A).support : Set D.S) := by
    simpa using Stacks.Blowup.disjoint_support_prod D.U Finset.univ A fun i _ ↦ hAdisj i
  refine ⟨Finset.univ.prod A, hKfp, hKdisj,
    (D.p_strictTransform_iff D.f D.F (Finset.univ.prod A)).mpr ?_⟩
  have := isProper_blowUpToBase_of_finitePresentation _ hKfp
  have hZc : ∀ i : Fin t.card,
      IsCompact ((blowUpToBase (Finset.univ.prod A) ⁻¹ᵁ
        (W ((t.equivFin.symm i) : D.S)) : (blowUp (Finset.univ.prod A)).Opens) :
          Set (blowUp (Finset.univ.prod A))) :=
    fun i ↦ QuasiCompact.isCompact_preimage (f := blowUpToBase (Finset.univ.prod A)) _
      (W ((t.equivFin.symm i) : D.S)).2 (hVc i)
  have hZcover : (⋃ i : Fin t.card, ((blowUpToBase (Finset.univ.prod A) ⁻¹ᵁ
      (W ((t.equivFin.symm i) : D.S)) : (blowUp (Finset.univ.prod A)).Opens) :
        Set (blowUp (Finset.univ.prod A)))) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    have hx : (blowUpToBase (Finset.univ.prod A)).base x ∈
        (⋃ i : Fin t.card, ((W ((t.equivFin.symm i) : D.S)) : Set D.S)) := by
      rw [hVcover]
      exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine hP (D.transform (Finset.univ.prod A) hKfp) rfl
    (fun i : Fin t.card ↦ blowUpToBase (Finset.univ.prod A) ⁻¹ᵁ
      (W ((t.equivFin.symm i) : D.S))) hZc hZcover fun i ↦ ?_
  refine D.p_restrict_transform (W ((t.equivFin.symm i) : D.S)) (hVc i) (Iloc i)
    (((Finset.univ.erase i).prod A).comap (W ((t.equivFin.symm i) : D.S)).ι) (hIfp i) ?_ ?_
    (Finset.univ.prod A) ?_ ((D.p_strictTransform_iff _ _ (Iloc i)).mp (hIP i))
  · exact finitePresentation_comap_subschemeι _ _
      (finitePresentation_prod_subschemeι _ A hAfp)
  · exact disjoint_preimage_support_comap _ _
      (Stacks.Blowup.disjoint_support_prod D.U (Finset.univ.erase i) A fun j _ ↦ hAdisj j)
  · rw [← Finset.mul_prod_erase Finset.univ A (Finset.mem_univ i), Stacks.IdealSheaf.comap_mul,
      hAcomap i]

end StrictTransformProblem

end AlgebraicGeometry

end
