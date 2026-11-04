module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsQuasiCompact.CompactBasisVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsQuasiCompact.SectionsColimit
public import StacksFrontier.Homology.Injectives.KInjective.Enlargement
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.CechComplexOfAFiniteFamily

/-!
# The higher cohomology of a filtered colimit of injectives on a quasi-compact open

Let `X` be a topological space with a basis of quasi-compact opens whose binary intersections
are again quasi-compact — hypotheses (H1) and (H2) of Stacks 0069 — let `R` be a sheaf of rings
on `X` and let `U ⊆ X` be a quasi-compact open. For a filtered system of *injective* sheaves of
`R`-modules the higher cohomology of the colimit over `U` vanishes:
`Hⁿ(U, colimᵢ Iᵢ) = 0` for `n > 0`.

This is the claim in the middle of the proof of Stacks 01FF, the step that makes the dimension
shift there work. The proof is the source's: with `B` the quasi-compact opens and `Cov` the
finite coverings by quasi-compact opens, all the multiple intersections occurring in a Čech
complex of a member of `Cov` are quasi-compact, so sections over them commute with the colimit
(Stacks 009F for sheaves of modules, which is
`Stacks.Cohomology.CompactSections.preservesColimitsOfShape_secF`); the Čech complex of the
colimit is therefore the colimit of the Čech complexes of the `Iᵢ`, each of which is acyclic in
positive degrees because an injective sheaf of modules is flasque; a filtered colimit of
complexes acyclic in positive degrees is acyclic (Stacks 00DB); and Stacks 01EW turns that Čech
vanishing into the vanishing of the higher cohomology over every quasi-compact open.

## Main results

* `Stacks.Cohomology.CompactColimit.cechCohomologyIsZero_colimit`: positive-degree Čech
  vanishing for a finite covering by quasi-compact opens passes to a filtered colimit of sheaves
  of modules.
* `Stacks.Cohomology.CompactColimit.isZero_hgroup_colimit_of_injective`: the higher cohomology
  over a quasi-compact open of a filtered colimit of injective sheaves of modules vanishes.
* `Stacks.Cohomology.CompactColimit.isZero_hgroup_colimit_injectiveEmbedding`: the same for the
  system of functorial injective embeddings of an arbitrary filtered system, which is the system
  the dimension shift of Stacks 01FF is applied to.

## Implementation notes

The identification of the Čech complex of a colimit with the colimit of the Čech complexes is
*not* obtained by exhibiting the underlying presheaf of the colimit sheaf as a colimit of
presheaves — it is not one. It is obtained degreewise: the degree-`n` term of the Čech complex
of a finite family is a finite product of evaluations
(`Stacks.Cohomology.CechColimit.cechComplexFunctor_comp_eval`), a finite product of evaluations
is a finite coproduct of them (`Stacks.Cohomology.CechColimit.piEvalIsoSigmaEval`, where
finiteness of the covering is used), and a coproduct of functors preserves a colimit as soon as
each summand does, because colimits in a functor category are computed pointwise and `colim` is
a left adjoint. Each summand is sections over one of the multiple intersections, which is
quasi-compact by (H2), so Stacks 009F for sheaves of modules applies to it.

Everything is at coefficient universe `u`, the universe of the space, because that is the range
of `Stacks.Cohomology.CompactSections.preservesColimitsOfShape_secF` and of
`Stacks.Cohomology.CompactBasis.cechCohomologyIsZero_of_injective`.

## References

* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 00DB](https://stacks.math.columbia.edu/tag/00DB)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis
open Stacks.CategoryTheory.CechComplex

universe v u

namespace Stacks.Cohomology.CompactColimit

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The presheaf of abelian groups underlying a sheaf of modules, functorially. -/
private noncomputable abbrev abPresheafFunctor :
    SheafOfModules.{u} R ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf.{u} R ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

variable {Idx : Type u} [SmallCategory Idx] [IsFiltered Idx]

/-- A finite product of "sections over a quasi-compact open" functors on sheaves of modules
preserves filtered colimits: the product is a coproduct, a coproduct is `colim` of the discrete
diagram, colimits in a functor category are pointwise, and each factor preserves filtered
colimits by Stacks 009F for sheaves of modules. -/
private theorem preservesColimitsOfShape_comp_piEval
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    (T : Type u) [Finite T] (V : T → Opens X) (hV : ∀ t, IsCompact (V t : Set X)) :
    PreservesColimitsOfShape Idx
      (abPresheafFunctor R ⋙ CechColimit.piEval (A := AddCommGrpCat.{u}) T V) := by
  let K : Discrete T ⥤ (Opens X)ᵒᵖ := Discrete.functor fun t => op (V t)
  let Ψ := abPresheafFunctor R ⋙
    (Functor.whiskeringLeft (Discrete T) (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj K
  have hΨ : PreservesColimitsOfShape Idx Ψ :=
    preservesColimitsOfShape_of_evaluation _ Idx fun d =>
      Stacks.Cohomology.CompactSections.preservesColimitsOfShape_secF
        (Idx := Idx) R h1 h2 (V d.as) (hV d.as)
  have hsigma : PreservesColimitsOfShape Idx
      (abPresheafFunctor R ⋙ CechColimit.sigmaEval (A := AddCommGrpCat.{u}) T V) := by
    show PreservesColimitsOfShape Idx
      (Ψ ⋙ (colim : (Discrete T ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}))
    infer_instance
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft (abPresheafFunctor R)
      (CechColimit.piEvalIsoSigmaEval (A := AddCommGrpCat.{u}) T V)).symm

/-- **The Čech complex of a filtered colimit of sheaves of modules.** For a finite family of
quasi-compact opens, on a space whose quasi-compact opens are closed under intersection, the
Čech complex of a filtered colimit is the colimit of the Čech complexes. -/
private theorem preservesColimitsOfShape_comp_cech
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    {ι : Type u} [Finite ι] (Uf : ι → Opens X) (hUf : ∀ i, IsCompact (Uf i : Set X)) :
    PreservesColimitsOfShape Idx
      (abPresheafFunctor R ⋙ cechComplexFunctor (A := AddCommGrpCat.{u}) Uf) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n => ?_
  rw [Functor.assoc, CechColimit.cechComplexFunctor_comp_eval]
  refine preservesColimitsOfShape_comp_piEval R h1 h2 _ _ fun x => ?_
  rw [inter_eq_iInf]
  exact Stacks.Cohomology.CompactBasis.isCompact_coe_iInf h2 n (fun k => Uf (x k))
    fun k => hUf (x k)

/-- **Positive-degree Čech vanishing passes to a filtered colimit.** Let `W` be a finite open
cover by quasi-compact opens of a space whose quasi-compact opens are closed under
intersection. If every member of a filtered system of sheaves of modules has vanishing
positive-degree Čech cohomology for `W`, then so does the colimit. This is Stacks 00DB applied
to the colimit of the Čech complexes. -/
theorem cechCohomologyIsZero_colimit
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    (D : Idx ⥤ SheafOfModules.{u} R) [HasColimit D]
    (W : OpenCover X) [Finite W.ι] (hW : ∀ i, IsCompact (W.obj i : Set X))
    (hz : ∀ i, ∀ n : ℕ, 0 < n → CechCohomologyIsZero R (D.obj i) W n)
    (n : ℕ) (hn : 0 < n) :
    CechCohomologyIsZero R (colimit D) W n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have := preservesColimitsOfShape_comp_cech (Idx := Idx) R h1 h2 W.obj hW
  have hc : IsColimit ((abPresheafFunctor R ⋙
      cechComplexFunctor (A := AddCommGrpCat.{u}) W.obj).mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves _ (colimit.isColimit D)
  show IsZero (((abPresheafFunctor R ⋙
    cechComplexFunctor (A := AddCommGrpCat.{u}) W.obj).obj (colimit D)).homology (m + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine CechColimit.exactAt_succ_of_isColimit hc m fun i => ?_
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hz i (m + 1) m.succ_pos

/-- **The claim inside the proof of Stacks 01FF.** On a space with a basis of quasi-compact
opens whose binary intersections are quasi-compact, the higher cohomology over a quasi-compact
open of a filtered colimit of injective sheaves of modules vanishes.

Injective sheaves of modules are flasque, so their positive-degree Čech cohomology vanishes
(Stacks 01EP and 09SZ); `cechCohomologyIsZero_colimit` carries that to the colimit; and Stacks
01EW, instantiated at the quasi-compact opens and the finite coverings by quasi-compact opens,
turns it into the vanishing of the higher cohomology. -/
theorem isZero_hgroup_colimit_of_injective
    [EnoughInjectives (SheafOfModules.{u} R)]
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    (D : Idx ⥤ SheafOfModules.{u} R) [HasColimit D] (hinj : ∀ i, Injective (D.obj i))
    (U : Opens X) (hU : IsCompact (U : Set X)) (n : ℕ) (hn : 0 < n) :
    IsZero (Hgroup R U n (colimit D)) := by
  refine Stacks.Cohomology.CompactBasis.isZero_hgroup_of_cechCohomologyIsZero.{u, v, u}
    R h1 h2 (colimit D) ?_ U hU n hn
  intro W _ hWc m hm
  refine cechCohomologyIsZero_colimit R h1 h2 D W hWc (fun i k hk => ?_) m hm
  have := hinj i
  exact Stacks.Cohomology.CompactBasis.cechCohomologyIsZero_of_injective R (D.obj i) W k hk

/-- **The claim of Stacks 01FF at the functorially embedded system.** For an arbitrary filtered
system `D` of sheaves of modules, `Stacks.Injectives.injectiveEmbedding` provides a system of
injectives `D ⋙ I` receiving `D` by a termwise monomorphism; the higher cohomology of its
colimit over a quasi-compact open vanishes. This is the form in which the dimension shift of
Stacks 01FF uses the claim. -/
theorem isZero_hgroup_colimit_injectiveEmbedding
    [EnoughInjectives (SheafOfModules.{u} R)]
    [IsGrothendieckAbelian.{u} (SheafOfModules.{u} R)]
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    (D : Idx ⥤ SheafOfModules.{u} R)
    [HasColimit (D ⋙ Stacks.Injectives.injectiveEmbedding.{u, _, _} (SheafOfModules.{u} R))]
    (U : Opens X) (hU : IsCompact (U : Set X)) (n : ℕ) (hn : 0 < n) :
    IsZero (Hgroup R U n
      (colimit (D ⋙ Stacks.Injectives.injectiveEmbedding.{u, _, _} (SheafOfModules.{u} R)))) :=
  isZero_hgroup_colimit_of_injective R h1 h2
    (D ⋙ Stacks.Injectives.injectiveEmbedding.{u, _, _} (SheafOfModules.{u} R))
    (fun i => inferInstanceAs (Injective
      ((Stacks.Injectives.injectiveEmbedding.{u, _, _} (SheafOfModules.{u} R)).obj (D.obj i))))
    U hU n hn

end Stacks.Cohomology.CompactColimit

end
