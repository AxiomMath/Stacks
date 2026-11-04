module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# Global functions on a limit of algebraic spaces

Stacks 07SI says that, in Situation 084R, `Γ(X, ℱ) = colim_{i ≥ 0} Γ(Xᵢ, ℱᵢ)` for
`ℱᵢ = f_{0i}^*ℱ₀` and `ℱ = f_0^*ℱ₀`, with `ℱ₀` quasi-coherent on `X₀`. This file proves the
case `ℱ₀ = 𝒪_{X₀}`:

`Γ(X, 𝒪_X) = colim_i Γ(Xᵢ, 𝒪_{Xᵢ})`,

along the pullback maps of global functions. Stacks 07SQ uses exactly this case: in its proof
`A = Γ(X, 𝒪_X)` is written as the colimit of the `Aᵢ = Γ(Xᵢ, 𝒪_{Xᵢ})`.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_affineLineToBase`: the affine line
  over `S`, as an algebraic space, is locally of finite presentation over `S`.
* `AlgebraicGeometry.Space.isStagesColimit_globalFunctions_of_isLimit`: for a directed inverse
  system of quasi-compact and quasi-separated algebraic spaces with affine transition morphisms,
  whose index set has cardinality below the cofinality of the size cutoff of the site, and
  whose limit is an algebraic space, the ring of global functions of the limit is the filtered
  colimit of the rings of global functions of the stages.
* `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_globalFunctions` and
  `AlgebraicGeometry.Space.LimitSituation.isStagesColimit_globalFunctions`: the same result for
  a descent situation (Stacks 09RH) and for a limit situation (Situation 084R).

## Implementation notes

*The proof does not go through the source's equalizer presentation.* A global function on an
algebraic space is a morphism to the affine line `𝔸¹_S`, naturally in the space
(`AlgebraicGeometry.Space.globalFunctionsHomEquiv` and
`AlgebraicGeometry.Space.globalFunctionsHomEquiv_natural`). So the statement is that
`Mor(X, 𝔸¹_S) = colim Mor(Xᵢ, 𝔸¹_S)`. The affine line is locally of finite presentation over
`S`, so this is Stacks 0CP4 for `𝔸¹_S ⟶ S`, whose two halves are
`AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving` (every function on the
limit comes from a stage) and
`AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving` (two functions on a
stage that agree on the limit agree on a later stage). Going this way avoids the coherence of
the inverse-image comparison isomorphisms that the module-level formulation
`AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit` needs. Moreover the transition maps
here are `AlgebraicGeometry.Space.globalFunctionsMap`, which is a ring homomorphism and is
strictly functorial (`AlgebraicGeometry.Space.globalFunctionsMap_comp`).

*The index-size hypothesis.* The results assume `#I < B.cutoff.ord.cof`. This is the hypothesis
under which Stacks 07SF holds in this library, and the statement is false without it. Take for
`I` the ordinals below the cutoff `κ`, let `K_α` be the field of rational functions over `ℚ` in
variables indexed by `α`, and set `X_α = Spec K_α`. Every stage lies in the site. But a
compatible family of points of the stages with values in a nonempty scheme `T` of the site would
embed the field `⋃ K_α`, which has cardinality `κ`, into a residue field of `T`, and every
residue field of `T` has cardinality below `κ`. So the limit presheaf is that of the empty
scheme, whose ring of global functions is zero, while the colimit of the `K_α` is not zero. The
source fixes a site large enough for its constructions, and the hypothesis is the explicit form
of that convention here.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The affine line is locally of finite presentation -/

/-- The structure morphism `𝔸¹_S ⟶ S` of the affine line, as a morphism of the big fppf site
over `S`. -/
noncomputable def affineLineToBase :
    affineLineBigFppfOver B S hS ⟶ baseTerminal B S hS :=
  Over.homMk (affineLineBigFppfOver B S hS).hom (Category.comp_id _)

/-- **The affine line over `S` is locally of finite presentation over `S`**, as a morphism of
algebraic spaces. The underlying morphism of schemes is the projection `𝔸¹_S ⟶ S`, which is
locally of finite presentation, and being locally of finite presentation is étale local on the
source and target (Stacks 04R3), so it holds on every étale chart. -/
theorem isLocallyOfFinitePresentation_affineLineToBase :
    IsLocallyOfFinitePresentation B S hS (yoneda.map (affineLineToBase B S hS)) :=
  holdsOnEveryEtaleChart_yoneda_map B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _
    (inferInstanceAs (LocallyOfFinitePresentation (AffineSpace PUnit.{u + 1} S ↘ S)))

/-! ### Global functions on the limit of an inverse system -/

section Generic

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
  (hI : #I < B.cutoff.ord.cof)
  (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
  (hDqc : ∀ i : I, IsQuasiCompactSpace B S hS (D.obj (op i)))
  (hDqs : ∀ i : I, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i)))
  (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
  (hc' : IsAlgebraicSpace B S hS c.pt)

include hc hI hDqc hDqs hDaff in
/-- **Stacks 07SI for the structure sheaf.** Let `D` be an inverse system, over a directed set
`I`, of quasi-compact and quasi-separated algebraic spaces over `S` with affine transition
morphisms, and let `c` be a limit cone of `D` whose vertex is an algebraic space. Suppose that
`I` has cardinality below the cofinality of the size cutoff of the site. Then the ring of
global functions of the limit is the filtered colimit of the rings of global functions of the
stages:

`Γ(lim Dᵢ, 𝒪) = colim_i Γ(Dᵢ, 𝒪)`,

along the pullbacks of global functions by the transition morphisms and by the projections,
in the elementwise form `Stacks.IsStagesColimit`.

Global functions are morphisms to the affine line, which is locally of finite presentation over
`S`. So the second and third clauses are the two halves of Stacks 0CP4 for `𝔸¹_S ⟶ S`, and the
first clause is the functoriality of the pullback of global functions. See the implementation
notes for why the size hypothesis cannot be dropped. -/
theorem isStagesColimit_globalFunctions_of_isLimit :
    Stacks.IsStagesColimit (G := fun i : I => globalFunctions' B S hS (D.obj (op i)))
      (T := globalFunctions' B S hS c.pt)
      (fun i j h x => globalFunctionsMap B S hS (U := ⟨D.obj (op i), hDalg i⟩)
        (V := ⟨D.obj (op j), hDalg j⟩) (ObjectProperty.homMk (D.map (homOfLE h).op)) x)
      (fun i x => globalFunctionsMap B S hS (U := ⟨D.obj (op i), hDalg i⟩)
        (V := ⟨c.pt, hc'⟩) (ObjectProperty.homMk (c.π.app (op i))) x) := by
  have hSize : #Iᵒᵖ < B.cutoff.ord.cof :=
    (Cardinal.mk_congr Opposite.equivToOpposite.symm).trans_lt hI
  have hHom : ∀ i j : Iᵒᵖ, #(i ⟶ j) < B.cutoff.ord.cof := fun i j =>
    (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)
  have hT := baseTerminal_yonedaIsTerminal B S hS
  have hφ := isLocallyOfFinitePresentation_affineLineToBase B S hS
  refine ⟨fun i j h x => ?_, fun t => ?_, fun i s s' hss => ?_⟩
  · rw [← RingHom.comp_apply, ← globalFunctionsMap_comp]
    congr 2
    exact ObjectProperty.hom_ext _ (c.w (homOfLE h).op)
  · let g := globalFunctionsHomEquiv B S hS ⟨c.pt, hc'⟩ t
    let i₀ : I := Classical.arbitrary I
    obtain ⟨j, t', k, a, -, hlim, -⟩ :=
      exists_stage_map_of_relativelyLimitPreserving B S hS hZ D c hc hSize hHom
        (fun i => hDalg i.unop) (fun i => hDqc i.unop) (fun i => hDqs i.unop) hDaff hc'
        (affineLineSpace B S hS).property (terminalSpace B S hS).property
        (yoneda.map (affineLineToBase B S hS)) hφ
        g.hom (op i₀) (hT.from _) (hT.hom_ext _ _)
    refine ⟨k.unop, (globalFunctionsHomEquiv B S hS ⟨D.obj k, hDalg k.unop⟩).symm
      (ObjectProperty.homMk (D.map a ≫ t')), ?_⟩
    apply (globalFunctionsHomEquiv B S hS ⟨c.pt, hc'⟩).injective
    rw [globalFunctionsHomEquiv_natural, Equiv.apply_symm_apply]
    exact ObjectProperty.hom_ext _ hlim
  · have hlim :
        c.π.app (op i) ≫ (globalFunctionsHomEquiv B S hS ⟨D.obj (op i), hDalg i⟩ s).hom =
          c.π.app (op i) ≫ (globalFunctionsHomEquiv B S hS ⟨D.obj (op i), hDalg i⟩ s').hom := by
      have h := fun s => globalFunctionsHomEquiv_natural B S hS (U := ⟨D.obj (op i), hDalg i⟩)
        (V := ⟨c.pt, hc'⟩) (ObjectProperty.homMk (c.π.app (op i))) s
      exact congrArg (fun f => f.hom)
        ((h s).symm.trans
          ((congrArg (globalFunctionsHomEquiv B S hS ⟨c.pt, hc'⟩) hss).trans (h s')))
    obtain ⟨k, a, hk⟩ :=
      exists_stage_eq_of_relativelyLimitPreserving B S hS hZ D c hc hSize hHom
        (fun i => hDalg i.unop) (fun i => hDqc i.unop) (fun i => hDqs i.unop) hDaff hc'
        (affineLineSpace B S hS).property (terminalSpace B S hS).property
        (yoneda.map (affineLineToBase B S hS)) hφ
        (op i) _ _ hlim (hT.hom_ext _ _)
    refine ⟨k.unop, leOfHom a.unop, ?_⟩
    apply (globalFunctionsHomEquiv B S hS ⟨D.obj k, hDalg k.unop⟩).injective
    rw [globalFunctionsHomEquiv_natural, globalFunctionsHomEquiv_natural]
    refine ObjectProperty.hom_ext _ ?_
    have ha : (homOfLE (leOfHom a.unop)).op = a := Subsingleton.elim _ _
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, ha]
    exact hk

end Generic

/-! ### Descent situations and limit situations -/

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **Stacks 07SI for the structure sheaf, in a descent situation.** In a descent situation
(Stacks 09RH) whose index set has cardinality below the cofinality of the size cutoff of the
site, the ring of global functions of the limit is the filtered colimit of the rings of global
functions of the stages, along the pullbacks by the transition morphisms and the projections.

This is `AlgebraicGeometry.Space.isStagesColimit_globalFunctions_of_isLimit` for the system,
the limit cone and the fields of the descent situation. -/
theorem isStagesColimit_globalFunctions (hI : #I < B.cutoff.ord.cof) :
    Stacks.IsStagesColimit (G := fun i : I => globalFunctions' B S hS (D.system.obj (op i)))
      (T := globalFunctions' B S hS D.limitCone.pt)
      (fun i j h x => globalFunctionsMap B S hS (U := ⟨D.system.obj (op i), D.algebraicSpace i⟩)
        (V := ⟨D.system.obj (op j), D.algebraicSpace j⟩)
        (ObjectProperty.homMk (D.system.map (homOfLE h).op)) x)
      (fun i x => globalFunctionsMap B S hS (U := ⟨D.system.obj (op i), D.algebraicSpace i⟩)
        (V := ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩)
        (ObjectProperty.homMk (D.limitCone.π.app (op i))) x) :=
  have : Nonempty I := ⟨D.base⟩
  isStagesColimit_globalFunctions_of_isLimit B S hS hZ D.system D.limitCone D.isLimit hI
    D.algebraicSpace D.quasiCompact D.quasiSeparated D.transition_affine D.limitAlgebraicSpace

end DescentSituation

namespace LimitSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)

/-- **Stacks 07SI for the structure sheaf, in Situation 084R.** In a limit situation whose
index set has cardinality below the cofinality of the size cutoff of the site, and whose limit
`X` is an algebraic space, the ring of global functions of `X` is the filtered colimit of the
rings of global functions of the stages, along the pullbacks by the transition morphisms
`AlgebraicGeometry.Space.LimitSituation.transition` and the projections
`AlgebraicGeometry.Space.LimitSituation.projection`.

The hypothesis `hX` is not an extra assumption in the presence of `hI`: it is Stacks 07SF. -/
theorem isStagesColimit_globalFunctions (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) :
    Stacks.IsStagesColimit (G := fun i : A.I => globalFunctions' B S hS (A.stage i).obj)
      (T := globalFunctions' B S hS (A.limitSpace hX).obj)
      (fun _ _ h x => globalFunctionsMap B S hS (A.transition h) x)
      (fun i x => globalFunctionsMap B S hS (A.projection hX i) x) :=
  isStagesColimit_globalFunctions_of_isLimit B S hS hZ A.system A.cone A.isLimitCone hI
    A.isAlgebraicSpace A.quasiCompact A.quasiSeparated A.transition_affine hX

end LimitSituation

end AlgebraicGeometry.Space

end
