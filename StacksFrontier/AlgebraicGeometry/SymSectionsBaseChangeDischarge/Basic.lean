module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.AffineSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChange.Basic

/-!
# The base-change comparison of graded section rings, with its hypothesis discharged

`Stacks.SymSectionsBaseChange.symSectionRingBaseChangeEquiv` identifies the graded ring of
sections of `Sym(E')` over an affine open `W` of `X'` with the base change of the graded ring of
sections of `Sym(E)` over an affine open `U` of `X` containing the image of `W`. It carries one
hypothesis: a `Γ(X', W)`-linear identification

`Γ(X', W) ⊗_{Γ(X, U)} Γ(E, U) ≃ Γ(E', W)`

of the sections of `E'` with the base change of the sections of `E`. This file **proves that
identification**, so that the comparison of graded section rings holds under `E' ≅ g^*E` alone.

## Main definitions

* `Stacks.SymSectionsBaseChangeDischarge.sectionsLinearEquiv`: the sections over an open,
  transported along an isomorphism of module sheaves.
* `Stacks.SymSectionsBaseChangeDischarge.sectionsBaseChangeEquiv`: that transport composed with
  the base-change comparison `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, in the
  shape `Stacks.SymSectionsBaseChange.symSectionRingBaseChangeEquiv` asks for.

## Main results

* `Stacks.SymSectionsBaseChangeDischarge.symSectionRingBaseChangeEquivOfIso`: **the graded ring
  of sections of `Sym(E')` over `W` is the base change of the graded ring of sections of
  `Sym(E)` over `U`**, assuming only `E' ≅ g^*E`.
* `Stacks.SymSectionsBaseChangeDischarge.mem_grading_symSectionTensorEquivOfIso`: the same
  comparison is one of **graded** rings, under the same hypotheses.

## Implementation notes

**Both ingredients were already public, which is the point of this file.** The sections
comparison is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`
(`StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`), the canonical declaration of
that statement, so no change of visibility anywhere is needed. Its own two inputs are public as
well:

* `AlgebraicGeometry.affineSectionsLinearEquiv`
  (`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/AffineSections.lean:92`) is public —
  `Γ(F.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(F, U)` — and is the canonical declaration of that
  statement.
* `AlgebraicGeometry.quasicoherentPullbackSectionsIso`
  (`StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`) is the spectrum-level
  comparison `S ⊗_R Γ(G, ⊤) ≅ Γ((Spec φ)^*G, ⊤)`;
  `Stacks.AlgebraicGeometry.AffineBaseChangeIso.pullbackΓIso`
  (`StacksFrontier/AlgebraicGeometry/AffineBaseChangeIso/AffineSections.lean:103`) is a second
  public declaration of the same statement.

So the route taken here is: restrict `F` along `hU.fromSpec`, compare over the two spectra,
transport along `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`, and come back down with
`affineSectionsLinearEquiv` at `V` — all of which
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` already does, normalised on `1 ⊗ a` by
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`.

**The module structures line up without a bridge.** `ModuleCat.extendScalars α` has carrier
`S ⊗[R] M` for the `R`-module structure `ModuleCat.restrictScalars α` puts on `S`, while
`Stacks.SymSectionsBaseChange.baseAlgebra` is `(g.appLE U W hWU).hom.toAlgebra`. Those agree on
the nose here, so `sectionsBaseChangeEquiv` is accepted as the `hsec` argument with no
transport — which is not automatic for this vocabulary, as the implementation notes of
`StacksDraft.AlgebraicGeometry.F3.SymSectionsBaseChange.SectionRing` record for the section ring.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Not done here

**No tag of Tag 0B3V is attached and none is earned.** Every result here carries the affineness
hypotheses `hU`, `hW` and `hWU`, which are chart-level data that Tag 0B3V's sixth label does not
mention, so the covering-set rule withholds the tag.

What this closes is the **first** of the two residues that
`Stacks.ProjBundleBaseChangeReduction` records against that label. The residue it does *not*
touch is the structural one: `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily` demands
a chart over *every* affine open of `X'`, while the comparison here exists only for a `W` inside
`g ⁻¹ᵁ U` for an affine `U` of `X` — a basis of `X'`, not all of its affine opens. There
is no restriction, pullback or comap operation on
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` anywhere in either tree, so the
per-open escape is still unavailable.

Nor does this file take the comparison to the level of `Proj`. The remaining step there is the
transport between `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.grading`, valued in
`AddSubgroup`, and the `Submodule`-valued grading that
`Stacks.AlgebraicGeometry.ProjChartBaseChange.isPullback_map_toSpecZero` is stated over.
-/
@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace Stacks.SymSectionsBaseChangeDischarge

universe u

/-- **The sections over an open, transported along an isomorphism of module sheaves.** An
isomorphism `F ≅ G` of `𝒪_X`-modules induces a `Γ(X, W)`-linear equivalence on sections over any
open `W`, by `AlgebraicGeometry.Scheme.Modules.Hom.app` and its linearity. -/
def sectionsLinearEquiv {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (W : X.Opens) :
    Γ(F, W) ≃ₗ[Γ(X, W)] Γ(G, W) where
  toFun := fun x => e.hom.app W x
  map_add' x y := by simp
  map_smul' r x := Scheme.Modules.Hom.app_smul e.hom r x
  invFun := fun x => e.inv.app W x
  left_inv x := by
    have h : (e.hom ≫ e.inv).app W = (𝟙 F :).app W := by rw [e.hom_inv_id]
    exact congr($(h) x)
  right_inv x := by
    have h : (e.inv ≫ e.hom).app W = (𝟙 G :).app W := by rw [e.inv_hom_id]
    exact congr($(h) x)

/-- **The sections of `E'` over `W` are the base change of the sections of `E` over `U`.** This
is the hypothesis `Stacks.SymSectionsBaseChange.symSectionRingBaseChangeEquiv` asks for, in its
exact shape: the tensor product is taken over the algebra structure
`Stacks.SymSectionsBaseChange.baseAlgebra` that file fixes. -/
def sectionsBaseChangeEquiv
    {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
    (E' : X'.Modules) (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    {U : X.Opens} (hU : IsAffineOpen U) {W : X'.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ g ⁻¹ᵁ U) :
    letI := Stacks.SymSectionsBaseChange.baseAlgebra g hWU
    (Γ(X', W) ⊗[Γ(X, U)] Γ(E, U)) ≃ₗ[Γ(X', W)] Γ(E', W) :=
  letI := Stacks.SymSectionsBaseChange.baseAlgebra g hWU
  (affinePullbackSectionsBaseChangeIso g E hU hW hWU).toLinearEquiv.trans
    (sectionsLinearEquiv hE.symm W)

/-- **The graded ring of sections of `Sym(E')` over `W` is the base change of the graded ring of
sections of `Sym(E)` over `U`, with no hypothesis beyond `E' ≅ g^*E`.** -/
def symSectionRingBaseChangeEquivOfIso
    {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
    (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
    (E' : X'.Modules) [E'.IsQuasicoherent]
    (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E')
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    {U : X.Opens} (hU : IsAffineOpen U) {W : X'.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ g ⁻¹ᵁ U) :
    letI := Stacks.SymSectionsBaseChange.baseAlgebra g hWU
    letI := Stacks.SymGraded.AffinePieces.sectionAlgebra E hqc (V := U)
    letI := Stacks.SymGraded.AffinePieces.sectionAlgebra E' hqc' (V := W)
    (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').sectionRing W ≃ₐ[Γ(X', W)]
      (Γ(X', W) ⊗[Γ(X, U)]
        (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionRing U) :=
  Stacks.SymSectionsBaseChange.symSectionRingBaseChangeEquiv g hWU E hqc E' hqc' hU hW
    (sectionsBaseChangeEquiv g E E' hE hU hW hWU)

/-- **The isomorphism is one of graded rings**, with no hypothesis beyond `E' ≅ g^*E`. -/
theorem mem_grading_symSectionTensorEquivOfIso
    {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
    (E' : X'.Modules) [E'.IsQuasicoherent]
    (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E')
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    {U : X.Opens} (hU : IsAffineOpen U) {W : X'.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ)
    (x : (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').sectionRing W) :
    letI := Stacks.SymSectionsBaseChange.baseAlgebra g hWU
    x ∈ (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').grading W n ↔
      Stacks.SymSectionsBaseChange.symSectionTensorEquiv g hWU E E' hqc' hW
          (sectionsBaseChangeEquiv g E E' hE hU hW hWU) x ∈
        Submodule.baseChange Γ(X', W) (SymPow.symmetricPower n Γ(X, U) Γ(E, U)) :=
  Stacks.SymSectionsBaseChange.symSectionTensorEquiv_grading g hWU E E' hqc' hW
    (sectionsBaseChangeEquiv g E E' hE hU hW hWU) n x

end Stacks.SymSectionsBaseChangeDischarge

end
