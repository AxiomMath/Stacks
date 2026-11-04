module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The scheme-theoretic support on an étale scheme chart, and the support of the module on it

Let `X` be an algebraic space over a scheme `S` and let `F` be a finite type quasi-coherent
`𝒪_X`-module with scheme-theoretic support `i : Z → X`, Stacks 07U1.  The two chart-level
clauses of **Stacks 07U0** are proved here.

Part (1) says that for a scheme `U` and an étale morphism `φ : U → X` the fibre product
`Z ×_X U` is the scheme-theoretic support of `φ^*F`.  An étale morphism of algebraic spaces is
flat, Stacks 0467, so this is Stacks 089C — the scheme-theoretic support commutes with a flat
pullback — read at `φ`, with the source taken to be the algebraic space of the scheme `U`.

Part (4) says that `F` and the module `G` on `Z` both have support `|Z|`.  The half about `F`
is `AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport`.  The
half about `G` is deduced from it here: the support of a direct image along a closed immersion
is the image of the support, so `|i|(Supp G) = Supp(i_*G) = Supp F = |i|(|Z|)`, and `|i|` is
injective.

## Main results

* `AlgebraicGeometry.Space.schemeTheoreticSupport_modulePullback_schemeSpace_of_isEtale`:
  **Stacks 07U0, part (1).**
* `AlgebraicGeometry.Space.supportOfSheaf_module_on_schemeTheoreticSupport_eq_univ`:
  **Stacks 07U0, part (4)**, for the module on the scheme-theoretic support.

## Implementation notes

Part (1) is stated for a scheme `U` of the big fppf site read as an algebraic space by
`AlgebraicGeometry.schemeSpace`, and for an arbitrary étale morphism `φ` from it, which is the
source's "scheme `U` with an étale morphism `φ : U → X`"; the fibre product `Z ×_X U` is the
inverse image subfunctor `CategoryTheory.Subfunctor.preimage`, which is what the cartesian
square `CategoryTheory.Subfunctor.isPullback_preimage` makes it.

Finite type appears in the two forms the inputs consume, as it does throughout this part of the
library: the sectionwise `CategoryTheory.PresheafOfModules.IsFiniteType` of Stacks 03DL(5),
which the construction of the closed subspace cut out by the annihilator ideal uses, and the
categorical `SheafOfModules.IsFiniteTypeOnSite`, which the support statements use.  Part (1)
takes the first and part (4) the second.

Part (4) takes the closed subspace, the module on it and the identification of its direct image
with `F` as data, as parts (2) and (3) of the same lemma already do in
`AlgebraicGeometry.Space.module_on_closedSubspace_unique` and
`AlgebraicGeometry.Space.isFiniteTypeOnSite_module_on_closedSubspace`; the extra hypothesis that
the closed subspace is the scheme-theoretic support is what distinguishes part (4) from them,
since the module on a larger closed subspace does not have full support.  Finite type of that
module is not assumed: it is part (3).

## References

* [Stacks Project, Lemma 67.15.3 (Tag 07U0)](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Definition 67.15.4 (Tag 07U1)](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Lemma 67.30.10 (Tag 089C)](https://stacks.math.columbia.edu/tag/089C)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Part (1): the scheme-theoretic support on an étale scheme chart -/

/-- **Stacks 07U0, part (1).**  Let `F` be a finite type quasi-coherent `𝒪_X`-module with
scheme-theoretic support `Z ⊆ X`, let `U` be a scheme over `S` and let `φ : U → X` be an étale
morphism.  Then the fibre product `Z ×_X U` is the scheme-theoretic support of `φ^*F`.

An étale morphism of algebraic spaces is flat (Stacks 0467,
`AlgebraicGeometry.Space.isFlat_of_isEtale`), so this is Stacks 089C,
`AlgebraicGeometry.Space.schemeTheoreticSupport_modulePullback`, at `φ`. -/
@[stacks 07U0 "part (1): on a scheme étale over X the scheme-theoretic support of the inverse \
image of F is the inverse image of the scheme-theoretic support of F"]
theorem schemeTheoreticSupport_modulePullback_schemeSpace_of_isEtale
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X.1 X.2).J F.val)
    (U : BigFppfOver B S hS) (φ : schemeSpace U ⟶ X) (hφ : IsEtale B S hS φ.hom) :
    schemeTheoreticSupport B S hS (schemeSpace U) ((modulePullback B S hS φ).obj F) =
      (schemeTheoreticSupport B S hS X F).preimage φ.hom :=
  schemeTheoreticSupport_modulePullback B S hS (isFlat_of_isEtale B S hS hφ) F hF hft

/-! ### Part (4): the module on the scheme-theoretic support has full support -/

/-- **Stacks 07U0, part (4), for the module on the scheme-theoretic support.**  Let `F` be a
finite type quasi-coherent `𝒪_X`-module, let `Z ⊆ X` be its scheme-theoretic support and let
`G` be an `𝒪_Z`-module whose direct image along the inclusion is `F`.  Then the support of `G`
is all of `|Z|`.

`G` is of finite type by part (3), so the support of its direct image is the image of its
support under the injective map on points of a closed immersion; that direct image is `F`,
whose support is `|Z|` by the other half of part (4),
`AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport`. -/
@[stacks 07U0 "part (4): the module on the scheme-theoretic support has support all of it"]
theorem supportOfSheaf_module_on_schemeTheoreticSupport_eq_univ
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) (Z : ClosedSubspaces B S hS X.1)
    (hZeq : Z.1 = schemeTheoreticSupport B S hS X F)
    (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).obj G ≅ F) :
    supportOfSheaf B S hS (closedSubspaceToSpace B S hS X Z).1
      ((SheafOfModules.toSheaf _).obj G) = Set.univ := by
  have _ : SheafOfModules.IsFiniteTypeOnSite G :=
    isFiniteTypeOnSite_module_on_closedSubspace B S hS X F hFft Z G e
  have hpush := supportOfSheaf_modulePushforward_eq_image_of_isFiniteTypeOnSite B S hS
    (closedSubspaceInclusion B S hS X Z) Z.2.2 G
  have h4a : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) =
      Set.range (pointsMap B S hS (closedSubspaceToSpace B S hS X Z).1
        (closedSubspaceInclusion B S hS X Z).hom) := by
    rw [supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F hF hFft, ← hZeq]
    rfl
  have hinj := pointsMap_hom_injective_of_isClosedImmersion B S hS
    (closedSubspaceInclusion B S hS X Z) Z.2.2
  refine Set.eq_univ_of_forall fun x => ?_
  have hmem : pointsMap B S hS (closedSubspaceToSpace B S hS X Z).1
        (closedSubspaceInclusion B S hS X Z).hom x ∈
      Set.range (pointsMap B S hS (closedSubspaceToSpace B S hS X Z).1
        (closedSubspaceInclusion B S hS X Z).hom) := ⟨x, rfl⟩
  rw [← h4a, ← supportOfSheaf_eq_of_iso B S hS X e, hpush] at hmem
  obtain ⟨y, hy, hxy⟩ := hmem
  exact hinj hxy ▸ hy

end AlgebraicGeometry.Space

end
