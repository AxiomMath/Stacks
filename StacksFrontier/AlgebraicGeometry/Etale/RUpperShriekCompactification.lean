module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleAdjunction

import StacksCore.Tactic.StacksAttribute

/-!
# For a quasi-finite separated morphism the two derived upper shrieks agree

Let `f : X ⟶ Y` be a separated quasi-finite morphism of quasi-compact and quasi-separated
schemes and let `Λ` be a ring. There are two functors `D(Y_étale, Λ) ⥤ D(X_étale, Λ)` called
`Rf^!`:

* the right adjoint of the derived lower shriek `Rf_! = Rf̄_* ∘ j_!` of a compactification
  `f = f̄ ∘ j`, [Stacks, Tag 0G2C];
* the total right derived functor of the upper shriek `f^!` of [Stacks, Tag 0F59], which is
  right adjoint to `f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` by [Stacks, Tag 0F5N].

They are the same functor, [Stacks, Tag 0GL8]. The proof of the source is uniqueness of
adjoints, as `Rf_! = f_!` by [Stacks, Tag 0GKM].

## Main results

All in the namespace `AlgebraicGeometry.SmallEtale`.

* `compactificationDerivedLowerShriekIso` — for a compactification `f = f̄ ∘ j` with `j` an
  open immersion and `f̄` finite, and for *any* total right derived functor `Rf̄_*` of `f̄_*`,
  the composite `Rf̄_* ∘ j_!` is isomorphic to the functor induced by `f_!`
  ([Stacks, Tag 0GKM], with the model of `Rf̄_*` left free).
* `compactificationRUpperShriekAdjunction` — the adjunction `Rf̄_* ∘ j_! ⊣ Rf^!`, with `Rf^!`
  the derived upper shriek of [Stacks, Tag 0F5N].
* `isLeftAdjoint_compactificationDerivedLowerShriek` — so `Rf_!` has a right adjoint, and
  `compactificationRightAdjointIso` and `rightAdjointIsoModuleRUpperShriekFunctor`: every right
  adjoint of `Rf_!`, in particular `Functor.rightAdjoint Rf_!`, is isomorphic to `Rf^!`.
* `exists_compactification_rightAdjointIso_moduleRUpperShriekFunctor` — the case of
  [Stacks, Tag 0GL8] for *one* compactification: for `f` separated and quasi-finite with
  quasi-compact quasi-separated target, `f` has a compactification `f = f̄ ∘ j` with `f̄` finite
  (Zariski's main theorem), the functor `Rf_! = Rf̄_* ∘ j_!` of it is a left adjoint, and every
  right adjoint of it is isomorphic to the `Rf^!` of [Stacks, Tag 0F5N]. The statement of the
  tag, for *every* compactification and the functor `Rf^!` of [Stacks, Tag 0G2C] on Mathlib's
  small étale sites, is
  `AlgebraicGeometry.SmallEtale.derivedUpperShriekUnboundedIsoModuleRUpperShriekFunctor` in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.QuasiFiniteComparison`.

## Implementation notes

*What "the functor of Lemma 0G2C" is.* The `Rf^!` of [Stacks, Tag 0G2C] is defined as a right
adjoint of `Rf_! = Rf̄_* ∘ j_!`. A right adjoint is determined up to unique isomorphism, so the
assertion of the source is stated for an *arbitrary* right adjoint `G` of `Rf_!`, given with
its adjunction; `CategoryTheory.Functor.rightAdjoint` of `Rf_!` is the instance
`rightAdjointIsoModuleRUpperShriekFunctor`. In the quasi-finite case the existence of the right
adjoint is proved here directly, from `Rf_! ≅ f_!` and [Stacks, Tag 0F5N], rather than by
Brown representability.

*The model of `Rf̄_*`.* `Rf̄_*` enters as an arbitrary total right derived functor of the
direct image `f̄_*` of sheaves of `Λ`-modules, at the quasi-isomorphisms of the homotopy
category. Since `f̄` is finite, `f̄_*` is exact, so the functor it induces on derived categories
is one such derived functor (`Stacks 03QP`), and any two are canonically isomorphic. The
extension by zero `j_!` is exact and needs no deriving; it is read, as in
[Stacks, Tag 0GKM], as the direct image with compact support along the open immersion `j`,
which is extension by zero by [Stacks, Tag 0F6Q].

*Hypotheses.* They are the source's: `f` separated and quasi-finite — [Stacks, Tag 02NG],
that is `LocallyQuasiFinite`, `LocallyOfFiniteType` and `QuasiCompact` together — and `Y`
quasi-compact and quasi-separated. Quasi-compactness and quasi-separatedness of `X` follow and
are not needed. The torsion hypothesis on `Λ` is not needed either: in the source it serves to
construct `Rf_!` and its right adjoint for a general separated finite type morphism, which in
the quasi-finite case are both available for every ring. The derived categories are arbitrary
`CategoryTheory.HasDerivedCategory.{w}` models, the one on `X̄` universally quantified as it
cannot be fixed before the compactification is produced.

## References

* [Stacks Project, Tag 0GL8](https://stacks.math.columbia.edu/tag/0GL8)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

section Compactification

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Xbar Y : B.Scheme}
  (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Xbar Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
  (RFbar : DerivedCategory (ModuleSheaf.{u, u, u} B Xbar Λ) ⥤
    DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
  (α : (etalePushforwardMod B Λ fbar).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RFbar)
  [RFbar.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Xbar Λ) (ComplexShape.up ℤ))]

/-- A total right derived functor `Rf̄_*` of the direct image along a finite morphism is the
functor induced on derived categories by `f̄_*`, which is exact. -/
def rightDerivedIsoMapDerivedCategoryOfIsFinite :
    RFbar ≅ (etalePushforwardMod B Λ fbar).mapDerivedCategory :=
  haveI := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact
    (etalePushforwardMod B Λ fbar)
  Functor.rightDerivedNatIso RFbar (etalePushforwardMod B Λ fbar).mapDerivedCategory α
    (etalePushforwardMod B Λ fbar).mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Xbar Λ) (ComplexShape.up ℤ))
    (Iso.refl _)

/-- **[Stacks, Tag 0GKM]** with the model of `Rf̄_*` left free: for a compactification
`f = f̄ ∘ j` with `j` an open immersion and `f̄` finite, the derived lower shriek
`Rf_! = Rf̄_* ∘ j_!` is isomorphic to the functor `f_!` of [Stacks, Tag 0F5N] on
`D(X_étale, Λ) ⥤ D(Y_étale, Λ)`, for every total right derived functor `Rf̄_*` of `f̄_*`. -/
def compactificationDerivedLowerShriekIso :
    moduleFShriekDerivedFunctor.{u, u, w, u} B Λ (j ≫ fbar) (fShriekMod.{u, u, u} B Λ (j ≫ fbar))
        (fShriekModForgetIso.{u, u, u} B Λ (j ≫ fbar)) ≅
      (fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar :=
  derivedLowerShriekModIsoOfOpenImmersion.{w} B Λ j fbar ≪≫
    Functor.isoWhiskerLeft _
      (rightDerivedIsoMapDerivedCategoryOfIsFinite.{w} B Λ fbar RFbar α).symm

/-- The adjunction `Rf_! ⊣ Rf^!` for the derived lower shriek `Rf_! = Rf̄_* ∘ j_!` of a
compactification with `f̄` finite, where `Rf^!` is the derived upper shriek of
[Stacks, Tag 0F5N]: the adjunction `f_! ⊣ Rf^!` transported along `Rf_! ≅ f_!`. -/
def compactificationRUpperShriekAdjunction :
    (fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar ⊣
      moduleRUpperShriekFunctor.{u, u, w, u} B Λ (j ≫ fbar) :=
  (moduleFShriekRUpperShriekAdjunction.{u, u, w, u} B Λ (j ≫ fbar)).ofNatIsoLeft
    (compactificationDerivedLowerShriekIso.{w} B Λ j fbar RFbar α)

include α in
/-- The derived lower shriek `Rf_! = Rf̄_* ∘ j_!` of a compactification with `f̄` finite has a
right adjoint, the case of [Stacks, Tag 0G2C] for a quasi-finite morphism. -/
theorem isLeftAdjoint_compactificationDerivedLowerShriek :
    ((fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar).IsLeftAdjoint :=
  (compactificationRUpperShriekAdjunction.{w} B Λ j fbar RFbar α).isLeftAdjoint

/-- Every right adjoint `G` of the derived lower shriek `Rf_! = Rf̄_* ∘ j_!` of a
compactification with `f̄` finite is isomorphic to the derived upper shriek `Rf^!` of
[Stacks, Tag 0F5N], by uniqueness of adjoints. -/
def compactificationRightAdjointIso
    (G : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B X Λ))
    (adj : (fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar ⊣ G) :
    G ≅ moduleRUpperShriekFunctor.{u, u, w, u} B Λ (j ≫ fbar) :=
  adj.rightAdjointUniq (compactificationRUpperShriekAdjunction.{w} B Λ j fbar RFbar α)

/-- The right adjoint `Functor.rightAdjoint Rf_!` of the derived lower shriek
`Rf_! = Rf̄_* ∘ j_!` of a compactification with `f̄` finite — the `Rf^!` of
[Stacks, Tag 0G2C] — is isomorphic to the derived upper shriek `Rf^!` of [Stacks, Tag 0F5N]. -/
def rightAdjointIsoModuleRUpperShriekFunctor :
    letI := isLeftAdjoint_compactificationDerivedLowerShriek.{w} B Λ j fbar RFbar α
    ((fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar).rightAdjoint ≅
      moduleRUpperShriekFunctor.{u, u, w, u} B Λ (j ≫ fbar) :=
  letI := isLeftAdjoint_compactificationDerivedLowerShriek.{w} B Λ j fbar RFbar α
  compactificationRightAdjointIso.{w} B Λ j fbar RFbar α _ (Adjunction.ofIsLeftAdjoint _)

end Compactification

/-- The case of [Stacks, Tag 0GL8] for one compactification, with finite `f̄`. Let `f : X ⟶ Y`
be a separated quasi-finite morphism of a big étale site with `Y` quasi-compact and
quasi-separated, and let `Λ` be a ring. Then `f` factors as an open immersion `j : X ⟶ X̄`
followed by a finite morphism `f̄ : X̄ ⟶ Y` (Zariski's main theorem, [Stacks, Tag 05K0]), and
for every model of `D(X̄_étale, Λ)` and every total right
derived functor `Rf̄_*` of `f̄_*`, the derived lower shriek `Rf_! = Rf̄_* ∘ j_!` of
[Stacks, Tag 0G2C] has a right adjoint, and every right adjoint `Rf^!` of it is isomorphic to
the derived upper shriek `Rf^! : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` of [Stacks, Tag 0F5N].

Quasi-finiteness is [Stacks, Tag 02NG]: locally quasi-finite, locally of finite type and
quasi-compact together. The compactification is produced, not assumed.

This says that *some* compactification works. [Stacks, Tag 0GL8] itself, for an arbitrary
compactification (made canonical by [Stacks, Tag 0F7I]) and the functor `Rf^!` of
[Stacks, Tag 0G2C] on Mathlib's small étale sites, is
`AlgebraicGeometry.SmallEtale.derivedUpperShriekUnboundedIsoModuleRUpperShriekFunctor`. -/
@[ega "IV 18.12.13" "special case"]
theorem exists_compactification_rightAdjointIso_moduleRUpperShriekFunctor
    (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
    [IsSeparated (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
    [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)] :
    ∃ (Xbar : B.Scheme) (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
      (_ : IsOpenImmersion (B.inclusion.map j)) (_ : IsFinite (B.inclusion.map fbar)),
      f = j ≫ fbar ∧
      ∀ [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Xbar Λ)]
        (RFbar : DerivedCategory (ModuleSheaf.{u, u, u} B Xbar Λ) ⥤
          DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
        (α : (etalePushforwardMod B Λ fbar).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RFbar),
        RFbar.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Xbar Λ) (ComplexShape.up ℤ)) →
        ((fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar).IsLeftAdjoint ∧
        ∀ (G : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
            DerivedCategory (ModuleSheaf.{u, u, u} B X Λ)),
          ((fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar ⊣ G) →
          Nonempty (G ≅ moduleRUpperShriekFunctor.{u, u, w, u} B Λ f) := by
  obtain ⟨Xbar, j, fbar, hj, hfbar, rfl⟩ := exists_isOpenImmersion_isFinite_factorization B f
  refine ⟨Xbar, j, fbar, hj, hfbar, rfl, fun RFbar α _ => ⟨?_, fun G adj => ?_⟩⟩
  · exact isLeftAdjoint_compactificationDerivedLowerShriek.{w} B Λ j fbar RFbar α
  · exact ⟨compactificationRightAdjointIso.{w} B Λ j fbar RFbar α G adj⟩

end AlgebraicGeometry.SmallEtale

end
