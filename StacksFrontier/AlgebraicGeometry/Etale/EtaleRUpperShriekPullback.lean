module

public import StacksFrontier.AlgebraicGeometry.Etale.RUpperShriekCompactification
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleModulePullbackAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

import StacksCore.Tactic.StacksAttribute

/-!
# For a separated étale morphism the derived upper shriek is the inverse image

Let `j : U ⟶ X` be a separated étale morphism of quasi-compact and quasi-separated schemes and
let `Λ` be a ring. The derived upper shriek `Rj^! : D(X_étale, Λ) ⥤ D(U_étale, Λ)` of
[Stacks, Tag 0G2C], the right adjoint of the derived lower shriek `Rj_! = Rj̄_* ∘ j'_!` of a
compactification `j = j̄ ∘ j'`, is the inverse image `j^{-1}`, [Stacks, Tag 0GL9]. The proof of
the source: both `Rj^!` and `j^{-1}` are right adjoint to `Rj_! = j_!`, by [Stacks, Tag 0GL8] and
[Stacks, Tag 0F5A].

## Main results

All in the namespace `AlgebraicGeometry.SmallEtale`.

* `fShriekModMapDerivedCategoryAdjunction` — for an étale `j`, the adjunction `j_! ⊣ j^{-1}` on
  sheaves of `Λ`-modules (the extension-by-zero adjunction of [Stacks, Tag 03S3], read through
  [Stacks, Tag 0F6Q]) induces `j_! ⊣ j^{-1}` on `D(U_étale, Λ)` and `D(X_étale, Λ)`, both
  functors being exact.
* `moduleRUpperShriekFunctorIsoPullbackMod` — for an étale `j`, the derived upper shriek `Rj^!`
  of [Stacks, Tag 0F5N] is `j^{-1}` on derived categories: the derived form of
  [Stacks, Tag 0F5A], by uniqueness of right adjoints of `j_!`.
* `compactificationRightAdjointIsoPullbackMod` — for a compactification `j = j̄ ∘ j'` of an
  étale `j` with `j'` an open immersion and `j̄` finite, every right adjoint of
  `Rj_! = Rj̄_* ∘ j'_!` is isomorphic to `j^{-1}`.
* `exists_compactification_rightAdjointIso_pullbackMod_mapDerivedCategory` —
  **[Stacks, Tag 0GL9]**: for `j` separated and étale with `U` quasi-compact and `X`
  quasi-compact and quasi-separated, `j` has a compactification `j = j̄ ∘ j'` with `j̄` finite,
  the functor `Rj_! = Rj̄_* ∘ j'_!` of it is a left adjoint, and every right adjoint `Rj^!` of it
  is isomorphic to `j^{-1} : D(X_étale, Λ) ⥤ D(U_étale, Λ)`.

## Implementation notes

*What "the functor `Rj^!` of Lemma 0G2C" is.* As in
`StacksFrontier.AlgebraicGeometry.Etale.RUpperShriekCompactification` ([Stacks, Tag 0GL8]), `Rj^!`
is a right adjoint of `Rj_! = Rj̄_* ∘ j'_!`, determined up to unique isomorphism, so the
statement is made for an *arbitrary* right adjoint `G` of `Rj_!`, given with its adjunction, and
for every model of `D(X̄_étale, Λ)` and every total right derived functor `Rj̄_*` of `j̄_*`. An
étale separated morphism of quasi-compact quasi-separated schemes is separated and
quasi-finite, so the compactification with `j̄` finite is the one Zariski's main theorem
produces, as in [Stacks, Tag 0GL8].

*`j^{-1}` on derived categories.* The inverse image of sheaves of `Λ`-modules is
`AlgebraicGeometry.SmallEtale.pullbackMod`, the `Λ`-linear lift of the abelian inverse image; it
is exact, so it needs no deriving and `j^{-1}` on `D(-_étale, Λ)` is
`(pullbackMod B Λ j).mapDerivedCategory`.

*Hypotheses.* They are the source's, except that some are not needed: `j` separated and étale,
`U` quasi-compact (which with `X` quasi-separated makes `j` quasi-compact), and `X`
quasi-compact and quasi-separated. Quasi-separatedness of `U` follows from that of `X`, `j`
being separated, and is not assumed. The torsion hypothesis on `Λ` is not needed, as in
[Stacks, Tag 0GL8]: in the quasi-finite case `Rj_!` and its right adjoint exist for every ring.

## References

* [Stacks Project, Tag 0GL9](https://stacks.math.columbia.edu/tag/0GL9)
* [Stacks Project, Tag 0GL8](https://stacks.math.columbia.edu/tag/0GL8)
* [Stacks Project, Tag 0F5A](https://stacks.math.columbia.edu/tag/0F5A)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

section Etale

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {U X : B.Scheme} (j : U ⟶ X)
  [Etale (B.inclusion.map j)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B U Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]

/-- For an étale `j : U ⟶ X`, the adjunction `j_! ⊣ j^{-1}` on sheaves of `Λ`-modules induces
the adjunction `j_! ⊣ j^{-1}` between `D(U_étale, Λ)` and `D(X_étale, Λ)`: both functors are
exact, so they act on derived categories without deriving. -/
def fShriekModMapDerivedCategoryAdjunction :
    (fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⊣
      (pullbackMod.{u, u, u} B Λ j).mapDerivedCategory :=
  Adjunction.mapDerivedCategory (etaleFShriekModPullbackAdjunction B X.obj X.property
    (⟨Over.mk j, inferInstanceAs (Etale (B.inclusion.map j))⟩ : SmallEtale B X.obj X.property) Λ)

/-- For an étale `j : U ⟶ X`, the derived upper shriek `Rj^! : D(X_étale, Λ) ⥤ D(U_étale, Λ)`
of [Stacks, Tag 0F5N] is the inverse image `j^{-1}`: both are right adjoint to `j_!`. This is
the derived form of [Stacks, Tag 0F5A]. -/
def moduleRUpperShriekFunctorIsoPullbackMod :
    moduleRUpperShriekFunctor.{u, u, w, u} B Λ j ≅
      (pullbackMod.{u, u, u} B Λ j).mapDerivedCategory :=
  (moduleFShriekRUpperShriekAdjunction.{u, u, w, u} B Λ j).rightAdjointUniq
    (fShriekModMapDerivedCategoryAdjunction.{w} B Λ j)

end Etale

section Compactification

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {U Xbar X : B.Scheme}
  (j : U ⟶ Xbar) (fbar : Xbar ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
  [Etale (B.inclusion.map (j ≫ fbar))]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B U Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Xbar Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
  (RFbar : DerivedCategory (ModuleSheaf.{u, u, u} B Xbar Λ) ⥤
    DerivedCategory (ModuleSheaf.{u, u, u} B X Λ))
  (α : (etalePushforwardMod B Λ fbar).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RFbar)
  [RFbar.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Xbar Λ) (ComplexShape.up ℤ))]

/-- For a compactification `j = j̄ ∘ j'` of an étale morphism, with `j'` an open immersion and
`j̄` finite, every right adjoint `G` of the derived lower shriek `Rj_! = Rj̄_* ∘ j'_!` is
isomorphic to the inverse image `j^{-1}` on derived categories: `G` is the `Rj^!` of
[Stacks, Tag 0F5N] by [Stacks, Tag 0GL8], which is `j^{-1}` as `j` is étale. -/
def compactificationRightAdjointIsoPullbackMod
    (G : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B U Λ))
    (adj : (fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙ RFbar ⊣ G) :
    G ≅ (pullbackMod.{u, u, u} B Λ (j ≫ fbar)).mapDerivedCategory :=
  compactificationRightAdjointIso.{w} B Λ j fbar RFbar α G adj ≪≫
    moduleRUpperShriekFunctorIsoPullbackMod.{w} B Λ (j ≫ fbar)

end Compactification

/-- **[Stacks, Tag 0GL9].** Let `j : U ⟶ X` be a separated étale morphism of a big étale site
with `U` quasi-compact and `X` quasi-compact and quasi-separated, and let `Λ` be a ring. Then
`j` factors as an open immersion `j' : U ⟶ X̄` followed by a finite morphism `j̄ : X̄ ⟶ X`
(Zariski's main theorem), and for every model of `D(X̄_étale, Λ)` and every total right derived
functor `Rj̄_*` of `j̄_*`, the derived lower shriek `Rj_! = Rj̄_* ∘ j'_!` of [Stacks, Tag 0G2C]
has a right adjoint, and every right adjoint `Rj^!` of it is isomorphic to the inverse image
`j^{-1} : D(X_étale, Λ) ⥤ D(U_étale, Λ)`.

The compactification is produced, not assumed. -/
@[stacks 0GL9 "Rj^! of Tag 0G2C is j^{-1}, for every right adjoint of Rj_!",
  ega "IV 18.12.13" "special case"]
theorem exists_compactification_rightAdjointIso_pullbackMod_mapDerivedCategory
    (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {U X : B.Scheme} (j : U ⟶ X)
    [IsSeparated (B.inclusion.map j)] [Etale (B.inclusion.map j)]
    [CompactSpace U.obj] [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B U Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)] :
    ∃ (Xbar : B.Scheme) (j' : U ⟶ Xbar) (fbar : Xbar ⟶ X)
      (_ : IsOpenImmersion (B.inclusion.map j')) (_ : IsFinite (B.inclusion.map fbar)),
      j = j' ≫ fbar ∧
      ∀ [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Xbar Λ)]
        (RFbar : DerivedCategory (ModuleSheaf.{u, u, u} B Xbar Λ) ⥤
          DerivedCategory (ModuleSheaf.{u, u, u} B X Λ))
        (α : (etalePushforwardMod B Λ fbar).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RFbar),
        RFbar.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Xbar Λ) (ComplexShape.up ℤ)) →
        ((fShriekMod.{u, u, u} B Λ j').mapDerivedCategory ⋙ RFbar).IsLeftAdjoint ∧
        ∀ (G : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
            DerivedCategory (ModuleSheaf.{u, u, u} B U Λ)),
          ((fShriekMod.{u, u, u} B Λ j').mapDerivedCategory ⋙ RFbar ⊣ G) →
          Nonempty (G ≅ (pullbackMod.{u, u, u} B Λ j).mapDerivedCategory) := by
  have : QuasiSeparatedSpace (B.inclusion.obj X) := ‹QuasiSeparatedSpace X.obj›
  have : CompactSpace (B.inclusion.obj X) := ‹CompactSpace X.obj›
  have : CompactSpace (B.inclusion.obj U) := ‹CompactSpace U.obj›
  have : QuasiCompact (B.inclusion.map j) :=
    (quasiCompact_iff_compactSpace (B.inclusion.map j)).2 ‹_›
  obtain ⟨Xbar, j', fbar, hj, hfbar, rfl⟩ := exists_isOpenImmersion_isFinite_factorization B j
  refine ⟨Xbar, j', fbar, hj, hfbar, rfl, fun RFbar α _ => ⟨?_, fun G adj => ?_⟩⟩
  · exact isLeftAdjoint_compactificationDerivedLowerShriek.{w} B Λ j' fbar RFbar α
  · exact ⟨compactificationRightAdjointIsoPullbackMod.{w} B Λ j' fbar RFbar α G adj⟩

end AlgebraicGeometry.SmallEtale
