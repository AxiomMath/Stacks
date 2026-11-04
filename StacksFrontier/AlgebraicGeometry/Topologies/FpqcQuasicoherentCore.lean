module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcOverSiteDichotomy
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# Tag 03DT reduced to covering sieves of the base

`Stacks.Sites.isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_isSheafFor` reduces the fpqc
sheaf condition for the presheaf of Tag 03DS to the sheaf condition for a single covering family
of an *arbitrary* scheme `X` over `S`.  This file removes the "arbitrary `X`": it is enough to
treat covering families of the base scheme itself, for every scheme and every quasi-coherent
module on it.

## Main definitions

* `Stacks.Sites.quasiCoherentPresheafBaseChangeIso`: restricting the presheaf of Tag 03DS of
  `(S, F)` along `CategoryTheory.Over.map X.hom` gives the presheaf of Tag 03DS of
  `(X.left, X.hom⁺ F)`.

## Main results

* `Stacks.Sites.isSheafFor_quasiCoherentPresheaf_of_base`: if, for every scheme `S'` and every
  quasi-coherent module `F'` on `S'`, the presheaf of Tag 03DS of `(S', F')` satisfies the sheaf
  condition for every fpqc covering sieve of `S'` itself, then it satisfies the sheaf condition
  for every covering family of every scheme over `S'`.
* `Stacks.Sites.isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_base`: consequently the
  presheaf of Tag 03DS is an fpqc sheaf on the schemes over `S`.  This is Tag 03DT in the fpqc
  case, assuming only the sheaf condition over the base.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Sites

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent] (X : Over S)

/-- **Base change for the presheaf of Tag 03DS.**  Restricting the presheaf
`(T ⟶ S) ↦ Γ(T, T.hom⁺ F)` along `CategoryTheory.Over.map X.hom` gives the presheaf of Tag 03DS
of the base change `X.hom⁺ F`. -/
noncomputable def quasiCoherentPresheafBaseChangeIso :
    (Over.map X.hom).op ⋙ quasiCoherentPresheafFunctor S F ≅
      quasiCoherentPresheafFunctor X.left ((Scheme.Modules.pullback X.hom).obj F) :=
  pullbackSectionsBaseChangeIso F X (quasiCoherentPresheaf S F)
    (quasiCoherentPresheaf X.left ((Scheme.Modules.pullback X.hom).obj F))

/-- **Tag 03DT over an arbitrary base scheme follows from Tag 03DT over the base.**  Assume that
for every scheme `S'`, every quasi-coherent module `F'` on `S'` and every fpqc covering sieve `T`
of `S'`, the presheaf of Tag 03DS of `(S', F')` satisfies the sheaf condition for the sieve of
`Over S'` corresponding to `T`.  Then it satisfies the sheaf condition for every family of
morphisms of schemes over `S` whose image is an fpqc covering family. -/
theorem isSheafFor_quasiCoherentPresheaf_of_base
    (h : ∀ (S' : Scheme.{u}) (F' : S'.Modules) [F'.IsQuasicoherent] (T : Sieve S'),
      T ∈ Scheme.fpqcTopology.{u} S' →
      Presieve.IsSheafFor
        (quasiCoherentPresheafFunctor S' F' ⋙ CategoryTheory.forget AddCommGrpCat)
        ((Sieve.overEquiv (Over.mk (𝟙 S') : Over S')).symm T).arrows)
    (R : Presieve X) (hR : R.map (Over.forget S) ∈ Scheme.fpqcPrecoverage.{u} X.left) :
    Presieve.IsSheafFor
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) R := by
  have hT : Sieve.overEquiv X (Sieve.generate R) ∈ Scheme.fpqcTopology.{u} X.left := by
    have h₀ := Precoverage.generate_mem_toGrothendieck hR
    rwa [Sieve.generate_map_eq_functorPushforward, ← Sieve.overEquiv_apply] at h₀
  have hbase := h X.left ((Scheme.Modules.pullback X.hom).obj F)
    (Sieve.overEquiv X (Sieve.generate R)) hT
  rw [isSheafFor_overEquiv_symm_baseChange_iff F X (quasiCoherentPresheaf S F)
    (quasiCoherentPresheaf X.left ((Scheme.Modules.pullback X.hom).obj F)),
    OrderIso.symm_apply_apply] at hbase
  rwa [Presieve.isSheafFor_iff_generate]

/-- **Tag 03DT, fpqc case, assuming the sheaf condition over the base.**  If the presheaf of
Tag 03DS of every pair (scheme, quasi-coherent module on it) satisfies the sheaf condition for
every fpqc covering sieve of that scheme, then the presheaf of Tag 03DS of `(S, F)` is an fpqc
sheaf on the schemes over `S`. -/
theorem isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_base
    (h : ∀ (S' : Scheme.{u}) (F' : S'.Modules) [F'.IsQuasicoherent] (T : Sieve S'),
      T ∈ Scheme.fpqcTopology.{u} S' →
      Presieve.IsSheafFor
        (quasiCoherentPresheafFunctor S' F' ⋙ CategoryTheory.forget AddCommGrpCat)
        ((Sieve.overEquiv (Over.mk (𝟙 S') : Over S')).symm T).arrows) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_isSheafFor S F
    fun {X} R hR ↦ isSheafFor_quasiCoherentPresheaf_of_base F X h R hR

end Stacks.Sites

end
