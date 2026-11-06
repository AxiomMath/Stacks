module

public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Basic
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology agrees with the cohomology of the direct image when the higher direct images vanish

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F` be a sheaf of `𝒪_X`-modules with
`R ᵖ f_*F = 0` for every `p > 0`. Then `H ᵖ(X, F) ≅ H ᵖ(Y, f_*F)` for every `p`. This is
[Stacks, Tag 01F4] part (1).

The route is not through the Leray spectral sequence. Global sections on `X`, valued in abelian
groups, *is* pushforward followed by global sections on `Y`, on the nose
(`Stacks.SchemeCohomology.pushforward_comp_secF`, and the same `rfl` at the ringed-space level),
so the two cohomology theories being compared are a right derived functor of one composite and
the composite of two right derived functors. [Stacks, Tag 015M] identifies them under exactly
the acyclicity that `StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Basic` supplies, and
uniqueness of right derived functors then gives
`R Γ(X, -) ≅ R f_* ⋙ R Γ(Y, -)` as functors `D⁺(Mod(𝒪_X)) ⥤ D⁺(Ab)`. The hypothesis on `F`
says that `R f_*` collapses on `F`, i.e. that `R f_*(F[0]) ≅ (f_*F)[0]`, and evaluating the
displayed isomorphism at `F[0]` and taking degree-`p` homology is the statement.

## Main definitions

* `Stacks.LeraySections.derivedSectionsUnit`: the comparison transformation of
  [Stacks, Tag 05T2] for the pair (module pushforward, abelian-group-valued global sections).
* `Stacks.LeraySections.rightDerivedFunctorPlusCompIso`: `R Γ(X, -) ≅ R f_* ⋙ R Γ(Y, -)`.
* `Stacks.LeraySections.derivedPushforwardSingleIso`: `R f_*(F[0]) ≅ (f_*F)[0]` for an
  `f_*`-acyclic `F`.
* `Stacks.LeraySections.cohomologyIsoOfVanishingHigherDirectImages`: **[Stacks, Tag 01F4]
  part (1)**, and `Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages` the
  same for a morphism of schemes.

## Main results

* `Stacks.LeraySections.isRightDerivedFunctor_derivedSectionsUnit`: `R f_*` followed by
  `R Γ(Y, -)` is a right derived functor of `Γ(X, -)`.
* `Stacks.LeraySections.rightAcyclic_modulePushforward_of_isZero_rightDerived`: the vanishing
  hypothesis of the source is right acyclicity for the pushforward, the pushforward being left
  exact.

`cohomologyIsoOfVanishingHigherDirectImages` carries the tag of [Stacks, Tag 01F4] for part (1).
Part (2) of the source — the collapse when it is the base cohomology of the higher direct images
that vanishes — is
`Stacks.Cohomology.LerayModules.isIso_cohomologyToSectionsHigherDirectImage_of_vanishing`, and
carries the same tag there; the two together are the covering set of the tag.

## Implementation notes

**Why not `Stacks.RightDerivedComp`.** The collapse isomorphism
`Stacks.RightDerivedComp.objIso` of
`StacksDraft.AlgebraicGeometry.F3.CohomologyPushforward.CompositeCollapse` has exactly the shape
wanted, `R ⁿ(G ⋙ T)(A) ≅ R ⁿT(G A)` at a `G`-acyclic `A`, but it asks `G` to preserve injective
objects: its proof makes `G` applied to an injective resolution *be* an injective resolution.
Module pushforward does not preserve injectives. The route taken here replaces that hypothesis
by right acyclicity of the images of injectives, which is strictly weaker and is what
[Stacks, Tag 01EX] actually gives.

**What is not proved, and why none of it is a clause of the tag.** The source states an
equality of cohomology groups and nothing else — it names no map, asserts no naturality and
mentions no smaller open — so `cohomologyIsoOfVanishingHigherDirectImages` together with the
part (2) statement already states the whole of [Stacks, Tag 01F4]. Everything in this paragraph
is strengthening *beyond* the source, not a missing clause of it.

The isomorphism is canonical in that it involves no choices — it is assembled from the
uniqueness isomorphism of right derived functors and from the unit of `R f_*`, both pinned, so
the statement already names *which* isomorphism it is — but it is not characterized by an
equation here: no lemma computes `cohomologyIsoOfVanishingHigherDirectImages` in degree zero
against the two canonical maps `Γ ⟶ R ⁰Γ`, and no compatibility with restriction to a smaller
open is stated. The same two normalizations are missing for the affine-morphism collapse; see
the implementation notes of `StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural`,
which rebuilds the comparison one level up rather than whiskering this one.

Identifying the isomorphism with the edge morphism `H^p(Y, f_* F) ⟶ H^p(X, F)` of the Leray
spectral sequence is also not done: `Stacks.Cohomology.RightDerivedEdge.edge`, and the
invertibility statement `Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app` built on it,
both ask `f_*` to preserve injective objects, which it does not — the left adjoint
`f^* = f^{-1}(-) ⊗_{f^{-1}𝒪_Y} 𝒪_X` being only right exact. The direct route taken here is the
one the source's own proof offers in place of the spectral sequence.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.ModulePushforwardComparison

universe u

namespace Stacks.LeraySections

section Leray

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Module sheaves on a ringed space form an abelian category with enough injectives, at the
-- spelling `structureSheafRing` the statements below use.
attribute [local instance] _root_.Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The comparison transformation of [Stacks, Tag 05T2] for the pair (module pushforward,
abelian-group-valued global sections on the target): the transformation from ordinary global
sections on `X`, read as `f_*` followed by global sections on `Y`, to the composite of the two
bounded below right derived functors, assembled from the two units. -/
noncomputable def derivedSectionsUnit :
    (modulePushforward f ⋙ secF (structureSheafRing Y) ⊤).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (modulePushforward f).rightDerivedFunctorPlus ⋙
        (secF (structureSheafRing Y) ⊤).rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (modulePushforward f ⋙ secF (structureSheafRing Y) ⊤))).inv
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft (modulePushforward f).mapHomotopyCategoryPlus
      (secF (structureSheafRing Y) ⊤).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight (modulePushforward f).rightDerivedFunctorPlusUnith
      (secF (structureSheafRing Y) ⊤).rightDerivedFunctorPlus

/-- **`R f_*` followed by `R Γ(Y, -)` is a right derived functor of `Γ(X, -)`.** The hypothesis
of [Stacks, Tag 015M] is `rightAcyclic_secF_modulePushforward_obj` at the top open of `Y`: the
pushforward of an injective module sheaf has acyclic abelian-group-valued global sections. Note
that `Γ(X, -)` here is literally `f_* ⋙ Γ(Y, -)`, the two being the same functor and not merely
isomorphic ones. -/
instance isRightDerivedFunctor_derivedSectionsUnit :
    ((modulePushforward f).rightDerivedFunctorPlus ⋙
        (secF (structureSheafRing Y) ⊤).rightDerivedFunctorPlus).IsRightDerivedFunctor
      (derivedSectionsUnit f)
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) :=
  isRightDerivedFunctor_comp_of_rightAcyclic_obj_injective _ _
    fun I hI => rightAcyclic_secF_modulePushforward_obj f ⊤ I hI

/-- **`R Γ(X, -) ≅ R f_* ⋙ R Γ(Y, -)`.** Both sides are right derived functors of the one
functor `Γ(X, -) = f_* ⋙ Γ(Y, -)` along `Qh : K⁺(Mod(𝒪_X)) ⥤ D⁺(Mod(𝒪_X))` — the left by
construction, the right by `isRightDerivedFunctor_derivedSectionsUnit` — so the isomorphism is
the uniqueness isomorphism of right derived functors, `Functor.rightDerivedNatIso` at the
identity. -/
noncomputable def rightDerivedFunctorPlusCompIso :
    (secF (structureSheafRing X) ⊤).rightDerivedFunctorPlus ≅
      (modulePushforward f).rightDerivedFunctorPlus ⋙
        (secF (structureSheafRing Y) ⊤).rightDerivedFunctorPlus :=
  Functor.rightDerivedNatIso _ _
    (secF (structureSheafRing X) (⊤ : Opens X.carrier)).rightDerivedFunctorPlusUnith
    (derivedSectionsUnit f)
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) (Iso.refl _)

/-- **For an `f_*`-acyclic module sheaf, `R f_*(F[0]) ≅ (f_*F)[0]`.** Right acyclicity *is*
invertibility of the unit of `R f_*` at the complex `F[0]` of the bounded below homotopy
category; the two remaining steps identify that complex with `F[0]` in the derived category
(`Functor.singleFunctorPlusIsoCompQh`) and `f_*` applied to it with `(f_*F)[0]`
(`Functor.mapSingleFunctorCompQhIso`). -/
noncomputable def derivedPushforwardSingleIso {F : SheafOfModules.{u} (structureSheafRing X)}
    (hF : (modulePushforward f).rightAcyclic F) :
    (modulePushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
        ((modulePushforward f).obj F) :=
  have : IsIso ((modulePushforward f).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)) := by
    -- `rightDerivedFunctorPlusUnith` is not exposed: compare it with the unit of
    -- `totalRightDerived` (the one `rightAcyclic` uses), both units of right derived functors.
    have : IsIso ((modulePushforward f).rightDerivedFunctorPlus.rightDerivedDesc
        (modulePushforward f).rightDerivedFunctorPlusUnith
        (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) _
        (((modulePushforward f).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
          (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))))) :=
      (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
    have hF' := hF
    unfold Functor.rightAcyclic at hF'
    rw [← Functor.rightDerived_fac_app (modulePushforward f).rightDerivedFunctorPlus
      (modulePushforward f).rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) _
      (((modulePushforward f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))))] at hF'
    exact (isIso_comp_right_iff _ _).1 hF'
  (modulePushforward f).rightDerivedFunctorPlus.mapIso
      ((Functor.singleFunctorPlusIsoCompQh 0).app F) ≪≫
    (asIso ((modulePushforward f).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj F))).symm ≪≫
    (Functor.mapSingleFunctorCompQhIso (modulePushforward f)).app F

/-- Cohomology and the cohomology of the direct image agree for an `f_*`-acyclic module sheaf,
in the `ℤ`-indexed spelling `Functor.rightDerivedPlus` of the higher right derived functors.
This is `rightDerivedFunctorPlusCompIso` evaluated at `F[0]`, followed by the collapse of
`R f_*` there, read in degree `p`. -/
noncomputable def rightDerivedPlusObjPushforwardIso {F : SheafOfModules.{u} (structureSheafRing X)}
    (hF : (modulePushforward f).rightAcyclic F) (p : ℤ) :
    ((secF (structureSheafRing X) ⊤).rightDerivedPlus p).obj F ≅
      ((secF (structureSheafRing Y) ⊤).rightDerivedPlus p).obj ((modulePushforward f).obj F) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).mapIso
    ((rightDerivedFunctorPlusCompIso f).app
        ((DerivedCategory.Plus.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj F) ≪≫
      (secF (structureSheafRing Y) ⊤).rightDerivedFunctorPlus.mapIso
        (derivedPushforwardSingleIso f hF))

/-- Vanishing of the higher direct images in the positive degrees is right acyclicity of the
module sheaf for the pushforward: the pushforward is a right adjoint, hence left exact, so
part (2) of [Stacks, Tag 015C] applies. -/
theorem rightAcyclic_modulePushforward_of_isZero_rightDerived
    {F : SheafOfModules.{u} (structureSheafRing X)}
    (hF : ∀ q : ℕ, 0 < q → IsZero (((modulePushforward f).rightDerived q).obj F)) :
    (modulePushforward f).rightAcyclic F := by
  rw [(Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (modulePushforward f) F).2 inferInstance]
  intro i hi
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (modulePushforward f) hn F]
  exact hF n (by omega)

/-- **[Stacks, Tag 01F4] part (1).** If the higher direct images of a sheaf of
`𝒪_X`-modules along a morphism of ringed spaces vanish, then its cohomology agrees in every
degree with the cohomology of its direct image. -/
@[stacks 01F4 "part (1)", sga "4½ Arcata 2.3.5" "H^p(X,F)=H^p(Y,f_*F)"]
noncomputable def cohomologyIsoOfVanishingHigherDirectImages
    {F : SheafOfModules.{u} (structureSheafRing X)}
    (hF : ∀ q : ℕ, 0 < q → IsZero (((modulePushforward f).rightDerived q).obj F)) (p : ℕ) :
    (Hfunctor (structureSheafRing X) ⊤ p).obj F ≅
      (Hfunctor (structureSheafRing Y) ⊤ p).obj ((modulePushforward f).obj F) :=
  (Stacks.DerivedIndexing.rightDerivedIso
      (secF (structureSheafRing X) (⊤ : Opens X.carrier)) p).app F ≪≫
    rightDerivedPlusObjPushforwardIso f
        (rightAcyclic_modulePushforward_of_isZero_rightDerived f hF) p ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso
        (secF (structureSheafRing Y) (⊤ : Opens Y.carrier)) p).app _).symm

end Leray

/-! ### The same statement for a morphism of schemes -/

section Schemes

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Module sheaves on a scheme form an abelian category with enough injectives, at the spelling
-- `AlgebraicGeometry.Scheme.ringCatSheaf` the statements below use.
attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

/-- **[Stacks, Tag 01F4] part (1) for a morphism of schemes.** Every identification needed to
read the ringed-space statement at a morphism of schemes is `rfl`, by
`Stacks.SchemeCohomology.modulePushforward_hom` and
`Stacks.SchemeCohomology.ringSheaf_ringedSpace`. -/
noncomputable def schemeCohomologyIsoOfVanishingHigherDirectImages {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules}
    (hF : ∀ q : ℕ, 0 < q →
      IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj F)) (p : ℕ) :
    (Hfunctor X.ringCatSheaf ⊤ p).obj F ≅
      (Hfunctor Y.ringCatSheaf ⊤ p).obj ((Scheme.Modules.pushforward f).obj F) :=
  cohomologyIsoOfVanishingHigherDirectImages (Stacks.SchemeCohomology.hom f) hF p

end Schemes

end Stacks.LeraySections

end
