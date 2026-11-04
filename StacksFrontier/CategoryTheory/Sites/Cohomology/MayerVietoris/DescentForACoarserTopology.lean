module

public import StacksFrontier.CategoryTheory.Sites.Modules.CoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.TriangleOfAPushoutSquare
import StacksCore.Tactic.StacksAttribute

/-!
# Mayer–Vietoris for a coarser topology, on the image of the derived direct image

Let `C` carry two Grothendieck topologies `J' ≤ J` and a sheaf of rings `𝒪` for `J`, and let
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})` be the comparison of the two topologies, whose direct image
is the identity on underlying presheaves. Let

```
E ⟶ Y
↓     ↓
Z ⟶ X
```

be a commutative square in `C` whose `J`-sheafified representables form a pushout square and
whose map `h_E^# ⟶ h_Y^#` is a monomorphism. Stacks 0EVY says that the canonical comparison
`c^K_{X,Z,Y,E}` of Stacks 0F16 is then an isomorphism for *every* object of `D(𝒪_J)`. For the
coarser topology `J'` that fails in general, but Stacks 0F19 says it holds for every object of
`D(𝒪_{J'})` in the essential image of `Rε_*`, and that is what this file proves.

## Main results

* `Stacks.Cohomology.MayerVietoris.quasiIso_cSquare_ofLe`: the canonical map of complexes for
  the coarser topology at a complex pushed forward along `ε` is the canonical map for the finer
  topology at the original complex, so it is a quasi-isomorphism whenever the latter is.
* `Stacks.Cohomology.MayerVietoris.isCSquareIso_ofLe_of_isPushout`: **Stacks 0F19.**

## Implementation notes

The proof is the source's. An object `K'` of the essential image of `Rε_*` is `Rε_* K`; a
K-injective complex `I` representing `K` is pushed forward to a complex `ε_* I` which is still
K-injective, by Stacks 093Y in the form
`Stacks.Sites.CoarserTopology.isKInjective_modulePushforward`, and which represents `K'`,
because a K-injective complex computes a right derived functor (Stacks 070K). The short exact
sequence of complexes of abelian groups which defines `c^{K'}` for the coarser topology is then
*the same* sequence that defines `c^K` for the finer one, and Stacks 0EVY applies.

"The same" is literal: `Stacks.Sites.CoarserTopology.modulePushforward` does not change the
underlying presheaf of modules, so the sections of `ε_* M` over an object of the site are the
same term as the sections of `M`, the two signed restriction maps agree, and
`quasiIso_cSquare_ofLe` holds by `rfl`. This is the reason `modulePushforward` is defined
directly rather than as `SheafOfModules.pushforward` along `𝟭 C`, which inserts a restriction of
scalars along `𝟙 𝒪` into every object.

`Rε_*` is taken as an arbitrary right derived functor of `ε_*` with its unit `η`, rather than a
chosen construction, so the statement is about the essential image of any of them; the
hypothesis that it *is* a right derived functor is what makes the essential image independent
of the choice.

## References

* [Stacks Project, Tag 0F19](https://stacks.math.columbia.edu/tag/0F19)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.CoarserTopology
open Stacks.MayerVietoris

namespace Stacks.Cohomology.MayerVietoris

universe u v w r

variable {S : AlgebraicGeometry.RingedSite.{u, w, r}} {J' : GrothendieckTopology S.C}
  (h : J' ≤ S.J)
  [HasSheafify S.J AddCommGrpCat.{v}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]

attribute [local instance] HasDerivedCategory.standard

/-- The direct image of `ε` on complexes of sheaves of modules: a complex of sheaves of modules
for the finer topology, regarded as a complex of sheaves of modules for the coarser one. -/
abbrev complexPushforwardOfLe :
    CochainComplex (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) ℤ :=
  haveI := modulePushforward_additive.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  (modulePushforward.{u, v, w, r} h
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The canonical map of a square is unchanged by coarsening the topology.** The sections of
`ε_* M` over an object of the site are the sections of `M`, so the two signed restriction maps
of Stacks 0F16, their mapping cocone and the canonical map into it are the same for the coarser
topology at `ε_* I` as for the finer topology at `I`. -/
lemma cSquare_complexPushforwardOfLe (sq : Square S.C)
    (I : CochainComplex (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ) :
    cSquare (S := S.ofLe h) sq ((complexPushforwardOfLe.{u, v, w, r} h).obj I) =
      cSquare (S := S) sq I := rfl

/-- **The canonical map of a square for the coarser topology is a quasi-isomorphism as soon as
it is one for the finer topology**, at a complex pushed forward along `ε`. -/
lemma quasiIso_cSquare_ofLe (sq : Square S.C)
    (I : CochainComplex (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ)
    (hI : QuasiIso (cSquare (S := S) sq I)) :
    QuasiIso (cSquare (S := S.ofLe h) sq ((complexPushforwardOfLe.{u, v, w, r} h).obj I)) := hI

variable [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- A complex pushed forward along `ε` represents the derived direct image of the object it
represents, when it is K-injective: a K-injective complex computes a right derived functor, by
Stacks 070K. -/
def derivedPushforwardOfLeIso
    (I : CochainComplex (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ)
    [I.IsKInjective]
    (Rε : DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ⥤
      DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)))
    (η : letI := (modulePushforward_additive.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O));
      (modulePushforward.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [hRD : Rε.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        (ComplexShape.up ℤ))] :
    DerivedCategory.Q.obj ((complexPushforwardOfLe.{u, v, w, r} h).obj I) ≅
      Rε.obj (DerivedCategory.Q.obj I) := by
  haveI := modulePushforward_additive.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  have hη : IsIso (η.app ((HomotopyCategory.quotient
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      (ComplexShape.up ℤ)).obj I)) :=
    @isIso_unit_app_of_isKInjective _ _ _ _ _ _
      (CanonicalMapOfComplexes.exists_kInjectiveResolution.{u, v}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))) _ _
      DerivedCategory.Qh inferInstance
      Rε η hRD I inferInstance
  exact (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O))).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso
      (((modulePushforward.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app I).symm ≪≫
    @asIso _ _ _ _ _ hη ≪≫
    Rε.mapIso ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))).app I)

/-- **Stacks 0F19.** Let `J' ≤ J` be two topologies on `C` and let `𝒪` be a sheaf of rings for
`J`, so that the identity of `C` is a comparison `ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`. Let a
commutative square in `C` be given whose `J`-sheafified representables form a pushout square and
whose map `h_E^# ⟶ h_Y^#` is a monomorphism. Then for every object `K'` of `D(𝒪_{J'})` in the
essential image of the derived direct image `Rε_*`, the canonical map `c^{K'}_{X,Z,Y,E}` of
Stacks 0F16 for the coarser topology is an isomorphism. -/
@[stacks 0F19]
theorem isCSquareIso_ofLe_of_isPushout (sq : Square S.C)
    (hpushout : (sq.map (Sheaf.sheafifiedYoneda S.J)).IsPushout)
    (hmono : Mono ((Sheaf.sheafifiedYoneda S.J).map sq.f₁₂))
    (Rε : DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ⥤
      DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)))
    (η : letI := (modulePushforward_additive.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O));
      (modulePushforward.{u, v, w, r} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        (ComplexShape.up ℤ))]
    (K' : DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)))
    (hK' : Rε.essImage K') :
    (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) sq).IsCSquareIso K' := by
  obtain ⟨K, ⟨e⟩⟩ := hK'
  obtain ⟨I, hI, ⟨eI⟩⟩ :=
    CanonicalMapOfComplexes.exists_kInjective_iso.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) K
  have := hI
  have : IsIso (CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq).derivedCSquare :=
    isIso_derivedCSquare_of_isPushout.{u, v, w, r} sq hpushout hmono
  have hfine : QuasiIso (cSquare (S := S) sq I) :=
    ((CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq).isCSquareIso_iff_quasiIso K I eI).mp
      inferInstance
  have : (((complexPushforwardOfLe.{u, v, w, r} h).obj I)).IsKInjective :=
    isKInjective_modulePushforward.{u, v, w, r} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) I
  exact ((CanonicalMapOfComplexes.derivedCSquareData.{u, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) sq).isCSquareIso_iff_quasiIso K'
      ((complexPushforwardOfLe.{u, v, w, r} h).obj I)
      (derivedPushforwardOfLeIso.{u, v, w, r} h I Rε η ≪≫ Rε.mapIso eI ≪≫ e)).mpr
    (quasiIso_cSquare_ofLe.{u, v, w, r} h sq I hfine)

end Stacks.Cohomology.MayerVietoris

end
