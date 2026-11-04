module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionwiseHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforward

/-!
# Sections over an affine étale object of a K-injective resolution of `ε^* Ĩ`

Let `I` be a complex of `A`-modules and let `ι : ε^* Ĩ ⟶ J` be a quasi-isomorphism into a
K-injective complex of `𝒪_étale`-modules. For every object `V` of the small étale site of `Spec A`
with affine underlying scheme, taking sections over `V` turns `ι` into a quasi-isomorphism of
complexes of `A`-modules.

This combines Stacks 03DW and 01XB with Stacks 0BKZ: the cohomology sheaves of `J` are the
quasi-coherent modules `ε^* H^q(I)~`, which have no higher cohomology over an affine object, so
over `V` the sectionwise cohomology of `J` is the module of sections of its cohomology sheaves
(`Stacks.Cohomology.HypercohomologyEdge.isIso_homologyComparison_app_of_acyclic_cover`).
The sectionwise cohomology of `ε^* Ĩ` over `V` is the module of sections of its cohomology sheaves
for a simpler reason: sections over `V` of `ε^*T` are flat base change, an exact functor
(`AlgebraicGeometry.AffineEtaleDuality.cartNatIso`).

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.quasiIso_secA_map`: sections over an affine object `V` of
  the small étale site turn a quasi-isomorphism `ε^* Ĩ ⟶ J` into a K-injective complex into a
  quasi-isomorphism of complexes of `A`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- Sections over `V`, as abelian groups. -/
abbrev secAb (V : Site A B hX) : Mod A B hX ⥤ AddCommGrpCat.{u} :=
  underlyingPresheaf (O A B hX) ⋙ (evaluation _ _).obj (op V)

/-- Sections over `V` as abelian groups are the `A`-module of sections over `V` followed by the
forgetful functor to abelian groups. -/
lemma secAb_eq (V : Site A B hX) :
    secAb A B hX V = secA A B hX V ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} := rfl

/-- **Sections over an affine étale object turn a K-injective resolution of `ε^* Ĩ` into a
quasi-isomorphism.** -/
theorem quasiIso_secA_map (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V))
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (J : CochainComplex (Mod A B hX) ℤ)
    [J.IsKInjective] (ι : ((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso ι] :
    QuasiIso (((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).map ι) := by
  let F := secAb A B hX V
  have hε (n : ℤ) : IsIso (homologyComparison (epsT A B hX) I n) :=
    isIso_homologyComparison_of_exact _ I n
  have hF : ∀ q : ℤ, IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ι) q) := by
    intro q
    have hJ : IsIso (homologyComparison F J q) := by
      rw [homologyComparison_comp]
      have : IsIso (homologyComparison ((evaluation _ AddCommGrpCat.{u}).obj (op V))
          (((underlyingPresheaf (O A B hX)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) q) :=
        isIso_homologyComparison_of_exact _ _ q
      have : IsIso ((homologyComparison (underlyingPresheaf (O A B hX)) J q).app (op V)) := by
        refine isIso_homologyComparison_app_of_acyclic_cover (O A B hX) J inferInstance
          (fun W => AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj W))
          (SmallEtale.hasEnoughObjects_isAffine B (Spec A) hX) ?_ hV q
        intro W hW p hp m
        have e : J.homology m ≅ (epsT A B hX).obj (I.homology m) := by
          exact (asIso (HomologicalComplex.homologyMap ι m)).symm ≪≫
            asIso (homologyComparison (epsT A B hX) I m)
        exact (SmallEtale.isZero_rightDerived_evaluation_of_isAffine B (Spec A) hX _
          (isQuasicoherentOnSite_epsT A B hX _) W hW p hp).of_iso
          (((SheafOfModules.evaluation (O A B hX) (op W)).rightDerived p).mapIso e)
      exact IsIso.comp_isIso' inferInstance this
    have hG : IsIso (homologyComparison F
        (((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) q) := by
      have := preservesFiniteLimits_epsT_secA A B hX V hV
      have := preservesFiniteColimits_epsT_secA A B hX V hV
      have : PreservesFiniteLimits (epsT A B hX ⋙ F) :=
        comp_preservesFiniteLimits (epsT A B hX ⋙ secA A B hX V) (forget₂ _ _)
      have : PreservesFiniteColimits (epsT A B hX ⋙ F) :=
        comp_preservesFiniteColimits (epsT A B hX ⋙ secA A B hX V) (forget₂ _ _)
      have h1 : IsIso (homologyComparison (epsT A B hX ⋙ F) I q) :=
        isIso_homologyComparison_of_exact _ I q
      rw [homologyComparison_comp] at h1
      exact IsIso.of_isIso_comp_right _ (F.map (homologyComparison (epsT A B hX) I q))
    have hnat := homologyComparison_naturality F ι q
    have : IsIso (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ι) q ≫ homologyComparison F J q) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (homologyComparison F J q)
  have hq : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ι) :=
    ⟨fun q => (quasiIsoAt_iff_isIso_homologyMap _ q).2 (hF q)⟩
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).map ι)
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).1 hq

end AlgebraicGeometry.AffineEtaleDuality

end
