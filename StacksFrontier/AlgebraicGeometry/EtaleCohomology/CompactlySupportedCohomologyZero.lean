module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Formula
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
import StacksCore.Tactic.StacksAttribute

/-!
# The zeroth compactly supported cohomology group

Let `X` be a separated scheme of finite type over a field `k`, let `Λ` be a ring and let `ℱ` be a
sheaf of `Λ`-modules on the small étale site of `X`.  Choosing a compactification
`j : X ⟶ X̄` over `k`, the compactly supported cohomology `RΓ_c(X, -) = RΓ(Spec k, Rf_!(-))` of
the complex `ℱ[0]` has, in degree zero, the group of global sections of the extension by zero
`j_!ℱ` on the compactification.

Three things are needed for that.  Extension by zero is exact, so `Rj_!(ℱ[0])` is `(j_!ℱ)[0]`;
the derived direct image of a complex concentrated in degree zero has `j_!ℱ` pushed forward as
its zeroth cohomology sheaf, because the direct image is left exact; and the derived global
sections of a bounded below complex have, in degree zero, the global sections of its zeroth
cohomology sheaf.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleGlobalSectionsDirectImageIso`: global sections of a direct
  image are global sections upstairs.

## Main results

* `Stacks.RightDerivedPlus.nonempty_homologyZero_rightDerivedFunctorPlus_iso`: for a left exact
  functor `G` and a complex `N` with no cohomology in negative degrees,
  `H⁰(RG(N)) ≅ G(H⁰(N))`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZero_preservesFiniteLimits`: extension by zero
  of sheaves of modules on small étale sites is left exact, hence exact.
* `Stacks.EtaleCohomology.nonempty_compactlySupportedCohomologyGroup_zero_iso`: the zeroth
  compactly supported cohomology group of `ℱ[0]` is `H⁰(X̄, j_!ℱ)`.

## Implementation notes

Tag 0GK1 asserts that the group `H⁰_c(X, ℱ)` of sections with proper support of Tag 0F72 and the
group `H⁰_c(X, ℱ)` of Tag 0GJZ agree, the proof being that both are `H⁰(X̄, j_!ℱ)`.  The second of
those two identifications is the one proved here; the comparison itself, which also needs Tags
0F75 and 0F73 and the passage between the two presentations of the small étale site they are
stated over, is `Stacks.EtaleCohomology.nonempty_addEquiv_compactlySupportedCohomologyGroup_zero`
in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZeroComparison`.

The torsion hypothesis of the source is not needed: its proof never uses it, and neither does
the one here, so the statement is for an arbitrary sheaf of modules.

The source quantifies over the chosen compactification ("choose a compactification `j`") and so
does the statement here; Tag 0F7I, that different compactifications give canonically isomorphic
functors, is therefore not needed.  Separatedness and finite type of `X` over `k` are what make
a compactification exist (Tag 0A9Z); with one given they are not used again, so they are absent
from the statement, which is correspondingly more general than the source's.

`Stacks.RightDerivedPlus.nonempty_homologyZero_rightDerivedFunctorPlus_iso` is stated as the
existence of an isomorphism rather than as a chosen one because the identification of a complex
with cohomology in a single degree with that cohomology object, placed in that degree, is itself
available only as an existence statement
(`DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE`).

Exactness of extension by zero for module coefficients is the argument of
`Stacks.EtaleCohomology.extensionByZero_exact` for abelian coefficients, at a different
coefficient category: the direct-sum formula of Tag 0F4K is stated for arbitrary coefficients,
and Grothendieck's axiom AB4 for modules is `Stacks.Sites.OverModules.mono_sigmaMap`.
`lan_preservesFiniteLimits_of_flat` does not apply, since composition with an étale morphism is
not representably flat.

## References

* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
* [Stacks Project, Tag 0GK1](https://stacks.math.columbia.edu/tag/0GK1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u r v

/-! ### Degree zero of a right derived functor at a bounded below complex -/

namespace Stacks.RightDerivedPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (G : A ⥤ B) [G.Additive] [EnoughInjectives A]

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **Degree zero of a right derived functor at a complex with no negative cohomology**: for a
left exact `G` and `N` in `D⁺` with `H ⁱ(N) = 0` for `i < 0`, `H ⁰(RG(N)) ≅ G(H ⁰(N))`.

Truncating, `τ_{≤0}N ⟶ N` is invertible on `H ⁰` and stays invertible after `RG`, the third
vertex of its truncation triangle being `τ_{>0}N`, which `RG` keeps in degrees `≥ 1`.  And
`τ_{≤0}N` has cohomology in degree zero only, so it is `H ⁰(N)` placed in degree zero, where
`R ⁰ G = G`. -/
theorem nonempty_homologyZero_rightDerivedFunctorPlus_iso [PreservesFiniteLimits G]
    (N : DerivedCategory.Plus A) [N.IsGE 0] :
    Nonempty ((DerivedCategory.Plus.homologyFunctor B 0).obj
        (G.rightDerivedFunctorPlus.obj N) ≅
      G.obj ((DerivedCategory.Plus.homologyFunctor A 0).obj N)) := by
  have hiso : ∀ i ≤ 0, IsIso ((DerivedCategory.Plus.homologyFunctor A i).map
      ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app N)) := fun i hi =>
    DerivedCategory.Plus.isIso_homologyMap_truncLEι_app N i 0 hi
  have hge : ((DerivedCategory.Plus.TStructure.t.truncLE (0 : ℤ)).obj N).IsGE 0 := by
    refine (DerivedCategory.Plus.isGE_iff _ 0).2 fun i hi => ?_
    have := hiso i hi.le
    exact (DerivedCategory.Plus.isZero_homology_of_isGE' N 0 i hi).of_iso
      (asIso ((DerivedCategory.Plus.homologyFunctor A i).map
        ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app N)))
  obtain ⟨M, ⟨e⟩⟩ :=
    DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((DerivedCategory.Plus.TStructure.t.truncLE (0 : ℤ)).obj N) 0
  have hthird : ((DerivedCategory.Plus.TStructure.t.triangleLEGT (0 : ℤ)).obj N).obj₃.IsGE
      (0 + 1) := DerivedCategory.Plus.isGE_truncGT_obj_succ N 0
  have hmain : IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
      (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app N))) := by
    refine DerivedCategory.Plus.isIso_homologyMap_mor₁_of_isGE₃ _
      (G.rightDerivedFunctorPlus.map_distinguished _
        (DerivedCategory.Plus.TStructure.t.triangleLEGT_distinguished 0 N)) 0 (0 + 1) ?_
      (by omega)
    have := hthird
    exact CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj G _ (0 + 1)
  have := hiso 0 le_rfl
  refine ⟨(asIso ((DerivedCategory.Plus.homologyFunctor B 0).map
    (G.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app N)))).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor B 0).mapIso
        (G.rightDerivedFunctorPlus.mapIso e) ≪≫ ?_⟩
  refine (rightDerivedPlusZeroObjIso G M) ≪≫ G.mapIso ?_
  exact ((DerivedCategory.Plus.homologyFunctor A 0).mapIso e ≪≫
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := A) 0).app M).symm ≪≫
      asIso ((DerivedCategory.Plus.homologyFunctor A 0).map
        ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app N))

end Stacks.RightDerivedPlus

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Exactness of extension by zero for module coefficients -/

section Exactness

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (Λ : Type r) [Ring Λ]

/-- The map induced by a monomorphism of presheaves of `Λ`-modules on the sections of the left
Kan extension over a scheme `V` étale over `X` is a monomorphism: by the direct-sum formula of
Tag 0F4K it is a coproduct of components of the given map, and `ModuleCat` satisfies
Grothendieck's axiom AB4. -/
theorem mono_etaleModuleLan_map_app
    {F F' : (U.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ} (α : F ⟶ F') (hα : Mono α)
    (V : X.Etale) :
    Mono (((smallEtaleCompose j).op.lan.map α).app (op V)) := by
  have hnat : (extensionByZeroPresheafSectionIso j F V).hom ≫
      ((smallEtaleCompose j).op.lan.map α).app (op V) =
        Limits.Sigma.map
          (g := fun φ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ)))
          (f := fun φ : V ⟶ smallEtaleSource j => F'.obj (op (sourceDescend j φ)))
          (fun φ => α.app (op (sourceDescend j φ))) ≫
        (extensionByZeroPresheafSectionIso j F' V).hom := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    have hι : ∀ (H : (U.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ),
        Limits.Sigma.ι
          (fun ψ : V ⟶ smallEtaleSource j => H.obj (op (sourceDescend j ψ))) φ ≫
          (extensionByZeroPresheafSectionIso j H V).hom = extensionByZeroSummandInclusion j H φ :=
      fun H => Limits.Sigma.ι_comp_desc (fun ψ => extensionByZeroSummandInclusion j H ψ) φ
    rw [← Category.assoc, hι, extensionByZeroSummandInclusion_naturality, ← hι F',
      Limits.Sigma.ι_map_assoc]
  have hσ : Mono (Limits.Sigma.map
      (g := fun φ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ)))
      (f := fun φ : V ⟶ smallEtaleSource j => F'.obj (op (sourceDescend j φ)))
      (fun φ => α.app (op (sourceDescend j φ)))) :=
    Stacks.Sites.OverModules.mono_sigmaMap.{u, r, max (u + 1) r} _ fun φ =>
      (NatTrans.mono_iff_mono_app α).1 hα (op (sourceDescend j φ))
  have : Mono ((extensionByZeroPresheafSectionIso j F V).hom ≫
      ((smallEtaleCompose j).op.lan.map α).app (op V)) := by
    rw [hnat]
    infer_instance
  exact (mono_comp_iff_of_isIso _ _).1 this

/-- The left Kan extension along composition with `j` preserves monomorphisms of presheaves of
`Λ`-modules. -/
instance etaleModuleLan_preservesMonomorphisms :
    Functor.PreservesMonomorphisms ((smallEtaleCompose j).op.lan :
      ((U.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) ⥤
        ((X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ)) where
  preserves {_ _} α hα :=
    have happ : ∀ W, Mono (((smallEtaleCompose j).op.lan.map α).app W) := fun W =>
      mono_etaleModuleLan_map_app j Λ α hα W.unop
    @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ happ

/-- Extension by zero of sheaves of modules preserves monomorphisms: it is the left Kan
extension along composition with `j` followed by sheafification, and both preserve
monomorphisms. -/
instance etaleModuleExtensionByZero_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (etaleModuleExtensionByZero.{u, r} Λ j) := by
  change Functor.PreservesMonomorphisms
    (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
      (smallEtaleCompose j).op.lan ⋙
        presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
  infer_instance

/-- Extension by zero of sheaves of modules preserves all colimits, being a left adjoint. -/
instance etaleModuleExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleExtensionByZero.{u, r} Λ j) :=
  have : PreservesColimitsOfSize.{0, 0} (etaleModuleExtensionByZero.{u, r} Λ j) :=
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Stacks Project, Tag 03S5** for module coefficients: extension by zero of sheaves of
`Λ`-modules on small étale sites preserves finite limits.  It is additive, preserves
monomorphisms and preserves all colimits, hence preserves homology, hence finite limits. -/
@[stacks 03S5 "left exactness of j_! for module coefficients"]
instance etaleModuleExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleExtensionByZero.{u, r} Λ j) :=
  have : (etaleModuleExtensionByZero.{u, r} Λ j).PreservesHomology :=
    (etaleModuleExtensionByZero.{u, r} Λ j).preservesHomology_of_preservesMonos_and_cokernels
  (etaleModuleExtensionByZero.{u, r} Λ j).preservesFiniteLimits_of_preservesHomology

end Exactness

/-! ### Global sections of a direct image -/

/-- Global sections of a direct image are global sections upstairs: `Γ(Y, g_*ℱ) = Γ(X, ℱ)`.
Global sections on the small étale site of `Y` are the sections over the terminal object `Y`,
the sections of `g_*ℱ` there are the sections of `ℱ` over the base change of that object along
`g`, and base change preserves terminal objects. -/
def etaleModuleGlobalSectionsDirectImageIso {X Y : Scheme.{u}} (g : X ⟶ Y) (Λ : Type r)
    [Ring Λ] :
    etaleModuleDirectImage.{u, r} Λ g ⋙ etaleModuleGlobalSections.{u, r} Λ Y ≅
      etaleModuleGlobalSections.{u, r} Λ X :=
  have hterm : IsTerminal ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ) terminalIsTerminal) ≪≫
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) hterm).symm

/-! ### The zeroth compactly supported cohomology group -/

section Zeroth

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The zeroth compactly supported cohomology group of a sheaf of `Λ`-modules `ℱ` on a `k`-scheme
`X`, placed in degree zero, is the group of global sections of the extension by zero `j_!ℱ` on a
compactification `j : X ⟶ X̄` of `X` over `k`.

This is the half of Tag 0GK1 that concerns Definition 0GJZ; the source's torsion hypothesis is not
used.  Tag 0GK1 itself is
`Stacks.EtaleCohomology.nonempty_addEquiv_compactlySupportedCohomologyGroup_zero`. -/
@[stacks 0GK1 "the Definition 0GJZ side only: H^0_c(X, F) is H^0 of the extension by zero on a \
compactification"]
theorem nonempty_compactlySupportedCohomologyGroup_zero_iso
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    (F : EtaleModules.{u, r} Λ X) :
    Nonempty ((compactlySupportedCohomologyGroup.{u, r} k f j Λ 0).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F) ≅
      (etaleModuleGlobalSections.{u, r} Λ j.space).obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F)) := by
  set G := etaleModuleExtensionByZero.{u, r} Λ j.immersion
  set D := etaleModuleDirectImage.{u, r} Λ j.toBase
  set Γ := etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))
  set S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ j.space) 0
  -- `Rj_!(ℱ[0]) ≅ (j_!ℱ)[0]`, extension by zero being exact.
  have e1 : S.obj (G.obj F) ≅ G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F) :=
    (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G 0).app F
  -- `H ⁰(Rf̄_*((j_!ℱ)[0])) ≅ f̄_*(j_!ℱ)`, the direct image being left exact.
  have e2 : (DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, r} Λ (Spec (.of k))) 0).obj
      (D.rightDerivedFunctorPlus.obj (S.obj (G.obj F))) ≅ D.obj (G.obj F) :=
    Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso D (G.obj F)
  -- `H ⁰(RΓ(N)) ≅ Γ(H ⁰(N))` at the bounded below complex `N = Rf̄_*((j_!ℱ)[0])`.
  have : (D.rightDerivedFunctorPlus.obj (S.obj (G.obj F))).IsGE 0 :=
    CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj D _ 0
  obtain ⟨e3⟩ := Stacks.RightDerivedPlus.nonempty_homologyZero_rightDerivedFunctorPlus_iso Γ
    (D.rightDerivedFunctorPlus.obj (S.obj (G.obj F)))
  exact ⟨(DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) 0).mapIso
    (Γ.rightDerivedFunctorPlus.mapIso (D.rightDerivedFunctorPlus.mapIso e1.symm)) ≪≫
      e3 ≪≫ Γ.mapIso e2 ≪≫
      (etaleModuleGlobalSectionsDirectImageIso.{u, r} j.toBase Λ).app (G.obj F)⟩

end Zeroth

end Stacks.EtaleCohomology

end
