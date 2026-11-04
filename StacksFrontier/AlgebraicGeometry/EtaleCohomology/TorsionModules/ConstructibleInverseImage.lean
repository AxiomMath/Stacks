module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstructibleCurveCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt

/-!
# Inverse images of constructible sheaves of modules, across big étale sites

Let `Λ` be a Noetherian ring, `X` a quasi-compact quasi-separated scheme of a big étale site `B`,
`F` a constructible sheaf of `Λ`-modules on `X_étale` (read on the small étale site of Tag 021B of
`B`), and `g : Y ⟶ X` a quasi-compact quasi-separated morphism from a quasi-compact
quasi-separated scheme `Y` which need not lie in `B`. Then `g⁻¹ F` is constructible on some big
étale site containing `Y`. This is Tag 095G, read on Mathlib's small étale sites, in the form
needed to apply finiteness theorems after a base change of the ground field.

## Main results

* `Stacks.EtaleCohomology.exists_isConstructibleEtaleModule_inverseImage`.

## Implementation notes

The proof is by generators, as in [SGA 4½, Th. finitude, 1.5]. `F` is the cokernel of a map
`⊕_j j_{W_j!}Λ̲ ⟶ ⊕_i j_{V_i!}Λ̲` with `V_i`, `W_j` affine and étale over `X` (the finite
generation step of Stacks 095N, applied to `F` and to the kernel of the resulting epimorphism).
Inverse image is a left adjoint, so `g⁻¹ F` is the cokernel of the inverse image of that map, and
`g⁻¹ (j_{V!} Λ̲) = j_{V'!} Λ̲` for `V' = V ×_X Y` (extension by zero commutes with inverse image
around a cartesian square, and the inverse image of a constant sheaf is constant). The schemes
`V'` are quasi-compact and quasi-separated, so their `j_{V'!}Λ̲` are constructible (Stacks 03S8)
on a big étale site containing `Y` and all of them, and constructible sheaves form a weak Serre
subcategory.

## References

* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [-instance] hasSheafifyEtale

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [local instance 10000] hasColimit_discrete_fin_etaleModules

variable (Λ : Type r) [CommRing Λ]

/-- **The inverse image of a generator `j_{V!}Λ̲` is the generator of the base change**: for an
étale `j : V ⟶ X` and any `g : Y ⟶ X`, `g⁻¹(j_! Λ̲) ≅ (j')_! Λ̲` with `j' : V ×_X Y ⟶ Y` the
base change of `j`. -/
def etaleModuleInverseImageShriekConstantIso {V X Y : Scheme.{u}} (j : V ⟶ X) [Etale j]
    (g : Y ⟶ X) (M : ModuleCat.{max (u + 1) r} Λ) :
    (etaleModuleInverseImage.{u, r} Λ g).obj ((etaleModuleShriekConstant.{u, r} Λ j).obj M) ≅
      (etaleModuleShriekConstant.{u, r} Λ (pullback.snd j g)).obj M :=
  ((etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ (IsPullback.of_hasPullback j g)).app
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)).symm ≪≫
    (etaleModuleExtensionByZero.{u, r} Λ (pullback.snd j g)).mapIso
      ((etaleModuleInverseImageConstantIso.{u, r} Λ (pullback.fst j g)).app M)

variable [IsNoetherianRing Λ]

/-- **Stacks 03S8 for an étale scheme over a member of a big étale site**: for a
quasi-compact quasi-separated `V` étale over `Y` and a big étale site containing both, `j_!Λ̲`
is constructible. -/
theorem isConstructibleEtaleModule_etaleModuleShriekConstant_of_contains (B : BigEtaleSite.{u})
    {V Y : Scheme.{u}} (hV : B.Contains V) (hY : B.Contains Y) (j : V ⟶ Y) [Etale j]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace V] [QuasiSeparatedSpace V] :
    IsBigSiteConstructibleEtaleModule B (B.obj Y hY) Λ ((etaleModuleShriekConstant.{u, r} Λ j).obj
      (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))) := by
  let U : SmallEtale B Y hY := ⟨Over.mk (ObjectProperty.homMk j : B.obj V hV ⟶ B.obj Y hY),
    (inferInstance : Etale j)⟩
  have : CompactSpace (B.obj Y hY).obj := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace (B.obj Y hY).obj := inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace U.obj.left.obj := inferInstanceAs (CompactSpace V)
  have : QuasiSeparatedSpace U.obj.left.obj := inferInstanceAs (QuasiSeparatedSpace V)
  exact isConstructibleEtaleModule_etaleModuleShriekConstant B (B.obj Y hY) Λ U

/-- **Tag 095G across big étale sites.** Let `F` be a constructible sheaf of `Λ`-modules on a
quasi-compact quasi-separated member `X` of a big étale site `B`, and `g : Y ⟶ X` a quasi-compact
quasi-separated morphism from a quasi-compact quasi-separated scheme. Then `g⁻¹ F` is
constructible on some big étale site containing `Y`. -/
theorem exists_isConstructibleEtaleModule_inverseImage (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] {Y : Scheme.{u}} (g : Y ⟶ X.obj)
    [QuasiCompact g] [QuasiSeparated g] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : EtaleModules.{u, r} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F) :
    ∃ (B' : BigEtaleSite.{u}) (hY : B'.Contains Y),
      IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ
        ((etaleModuleInverseImage.{u, r} Λ g).obj F) := by
  classical
  have hS := isWeakSerreClass_isBigSiteConstructibleEtaleModule B X Λ
  have hgen : ∀ V : SmallEtale B X.obj X.property, IsAffine V.obj.left.obj →
      IsBigSiteConstructibleEtaleModule B X Λ (smallEtaleShriekGenerator B X Λ V) := fun V hV => by
    have := hV
    exact isConstructibleEtaleModule_etaleModuleShriekConstant B X Λ V
  -- the presentation `⊕_j j_{W_j!}Λ̲ ⟶ ⊕_i j_{V_i!}Λ̲ ⟶ F ⟶ 0`
  obtain ⟨n, V, hV, φ, hφ⟩ := exists_epi_sigma_smallEtaleShriekGenerator B X Λ F hF
  have hSumV :
      IsBigSiteConstructibleEtaleModule B X Λ (∐ fun i => smallEtaleShriekGenerator B X Λ (V i)) :=
    (IsBigSiteConstructibleEtaleModule B X Λ).prop_colimit _
      fun (i : Discrete (Fin n)) => hgen _ (hV i.as)
  have hK : IsBigSiteConstructibleEtaleModule B X Λ (kernel φ) :=
    (IsBigSiteConstructibleEtaleModule B X Λ).prop_kernel φ hSumV hF
  obtain ⟨n', W, hW, ψ, hψ⟩ := exists_epi_sigma_smallEtaleShriekGenerator B X Λ _ hK
  let α := ψ ≫ kernel.ι φ
  have hex : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ)
  let eF : cokernel α ≅ F := cokernelEpiComp ψ (kernel.ι φ) ≪≫
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (hex.gIsCokernel))
  -- the base changes of the affine étale schemes
  let jv : ∀ i, (V i).obj.left.obj ⟶ X.obj := fun i => B.inclusion.map (V i).obj.hom
  let jw : ∀ i, (W i).obj.left.obj ⟶ X.obj := fun i => B.inclusion.map (W i).obj.hom
  let s : Option (Fin n ⊕ Fin n') → Scheme.{u} := fun o => match o with
    | none => Y
    | some (Sum.inl i) => pullback (jv i) g
    | some (Sum.inr i) => pullback (jw i) g
  obtain ⟨B', hB'⟩ := BigEtaleSite.exists_contains_of_small (Set.range s)
  have hY : B'.Contains Y := hB' _ ⟨none, rfl⟩
  have hVc : ∀ i, B'.Contains (pullback (jv i) g) := fun i => hB' _ ⟨some (Sum.inl i), rfl⟩
  have hWc : ∀ i, B'.Contains (pullback (jw i) g) := fun i => hB' _ ⟨some (Sum.inr i), rfl⟩
  refine ⟨B', hY, ?_⟩
  have hS' := isWeakSerreClass_isBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ
  let E := etaleModuleInverseImage.{u, r} Λ g
  have : PreservesColimitsOfSize.{0, 0} E :=
    (etaleModuleInverseImageAdj.{u, r} Λ g).leftAdjoint_preservesColimits
  have hgen' : ∀ (T : SmallEtale B X.obj X.property) (hT : IsAffine T.obj.left.obj),
      B'.Contains (pullback (B.inclusion.map T.obj.hom) g) →
      IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ
        (E.obj (smallEtaleShriekGenerator B X Λ T)) := fun T hT hc => by
    have : IsAffine (B.inclusion.obj T.obj.left) := hT
    have : Etale (B.inclusion.map T.obj.hom) := T.property
    have : CompactSpace ↥(pullback (B.inclusion.map T.obj.hom) g : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst (B.inclusion.map T.obj.hom) g)
    have : QuasiSeparatedSpace ↥(pullback (B.inclusion.map T.obj.hom) g : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (B.inclusion.map T.obj.hom) g)
    exact (IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ).prop_of_iso
      (etaleModuleInverseImageShriekConstantIso Λ _ g _).symm
      (isConstructibleEtaleModule_etaleModuleShriekConstant_of_contains Λ B' hc hY _)
  have hESum : ∀ {m : ℕ} (T : Fin m → SmallEtale B X.obj X.property),
      (∀ i, IsAffine (T i).obj.left.obj) →
      (∀ i, B'.Contains (pullback (B.inclusion.map (T i).obj.hom) g)) →
      IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ
        (E.obj (∐ fun i => smallEtaleShriekGenerator B X Λ (T i))) := fun {m} T hT hc => by
    have : (IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ).IsClosedUnderFiniteCoproducts :=
      isClosedUnderFiniteCoproducts_isConstructibleEtaleModule B' (B'.obj Y hY) Λ
    exact (IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ).prop_of_iso
      (PreservesCoproduct.iso E _).symm
      ((IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ).prop_colimit _
        fun (i : Discrete (Fin m)) => hgen' _ (hT i.as) (hc i.as))
  exact (IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ).prop_of_iso (E.mapIso eF)
    ((IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ).prop_of_iso
      (PreservesCokernel.iso E α).symm
      ((IsBigSiteConstructibleEtaleModule B' (B'.obj Y hY) Λ).prop_cokernel _ (hESum W hW hWc)
        (hESum V hV hVc)))

end Stacks.EtaleCohomology

end
