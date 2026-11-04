module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperDirectImageBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Etale.LowerShriekProperDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Etale.ModuleSheafDirectImageAcyclicComplexes
public import StacksFrontier.AlgebraicGeometry.Etale.ModuleSheafTorsionCoextension
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompRightDerivedPlusResolution

import StacksCore.Tactic.StacksAttribute

/-!
# The base change map `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` is an isomorphism

Consider a commutative square of a big étale site
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
```
with `f` and `f'` proper and `k` and `l` separated and locally quasi-finite, and a ring `Λ`.
[Stacks, Tag 0F7B] says that the canonical map
`AlgebraicGeometry.SmallEtale.properBaseChangeMap : l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` of functors
`D(X'_étale, Λ) ⥤ D(Y_étale, Λ)` is an isomorphism at `K` if (a) `K` is bounded below and has
torsion cohomology sheaves, or (b) `Λ` is a torsion ring.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforwardMod_fShriekMod_of_injective`:
  `R^q f_* (k_! I) = 0` for `q > 0` and `I` an injective torsion sheaf of `Λ`-modules.
* `AlgebraicGeometry.SmallEtale.isIso_properBaseChangeMap_of_natCast_eq_zero`: case (b).

## Implementation notes

The coefficient ring `Λ` lives in the universe `u` of the big étale site, as for the map itself
and for [Stacks, Tag 0F7C] and [Stacks, Tag 0F7F] built on it: the sheaves of `Λ`-modules are
`AlgebraicGeometry.SmallEtale.ModuleSheaf.{u, u, u}`.

The proof is the source's. At a K-injective complex `I` with injective terms, the map is, by its
characterization `AlgebraicGeometry.SmallEtale.properBaseChangeMap_fac_app`, the identification
`l_! f'_* I = f_* k_! I` followed by the unit of `Rf_*` at `k_! I`. When `Λ` is torsion the terms
`k_! I^n` are `f_*`-acyclic
(`AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_fShriekFunctor_of_square`,
the injective `I^n` having no higher direct images under `f'` by [Stacks, Tag 03FD]), and a
complex of `f_*`-acyclic sheaves computes `Rf_*` on the unbounded derived category, `Rf_*` having
finite cohomological dimension locally on `Y`
(`AlgebraicGeometry.SmallEtale.quasiIso_etalePushforwardMod_map_of_rightAcyclic`, [Stacks, Tag
095U] and [Stacks, Tag 07K7]).

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X' X Y' Y : B.Scheme}
  (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y) (w : k ≫ f = f' ≫ l)

/-- `R^q g_* N = 0` for a sheaf of `Λ`-modules `N` as soon as it holds on underlying abelian
sheaves. -/
private theorem isZero_rightDerived_etalePushforwardMod_of_forget {T S : B.Scheme} (g : T ⟶ S)
    (q : ℕ) (N : ModuleSheaf.{u, u, u} B T Λ)
    (h : IsZero (((etalePushforward.{u, u + 1} B g).rightDerived q).obj
      ((forgetModuleSheaf.{u, u, u} B T Λ).obj N))) :
    IsZero (((etalePushforwardMod B Λ g).rightDerived q).obj N) :=
  isZero_of_isZero_forgetModuleSheaf B Λ
    (h.of_iso ((rightDerivedEtalePushforwardModForgetIso B Λ g q).app N))

/-- A functor preserving zero morphisms preserves the vanishing of a complex below a degree. -/
private theorem isStrictlyGE_map_homologicalComplex {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => F.map_isZero (K.isZero_of_isStrictlyGE n i hi)

include w in
/-- **`R^q f_* (k_! N) = 0` for `q > 0`, for a torsion sheaf of `Λ`-modules `N` without higher
direct images under `f'`**: on underlying abelian sheaves
(`AlgebraicGeometry.SmallEtale.rightDerivedEtalePushforwardModForgetIso`) this is
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_fShriekFunctor_of_square`. -/
theorem isZero_rightDerived_etalePushforwardMod_fShriekMod_of_acyclic
    [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map f')]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    (N : ModuleSheaf.{u, u, u} B X' Λ) (hN : moduleTorsionSheafProperty.{u, u, u} B X' Λ N)
    (hN' : ∀ p : ℕ, 0 < p → IsZero (((etalePushforwardMod B Λ f').rightDerived p).obj N))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforwardMod B Λ f).rightDerived q).obj
      ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).obj N)) := by
  refine isZero_rightDerived_etalePushforwardMod_of_forget B Λ f q _ ?_
  exact isZero_rightDerived_etalePushforward_fShriekFunctor_of_square B k f' f l w _ hN
    (fun p hp => ((forgetModuleSheaf.{u, u, u} B Y' Λ).map_isZero (hN' p hp)).of_iso
      ((rightDerivedEtalePushforwardModForgetIso B Λ f' p).app N).symm) q hq

include w in
/-- **`R^q f_* (k_! I) = 0` for `q > 0`, for an injective torsion sheaf of `Λ`-modules `I`**: the
injective `I` has no higher direct images under `f'` ([Stacks, Tag 03FD]). -/
theorem isZero_rightDerived_etalePushforwardMod_fShriekMod_of_injective
    [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map f')]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    (I : ModuleSheaf.{u, u, u} B X' Λ) [Injective I]
    (hI : moduleTorsionSheafProperty.{u, u, u} B X' Λ I) (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforwardMod B Λ f).rightDerived q).obj
      ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).obj I)) :=
  isZero_rightDerived_etalePushforwardMod_fShriekMod_of_acyclic B Λ k f' f l w I hI
    (fun p hp => by
      obtain ⟨p, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      exact Functor.isZero_rightDerived_obj_injective_succ _ _ _) q hq

/-! ### Higher direct images of sheaves of `Λ`-modules commute with filtered colimits -/

/-- **Higher direct images of sheaves of `Λ`-modules along a quasi-compact and quasi-separated
morphism commute with filtered colimits**: on underlying abelian sheaves
(`AlgebraicGeometry.SmallEtale.rightDerivedEtalePushforwardModForgetIso`) this is
`AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_rightDerived_etalePushforward`, and
forgetting the module structure preserves and reflects colimits. -/
theorem preservesColimitsOfShape_rightDerived_etalePushforwardMod {T S : B.Scheme} (g : T ⟶ S)
    [QuasiCompact (B.inclusion.map g)] [QuasiSeparated (B.inclusion.map g)] (q : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((etalePushforwardMod B Λ g).rightDerived q) := by
  let G := forgetModuleSheaf.{u, u, u} B S Λ
  have := preservesColimitsOfSize_forgetModuleSheaf.{u, u, u} B T Λ
  have := preservesColimitsOfSize_forgetModuleSheaf.{u, u, u} B S Λ
  have := preservesColimitsOfShape_rightDerived_etalePushforward B g q I
  have : PreservesColimitsOfShape I ((etalePushforwardMod B Λ g).rightDerived q ⋙ G) :=
    preservesColimitsOfShape_of_natIso (rightDerivedEtalePushforwardModForgetIso B Λ g q).symm
  have : ReflectsColimitsOfShape I G := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ G

/-- Higher direct images of sheaves of `Λ`-modules along a proper morphism commute with filtered
colimits. -/
private theorem preservesColimitsOfShape_rightDerived_etalePushforwardMod_of_proper
    {T S : B.Scheme} (g : T ⟶ S) [IsProper (B.inclusion.map g)] (q : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((etalePushforwardMod B Λ g).rightDerived q) := by
  have : UniversallyClosed (B.inclusion.map g) := IsProper.toUniversallyClosed
  have : QuasiCompact (B.inclusion.map g) := instQuasiCompactOfUniversallyClosed _
  have : IsSeparated (B.inclusion.map g) := IsProper.toIsSeparated
  have : QuasiSeparated (B.inclusion.map g) := IsSeparated.instQuasiSeparated _
  exact preservesColimitsOfShape_rightDerived_etalePushforwardMod B Λ g q I

/-! ### The composition comparison `R(f_* ∘ k_!) ⟶ Rf_* ∘ k_!` at torsion sheaves -/

section Comparison

attribute [local instance] HasDerivedCategory.standard

variable [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
  [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
  [LocallyOfFiniteType (B.inclusion.map k)]
  [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
  [LocallyOfFiniteType (B.inclusion.map l)]

include w in
/-- `R^p(f_* ∘ k_!) = l_! ∘ R^p f'_*` on sheaves of `Λ`-modules, `l_!` being exact: a sheaf
without higher direct images under `f'` is acyclic for `f_* ∘ k_! = l_! ∘ f'_*`. -/
theorem isZero_rightDerived_fShriekMod_comp_etalePushforwardMod
    (N : ModuleSheaf.{u, u, u} B X' Λ) (p : ℕ)
    (hN : IsZero (((etalePushforwardMod B Λ f').rightDerived p).obj N)) :
    IsZero (((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k) ⋙
      etalePushforwardMod B Λ f).rightDerived p).obj N) := by
  have : (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  refine (((etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).map_isZero hN).of_iso ?_)
  exact ((rightDerivedIsoOfIso (pushforwardFShriekModSquareIso B Λ k f' f l w) p).symm.app N ≪≫
    ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ (Iso.refl _) p).app N).symm)

include w in
/-- **The composition comparison `R(f_* ∘ k_!) ⟶ Rf_* ∘ k_!` is invertible at a sheaf of
`Λ`-modules annihilated by an integer `m > 0`.** Such a sheaf is the restriction of scalars of a
sheaf of `Λ/mΛ`-modules
(`AlgebraicGeometry.SmallEtale.isIso_moduleSheafCoextensionAdj_counit_app`), and the restriction of
scalars of an injective resolution of the latter is a resolution by torsion sheaves without higher
direct images under `f'` ([Stacks, Tag 03FD] over `Λ/mΛ`). Its terms are acyclic for
`f_* ∘ k_! = l_! ∘ f'_*`, and their images under `k_!` are acyclic for `f_*`
(`isZero_rightDerived_etalePushforwardMod_fShriekMod_of_acyclic`). -/
theorem isIso_rightDerivedFunctorPlusComp_app_single_of_nsmul (M : ModuleSheaf.{u, u, u} B X' Λ)
    (m : ℕ) (hm : 0 < m)
    (hM : ∀ (U : (SmallEtale B X'.obj X'.property)ᵒᵖ) (x : M.obj.obj U), (m : Λ) • x = 0) :
    IsIso ((Functor.rightDerivedFunctorPlusComp (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k))
      (etalePushforwardMod B Λ f)).app ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) := by
  let Res := moduleSheafRestriction B X' Λ m
  let Ψ := moduleSheafCoextension B X' Λ m
  have := isIso_moduleSheafCoextensionAdj_counit_app B X' Λ m M hM
  let e : Res.obj (Ψ.obj M) ≅ M := asIso ((moduleSheafCoextensionAdj B X' Λ m).counit.app M)
  obtain ⟨J, s, hs, hJinj, hJ0⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      ((CochainComplex.singleFunctor _ 0).obj (Ψ.obj M)) 0
  let T := (Res.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  have : CochainComplex.IsStrictlyGE T 0 := isStrictlyGE_map_homologicalComplex Res J 0
  have : Res.PreservesHomology := Functor.preservesHomologyOfExact _
  let ι : (CochainComplex.singleFunctor _ 0).obj M ⟶ T :=
    (CochainComplex.singleFunctor _ 0).map e.inv ≫
      (HomologicalComplex.singleMapHomologicalComplex Res (ComplexShape.up ℤ) 0).inv.app
        (Ψ.obj M) ≫ (Res.mapHomologicalComplex (ComplexShape.up ℤ)).map s
  have : QuasiIso ι := by
    have := hs
    have : QuasiIso ((Res.mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology _ _
    have : QuasiIso ((CochainComplex.singleFunctor _ 0).map e.inv) := quasiIso_of_isIso _
    have : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex Res (ComplexShape.up ℤ)
        0).inv.app (Ψ.obj M)) := quasiIso_of_isIso _
    dsimp only [ι]
    infer_instance
  have hacyc : ∀ (i : ℤ) (p : ℕ), 0 < p →
      IsZero (((etalePushforwardMod B Λ f').rightDerived p).obj (T.X i)) := fun i p hp => by
    obtain ⟨p, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
    refine isZero_rightDerived_etalePushforwardMod_of_forget B Λ f' (p + 1) _ ?_
    exact isZero_rightDerived_etalePushforward_forgetModuleSheaf_of_injective B
      (NatCastQuotient Λ m) f' (J.X i) p
  have htors : ∀ i : ℤ, moduleTorsionSheafProperty.{u, u, u} B X' Λ (T.X i) := fun i =>
    moduleTorsionSheafProperty_of_natCast_eq_zero B (NatCastQuotient Λ m) m hm
      (natCast_natCastQuotient_eq_zero Λ m) (J.X i)
  exact Stacks.ExactCompDerived.isIso_rightDerivedFunctorPlusComp_app_single_of_resolution _ _ M T 0
    ι
    (fun i p hp => isZero_rightDerived_fShriekMod_comp_etalePushforwardMod B Λ k f' f l w _ p
      (hacyc i p hp))
    (fun i p hp => isZero_rightDerived_etalePushforwardMod_fShriekMod_of_acyclic B Λ k f' f l w _
      (htors i) (hacyc i) p hp)

include w in
/-- **The composition comparison `R(f_* ∘ k_!) ⟶ Rf_* ∘ k_!` is invertible at a torsion sheaf
of `Λ`-modules.** A torsion sheaf is the filtered colimit of its subsheaves `M[n!]`
(`AlgebraicGeometry.SmallEtale.isColimitFactorialTorsionCocone`), at which the comparison is
invertible (`isIso_rightDerivedFunctorPlusComp_app_single_of_nsmul`), and the higher derived
functors `R^q(f_* ∘ k_!) = l_! ∘ R^q f'_*` and `R^q f_* ∘ k_!` commute with filtered colimits. -/
theorem isIso_rightDerivedFunctorPlusComp_app_single_of_torsion (M : ModuleSheaf.{u, u, u} B X' Λ)
    (hM : moduleTorsionSheafProperty.{u, u, u} B X' Λ M) :
    IsIso ((Functor.rightDerivedFunctorPlusComp (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k))
      (etalePushforwardMod B Λ f)).app ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) := by
  have : (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).IsLeftAdjoint :=
    fShriekMod_isLeftAdjoint.{u, u, u} B Λ l
  have : (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).IsLeftAdjoint :=
    fShriekMod_isLeftAdjoint.{u, u, u} B Λ k
  let D := factorialTorsionDiagram B Λ M
  refine Stacks.ExactCompDerived.isIso_rightDerivedFunctorPlusComp_app_single_of_isColimit _ _
    (isColimitFactorialTorsionCocone B Λ M hM) (fun j => ?_) (fun q => ?_) (fun q => ?_)
  · have hz :
        ((j.down.factorial : ℕ) : ℤ) • 𝟙 (kernel (((j.down.factorial : ℕ) : ℤ) • 𝟙 M)) = 0 := by
      rw [← cancel_mono (kernel.ι (((j.down.factorial : ℕ) : ℤ) • 𝟙 M)), Preadditive.zsmul_comp,
        Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_zsmul,
        kernel.condition]
    refine isIso_rightDerivedFunctorPlusComp_app_single_of_nsmul B Λ k f' f l w (D.obj j)
      j.down.factorial (Nat.factorial_pos _) fun U x => ?_
    have h₁ : (((j.down.factorial : ℕ) : ℤ) •
        𝟙 (kernel (((j.down.factorial : ℕ) : ℤ) • 𝟙 M)).obj).app U x = 0 :=
      congrArg (fun g => g.hom.app U x) hz
    rw [NatTrans.app_zsmul, NatTrans.id_app] at h₁
    rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul]
    exact h₁
  · have := preservesColimitsOfShape_rightDerived_etalePushforwardMod_of_proper B Λ f' q
      (ULift.{u + 1} ℕ)
    exact preservesColimit_of_natIso D
      ((rightDerivedIsoOfIso (pushforwardFShriekModSquareIso B Λ k f' f l w) q).symm ≪≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ (Iso.refl _) q).symm).symm
  · have := preservesColimitsOfShape_rightDerived_etalePushforwardMod_of_proper B Λ f q
      (ULift.{u + 1} ℕ)
    infer_instance

end Comparison

section Derived

variable [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
  [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
  [LocallyOfFiniteType (B.inclusion.map k)]
  [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
  [LocallyOfFiniteType (B.inclusion.map l)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
  (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
    DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
  (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
  (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
    DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
  (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF'.IsRightDerivedFunctor αF'
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
  [RF.IsRightDerivedFunctor αF
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))]

/-- Every object of `D(X'_étale, Λ)` is the image of a K-injective complex with injective terms:
the chosen functorial K-injective resolution of a complex representing it. -/
def derivedIsoQhKInjectiveResolution (K : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ)) :
    K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((Stacks.Injectives.kInjectiveResolutionFunctor.{u + 1} _).obj
        (DerivedCategory.Q.objPreimage K))) :=
  let φ := DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion.{u + 1} _).app
        (DerivedCategory.Q.objPreimage K))
  have : IsIso φ := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ asIso φ ≪≫
    ((DerivedCategory.quotientCompQhIso _).app _).symm

include w in
/-- **The map of [Stacks, Tag 0F7B] at a K-injective complex.** At a K-injective complex `I`
the map is invertible as soon as the direct image `f_*` carries a K-injective resolution of
`k_! I` to a quasi-isomorphism: by `AlgebraicGeometry.SmallEtale.properBaseChangeMap_fac_app`,
precomposed with the invertible unit of `Rf'_*` at `I`, it is the identification
`l_! f'_* I = f_* k_! I` followed by the unit of `Rf_*` at `k_! I`. -/
theorem isIso_properBaseChangeMap_app_of_isKInjective
    (I : CochainComplex (ModuleSheaf.{u, u, u} B X' Λ) ℤ) (hI : I.IsKInjective)
    (hM : ∃ (J : CochainComplex (ModuleSheaf.{u, u, u} B X Λ) ℤ)
      (s : ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I ⟶ J), QuasiIso s ∧ J.IsKInjective ∧
        QuasiIso (((etalePushforwardMod B Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    IsIso ((properBaseChangeMap B Λ k f' f l w RF' αF' RF αF).app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  obtain ⟨J, s, hs', hJ, hs⟩ := hM
  have h₁₀ := Stacks.ExactCompDerived.isIso_unit_app_of_quasiIso_map.{u + 1}
    (etalePushforwardMod B Λ f') RF' αF' (𝟙 I) hI (by
      rw [CategoryTheory.Functor.map_id]; infer_instance)
  have h₁ : IsIso (αF'.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := h₁₀
  have h₂₀ := Stacks.ExactCompDerived.isIso_unit_app_of_quasiIso_map.{u + 1}
    (etalePushforwardMod B Λ f) RF αF s hJ hs
  have h₂ : IsIso (αF.app (((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := h₂₀
  have hfac := properBaseChangeMap_fac_app B Λ k f' f l w RF' αF' RF αF
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  have : IsIso ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory.map
      (αF'.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (properBaseChangeMap B Λ k f' f l w RF' αF' RF αF).app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
    rw [hfac]; infer_instance
  exact IsIso.of_isIso_comp_left
    ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory.map
      (αF'.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) _

include w in
/-- **[Stacks, Tag 0F7B], case (b)**: over a torsion ring `Λ` the map
`l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` is invertible on the whole unbounded derived category
`D(X'_étale, Λ)`. At a K-injective complex `I` with injective terms, the terms of `k_! I` are
`f_*`-acyclic (`isZero_rightDerived_etalePushforwardMod_fShriekMod_of_injective`), and a complex
of `f_*`-acyclic sheaves computes `Rf_*`
(`AlgebraicGeometry.SmallEtale.quasiIso_etalePushforwardMod_map_of_rightAcyclic`). -/
theorem isIso_properBaseChangeMap_of_natCast_eq_zero (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) :
    IsIso (properBaseChangeMap B Λ k f' f l w RF' αF' RF αF) := by
  have : ∀ K, IsIso ((properBaseChangeMap B Λ k f' f l w RF' αF' RF αF).app K) := fun K => by
    obtain ⟨I, hI, hinj, ⟨e⟩⟩ : ∃ I : CochainComplex (ModuleSheaf.{u, u, u} B X' Λ) ℤ,
        I.IsKInjective ∧ (∀ n, Injective (I.X n)) ∧ Nonempty (K ≅ DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
      ⟨_, Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective _ _,
        fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective _ _ n,
        ⟨derivedIsoQhKInjectiveResolution B Λ K⟩⟩
    refine (NatTrans.isIso_app_iff_of_iso _ e).2 ?_
    obtain ⟨J, s, hJ, hs⟩ :=
      Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian.{u + 1}
        _ (((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
    have hP : ∀ (i : ℤ) (p : ℕ), 0 < p → IsZero (((etalePushforwardMod B Λ f).rightDerived p).obj
        ((((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).X i)) := fun i p hp => by
      have := hinj i
      exact isZero_rightDerived_etalePushforwardMod_fShriekMod_of_injective B Λ k f' f l w
        (I.X i) (moduleTorsionSheafProperty_of_natCast_eq_zero B Λ m hm hΛ _) p hp
    exact isIso_properBaseChangeMap_app_of_isKInjective B Λ k f' f l w RF' αF' RF αF I hI
      ⟨J, s, hs, hJ, quasiIso_etalePushforwardMod_map_of_rightAcyclic B Λ f m hm hΛ hP s hJ⟩
  exact NatIso.isIso_of_isIso_app _

include w in
/-- **[Stacks, Tag 0F7B], case (a)**: the map `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` is invertible at every
`K ∈ D(X'_étale, Λ)` which is bounded below and has torsion cohomology sheaves, for an arbitrary
ring `Λ`. Represent `K` by a bounded below complex `I` of injective sheaves; by
`isIso_properBaseChangeMap_app_of_isKInjective` it suffices that `f_*` carries a resolution of
`k_! I` by a bounded below complex of injectives to a quasi-isomorphism. That is the dévissage
`Stacks.ExactCompDerived.quasiIso_map_of_injective_of_isStrictlyGE` along the canonical
truncations, the composition comparison `R(f_* ∘ k_!) ⟶ Rf_* ∘ k_!` being invertible at the
torsion cohomology sheaves of `I` (`isIso_rightDerivedFunctorPlusComp_app_single_of_torsion`:
the source's reduction to case (b) over `Λ/nΛ` and its passage to the colimit over `n`). -/
theorem isIso_properBaseChangeMap_app_of_isGE (K : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ))
    (n : ℤ) [K.IsGE n] (hK : moduleTorsionCohomologyProperty.{u, u, w, u} B X' Λ K) :
    IsIso ((properBaseChangeMap B Λ k f' f l w RF' αF' RF αF).app K) := by
  obtain ⟨M, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K n
  obtain ⟨I, s, hs, hIinj, hIn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective M n
  have := hs
  have : IsIso (DerivedCategory.Q.map s) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  let e' : K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) :=
    e ≪≫ asIso (DerivedCategory.Q.map s) ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm
  refine (NatTrans.isIso_app_iff_of_iso _ e').2 ?_
  let F := etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)
  have : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n :=
    isStrictlyGE_map_homologicalComplex F I n
  obtain ⟨J, s', hs', hJinj, hJn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n
  have := hs'
  have htors : ∀ q : ℤ, moduleTorsionSheafProperty.{u, u, u} B X' Λ (I.homology q) := by
    intro q
    have h0 := hK q
    unfold moduleTorsionSheafProperty at h0 ⊢
    exact (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      ((forgetModuleSheaf.{u, u, u} B X' Λ).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso (e ≪≫ asIso (DerivedCategory.Q.map s)) ≪≫
          (DerivedCategory.homologyFunctorFactors _ q).app I)) h0
  refine isIso_properBaseChangeMap_app_of_isKInjective B Λ k f' f l w RF' αF' RF αF I
    (CochainComplex.isKInjective_of_injective I n)
    ⟨J, s', hs', CochainComplex.isKInjective_of_injective J n,
      Stacks.ExactCompDerived.quasiIso_map_of_injective_of_isStrictlyGE F
        (etalePushforwardMod B Λ f) I n
        (fun q => isIso_rightDerivedFunctorPlusComp_app_single_of_torsion B Λ k f' f l w
          (I.homology q) (htors q)) s' n⟩

include w in
/-- **[Stacks, Tag 0F7B].** Consider a commutative diagram of schemes of a big étale site
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
```
with `f` and `f'` proper and `k` and `l` separated and locally quasi-finite (here, as in the
source, locally quasi-finite includes locally of finite type). Let `Λ` be a ring, in the
universe `u` of the site. Functorially in `K ∈ D(X'_étale, Λ)` there is a canonical map
`l_! Rf'_* K ⟶ Rf_*(k_! K)` in `D(Y_étale, Λ)`, namely
`AlgebraicGeometry.SmallEtale.properBaseChangeMap` (for any right derived functors `Rf'_*`, `Rf_*`
of the direct images, with their units). This map is an isomorphism if

* (a) `K` is bounded below and has torsion cohomology sheaves, or
* (b) `Λ` is a torsion ring.

Case (a) is `isIso_properBaseChangeMap_app_of_isGE`, case (b)
`isIso_properBaseChangeMap_of_natCast_eq_zero`. -/
@[stacks 0F7B]
theorem isIso_properBaseChangeMap_app (K : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ))
    (hK : (∃ n : ℤ, K.IsGE n ∧ moduleTorsionCohomologyProperty.{u, u, w, u} B X' Λ K) ∨
      ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    IsIso ((properBaseChangeMap B Λ k f' f l w RF' αF' RF αF).app K) := by
  rcases hK with ⟨n, hn, hK⟩ | ⟨m, hm, hΛ⟩
  · exact isIso_properBaseChangeMap_app_of_isGE B Λ k f' f l w RF' αF' RF αF K n hK
  · have := isIso_properBaseChangeMap_of_natCast_eq_zero B Λ k f' f l w RF' αF' RF αF m hm hΛ
    infer_instance

end Derived

end AlgebraicGeometry.SmallEtale

end
