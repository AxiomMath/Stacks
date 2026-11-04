module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectBounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectFlatStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfUnderlyingAbelian

/-!
# `RΓ(Y, K)` is perfect for `K` in `D_ctf` on a proper scheme of dimension at most one

Let `Ω` be an algebraically closed field, `Y` a scheme proper over `Spec Ω` whose underlying space
has Krull dimension at most one (possibly reducible, non-reduced, not projective), `Λ` a finite
ring, not necessarily commutative, and `K` an object of `D⁺(Y_étale, Λ)` lying in
`D_ctf(Y_étale, Λ)`. Then `RΓ(Y, K)` is a perfect complex of `Λ`-modules.

This is the argument of [Stacks, Tag 03TV] with the curve replaced by any proper scheme of
dimension at most one over an algebraically closed field: the only geometric inputs of that proof
are the vanishing of the cohomology of torsion sheaves above degree two (Tag 0A53) and the
finiteness of the cohomology of constructible sheaves on a proper scheme (Tag 0A57), and both hold
in the generality of Situation 0A52 (`Stacks.EtaleCohomology.TorsionSheafSituation`): separated of
finite type and of dimension at most one over an algebraically closed field.

`Y` is quasi-compact and quasi-separated, so `K` is represented by a bounded complex `C` of
constructible flat sheaves (`Stacks.EtaleCohomology.isCtf_iff_of_qcqs`). By the stupid truncations
of `C` (`StacksDraft.Perfect.isPerfect_rightDerivedFunctorPlus_of_bounded`) it suffices to treat a
single sheaf `G` with finite projective stalks and constructible underlying abelian sheaf. With an
injective resolution `G[0] ⟶ I`, the cohomology of `Γ(Y, I)` lives in degrees `[0, 2]` and is
finite, and `Tot(R ⊗[Λ] Γ(Y, I))` vanishes in degree `-1` for the truncated finite free
resolutions `R` of the finite right modules, by dimension shifting into the cohomology above
degree two of a torsion sheaf; the Tor criterion
`StacksDraft.Perfect.TorTotal.isPerfect_of_isZero_homology_mapBifunctor` concludes.

## Main results

* `Stacks.SheafTwist.isZero_homology_mapBifunctor_moduleSections_of_dimLEOne`: the Tor vanishing.
* `Stacks.SheafTwist.isPerfect_etaleModuleDerivedGlobalSections_single_of_dimLEOne`: the case of a
  single sheaf.
* `Stacks.EtaleCohomology.isPerfect_etaleModuleDerivedGlobalSections_of_isCtf_of_dimLEOne`:
  `RΓ(Y, K)` is perfect.
* `isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf_of_dimLEOne` (in
  `Stacks.EtaleCohomology`):
  the same for `RΓ(X_{k̄}, K|_{X_{k̄}})`, with `X` proper of dimension at most one over any
  field `k` and `k̄` algebraically closed and algebraic over `k`.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
* [Stacks Project, Tag 0A57](https://stacks.math.columbia.edu/tag/0A57)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Abelian HomologicalComplex
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe u r

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ] [Finite Λ] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {Y : Scheme.{u}} (f : Y ⟶ Spec (.of Ω))

/-- Torsion abelian sheaves on `Y` have no cohomology above degree two (Tag 0A53). -/
private lemma subsingleton_ext_of_torsionSheafProperty [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim Y ≤ 1)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}}
    (hF : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology F) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r} Y) F q) :=
  ({ k := Ω, X := Y, structureMorphism := f, dimension_le_one := hdim, F := F,
     isTorsion := hF } : Stacks.EtaleCohomology.TorsionSheafSituation.{u, r}
    ).isVanishingAboveDegreeTwo q hq

section Vanishing

variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (hdim : topologicalKrullDim Y ≤ 1)

include f hdim in
/-- **The cohomology of a sheaf of modules on `Y` vanishes above degree two** (Tag 0A53), for `Y`
separated of finite type and of dimension at most one over an algebraically closed field. -/
lemma subsingleton_ext_sheafForget_of_dimLEOne
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((Stacks.EtaleResolution.sheafForget Λ Y).obj G) q) := by
  have h : Subsingleton (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj G)
        q) :=
    subsingleton_ext_of_torsionSheafProperty f hdim (torsionSheafProperty_forget₂ G) q hq
  exact (Stacks.EtaleResolution.injective_comp_mk₀_hom (sheafForgetIsoForget₂ G) q).subsingleton

include f hdim in
/-- **The cycles of the twist complex on `Y` have no cohomology above degree two**: they are
torsion, so Tag 0A53 applies. -/
lemma subsingleton_ext_twistComplex_cycles_of_dimLEOne
    (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ)
    (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ)
    [HasMapBifunctor R I (twist.{u, r} D Y) (ComplexShape.up ℤ)] (n : ℤ) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((twistComplex D Y R I).cycles n) q) :=
  subsingleton_ext_of_torsionSheafProperty f hdim
    (torsionSheafProperty_twistComplex_cycles D _ R I n) q hq

include f hdim in
/-- **The Tor vanishing for the global sections of an injective resolution on `Y`**, for `Y`
separated of finite type and of dimension at most one over an algebraically closed field. Let `G`
have finite projective stalks and let `G[0] ⟶ I` be an injective resolution. For a complex `R` of
finite free right `Λ`-modules concentrated in degrees `[e, c]` with `e + 3 ≤ -1`, exact in the
degrees `p > e` other than `0`, the total complex `Tot(R ⊗[Λ] Γ(Y, I))` has no cohomology in
degree `-1`. -/
theorem isZero_homology_mapBifunctor_moduleSections_of_dimLEOne
    (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ)
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y)
    (hG : ∀ y : Y,
      Module.Finite Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G))
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ) [∀ n, Injective (I.X n)]
    (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G ⟶ I) [QuasiIso ι]
    (R : CochainComplex (ModuleCat.{max (u + 1) r} (MulOpposite Λ)) ℤ) (e c : ℤ)
    (hb : ∀ p, p < e ∨ c < p → IsZero (R.X p))
    (hfree : ∀ p, Module.Finite (MulOpposite Λ) (R.X p) ∧ Module.Free (MulOpposite Λ) (R.X p))
    (hR : ∀ p, e < p → p ≠ 0 → R.ExactAt p) (he : e + 3 ≤ -1)
    [HasMapBifunctor R (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      D.ordinary (ComplexShape.up ℤ)] :
    IsZero ((mapBifunctor R (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      D.ordinary (ComplexShape.up ℤ)).homology (-1)) := by
  let R' := liftComplex.{u} R hfree
  let M' := ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have h' : ∀ p, p < e ∨ c < p → IsZero (R'.X p) := fun p hp =>
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ)) _
      (hb p hp)
  let K := ((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj R' |>.obj I
  have : HasMapBifunctor R' I (twist.{u, r} D Y) (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ (finite_support_of_columnBounds K e c fun p hp =>
      isZero_of_forall_isZero_X fun q => ((twist.{u, r} D Y).map_isZero (h' p hp)).obj (I.X q))
  have : HasMapBifunctor R' M' (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary)
      (ComplexShape.up ℤ) := ‹HasMapBifunctor R M' D.ordinary (ComplexShape.up ℤ)›
  have : (HomologicalComplex₂.TotalMap.mapBicomplex (Stacks.EtaleSections.sections.{r, u} Y)
      K).HasTotal (ComplexShape.up ℤ) := HomologicalComplex₂.hasTotal_of_finite _ _
    (finite_support_of_columnBounds _ e c (fun p hp => isZero_of_forall_isZero_X fun q =>
      (Stacks.EtaleSections.sections.{r, u} Y).map_isZero
        (((twist.{u, r} D Y).map_isZero (h' p hp)).obj (I.X q))))
  let T := twistComplex D Y R' I
  let eX : ((forget₂ (ModuleCat.{max (u + 1) r} ℤ)
      AddCommGrpCat.{max (u + 1) r}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (mapBifunctor R' M' (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary)
          (ComplexShape.up ℤ)) ≅
      StacksDraft.DimensionShift.homComplex (Stacks.EtaleSections.zSheaf.{r} Y) T :=
    (sectionsTwistComplexIso D Y R' I e c h').symm ≪≫
      Stacks.EtaleSections.sectionsComplexIso.{r} Y T
  -- dimension shifting from degree `e`
  let n := (-2 - e).toNat
  have hn : e + 1 + (n : ℤ) = -1 := by omega
  obtain ⟨φ, hφ⟩ := StacksDraft.DimensionShift.exists_injective_homology_ext
    (Stacks.EtaleSections.zSheaf.{r} Y) n T e
    (fun k hk => exactAt_twistComplex D Y R' e c h' G hG I ι (e + 1 + k) (by omega)
      (hR (e + 1 + k) (by omega) (by omega)))
    (fun k _ q => subsingleton_ext_twistComplex_X.{max (u + 1) r} Y D R' I e c h' (e + k) q)
  have hsub := subsingleton_ext_twistComplex_cycles_of_dimLEOne f hdim D R' I e (n + 1) (by omega)
  have hz : IsZero ((StacksDraft.DimensionShift.homComplex
      (Stacks.EtaleSections.zSheaf.{r} Y) T).homology (-1)) := by
    rw [← hn]
    have := hφ.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hz' := hz.of_iso (HomologicalComplex.homologyMapIso eX (-1))
  rw [← exactAt_iff_isZero_homology] at hz' ⊢
  exact (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r})).1 hz'

end Vanishing

section Proper

variable [IsProper f] (hdim : topologicalKrullDim Y ≤ 1)

include f hdim in
/-- **The cohomology of a constructible sheaf of modules on `Y` is finite** (Tag 0A57), for `Y`
proper and of dimension at most one over an algebraically closed field. -/
lemma finite_ext_sheafForget_of_dimLEOne (B : BigEtaleSite.{u}) (hY : B.Contains Y)
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y)
    (hcon : Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf.{u, r} B Y hY
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ)
        AddCommGrpCat.{max (u + 1) r})).obj G))
    (q : ℕ) :
    Finite (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((Stacks.EtaleResolution.sheafForget Λ Y).obj G) q) := by
  have h : Finite (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj G)
        q) :=
    ({ k := Ω, X := Y, structureMorphism := f, dimension_le_one := hdim,
       F := _, isTorsion := torsionSheafProperty_forget₂ G } :
      Stacks.EtaleCohomology.TorsionSheafSituation.{u, r}).finiteCohomologyOfIsProper B hY
        ‹IsProper f› hcon q
  exact Finite.of_injective _ (Stacks.EtaleResolution.injective_comp_mk₀_hom
    (sheafForgetIsoForget₂ G) q)

attribute [local instance] HasDerivedCategory.standard

include f hdim in
/-- **`RΓ(Y, G)` is perfect** for a sheaf `G` of modules over the finite ring `Λ` on a scheme `Y`
proper and of dimension at most one over an algebraically closed field, when the stalks of `G`
are finite projective and its underlying abelian sheaf is constructible. -/
theorem isPerfect_etaleModuleDerivedGlobalSections_single_of_dimLEOne
    (B : BigEtaleSite.{u}) (hY : B.Contains Y)
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y)
    (hG : ∀ y : Y,
      Module.Finite Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G))
    (hcon : Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf.{u, r} B Y hY
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ)
        AddCommGrpCat.{max (u + 1) r})).obj G)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((Stacks.EtaleCohomology.etaleModuleDerivedGlobalSections.{u, r} Λ Y).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  have := Stacks.EtaleCohomology.etaleModules_enoughInjectives.{u, r} Λ Y
  obtain ⟨Ires, -, hge⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    ((CochainComplex.singleFunctor (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) 0).obj G)
  let I := Ires.cocomplex
  have : I.IsStrictlyGE 0 := hge
  let D := StacksDraft.Perfect.balancedDerivedTensoring.{r, max (u + 1) r} Λ
  let M' := ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hpos : ∀ n : ℕ, Finite (M'.homology ((n : ℤ) + 1)) ∧
      (2 ≤ n → Subsingleton (M'.homology ((n : ℤ) + 1))) := by
    intro n
    obtain ⟨φ, hφ⟩ :=
      Stacks.EtaleResolution.exists_injective_homology_sections.{max (u + 1) r, u, r}
      Λ Y G I Ires.ι n
    let e := homologyGlobalSectionsForgetIso (Λ := Λ) I ((n : ℤ) + 1)
    refine ⟨?_, fun hn => ?_⟩
    · have := finite_ext_sheafForget_of_dimLEOne f hdim B hY G hcon (n + 1)
      have := Finite.of_injective φ hφ
      exact Finite.of_equiv _ e.addCommGroupIsoToAddEquiv.toEquiv
    · have := subsingleton_ext_sheafForget_of_dimLEOne f hdim G (n + 1) (by omega)
      have := hφ.subsingleton
      exact e.addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj M') := by
    refine isPerfect_of_isZero_homology_mapBifunctor D M' 0 2
      (fun i hi => isZero_homology_moduleSections_of_neg I i hi) (fun i hi => ?_) (fun i => ?_) 3
      (fun R e c hb hfree hR he _ => isZero_homology_mapBifunctor_moduleSections_of_dimLEOne f hdim
        D G hG I Ires.ι R e c hb hfree hR (by omega))
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
      exact ModuleCat.isZero_iff_subsingleton.2 ((hpos n).2 (by omega))
    · rcases lt_trichotomy i 0 with hi | rfl | hi
      · have := ModuleCat.isZero_iff_subsingleton.1 (isZero_homology_moduleSections_of_neg I i hi)
        exact Module.Finite.of_finite
      · have := finite_homology_zero_moduleSections G I Ires.ι
          (finite_moduleSections_of_finite_ext G
            (finite_ext_sheafForget_of_dimLEOne f hdim B hY G hcon 0))
        exact Module.Finite.of_finite
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
        have := (hpos n).1
        exact Module.Finite.of_finite
  refine StacksDraft.Perfect.isPerfect_of_iso
    (Functor.rightDerivedFunctorPlusInjectiveResolutionIso
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y) G Ires ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology _
          (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y)) (ComplexShape.up ℤ)).app I)) hperf

end Proper

end Stacks.SheafTwist

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **`RΓ(Y, K)` is perfect for `K ∈ D_ctf` on a proper scheme of dimension at most one.** Let
`Ω` be an algebraically closed field, `Y` a scheme proper over `Spec Ω` with
`dim Y ≤ 1` (not necessarily reduced, irreducible or projective), `Λ` a finite ring, not
necessarily commutative, and `K ∈ D⁺(Y_étale, Λ)` lying in `D_ctf(Y_étale, Λ)`. Then the derived
global sections `RΓ(Y, K)` form a perfect complex of `Λ`-modules. This is the argument of
[Stacks, Tag 03TV] for an arbitrary such `Y`. -/
theorem isPerfect_etaleModuleDerivedGlobalSections_of_isCtf_of_dimLEOne
    (B : BigEtaleSite.{u}) (Y : B.Scheme) (Λ : Type r) [Ring Λ] [Finite Λ]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (f : Y.obj ⟶ Spec (.of Ω)) [IsProper f]
    (hdim : topologicalKrullDim Y.obj ≤ 1)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y.obj))
    (hK : IsCtf.{u, r} B Y Λ (DerivedCategory.Plus.ι.obj K)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ Y.obj).obj K)) := by
  have : CompactSpace Y.obj :=
    @QuasiCompact.compactSpace_of_compactSpace Y.obj (Spec (.of Ω)) f inferInstance inferInstance
  have : QuasiSeparatedSpace Y.obj :=
    @quasiSeparatedSpace_of_quasiSeparated Y.obj (Spec (.of Ω)) f
      (quasiSeparatedSpace_of_isAffine (Spec (.of Ω))) inferInstance
  obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := (isCtf_iff_of_qcqs B Λ _).1 hK
  -- `K` is the class of the bounded complex `C`
  let eL : DerivedCategory.Plus.Qh.obj (Functor.plusObj C ⟨a, ha⟩) ≅ K :=
    DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.quotientCompQhIso _).app C ≪≫ e)
  refine StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, r} Λ Y.obj).mapIso eL.symm)) ?_
  let good : EtaleModules.{u, r} Λ Y.obj → Prop := fun G =>
    IsConstructibleFlatEtaleModule B Y Λ G ∧ ∀ y : Y.obj,
      Module.Finite Λ (((Stacks.SheafTwist.geometricSitePoint.{u, r} Y.obj y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((Stacks.SheafTwist.geometricSitePoint.{u, r} Y.obj y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G)
  have := etaleModules_enoughInjectives.{u, r} Λ Y.obj
  refine StacksDraft.Perfect.isPerfect_rightDerivedFunctorPlus_of_bounded
    (etaleModuleGlobalSections.{u, r} Λ Y.obj) good (fun {G G'} eG hG => ⟨hG.1.of_iso B Y Λ eG,
      fun y => Stacks.SheafTwist.finite_projective_sheafFiber_of_iso Y.obj y eG (hG.2 y)⟩)
    (fun G hG => Stacks.SheafTwist.isPerfect_etaleModuleDerivedGlobalSections_single_of_dimLEOne
      f hdim B Y.property G hG.2
      (AlgebraicGeometry.isConstructibleAbelianSheaf_forget₂_of_isConstructibleFlatModuleSheaf B Λ
        Y _ hG.1)) C a b (fun i => ⟨hC i,
      Stacks.SheafTwist.finite_projective_sheafFiber_of_isConstructibleFlat B Y Λ C hC i⟩)

/-- **`RΓ(X_{k̄}, K)` is perfect for `K ∈ D_ctf` on a proper scheme of dimension at most one.**
Let `X` be a scheme proper over a field `k` with `dim X ≤ 1` (not necessarily reduced,
irreducible or projective), `k̄` an algebraically closed field algebraic over `k`, `Λ` a finite
ring, not necessarily commutative, and `K ∈ D_ctf(X_étale, Λ)`. Then the derived global sections
of the restriction of `K` to `X_{k̄}` form a perfect complex of `Λ`-modules. This is
[Stacks, Tag 03TV] without the hypothesis that `X` is a projective curve. -/
theorem isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf_of_dimLEOne
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ] [Finite Λ] {k : Type u} [Field k]
    (gk : X.obj ⟶ Spec (.of k)) [IsProper gk] (hdim : topologicalKrullDim X.obj ≤ 1)
    (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj K)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk gk) kbar)).obj
        ((etaleModuleInverseImage.{u, r} Λ
          (Stacks.Frobenius.fieldBaseChangeProj (Over.mk gk) kbar)).mapDerivedCategoryPlus.obj
            K))) := by
  have hY : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk gk) kbar) :=
    ProjectiveCurveBaseChange.contains_fieldBaseChange gk kbar B X.property inferInstance
      inferInstance
  let Y' : B.Scheme := B.obj _ hY
  let f : Y' ⟶ X := ObjectProperty.homMk (Stacks.Frobenius.fieldBaseChangeProj (Over.mk gk) kbar)
  have : IsProper (pullback.snd (Over.mk gk).hom (Stacks.Frobenius.specAlgebraMap k kbar)) :=
    inferInstanceAs (IsProper (pullback.snd gk _))
  have hd : topologicalKrullDim Y'.obj ≤ 1 :=
    (topologicalKrullDim_pullback_spec_algebraMap k kbar gk).trans_le hdim
  let F := etaleModuleInverseImage.{u, r} Λ (Stacks.Frobenius.fieldBaseChangeProj (Over.mk gk) kbar)
  let eF : F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
    ObjectProperty.liftCompιIso (DerivedCategory.TStructure.t.plus) _ _
  exact isPerfect_etaleModuleDerivedGlobalSections_of_isCtf_of_dimLEOne B Y' Λ
    (pullback.snd (Over.mk gk).hom (Stacks.Frobenius.specAlgebraMap k kbar)) hd _
    ((IsCtf.pullback B Λ f hK).of_iso B Y' Λ (eF.app K).symm)

end Stacks.EtaleCohomology

end
