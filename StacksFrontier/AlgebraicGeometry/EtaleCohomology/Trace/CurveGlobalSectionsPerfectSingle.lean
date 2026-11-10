module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectTorVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Homology.Perfect.BalancedDerivedTensor
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# `RΓ(X_{k̄}, G)` is perfect for a single sheaf with finite projective stalks

Let `X` be a projective curve over a field `k`, `k̄` an algebraically closed extension,
`Y = X_{k̄}` and `Λ` a finite ring, not necessarily commutative. For a sheaf `G` of `Λ`-modules
on the small étale site of `Y` whose stalks are finite projective and whose underlying abelian
sheaf is constructible, `RΓ(Y, G)` is a perfect complex of `Λ`-modules. With an injective
resolution `G[0] ⟶ I`, the complex `M = Γ(Y, I)` has cohomology in degrees `[0, 2]` (Tag 0A53),
finite in each degree (Tag 0A57), and `Tot(R ⊗[Λ] M)` vanishes in degree `-1` for the
truncated finite free resolutions `R` of the finite right modules; the Tor criterion
`StacksDraft.Perfect.TorTotal.isPerfect_of_isZero_homology_mapBifunctor` concludes. This is the
case of a single sheaf in the proof of [Stacks, Tag 03TV].

## Main results

* `Stacks.SheafTwist.isPerfect_etaleModuleDerivedGlobalSections_single`: `RΓ(X_{k̄}, G)` is
  perfect.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
* [Stacks Project, Tag 0A57](https://stacks.math.columbia.edu/tag/0A57)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Abelian HomologicalComplex
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe u r

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] (hcurve : IsCurve k g)

/-- The underlying abelian sheaf of a sheaf of modules over a finite ring is torsion: it is
killed by `|Λ|`. -/
lemma torsionSheafProperty_forget₂ {Y : Scheme.{u}}
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj G) := by
  intro U x
  refine ⟨⊤, Y.smallEtaleTopology.top_mem U, fun V f _ => ⟨Nat.card Λ, Nat.card_pos, ?_⟩⟩
  have hc : (Nat.card Λ : Λ) = 0 := by rw [← nsmul_one, card_nsmul_eq_zero']
  change Nat.card Λ • (G.obj.map f.op).hom x = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, hc, zero_smul]

/-- Forgetting a sheaf of `Λ`-modules to abelian groups through `ℤ`-modules or directly gives
the same abelian sheaf. -/
def sheafForgetIsoForget₂ {Y : Scheme.{u}} (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    (Stacks.EtaleResolution.sheafForget Λ Y).obj G ≅
      (sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj G :=
  (sheafComposeIso Y (Iso.refl _ :
    Stacks.EtaleResolution.forgetAb.{u + 1} Λ ≅
      forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).app G

include hcurve in
/-- **The cohomology of a sheaf of modules on `X_{k̄}` vanishes above degree two** (Tag 0A53). -/
lemma subsingleton_ext_sheafForget
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar)) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r}
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
      ((Stacks.EtaleResolution.sheafForget Λ _).obj G) q) := by
  have h : Subsingleton (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r}
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj G)
        q) :=
    (Stacks.EtaleCohomology.ProjectiveCurveBaseChange.torsionSheafSituation.{r} g kbar hcurve _
      (torsionSheafProperty_forget₂ G)).isVanishingAboveDegreeTwo q hq
  exact (Stacks.EtaleResolution.injective_comp_mk₀_hom (sheafForgetIsoForget₂ G) q).subsingleton

include hcurve in
/-- **The cohomology of a constructible sheaf of modules on `X_{k̄}` is finite** (Tag 0A57). -/
lemma finite_ext_sheafForget (hproj : IsProjective g) (B : BigEtaleSite.{u})
    (hY : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
    (hcon : Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf.{u, r} B _ hY
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ)
        AddCommGrpCat.{max (u + 1) r})).obj G))
    (q : ℕ) :
    Finite (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r}
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
      ((Stacks.EtaleResolution.sheafForget Λ _).obj G) q) := by
  have h : Finite (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r}
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).obj G)
        q) :=
    (Stacks.EtaleCohomology.ProjectiveCurveBaseChange.torsionSheafSituation.{r} g kbar hcurve _
      (torsionSheafProperty_forget₂ G)).finiteCohomologyOfIsProper B hY
        (Stacks.EtaleCohomology.ProjectiveCurveBaseChange.isProper_of_iso (Iso.refl _) hproj)
        hcon q
  exact Finite.of_injective _ (Stacks.EtaleResolution.injective_comp_mk₀_hom
    (sheafForgetIsoForget₂ G) q)

/-! ### The cohomology of the global sections of a resolution -/

section Sections

variable {Y : Scheme.{u}} (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y)
  (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ) [I.IsStrictlyGE 0]
  [∀ n, Injective (I.X n)]
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G ⟶ I) [QuasiIso ι]

/-- Sections over `Y` of sheaves of modules are left exact. -/
instance preservesFiniteLimits_moduleSections (Y : Scheme.{u}) :
    PreservesFiniteLimits (moduleSections.{u, r} (Λ := Λ) Y) :=
  have : PreservesFiniteLimits (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 Y)))) := comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_natIso (Iso.refl _)

omit [Finite Λ] [∀ n, Injective (I.X n)] in
/-- The global sections of `I` vanish in negative degrees. -/
lemma isZero_homology_moduleSections_of_neg (i : ℤ) (hi : i < 0) :
    IsZero ((((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((moduleSections Y).map_isZero (I.isZero_of_isStrictlyGE 0 i hi))

/-- `Hⁿ⁺¹(Γ(Y, I))`, read in abelian groups, through the global sections functor of Mathlib and
through the sections over the terminal object. -/
def homologyGlobalSectionsForgetIso (n : ℤ) :
    (((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y ⋙
        Stacks.EtaleResolution.forgetAb.{u + 1} Λ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).homology n ≅
      (Stacks.EtaleResolution.forgetAb.{u + 1} Λ).obj
        ((((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology n) :=
  HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections
      Y.smallEtaleTopology _ (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y))
        (Stacks.EtaleResolution.forgetAb.{u + 1} Λ)) (ComplexShape.up ℤ)).app I ≪≫
      (Functor.mapHomologicalComplexCompIso (F := moduleSections Y)
        (G := Stacks.EtaleResolution.forgetAb.{u + 1} Λ) (Iso.refl _)
          (ComplexShape.up ℤ)).symm.app I) n ≪≫
    ((((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).sc n).mapHomologyIso
      (Stacks.EtaleResolution.forgetAb.{u + 1} Λ)

omit [Finite Λ] [∀ n, Injective (I.X n)] in
include ι in
/-- **`H⁰(Γ(Y, I))` is finite when `Γ(Y, G)` is**: sections are left exact, so the cycles of
`Γ(Y, I)` in degree `0` are the sections of the cycles `G` of `I`. -/
lemma finite_homology_zero_moduleSections (hG : Finite ((moduleSections Y).obj G)) :
    Finite ((((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology 0) := by
  let M' := ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hd : M'.d ((ComplexShape.up ℤ).prev 0) 0 = 0 :=
    ((moduleSections Y).map_isZero (I.isZero_of_isStrictlyGE 0 _ (by simp))).eq_of_src _ _
  have hdI : I.d ((ComplexShape.up ℤ).prev 0) 0 = 0 :=
    (I.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _
  let eG : I.cycles 0 ≅ G :=
    I.isoHomologyπ _ 0 rfl hdI ≪≫ (asIso (homologyMap ι 0)).symm ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ 0 G
  have hSex : (ShortComplex.mk (I.iCycles 0) (I.d 0 1) (by simp)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (I.cyclesIsKernel 0 1 (by simp))
  have := preservesFiniteLimits_moduleSections.{u, r} (Λ := Λ) Y
  have hex := hSex.map_of_mono_of_preservesKernel (moduleSections Y)
    (inferInstanceAs (Mono (I.iCycles 0))) inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hfinC : Finite ((moduleSections Y).obj (I.cycles 0)) :=
    Finite.of_equiv _ ((moduleSections Y).mapIso eG).symm.toLinearEquiv.toEquiv
  have hlift : ∀ z : M'.cycles 0, ∃ y : (moduleSections Y).obj (I.cycles 0),
      ((moduleSections Y).map (I.iCycles 0)).hom y = (M'.iCycles 0).hom z := fun z =>
    hex _ (ConcreteCategory.congr_hom (M'.iCycles_d 0 1) z)
  choose φ hφ using hlift
  have hinj : Function.Injective φ := fun a b hab =>
    (ModuleCat.mono_iff_injective (M'.iCycles 0)).1 inferInstance (by rw [← hφ a, ← hφ b, hab])
  have := Finite.of_injective φ hinj
  exact Finite.of_equiv _ (M'.isoHomologyπ _ 0 rfl hd).toLinearEquiv.toEquiv

omit [Finite Λ] in
/-- The sections over `Y` of a sheaf of modules are finite when its underlying abelian sheaf has
finite `H⁰`. -/
lemma finite_moduleSections_of_finite_ext
    (h : Finite (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r} Y)
      ((Stacks.EtaleResolution.sheafForget Λ Y).obj G) 0)) :
    Finite ((moduleSections Y).obj G) := by
  have : Finite (Stacks.EtaleSections.zSheaf.{r} Y ⟶
      (Stacks.EtaleResolution.sheafForget Λ Y).obj G) :=
    Finite.of_equiv _ Ext.homEquiv₀
  have : Finite ((preadditiveCoyoneda.obj (op (Stacks.EtaleSections.zSheaf.{r} Y))).obj
      ((Stacks.EtaleResolution.sheafForget Λ Y).obj G)) := this
  exact Finite.of_equiv _ ((Stacks.EtaleSections.sectionsIso.{r} Y).app
    ((Stacks.EtaleResolution.sheafForget Λ Y).obj G)).symm.addCommGroupIsoToAddEquiv.toEquiv

end Sections

/-! ### Perfectness for a single sheaf -/

attribute [local instance] HasDerivedCategory.standard

include hcurve in
/-- **`RΓ(X_{k̄}, G)` is perfect** for a sheaf `G` of modules over the finite ring `Λ` on the
base change `X_{k̄}` of a projective curve to an algebraically closed field, when the stalks of `G`
are finite projective and its underlying abelian sheaf is constructible. -/
theorem isPerfect_etaleModuleDerivedGlobalSections_single (hproj : IsProjective g)
    (B : BigEtaleSite.{u}) (hY : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
    (hG : ∀ y : Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar,
      Module.Finite Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G))
    (hcon : Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf.{u, r} B _ hY
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r} Λ)
        AddCommGrpCat.{max (u + 1) r})).obj G)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((Stacks.EtaleCohomology.etaleModuleDerivedGlobalSections.{u, r} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  let Y := Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar
  have := Stacks.EtaleCohomology.etaleModules_enoughInjectives.{u, r} Λ Y
  obtain ⟨Ires, -, hge⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    ((CochainComplex.singleFunctor (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) 0).obj G)
  let I := Ires.cocomplex
  have : I.IsStrictlyGE 0 := hge
  let D := StacksDraft.Perfect.balancedDerivedTensoring.{r, max (u + 1) r} Λ
  let M' := ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hpos : ∀ i : ℤ, 0 < i → Finite (M'.homology i) ∧
      (3 ≤ i → Subsingleton (M'.homology i)) := by
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    obtain ⟨f, hf⟩ :=
      Stacks.EtaleResolution.exists_injective_homology_sections.{max (u + 1) r, u, r}
      Λ Y G I Ires.ι n
    let e := homologyGlobalSectionsForgetIso (Λ := Λ) I ((n : ℤ) + 1)
    refine ⟨?_, fun hn => ?_⟩
    · have := finite_ext_sheafForget g kbar hcurve hproj B hY G hcon (n + 1)
      have := Finite.of_injective f hf
      exact Finite.of_equiv _ e.addCommGroupIsoToAddEquiv.toEquiv
    · have := subsingleton_ext_sheafForget g kbar hcurve G (n + 1) (by omega)
      have := hf.subsingleton
      exact e.addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj M') := by
    refine isPerfect_of_isZero_homology_mapBifunctor D M' 0 2
      (fun i hi => isZero_homology_moduleSections_of_neg I i hi) (fun i hi => ?_) (fun i => ?_) 3
      (fun R e c hb hfree hR he _ => isZero_homology_mapBifunctor_moduleSections D g kbar hcurve
        G hG I Ires.ι R e c hb hfree hR (by omega))
    · exact ModuleCat.isZero_iff_subsingleton.2 ((hpos i (by omega)).2 (by omega))
    · rcases lt_trichotomy i 0 with hi | rfl | hi
      · have := ModuleCat.isZero_iff_subsingleton.1 (isZero_homology_moduleSections_of_neg I i hi)
        exact Module.Finite.of_finite
      · have := finite_homology_zero_moduleSections G I Ires.ι
          (finite_moduleSections_of_finite_ext G
            (finite_ext_sheafForget g kbar hcurve hproj B hY G hcon 0))
        exact Module.Finite.of_finite
      · have := (hpos i hi).1
        exact Module.Finite.of_finite
  refine StacksDraft.Perfect.isPerfect_of_iso
    (Functor.rightDerivedFunctorPlusInjectiveResolutionIso
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y) G Ires ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology _
          (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y)) (ComplexShape.up ℤ)).app I)) hperf

end Stacks.SheafTwist

end
