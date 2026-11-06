module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeCompatibleFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeTransfer
public import StacksFrontier.CategoryTheory.Adjunction.PushTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.GrothendieckExistenceSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCoherentEquivalence
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The thickenings of a space over `Spec R`, as a tower over `S`

Let `X` be an algebraic space over `S` with a morphism `π : X ⟶ Spec R`, `R` a ring with an
ideal `I`.  A *tower of thickenings* of `X` (`AlgebraicGeometry.Space.SiteChangeTower`) is a
family of cartesian squares

```
Z_n --i_n--> X
 |           | π
T_n --ι_n--> Spec R
```

with `T_n ≅ Spec(R / I^{n+1})` over `Spec R`, and morphisms `s_n : Z_n ⟶ Z_{n+1}` with
`s_n ≫ i_{n+1} = i_n`.  For `R` Noetherian and `I`-adically complete, Stacks 08B9 read on `X`
says that a morphism `G ⟶ F` of coherent `𝒪_X`-modules with support proper over `Spec R` is the
same as a compatible family of morphisms `i_n^* G ⟶ i_n^* F`
(`AlgebraicGeometry.Space.SiteChangeTower.existsUnique_hom_of_compatible`).

## References

* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite


universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (.of R))} {h : B.obj hR ⟶ B.obj hS}

/-- **A tower of thickenings of a space over `Spec R`**: base changes `i_n : Z_n ⟶ X` of the
thickenings `Spec(R / I^{n+1}) ⟶ Spec R` along `π : X ⟶ Spec R`, with transitions
`s_n : Z_n ⟶ Z_{n+1}` over `X`. -/
structure SiteChangeTower (X : AlgebraicSpaces B S hS) (π : X ⟶ schemeSpace (Over.mk h))
    (I : Ideal R) (Z : ℕ → AlgebraicSpaces B S hS) (i : ∀ n, Z n ⟶ X)
    (s : ∀ n, Z n ⟶ Z (n + 1)) (T : ℕ → BigFppfOver B S hS) (ι : ∀ n, T n ⟶ Over.mk h)
    (p : ∀ n, Z n ⟶ schemeSpace (T n)) : Prop where
  /-- The transitions are maps over `X`. -/
  comp : ∀ n, s n ≫ i (n + 1) = i n
  /-- The squares are cartesian. -/
  isPullback : ∀ n, IsPullback (i n) (p n) π (schemeSpaceMap (ι n))
  /-- The thickenings are the spectra of the quotients, compatibly with their maps to
  `Spec R`. -/
  iso : ∀ n, ∃ e : (BigFppfOver.toScheme B S hS).obj (T n) ≅ adicThickening R I n,
    (BigFppfOver.toScheme B S hS).map (ι n) = e.hom ≫ adicThickeningι R I n

/-- A coherent module on an algebraic space is of finite type on its small étale site. -/
private theorem isFiniteTypeOnSite_of_isCoherent (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : IsCoherent B S hS Y.1 Y.2 M) :
    SheafOfModules.IsFiniteTypeOnSite M :=
  let := hM.toIsCoherentOnSite
  isFiniteTypeOnSite_of_isCoherentOnSite B S hS Y M

namespace SiteChangeTower

variable {X : AlgebraicSpaces B S hS} {π : X ⟶ schemeSpace (Over.mk h)} {I : Ideal R}
  {Z : ℕ → AlgebraicSpaces B S hS} {i : ∀ n, Z n ⟶ X} {s : ∀ n, Z n ⟶ Z (n + 1)}
  {T : ℕ → BigFppfOver B S hS} {ι : ∀ n, T n ⟶ Over.mk h} {p : ∀ n, Z n ⟶ schemeSpace (T n)}
  (𝒯 : SiteChangeTower X π I Z i s T ι p)

include 𝒯

/-- The identification of a thickening with the spectrum of the quotient. -/
noncomputable def thickIso (n : ℕ) :
    (BigFppfOver.toScheme B S hS).obj (T n) ≅ adicThickening R I n :=
  (𝒯.iso n).choose

/-- The map `T_n ⟶ Spec R` is `thickIso n` followed by `Spec(R / I^{n+1}) ⟶ Spec R`. -/
theorem thickIso_spec (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map (ι n) = (𝒯.thickIso n).hom ≫ adicThickeningι R I n :=
  (𝒯.iso n).choose_spec

/-- The thickenings `T_n` are affine. -/
theorem isAffine (n : ℕ) : IsAffine ((BigFppfOver.toScheme B S hS).obj (T n)) :=
  IsAffine.of_isIso (𝒯.thickIso n).hom

/-- The maps `ι_n : T_n ⟶ Spec R` are closed immersions. -/
theorem isClosedImmersion_toScheme_map (n : ℕ) :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (ι n)) := by
  rw [𝒯.thickIso_spec n]
  have : AlgebraicGeometry.IsClosedImmersion (adicThickeningι R I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/-- The maps `ι_n : T_n ⟶ Spec R` are surjective on global sections. -/
theorem surjective (n : ℕ) :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map (ι n)).appTop.hom :=
  surjective_appTop_of_eq_comp_adicThickeningι R I n _ (𝒯.thickIso n) (𝒯.thickIso_spec n)

/-- The kernel of `ι_n` on global sections is the image of `I^{n+1}`. -/
theorem ker (n : ℕ) :
    siteMapKer B S hS (ι n) = Ideal.map (Scheme.ΓSpecIso (.of R)).inv.hom (I ^ (n + 1)) :=
  (ker_appTop_of_eq_comp_adicThickeningι R I n _ (𝒯.thickIso n) (𝒯.thickIso_spec n)).trans
    (ker_appTop_adicThickeningι R I n)

/-- The inclusions of a tower are closed immersions. -/
theorem isClosedImmersion_i (n : ℕ) : IsClosedImmersion B S hS (i n).hom :=
  isClosedImmersion_of_isPullback_schemeSpaceMap B S hS π (ι n) (i n) (p n)
    (𝒯.isPullback n) (𝒯.isClosedImmersion_toScheme_map n)

section Quotients

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- `Ψ(i_{n*} i_n^* N) ≅ Ψ N / I^{n+1} Ψ N`. -/
def thickeningIso (N : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    (siteChangeModules B X π).obj
        ((modulePushforward B S hS (i n)).obj ((modulePullback B S hS (i n)).obj N)) ≅
      idealPowerQuotient B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
        (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
        ((siteChangeModules B X π).obj N) :=
  haveI := 𝒯.isAffine n
  siteChangeThickeningIso X π I n (ι n) (i n) (p n) (𝒯.isPullback n)
    (𝒯.isClosedImmersion_toScheme_map n) (𝒯.surjective n) (𝒯.ker n) N

/-- The image under `Ψ` of the unit `N ⟶ i_{n*} i_n^* N`, followed by `thickeningIso`, is the
quotient map `Ψ N ⟶ Ψ N / I^{n+1} Ψ N`. -/
@[reassoc (attr := simp)]
theorem map_unit_thickeningIso_hom (N : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    (siteChangeModules B X π).map ((modulePullbackAdjunction B S hS (i n)).unit.app N) ≫
        (𝒯.thickeningIso N n).hom =
      cokernel.π (idealPowerMultiple B (Spec (.of R)) hR (siteChangeSpace B X π).1
        (siteChangeSpace B X π).2
        (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
        ((siteChangeModules B X π).obj N)).ι :=
  have := 𝒯.isAffine n
  map_unit_siteChangeThickeningIso_hom X π I n (ι n) (i n) (p n) (𝒯.isPullback n)
    (𝒯.isClosedImmersion_toScheme_map n) (𝒯.surjective n) (𝒯.ker n) N

/-- The comparison `i_n^* ≅ i_{n+1}^* ⋙ s_n^*`. -/
def tri (n : ℕ) :
    modulePullback B S hS (i n) ≅
      modulePullback B S hS (i (n + 1)) ⋙ modulePullback B S hS (s n) :=
  modulePullbackTriangle B S hS (𝒯.comp n)

/-- **Stacks 08B9 on a tower of thickenings.**  For coherent `𝒪_X`-modules `F`, `G` with support
proper over `Spec R`, a family of morphisms `α_n : i_n^* G ⟶ i_n^* F` compatible with the
comparisons `i_n^* ≅ s_n^* i_{n+1}^*` comes from a unique morphism `G ⟶ F`. -/
theorem existsUnique_hom_of_compatible [IsNoetherianRing R] [IsAdicComplete I R]
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hπ : IsLocallyOfFiniteType B S hS π.hom) (F G : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) (hG : IsCoherent B S hS X.1 X.2 G)
    (hFp : HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ
      ((SheafOfModules.toSheaf _).obj F))
    (hGp : HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ
      ((SheafOfModules.toSheaf _).obj G))
    (α : ∀ n, (modulePullback B S hS (i n)).obj G ⟶ (modulePullback B S hS (i n)).obj F)
    (hα : ∀ n, α n ≫ (𝒯.tri n).hom.app F =
      (𝒯.tri n).hom.app G ≫ (modulePullback B S hS (s n)).map (α (n + 1))) :
    ∃! ψ : G ⟶ F, ∀ n, (modulePullback B S hS (i n)).map ψ = α n := by
  let adj := fun n => modulePullbackAdjunction B S hS (i n)
  let hf := (isLocallyOfFiniteType_siteChangeStructure_iff X π).2 hπ
  have hft := isFiniteTypeOnSite_of_isCoherent X
  let Q := fun n => (modulePushforward B S hS (i n)).obj ((modulePullback B S hS (i n)).obj F)
  let t : ∀ n, Q (n + 1) ⟶ Q n := fun n =>
    Adjunction.pushTransition (adj n) (adj (n + 1)) (𝒯.tri n)
      ((modulePullback B S hS (i (n + 1))).obj F) ((𝒯.tri n).inv.app F)
  have ht : ∀ n, (adj (n + 1)).unit.app F ≫ t n = (adj n).unit.app F := fun n =>
    Adjunction.unit_comp_pushTransition (adj n) (adj (n + 1)) (𝒯.tri n) F
  let c : ∀ n, G ⟶ Q n := fun n => (adj n).homEquiv G _ (α n)
  have hc : ∀ n, c (n + 1) ≫ t n = c n := fun n => by
    refine (Adjunction.homEquiv_comp_pushTransition (adj n) (adj (n + 1)) (𝒯.tri n)
      ((𝒯.tri n).inv.app F) (α (n + 1))).trans (congrArg ((adj n).homEquiv G _) ?_)
    rw [← Category.assoc, ← hα n, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  obtain ⟨d, hd, hdu⟩ := existsUnique_hom_of_compatible_siteChange X π I hf G F
    ((isCoherent_siteChangeModules_iff X π G).2 hG) ((isCoherent_siteChangeModules_iff X π F).2 hF)
    ((hasProperSupport_siteChangeModules_iff X π hπ G hG.toIsQuasicoherentOnSite (hft G hG)).2 hGp)
    ((hasProperSupport_siteChangeModules_iff X π hπ F hF.toIsQuasicoherentOnSite (hft F hF)).2 hFp)
    Q (fun n => (adj n).unit.app F) (fun n => 𝒯.thickeningIso F n)
    (fun n => 𝒯.map_unit_thickeningIso_hom F n) t ht c hc
  have key : ∀ (e : G ⟶ F) (n : ℕ), e ≫ (adj n).unit.app F = c n ↔
      (modulePullback B S hS (i n)).map e = α n := fun e n => by
    have h1 : e ≫ (adj n).unit.app F =
        (adj n).homEquiv G _ ((modulePullback B S hS (i n)).map e) :=
      ((adj n).unit_naturality e).symm.trans ((adj n).homEquiv_unit _ _ _).symm
    rw [h1]
    exact Equiv.apply_eq_iff_eq _
  exact ⟨d, fun n => (key d n).1 (hd n), fun e he => hdu e fun n => (key e n).2 (he n)⟩

/-- **Support proper over `Spec R` of the direct image of the first level.** -/
theorem hasProperSupport_modulePushforward_zero (hπ : IsLocallyOfFiniteType B S hS π.hom)
    (F₀ : Modules.{u, u} B S hS (Z 0).1 (Z 0).2) (_hF₀ : SheafOfModules.IsFiniteTypeOnSite F₀)
    (hp : IsLocallyOfFiniteType B S hS (p 0).hom)
    (hF₀p : HasProperSupport B S hS (Z 0).2 (schemeSpace (T 0)).2 (p 0).hom hp
      ((SheafOfModules.toSheaf _).obj F₀)) :
    HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS (i 0)).obj F₀)) := by
  obtain ⟨hcl, hprop⟩ := hF₀p
  have hi := 𝒯.isClosedImmersion_i 0
  have hsupp := supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS (i 0) hi
    F₀ hcl
  have hlft : IsLocallyOfFiniteType B S hS ((i 0).hom ≫ π.hom) :=
    isLocallyOfFiniteType_comp' B S hS _ _ X.2 (schemeSpace (Over.mk h)).2
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _ hi) hπ
  have hιc : IsClosedImmersion B S hS (schemeSpaceMap (ι 0)).hom :=
    (presheaf_yoneda_map_iff B S hS inferInstance _).2 (𝒯.isClosedImmersion_toScheme_map 0)
  have hw : (i 0).hom ≫ π.hom = (p 0).hom ≫ (schemeSpaceMap (ι 0)).hom :=
    congrArg (fun q => q.hom) (𝒯.isPullback 0).w
  have hprop' : IsProperOver B S hS (Z 0).2 (schemeSpace (Over.mk h)).2
      ((i 0).hom ≫ π.hom) hlft _ hcl := by
    show IsProper B S hS (_ ≫ ((i 0).hom ≫ π.hom))
    rw [hw, ← Category.assoc]
    exact isProper_comp' B S hS _ _ (schemeSpace (T 0)).2 (schemeSpace (Over.mk h)).2 hprop
      (isProper_of_isClosedImmersion B S hS (schemeSpace (T 0)).2 (schemeSpace (Over.mk h)).2 _
        hιc)
  have himg := isProperOver_image_of_universallyClosed B S hS (Z 0).2 X.2
    (schemeSpace (Over.mk h)).2 (i 0).hom π.hom
    (universallyClosed_of_isClosedImmersion B S hS (Z 0).2 X.2 _ hi) hlft hπ _ hcl hprop'
  unfold HasProperSupport
  rw [hsupp]
  exact ⟨_, himg⟩


end Quotients

/-- **Stacks 08B9 on a tower, against fixed levels.**  For coherent `𝒪_X`-modules `F`, `G` with
support proper over `Spec R` and identifications `ρ_n : i_n^* F ≅ L_n`, `μ_n : i_n^* G ⟶ L_n`
compatible with transitions `τ_n : s_n^* L_{n+1} ⟶ L_n`, there is a unique `ψ : G ⟶ F` with
`i_n^* ψ ≫ ρ_n = μ_n`. -/
theorem existsUnique_hom_of_compatible_levels [IsNoetherianRing R] [IsAdicComplete I R]
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hπ : IsLocallyOfFiniteType B S hS π.hom) (F G : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) (hG : IsCoherent B S hS X.1 X.2 G)
    (hFp : HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ
      ((SheafOfModules.toSheaf _).obj F))
    (hGp : HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ
      ((SheafOfModules.toSheaf _).obj G))
    (L : ∀ n, Modules.{u, u} B S hS (Z n).1 (Z n).2)
    (τ : ∀ n, (modulePullback B S hS (s n)).obj (L (n + 1)) ⟶ L n)
    (ρ : ∀ n, (modulePullback B S hS (i n)).obj F ⟶ L n) [∀ n, IsIso (ρ n)]
    (μ : ∀ n, (modulePullback B S hS (i n)).obj G ⟶ L n)
    (hρ : ∀ n, (𝒯.tri n).hom.app F ≫ (modulePullback B S hS (s n)).map (ρ (n + 1)) ≫ τ n = ρ n)
    (hμ : ∀ n, (𝒯.tri n).hom.app G ≫ (modulePullback B S hS (s n)).map (μ (n + 1)) ≫ τ n =
      μ n) :
    ∃! ψ : G ⟶ F, ∀ n, (modulePullback B S hS (i n)).map ψ ≫ ρ n = μ n := by
  have hτ : ∀ n, τ n = inv ((modulePullback B S hS (s n)).map (ρ (n + 1))) ≫
      (𝒯.tri n).inv.app F ≫ ρ n := fun n => by
    rw [← hρ n]
    simp
  obtain ⟨ψ, hψ, hψu⟩ := 𝒯.existsUnique_hom_of_compatible hπ F G hF hG hFp hGp
    (fun n => μ n ≫ inv (ρ n)) (fun n => by
      rw [← hμ n, hτ n]
      simp [Functor.map_inv])
  refine ⟨ψ, fun n => ?_, fun ψ' hψ' => hψu ψ' fun n => ?_⟩
  · rw [hψ n]
    simp
  · rw [← hψ' n]
    simp

section Algebraization

variable (F : ∀ n, Modules.{u, u} B S hS (Z n).1 (Z n).2)

/-- The direct images `i_{n*} F_n` of the levels. -/
abbrev push (i : ∀ n, Z n ⟶ X) (F : ∀ n, Modules.{u, u} B S hS (Z n).1 (Z n).2) (n : ℕ) :
    Modules.{u, u} B S hS X.1 X.2 :=
  (modulePushforward B S hS (i n)).obj (F n)

/-- The unit `i_{n*} F_n ⟶ i_{n*} i_n^* i_{n*} F_n` is an isomorphism. -/
theorem isIso_unit_push (n : ℕ) :
    IsIso ((modulePullbackAdjunction B S hS (i n)).unit.app (push i F n)) := by
  have := isIso_modulePullbackAdjunction_counit B S hS (i n) (𝒯.isClosedImmersion_i n) (F n)
  have : IsIso ((modulePullbackAdjunction B S hS (i n)).unit.app (push i F n) ≫
      (modulePushforward B S hS (i n)).map
        ((modulePullbackAdjunction B S hS (i n)).counit.app (F n))) := by
    rw [(modulePullbackAdjunction B S hS (i n)).right_triangle_components (F n)]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((modulePushforward B S hS (i n)).map
    ((modulePullbackAdjunction B S hS (i n)).counit.app (F n)))

section Quotients

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- `I^{n+1} Ψ(i_{n*} F_n) = 0`. -/
theorem idealPowerMultiple_push_eq_bot (n : ℕ) :
    idealPowerMultiple B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
      ((siteChangeModules B X π).obj (push i F n)) = ⊥ := by
  have := 𝒯.isIso_unit_push F n
  have : IsIso (cokernel.π (idealPowerMultiple B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
      ((siteChangeModules B X π).obj (push i F n))).ι) := by
    rw [← 𝒯.map_unit_thickeningIso_hom (push i F n) n]
    infer_instance
  have _hm := @IsIso.mono_of_iso _ _ _ _ _ this
  refine (submodule_ι_eq_zero_iff B (Spec (.of R)) hR (siteChangeSpace B X π).1
    (siteChangeSpace B X π).2 _).1 ?_
  exact (cancel_mono (cokernel.π (idealPowerMultiple B (Spec (.of R)) hR
    (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
    (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
    ((siteChangeModules B X π).obj (push i F n))).ι)).1
      ((cokernel.condition _).trans zero_comp.symm)

/-- **The system `(Ψ(i_{n*} F_n))_n` is a coherent adic system**, for transitions which are the
unit followed by the direct image of an isomorphism. -/
theorem isCoherentAdicSystem_ofOpSequence
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hF : ∀ n, IsCoherent B S hS (Z n).1 (Z n).2 (F n))
    (τ : ∀ n, push i F (n + 1) ⟶ push i F n)
    (hτ : ∀ n, ∃ l : (modulePullback B S hS (i n)).obj (push i F (n + 1)) ⟶ F n, IsIso l ∧
      τ n = (modulePullbackAdjunction B S hS (i n)).unit.app (push i F (n + 1)) ≫
        (modulePushforward B S hS (i n)).map l) :
    IsCoherentAdicSystem B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I)
      (Functor.ofOpSequence (X := fun n => (siteChangeModules B X π).obj (push i F n))
        (fun n => (siteChangeModules B X π).map (τ n))) := by
  refine ⟨fun n => (isCoherent_siteChangeModules_iff X π _).2
      (isCoherent_modulePushforward_of_isClosedImmersion B S hS hX.out (i n)
        (𝒯.isClosedImmersion_i n) (F n) (hF n)),
    fun n => 𝒯.idealPowerMultiple_push_eq_bot F n, fun n => ?_⟩
  obtain ⟨l, hl, hτl⟩ := hτ n
  have key : cokernel.π (idealPowerMultiple B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
      ((siteChangeModules B X π).obj (push i F (n + 1)))).ι ≫
      ((𝒯.thickeningIso (push i F (n + 1)) n).symm ≪≫ (siteChangeModules B X π).mapIso
        ((modulePushforward B S hS (i n)).mapIso (asIso l))).hom =
      (siteChangeModules B X π).map (τ n) := by
    rw [hτl, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_hom, asIso_hom,
      ← 𝒯.map_unit_thickeningIso_hom (push i F (n + 1)) n, Category.assoc,
      Iso.hom_inv_id_assoc, ← Functor.map_comp]
  exact ⟨_, key.trans (Functor.ofOpSequence_map_homOfLE_succ
    (X := fun n => (siteChangeModules B X π).obj (push i F n))
    (fun n => (siteChangeModules B X π).map (τ n)) n).symm⟩

/-- **Restrictions from an algebraization of the system.**  If `θ_n` identify the completion of
`Ψ N` with the system `(Ψ(i_{n*} F_n))_n`, then `i_n^* N ≅ F_n`, compatibly with the
transitions. -/
theorem exists_iso_of_adicQuotientSystem_iso
    (φ : ∀ n, (modulePullback B S hS (s n)).obj (F (n + 1)) ⟶ F n)
    (τ : ∀ n, push i F (n + 1) ⟶ push i F n)
    (hτ : ∀ n {G : Modules.{u, u} B S hS X.1 X.2}
      (α : (modulePullback B S hS (i (n + 1))).obj G ⟶ F (n + 1)),
      (modulePullbackAdjunction B S hS (i (n + 1))).homEquiv G (F (n + 1)) α ≫ τ n =
        (modulePullbackAdjunction B S hS (i n)).homEquiv G (F n)
          ((𝒯.tri n).hom.app G ≫ (modulePullback B S hS (s n)).map α ≫ φ n))
    (N : Modules.{u, u} B S hS X.1 X.2)
    (θ : ∀ n, idealPowerQuotient B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
      ((siteChangeModules B X π).obj N) ≅ (siteChangeModules B X π).obj (push i F n))
    (hθ : ∀ n, idealPowerQuotientMapOfLE B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I)
      (Nat.le_succ (n + 1)) ((siteChangeModules B X π).obj N) ≫ (θ n).hom =
        (θ (n + 1)).hom ≫ (siteChangeModules B X π).map (τ n)) :
    ∃ ψ : ∀ n, (modulePullback B S hS (i n)).obj N ≅ F n,
      ∀ n, (𝒯.tri n).hom.app N ≫ (modulePullback B S hS (s n)).map (ψ (n + 1)).hom ≫
        φ n = (ψ n).hom := by
  obtain ⟨hΨ⟩ : Nonempty (siteChangeModules B X π).FullyFaithful :=
    ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
  obtain ⟨pN, hpN⟩ : ∃ pN : ∀ n, (siteChangeModules B X π).obj N ⟶
      idealPowerQuotient B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
        (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
        ((siteChangeModules B X π).obj N),
      ∀ n, pN n = cokernel.π (idealPowerMultiple B (Spec (.of R)) hR (siteChangeSpace B X π).1
        (siteChangeSpace B X π).2 (C1573.baseIdealSubmodule (siteChangeSpace B X π).1
          (siteChangeSpace B X π).2 I) (n + 1) ((siteChangeModules B X π).obj N)).ι :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hwΨ⟩ : ∃ w : ∀ n, N ⟶ push i F n,
      ∀ n, (siteChangeModules B X π).map (w n) = pN n ≫ (θ n).hom :=
    ⟨fun n => hΨ.preimage (pN n ≫ (θ n).hom), fun n => hΨ.map_preimage _⟩
  have hw : ∀ n, w (n + 1) ≫ τ n = w n := fun n => by
    refine hΨ.map_injective ?_
    rw [Functor.map_comp, hwΨ, hwΨ, Category.assoc, ← hθ n, ← Category.assoc, hpN, hpN,
      π_comp_idealPowerQuotientMapOfLE]
  obtain ⟨ψ₀, hwψ⟩ : ∃ ψ₀ : ∀ n, (modulePullback B S hS (i n)).obj N ⟶ F n,
      ∀ n, w n = (modulePullbackAdjunction B S hS (i n)).homEquiv N (F n) (ψ₀ n) :=
    ⟨fun n => ((modulePullbackAdjunction B S hS (i n)).homEquiv N (F n)).symm (w n),
      fun n => (Equiv.apply_symm_apply _ _).symm⟩
  have hψiso : ∀ n, IsIso (ψ₀ n) := fun n => by
    have hu : (siteChangeModules B X π).map
        ((modulePullbackAdjunction B S hS (i n)).unit.app N) =
          pN n ≫ (𝒯.thickeningIso N n).inv := by
      rw [hpN]
      exact (Iso.eq_comp_inv _).2 (𝒯.map_unit_thickeningIso_hom N n)
    have : Epi ((siteChangeModules B X π).map
        ((modulePullbackAdjunction B S hS (i n)).unit.app N)) := by
      rw [hu]
      have : Epi (pN n) := by rw [hpN]; exact coequalizer.π_epi
      exact epi_comp' this (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))
    have key : (siteChangeModules B X π).map ((modulePushforward B S hS (i n)).map (ψ₀ n)) =
        (𝒯.thickeningIso N n).hom ≫ (θ n).hom := by
      refine (cancel_epi ((siteChangeModules B X π).map
        ((modulePullbackAdjunction B S hS (i n)).unit.app N))).1 ?_
      have h1 := (modulePullbackAdjunction B S hS (i n)).homEquiv_unit N (F n) (ψ₀ n)
      rw [← Functor.map_comp, ← h1, ← hwψ, hwΨ, hpN]
      exact (𝒯.map_unit_thickeningIso_hom_assoc N n _).symm
    have : IsIso ((siteChangeModules B X π).map
        ((modulePushforward B S hS (i n)).map (ψ₀ n))) := by
      rw [key]
      infer_instance
    have : IsIso ((modulePushforward B S hS (i n)).map (ψ₀ n)) :=
      isIso_of_reflects_iso _ (siteChangeModules B X π)
    exact (fullyFaithfulModulePushforward B S hS (i n)
      (𝒯.isClosedImmersion_i n)).isIso_of_isIso_map (ψ₀ n)
  have hcompat : ∀ n, (𝒯.tri n).hom.app N ≫ (modulePullback B S hS (s n)).map (ψ₀ (n + 1)) ≫
      φ n = ψ₀ n := fun n => by
    refine ((modulePullbackAdjunction B S hS (i n)).homEquiv N (F n)).injective ?_
    rw [← hwψ, ← hw n, hwψ (n + 1)]
    exact (hτ n (ψ₀ (n + 1))).symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ n, (modulePullback B S hS (i n)).obj N ≅ F n, ∀ n, (ψ n).hom = ψ₀ n :=
    ⟨fun n => @asIso _ _ _ _ (ψ₀ n) (hψiso n), fun n => @asIso_hom _ _ _ _ (ψ₀ n) (hψiso n)⟩
  exact ⟨ψ, fun n => by simpa only [hψ] using hcompat n⟩

/-- **Stacks 08BE on a tower of thickenings.**  Let `R` be Noetherian and `I`-adically complete
and `π` separated of finite type.  A family of coherent modules `F_n` on the `Z_n` with
`s_n^* F_{n+1} ≅ F_n`, whose first term has support proper over `T_0`, is the family of
restrictions of a coherent `𝒪_X`-module with support proper over `Spec R`, compatibly with the
given identifications. -/
theorem exists_of_compatible [IsNoetherianRing R] [IsAdicComplete I R]
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hπ : IsFiniteType B S hS π.hom) (hsep : IsSeparated B S hS π.hom)
    (hF : ∀ n, IsCoherent B S hS (Z n).1 (Z n).2 (F n))
    (φ : ∀ n, (modulePullback B S hS (s n)).obj (F (n + 1)) ≅ F n)
    (hp : IsLocallyOfFiniteType B S hS (p 0).hom)
    (hF₀p : HasProperSupport B S hS (Z 0).2 (schemeSpace (T 0)).2 (p 0).hom hp
      ((SheafOfModules.toSheaf _).obj (F 0))) :
    ∃ (G : Modules.{u, u} B S hS X.1 X.2) (_ : IsCoherent B S hS X.1 X.2 G)
      (_ : HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ.1
        ((SheafOfModules.toSheaf _).obj G))
      (ψ : ∀ n, (modulePullback B S hS (i n)).obj G ≅ F n),
      ∀ n, (𝒯.tri n).hom.app G ≫ (modulePullback B S hS (s n)).map (ψ (n + 1)).hom ≫
        (φ n).hom = (ψ n).hom := by
  have hf'ft : IsFiniteType B (Spec (.of R)) hR (siteChangeStructure X π).hom :=
    (isFiniteType_siteChangeStructure_iff X π).2 hπ
  have hf'sep : IsSeparated B (Spec (.of R)) hR (siteChangeStructure X π).hom :=
    isSeparated_siteChangeStructure X π hsep
  let := C1573.fact_isLocallyNoetherian_of_baseObject (siteChangeSpace B X π)
    (siteChangeStructure X π) hf'ft.1
  have hft := isFiniteTypeOnSite_of_isCoherent X
  have hftZ := isFiniteTypeOnSite_of_isCoherent (Z 0) (F 0) (hF 0)
  obtain ⟨τ, hτ, hτl⟩ : ∃ τ : ∀ n, push i F (n + 1) ⟶ push i F n,
      (∀ n {G : Modules.{u, u} B S hS X.1 X.2}
        (α : (modulePullback B S hS (i (n + 1))).obj G ⟶ F (n + 1)),
        (modulePullbackAdjunction B S hS (i (n + 1))).homEquiv G (F (n + 1)) α ≫ τ n =
          (modulePullbackAdjunction B S hS (i n)).homEquiv G (F n)
            ((𝒯.tri n).hom.app G ≫ (modulePullback B S hS (s n)).map α ≫ (φ n).hom)) ∧
      ∀ n, ∃ l : (modulePullback B S hS (i n)).obj (push i F (n + 1)) ⟶ F n, IsIso l ∧
        τ n = (modulePullbackAdjunction B S hS (i n)).unit.app (push i F (n + 1)) ≫
          (modulePushforward B S hS (i n)).map l :=
    ⟨fun n => Adjunction.pushTransition (modulePullbackAdjunction B S hS (i n))
        (modulePullbackAdjunction B S hS (i (n + 1))) (𝒯.tri n) (F (n + 1)) (φ n).hom,
      fun n _ α => Adjunction.homEquiv_comp_pushTransition _ _ _ _ α,
      fun n => by
        have := isIso_modulePullbackAdjunction_counit B S hS (i (n + 1))
          (𝒯.isClosedImmersion_i (n + 1)) (F (n + 1))
        exact Adjunction.exists_isIso_pushTransition _ _ _ _ _⟩
  have hE0coh := isCoherent_modulePushforward_of_isClosedImmersion B S hS hX.out (i 0)
    (𝒯.isClosedImmersion_i 0) (F 0) (hF 0)
  have hE0 := (hasProperSupport_siteChangeModules_iff X π hπ.1 (push i F 0)
    hE0coh.toIsQuasicoherentOnSite (hft _ hE0coh)).2
      (𝒯.hasProperSupport_modulePushforward_zero hπ.1 (F 0) hftZ hp hF₀p)
  let Eobj : CoherentAdicSystemsProperOver B (Spec (.of R)) hR (siteChangeSpace B X π).2
      (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom hf'ft.1
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) :=
    ⟨⟨_, 𝒯.isCoherentAdicSystem_ofOpSequence F hF τ hτl⟩, hE0⟩
  let Φ := completionFunctorProperOver B (Spec (.of R)) hR (siteChangeSpace B X π).1
    (schemeSpace (baseObject R B hR)).1 (siteChangeSpace B X π).2
    (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom hf'ft.1
    (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I)
    (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := (siteChangeSpace B X π).1)
      (hX := (siteChangeSpace B X π).2) I)
  have : Φ.IsEquivalence :=
    C1573.isEquivalence_completionFunctorProperOver I (siteChangeSpace B X π)
      (siteChangeStructure X π) hf'ft hf'sep
  obtain ⟨G', ⟨eG⟩⟩ := Functor.EssSurj.mem_essImage (F := Φ) Eobj
  obtain ⟨N, ⟨eN⟩⟩ := Functor.EssSurj.mem_essImage (F := siteChangeModules B X π) G'.obj.obj
  have hNcoh : IsCoherent B S hS X.1 X.2 N := (isCoherent_siteChangeModules_iff X π N).1
    (isCoherent_of_iso B (Spec (.of R)) hR (siteChangeSpace B X π).2 eN.symm G'.obj.property)
  have hNp := (hasProperSupport_siteChangeModules_iff X π hπ.1 N hNcoh.toIsQuasicoherentOnSite
      (hft N hNcoh)).1 (hasProperSupport_of_iso _ _ _ eN.symm G'.property)
  let θ : adicQuotientSystem B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I)
      ((siteChangeModules B X π).obj N) ≅
        Functor.ofOpSequence (X := fun n => (siteChangeModules B X π).obj (push i F n))
          (fun n => (siteChangeModules B X π).map (τ n)) :=
    (adicQuotientFunctor B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
      (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I)).mapIso eN ≪≫
      ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso eG)
  obtain ⟨ψ, hψ⟩ := 𝒯.exists_iso_of_adicQuotientSystem_iso F (fun n => (φ n).hom) τ hτ N
    (fun n => θ.app (op n)) (fun n => by
      have hnat := θ.hom.naturality (homOfLE (Nat.le_add_right n 1)).op
      rwa [adicQuotientSystem_map, Functor.ofOpSequence_map_homOfLE_succ] at hnat)
  exact ⟨N, hNcoh, hNp, ψ, hψ⟩

end Quotients

end Algebraization

end SiteChangeTower

end AlgebraicGeometry.Space

end
