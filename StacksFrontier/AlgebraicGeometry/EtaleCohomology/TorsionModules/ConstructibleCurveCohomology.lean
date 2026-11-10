module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ShriekZModCurveFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of constructible torsion sheaves of modules on curves

Let `Λ` be a Noetherian ring, `k` an algebraically closed field and `X` a separated scheme of
finite type over `k` of dimension at most one. [Stacks, Tag 0GJI] asserts that for a constructible
sheaf `F` of `Λ`-modules on `X_étale` which is torsion, `H^q(X, F)` is a finite `Λ`-module

1. if `F` is torsion prime to the characteristic of `k` (Tag 0GJJ), and
2. if `X` is proper over `k` (Tag 0GJK).

## Main results

* `module_finite_etaleCohomology_of_isPrimeToCharacteristicTorsion`: `H^q(X, F)` is a finite
  `Λ`-module when `F` is torsion prime to the characteristic of `k`.
* `module_finite_etaleCohomology_of_isProper`: `H^q(X, F)` is a finite `Λ`-module when `X` is
  proper over `k`.

## Implementation notes

The proof is not the source's dévissage through Lemmas 0GJC, 0GJE, 0GJF and 0GJH (dense opens,
the method of the trace, Zariski's main theorem). It is the argument by generators of
[SGA 4½, Th. finitude, 1.5]: a constructible sheaf `F` on the quasi-compact quasi-separated `X` is
a quotient of a finite direct sum of extensions by zero `j_{U!}Λ̲` from affine étale `U ⟶ X`
(the finite generation step of Stacks 095N). Each summand corresponds to a section of `F` over
`U`, which is killed by an integer `N` prime to the characteristic, so the quotient map factors
through `⊕ j_{U!}(Λ/N)̲`. The kernel is again constructible and torsion of the same kind, and
`H^q = 0` for `q > 2` (Tag 0A53), so a descending induction on `q` reduces the theorem to the
finiteness of `H^q(X, j_{U!}(Λ/N)̲)`. That is the `𝔽_ℓ`-basis trick of the proof of Tag 0GJC for
the coefficient functor `M ↦ j_!(M̲)`, whose input `H^q(X, j_!(ℤ/ℓ))` is finite by Tags 0A56 and
0A57, the abelian sheaf `j_!(ℤ/ℓ)` being constructible by Stacks 03S8.

The case distinction is carried by an integer `p`, the exponent to which the torsion of `F` is
prime: `p = char(k)` (read as the exponential characteristic) for part (1), and `p = 1`, which
imposes no condition, for part (2), where `X` is proper.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

-- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the module universe `u + 1` and its
-- unification against `ModuleCat.{max (u + 1) r}` fails with a universe error instead of
-- backtracking, so it is switched off here.
attribute [-instance] hasSheafifyEtale

/-- Sheaves of `Λ`-modules on the small étale site have finite coproducts, being an abelian
category. -/
theorem hasFiniteCoproducts_etaleModules (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    HasFiniteCoproducts (EtaleModules.{u, r} Λ X) :=
  have : HasFiniteBiproducts (EtaleModules.{u, r} Λ X) := Abelian.hasFiniteBiproducts
  hasFiniteCoproducts_of_hasFiniteBiproducts _

/-- A finite family of sheaves of `Λ`-modules on the small étale site has a coproduct. Stated for
`Discrete.functor` directly: instance search does not reach it from the abelian structure within
its budget. -/
local instance (priority := 10000) hasColimit_discrete_fin_etaleModules (Λ : Type r) [Ring Λ]
    (X : Scheme.{u}) (n : ℕ) (Q : Fin n → EtaleModules.{u, r} Λ X) :
    HasColimit (Discrete.functor Q) :=
  haveI := (hasFiniteCoproducts_etaleModules Λ X).out n
  HasColimitsOfShape.has_colimit _

/-! ### Sections of a torsion sheaf over a quasi-compact object -/

section Sections

variable {X : Scheme.{u}}

/-- A section of an abelian sheaf which vanishes on the members of a covering sieve vanishes. -/
theorem section_eq_zero_of_forall_sieve_map_eq_zero
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (V : X.Etale)
    (x : G.obj.obj (op V)) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V)
    (hx : ∀ (W : X.Etale) (f : W ⟶ V), R f → G.obj.map f.op x = 0) : x = 0 := by
  have hG := (isSheaf_iff_isSheaf_of_type X.smallEtaleTopology _).mp
    (GrothendieckTopology.HasSheafCompose.isSheaf G.obj G.2
      (F := forget AddCommGrpCat.{max (u + 1) r}))
  refine (hG.isSeparated _ hR).ext fun W f hf => ?_
  change G.obj.map f.op x = G.obj.map f.op 0
  exact (hx W f hf).trans (map_zero _).symm

/-- If `n i` kills `y`, then so does the product `∏ j, n j`. -/
private theorem prod_nsmul_eq_zero_of_nsmul_eq_zero {M ι : Type*} [AddMonoid M] [Fintype ι]
    (n : ι → ℕ) (i : ι) {y : M} (h : n i • y = 0) : (∏ j, n j) • y = 0 := by
  obtain ⟨c, hc⟩ : n i ∣ ∏ j, n j := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, mul_nsmul, h, smul_zero]

/-- **A section over a quasi-compact object of a sheaf whose torsion is prime to `p` is killed by a
single integer prime to `p`.** The covering sieve on whose members the section is killed by
integers prime to `p` contains a finite covering family (`exists_qcSepCovering_le`), and the
product of the integers attached to its members kills the section. -/
@[sga "4 IX 1.2" "(ii)"]
theorem exists_nsmul_eq_zero_of_isPrimeToCharacteristicTorsion [CompactSpace X]
    [QuasiSeparatedSpace X] (p : ℕ) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
    (hG : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p G) (V : X.Etale)
    (hV : V ∈ qcSeparatedOver X) (x : G.obj.obj (op V)) :
    ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ N • x = 0 := by
  classical
  obtain ⟨R, hR, hann⟩ := hG V x
  obtain ⟨E, ⟨hfin, -, -, hcov⟩, hle⟩ := exists_qcSepCovering_le V hV R hR
  have hmem : ∀ i, R (E.f i) := fun i => hle _ (Sieve.ofArrows_mk _ _ i)
  choose n hn hcop hzero using fun i => hann (E.X i) (E.f i) (hmem i)
  have := Fintype.ofFinite E.I₀
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i,
    Nat.Coprime.prod_left fun i _ => hcop i, ?_⟩
  refine section_eq_zero_of_forall_sieve_map_eq_zero G V _ E.sieve₀ hcov fun W g hg => ?_
  obtain ⟨Y, h, _, ⟨i⟩, rfl⟩ := hg
  have h0 : (G.obj.map (E.f i).op) ((∏ i, n i) • x) = 0 := by
    rw [map_nsmul]
    exact prod_nsmul_eq_zero_of_nsmul_eq_zero n i (hzero i)
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, h0, map_zero]

end Sections

/-! ### The generators on Mathlib's small étale site -/

section Generators

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-- The generator `j_!Λ̲` on Mathlib's small étale site of `X` attached to an object `U` of the
small étale site of Tag 021B, `j` being its structure morphism. -/
abbrev smallEtaleShriekGenerator (U : SmallEtale B X.obj X.property) :
    EtaleModules.{u, r} Λ X.obj :=
  (@etaleModuleShriekConstant.{u, r} Λ _ _ _ (B.inclusion.map U.obj.hom) U.property).obj
    (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))

/-- **The extension by zero `j_{U!}Λ̲` from an object `U` of the small étale site of Tag 021B,
transported to Mathlib's small étale site, is `j_!` of the constant sheaf `Λ̲` there**, `j` being
the structure morphism of `U` (`AlgebraicGeometry.SmallEtale.sheafEquivExtensionByZeroIso` and
the restriction of a constant sheaf along the dense subsite). This is
`AlgebraicGeometry.moduleShriekConstantTransportIso` for a ring in a universe of its own. -/
def etaleModuleShriekConstantSheafEquivIso (U : SmallEtale B X.obj X.property) :
    smallEtaleShriekGenerator B X Λ U ≅
      (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).functor.obj
        (moduleShriekConstant.{u, r, r} B X Λ U) := by
  haveI : Etale (B.inclusion.map U.obj.hom) := U.property
  let A := ModuleCat.{max (u + 1) r} Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B U.obj.left Λ
  let eW := SmallEtale.sheafEquiv B U.obj.left.1 U.obj.left.property A
  let T := SmallEtale.sheafEquivExtensionByZeroIso B X.obj X.property U A
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (B.inclusion.map U.obj.hom))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtalePostcompose B X.obj X.property U) A
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.obj X.property))
  let rc := (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    U.obj.left.1.smallEtaleTopology
    (SmallEtale.toEtaleSite B U.obj.left.1 U.obj.left.property) A).app
      (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))
  let d : eW.functor.obj ((constantSheaf (SmallEtale.topology B U.obj.left.1
        U.obj.left.property) A).obj (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))) ≅
      (constantSheaf U.obj.left.1.smallEtaleTopology A).obj
        (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)) :=
    eW.functor.mapIso rc.symm ≪≫ eW.counitIso.app _
  exact (etaleModuleExtensionByZero.{u, r} Λ _).mapIso d.symm ≪≫ T.app _

variable [IsNoetherianRing Λ]

/-- Constructible sheaves of `Λ`-modules on Mathlib's small étale site are closed under finite
coproducts: a binary coproduct is a biproduct, hence an extension of one summand by the other, and
they form a weak Serre subcategory. -/
instance isClosedUnderFiniteCoproducts_isConstructibleEtaleModule :
    (IsBigSiteConstructibleEtaleModule B X Λ).IsClosedUnderFiniteCoproducts := by
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B X Λ
  have : (IsBigSiteConstructibleEtaleModule B X Λ).IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
      rintro _ ⟨H, hH⟩
      exact (IsBigSiteConstructibleEtaleModule B X Λ).prop_of_iso
        ((biprod.isoCoprod _ _).trans (HasColimit.isoOfNatIso (diagramIsoPair H)).symm)
        ((IsBigSiteConstructibleEtaleModule B X Λ).prop_biprod (hH ⟨.left⟩) (hH ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- **Stacks 03S8 on Mathlib's small étale site**: for an object `U` of the small étale site of
Tag 021B of a quasi-compact quasi-separated `X`, with `U` quasi-compact and quasi-separated and
structure morphism `j`, the sheaf `j_!Λ̲` is constructible. -/
theorem isConstructibleEtaleModule_etaleModuleShriekConstant [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    haveI : Etale (B.inclusion.map U.obj.hom) := U.property
    IsBigSiteConstructibleEtaleModule B X Λ ((etaleModuleShriekConstant.{u, r} Λ
      (B.inclusion.map U.obj.hom)).obj (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))) := by
  have : Etale (B.inclusion.map U.obj.hom) := U.property
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B X Λ
  refine (IsBigSiteConstructibleEtaleModule B X Λ).prop_of_iso
    (etaleModuleShriekConstantSheafEquivIso B X Λ U).symm ?_
  change IsConstructibleModuleSheaf B X Λ ((etaleModulesToSmallEtale B X Λ).obj _)
  exact isConstructibleModuleSheaf_congr B Λ X
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).unitIso.app _)
    (isConstructibleModuleSheaf_moduleShriekConstant B X Λ U)

end Generators

/-! ### Maps out of a generator are killed by an integer -/

section Exponent

variable {Λ : Type r} [CommRing Λ] {X : Scheme.{u}}

/-- **A map from `j_!Λ̲` to a sheaf whose torsion is prime to `p` is killed by an integer prime to
`p`**, for `j : U ⟶ X` étale with `U` affine and `X` quasi-compact quasi-separated. Such a map is
the adjoint of a section of the sheaf over `U`, which is killed by an integer prime to `p`
(`exists_nsmul_eq_zero_of_isPrimeToCharacteristicTorsion`). -/
theorem exists_nsmul_eq_zero_of_hom_etaleModuleShriekConstant [CompactSpace X]
    [QuasiSeparatedSpace X] (p : ℕ) (F : EtaleModules.{u, r} Λ X)
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p
      ((etaleModuleForgetAb.{u, r} Λ X).obj F))
    {U : Scheme.{u}} (j : U ⟶ X) [Etale j] [IsAffine U]
    (g : (etaleModuleShriekConstant.{u, r} Λ j).obj (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)) ⟶
      F) :
    ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ N • g = 0 := by
  let adj := (constantSheafAdj U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (etaleSiteTerminalIsTerminal U)).comp (etaleModuleExtensionByZeroAdj.{u, r} Λ j)
  let ĝ := adj.homEquiv _ _ g
  let V' : X.Etale := (Scheme.Etale.smallEtaleCompose j).obj (etaleSiteTerminal U)
  have : IsAffine V'.left := ‹IsAffine U›
  obtain ⟨N, hN, hNp, hx⟩ := exists_nsmul_eq_zero_of_isPrimeToCharacteristicTorsion p
    ((etaleModuleForgetAb.{u, r} Λ X).obj F) hF V' (mem_qcSeparatedOver_of_isAffine V')
    (ĝ (ULift.up 1))
  have h1 : adj.homEquiv _ _ (N • g) = N • ĝ := by
    rw [Adjunction.homEquiv_unit, Functor.map_nsmul, Preadditive.comp_nsmul,
      ← Adjunction.homEquiv_unit]
  have h0 : adj.homEquiv (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)) F 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  refine ⟨N, hN, hNp, (adj.homEquiv _ _).injective (h1.trans (Eq.trans ?_ h0.symm))⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun l => ?_)
  obtain ⟨l⟩ := l
  change N • ĝ (ULift.up l) = 0
  have hl : (ULift.up l : ULift.{max (u + 1) r} Λ) = l • ULift.up 1 := by
    ext
    simp
  rw [hl, map_smul, smul_comm]
  change l • (N • ĝ (ULift.up 1)) = 0
  rw [show N • ĝ (ULift.up 1) = 0 from hx, smul_zero]

end Exponent

/-! ### Presentation by generators on Mathlib's small étale site -/

section Presentation

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  smallEtaleHasColimitsOfSizeModuleMax

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **A constructible sheaf of `Λ`-modules on Mathlib's small étale site of a quasi-compact
quasi-separated scheme is a quotient of a finite direct sum of generators `j_{U!}Λ̲` with `U`
affine.** This is the finite generation step of Stacks 095N on the site of Tag 021B
(`AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine`), transported. -/
theorem exists_epi_sigma_smallEtaleShriekGenerator [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj] (F : EtaleModules.{u, r} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) :
    ∃ (n : ℕ) (V : Fin n → SmallEtale B X.obj X.property),
      (∀ i, IsAffine (V i).obj.left.obj) ∧
        ∃ φ : (∐ fun i => smallEtaleShriekGenerator B X Λ (V i)) ⟶ F, Epi φ := by
  let E := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)
  obtain ⟨n, V, hV, f, hf⟩ := exists_finite_epi_comp_sigma_moduleShriekConstant_affine B X Λ
    (𝟙 (E.inverse.obj F)) hF
  rw [Category.comp_id] at hf
  have := (hasFiniteCoproducts_etaleModules Λ X.obj).out n
  have hpc : PreservesColimitsOfShape (Discrete (Fin n)) E.functor :=
    E.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimit (Discrete.functor fun i => moduleShriekConstant.{u, r, r} B X Λ (V i))
      E.functor := hpc.preservesColimit
  let e₁ : (∐ fun i => smallEtaleShriekGenerator B X Λ (V i)) ≅
      ∐ fun i => E.functor.obj (moduleShriekConstant.{u, r, r} B X Λ (V i)) :=
    Sigma.mapIso fun i => etaleModuleShriekConstantSheafEquivIso B X Λ (V i)
  let e₂ : E.functor.obj (∐ fun i => moduleShriekConstant.{u, r, r} B X Λ (V i)) ≅
      ∐ fun i => E.functor.obj (moduleShriekConstant.{u, r, r} B X Λ (V i)) :=
    PreservesCoproduct.iso E.functor _
  have : Epi (E.functor.map f) := E.functor.map_epi f
  exact ⟨n, V, hV, e₁.hom ≫ e₂.inv ≫ E.functor.map f ≫ E.counitIso.hom.app F,
    epi_comp' inferInstance (epi_comp' inferInstance (epi_comp' inferInstance inferInstance))⟩

end Presentation

/-! ### Vanishing above degree two -/

section Vanishing

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]

include π in
/-- **The cohomology of a torsion sheaf of `Λ`-modules on a curve vanishes above degree two**
(Tag 0A53, read on the underlying abelian sheaf through Stacks 03FD). -/
theorem subsingleton_etaleModuleCohomology_of_two_lt (hdim : topologicalKrullDim X ≤ 1)
    {Λ : Type r} [CommRing Λ] (F : EtaleModules.{u, r} Λ X)
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForgetAb.{u, r} Λ X).obj F)) (q : ℕ) (hq : 2 < q) :
    Subsingleton (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj F) := by
  let S : TorsionSheafSituation.{u, r} :=
    { k := k, X := X, structureMorphism := π, dimension_le_one := hdim,
      F := (etaleModuleForgetAb.{u, r} Λ X).obj F, isTorsion := hF }
  have h' : Subsingleton (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived
      q).obj ((etaleModuleForgetAb.{u, r} Λ X).obj F)) :=
    ((Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{r} X.smallEtaleTopology
      q).app _).addCommGroupIsoToAddEquiv.subsingleton_congr.2 (S.isVanishingAboveDegreeTwo q hq)
  exact ((etaleModuleCohomologyForgetIso.{u, r} Λ X q).app F).addCommGroupIsoToAddEquiv
    |>.subsingleton_congr.2 h'

include π in
/-- The cohomology of a sheaf of `Λ`-modules on a curve whose torsion is prime to `p` is finite
above degree two, where it vanishes. -/
theorem module_finite_etaleModuleCohomology_of_two_lt (hdim : topologicalKrullDim X ≤ 1)
    {Λ : Type r} [CommRing Λ] (p : ℕ) (G : EtaleModules.{u, r} Λ X)
    (hG : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p
      ((etaleModuleForgetAb.{u, r} Λ X).obj G)) (q : ℕ) (hq : 2 < q) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj G) := by
  have hG' : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForgetAb.{u, r} Λ X).obj G) := fun V x => by
    obtain ⟨R, hR, h⟩ := hG V x
    exact ⟨R, hR, fun W g hg => by
      obtain ⟨n, hn, -, hz⟩ := h W g hg
      exact ⟨n, hn, hz⟩⟩
  have := subsingleton_etaleModuleCohomology_of_two_lt π hdim G hG' q hq
  have : Finite (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj G) :=
    Finite.of_subsingleton
  exact Module.Finite.of_finite

end Vanishing

/-! ### Finite direct sums -/

section Sums

variable {Λ : Type r} [CommRing Λ] {X : Scheme.{u}}

/-- The cohomology of a finite direct sum of sheaves of `Λ`-modules with finite cohomology is
finite: cohomology is additive, so it carries the direct sum to the direct sum. -/
theorem module_finite_etaleModuleCohomology_sigma (q : ℕ) {n : ℕ}
    (Q : Fin n → EtaleModules.{u, r} Λ X)
    (h : ∀ i, Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (Q i))) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (∐ Q)) := by
  let G := (etaleModuleGlobalSections.{u, r} Λ X).rightDerived q
  have : HasFiniteBiproducts (EtaleModules.{u, r} Λ X) := Abelian.hasFiniteBiproducts
  let e : G.obj (∐ Q) ≅ ModuleCat.of Λ (∀ i, G.obj (Q i)) :=
    G.mapIso (biproduct.isoCoproduct Q).symm ≪≫ G.mapBiproduct Q ≪≫
      ModuleCat.biproductIsoPi fun i => G.obj (Q i)
  exact Module.Finite.equiv e.symm.toLinearEquiv

end Sums

/-! ### Exponents of finite coproducts -/

section Exponents

variable {C : Type*} [Category C] [Preadditive C]

/-- If each `Q i` is killed by `N i`, then the coproduct `∐ Q` is killed by `∏ i, N i`. -/
theorem nsmul_id_sigma_eq_zero {n : ℕ} (Q : Fin n → C) [HasCoproduct Q] (N : Fin n → ℕ)
    (hQ : ∀ i, N i • 𝟙 (Q i) = 0) : (∏ i, N i) • 𝟙 (∐ Q) = 0 := by
  refine Sigma.hom_ext _ _ fun i => ?_
  have hι : N i • Sigma.ι Q i = 0 := by
    rw [← Category.id_comp (Sigma.ι Q i), ← Preadditive.nsmul_comp, hQ i, zero_comp]
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  exact prod_nsmul_eq_zero_of_nsmul_eq_zero N i hι

end Exponents

/-! ### The descending induction -/

section Main

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme)
  (π : X.obj ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- An abelian sheaf killed by a positive integer `N` prime to `p` has torsion prime to `p`. -/
theorem isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero {Y : Scheme.{u}} (p : ℕ)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (N : ℕ) (hN : 0 < N)
    (hNp : N.Coprime p) (h : N • 𝟙 G = 0) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion Y.smallEtaleTopology p G := by
  have hz : ((N : ℤ) • 𝟙 G) = 0 := by rw [natCast_zsmul, h]
  intro V x
  refine ⟨⊤, Y.smallEtaleTopology.top_mem V, fun W g _ => ⟨N, hN, hNp, ?_⟩⟩
  rw [← natCast_zsmul]
  exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff G N).1 hz _ _

/-- **The cohomology of `j_!(Λ/N)̲` is finite** for a generator attached to an affine `U` and an
integer `N > 0` prime to `p`: this is the `𝔽_ℓ`-basis trick for `M ↦ j_!(M̲)`
(`module_finite_etaleCohomology_etaleModuleShriekConstant`) at `M = Λ/N`, with input the
finiteness of `H^q(X, j_!(ℤ/ℓ))` for the primes `ℓ ∣ N`
(`finite_rightDerived_etaleAbelianShriekConstant_zmod`). -/
theorem module_finite_etaleCohomology_cokernel_nsmul_smallEtaleShriekGenerator
    (hdim : topologicalKrullDim X.obj ≤ 1) (p : ℕ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ.Coprime p → ℓ.Coprime (ringExpChar k) ∨ IsProper π)
    (V : SmallEtale B X.obj X.property) [IsAffine V.obj.left.obj] (N : ℕ) (hN : 0 < N)
    (hNp : N.Coprime p) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X.obj).rightDerived q).obj
      (cokernel (N • 𝟙 (smallEtaleShriekGenerator B X Λ V)))) := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated π
  let : Etale (B.inclusion.map V.obj.hom) := V.property
  have : CompactSpace (B.inclusion.obj (B.obj X.obj X.property)) :=
    inferInstanceAs (CompactSpace X.obj)
  have : QuasiSeparatedSpace (B.inclusion.obj (B.obj X.obj X.property)) :=
    inferInstanceAs (QuasiSeparatedSpace X.obj)
  let M₀ := ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)
  let C₀ : ModuleCat.{max (u + 1) r} Λ := cokernel (N • 𝟙 M₀)
  let T := etaleModuleShriekConstant.{u, r} Λ (B.inclusion.map V.obj.hom)
  have hT : T.map (N • 𝟙 M₀) = N • 𝟙 (T.obj M₀) := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  let e : T.obj C₀ ≅ cokernel (N • 𝟙 (T.obj M₀)) :=
    PreservesCokernel.iso T (N • 𝟙 M₀) ≪≫ cokernelIsoOfEq hT
  have : Module.Finite Λ C₀ :=
    Module.Finite.of_surjective (cokernel.π (N • 𝟙 M₀)).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have hM : ∀ m : C₀, N • m = 0 := fun m => by
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (cokernel.π (N • 𝟙 M₀))).1
      inferInstance m
    have h := congrArg (fun f => f.hom y) (cokernel.condition (N • 𝟙 M₀))
    rw [← map_nsmul]
    exact h
  have hfin := module_finite_etaleCohomology_etaleModuleShriekConstant
    (B.inclusion.map V.obj.hom) N hN
    (fun ℓ hℓ hdvd q' => finite_rightDerived_etaleAbelianShriekConstant_zmod B X π hdim V
      ℓ hℓ (hp ℓ hℓ (Nat.Coprime.coprime_dvd_left hdvd hNp)) q') C₀ hM q
  have : Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X.obj).rightDerived q).obj
      (T.obj C₀)) := hfin
  exact Module.Finite.equiv
    (((etaleModuleGlobalSections.{u, r} Λ X.obj).rightDerived q).mapIso e).toLinearEquiv

/-- **A constructible sheaf of `Λ`-modules on Mathlib's small étale site of a quasi-compact
quasi-separated scheme, with torsion prime to `p`, is a quotient of a finite direct sum of
sheaves `j_{U!}(Λ/N)̲` with `U` affine and `N > 0` prime to `p`.** -/
theorem exists_epi_sigma_cokernel_nsmul_smallEtaleShriekGenerator [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj] (p : ℕ) (G : EtaleModules.{u, r} Λ X.obj)
    (hc : IsBigSiteConstructibleEtaleModule B X Λ G)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p
      ((etaleModuleForgetAb.{u, r} Λ X.obj).obj G)) :
    ∃ (n : ℕ) (V : Fin n → SmallEtale B X.obj X.property) (N : Fin n → ℕ),
      (∀ i, IsAffine (V i).obj.left.obj) ∧ (∀ i, 0 < N i) ∧ (∀ i, (N i).Coprime p) ∧
        ∃ Φ : (∐ fun i => cokernel (N i • 𝟙 (smallEtaleShriekGenerator B X Λ (V i)))) ⟶ G,
          Epi Φ := by
  obtain ⟨n, V, hV, φ, hφ⟩ := exists_epi_sigma_smallEtaleShriekGenerator B X Λ G hc
  have hN : ∀ i, ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧
      N • (Sigma.ι (fun i => smallEtaleShriekGenerator B X Λ (V i)) i ≫ φ) = 0 := fun i => by
    have : Etale (B.inclusion.map (V i).obj.hom) := (V i).property
    have : IsAffine (B.inclusion.obj (V i).obj.left) := hV i
    exact exists_nsmul_eq_zero_of_hom_etaleModuleShriekConstant p G ht
      (B.inclusion.map (V i).obj.hom) _
  choose N hN0 hNp hNφ using hN
  let P := fun i => smallEtaleShriekGenerator B X Λ (V i)
  let Q := fun i => cokernel (N i • 𝟙 (P i))
  let φ' : ∀ i, Q i ⟶ G := fun i => cokernel.desc _
    (Sigma.ι (fun i => smallEtaleShriekGenerator B X Λ (V i)) i ≫ φ)
    (by rw [Preadditive.nsmul_comp, Category.id_comp, hNφ i])
  let Φ : (∐ Q) ⟶ G := Sigma.desc φ'
  have hfac : Limits.Sigma.map (fun i => cokernel.π (N i • 𝟙 (P i))) ≫ Φ = φ := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_map_assoc, Sigma.ι_comp_desc, cokernel.π_desc]
  refine ⟨n, V, N, hV, hN0, hNp, Φ, ?_⟩
  rw [← hfac] at hφ
  exact epi_of_epi (Limits.Sigma.map fun i => cokernel.π (N i • 𝟙 (P i))) Φ

/-- **The cohomology of a constructible sheaf of `Λ`-modules on a curve whose torsion is prime to
`p` is finite**, for an integer `p` such that every prime `ℓ` prime to `p` is prime to the
characteristic of `k` or `X` is proper. This is the common form of Tags 0GJJ (`p = char(k)`) and
0GJK (`p = 1`, `X` proper).

Descending induction on `q`, starting above degree two where the cohomology vanishes (Tag 0A53):
`F` is a quotient of `⊕_i j_{U_i!}(Λ/N_i)̲` with `N_i` prime to `p`, the kernel `K` is again
constructible with torsion prime to `p`, and `H^q(⊕_i j_{U_i!}(Λ/N_i)̲) ⟶ H^q(F) ⟶ H^{q+1}(K)` is
exact with finite outer terms. -/
@[sga "5 VI 3.1" "partial"]
theorem module_finite_etaleCohomology_of_isPrimeToCharacteristicTorsion_of_forall
    (hdim : topologicalKrullDim X.obj ≤ 1) (p : ℕ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ.Coprime p → ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ)
    (F : EtaleModules.{u, r} Λ X.obj) (hc : IsBigSiteConstructibleEtaleModule B X Λ F)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p
      ((etaleModuleForgetAb.{u, r} Λ X.obj).obj F)) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X.obj).rightDerived q).obj F) := by
  classical
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated π
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B X Λ
  suffices h : ∀ m q : ℕ, 3 ≤ q + m → ∀ G : EtaleModules.{u, r} Λ X.obj,
      IsBigSiteConstructibleEtaleModule B X Λ G →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p
        ((etaleModuleForgetAb.{u, r} Λ X.obj).obj G) →
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X.obj).rightDerived q).obj G) from
    h 3 q (by omega) F hc ht
  intro m
  induction m with
  | zero => exact fun q hq G _ hG =>
      module_finite_etaleModuleCohomology_of_two_lt π hdim p G hG q (by omega)
  | succ m ih =>
    intro q hq G hcG htG
    by_cases hq3 : 3 ≤ q
    · exact module_finite_etaleModuleCohomology_of_two_lt π hdim p G htG q (by omega)
    obtain ⟨n, V, N, hV, hN0, hNp, Φ, hΦ⟩ :=
      exists_epi_sigma_cokernel_nsmul_smallEtaleShriekGenerator B X Λ p G hcG htG
    let Q := fun i => cokernel (N i • 𝟙 (smallEtaleShriekGenerator B X Λ (V i)))
    let S := ShortComplex.mk (kernel.ι Φ) Φ (kernel.condition Φ)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel (kernelIsKernel Φ)) inferInstance
        inferInstance
    have hgen : ∀ i, IsBigSiteConstructibleEtaleModule B X Λ
        (smallEtaleShriekGenerator B X Λ (V i)) := fun i =>
      have := hV i; isConstructibleEtaleModule_etaleModuleShriekConstant B X Λ (V i)
    have hK : IsBigSiteConstructibleEtaleModule B X Λ (kernel Φ) :=
      (IsBigSiteConstructibleEtaleModule B X Λ).prop_kernel Φ
        ((IsBigSiteConstructibleEtaleModule B X Λ).prop_coproduct fun i =>
          (IsBigSiteConstructibleEtaleModule B X Λ).prop_cokernel _ (hgen i) (hgen i)) hcG
    have hNtK : (∏ i, N i) • 𝟙 (kernel Φ) = 0 := by
      rw [← cancel_mono (kernel.ι Φ), Preadditive.nsmul_comp, Category.id_comp, zero_comp,
        ← Category.comp_id (kernel.ι Φ), ← Preadditive.comp_nsmul, nsmul_id_sigma_eq_zero Q N
          fun i => nsmul_id_cokernel_nsmul_id_eq_zero _ (N i), comp_zero]
    have htK : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p
        ((etaleModuleForgetAb.{u, r} Λ X.obj).obj (kernel Φ)) :=
      isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero p _ (∏ i, N i)
        (Finset.prod_pos fun i _ => hN0 i) (Nat.Coprime.prod_left fun i _ => hNp i)
        (by rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hNtK, Functor.map_zero])
    have hQfin : ∀ i, Module.Finite Λ
        (((etaleModuleGlobalSections.{u, r} Λ X.obj).rightDerived q).obj (Q i)) := fun i =>
      have := hV i
      module_finite_etaleCohomology_cokernel_nsmul_smallEtaleShriekGenerator B X π Λ hdim p hp
        (V i) (N i) (hN0 i) (hNp i) q
    exact TorsionModules.module_finite_of_exact Λ _
      ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (etaleModuleGlobalSections.{u, r} Λ X.obj)).exact_δ₁ hS q)
      (module_finite_etaleModuleCohomology_sigma q Q hQfin) (ih (q + 1) (by omega) _ hK htK)

end Main

/-! ### Tag 0GJI -/

section Tag

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

namespace TorsionModules

variable {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme)
  (π : X.obj ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  (hdim : topologicalKrullDim X.obj ≤ 1) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

include π hdim in
/-- **Stacks Project, Tag 0GJI, part (1) (Tag 0GJJ).** Let `Λ` be a Noetherian ring, `k` an
algebraically closed field, `X` a separated scheme of finite type over `k` of dimension at most
one, and `F` a constructible sheaf of `Λ`-modules on `X_étale` which is torsion prime to the
characteristic of `k`. Then `H^q_étale(X, F)` is a finite `Λ`-module for every `q`.

"Torsion prime to `char(k)`" is `Stacks.Torsion.IsPrimeToCharacteristicTorsion` of the underlying
abelian sheaf at the exponential characteristic of `k`: every local section is, locally, killed by
a positive integer prime to it. It implies that `F` is torsion, and in characteristic zero it is
exactly that. Constructibility is `Stacks.EtaleCohomology.IsBigSiteConstructibleEtaleModule`
(Tag 03RW (3), read on the small étale site of Tag 021B of a big étale site `B` containing `X`). -/
@[stacks 0GJJ, stacks 0GJI "part (1): F torsion prime to char(k)", sga "5 VI 3.1" "partial"]
theorem module_finite_etaleCohomology_of_isPrimeToCharacteristicTorsion
    (F : EtaleModules.{u, r} Λ X.obj) (hc : IsBigSiteConstructibleEtaleModule B X Λ F)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology (ringExpChar k)
      ((etaleModuleForgetAb.{u, r} Λ X.obj).obj F)) (q : ℕ) :
    Module.Finite Λ
      (((Sheaf.Γ X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).rightDerived q).obj F) :=
  module_finite_etaleCohomology_of_isPrimeToCharacteristicTorsion_of_forall B X π Λ hdim
    (ringExpChar k) (fun _ _ h => Or.inl h) q F hc ht

include hdim in
/-- **Stacks Project, Tag 0GJI, part (2) (Tag 0GJK).** Let `Λ` be a Noetherian ring, `k` an
algebraically closed field, `X` a proper scheme over `k` of dimension at most one, and `F` a
constructible sheaf of `Λ`-modules on `X_étale` which is torsion. Then `H^q_étale(X, F)` is a
finite `Λ`-module for every `q`.

Torsion is `Stacks.EtaleCohomology.IsTorsionEtaleModule`: every local section is, locally, killed
by a positive integer. -/
@[stacks 0GJK, stacks 0GJI "part (2): X proper"]
theorem module_finite_etaleCohomology_of_isProper [IsProper π]
    (F : EtaleModules.{u, r} Λ X.obj) (hc : IsBigSiteConstructibleEtaleModule B X Λ F)
    (ht : IsTorsionEtaleModule.{u, r} Λ X.obj F) (q : ℕ) :
    Module.Finite Λ
      (((Sheaf.Γ X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).rightDerived q).obj F) :=
  module_finite_etaleCohomology_of_isPrimeToCharacteristicTorsion_of_forall B X π Λ hdim 1
    (fun _ _ _ => Or.inr ‹IsProper π›) q F hc fun V x => by
      obtain ⟨R, hR, h⟩ := ht V x
      exact ⟨R, hR, fun W g hg => by
        obtain ⟨n, hn, hz⟩ := h W g hg
        exact ⟨n, hn, Nat.coprime_one_right n, hz⟩⟩

end TorsionModules

end Tag

end Stacks.EtaleCohomology

end
