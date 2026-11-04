module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexLowerVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageQcqs
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ConnectiveHypercohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing complex of a closed subscheme of a proper curve

Let `X` be a proper scheme of dimension at most one over a field `k` and let `i : Y ⟶ X` be a
closed immersion. [Stacks, Tag 0E33] identifies the dualizing complex and dualizing sheaf of `Y`
with those of `X`:

  `ω_Y^• = R𝓗om(𝒪_Y, ω_X^•)`,  `ω_Y = 𝓗om(𝒪_Y, ω_X)`,  `i_*ω_Y = 𝓗om_{𝒪_X}(i_*𝒪_Y, ω_X)`.

## Main definitions

* `Stacks.Duality.rightAdjointClosedImmersionCompIso` — for `f : X ⟶ S` and a closed immersion
  `i`, the right adjoint of `R(i ≫ f)_*` is that of `Ri_*` after that of `Rf_*`.
* `Stacks.Duality.relativeDualizingComplexClosedImmersionIso` — `(i ≫ f)^× K ≅ R𝓗om(𝒪_Y, f^× K)`
  when `f^× K` is bounded below.
* `Stacks.Duality.dualizingComplexOverFieldClosedImmersionIso`,
  `Stacks.Duality.dualizingSheafOverFieldClosedImmersionIso` and
  `Stacks.Duality.pushforwardDualizingSheafOverFieldClosedImmersionIso` — the three
  identifications of [Stacks, Tag 0E33].

## Main results

* `Stacks.Duality.nonempty_homologyRightDerivedIso_of_isGE` — for a left exact `F` and `M` in
  `D^{≥ n}`, `Hⁿ(RF(M)) = F(Hⁿ(M))`.
* `Stacks.Duality.dualizingComplexOverField_closedImmersion` — **[Stacks, Tag 0E33]**.

## Implementation notes

The proof is the source's. With `a`, `b`, `c` the right adjoints of `Rf_*`, `Rg_*`, `Ri_*` for
`f : X ⟶ Spec k`, `g = i ≫ f`, the composition formula `Rg_* = Rf_* ∘ Ri_*` gives `b = c ∘ a`
by uniqueness of adjoints, so `ω_Y^• = b(𝒪) = c(ω_X^•)`, and `c = R𝓗om(𝒪_Y, -)` on
bounded-below objects by [Stacks, Tag 0A9X]. The dualizing complex `ω_X^•` lies in `D^{≥ -1}`
(`Stacks.Duality.isGE_dualizingComplexOverField`), which supplies both the boundedness that
[Stacks, Tag 0A9X] asks for and, `𝓗om(𝒪_Y, -)` being left exact, the identification of
`H^{-1}` in part (2). The last identification is the description of `𝓗om(𝒪_Y, -)` in
[Stacks, Tag 0A75], which is the underived form of [Stacks, Tag 0A77] cited by the source.

All derived categories are the locally small models, at which the right adjoints of
[Stacks, Tag 0A9E] exist.

## References

* [Stacks Project, Tag 0E33](https://stacks.math.columbia.edu/tag/0E33)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality

section Composition

variable {Y X S : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (f : X ⟶ S)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (n : ℤ),
    ((DerivedCategory.homologyFunctor S.Modules n).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (n : ℤ),
    ((DerivedCategory.homologyFunctor S.Modules n).obj
      ((derivedPushforward (i ≫ f)).obj K.obj)).IsQuasicoherent)

/-- `R(i ≫ f)_* = Rf_* ∘ Ri_*` on the quasi-coherent derived categories, for a closed
immersion `i`: the composition formula for derived direct image read on the full
subcategories. -/
def quasiCoherentDerivedPushforwardClosedImmersionCompIso :
    LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⋙
        quasiCoherentDerivedPushforward f hpushf ≅
      quasiCoherentDerivedPushforward (i ≫ f) hpushg :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPushforwardCompIso i f).app K.obj))
    (fun e => ObjectProperty.hom_ext _ ((derivedPushforwardCompIso i f).hom.naturality e.hom))

variable {a : quasiCoherentDerivedCategory S ⥤ quasiCoherentDerivedCategory X}
  {b : quasiCoherentDerivedCategory S ⥤ quasiCoherentDerivedCategory Y}
  {c : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}

/-- **`b = c ∘ a`**: for a closed immersion `i : Y ⟶ X` and `f : X ⟶ S`, the right adjoint of
`R(i ≫ f)_*` is the right adjoint of `Ri_*` after that of `Rf_*`, by uniqueness of right
adjoints. -/
def rightAdjointClosedImmersionCompIso
    (adjf : quasiCoherentDerivedPushforward f hpushf ⊣ a)
    (adjg : quasiCoherentDerivedPushforward (i ≫ f) hpushg ⊣ b)
    (adji : LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⊣ c) :
    b ≅ a ⋙ c :=
  adjg.rightAdjointUniq
    ((adji.comp adjf).ofNatIsoLeft
      (quasiCoherentDerivedPushforwardClosedImmersionCompIso i f hpushf hpushg))

/-- **`ω_Y^• = R𝓗om(𝒪_Y, ω_X^•)` for the relative dualizing complexes.** Let `i : Y ⟶ X` be a
pseudo-coherent closed immersion with `Y` quasi-compact and quasi-separated, let `f : X ⟶ S`,
and let `K ∈ D_QCoh(𝒪_S)`. If `f^×K` is bounded below then
`(i ≫ f)^×K ≅ R𝓗om(𝒪_Y, f^×K)`: the twisted inverse image of `i ≫ f` is that of `i` after that
of `f` (`rightAdjointClosedImmersionCompIso`), and the twisted inverse image of `i` is
`R𝓗om(𝒪_Y, -)` on bounded-below objects ([Stacks, Tag 0A9X]). -/
def relativeDualizingComplexClosedImmersionIso [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hpc : PseudoCoherent i)
    [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
    [(quasiCoherentDerivedPushforward (i ≫ f) hpushg).IsLeftAdjoint]
    (K : quasiCoherentDerivedCategory S)
    (hK : DerivedCategoryB.IsBoundedBelow (relativeDualizingComplex f hpushf K).obj) :
    (relativeDualizingComplex (i ≫ f) hpushg K).obj ≅
      (LocallySmall.derivedSheafHomExactSupport i).obj
        (relativeDualizingComplex f hpushf K).obj :=
  (ObjectProperty.ι _).mapIso ((rightAdjointClosedImmersionCompIso i f hpushf hpushg
      (twistedInverseImageAdjunction f hpushf) (twistedInverseImageAdjunction (i ≫ f) hpushg)
      (Adjunction.ofIsLeftAdjoint _)).app K) ≪≫
    (LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion i hpc _
      (Adjunction.ofIsLeftAdjoint _)).some.app ⟨relativeDualizingComplex f hpushf K, hK⟩

end Composition

section LeftExact

variable {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian.{u} C]
  [HasDerivedCategory.{u} C]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory.{u} D]

/-- **The lowest cohomology of a right derived functor of a left exact functor.** For an object
`M` of `D(C)` with no cohomology below degree `n`, `Hⁿ(RF(M)) ≅ F(Hⁿ(M))`: `M` is represented by
a complex of injectives vanishing below `n`, which is K-injective and so computes `RF`, and `F`
preserves the kernel computing degree-`n` cohomology of such a complex. -/
theorem nonempty_homologyRightDerivedIso_of_isGE (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (M : DerivedCategory C) (n : ℤ) (hGE : M.IsGE n) :
    Nonempty ((DerivedCategory.homologyFunctor D n).obj (RF.obj M) ≅
      F.obj ((DerivedCategory.homologyFunctor C n).obj M)) := by
  let Mplus : DerivedCategory.Plus C := ⟨M, ⟨n, hGE⟩⟩
  have _ : Mplus.IsGE n := ⟨hGE.ge⟩
  obtain ⟨L, hL, ⟨ePlus⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Mplus n
  have _ : L.obj.IsStrictlyGE n := hL
  let I : CochainComplex C ℤ := ((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj
  have hIge : I.IsStrictlyGE n :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := L.obj) (InjectiveObject.ι C) n).2 hL
  have hIinj : ∀ m : ℤ, Injective (I.X m) := fun m => (L.obj.X m).property
  have ePlusFull : DerivedCategory.Q.obj I ≅ M := DerivedCategory.Plus.ι.mapIso ePlus
  have hIK : I.IsKInjective :=
    let : ∀ m : ℤ, Injective (I.X m) := hIinj
    CochainComplex.isKInjective_of_injective I n
  have hα : IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K => ⟨(Stacks.Injectives.kInjectiveResolutionFunctor C).obj K,
        (Stacks.Injectives.kInjectiveResolutionInclusion C).app K, inferInstance,
        inferInstance⟩)).2 DerivedCategory.Qh RF α I hIK
  have eDerived : RF.obj M ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    let := hα
    RF.mapIso ePlusFull |>.symm ≪≫
      RF.mapIso ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
      (asIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))).symm ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
      (DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  refine ⟨((DerivedCategory.homologyFunctor D n).mapIso eDerived).trans ?_⟩
  have hX₁ : IsZero (I.sc n).X₁ := by
    dsimp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]
    exact (CochainComplex.isStrictlyGE_iff I n).mp hIge ((ComplexShape.up ℤ).prev n) (by simp)
  have hpres : (I.sc n).leftHomologyData.IsPreservedBy F :=
    { g := inferInstance
      f' := by rw [hX₁.eq_of_src (I.sc n).leftHomologyData.f' 0]; infer_instance }
  have _ : F.PreservesLeftHomologyOf (I.sc n) :=
    let := hpres
    Functor.PreservesLeftHomologyOf.mk' (F := F) (S := I.sc n) (I.sc n).leftHomologyData
  refine ((DerivedCategory.homologyFunctorFactors D n).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).trans ?_
  exact ((I.sc n).mapHomologyIso F).trans
    (F.mapIso ((DerivedCategory.homologyFunctorFactors C n).app I).symm ≪≫
      F.mapIso ((DerivedCategory.homologyFunctor C n).mapIso ePlusFull))

end LeftExact

section SheafHom

variable {Y X : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- **The lowest cohomology of `R𝓗om(𝒪_Y, -)`.** For a closed immersion `i : Y ⟶ X` and an object
`M` of `D(𝒪_X)` with no cohomology below degree `n`,
`Hⁿ(R𝓗om(𝒪_Y, M)) ≅ 𝓗om(𝒪_Y, Hⁿ(M))`: sheaf Hom with exact support is a right adjoint, hence
left exact. -/
theorem nonempty_homology_derivedSheafHomExactSupport_iso_of_isGE
    (M : DerivedCategory X.Modules) (n : ℤ) (hM : M.IsGE n) :
    Nonempty ((DerivedCategory.homologyFunctor Y.Modules n).obj
        ((LocallySmall.derivedSheafHomExactSupport i).obj M) ≅
      (closedQuotient i).sheafHomExactSupport.obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj M)) :=
  have : PreservesFiniteLimits (closedQuotient i).sheafHomExactSupport :=
    (closedQuotient i).modulePushforwardSheafHomExactSupportAdjunction
      |>.rightAdjoint_preservesLimits.preservesFiniteLimits.{0, 0}
  nonempty_homologyRightDerivedIso_of_isGE (closedQuotient i).sheafHomExactSupport
    (LocallySmall.derivedSheafHomExactSupport i)
    (LocallySmall.derivedSheafHomExactSupportComparison i) M n hM

end SheafHom

section Curve

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (i : Y ⟶ X) [IsClosedImmersion i]

/-- **[Stacks, Tag 0E33], part (1): `ω_Y^• = R𝓗om(𝒪_Y, ω_X^•)`.** For a closed immersion
`i : Y ⟶ X` into a proper scheme of dimension at most one over a field, the dualizing complex of
`Y` is derived sheaf Hom out of `𝒪_Y` into that of `X`. The dualizing complex `ω_X^•` lies in
`D^{≥ -1}`, so this is `Stacks.Duality.relativeDualizingComplexClosedImmersionIso`; the immersion
is pseudo-coherent because `X` is Noetherian. -/
def dualizingComplexOverFieldClosedImmersionIso
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    (dualizingComplexOverField (i ≫ f)).obj ≅
      (LocallySmall.derivedSheafHomExactSupport i).obj (dualizingComplexOverField f).obj :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace i
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (i ≫ f)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI := isGE_dualizingComplexOverField f hdim
  relativeDualizingComplexClosedImmersionIso i f _ _
    ((pseudoCoherent_iff_locallyOfFiniteType i).2 inferInstance) _
    ⟨-1, fun n hn => DerivedCategory.isZero_of_isGE (dualizingComplexOverField f).obj (-1) n hn⟩

/-- **[Stacks, Tag 0E33], part (2), first half: `ω_Y = 𝓗om(𝒪_Y, ω_X)`.** Taking `H^{-1}` of
part (1): `ω_X^•` lies in `D^{≥ -1}` and sheaf Hom with exact support is left exact, so
`H^{-1}(R𝓗om(𝒪_Y, ω_X^•)) = 𝓗om(𝒪_Y, H^{-1}(ω_X^•))`. -/
def dualizingSheafOverFieldClosedImmersionIso
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    dualizingSheafOverField (i ≫ f) ≅
      (closedQuotient i).sheafHomExactSupport.obj (dualizingSheafOverField f) :=
  (DerivedCategory.homologyFunctor Y.Modules (-1)).mapIso
      (dualizingComplexOverFieldClosedImmersionIso f i hdim) ≪≫
    (nonempty_homology_derivedSheafHomExactSupport_iso_of_isGE i _ (-1)
      (isGE_dualizingComplexOverField f hdim)).some

/-- **[Stacks, Tag 0E33], part (2), second half:
`i_*ω_Y = 𝓗om_{𝒪_X}(i_*𝒪_Y, ω_X)`.** The first half pushed forward along `i`, followed by the
identification `i_*𝓗om(𝒪_Y, -) = 𝓗om_{𝒪_X}(i_*𝒪_Y, -)` of [Stacks, Tag 0A75]. -/
def pushforwardDualizingSheafOverFieldClosedImmersionIso
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    (Scheme.Modules.pushforward i).obj (dualizingSheafOverField (i ≫ f)) ≅
      (closedQuotient i).homSheafFromPushforwardStructureSheaf.obj
        (dualizingSheafOverField f) :=
  (Scheme.Modules.pushforward i).mapIso (dualizingSheafOverFieldClosedImmersionIso f i hdim) ≪≫
    (closedQuotient i).modulePushforwardSheafHomExactSupportIsoHomSheaf.app
      (dualizingSheafOverField f)

/-- **Stacks Project, Tag 0E33.** Let `X` be a proper scheme of dimension at most one over a
field `k` and let `i : Y ⟶ X` be a closed immersion, with dualizing complexes and dualizing
sheaves `ω_X^•, ω_X, ω_Y^•, ω_Y` as in [Stacks, Tag 0BS2]. Then
1. `ω_Y^• = R𝓗om(𝒪_Y, ω_X^•)`;
2. `ω_Y = 𝓗om(𝒪_Y, ω_X)` and `i_*ω_Y = 𝓗om_{𝒪_X}(i_*𝒪_Y, ω_X)`. -/
@[stacks 0E33]
theorem dualizingComplexOverField_closedImmersion
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    Nonempty ((dualizingComplexOverField (i ≫ f)).obj ≅
        (LocallySmall.derivedSheafHomExactSupport i).obj (dualizingComplexOverField f).obj) ∧
      Nonempty (dualizingSheafOverField (i ≫ f) ≅
        (closedQuotient i).sheafHomExactSupport.obj (dualizingSheafOverField f)) ∧
      Nonempty ((Scheme.Modules.pushforward i).obj (dualizingSheafOverField (i ≫ f)) ≅
        (closedQuotient i).homSheafFromPushforwardStructureSheaf.obj
          (dualizingSheafOverField f)) :=
  ⟨⟨dualizingComplexOverFieldClosedImmersionIso f i hdim⟩,
    ⟨dualizingSheafOverFieldClosedImmersionIso f i hdim⟩,
    ⟨pushforwardDualizingSheafOverFieldClosedImmersionIso f i hdim⟩⟩

end Curve

end Stacks.Duality

end
