module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.WeaklyAssociatedPointsFinite
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.RingTheory.Flat.FlatLocusFiniteModuleOpenness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative flat locus of a module of finite type

Let `f : X ⟶ S` be a morphism of schemes locally of finite presentation and let `F` be a
quasi-coherent `𝒪_X`-module of finite type. If the weakly associated points of `S` are locally
finite, the locus `U` of points at which `F` is flat over `S` is open, and `F|_U` is of finite
presentation and flat over `S`. These are the three assertions of Stacks 05IK.

For a module of *finite presentation* openness holds with no hypothesis on `S`; that is
Stacks 0399, `AlgebraicGeometry.isOpen_setOf_flatOverAt`. For a morphism locally of finite
*type* the three assertions are Stacks 05IQ, in
`StacksFrontier/AlgebraicGeometry/Flatness/FiniteTypeII/ModuleFlatLocusFiniteType.lean`.

## Main results

* `AlgebraicGeometry.isOpen_flatLocus` is the openness assertion of Stacks 05IK.
* `AlgebraicGeometry.isFinitePresentation_flatLocus` is its finite-presentation assertion and
  `AlgebraicGeometry.isFlatOver_flatLocus` its flatness assertion. Both are read off from the
  stronger statements for an arbitrary open subscheme of the flat locus,
  `AlgebraicGeometry.isFinitePresentation_restrict_of_subset_flatLocus` proved here and
  `AlgebraicGeometry.isFlatOver_restrict_of_subset_flatLocus`, which needs no hypothesis at all.

## Implementation notes

Both results rest on `Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime`, the
affine content of Stacks 05IK, which is the theorem
`Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime`; it reaches them through
Stacks 05IL in `StacksFrontier/RingTheory/Flat/FlatLocusFiniteModuleOpenness.lean`.

The reduction to the affine case is the one Stacks 0399 goes through, and the chain of
comparisons is shared with it: an isomorphism of modules
(`AlgebraicGeometry.flatOverAt_iff_of_iso`), the identification of relative flatness with
flatness of the stalk over the sections of an affine open of the base
(`AlgebraicGeometry.flatOverAt_iff_flat_sectionsStalk` together with
`AlgebraicGeometry.germ_spec_comp_stalkMap`), and invariance under restriction along an open
immersion (`AlgebraicGeometry.isFlatOverAt_restrict_iff`). What differs is the ring-theoretic
input: instead of Stacks 00RC, which asks the module to be finitely presented, the finite type
case uses the two assertions of Stacks 05IL,
`Stacks.Flatness.isOpen_setOf_flat_localizedModule_atPrime_of_finite_weaklyAssociatedPrimes` and
`Stacks.Flatness.finitePresentation_localizedModule_away_of_basicOpen_subset_flatLocus`, whose
hypothesis on the base is supplied by `AlgebraicGeometry.weaklyAssociatedPrimes_sections_finite`
on an affine open of `S` contained in a witness of local finiteness. Because of that the affine
statement below carries, besides openness, the pointwise comparison of relative flatness with
flatness of the localizations of the module of sections; the finite-presentation half needs it
at every point, not just openness.

The finite-presentation assertion is Zariski-local on the open subscheme in the strong sense of
Stacks 05B0 (`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`), so it is enough to
produce finite presentation after pulling back to the spectrum of the sections of each affine
open of the subscheme lying over an affine open of the base inside a witness; those spectra
cover the subscheme. On such a chart the module of sections is finitely presented by Stacks 05IL
applied to the unit `g = 1`, since the flatness hypothesis holds at *every* prime there.

## References

* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
* [Stacks Project, Tag 05IL](https://stacks.math.columbia.edu/tag/05IL)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry

noncomputable section

/-- **The affine case, for the sheaf associated to a module.** For a ring map `A → B` of finite
presentation whose source has finitely many weakly associated primes and a finite `B`-module `M`,
the locus of primes of `B` where the stalk of `M~` is flat over `A` is open, and at each prime it
agrees with flatness over `A` of the localization of `M` there. -/
@[sga "1 IV 6.10" "special case", sga "3 VIB 13.1" "(i), special case"]
private theorem isOpen_flat_tilde_stalk_of_finite_weakAss
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (M : ModuleCat.{u} B) [Module.Finite B M]
    (hφ : RingHom.FinitePresentation φ.hom) (hA : (weaklyAssociatedPrimes A A).Finite) :
    IsOpen {q : PrimeSpectrum B |
      letI : Module A ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
      Module.Flat A ((tilde M).presheaf.stalk q)} ∧
    ∀ q : PrimeSpectrum B, letI : Algebra A B := φ.hom.toAlgebra
      letI : Module A M := Module.compHom M φ.hom
      letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      letI : q.asIdeal.IsPrime := q.isPrime
      (letI : Module A ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
       Module.Flat A ((tilde M).presheaf.stalk q)) ↔
        Module.Flat A (LocalizedModule.AtPrime q.asIdeal M) := by
  algebraize [φ.hom]
  let _ : Module A M := Module.compHom M φ.hom
  let _ : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Algebra.FinitePresentation A B := RingHom.finitePresentation_algebraMap.mpr hφ
  have hO : IsOpen {q : PrimeSpectrum B |
      Module.Flat A (LocalizedModule.AtPrime q.asIdeal M)} :=
    Stacks.Flatness.isOpen_setOf_flat_localizedModule_atPrime_of_finite_weaklyAssociatedPrimes
      hA
  have hEq (q : PrimeSpectrum B) :
      (let : Module A ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
       Module.Flat A ((tilde M).presheaf.stalk q)) ↔
        Module.Flat A (LocalizedModule.AtPrime q.asIdeal M) := by
    let _ : q.asIdeal.IsPrime := q.isPrime
    let _ : Module A ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
    let _ : IsScalarTower A B ((tilde M).presheaf.stalk q) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let e : LocalizedModule.AtPrime q.asIdeal M ≃ₗ[B] ((tilde M).presheaf.stalk q) :=
      IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap _ M) (tilde.toStalk M q).hom
    exact (Module.Flat.equiv_iff (e.restrictScalars A)).symm
  exact ⟨Set.ext hEq ▸ hO, hEq⟩

/-- Relative flatness of `M~` at a point of `Spec B`, over an affine open `V` of the base through
`φ : Γ(S, V) ⟶ B`, is flatness of its stalk over `Γ(S, V)`. -/
private theorem isFlatOverAt_tilde_iff_flat_stalk
    {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V)
    {B : CommRingCat.{u}} (φ : Γ(S, V) ⟶ B) (M : ModuleCat.{u} B) (q : PrimeSpectrum B) :
    IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom (tilde M) q ↔
      (letI : Module Γ(S, V) ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
       Module.Flat Γ(S, V) ((tilde M).presheaf.stalk q)) := by
  let _ : Module Γ(S, V) ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
  change IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom (tilde M) q ↔
    Module.Flat Γ(S, V) ((tilde M).presheaf.stalk q)
  have hx : (Spec.map φ ≫ hV.fromSpec) q ∈ V := by
    change (Spec.map φ q) ∈ hV.fromSpec ⁻¹ᵁ V
    rw [hV.fromSpec_preimage_self]
    trivial
  rw [flatOverAt_iff_flat_sectionsStalk (Spec.map φ ≫ hV.fromSpec) (tilde M) hV q hx]
  let N := (tilde M).presheaf.stalk q
  let _ : Module ((Spec B).presheaf.stalk q) N := Scheme.Modules.moduleStalkPresheaf (tilde M) q
  let _ : Algebra B ((Spec B).presheaf.stalk q) := StructureSheaf.stalkAlgebra B q
  let _ : Module B N := Module.compHom N (algebraMap B ((Spec B).presheaf.stalk q))
  have hB (b : B) (m : N) : (algebraMap B ((Spec B).presheaf.stalk q) b) • m = b • m := rfl
  have hr : S.presheaf.germ V ((Spec.map φ ≫ hV.fromSpec) q) hx ≫
      (Spec.map φ ≫ hV.fromSpec).stalkMap q =
      φ ≫ CommRingCat.ofHom (algebraMap B ((Spec B).presheaf.stalk q)) := by
    calc
      _ = φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ q trivial :=
        germ_spec_comp_stalkMap hV φ q hx
      _ = _ := by
        ext a
        rfl
  let moduleS : Module (S.presheaf.stalk ((Spec.map φ ≫ hV.fromSpec) q)) N :=
    Module.compHom N ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
  let moduleLeft : Module Γ(S, V) N :=
    let : Module (S.presheaf.stalk ((Spec.map φ ≫ hV.fromSpec) q)) N := moduleS
    Module.compHom N (S.presheaf.germ V _ hx).hom
  let moduleRight : Module Γ(S, V) N := Module.compHom N φ.hom
  have hmodule : moduleLeft = moduleRight := by
    apply Module.ext'
    intro a m
    change ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
        ((S.presheaf.germ V _ hx).hom a) • m = (φ.hom a) • m
    have hval := congrArg (fun t : Γ(S, V) ⟶ (Spec B).presheaf.stalk q => t a) hr
    change ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
        ((S.presheaf.germ V _ hx).hom a) =
      algebraMap B ((Spec B).presheaf.stalk q) (φ.hom a) at hval
    rw [hval, hB]
  change @Module.Flat Γ(S, V) N _ _ moduleLeft ↔ @Module.Flat Γ(S, V) N _ _ moduleRight
  rw [hmodule]

/-- **The affine case.** Openness of the relative flat locus for a module of finite type on the
spectrum of a finitely presented algebra over the sections of an affine open of the base, with
the pointwise comparison of relative flatness and flatness of the localized modules of
sections. -/
@[ega "IV 11.3.1" "special case"]
private theorem isOpen_flatOverAt_spec_of_finite_weakAss
    {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V)
    {B : CommRingCat.{u}} (φ : Γ(S, V) ⟶ B) (hφ : RingHom.FinitePresentation φ.hom)
    (F : (Spec B).Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hA : (weaklyAssociatedPrimes Γ(S, V) Γ(S, V)).Finite) :
    IsOpen {q : Spec B |
      IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q} ∧
    ∀ q : Spec B, letI : Algebra Γ(S, V) B := φ.hom.toAlgebra
      letI : Module Γ(S, V) (moduleSpecΓFunctor.obj F) :=
        Module.compHom (moduleSpecΓFunctor.obj F) φ.hom
      letI : IsScalarTower Γ(S, V) B (moduleSpecΓFunctor.obj F) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      letI : q.asIdeal.IsPrime := q.isPrime
      IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q ↔
        Module.Flat Γ(S, V)
          (LocalizedModule.AtPrime q.asIdeal (moduleSpecΓFunctor.obj F)) := by
  let M := moduleSpecΓFunctor.obj F
  have : Module.Finite B M := moduleFinite_of_isFiniteType_qc B F
  let _ : Algebra Γ(S, V) B := φ.hom.toAlgebra
  let _ : Module Γ(S, V) M := Module.compHom M φ.hom
  let _ : IsScalarTower Γ(S, V) B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : F ≅ tilde M := (asIso F.fromTildeΓ).symm
  obtain ⟨hO, hM⟩ := isOpen_flat_tilde_stalk_of_finite_weakAss φ M hφ hA
  have heq : {q : PrimeSpectrum B |
        IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q} =
      {q : PrimeSpectrum B |
        let : Module Γ(S, V) ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
        Module.Flat Γ(S, V) ((tilde M).presheaf.stalk q)} :=
    Set.ext fun q =>
      (flatOverAt_iff_of_iso _ e q).trans (isFlatOverAt_tilde_iff_flat_stalk hV φ M q)
  exact ⟨heq ▸ hO, fun q => (Set.ext_iff.mp heq q).trans (hM q)⟩

/-- Around any point of `Y` there are an affine open `V` lying over an affine open `W` of `S`
whose ring of sections has finitely many weakly associated primes. -/
private theorem exists_affine_chart_of_locally_finite_weakAss
    {Y S : Scheme.{u}} (g : Y ⟶ S)
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) (y : Y) :
    ∃ (W : S.Opens) (V : Y.Opens), IsAffineOpen W ∧
      (weaklyAssociatedPrimes (Γ(S, W) : Type u) (Γ(S, W) : Type u)).Finite ∧
      IsAffineOpen V ∧ V ≤ g ⁻¹ᵁ W ∧ y ∈ V := by
  obtain ⟨W₀, hgyW₀, hW₀fin⟩ := hS (g y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hgyW, hWW₀⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hgyW₀ W₀.2
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hgyW (g ⁻¹ᵁ W).2
  exact ⟨W, V, hW, weaklyAssociatedPrimes_sections_finite (SheafOfModules.unit S.ringCatSheaf) hW
    hWW₀ hW₀fin, hV, hVW, hyV⟩

/-- **Stacks Project, Tag 05IK (openness).** The locus where a quasi-coherent module of finite
type is flat over the target of a morphism locally of finite presentation is open, provided the
weakly associated points of the target are locally finite. -/
@[stacks 05IK "openness of the relative flat locus",
  ega "IV 11.1.6" "case C = B",
  ega "IV 11.3.3" "wk assoc pts loc finite", sga "3 VIB 13.1" "(i) U open"]
theorem isOpen_flatLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) :
    IsOpen (flatLocus f F) := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨W, V, hW, hWA, hV, hVW, hxV⟩ := exists_affine_chart_of_locally_finite_weakAss f hS x
  let φ : Γ(S, W) ⟶ Γ(X, V) := f.appLE W V hVW
  let j : Spec Γ(X, V) ⟶ X := hV.fromSpec
  let _ : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  let G : (Spec Γ(X, V)).Modules := F.restrict j
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j F
  have : G.IsFiniteType := Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict j F
  have hjf : Spec.map φ ≫ hW.fromSpec = j ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hW hV hVW
  have hO : IsOpen {q : Spec Γ(X, V) | IsFlatOverAt (j ≫ f).toLRSHom.toShHom G q} := by
    rw [← hjf]
    exact (isOpen_flatOverAt_spec_of_finite_weakAss hW φ
      (f.finitePresentation_appLE hW hV hVW) G hWA).1
  have heq : {q : Spec Γ(X, V) | IsFlatOverAt (j ≫ f).toLRSHom.toShHom G q} =
      j ⁻¹' flatLocus f F := Set.ext fun q => isFlatOverAt_restrict_iff j f F q
  refine ⟨j '' (j ⁻¹' flatLocus f F), Set.image_preimage_subset j _,
    j.isOpenEmbedding.isOpenMap _ (heq ▸ hO), ?_⟩
  obtain ⟨q, hq⟩ : x ∈ Set.range j := by
    rw [show Set.range j = _ from hV.range_fromSpec]
    exact hxV
  exact ⟨q, by simpa only [Set.mem_preimage, hq] using hx, hq⟩

/-- Finite presentation on an affine chart of a morphism that is flat at every point of its
source: the pullback of the module to the spectrum of the sections of an affine open `V` of the
source lying over an affine open `W` of the base is of finite presentation, provided `W` sits
inside an open meeting the weakly associated points of the base in a finite set. -/
private theorem isFinitePresentation_pullback_of_flat_affine
    {Y S : Scheme.{u}} (g : Y ⟶ S) [LocallyOfFinitePresentation g]
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    (hflat : ∀ y : Y, IsFlatOverAt g.toLRSHom.toShHom G y)
    {W : S.Opens} (hW : IsAffineOpen W)
    (hWA : (weaklyAssociatedPrimes (Γ(S, W) : Type u) (Γ(S, W) : Type u)).Finite)
    {V : Y.Opens} (hV : IsAffineOpen V) (hVW : V ≤ g ⁻¹ᵁ W) :
    ((Scheme.Modules.pullback hV.fromSpec).obj G).IsFinitePresentation := by
  let B := Γ(Y, V)
  let φ : Γ(S, W) ⟶ B := g.appLE W V hVW
  let j : Spec B ⟶ Y := hV.fromSpec
  let _ : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  let H : (Spec B).Modules := G.restrict j
  have : H.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j G
  have : H.IsFiniteType := Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict j G
  let M := moduleSpecΓFunctor.obj H
  have : Module.Finite B M := moduleFinite_of_isFiniteType_qc B H
  let _ : Algebra (Γ(S, W) : Type u) B := φ.hom.toAlgebra
  let _ : Module (Γ(S, W) : Type u) M := Module.compHom M φ.hom
  let _ : IsScalarTower (Γ(S, W) : Type u) B M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hφ : RingHom.FinitePresentation φ.hom := g.finitePresentation_appLE hW hV hVW
  have : Algebra.FinitePresentation (Γ(S, W) : Type u) B :=
    RingHom.finitePresentation_algebraMap.mpr hφ
  have hjg : Spec.map φ ≫ hW.fromSpec = j ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hW hV hVW
  have hflatlocalized (q : PrimeSpectrum B) :
      Module.Flat (Γ(S, W) : Type u) (LocalizedModule.AtPrime q.asIdeal M) := by
    refine ((isOpen_flatOverAt_spec_of_finite_weakAss hW φ hφ H hWA).2 q).mp ?_
    rw [hjg]
    exact (isFlatOverAt_restrict_iff j g G q).mpr (hflat (j q))
  -- the whole spectrum is the basic open of `1`, so Stacks 05IL applies there
  have hMfp : Module.FinitePresentation B M := by
    refine Module.FinitePresentation.of_localizationSpan (s := ({1} : Set B)) (by simp) fun a => ?_
    rw [show a.1 = (1 : B) from Set.mem_singleton_iff.mp a.2]
    exact Stacks.Flatness.finitePresentation_localizedModule_away_of_basicOpen_subset_flatLocus
      hWA (1 : B) fun q _ => hflatlocalized q
  exact (SheafOfModules.isFinitePresentation (Spec B).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback j).app G)
    ((SheafOfModules.isFinitePresentation (Spec B).ringCatSheaf).prop_of_iso
      (@asIso _ _ _ _ H.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent H))
      ((tilde_isFinitePresentation_iff M).2 hMfp))

/-- **Stacks Project, Tag 05IK (finite presentation on the flat locus).** For a morphism locally
of finite presentation whose target has locally finite weakly associated points, a quasi-coherent
module of finite type is of finite presentation after restriction to any open subscheme contained
in its relative flat locus. -/
theorem isFinitePresentation_restrict_of_subset_flatLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite)
    (U : X.Opens) (hU : (U : Set X) ⊆ flatLocus f F) :
    (F.restrict U.ι).IsFinitePresentation := by
  let Y := U.toScheme
  let g : Y ⟶ S := U.ι ≫ f
  let G : Y.Modules := F.restrict U.ι
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor U.ι F
  have : G.IsFiniteType := Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict U.ι F
  have hflat (y : Y) : IsFlatOverAt g.toLRSHom.toShHom G y :=
    (isFlatOverAt_restrict_iff U.ι f F y).mpr (hU y.2)
  -- the charts of the cover: an affine `V` of `U` over an affine `W` of `S` inside a witness
  let I : Type u := Σ W : S.affineOpens, {V : Y.affineOpens //
      (weaklyAssociatedPrimes (Γ(S, W.1) : Type u) (Γ(S, W.1) : Type u)).Finite ∧
        V.1 ≤ g ⁻¹ᵁ W.1}
  let 𝒰open : Y.Cover (Scheme.precoverage @IsOpenImmersion) :=
    Scheme.Cover.mkOfCovers I (fun i => Spec Γ(Y, i.2.1.1))
      (fun i => i.2.1.2.fromSpec)
      (fun y => by
        obtain ⟨W, V, hW, hWA, hV, hVW, hyV⟩ :=
          exists_affine_chart_of_locally_finite_weakAss g hS y
        let _ : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
        have hrange : y ∈ Scheme.Hom.opensRange hV.fromSpec := by
          rwa [hV.opensRange_fromSpec]
        obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp hrange
        exact ⟨⟨⟨W, hW⟩, ⟨V, hV⟩, hWA, hVW⟩, z, hz⟩)
      (fun i => i.2.1.2.isOpenImmersion_fromSpec)
  let 𝒰 : Y.Cover Scheme.fpqcPrecoverage :=
    { __ := 𝒰open.toPreZeroHypercover
      mem₀ := Scheme.zariskiPrecoverage_le_fpqcPrecoverage Y 𝒰open.mem₀ }
  exact isFinitePresentation_of_pullback_fpqcCover G 𝒰 fun i =>
    isFinitePresentation_pullback_of_flat_affine g G hflat i.1.2 i.2.2.1 i.2.1.2 i.2.2.2

/-- **Stacks Project, Tag 05IK (finite presentation on the flat locus).** For a morphism locally
of finite presentation whose target has locally finite weakly associated points, a quasi-coherent
module of finite type restricts to a module of finite presentation on the open subscheme that is
its relative flat locus. -/
@[stacks 05IK "finite presentation on the flat locus"]
theorem isFinitePresentation_flatLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) :
    letI U : X.Opens := ⟨flatLocus f F, isOpen_flatLocus f F hS⟩
    (F.restrict U.ι).IsFinitePresentation :=
  isFinitePresentation_restrict_of_subset_flatLocus f F hS _ Set.Subset.rfl

/-- **Stacks Project, Tag 05IK (flatness on the flat locus).** For a morphism locally of finite
presentation whose target has locally finite weakly associated points, a quasi-coherent module of
finite type restricts to a module flat over the base on the open subscheme that is its relative
flat locus. -/
@[stacks 05IK "flatness over the base on the flat locus"]
theorem isFlatOver_flatLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) :
    letI U : X.Opens := ⟨flatLocus f F, isOpen_flatLocus f F hS⟩
    IsFlatOver (U.ι ≫ f).toLRSHom.toShHom (F.restrict U.ι) :=
  isFlatOver_restrict_of_subset_flatLocus f F _ Set.Subset.rfl

end

end AlgebraicGeometry
