module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.PullbackIsoInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AffineDualAmplitudeUniform
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDualityBounded

/-!
# The amplitude of duality against a dualizing complex, on the slice site over an affine open

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` ([Stacks, Tag 0A87]) and
`W ⊆ X` an affine open.
`Stacks.Duality.exists_hasInjectiveAmplitude_forall_isLE_derivedSheafHomTilde` and its companion
below prove the two amplitude bounds

`A ∈ D^{≥q}  ⟹  R𝓗om(A, ω̃) ∈ D^{≤b-q}`,
`A ∈ D^{≤q}  ⟹  R𝓗om(A, ω̃) ∈ D^{≥a-q}`

for `A` in `D_Coh(𝒪_{Spec R})`, with `[a, b]` depending only on the dualizing complex `ω` and not
on `A` or `q`. The dévissage of
`AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHomEvaluation_of_truncLE_approximation`
applies those bounds to objects that are born on a *slice site* `Opens(X)/W` — the cone of a
strictly perfect approximation, which exists over `W` and nowhere else — and so needs them there.
This file restates them on `Opens(X)/W`, for `W` affine.

Everything runs over one functor, `Stacks.Duality.sliceSpecFunctor W hW`: restriction of the
slice-site model of `𝒪_X|_W`-modules to the open-subscheme model
(`AlgebraicGeometry.Scheme.Modules.overEquiv`) followed by restriction along the inverse of
`W ≅ Spec Γ(X, W)`, each induced on unbounded derived categories. It carries the derived internal
Hom of the slice site to the derived internal Hom of `Spec Γ(X, W)`
(`Stacks.Duality.sliceSpecDerivedSheafHomIso`), it carries `K|_W` to the sheafification of a
dualizing complex for `Γ(X, W)`
(`Stacks.Duality.exists_isDualizingComplex_iso_sliceSpecFunctor_restrict`), and — being built from
two equivalences — it reflects the two cohomological bounds
(`Stacks.Duality.isLE_of_isLE_sliceSpecFunctor_obj`,
`Stacks.Duality.isGE_of_isGE_sliceSpecFunctor_obj`), which is what lets a bound established over
`Spec Γ(X, W)` be read back on the slice site.

## Main definitions

* `Stacks.Duality.sliceSpecModulesFunctor` and `Stacks.Duality.sliceSpecFunctor`: the transport,
  on modules and on derived categories.
* `Stacks.Duality.sliceSpecFunctorHomologyIso`: the transport commutes with cohomology, both of
  its factors being exact.
* `Stacks.Duality.sliceSpecDerivedSheafHomIso`: the transport carries the derived internal Hom of
  the slice site to the derived internal Hom of `Spec Γ(X, W)`.
* `Stacks.Duality.sliceSpecFunctorRestrictIso`: on an object restricted from `X`, the transport is
  the iterated restriction along `W.ι` and `(W ≅ Spec Γ(X, W))⁻¹`.

## Main results

* `Stacks.Duality.isLE_of_isLE_sliceSpecFunctor_obj` and
  `Stacks.Duality.isGE_of_isGE_sliceSpecFunctor_obj`: the transport reflects the two bounds.
* `Stacks.Duality.exists_isDualizingComplex_iso_sliceSpecFunctor_restrict`: the transport of `K|_W`
  is the derived sheafification of a dualizing complex for `Γ(X, W)`.
* `Stacks.Duality.isCoherent_homology_sliceSpecFunctor_restrict`: the transport of the restriction
  of an object of `D_Coh(𝒪_X)` has coherent cohomology sheaves.
* `Stacks.Duality.isCoherent_homology_sliceSpecFunctor_derivedSheafHom`: **duality against `K|_W`
  preserves coherence, read through the transport.** This is the second assertion of
  [Stacks, Tag 0A89] in the form the two bounds compose along: the output of either bound satisfies
  the coherence hypothesis of the other.
* `Stacks.Duality.exists_forall_isLE_derivedSheafHomSlice` and
  `Stacks.Duality.exists_forall_isGE_derivedSheafHomSlice`: **the two amplitude bounds on the
  slice site over an affine open**, with the interval chosen before the object, exactly as in
  `Stacks.Duality.exists_hasInjectiveAmplitude_forall_isLE_derivedSheafHomTilde`.

## The coherence hypothesis

The two bounds and the coherence statement ask for coherence of the cohomology sheaves of
`sliceSpecFunctor W hW |>.obj A`, an object of `D(𝒪_{Spec Γ(X, W)})`, rather than of `A` itself.
That is the form `Stacks.Duality.exists_iso_tilde_of_isCoherent_homology` consumes, and it is the
form every producer here delivers: `isCoherent_homology_sliceSpecFunctor_restrict` for an object
restricted from `X`, `isCoherent_homology_sliceSpecFunctor_derivedSheafHom` for a derived internal
Hom, and the weak Serre closure of
`StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory` over `Spec Γ(X, W)` for the
vertices of a distinguished triangle, `sliceSpecFunctor W hW` being triangulated.

Reading the hypothesis instead as `Stacks.SheafOfModules.Site.HasCoherentCohomology A` on the
slice site would need coherence to travel along `AlgebraicGeometry.Scheme.Modules.overEquiv`, of
which the library has the finite-type half
(`AlgebraicGeometry.Modules.isFiniteType_overEquiv_functor` and its inverse companion) and not the
kernel-condition half; the two readings are therefore not compared here.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHom`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-! ### The transport from the slice site over an affine open to its spectrum -/

/-- **The transport of `𝒪_X|_W`-modules from the slice site `Opens(X)/W` to `Spec Γ(X, W)`**, for
`W` an affine open: the equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` onto the
open-subscheme model, followed by restriction along the inverse of `W ≅ Spec Γ(X, W)`. Both
factors are equivalences, so this functor is faithful and exact. -/
def sliceSpecModulesFunctor (W : X.Opens) (hW : IsAffineOpen W) :
    SheafOfModules.{u} (X.ringCatSheaf.over W) ⥤ (Spec Γ(X, W)).Modules :=
  (Scheme.Modules.overEquiv W).functor ⋙ Scheme.Modules.restrictFunctor hW.isoSpec.inv

/-- **The transport of `Stacks.Duality.sliceSpecModulesFunctor` to unbounded derived
categories.** -/
def sliceSpecFunctor (W : X.Opens) (hW : IsAffineOpen W) :
    DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W)) ⥤
      DerivedCategory (Spec Γ(X, W)).Modules :=
  (Scheme.Modules.overEquiv W).functor.mapDerivedCategory ⋙
    (Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapDerivedCategory

section Transport

variable (W : X.Opens) (hW : IsAffineOpen W)

/-- The transport is faithful: `overEquiv W` is an equivalence, and restriction along an
isomorphism of schemes is isomorphic to the pullback along it, which is one. -/
instance faithful_sliceSpecModulesFunctor : (sliceSpecModulesFunctor W hW).Faithful := by
  dsimp only [sliceSpecModulesFunctor]
  have h0 : (Stacks.SheafOfModules.PullbackIsoTensor.pullbackMod hW.isoSpec.inv).Faithful :=
    inferInstance
  have h1 : (Scheme.Modules.restrictFunctor hW.isoSpec.inv).Faithful :=
    Functor.Faithful.of_iso (F := Stacks.SheafOfModules.PullbackIsoTensor.pullbackMod
      hW.isoSpec.inv) (Scheme.Modules.restrictFunctorIsoPullback hW.isoSpec.inv).symm
  exact Functor.Faithful.comp _ _

/-- The transport is additive. -/
instance additive_sliceSpecModulesFunctor : (sliceSpecModulesFunctor W hW).Additive := by
  dsimp only [sliceSpecModulesFunctor]; infer_instance

/-- **The transport commutes with cohomology.** Both of its factors are exact, so each of them
commutes with the degree-`n` cohomology functor by
`DerivedCategoryB.mapDerivedCategoryHomologyIso`. -/
def sliceSpecFunctorHomologyIso (n : ℤ) :
    sliceSpecFunctor W hW ⋙ DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules n ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (X.ringCatSheaf.over W)) n ⋙
        sliceSpecModulesFunctor W hW :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (DerivedCategoryB.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor hW.isoSpec.inv) n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (DerivedCategoryB.mapDerivedCategoryHomologyIso
        (Scheme.Modules.overEquiv W).functor n) _ ≪≫
    Functor.associator _ _ _

/-- A faithful additive functor reflects the zero object: it is faithful on the identity of the
object, which is zero exactly when the object is. -/
private theorem isZero_of_isZero_sliceSpecModulesFunctor
    {M : SheafOfModules.{u} (X.ringCatSheaf.over W)}
    (h : IsZero ((sliceSpecModulesFunctor W hW).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine (sliceSpecModulesFunctor W hW).map_injective ?_
  rw [(sliceSpecModulesFunctor W hW).map_id, (sliceSpecModulesFunctor W hW).map_zero]
  exact (IsZero.iff_id_eq_zero _).1 h

/-- **The transport reflects a bound above.** Its cohomology is the transport of the cohomology,
and the transport on modules reflects the zero object. -/
theorem isLE_of_isLE_sliceSpecFunctor_obj
    (E : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))) (n : ℤ)
    (h : ((sliceSpecFunctor W hW).obj E).IsLE n) : E.IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine isZero_of_isZero_sliceSpecModulesFunctor W hW ?_
  exact IsZero.of_iso ((DerivedCategory.isLE_iff _ n).1 h i hi)
    ((sliceSpecFunctorHomologyIso W hW i).app E).symm

/-- **The transport reflects a bound below.** -/
theorem isGE_of_isGE_sliceSpecFunctor_obj
    (E : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))) (n : ℤ)
    (h : ((sliceSpecFunctor W hW).obj E).IsGE n) : E.IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  refine isZero_of_isZero_sliceSpecModulesFunctor W hW ?_
  exact IsZero.of_iso ((DerivedCategory.isGE_iff _ n).1 h i hi)
    ((sliceSpecFunctorHomologyIso W hW i).app E).symm

/-- **The transport carries the derived internal Hom of the slice site to the derived internal Hom
of `Spec Γ(X, W)`.** This is `Stacks.SheafOfModules.derivedSheafHomSchemeOpenIso`, the transport
of [Stacks, Tag 0E8H] along `overEquiv W`, followed by
`Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso`, its transport along an isomorphism of
schemes. -/
def sliceSpecDerivedSheafHomIso
    (A B : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))) :
    (sliceSpecFunctor W hW).obj ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
        W).derivedSheafHomBifunctor.obj (op A)).obj B) ≅
      ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, W)).sheaf).obj
        (op ((sliceSpecFunctor W hW).obj A))).obj ((sliceSpecFunctor W hW).obj B) :=
  (Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapDerivedCategory.mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeOpenIso W A B) ≪≫
    Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso hW.isoSpec.inv _ _

end Transport

/-! ### The transport of an object restricted from the scheme -/

section Restrict

variable [IsLocallyNoetherian X] (W : X.Opens) (hW : IsAffineOpen W)

/-- **On an object restricted from `X`, the transport is the iterated restriction.** Restriction
to the slice site followed by `overEquiv W` is restriction along the open immersion `W.ι`
(`Stacks.SheafOfModules.derivedOverFunctorEquiv`), and the second factor of the transport is left
untouched. -/
def sliceSpecFunctorRestrictIso (E : DerivedCategory X.Modules) :
    (sliceSpecFunctor W hW).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj E) ≅
      (Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E) :=
  (Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapDerivedCategory.mapIso
    ((Stacks.SheafOfModules.derivedOverFunctorEquiv W).app E)

/-- **The transport of the restriction of an object of `D_Coh(𝒪_X)` has coherent cohomology
sheaves.** On such an object the transport is the iterated restriction along two open immersions,
and coherence of all cohomology sheaves survives each of them
(`Stacks.Duality.isCoherent_homology_restrictFunctor`). -/
theorem isCoherent_homology_sliceSpecFunctor_restrict (E : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsCoherent) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules n).obj
      ((sliceSpecFunctor W hW).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj
          E))).IsCoherent := by
  have hR : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have _ : IsLocallyNoetherian (Spec Γ(X, W)) := isLocallyNoetherian_Spec.mpr hR
  refine isCoherent_of_modulesIso
    ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules n).mapIso
      (sliceSpecFunctorRestrictIso W hW E)).symm ?_
  exact isCoherent_homology_restrictFunctor hW.isoSpec.inv _
    (fun j => isCoherent_homology_restrictFunctor W.ι E hE j) n

/-- **The transport of `K|_W` is the derived sheafification of a dualizing complex for
`Γ(X, W)`.** This is `Stacks.Duality.exists_isDualizingComplex_iso_tilde_of_hasDualizingModelOn`
read through `Stacks.Duality.sliceSpecFunctorRestrictIso`. -/
theorem exists_isDualizingComplex_iso_sliceSpecFunctor_restrict
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    letI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, W)), Dualizing.IsDualizingComplex ω ∧
      Nonempty ((sliceSpecFunctor W hW).obj ((SheafOfModules.overFunctor.{u} X.ringCatSheaf
            W).mapDerivedCategory.obj K) ≅
        (tilde.functor Γ(X, W)).mapDerivedCategory.obj ω) := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨ω, hω, ⟨e⟩⟩ :=
    exists_isDualizingComplex_iso_tilde_of_hasDualizingModelOn hW K (hK W hW)
  exact ⟨ω, hω, ⟨sliceSpecFunctorRestrictIso W hW K ≪≫ e⟩⟩

/-! ### The two amplitude bounds, and coherence, on the slice site -/

/-- `sliceSpecDerivedSheafHomIso` followed by an isomorphism of the second argument. -/
private def sliceSpecDerivedSheafHomIsoOfIso
    (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W)))
    {B : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))}
    {B' : DerivedCategory (Spec Γ(X, W)).Modules} (e : (sliceSpecFunctor W hW).obj B ≅ B') :
    (sliceSpecFunctor W hW).obj ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
        W).derivedSheafHomBifunctor.obj (op A)).obj B) ≅
      ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, W)).sheaf).obj
        (op ((sliceSpecFunctor W hW).obj A))).obj B' :=
  sliceSpecDerivedSheafHomIso W hW A B ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, W)).sheaf).obj
      (op ((sliceSpecFunctor W hW).obj A))).mapIso e

/-- **Duality against `K|_W` on the slice site over an affine open preserves coherence, read
through the transport.** For `A` an object of the derived category of `𝒪_X|_W`-modules on
`Opens(X)/W` whose transport to `Spec Γ(X, W)` has coherent cohomology sheaves, the transport of
`R𝓗om_{𝒪_X|_W}(A, K|_W)` has coherent cohomology sheaves too.

Over `Spec Γ(X, W)` the transported object is the derived sheafification of an object of
`D_Coh(Γ(X, W))` (`Stacks.Duality.exists_iso_tilde_of_isCoherent_homology`) and `K|_W` becomes the
derived sheafification of a dualizing complex, so
`Stacks.Duality.isCoherent_homology_derivedSheafHomTilde` — [Stacks, Tag 0A88] followed by
[Stacks, Tag 0G4H] — applies. This is the second assertion of [Stacks, Tag 0A89] in the shape
along which the two amplitude bounds below compose: the conclusion of either one satisfies the
coherence hypothesis of the other. -/
theorem isCoherent_homology_sliceSpecFunctor_derivedSheafHom
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W)))
    (hA : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
      ((sliceSpecFunctor W hW).obj A)).IsCoherent) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules n).obj
      ((sliceSpecFunctor W hW).obj ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
        W).derivedSheafHomBifunctor.obj (op A)).obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj
            K)))).IsCoherent := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨ω, hω, ⟨eK⟩⟩ := exists_isDualizingComplex_iso_sliceSpecFunctor_restrict W hW hK
  obtain ⟨M, hM, ⟨eA⟩⟩ :=
    exists_iso_tilde_of_isCoherent_homology Γ(X, W) ((sliceSpecFunctor W hW).obj A) hA
  refine isCoherent_of_modulesIso
    ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules n).mapIso
      (((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, W)).sheaf).mapIso
            (Iso.op eA.symm)).app _ ≪≫
        (sliceSpecDerivedSheafHomIsoOfIso W hW A eK).symm)) ?_
  exact isCoherent_homology_derivedSheafHomTilde Γ(X, W) M ω hM hω n

/-- **Duality against a dualizing complex on the slice site over an affine open carries
`D^{≥q}` into `D^{≤b-q}`, with `b` independent of the object and of `q`.** Let `X` be a locally
Noetherian scheme, `K` a dualizing complex on it and `W ⊆ X` an affine open. There is an integer
`b`, depending only on `K` and `W`, such that for every object `A` of the derived category of
`𝒪_X|_W`-modules on `Opens(X)/W` whose transport to `Spec Γ(X, W)` has coherent cohomology
sheaves and which has no cohomology below `q`, the object `R𝓗om_{𝒪_X|_W}(A, K|_W)` has no
cohomology above `b - q`.

Over `Spec Γ(X, W)` this is
`Stacks.Duality.exists_hasInjectiveAmplitude_forall_isLE_derivedSheafHomTilde`, with `b` the upper
end of an injective amplitude interval for the dualizing model of `K` over `Γ(X, W)`; the bound is
read back on the slice site by `Stacks.Duality.isLE_of_isLE_sliceSpecFunctor_obj`. -/
theorem exists_forall_isLE_derivedSheafHomSlice {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    ∃ b : ℤ, ∀ (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))) (q : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
        ((sliceSpecFunctor W hW).obj A)).IsCoherent) →
      A.IsGE q →
      ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
        W).derivedSheafHomBifunctor.obj (op A)).obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj
            K)).IsLE (b - q) := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨ω, hω, ⟨eK⟩⟩ := exists_isDualizingComplex_iso_sliceSpecFunctor_restrict W hW hK
  obtain ⟨b, hb⟩ := exists_hasInjectiveAmplitude_forall_isLE_derivedSheafHomTilde Γ(X, W) hω
  refine ⟨b, fun A q hAcoh hAq => ?_⟩
  have hΦA : ((sliceSpecFunctor W hW).obj A).IsGE q :=
    CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ _ q
      (CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ A q hAq)
  have h := hb ((sliceSpecFunctor W hW).obj A) q hAcoh hΦA
  refine isLE_of_isLE_sliceSpecFunctor_obj W hW _ (b - q) ?_
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (sliceSpecDerivedSheafHomIsoOfIso W hW A eK).symm (b - q)

/-- **Duality against a dualizing complex on the slice site over an affine open carries
`D^{≤q}` into `D^{≥a-q}`, with `a` independent of the object and of `q`.** The companion of
`Stacks.Duality.exists_forall_isLE_derivedSheafHomSlice`, with the lower end of the amplitude
interval; over `Spec Γ(X, W)` it is
`Stacks.Duality.exists_hasInjectiveAmplitude_forall_isGE_derivedSheafHomTilde`, and the bound is
read back on the slice site by `Stacks.Duality.isGE_of_isGE_sliceSpecFunctor_obj`. -/
theorem exists_forall_isGE_derivedSheafHomSlice {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    ∃ a : ℤ, ∀ (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))) (q : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
        ((sliceSpecFunctor W hW).obj A)).IsCoherent) →
      A.IsLE q →
      ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
        W).derivedSheafHomBifunctor.obj (op A)).obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj
            K)).IsGE (a - q) := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨ω, hω, ⟨eK⟩⟩ := exists_isDualizingComplex_iso_sliceSpecFunctor_restrict W hW hK
  obtain ⟨a, ha⟩ := exists_hasInjectiveAmplitude_forall_isGE_derivedSheafHomTilde Γ(X, W) hω
  refine ⟨a, fun A q hAcoh hAq => ?_⟩
  have hΦA : ((sliceSpecFunctor W hW).obj A).IsLE q :=
    have h1 : (((Scheme.Modules.overEquiv W).functor.mapDerivedCategory).obj A).IsLE q :=
      Stacks.Homology.isLE_mapDerivedCategory_obj _ A q
    Stacks.Homology.isLE_mapDerivedCategory_obj _ _ q
  have h := ha ((sliceSpecFunctor W hW).obj A) q hAcoh hΦA
  refine isGE_of_isGE_sliceSpecFunctor_obj W hW _ (a - q) ?_
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (sliceSpecDerivedSheafHomIsoOfIso W hW A eK).symm (a - q)

end Restrict

end Stacks.Duality

end
