module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayFromModule

/-!
# A dualizing module makes a locally Noetherian scheme Cohen–Macaulay

Let `X` be a locally Noetherian scheme and let `ω_X` be an `𝒪_X`-module whose degree-zero complex
`ω_X[0]` is a dualizing complex on `X` (`Stacks.Duality.IsDualizingComplex`, [Stacks, Tag 0A87]).
Then `X` is a Cohen–Macaulay scheme (`AlgebraicGeometry.IsCohenMacaulay`, [Stacks, Tag 02IO]). This
is [Stacks, Tag 0AWU].

The content is entirely the ring-level statement [Stacks, Tag 0DW5]
(`Dualizing.isCohenMacaulayRing_of_dualizingModule`): a Noetherian ring carrying a finite module
whose degree-zero complex is dualizing is Cohen–Macaulay. What this file supplies is the passage
from the scheme to its affine opens. `AlgebraicGeometry.IsCohenMacaulay` asks, at every point, for
an affine open neighbourhood with Cohen–Macaulay ring of sections, and
`Stacks.Duality.IsDualizingComplex` provides, at every affine open `U`, a dualizing complex `ω`
over `Γ(X, U)` whose associated sheaf is `ω_X[0]|_U`. So the only thing to check is that such an
`ω` again has its cohomology in the single degree zero, hence is the degree-zero complex of a
finite `Γ(X, U)`-module.

That check is the two exact functors of `Stacks.Duality.HasDualizingModelOn` read on cohomology.
Restriction along `U ⟶ X` and the composite of the associated-sheaf functor with restriction along
`U ≅ Spec Γ(X, U)` both commute with cohomology (`Dualizing.mapDerivedCategoryHomologyIso`), so
`H^i(ω)` becomes zero as a sheaf on `U` for `i ≠ 0`; and that forces `H^i(ω) = 0`, because
restricting back along the inverse of `U ≅ Spec Γ(X, U)` returns to `Spec Γ(X, U)`, where
`AlgebraicGeometry.tilde.functor` is fully faithful and therefore reflects zero objects.

## Main results

* `Stacks.Duality.isCohenMacaulayRing_sections_of_hasDualizingModelOn` — an affine open carrying a
  dualizing model of a complex concentrated in degree zero has Cohen–Macaulay ring of sections.
* `Stacks.Duality.isCohenMacaulay_of_isDualizingComplex_single` — a locally Noetherian scheme
  carrying an `𝒪_X`-module `ω_X` with `ω_X[0]` dualizing is Cohen–Macaulay.
* `Stacks.Duality.isCohenMacaulay_of_exists_coherent_dualizingModule` — a locally Noetherian scheme
  carrying a coherent `ω_X` with `ω_X[0]` dualizing is Cohen–Macaulay.

## Implementation notes

Coherence of `ω_X` is a hypothesis of the tagged statement but is not used: finiteness of the
cohomology modules is already part of the definition of a dualizing complex over a Noetherian ring
([Stacks, Tag 0A7B]).

`D(𝒪_X)` is an instance argument, matching `Stacks.Duality.IsDualizingComplex`. The derived
categories `D(𝒪_U)` and `D(Γ(X, U))` that `Stacks.Duality.HasDualizingModelOn` uses are those of
`HasDerivedCategory.standard`, which is also the choice in the statement of
`Dualizing.isCohenMacaulayRing_of_dualizingModule`.

## References

* [Stacks Project, Tag 0AWU](https://stacks.math.columbia.edu/tag/0AWU)
* [Stacks Project, Tag 0DW5](https://stacks.math.columbia.edu/tag/0DW5)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 02IO](https://stacks.math.columbia.edu/tag/02IO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

/-- Being a dualizing complex over a Noetherian ring depends on the object only through its
isomorphism class in the derived category. -/
theorem ringIsDualizingComplex_of_iso {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {K L : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ L)
    (hK : Dualizing.IsDualizingComplex K) : Dualizing.IsDualizingComplex L := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, I, hGE, hLE, hI, ⟨h⟩⟩ := hK.finiteInjectiveDimension
    exact ⟨a, b, I, hGE, hLE, hI, ⟨e.symm ≪≫ h⟩⟩
  · intro i
    have : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
      hK.finiteCohomology i
    exact Module.Finite.equiv
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e).toLinearEquiv)
  · intro I hI hInjective hBounded
    exact hK.homothetyQuasiIso I ⟨hI.some ≪≫ e.symm⟩ hInjective hBounded

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **The ring of sections of an affine open carrying a dualizing model of `ω_X[0]` is
Cohen–Macaulay.** -/
theorem isCohenMacaulayRing_sections_of_hasDualizingModelOn (omegaX : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U)
    (h : HasDualizingModelOn ((DerivedCategory.singleFunctor X.Modules 0).obj omegaX) U hU) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    IsCohenMacaulayRing Γ(X, U) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨D, hD, ⟨e⟩⟩ := h
  set K := (DerivedCategory.singleFunctor X.Modules 0).obj omegaX with hK
  set G := Scheme.Modules.restrictFunctor U.ι with hG
  set F := tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom with hF
  have hback : Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.inv ≅ 𝟭 (Spec Γ(X, U)).Modules :=
    (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hU.isoSpec.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId
  have hvan : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D) := by
    intro i hi
    have hKzero : IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact DerivedCategory.isZero_of_isGE K 0 i hlt
      · exact DerivedCategory.isZero_of_isLE K 0 i hgt
    have hGK : IsZero ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
        (G.mapDerivedCategory.obj K)) :=
      (G.map_isZero hKzero).of_iso ((Dualizing.mapDerivedCategoryHomologyIso G i).app K)
    have hFD : IsZero ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
        (F.mapDerivedCategory.obj D)) :=
      hGK.of_iso ((DerivedCategory.homologyFunctor U.toScheme.Modules i).mapIso e).symm
    have hFH : IsZero (F.obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D)) :=
      hFD.of_iso ((Dualizing.mapDerivedCategoryHomologyIso F i).app D).symm
    have hTilde : IsZero ((tilde.functor Γ(X, U)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D)) :=
      ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).map_isZero hFH).of_iso
        (hback.app _).symm
    exact IsZero.of_full_of_faithful_of_isZero (tilde.functor Γ(X, U)) _ hTilde
  let : D.IsGE 0 := (DerivedCategory.isGE_iff D 0).2 fun i hi => hvan i (by lia)
  let : D.IsLE 0 := (DerivedCategory.isLE_iff D 0).2 fun i hi => hvan i (by lia)
  obtain ⟨M, ⟨eD⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D 0
  let : Module.Finite Γ(X, U)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) 0).obj D) :=
    hD.finiteCohomology 0
  let : Module.Finite Γ(X, U) M :=
    Module.Finite.equiv
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) 0).mapIso eD ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} Γ(X, U)) 0).app M).toLinearEquiv)
  exact Dualizing.isCohenMacaulayRing_of_dualizingModule.{u, u} M
    (ringIsDualizingComplex_of_iso eD hD)

/-- **A locally Noetherian scheme with a dualizing module is Cohen–Macaulay.** Let `X` be a locally
Noetherian scheme and `ω_X` an `𝒪_X`-module such that `ω_X[0]` is a dualizing complex on `X`; then
`X` is a Cohen–Macaulay scheme. -/
theorem isCohenMacaulay_of_isDualizingComplex_single (omegaX : X.Modules)
    (hdual : IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules 0).obj omegaX)) :
    AlgebraicGeometry.IsCohenMacaulay X := by
  refine (AlgebraicGeometry.isCohenMacaulay_iff X).2 fun x => ?_
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  exact ⟨⟨V, hV⟩, hxV, ⟨inferInstance,
    isCohenMacaulayRing_sections_of_hasDualizingModelOn omegaX V hV (hdual V hV)⟩⟩

/-- Let `X` be a locally Noetherian scheme. If there exists a coherent sheaf `ω_X` such that
`ω_X[0]` is a dualizing complex on `X`, then `X` is a Cohen–Macaulay scheme. -/
@[stacks 0AWU]
theorem isCohenMacaulay_of_exists_coherent_dualizingModule
    (h : ∃ omegaX : X.Modules, _root_.SheafOfModules.IsCoherent omegaX ∧
      IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules 0).obj omegaX)) :
    AlgebraicGeometry.IsCohenMacaulay X := by
  obtain ⟨omegaX, -, hdual⟩ := h
  exact isCohenMacaulay_of_isDualizingComplex_single omegaX hdual

end Stacks.Duality

end
