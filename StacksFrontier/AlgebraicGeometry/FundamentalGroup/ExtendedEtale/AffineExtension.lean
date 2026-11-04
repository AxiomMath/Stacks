module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.AffineCase
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenExtension
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A coherent module on an open of an affine Noetherian scheme extends

Let `X` be an affine scheme with Noetherian ring of global sections and let `U ⊆ X` be an open.
Then every coherent `𝒪_U`-module is the restriction of a coherent `𝒪_X`-module. This is the
affine case of [Stacks, Tag 0G41] part (2).

## Main results

* `exists_isCoherent_restrict_iso_spec` — the statement on `Spec R` for `R` Noetherian.
* `exists_isCoherent_restrict_iso` — the statement on an arbitrary affine locally Noetherian
  scheme.

## References

* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-! ### The case of the spectrum of a Noetherian ring -/

/-- **A coherent module on an open of the spectrum of a Noetherian ring extends.** Every coherent
module on an open `U` of `Spec R`, for `R` Noetherian, is the restriction to `U` of a coherent
module on `Spec R`. -/
@[sga "6 0 2.5" "special case"]
public theorem exists_isCoherent_restrict_iso_spec {R : CommRingCat.{u}} [IsNoetherianRing R]
    (U : (Spec R).Opens) (G : U.toScheme.Modules)
    [_root_.SheafOfModules.IsCoherent G] :
    ∃ E : (Spec R).Modules, _root_.SheafOfModules.IsCoherent E ∧
      Nonempty (E.restrict U.ι ≅ G) := by
  have hU : IsCompact U.1 := NoetherianSpace.isCompact _
  have : QuasiCompact U.ι := quasiCompact_ι_of_isCompact U hU
  have hGq : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hGft : G.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  obtain ⟨F, hFq, ⟨eF⟩⟩ := exists_quasicoherent_restrict_iso U.ι G
  have : F.IsQuasicoherent := hFq
  have hFU : (F.restrict U.ι).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} eF.symm
  obtain ⟨K, hKq, hKft, hKiso⟩ :=
    exists_finiteTypeQuasicoherentSubobject_isIso_restrict F U hU hFU
  have : (K : (Spec R).Modules).IsQuasicoherent := hKq
  have : (K : (Spec R).Modules).IsFiniteType := hKft
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map K.arrow) := hKiso
  exact ⟨(K : (Spec R).Modules),
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _,
    ⟨asIso ((Scheme.Modules.restrictFunctor U.ι).map K.arrow) ≪≫ eF⟩⟩

/-! ### The case of an arbitrary affine scheme -/

/-- **A coherent module on an open of an affine locally Noetherian scheme extends.** Every
coherent module on an open `U` of `X` is the restriction to `U` of a coherent module on `X`. -/
public theorem exists_isCoherent_restrict_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsAffine X] (U : X.Opens) (G : U.toScheme.Modules)
    [_root_.SheafOfModules.IsCoherent G] :
    ∃ E : X.Modules, _root_.SheafOfModules.IsCoherent E ∧
      Nonempty (E.restrict U.ι ≅ G) := by
  have hR : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let ε : X ≅ Spec Γ(X, ⊤) := X.isoSpec
  let U' : (Spec Γ(X, ⊤)).Opens := ε.hom ''ᵁ U
  let φ : U.toScheme ≅ U'.toScheme := ε.hom.isoImage U
  have hφ : φ.hom ≫ U'.ι = U.ι ≫ ε.hom := Scheme.Hom.isoImage_hom_ι ε.hom U
  have hGq : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let G' : U'.toScheme.Modules := (Scheme.Modules.pushforward φ.hom).obj G
  have hG'c : _root_.SheafOfModules.IsCoherent G' :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite φ.hom G
  obtain ⟨E', hE'c, ⟨e'⟩⟩ := exists_isCoherent_restrict_iso_spec U' G'
  have : _root_.SheafOfModules.IsCoherent E' := hE'c
  have hE'q : E'.IsQuasicoherent := isQuasicoherent_of_isCoherent E'
  refine ⟨(Scheme.Modules.pushforward ε.inv).obj E',
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite ε.inv E',
    ⟨?_⟩⟩
  calc ((Scheme.Modules.pushforward ε.inv).obj E').restrict U.ι
      ≅ ((Scheme.Modules.pushforward ε.inv).obj E').restrict (φ.hom ≫ U'.ι ≫ ε.inv) :=
        (Scheme.Modules.restrictFunctorCongr (by
          rw [← Category.assoc, hφ, Category.assoc, ε.hom_inv_id, Category.comp_id])).app _
    _ ≅ (((Scheme.Modules.pushforward ε.inv).obj E').restrict (U'.ι ≫ ε.inv)).restrict φ.hom :=
        (Scheme.Modules.restrictFunctorComp φ.hom (U'.ι ≫ ε.inv)).app _
    _ ≅ ((((Scheme.Modules.pushforward ε.inv).obj E').restrict ε.inv).restrict
          U'.ι).restrict φ.hom :=
        (Scheme.Modules.restrictFunctor φ.hom).mapIso
          ((Scheme.Modules.restrictFunctorComp U'.ι ε.inv).app _)
    _ ≅ (E'.restrict U'.ι).restrict φ.hom :=
        (Scheme.Modules.restrictFunctor φ.hom).mapIso
          ((Scheme.Modules.restrictFunctor U'.ι).mapIso
            ((Scheme.Modules.restrictFunctorAdjCounitIso ε.inv).app E'))
    _ ≅ G'.restrict φ.hom := (Scheme.Modules.restrictFunctor φ.hom).mapIso e'
    _ ≅ G := (Scheme.Modules.restrictFunctorAdjCounitIso φ.hom).app G

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
