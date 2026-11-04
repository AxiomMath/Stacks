module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ShrinkingToBasicOpen
public import StacksFrontier.RingTheory.AdicCompletion.ShortExact

/-!
# Projective sections survive shrinking the base to a basic open

Let `h : Y ⟶ A` be a morphism of affine schemes, `g : Y ⟶ X` a morphism and `F` an
`𝒪_X`-module whose pullback to `Y` is quasi-coherent.  If the global sections of `g^* F` form a
projective `Γ(A, 𝒪_A)`-module (the scalars acting through `h`), then for every global function
`a` on `A` the global sections of the pullback of `F` to the basic open `D(h^♯ a)` of `Y` form a
projective module over the functions on `D(a)`.

This is the shrinking step of Stacks 0CWC, where the base of the affine étale diagram of
Stacks 0CVZ is replaced by a basic open neighbourhood on which the relative assassin is captured.
The same computation is done in the proof of Stacks 05ID for a square of étale neighbourhoods;
here nothing is assumed of `g` and no distinguished point appears.

## Main results

* `AlgebraicGeometry.projective_sections_pullback_basicOpen`: the statement above.

## References

* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Projective sections survive shrinking the base to a basic open.**  For `h : Y ⟶ A` with `Y`
and `A` affine, `g : Y ⟶ X`, an `𝒪_X`-module `F` with quasi-coherent pullback to `Y` whose global
sections are projective over `Γ(A, 𝒪_A)`, and a global function `a` on `A`, the global sections of
the pullback of `F` to `D(h^♯ a)` are projective over `Γ(D(a), 𝒪)`, the scalars acting through
the restriction of `h`. -/
theorem projective_sections_pullback_basicOpen {X Y A : Scheme.{u}} [IsAffine Y] [IsAffine A]
    (h : Y ⟶ A) (g : Y ⟶ X) (F : X.Modules)
    [((Scheme.Modules.pullback g).obj F).IsQuasicoherent] (a : Γ(A, ⊤))
    (hproj :
      letI : Module Γ(A, ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _ h.appTop.hom
      Module.Projective Γ(A, ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    letI : Module Γ((A.basicOpen a).toScheme, ⊤)
        Γ((Scheme.Modules.pullback ((Y.basicOpen (h.appTop.hom a)).ι ≫ g)).obj F, ⊤) :=
      Module.compHom _ (restrictBasicOpenHom h a).appTop.hom
    Module.Projective Γ((A.basicOpen a).toScheme, ⊤)
      Γ((Scheme.Modules.pullback ((Y.basicOpen (h.appTop.hom a)).ι ≫ g)).obj F, ⊤) := by
  let : Algebra Γ(A, ⊤) Γ(Y, ⊤) := h.appTop.hom.toAlgebra
  let : Module Γ(A, ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
    Module.compHom _ h.appTop.hom
  let := modulePullbackBasicOpenSections g F (h.appTop.hom a)
  let : Module Γ(A, ⊤) Γ((Scheme.Modules.pullback
      ((Y.basicOpen (h.appTop.hom a)).ι ≫ g)).obj F, ⊤) :=
    Module.compHom _ ((Y.basicOpen (h.appTop.hom a)).ι.appTop.hom.comp h.appTop.hom)
  have : IsScalarTower Γ(A, ⊤) Γ(Y, ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(A, ⊤) Γ(Y, ⊤)
      Γ((Scheme.Modules.pullback ((Y.basicOpen (h.appTop.hom a)).ι ≫ g)).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hψ₀ : IsLocalizedModule (.powers (algebraMap Γ(A, ⊤) Γ(Y, ⊤) a))
      (pullbackBasicOpenSectionsMap g F (h.appTop.hom a)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact isLocalizedModule_pullbackBasicOpenSectionsMap g F (h.appTop.hom a)
  have hψ : IsLocalizedModule.Away a
      ((pullbackBasicOpenSectionsMap g F (h.appTop.hom a)).restrictScalars Γ(A, ⊤)) :=
    IsLocalizedModule.restrictScalars_powers a _
  let : Algebra Γ(A, ⊤) Γ((A.basicOpen a).toScheme, ⊤) :=
    (A.basicOpen a).ι.appTop.hom.toAlgebra
  have hlocR : IsLocalization.Away a Γ((A.basicOpen a).toScheme, ⊤) :=
    Γ_restrict_isLocalization A a
  let : Module Γ((A.basicOpen a).toScheme, ⊤) Γ((Scheme.Modules.pullback
      ((Y.basicOpen (h.appTop.hom a)).ι ≫ g)).obj F, ⊤) :=
    Module.compHom _ (restrictBasicOpenHom h a).appTop.hom
  have htowerN : IsScalarTower Γ(A, ⊤) Γ((A.basicOpen a).toScheme, ⊤)
      Γ((Scheme.Modules.pullback ((Y.basicOpen (h.appTop.hom a)).ι ≫ g)).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun r t =>
      congrArg (fun z => z • t)
        (congrArg (fun φ : Γ(A, ⊤) ⟶ Γ((Y.basicOpen (h.appTop.hom a)).toScheme, ⊤) =>
          φ.hom r) (appTop_comp_restrictBasicOpenHom_appTop h a))
  let ε : Γ((A.basicOpen a).toScheme, ⊤) ≃+* Localization.Away a :=
    (IsLocalization.algEquiv (Submonoid.powers a) Γ((A.basicOpen a).toScheme, ⊤)
      (Localization.Away a)).toRingEquiv
  let : Module Γ((A.basicOpen a).toScheme, ⊤) (LocalizedModule (Submonoid.powers a)
      Γ((Scheme.Modules.pullback g).obj F, ⊤)) :=
    Module.compHom _ (ε : Γ((A.basicOpen a).toScheme, ⊤) →+* Localization.Away a)
  have htowerL : IsScalarTower Γ(A, ⊤) Γ((A.basicOpen a).toScheme, ⊤)
      (LocalizedModule (Submonoid.powers a) Γ((Scheme.Modules.pullback g).obj F, ⊤)) :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      show ε (algebraMap Γ(A, ⊤) Γ((A.basicOpen a).toScheme, ⊤) r) • m = r • m
      rw [show ε (algebraMap Γ(A, ⊤) Γ((A.basicOpen a).toScheme, ⊤) r) =
          algebraMap Γ(A, ⊤) (Localization.Away a) r from
        (IsLocalization.algEquiv (Submonoid.powers a)
          Γ((A.basicOpen a).toScheme, ⊤) (Localization.Away a)).commutes r,
        IsScalarTower.algebraMap_smul]
  have : Module.Projective Γ(A, ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤) := hproj
  have : Module.Projective (Localization.Away a) (LocalizedModule (Submonoid.powers a)
      Γ((Scheme.Modules.pullback g).obj F, ⊤)) := inferInstance
  have : Module.Projective Γ((A.basicOpen a).toScheme, ⊤)
      (LocalizedModule (Submonoid.powers a) Γ((Scheme.Modules.pullback g).obj F, ⊤)) :=
    Stacks.AdicCompletion.SplitShortExact.projective_of_ringEquiv ε.symm (AddEquiv.refl _)
      (fun c x => congrArg (fun r => r • x) (ε.apply_symm_apply c).symm) ‹_›
  exact Module.Projective.of_equiv'
    (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers a)
      Γ((A.basicOpen a).toScheme, ⊤)
      (IsLocalizedModule.linearEquiv (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a)
          Γ((Scheme.Modules.pullback g).obj F, ⊤))
        ((pullbackBasicOpenSectionsMap g F (h.appTop.hom a)).restrictScalars Γ(A, ⊤))))

end AlgebraicGeometry

end
