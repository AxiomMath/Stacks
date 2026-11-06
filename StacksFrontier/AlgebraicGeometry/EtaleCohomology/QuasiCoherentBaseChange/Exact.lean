module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

/-!
# Exactness of `ℱ ↦ ℱᵉ` on short exact sequences

A short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of quasi-coherent modules on a scheme `Z` gives a
short exact sequence `0 → ℱ₁ᵉ → ℱ₂ᵉ → ℱ₃ᵉ → 0` of abelian sheaves on `Z_étale`. Over an étale
`T ⟶ Z` the pullback to `T` is exact because `T ⟶ Z` is flat, so the sections over `T` form a
left exact sequence; over an affine `T` they form a short exact sequence, and the affine
étale `Z`-schemes cover every étale `Z`-scheme, so `ℱ₂ᵉ ⟶ ℱ₃ᵉ` is locally surjective.

The same holds for the pullback of the sequence along any flat morphism `g : Y ⟶ Z`, which is how
it is used for the scalar extension of a scheme over a field.

## Main results

* `AlgebraicGeometry.QcohEtale.shortExact_etaleShortComplex`: the statement for a short complex
  of quasi-coherent modules which is short exact after pullback to every étale `Z`-scheme.
* `AlgebraicGeometry.QcohEtale.shortExact_etaleShortComplex_of_shortExact`: the statement for
  a short exact sequence.
* `AlgebraicGeometry.QcohEtale.shortExact_etaleShortComplex_pullback`: the statement for the
  pullback of a short exact sequence along a flat morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.QcohEtale

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

variable {Z : Scheme.{u}}

/-- An open subscheme of an étale `Z`-scheme, as an étale `Z`-scheme. -/
def openObj (T : Z.Etale) (V : T.left.Opens) : Z.Etale :=
  MorphismProperty.Over.mk ⊤ (V.ι ≫ T.hom) inferInstance

/-- The inclusion of an open subscheme of an étale `Z`-scheme. -/
def openHom (T : Z.Etale) (V : T.left.Opens) : openObj T V ⟶ T :=
  MorphismProperty.Over.homMk V.ι rfl trivial

/-- The underlying morphism of schemes of `openHom T V` is the open immersion `V.ι`. -/
theorem openHom_left (T : Z.Etale) (V : T.left.Opens) : (openHom T V).left = V.ι := rfl

/-- The affine opens of an étale `Z`-scheme cover it. -/
theorem affineCover_mem (T : Z.Etale) :
    Sieve.ofArrows _ (fun V : T.left.affineOpens => openHom T V.1) ∈
      Z.smallEtaleTopology T := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨V, hV, hx, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    T.left.isBasis_affineOpens) (show x ∈ (⊤ : T.left.Opens) from trivial)
  exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, ⟨x, hx⟩, rfl⟩

/-- `ℱᵉ ⟶ 𝒢ᵉ` is locally surjective as soon as it is surjective on sections over the affine
étale `Z`-schemes. -/
theorem isLocallySurjective_etaleMap {F G : Z.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G)
    (hsurj : ∀ T : Z.Etale, IsAffine T.left →
      Function.Surjective (((Scheme.Modules.pullback T.hom).map φ).app ⊤)) :
    Presheaf.IsLocallySurjective Z.smallEtaleTopology (etaleMap φ).hom where
  imageSieve_mem {T} y := by
    refine Z.smallEtaleTopology.superset_covering ?_ (affineCover_mem T)
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro V
    obtain ⟨t, ht⟩ := hsurj (openObj T V.1) V.2
      ((etaleSheaf G).obj.map (openHom T V.1).op y).down
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

/-- **Exactness of `ℱ ↦ ℱᵉ`, sectionwise form.** -/
theorem shortExact_etaleShortComplex (S : ShortComplex Z.Modules) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hmono : ∀ T : Z.Etale,
      Function.Injective (((Scheme.Modules.pullback T.hom).map S.f).app ⊤))
    (hexact : ∀ (T : Z.Etale) (y : Γ((Scheme.Modules.pullback T.hom).obj S.X₂, ⊤)),
      ((Scheme.Modules.pullback T.hom).map S.g).app ⊤ y = 0 →
        ∃ x, ((Scheme.Modules.pullback T.hom).map S.f).app ⊤ x = y)
    (hsurj : ∀ T : Z.Etale, IsAffine T.left →
      Function.Surjective (((Scheme.Modules.pullback T.hom).map S.g).app ⊤)) :
    (etaleShortComplex S).ShortExact := by
  have hmonoT : ∀ T : Z.Etaleᵒᵖ, Mono ((etaleShortComplex S).f.hom.app T) := fun T =>
    (AddCommGrpCat.mono_iff_injective _).2 fun a b hab =>
      ULift.ext (hmono T.unop (congrArg ULift.down hab))
  have hmono' : Mono (etaleShortComplex S).f := by
    have : Mono (etaleShortComplex S).f.hom := NatTrans.mono_of_mono_app _
    exact Sheaf.Hom.mono_of_presheaf_mono _ _ _
  have hepi : Epi (etaleShortComplex S).g :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := (etaleShortComplex S).g)).1
      (isLocallySurjective_etaleMap S.g hsurj)
  have hlim : IsLimit (KernelFork.ofι (etaleShortComplex S).f (etaleShortComplex S).zero) := by
    apply isLimitOfReflects (sheafToPresheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    refine (KernelFork.isLimitMapConeEquiv _ _).symm ?_
    refine evaluationJointlyReflectsLimits _ fun T => ?_
    refine (KernelFork.isLimitMapConeEquiv _ _).symm ?_
    let ST : ShortComplex AddCommGrpCat.{u + 1} := (etaleShortComplex S).map
      (sheafToPresheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation Z.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj T)
    have hST : ST.Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro y hy
      obtain ⟨x, hx⟩ := hexact T.unop y.down (congrArg ULift.down hy)
      exact ⟨ULift.up x, ULift.ext hx⟩
    exact ((ShortComplex.exact_and_mono_f_iff_f_is_kernel ST).1 ⟨hST, hmonoT T⟩).some
  exact { mono_f := hmono', epi_g := hepi, exact := ShortComplex.exact_of_f_is_kernel _ hlim }

/-- The pullback along a flat morphism preserves short exact sequences. -/
private theorem shortExact_map_pullback_of_flat {W : Scheme.{u}} (h : W ⟶ Z) [Flat h]
    {S : ShortComplex Z.Modules} (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pullback h)).ShortExact := by
  have := preservesFiniteLimits_modulesPullback_of_flat h
  exact hS.map_of_exact _

/-- Sections over an étale `Z`-scheme turn the pullback of a short exact sequence of
quasi-coherent modules along a flat morphism into a left exact sequence, and into a short exact
sequence when the source is affine. -/
theorem sections_pullback_of_shortExact {W : Scheme.{u}} (h : W ⟶ Z) [Flat h]
    (S : ShortComplex Z.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : S.ShortExact) :
    Function.Injective (((Scheme.Modules.pullback h).map S.f).app ⊤) ∧
      (∀ y : Γ((Scheme.Modules.pullback h).obj S.X₂, ⊤),
        ((Scheme.Modules.pullback h).map S.g).app ⊤ y = 0 →
          ∃ x, ((Scheme.Modules.pullback h).map S.f).app ⊤ x = y) ∧
      (IsAffine W → Function.Surjective (((Scheme.Modules.pullback h).map S.g).app ⊤)) := by
  have hS' := shortExact_map_pullback_of_flat h hS
  refine ⟨SheafOfModules.injective_of_mono_sections _ hS'.mono_f (op ⊤), 
    (SheafOfModules.exists_of_shortExact_sections hS' (op ⊤)), fun hW => ?_⟩
  have : Epi ((Scheme.Modules.pullback h).map S.g) := hS'.epi_g
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen W
    ((Scheme.Modules.pullback h).map S.g) ⊤ (isAffineOpen_top W)

/-- **`ℱ ↦ ℱᵉ` carries short exact sequences of quasi-coherent modules to short exact
sequences.** -/
theorem shortExact_etaleShortComplex_of_shortExact (S : ShortComplex Z.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (hS : S.ShortExact) :
    (etaleShortComplex S).ShortExact :=
  have h := fun T : Z.Etale => sections_pullback_of_shortExact T.hom S hS
  shortExact_etaleShortComplex S (fun T => (h T).1) (fun T => (h T).2.1) (fun T => (h T).2.2)

/-- **The pullback of a short exact sequence of quasi-coherent modules along a flat morphism
`g : Y ⟶ Z` stays short exact after `ℱ ↦ ℱᵉ` on `Y_étale`.** -/
theorem shortExact_etaleShortComplex_pullback {Y : Scheme.{u}} (g : Y ⟶ Z) [Flat g]
    (S : ShortComplex Z.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : S.ShortExact) :
    (etaleShortComplex (pullbackShortComplex g S)).ShortExact := by
  exact shortExact_etaleShortComplex_of_shortExact _ (shortExact_map_pullback_of_flat g hS)

end AlgebraicGeometry.QcohEtale

end
