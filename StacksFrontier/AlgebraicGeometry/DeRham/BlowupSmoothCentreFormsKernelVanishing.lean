module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsKernel
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsKernelCech

/-!
# Clause (3) of Stacks 0FUU

Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`;
write `b : X' ⟶ X` for the blowing up along `Z`, `j : E ⟶ X'` for the exceptional divisor and
`p : E ⟶ Z` for its projection onto the centre. Clause (3) of [Stacks, Tag 0FUU] says that the
canonical map `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on cohomology sheaves in
every degree `q ≥ 1`.

By `Stacks.DeRham.isIso_homology_blowupFormsRestrictionDerivedComparison_of_isZero` this follows
from the vanishing of `R^q b_*𝒦^a` for `q ≥ 1`, where `𝒦^a` is the kernel of the restriction of
forms `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}`. That vanishing is étale local and holds off the centre and in
codimension `0` (`Stacks.DeRham.isZero_blowupFormsKernelHigherDirectImage_of_coordinate`), so it
reduces to the coordinate situation `𝐀^m_T ⊆ 𝐀^{m+n}_T` over affine `T`, `n ≥ 1`. There it is
transported, along the identification with the coordinate situation of Section 50.16 of the source
and along the identification of the blowup with the cone `L` over the projective bundle `P`
(`Stacks.DeRham.CoordinateCone.coneStacksBlowupIso`, whose exceptional divisor is the zero section
`Stacks.DeRham.CoordinateCone.coneExceptionalIso`), from the vanishing of `R^q b_*𝒦^a_L` on the
cone, which is clause (3) of [Stacks, Tag 0FUR]
(`Stacks.DeRham.CoordinateCone.isZero_homology_derivedPushforward_coneFormsKernel`).

Clause (3) needs no hypothesis on the codimension: where `Z` contains an open of `X`, the blowup
and the exceptional divisor are empty there and both sides vanish.

## Main results

* `Stacks.DeRham.pullbackFormsDirectImageKernelIso`: the kernel of the comparison map on direct
  images of forms along `g` commutes with étale base change.
* `Stacks.DeRham.CoordinateCone.isZero_blowupFormsKernelHigherDirectImage_coordinateEmbedding`:
  the vanishing passes from the cone to the blowup of the coordinate centre.
* `Stacks.DeRham.isZero_blowupFormsKernelHigherDirectImage_of_smooth_of_cone`: the vanishing for
  every closed immersion of schemes smooth over `S`, from the vanishing on the cone.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_isClosedImmersion
  Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

namespace Stacks.DeRham

/-! ### The kernel of the comparison map under étale base change -/

section EtaleBaseChange

variable {X X₁ Y Y₁ S S₁ : Scheme.{u}} {g : Y ⟶ X} {g₁ : Y₁ ⟶ X₁} {ε : X₁ ⟶ X} {ε' : Y₁ ⟶ Y}

/-- **The kernel of `Ω^a_{X/S} ⟶ g_*Ω^a_{Y/S}` under étale base change**: for a cartesian square
with `ε` étale and a compatible étale `e : S₁ ⟶ S`, `ε^*` of the kernel of the comparison map for
`g` is the kernel of the comparison map for `g₁`. The inverse image along the flat `ε` is exact,
and it carries the comparison map for `g` to the one for `g₁` up to the canonical maps of
[Stacks, Tag 0FLV] and flat base change in degree zero. -/
def pullbackFormsDirectImageKernelIso (H : IsPullback ε' g₁ g ε) [Etale ε] [QuasiCompact g]
    [QuasiSeparated g] (π : X ⟶ S) (π₁ : X₁ ⟶ S₁) (e : S₁ ⟶ S) [Etale e]
    (he : ε ≫ π = π₁ ≫ e) (a : ℕ) :
    (Scheme.Modules.pullback ε).obj
        (kernel (Scheme.Hom.formsDirectImageComparison g π (a : ℤ))) ≅
      kernel (Scheme.Hom.formsDirectImageComparison g₁ π₁ (a : ℤ)) :=
  haveI := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ε π π₁ e he (a : ℤ)
  haveI := Scheme.Hom.isIso_baseChange_comp_pushforward_map_relativeDifferentialFormsMap H π π₁ e
    he a
  pullbackKernelIsoOfFlat ε _ ≪≫
    kernel.mapIso _ _ (asIso (Scheme.Hom.relativeDifferentialFormsMap ε π π₁ e he (a : ℤ)))
      (asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
          (Scheme.Hom.relativeDifferentialForms (g ≫ π) (a : ℤ)) ≫
        (Scheme.Modules.pushforward g₁).map
          (Scheme.Hom.relativeDifferentialFormsMap ε' (g ≫ π) (g₁ ≫ π₁) e
            (by rw [← Category.assoc, H.w, Category.assoc, he, Category.assoc]) (a : ℤ))))
      (Scheme.Hom.pullback_map_formsDirectImageComparison_comp H.w π π₁ e he (a : ℤ))

end EtaleBaseChange

/-! ### The vanishing transported along an isomorphism of blowups -/

/-- **The vanishing of `R^q b_*𝒦^a` along an isomorphism of blowups.** Let `κ : L ⟶ X'` be an
isomorphism over `X` from a scheme `b_L : L ⟶ X` to the blowup, under which a closed subscheme
`j₀ : P ⟶ L` corresponds to the exceptional divisor. If `R^q b_{L*}` kills the kernel of the
comparison map `Ω^a_{L/S} ⟶ j₀_*Ω^a_{P/S}` (in the guise of any `K` isomorphic to it), then
`R^q b_*𝒦^a = 0`: flat base change along `𝟙_X` ([Stacks, Tag 02KH]) identifies `R^q b_*𝒦^a` with
`R^q b_{L*}κ^*𝒦^a`, and `κ^*𝒦^a` is that kernel. -/
theorem isZero_blowupFormsKernelHigherDirectImage_of_iso {S X Z L P : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact (Stacks.Blowup.blowUpToBase i.ker)]
    (bL : L ⟶ X) (κ : L ⟶ Stacks.Blowup.blowUp i.ker) [IsIso κ] (hκ : κ ≫ blowupMap i = bL)
    (j₀ : P ⟶ L) (ε'' : P ⟶ Stacks.Blowup.exceptionalDivisor i.ker) [IsIso ε'']
    (hε : ε'' ≫ exceptionalInclusion i = j₀ ≫ κ) (a : ℕ) {K : L.Modules}
    (eK : K ≅ kernel (Scheme.Hom.formsDirectImageComparison j₀ (bL ≫ f) (a : ℤ))) (q : ℤ)
    (h : IsZero ((@Functor.rightDerivedPlus _ _ _ _ _ _ (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (modulePushforward bL.toLRSHom.toShHom) _ _ q).obj K)) :
    IsZero (blowupFormsKernelHigherDirectImage f i (a : ℤ) q) := by
  have hb : IsPullback κ bL (blowupMap i) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hκ]⟩
  have hj : IsPullback ε'' j₀ (exceptionalInclusion i) κ := IsPullback.of_horiz_isIso ⟨hε⟩
  have he : κ ≫ (blowupMap i ≫ f) = (bL ≫ f) ≫ 𝟙 S := by
    rw [← Category.assoc, hκ, Category.comp_id]
  have hbc := Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso hb
    (blowupFormsKernel f i (a : ℤ)) q
  have hK : (modulePullback κ.toLRSHom.toShHom).obj (blowupFormsKernel f i (a : ℤ)) ≅ K :=
    ((Stacks.ProjectiveBundleQuotients.pullbackIso κ).app _).symm ≪≫
      (Scheme.Modules.pullback κ).mapIso (blowupFormsKernelIso f i (a : ℤ)) ≪≫
      pullbackFormsDirectImageKernelIso hj _ (bL ≫ f) (𝟙 S) he a ≪≫ eK.symm
  have h₁ : IsZero ((modulePullback (Scheme.Hom.toLRSHom (𝟙 X)).toShHom).obj
      (blowupFormsKernelHigherDirectImage f i (a : ℤ) q)) :=
    h.of_iso (hbc ≪≫ (@Functor.rightDerivedPlus _ _ _ _ _ _ (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (modulePushforward bL.toLRSHom.toShHom) _ _ q).mapIso hK)
  exact h₁.of_iso (((Scheme.Modules.pullbackId X).app _).symm ≪≫
    (Stacks.ProjectiveBundleQuotients.pullbackIso (𝟙 X)).app _)

/-- `isZero_blowupFormsKernelHigherDirectImage_of_iso` with the vanishing on `L` stated as the
vanishing of `H^q(Rb_{L*}(K[0]))`, at any models of the derived categories. -/
theorem isZero_blowupFormsKernelHigherDirectImage_of_iso_of_homology {S X Z L P : Scheme.{u}}
    (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact (Stacks.Blowup.blowUpToBase i.ker)] (bL : L ⟶ X)
    (κ : L ⟶ Stacks.Blowup.blowUp i.ker) [IsIso κ] (hκ : κ ≫ blowupMap i = bL) (j₀ : P ⟶ L)
    (ε'' : P ⟶ Stacks.Blowup.exceptionalDivisor i.ker) [IsIso ε'']
    (hε : ε'' ≫ exceptionalInclusion i = j₀ ≫ κ) (a : ℕ) {K : L.Modules}
    (eK : K ≅ kernel (Scheme.Hom.formsDirectImageComparison j₀ (bL ≫ f) (a : ℤ)))
    (hL : HasDerivedCategory (ModuleSheaves L.toRingedSpace))
    (hX : HasDerivedCategory (ModuleSheaves X.toRingedSpace)) (q : ℤ)
    (h : IsZero ((@DerivedCategory.homologyFunctor _ _ _ hX q).obj
      ((@derivedPushforward _ _ bL.toLRSHom.toShHom hL hX).obj
        ((@DerivedCategory.singleFunctor (ModuleSheaves L.toRingedSpace) _ _ hL 0).obj K)))) :
    IsZero (blowupFormsKernelHigherDirectImage f i (a : ℤ) q) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing L.toRingedSpace)
  exact isZero_blowupFormsKernelHigherDirectImage_of_iso f i bL κ hκ j₀ ε'' hε a eK q
    ((isZero_homology_derivedPushforward_iff _ hL hX (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) q K).1 h)

/-! ### From the cone to the blowup of the coordinate centre -/

namespace CoordinateCone

variable (R : Type u) [CommRing R] (m n : ℕ)

open Stacks.AlgebraicGeometry.ProjAndSpec
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation (truncationConeData)

/-- `𝒦^a_L` is the kernel of the comparison map on direct images of forms along the zero section:
the restriction of forms is that map followed by an isomorphism. -/
def coneFormsKernelIso (a : ℤ) :
    coneFormsKernel R m n a ≅ kernel (Scheme.Hom.formsDirectImageComparison
      (zeroSection (truncationConeData (yGrading R m n))) (coneToBase R m n) a) :=
  kernelIsoOfEq (coneFormsRestriction.eq_1 R m n a) ≪≫ kernelCompMono _ _

/-- `epi_homology_zero_derivedPushforward_map_of_epi_pushforward`, with the injectives of
`𝒪_{X'}`-modules supplied by `SheafOfModules.isGrothendieckAbelianU`. -/
private theorem epi_homology_zero_derivedPushforward_map_of_epi_pushforward_grothendieck
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [HasDerivedCategory (ModuleSheaves X'.toRingedSpace)]
    [HasDerivedCategory (ModuleSheaves Y'.toRingedSpace)] {M N : X'.Modules} (g : M ⟶ N)
    (hg : Epi ((Scheme.Modules.pushforward f').map g)) :
    Epi ((DerivedCategory.homologyFunctor _ 0).map
      ((derivedPushforward f'.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctor (ModuleSheaves X'.toRingedSpace) 0).map g))) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X'.toRingedSpace)
  exact epi_homology_zero_derivedPushforward_map_of_epi_pushforward f' g hg

/-- The source `L` of the cone `b : L ⟶ X`, read off `b` itself. -/
abbrev coneSource : Scheme.{u} := (Arrow.mk (coneToAmbient R m n)).left

section Derived

variable
  [iX : HasDerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)]
  [iL : HasDerivedCategory (ModuleSheaves (coneSource R m n).toRingedSpace)]
  [iZ : HasDerivedCategory (ModuleSheaves (coneCentre R m n).toRingedSpace)]
  [iP : HasDerivedCategory (ModuleSheaves (coneBundle R m n).toRingedSpace)]

/-- `H⁰(Rb_*ρ)` is an epimorphism, `b_*ρ` being one (`epi_pushforward_coneFormsRestriction`). -/
theorem epi_homology_zero_derivedPushforward_coneFormsRestriction (a : ℕ) :
    Epi ((@DerivedCategory.homologyFunctor _ _ _ iX 0).map
      ((@derivedPushforward (coneSource R m n).toRingedSpace _
        (coneToAmbient R m n).toLRSHom.toShHom iL iX).map
        ((@DerivedCategory.singleFunctor (ModuleSheaves (coneSource R m n).toRingedSpace) _ _ iL
          0).map (coneFormsRestriction R m n (a : ℤ))))) := by
  have hg : Epi ((@Scheme.Modules.pushforward (coneSource R m n) _ (coneToAmbient R m n)).map
      (coneFormsRestriction R m n (a : ℤ))) := by
    have := isClosedImmersion_zeroSection (truncationConeData (yGrading R m n))
    have hN := AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward
      (X := coneSource R m n) (coneToAmbient R m n) _
      (AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward
        (zeroSection (truncationConeData (yGrading R m n))) _
        (Scheme.Hom.isQuasicoherent_relativeDifferentialForms
          (zeroSection (truncationConeData (yGrading R m n)) ≫ coneToBase R m n) a))
    have h₁ := Scheme.Hom.epi_pushforward_map_of_surjective_app_top (Y := coneSource R m n)
      (coneToAmbient R m n) _
      (Scheme.Hom.surjective_formsDirectImageComparison_app_top _ _ (zeroSection_comp_pi _) _
        (coneProjection_comp_coneZeroSection_comp_coneToBase R m n) (a : ℤ))
    rw [coneFormsRestriction, Functor.map_comp]
    infer_instance
  exact @epi_homology_zero_derivedPushforward_map_of_epi_pushforward_grothendieck (coneSource R m n)
    _ (coneToAmbient R m n) iL iX _ _ (coneFormsRestriction R m n (a : ℤ)) hg

/-- `H^q(Rb_*ρ)` is invertible as soon as the comparison of clause (3) of [Stacks, Tag 0FUR] is. -/
theorem isIso_homology_derivedPushforward_coneFormsRestriction (a k : ℕ)
    (h : IsIso ((@DerivedCategory.homologyFunctor _ _ _ iX (k : ℤ)).map
      (@coneFormsDerivedComparison R _ m n iX iL iZ iP (a : ℤ)))) :
    IsIso ((@DerivedCategory.homologyFunctor _ _ _ iX (k : ℤ)).map
      ((@derivedPushforward (coneSource R m n).toRingedSpace _
        (coneToAmbient R m n).toLRSHom.toShHom iL iX).map
        ((@DerivedCategory.singleFunctor (ModuleSheaves (coneSource R m n).toRingedSpace) _ _ iL
          0).map (coneFormsRestriction R m n (a : ℤ))))) := by
  rw [coneFormsDerivedComparison_eq] at h
  exact @isIso_homology_derivedPushforward_map_single_of_isIso_formsDerivedComparisonOf
    _ _ _ _ iX iL iZ iP _ _ _ _ _ _ _ _ _ _ h

/-- **Clause (3) of [Stacks, Tag 0FUR] gives `H^q(Rb_*𝒦^a_L) = 0` for `q ≥ 1`**: by the long exact
sequence of `0 ⟶ 𝒦^a_L ⟶ Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S} ⟶ 0`, `Rb_*ρ` being invertible on `H^q` for
`q ≥ 1` and onto on `H⁰`. -/
theorem isZero_homology_derivedPushforward_coneFormsKernel (a : ℕ)
    (h : ∀ k : ℕ, 1 ≤ k → IsIso ((@DerivedCategory.homologyFunctor _ _ _ iX (k : ℤ)).map
      (@coneFormsDerivedComparison R _ m n iX iL iZ iP (a : ℤ))))
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ iX q).obj
      ((@derivedPushforward (coneSource R m n).toRingedSpace _
        (coneToAmbient R m n).toLRSHom.toShHom iL iX).obj
        ((@DerivedCategory.singleFunctor (ModuleSheaves (coneSource R m n).toRingedSpace) _ _ iL
          0).obj (kernel (coneFormsRestriction R m n (a : ℤ)))))) := by
  have := epi_coneFormsRestriction R m n a
  refine @isZero_homology_derivedPushforward_kernel_of_isIso _ _ iX iL (coneToAmbient R m n) _ _
    (coneFormsRestriction R m n (a : ℤ)) _ (fun k hk => ?_)
    (epi_homology_zero_derivedPushforward_coneFormsRestriction R m n a) q hq
  obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = k' := ⟨k.toNat, by omega⟩
  exact isIso_homology_derivedPushforward_coneFormsRestriction R m n a k (h k (by omega))

/-- **Clause (3) of [Stacks, Tag 0FUR] gives the vanishing of `R^q b_*𝒦^a` for the blowup of the
coordinate centre**, for `q ≥ 1`. On the cone `H^q(Rb_*𝒦^a_L) = 0`
(`isZero_homology_derivedPushforward_coneFormsKernel`); the cone `L` is the blowup over `X`
(`coneStacksBlowupIso`) and its zero section is the exceptional divisor (`coneExceptionalIso`),
and flat base change along `𝟙_X` ([Stacks, Tag 02KH]) carries this to `R^q b_*𝒦^a = 0`. -/
theorem isZero_blowupFormsKernelHigherDirectImage_coordinateEmbedding (a : ℕ)
    (h : ∀ k : ℕ, 1 ≤ k → IsIso ((@DerivedCategory.homologyFunctor _ _ _ iX (k : ℤ)).map
      (@coneFormsDerivedComparison R _ m n iX iL iZ iP (a : ℤ))))
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero (blowupFormsKernelHigherDirectImage (Stacks.DeRham.coordinateAmbientToBase R m n)
      (Stacks.MoreMorphisms.coordinateEmbedding R m n) (a : ℤ) q) := by
  have := CoordinateCone.quasiCompact_blowUpToBase_coordinateEmbedding R m n
  exact isZero_blowupFormsKernelHigherDirectImage_of_iso_of_homology
    (Stacks.DeRham.coordinateAmbientToBase R m n) (Stacks.MoreMorphisms.coordinateEmbedding R m n)
    (coneToAmbient R m n) (coneStacksBlowupIso R m n).hom (coneStacksBlowupIso_hom_comp R m n)
    (coneZeroSection R m n) (coneExceptionalIso R m n).hom
    (coneExceptionalIso_hom_comp_ι R m n) a (coneFormsKernelIso R m n (a : ℤ)) iL iX q
    (isZero_homology_derivedPushforward_coneFormsKernel R m n a h q hq)

end Derived

end CoordinateCone

/-! ### The coordinate situation over an affine base -/

/-- **The vanishing of `R^q b_*𝒦^a` for the coordinate situation over an affine base** follows
from the vanishing for the coordinate situation of Section 50.16, along the identification
`isPullback_coordinateSubspaceEmbedding_coordinateEmbedding`. -/
theorem isZero_blowupFormsKernelHigherDirectImage_coordinateSubspaceEmbedding_of_isAffine
    (T : Scheme.{u}) [IsAffine T] (m n a : ℕ) (q : ℤ)
    (h : IsZero (blowupFormsKernelHigherDirectImage
      (Stacks.DeRham.coordinateAmbientToBase Γ(T, ⊤) m n)
      (Stacks.MoreMorphisms.coordinateEmbedding Γ(T, ⊤) m n) (a : ℤ) q)) :
    IsZero (blowupFormsKernelHigherDirectImage (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n) (a : ℤ) q) := by
  have := CoordinateCone.quasiCompact_blowUpToBase_coordinateEmbedding Γ(T, ⊤) m n
  exact isZero_blowupFormsKernelHigherDirectImage_of_isPullback
    (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom
    (isPullback_coordinateSubspaceEmbedding_coordinateEmbedding T m n) T.isoSpec.hom
    (affineSpaceIsoSpecRename_hom_comp T m n) a q h

/-! ### The global vanishing -/

section Global

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f]
  [Smooth (i ≫ f)]

/-- **`R^q b_*𝒦^a = 0` for `q ≥ 1`, for every closed immersion of schemes smooth over `S`**, from
its vanishing on the cone of the coordinate situation of Section 50.16 for `n ≥ 1`. Over each
affine open `V` of `S` it is the covering argument
`isZero_blowupFormsKernelHigherDirectImage_of_coordinate`, the coordinate situation of
codimension `0` having an empty blowup. -/
theorem isZero_blowupFormsKernelHigherDirectImage_of_smooth_of_cone
    (hcone : ∀ (R : Type u) [CommRing R] (m n : ℕ), 1 ≤ n → ∀ (a k : ℕ), 1 ≤ k →
      IsIso ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard
          (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)) (k : ℤ)).map
        (@CoordinateCone.coneFormsDerivedComparison R _ m n
          (HasDerivedCategory.standard
            (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace))
          (HasDerivedCategory.standard
            (ModuleSheaves (CoordinateCone.coneSource R m n).toRingedSpace))
          (HasDerivedCategory.standard
            (ModuleSheaves (CoordinateCone.coneCentre R m n).toRingedSpace))
          (HasDerivedCategory.standard
            (ModuleSheaves (CoordinateCone.coneBundle R m n).toRingedSpace)) (a : ℤ))))
    (a : ℕ) (q : ℤ) (hq : 1 ≤ q) :
    IsZero (blowupFormsKernelHigherDirectImage f i (a : ℤ) q) := by
  have := quasiCompact_blowUpToBase_of_smooth f i
  have hcov : ∀ V : S.affineOpens, IsZero ((Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj
      (blowupFormsKernelHigherDirectImage f i (a : ℤ) q)) := by
    intro V
    have : IsAffine V.1.toScheme := V.2
    have : Smooth (restrictCentre i (f ⁻¹ᵁ V.1) ≫ f ∣_ V.1) := by
      rw [restrictCentre_comp_morphismRestrict]
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict (i ≫ f) V.1).flip inferInstance
    have h := isZero_blowupFormsKernelHigherDirectImage_of_coordinate (f ∣_ V.1)
      (restrictCentre i (f ⁻¹ᵁ V.1)) a q (by omega) fun m n => by
        rcases n with _ | n
        · exact isZero_blowupFormsKernelHigherDirectImage_coordinate_zero V.1.toScheme m (a : ℤ)
            q (by omega)
        · exact isZero_blowupFormsKernelHigherDirectImage_coordinateSubspaceEmbedding_of_isAffine
            V.1.toScheme m (n + 1) a q
            (@CoordinateCone.isZero_blowupFormsKernelHigherDirectImage_coordinateEmbedding
              Γ(V.1.toScheme, ⊤) _ m (n + 1) (HasDerivedCategory.standard _)
              (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
              (HasDerivedCategory.standard _) a (hcone _ m (n + 1) (by omega) a) q hq)
    exact isZero_pullback_blowupFormsKernelHigherDirectImage_of_isPullback (f ∣_ V.1)
      (isPullback_restrictCentre i (f ⁻¹ᵁ V.1)) V.1.ι (morphismRestrict_ι f V.1).symm a q h
  refine isZero_of_isZero_pullback_ι (fun V : S.affineOpens => f ⁻¹ᵁ V.1) ?_ hcov
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

section Derived

variable [HasDerivedCategory (ModuleSheaves X.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves Z.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.exceptionalDivisor i.ker).toRingedSpace)]

/-- **Clause (3) of [Stacks, Tag 0FUU] from clause (3) of [Stacks, Tag 0FUR] on the cone**: for
every closed immersion of schemes smooth over `S`, of any codimension, the canonical map
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on cohomology sheaves in every degree
`q ≥ 1`, at any models of the derived categories, as soon as the comparison on the cone of the
coordinate situation of Section 50.16 is. -/
theorem isIso_homology_blowupFormsRestrictionDerivedComparison_of_smooth_of_cone
    (hcone : ∀ (R : Type u) [CommRing R] (m n : ℕ), 1 ≤ n → ∀ (a k : ℕ), 1 ≤ k →
      IsIso ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard
          (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)) (k : ℤ)).map
        (@CoordinateCone.coneFormsDerivedComparison R _ m n
          (HasDerivedCategory.standard
            (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace))
          (HasDerivedCategory.standard
            (ModuleSheaves (CoordinateCone.coneSource R m n).toRingedSpace))
          (HasDerivedCategory.standard
            (ModuleSheaves (CoordinateCone.coneCentre R m n).toRingedSpace))
          (HasDerivedCategory.standard
            (ModuleSheaves (CoordinateCone.coneBundle R m n).toRingedSpace)) (a : ℤ))))
    (a : ℕ) (q : ℤ) (hq : 0 < q) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (blowupFormsRestrictionDerivedComparison f i (a : ℤ))) :=
  isIso_homology_blowupFormsRestrictionDerivedComparison_of_isZero f i a
    (fun k hk => (isZero_homology_derivedPushforward_blowupFormsKernel_iff f i (a : ℤ) k).2
      (isZero_blowupFormsKernelHigherDirectImage_of_smooth_of_cone f i hcone a k hk)) q hq

/-- **[Stacks, Tag 0FUU], clause (3).** Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed
immersion with `Z` smooth over `S`. Let `b : X' ⟶ X` be the blowing up of `X` along `Z`, with
exceptional divisor `E` and projection `p : E ⟶ Z`. Then for every `a ≥ 0` the canonical map
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on cohomology sheaves in every degree
`q ≥ 1`, at any models of the derived categories.

No hypothesis on the codimension is needed: where `Z` contains an open of `X`, the blowup and the
exceptional divisor are empty there. The proof reduces, étale locally by [Stacks, Tag 0FUE], to
the coordinate situation of Section 50.16, where it is clause (3) of [Stacks, Tag 0FUR]. -/
@[stacks 0FUU "clause (3): Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S} is an isomorphism on cohomology \
sheaves in every degree q ≥ 1, every a ≥ 0, for a closed immersion of schemes smooth over S of any \
codimension"]
theorem isIso_homology_blowupFormsRestrictionDerivedComparison_of_smooth (a : ℕ) (q : ℤ)
    (hq : 0 < q) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (blowupFormsRestrictionDerivedComparison f i (a : ℤ))) :=
  isIso_homology_blowupFormsRestrictionDerivedComparison_of_smooth_of_cone f i
    (fun R _ m n hn a k hk => @CoordinateCone.isIso_homology_coneFormsDerivedComparison R _ m n
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) hn a k hk) a q hq

end Derived

end Global

end Stacks.DeRham

end
