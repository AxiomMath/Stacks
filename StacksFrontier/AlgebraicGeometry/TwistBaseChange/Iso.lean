module

public import StacksFrontier.AlgebraicGeometry.TwistBaseChange.Sections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison maps on the twists are isomorphisms for a graded localization

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings exhibiting `B` as a
localization of `A` away from an element `g` of degree `0`. This file proves that the comparison
map

`θ n : mapHom* 𝒪_{Proj 𝒜}(n) ⟶ ι* 𝒪_{Proj ℬ}(n)`

is an isomorphism for every `n : ℤ`, and deduces the same for the restriction map of a
quasi-coherent graded algebra along a basic open inclusion of affine opens of the base.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistBaseChange.adjointTwistMap`: the adjoint comparison map, typed
  as a morphism of `𝒪`-modules on the scheme `Proj 𝒜`.
* `Stacks.AlgebraicGeometry.TwistBaseChange.restrictTwistMap`: the comparison transported from
  the pullback to the restriction along the open immersion `mapHom`.

## Main results

* `Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap`: the comparison map on the `n`-th
  twist is an isomorphism, and `isIso_projMapData_twistMap` the same for
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_res` and
  `isIso_projMapData_twistMap_res`: the same for the restriction map of a
  `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` along a basic open inclusion `D(f) ⊆ U`
  of affine opens.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_of_inputs`: the comparison map is an
  isomorphism as soon as `mapHom` is an open immersion, the fibre comparison is injective at every
  point of `U(ψ)`, and homogeneous fractions lift pointwise
  (`Stacks.AlgebraicGeometry.TwistBaseChange.FractionLift`).
* `Stacks.AlgebraicGeometry.TwistBaseChange.mono_restrictTwistMap`, `epi_restrictTwistMap` and
  `isIso_restrictTwistMap`: under these inputs the restricted comparison map is a monomorphism,
  an epimorphism and an isomorphism.
* `Stacks.AlgebraicGeometry.TwistBaseChange.leftAdjointUniq_hom_app_homEquiv_symm`: the canonical
  isomorphism of two left adjoints of one right adjoint carries the inverse transpose taken in one
  adjunction to the inverse transpose taken in the other.

## Implementation notes

A morphism out of `mapHom* 𝒪_{Proj 𝒜}(n)` has no usable description on sections, so the pullback
is replaced by the restriction along the open immersion `mapHom`, whose sections over an open `V`
of `U(ψ)` are the sections of `𝒪_{Proj 𝒜}(n)` over the image `mapHom ''ᵁ V`. Both functors are
left adjoint to the pushforward, and by `leftAdjointUniq_hom_app_homEquiv_symm` invertibility of
`θ` is equivalent to invertibility of `restrictTwistMap`. That is shown by monomorphy and
epimorphy, the category of sheaves of modules on a scheme being balanced: monomorphy is
injectivity on sections, and epimorphy is local surjectivity.

`AlgebraicGeometry.Scheme.Modules` is a `def`, and a twisting sheaf is an object of it only
through the further `def`s `TopCat.Sheaf`, `sheafCompose` and `AlgebraicGeometry.Proj`, which are
made `implicit_reducible` locally. `adjointTwistMap` carries the `def`-valued type so that
`AlgebraicGeometry.Scheme.Modules.Hom.app` applies to it, and some equations are applied through
`Eq.trans` rather than `rw`, since the goals are not type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 01N3](https://stacks.math.columbia.edu/tag/01N3)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistEpi
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.TwistBaseChange

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

/-! ### Two left adjoints of one right adjoint -/

/-- For two adjunctions with the same right adjoint, the canonical isomorphism of the two left
adjoints carries the inverse transpose taken in one adjunction to the inverse transpose taken in
the other. -/
public theorem leftAdjointUniq_hom_app_homEquiv_symm {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R) {X : C} {Y : D}
    (φ : X ⟶ R.obj Y) :
    (Adjunction.leftAdjointUniq adj adj').hom.app X ≫ (adj'.homEquiv X Y).symm φ =
      (adj.homEquiv X Y).symm φ := by
  have h1 : adj.homEquiv X Y ((Adjunction.leftAdjointUniq adj adj').hom.app X ≫
      (adj'.homEquiv X Y).symm φ) = φ := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
      Equiv.apply_symm_apply]
  exact (adj.homEquiv X Y).injective (h1.trans (Equiv.apply_symm_apply _ _).symm)

/-- If the inverse transpose of `φ` in one adjunction is an isomorphism, so is its inverse
transpose in any other adjunction with the same right adjoint. -/
private theorem isIso_homEquiv_symm_of_isIso {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R) {X : C} {Y : D}
    (φ : X ⟶ R.obj Y) (h : IsIso ((adj.homEquiv X Y).symm φ)) :
    IsIso ((adj'.homEquiv X Y).symm φ) := by
  have : IsIso ((Adjunction.leftAdjointUniq adj adj').hom.app X ≫ (adj'.homEquiv X Y).symm φ) :=
    (leftAdjointUniq_hom_app_homEquiv_symm adj adj' φ).symm ▸ h
  exact IsIso.of_isIso_comp_left ((Adjunction.leftAdjointUniq adj adj').hom.app X) _

section

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) [IsOpenImmersion (mapHom 𝒜 ℬ ψ)]

/-- The adjoint comparison map `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`,
typed as a morphism of `𝒪`-modules on the scheme `Proj 𝒜`. -/
@[ega "II 8.12.4" "special case"]
public abbrev adjointTwistMap (n : ℤ) :
    Scheme.Modules.Hom (X := AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 n)
      ((Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
        ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))) :=
  twistPushforwardMap 𝒜 ℬ ψ n

/-- The comparison map on the `n`-th twist, transported from the pullback to the restriction
along the open immersion `mapHom`. -/
public def restrictTwistMap (n : ℤ) :
    (Scheme.Modules.restrictFunctor (mapHom 𝒜 ℬ ψ)).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n) :=
  ((Scheme.Modules.restrictAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _).symm
    (adjointTwistMap 𝒜 ℬ ψ n)

/-- The comparison on sections of the restricted comparison map: over an open `V` of `U(ψ)` it is
the comparison on sections over the image of `V`, followed by the restriction along the equality
of opens `mapHom ⁻¹ᵁ (mapHom ''ᵁ V) = V`. -/
public theorem restrictTwistMap_app (n : ℤ) (V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens) :
    (restrictTwistMap 𝒜 ℬ ψ n).app V =
      (adjointTwistMap 𝒜 ℬ ψ n).app (mapHom 𝒜 ℬ ψ ''ᵁ V) ≫
        ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj
          (twistingSheaf ℬ n)).presheaf.map
            (eqToHom ((mapHom 𝒜 ℬ ψ).preimage_image_eq V).symm).op := by
  have h : restrictTwistMap 𝒜 ℬ ψ n =
      (Scheme.Modules.restrictFunctor (mapHom 𝒜 ℬ ψ)).map (adjointTwistMap 𝒜 ℬ ψ n) ≫
        (Scheme.Modules.restrictAdjunction (mapHom 𝒜 ℬ ψ)).counit.app
          ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) :=
    Adjunction.homEquiv_counit _ _ _ _
  rw [h, Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictAdjunction_counit_app_app]
  rfl

/-- The pointwise formula for the restricted comparison map on sections. -/
public theorem restrictTwistMap_app_val (n : ℤ) (V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (.op (mapHom 𝒜 ℬ ψ ''ᵁ V)))
    (w : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V)) :
    (((restrictTwistMap 𝒜 ℬ ψ n).app V) s).1 w =
      twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ w)
        (s.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ w),
          ⟨liftPt 𝒜 ℬ ψ w, liftPt_mem 𝒜 ℬ ψ w, rfl⟩⟩) := by
  rw [restrictTwistMap_app]
  rfl

/-- The reindexing of points over the image of an open of `U(ψ)` is surjective: every point of
`mapHom ''ᵁ V` comes from a point of `V`. -/
public theorem surjective_imageIndex (V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens) :
    Function.Surjective (fun w : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V) =>
      (⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ w),
        ⟨liftPt 𝒜 ℬ ψ w, liftPt_mem 𝒜 ℬ ψ w, rfl⟩⟩ : ↥(mapHom 𝒜 ℬ ψ ''ᵁ V))) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hyV, hyx⟩ := hx
  refine ⟨⟨(y.1 : AlgebraicGeometry.Proj ℬ), mem_image_of_mem 𝒜 ℬ ψ y hyV⟩, Subtype.ext ?_⟩
  have hlift : liftPt 𝒜 ℬ ψ
      (⟨(y.1 : AlgebraicGeometry.Proj ℬ), mem_image_of_mem 𝒜 ℬ ψ y hyV⟩ :
        ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V)) = y := Subtype.ext rfl
  change basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ _) = x
  rwa [hlift]

end

section Gate

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) [IsOpenImmersion (mapHom 𝒜 ℬ ψ)]

/-! ### Injectivity, hence monomorphy -/

/-- The restricted comparison map is injective on sections over every open of `U(ψ)`. -/
public theorem injective_restrictTwistMap_app
    (hfib : ∀ y : (mapDomain 𝒜 ℬ ψ).toScheme, Function.Injective (twistFibreMap 𝒜 ℬ ψ y))
    (n : ℤ) (V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens) :
    Function.Injective fun s => (restrictTwistMap 𝒜 ℬ ψ n).app V s := by
  intro x y hxy
  refine Subtype.ext (funext ?_)
  refine (surjective_imageIndex 𝒜 ℬ ψ V).forall.mpr fun w => ?_
  refine hfib (liftPt 𝒜 ℬ ψ w) ?_
  refine Eq.trans (restrictTwistMap_app_val 𝒜 ℬ ψ n V x w).symm ?_
  exact Eq.trans (congrFun (congrArg Subtype.val hxy) w)
    (restrictTwistMap_app_val 𝒜 ℬ ψ n V y w)

/-- If the fibre comparison is injective at every point of `U(ψ)`, the restricted comparison map
is a monomorphism. -/
public theorem mono_restrictTwistMap
    (hfib : ∀ y : (mapDomain 𝒜 ℬ ψ).toScheme, Function.Injective (twistFibreMap 𝒜 ℬ ψ y))
    (n : ℤ) : Mono (restrictTwistMap 𝒜 ℬ ψ n) := by
  have happ : ∀ U, Mono (((Scheme.Modules.toPresheaf (mapDomain 𝒜 ℬ ψ).toScheme).map
      (restrictTwistMap 𝒜 ℬ ψ n)).app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (injective_restrictTwistMap_app 𝒜 ℬ ψ hfib n U.unop)
  exact (Scheme.Modules.toPresheaf _).mono_of_mono_map (NatTrans.mono_of_mono_app _)

/-! ### Local surjectivity, hence epimorphy -/

/-- If homogeneous fractions lift pointwise, the restricted comparison map is an
epimorphism. -/
public theorem epi_restrictTwistMap (hlift : FractionLift 𝒜 ℬ ψ) (n : ℤ) :
    Epi (restrictTwistMap 𝒜 ℬ ψ n) := by
  have hind : Topology.IsInducing (mapHom 𝒜 ℬ ψ).base :=
    (mapHom 𝒜 ℬ ψ).isOpenEmbedding.isInducing
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
    (restrictTwistMap 𝒜 ℬ ψ n) ?_
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr ?_
  intro V t y hy
  obtain ⟨U, hU⟩ := exists_preimage_opens_of_isInducing (mapHom 𝒜 ℬ ψ) hind V
  subst hU
  obtain ⟨V₁, hV₁U, hyV₁, s, hs⟩ := exists_fractionSection_eq 𝒜 ℬ ψ hlift hind n U
    (show (twistingSheaf ℬ n).val.obj
      (.op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) from t) y hy
  have himg : mapHom 𝒜 ℬ ψ ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V₁) ≤ V₁ :=
    (mapHom 𝒜 ℬ ψ).image_preimage_le V₁
  refine ⟨mapHom 𝒜 ℬ ψ ⁻¹ᵁ V₁, fun p hp => hV₁U hp,
    ⟨(twistingSheaf 𝒜 n).val.presheaf.map (homOfLE himg).op s, ?_⟩, hyV₁⟩
  refine Subtype.ext (funext fun w => ?_)
  exact Eq.trans (restrictTwistMap_app_val 𝒜 ℬ ψ n (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V₁) _ w) (hs w _)

/-! ### The isomorphism -/

/-- If the fibre comparison is injective at every point of `U(ψ)` and homogeneous fractions lift
pointwise, the restricted comparison map is an isomorphism. -/
public theorem isIso_restrictTwistMap
    (hfib : ∀ y : (mapDomain 𝒜 ℬ ψ).toScheme, Function.Injective (twistFibreMap 𝒜 ℬ ψ y))
    (hlift : FractionLift 𝒜 ℬ ψ) (n : ℤ) :
    IsIso (restrictTwistMap 𝒜 ℬ ψ n) :=
  have := mono_restrictTwistMap 𝒜 ℬ ψ hfib n
  have := epi_restrictTwistMap 𝒜 ℬ ψ hlift n
  isIso_of_mono_of_epi _

/-- If the induced morphism is an open immersion, the fibre comparison is injective at every
point of `U(ψ)`, and homogeneous fractions lift pointwise, then the comparison map `θ n` on the
`n`-th twisting sheaf is an isomorphism, for every `n : ℤ`. -/
public theorem isIso_twistMap_of_inputs
    (hfib : ∀ y : (mapDomain 𝒜 ℬ ψ).toScheme, Function.Injective (twistFibreMap 𝒜 ℬ ψ y))
    (hlift : FractionLift 𝒜 ℬ ψ) (n : ℤ) :
    IsIso (twistMap 𝒜 ℬ ψ n) := by
  have h4 := isIso_homEquiv_symm_of_isIso
    (Scheme.Modules.restrictAdjunction (mapHom 𝒜 ℬ ψ))
    (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)) (adjointTwistMap 𝒜 ℬ ψ n)
    (isIso_restrictTwistMap 𝒜 ℬ ψ hfib hlift n)
  have h5 : IsIso ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ n)) := NatIso.isIso_app_of_isIso _ _
  rw [twistMap]
  infer_instance

end Gate

section Final

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- For a homomorphism of nonnegatively graded rings exhibiting
`B` as a localization of `A` away from an element of degree `0`, the comparison map `θ n` on the
`n`-th twisting sheaf is an isomorphism, for every `n : ℤ`. -/
public theorem isIso_twistMap (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] (n : ℤ) :
    IsIso (twistMap 𝒜 ℬ ψ n) :=
  have : IsOpenImmersion (mapHom 𝒜 ℬ ψ) := isOpenImmersion_mapHom 𝒜 ℬ ψ hg halg
  isIso_twistMap_of_inputs 𝒜 ℬ ψ (fun y => (bijective_twistFibreMap 𝒜 ℬ ψ g halg y).1)
    (fractionLift_of_isLocalizationAway 𝒜 ℬ ψ hg halg) n

/-- If `ψ` presents `B` as the localization `A_g` of `A` at a degree-zero element `g`, then the
comparison map `θ : r_ψ^* 𝒪_X(n) → 𝒪_Y(n)` of
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` is an isomorphism for every `n : ℤ`. -/
@[stacks 01N3 "the maps on twists"]
public theorem isIso_projMapData_twistMap (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] (n : ℤ) :
    IsIso ((projMapData 𝒜 ℬ ψ).twistMap n) := by
  rw [projMapData_twistMap]
  exact isIso_twistMap 𝒜 ℬ ψ hg halg n

end Final

section Relative

variable {S : Scheme.{u}} (𝒜 : RelativeProj.GradedAlgebra S)

/-- For a basic open inclusion `D(f) ⊆ U` of affine opens of the base, the comparison maps on all
the twisting sheaves of the restriction map of a quasi-coherent graded algebra are
isomorphisms. -/
public theorem isIso_twistMap_res (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) (n : ℤ) :
    IsIso (twistMap (𝒜.grading U) (𝒜.grading (U.basicOpen f))
      (𝒜.res (S.basicOpen_le f)) n) := by
  let := 𝒜.algebra (U := U.basicOpen f) (V := U) (S.basicOpen_le f)
  have := 𝒜.isLocalization U f
  exact isIso_twistMap _ _ _ (𝒜.str_mem U f)
    (𝒜.algebraMap_eq (U := U.basicOpen f) (V := U) (S.basicOpen_le f)) n

/-- For a basic open inclusion `D(f) ⊆ U` of affine opens of the base, the comparison map on the
`n`-th twist of `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` of the restriction map of
a quasi-coherent graded algebra is an isomorphism. -/
public theorem isIso_projMapData_twistMap_res (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens))
    (n : ℤ) :
    IsIso ((projMapData (𝒜.grading U) (𝒜.grading (U.basicOpen f))
      (𝒜.res (S.basicOpen_le f))).twistMap n) := by
  rw [projMapData_twistMap]
  exact isIso_twistMap_res 𝒜 U f n

end Relative

end Stacks.AlgebraicGeometry.TwistBaseChange

end
