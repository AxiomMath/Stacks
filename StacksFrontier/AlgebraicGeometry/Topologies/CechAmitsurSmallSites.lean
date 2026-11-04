module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Topologies.CechAmitsurQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# Čech complexes of quasi-coherent presheaves on the small étale and Zariski sites

Let `S` be a scheme, `F` a quasi-coherent `𝒪_S`-module and `Fᵃ` the associated presheaf. For a
standard étale covering `𝒰 = {U_i → U}` in the small étale site `S_étale`, and for a standard
Zariski covering `𝒰 = {U_i → U}` of an affine open `U` in the small Zariski site `S_Zar`, the
Čech complex `Č^•(𝒰, Fᵃ)` is isomorphic to the complex `s((A/R)_• ⊗_R M)`, where
`R = Γ(U, 𝒪)`, `A = Γ(∐ U_i, 𝒪)` and `M = Fᵃ(U)`; in particular `Ȟ^p(𝒰, Fᵃ) = 0` for `p ≥ 1`.
In the Zariski case the ring `A` is computed in `Over S`.

## Main results

* `AlgebraicGeometry.isIso_cechProductMapOfFunctor_etaleForget` and
  `AlgebraicGeometry.isIso_cechProductMapOfFunctor_restrictFunctor`: each inclusion preserves
  the iterated fibre products of an arbitrary family.
* `AlgebraicGeometry.restrictFunctor_preservesLimitsOfShape_walkingCospan`: the inclusion of the
  small Zariski site preserves fibre products, the fibre product of two opens being their
  intersection on both sides.
* `AlgebraicGeometry.IsSmallEtaleStandardCovering.isStandardCovering_map`: a
  small-étale-standard covering has standard-étale image family.
* `AlgebraicGeometry.cechComplexIsoImageSmallEtale` and
  `AlgebraicGeometry.cechComplexIsoImageSmallZariski`: the Čech complex in the small site is
  the Čech complex of the image family in `Over S`.
* `AlgebraicGeometry.cechComplexIsoAmitsurSmallEtale` and
  `AlgebraicGeometry.cechComplexIsoAmitsurSmallZariski`: the isomorphism of complexes
  `Č^•(𝒰, Fᵃ) ≅ s((A/R)_• ⊗_R M)`.
* `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale` and
  `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf_smallZariski`: the
  vanishing of `Ȟ^p(𝒰, Fᵃ)` for `p ≥ 1`.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 023F](https://stacks.math.columbia.edu/tag/023F)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology Stacks.CechSite Stacks.Descent
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-! ### The forgetful functor preserves the fibre products of a family -/

/-- The forgetful functor of the small étale site preserves the iterated fibre products of an
arbitrary family. -/
public theorem isIso_cechProductMapOfFunctor_etaleForget {T : S.Etale}
    (𝒱 : PreZeroHypercover.{u} T) (n : ℕ) (i : Fin (n + 1) → 𝒱.I₀) :
    IsIso (cechProductMapOfFunctor (Scheme.Etale.forget S) 𝒱 n i) :=
  let : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (𝒱.f (i a))))
      (Over.post (X := T) (Scheme.Etale.forget S)) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost (Scheme.Etale.forget S) 𝒱
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  isIso_cechProductMapOfFunctor (Scheme.Etale.forget S) 𝒱 n i

/-- The image in `Over S` of a small-étale-standard covering is a standard étale covering. -/
public theorem IsSmallEtaleStandardCovering.isStandardCovering_map {T : S.Etale}
    (𝒱 : PreZeroHypercover.{u} T) (h : IsSmallEtaleStandardCovering S 𝒱) :
    letI : IsAffine ((Scheme.Etale.forget S).obj T).left :=
      (IsSmallEtaleStandardCovering.isAffine S h).1
    IsStandardCovering .etale
      (fun i ↦ ((𝒱.map (Scheme.Etale.forget S)).X i).left)
      (fun i ↦ ((𝒱.map (Scheme.Etale.forget S)).f i).left) :=
  h.2

/-! ### The Čech complex of the small étale site is the Čech complex of the image family -/

/-- The Čech complex of a family in the small étale site, with coefficients the restriction of
`Fᵃ` along the forgetful functor, is the Čech complex of its image family in `Over S` with
coefficients `Fᵃ`. -/
public def cechComplexIsoImageSmallEtale (F : S.Modules) [F.IsQuasicoherent] {T : S.Etale}
    (𝒱 : PreZeroHypercover.{u} T) :
    cechComplex 𝒱 ((Scheme.Etale.forget S).op ⋙ quasiCoherentPresheafFunctor S F) ≅
      cechComplex (𝒱.map (Scheme.Etale.forget S)) (quasiCoherentPresheafFunctor S F) :=
  (cechComplexIsoOfFunctor (Scheme.Etale.forget S) 𝒱 (quasiCoherentPresheafFunctor S F)
    (fun n i ↦ isIso_cechProductMapOfFunctor_etaleForget S 𝒱 n i)).symm

/-! ### The Čech complex of `Fᵃ` on the small étale site -/

/-- For a small-étale-standard covering `𝒰 = {U_i → U}` of an object of `S_étale`, the Čech
complex of the presheaf `Fᵃ` is the complex `s((A/R)_• ⊗_R M)`, where `R = Γ(U, 𝒪)`,
`A = Γ(∐ U_i, 𝒪)` and `M = Fᵃ(U)`. -/
@[stacks 03FJ "the isomorphism of complexes, case (b), the small étale site"]
public def cechComplexIsoAmitsurSmallEtale (F : S.Modules) [F.IsQuasicoherent] {T : S.Etale}
    (𝒱 : PreZeroHypercover.{u} T) (h : IsSmallEtaleStandardCovering S 𝒱) :
    letI : IsAffine ((Scheme.Etale.forget S).obj T).left :=
      (IsSmallEtaleStandardCovering.isAffine S h).1
    letI : Finite (𝒱.map (Scheme.Etale.forget S)).I₀ :=
      IsSmallEtaleStandardCovering.finite S h
    letI := overAffineSliceAlgebra ((Scheme.Etale.forget S).obj T)
      (Sigma.desc (𝒱.map (Scheme.Etale.forget S)).f)
    cechComplex 𝒱 ((Scheme.Etale.forget S).op ⋙ quasiCoherentPresheafFunctor S F) ≅
      ((forget₂ (ModuleCat.{u} (Γ(((Scheme.Etale.forget S).obj T).left, ⊤) : Type u))
            AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (amitsurCochainComplex (Γ(((Scheme.Etale.forget S).obj T).left, ⊤) : Type u)
          (Γ((∐ (𝒱.map (Scheme.Etale.forget S)).X).left, ⊤) : Type u)
          (Stacks.Sites.coeffModule S F (𝟭 (Over S)) ((Scheme.Etale.forget S).obj T))) :=
  letI : IsAffine ((Scheme.Etale.forget S).obj T).left :=
    (IsSmallEtaleStandardCovering.isAffine S h).1
  cechComplexIsoImageSmallEtale S F 𝒱 ≪≫
    cechComplexIsoAmitsurStandardCovering ((Scheme.Etale.forget S).obj T) .etale F
      (𝒱.map (Scheme.Etale.forget S))
      (IsSmallEtaleStandardCovering.isStandardCovering_map S 𝒱 h)

/-- The Čech cohomology of `Fᵃ` on a small-étale-standard covering vanishes in every positive
degree. -/
@[stacks 03FJ "the `Cech^p = 0 for p >= 1` clause, case (b), the small étale site"]
public theorem isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale (F : S.Modules)
    [F.IsQuasicoherent] {T : S.Etale} (𝒱 : PreZeroHypercover.{u} T)
    (h : IsSmallEtaleStandardCovering S 𝒱) (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱
      ((Scheme.Etale.forget S).op ⋙ quasiCoherentPresheafFunctor S F) p) :=
  let : IsAffine ((Scheme.Etale.forget S).obj T).left :=
    (IsSmallEtaleStandardCovering.isAffine S h).1
  cechCohomology_isZero_of_isZero_of_functor (Scheme.Etale.forget S) 𝒱
    (quasiCoherentPresheafFunctor S F) (isIso_cechProductMapOfFunctor_etaleForget S 𝒱 · ·) p
    (isZero_cechCohomology_succ_quasiCoherentPresheaf ((Scheme.Etale.forget S).obj T) .etale F
      (𝒱.map (Scheme.Etale.forget S))
      (IsSmallEtaleStandardCovering.isStandardCovering_map S 𝒱 h) p hp)

/-! ### The inclusion of the small Zariski site preserves the fibre products of a family

The small Zariski site of `S` is `S.Opens`, and its inclusion into the schemes over `S` is
`AlgebraicGeometry.Scheme.restrictFunctor`. It preserves fibre products: the fibre product of two
opens over a third is their intersection. -/

variable {S}

/-- There is at most one morphism of `Over S` from an object to an open of `S`. -/
public instance subsingleton_hom_restrictFunctor (Z : Over S) (V : S.Opens) :
    Subsingleton (Z ⟶ S.restrictFunctor.obj V) where
  allEq g h := Over.OverMorphism.ext
    ((cancel_mono V.ι).1 ((Over.w g).trans (Over.w h).symm))

/-- An open of `S` receiving a morphism of `Over S` from `Z` contains the image of the structure
morphism of `Z`. -/
public theorem range_subset_of_hom_restrictFunctor {Z : Over S} {V : S.Opens}
    (g : Z ⟶ S.restrictFunctor.obj V) : Set.range Z.hom.base ⊆ (V : Set S) := by
  rw [← Over.w g, ← Scheme.Opens.range_ι V]
  rintro _ ⟨y, rfl⟩
  exact ⟨g.left.base y, (Scheme.Hom.comp_apply g.left V.ι y).symm⟩

/-- The morphism of `Over S` from `Z` to an open of `S` containing the image of the structure
morphism of `Z`, obtained by lifting that structure morphism through the open immersion. -/
public def homToRestrictFunctor (Z : Over S) (V : S.Opens)
    (hV : Set.range Z.hom.base ⊆ (V : Set S)) : Z ⟶ S.restrictFunctor.obj V :=
  have hrange : Set.range Z.hom.base ⊆ Set.range V.ι.base := by rwa [Scheme.Opens.range_ι]
  Over.homMk (show Z.left ⟶ V.toScheme from IsOpenImmersion.lift V.ι Z.hom hrange)
    (IsOpenImmersion.lift_fac V.ι Z.hom hrange)

/-- The intersection of two opens of `S` is their fibre product among the schemes over `S`. -/
public def isLimitMapRestrictFunctorInfPullbackCone {U V W : S.Opens} (f : U ⟶ W) (g : V ⟶ W) :
    IsLimit (S.restrictFunctor.mapCone (opensInfPullbackCone f g)) := by
  refine (PullbackCone.isLimitMapConeEquiv (opensInfPullbackCone f g) S.restrictFunctor).2 ?_
  refine PullbackCone.IsLimit.mk _ (fun s => homToRestrictFunctor s.pt (U ⊓ V) ?_)
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)
  simpa only [TopologicalSpace.Opens.coe_inf] using Set.subset_inter
    (range_subset_of_hom_restrictFunctor s.fst) (range_subset_of_hom_restrictFunctor s.snd)

/-- The inclusion of the small Zariski site into the schemes over `S` preserves fibre products. -/
public instance restrictFunctor_preservesLimitsOfShape_walkingCospan :
    PreservesLimitsOfShape WalkingCospan S.restrictFunctor where
  preservesLimit {K} := by
    have : PreservesLimit
        (cospan (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr))
        S.restrictFunctor :=
      preservesLimit_of_preserves_limit_cone (isLimitOpensInfPullbackCone _ _)
        (isLimitMapRestrictFunctorInfPullbackCone _ _)
    exact preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

/-- A cospan of opens of `S` has a pullback, namely their intersection. -/
public instance hasPullback_opens {U V W : S.Opens} (f : U ⟶ W) (g : V ⟶ W) :
    HasPullback f g :=
  ⟨⟨⟨_, isLimitOpensInfPullbackCone f g⟩⟩⟩

/-- The inclusion of the small Zariski site preserves the iterated fibre products of an
arbitrary family. -/
public theorem isIso_cechProductMapOfFunctor_restrictFunctor {T : S.Opens}
    (𝒱 : PreZeroHypercover.{u} T)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒱.I₀), HasProduct (fun a ↦ Over.mk (𝒱.f (i a)))]
    (n : ℕ) (i : Fin (n + 1) → 𝒱.I₀) :
    IsIso (cechProductMapOfFunctor S.restrictFunctor 𝒱 n i) :=
  let : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (𝒱.f (i a))))
      (Over.post (X := T) S.restrictFunctor) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost S.restrictFunctor 𝒱
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  isIso_cechProductMapOfFunctor S.restrictFunctor 𝒱 n i

/-! ### The Čech complex of `Fᵃ` on the small Zariski site -/

/-- The Čech complex of a family of opens of `S`, with coefficients the restriction of `Fᵃ`, is
the Čech complex of its image family in `Over S` with coefficients `Fᵃ`. -/
public def cechComplexIsoImageSmallZariski (F : S.Modules) [F.IsQuasicoherent] {T : S.Opens}
    (𝒱 : PreZeroHypercover.{u} T)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒱.I₀), HasProduct (fun a ↦ Over.mk (𝒱.f (i a)))] :
    cechComplex 𝒱 (S.restrictFunctor.op ⋙ quasiCoherentPresheafFunctor S F) ≅
      cechComplex (𝒱.map S.restrictFunctor) (quasiCoherentPresheafFunctor S F) :=
  (cechComplexIsoOfFunctor S.restrictFunctor 𝒱 (quasiCoherentPresheafFunctor S F)
    (fun n i ↦ isIso_cechProductMapOfFunctor_restrictFunctor 𝒱 n i)).symm

/-- For a standard Zariski covering `𝒰 = {U_i → U}` of an affine open `U` of `S`, the Čech
complex in `S_Zar` of the presheaf `Fᵃ`, which on the small Zariski site is `V ↦ Γ(V, F|_V)`,
is the complex `s((A/R)_• ⊗_R M)`, where `R = Γ(U, 𝒪)`, `A = Γ(∐ U_i, 𝒪)` with the coproduct
taken in `Over S`, and `M = Fᵃ(U)`. -/
@[stacks 03FJ "the isomorphism of complexes, case (c), the small Zariski site"]
public def cechComplexIsoAmitsurSmallZariski (F : S.Modules) [F.IsQuasicoherent]
    {T : S.Opens} [IsAffine (S.restrictFunctor.obj T).left]
    (𝒱 : PreZeroHypercover.{u} T)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒱.I₀), HasProduct (fun a ↦ Over.mk (𝒱.f (i a)))]
    (h : IsStandardCovering .zariski
      (fun i ↦ ((𝒱.map S.restrictFunctor).X i).left)
      (fun i ↦ ((𝒱.map S.restrictFunctor).f i).left)) :
    letI : Finite (𝒱.map S.restrictFunctor).I₀ := h.finite_index
    letI := overAffineSliceAlgebra (S.restrictFunctor.obj T)
      (Sigma.desc (𝒱.map S.restrictFunctor).f)
    cechComplex 𝒱 (S.restrictFunctor.op ⋙ quasiCoherentPresheafFunctor S F) ≅
      ((forget₂ (ModuleCat.{u} (Γ((S.restrictFunctor.obj T).left, ⊤) : Type u))
            AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (amitsurCochainComplex (Γ((S.restrictFunctor.obj T).left, ⊤) : Type u)
          (Γ((∐ (𝒱.map S.restrictFunctor).X).left, ⊤) : Type u)
          (Stacks.Sites.coeffModule S F (𝟭 (Over S)) (S.restrictFunctor.obj T))) :=
  cechComplexIsoImageSmallZariski F 𝒱 ≪≫
    cechComplexIsoAmitsurStandardCovering (S.restrictFunctor.obj T) .zariski F
      (𝒱.map S.restrictFunctor) h

/-- The Čech cohomology of `Fᵃ` on a standard Zariski covering of an affine open of `S` vanishes
in every positive degree. -/
@[stacks 03FJ "the `Cech^p = 0 for p >= 1` clause, case (c), the small Zariski site"]
public theorem isZero_cechCohomology_succ_quasiCoherentPresheaf_smallZariski (F : S.Modules)
    [F.IsQuasicoherent] {T : S.Opens} [IsAffine (S.restrictFunctor.obj T).left]
    (𝒱 : PreZeroHypercover.{u} T)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒱.I₀), HasProduct (fun a ↦ Over.mk (𝒱.f (i a)))]
    (h : IsStandardCovering .zariski
      (fun i ↦ ((𝒱.map S.restrictFunctor).X i).left)
      (fun i ↦ ((𝒱.map S.restrictFunctor).f i).left)) (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱
      (S.restrictFunctor.op ⋙ quasiCoherentPresheafFunctor S F) p) :=
  cechCohomology_isZero_of_isZero_of_functor S.restrictFunctor 𝒱
    (quasiCoherentPresheafFunctor S F) (isIso_cechProductMapOfFunctor_restrictFunctor 𝒱 · ·) p
    (isZero_cechCohomology_succ_quasiCoherentPresheaf (S.restrictFunctor.obj T) .zariski F
      (𝒱.map S.restrictFunctor) h p hp)

end AlgebraicGeometry

end
