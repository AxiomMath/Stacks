module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleFromCompletionSpace
public import StacksFrontier.RingTheory.Rig.EtaleOutsideRingEquiv

/-!
# The chart data of Stacks 0AR2

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of algebraic
spaces over `S` and let `T ⊆ |X|` be closed, with `U ⊂ X` the open complement of `T` and
`U' = f⁻¹U`; this is the situation of Stacks 0GDB. Assume that `X` is locally Noetherian, `f` is
locally of finite type and `U' → U` is étale, the hypotheses of **Stacks 0AR2**.

For a commuting square of étale charts `Spec A' ⟶ X'`, `Spec A ⟶ X` over `f`, whose horizontal
map is the spectrum of a ring map `φ : A → A'`, this file derives the affine data of the source's
proof: `A` is Noetherian, `φ` is of finite type, and `Spec A' → Spec A` is étale over the
complement of the inverse image of `T`, which is the zero locus of any ideal cutting it out. The
source says: "Observe that `W'_{ij} → W_i` is locally of finite type and induces a smooth
morphism `W'_{ij} ∖ T'_{ij} → W_i ∖ T_i` (as this is true for `f` and these properties of
morphisms are étale local on the source and target). Observe that `W_i` is locally Noetherian."

Together with the affine case `isRigEtaleHom_adicCompletionMap_of_isEtaleOutside` this gives the
hypothesis `hP` of `correspondsToNoetherianMapAfterSourceCover_completionSheafMap` for
rig-étaleness: condition (4) of **Stacks 0GCZ** for `f_{/T}`, from which the implication
(4) ⟹ (1) of Stacks 0GCZ gives that `f_{/T}` is rig-étale.

## Main results

* `AlgebraicGeometry.FormalSpace.isNoetherianRing_of_isLocallyNoetherian_chart`,
  `AlgebraicGeometry.FormalSpace.finiteType_of_isLocallyOfFiniteType_chart` and
  `AlgebraicGeometry.FormalSpace.isEtaleOutside_of_isEtale_openComplementRestriction_chart`: the
  affine data.
* `AlgebraicGeometry.FormalSpace.correspondsToRigEtaleMapAfterSourceCover_completionSheafMap`:
  condition (4) of Stacks 0GCZ for `f_{/T}`, from compatible étale atlases of `X` and `X'`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_of_atlases`: `f_{/T}` is
  rig-étale, from compatible étale atlases of `X` and `X'`.

## References

* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- The ring of an étale chart `Spec A ⟶ X` of a locally Noetherian algebraic space is
Noetherian. -/
theorem isNoetherianRing_of_isLocallyNoetherian_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXN : Space.IsLocallyNoetherian B S hS X)
    {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A))) (str : Spec (.of A) ⟶ S)
    (a : yoneda.obj (affineOver B S hS hA str) ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsNoetherianRing A :=
  isLocallyNoetherian_Spec.mp
    (hXN _ a ((Space.isEtale_iff_presheaf_of_yoneda B S hS a).mpr ha))

/-- The ring map of a chart square over a morphism locally of finite type is of finite type. -/
theorem finiteType_of_isLocallyOfFiniteType_chart
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    {A A' : Type u} [CommRing A] [CommRing A'] (hA : B.Contains (Spec (.of A)))
    (hA' : B.Contains (Spec (.of A'))) (str : Spec (.of A) ⟶ S) (φ : A →+* A')
    (a : yoneda.obj (affineOver B S hS hA str) ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (a' : yoneda.obj (affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str)) ⟶ X')
    (ha' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a')
    (h : affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str) ⟶
      affineOver B S hS hA str)
    (hh : h = Space.specSiteObjectMap φ hA hA' str)
    (hsq : yoneda.map h ≫ a = a' ≫ f) :
    φ.FiniteType := by
  have h1 := hf _ _ a' a h ha' ha hsq
  subst hh
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h1

/-- **The chart map is étale off the inverse image of `T`.** For a chart square over a morphism
`f` whose restriction to the open complement of a closed `T` is étale, with Noetherian rings and
a finite type ring map `φ : A → A'`, and an ideal `J ⊆ A` cutting out the inverse image of `T` in
`Spec A`, the map `Spec A' → Spec A` is étale over `Spec A ∖ V(J)`. -/
theorem isEtaleOutside_of_isEtale_openComplementRestriction_chart
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    {A A' : Type u} [CommRing A] [CommRing A'] [IsNoetherianRing A] [IsNoetherianRing A']
    (hA : B.Contains (Spec (.of A)))
    (hA' : B.Contains (Spec (.of A'))) (str : Spec (.of A) ⟶ S) (φ : A →+* A')
    (hφ : φ.FiniteType)
    (a : yoneda.obj (affineOver B S hS hA str) ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (a' : yoneda.obj (affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str)) ⟶ X')
    (ha' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a')
    (h : affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str) ⟶
      affineOver B S hS hA str)
    (hh : h = Space.specSiteObjectMap φ hA hA' str)
    (hsq : yoneda.map h ≫ a = a' ≫ f) (J : Ideal A)
    (hJ : Space.pointsMap B S hS _ a ⁻¹' T = zeroLocusPoints B S hS hA str J) :
    letI : Algebra A A' := φ.toAlgebra
    Rig.IsEtaleOutside J A' := by
  let : Algebra A A' := φ.toAlgebra
  let F : Spec (.of A') ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
  have hF : LocallyOfFiniteType F :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hφ
  let α : A ≃+* Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  let β : A' ≃+* Γ(Spec (.of A'), ⊤) :=
    (Scheme.ΓSpecIso (.of A')).symm.commRingCatIsoToRingEquiv
  let : Algebra Γ(Spec (.of A), ⊤) Γ(Spec (.of A'), ⊤) := F.appTop.hom.toAlgebra
  have hcomm : ∀ x : A, β (algebraMap A A' x) =
      algebraMap Γ(Spec (.of A), ⊤) Γ(Spec (.of A'), ⊤) (α x) := by
    intro x
    have h3 : (Scheme.ΓSpecIso (.of A)).inv ≫ F.appTop =
        CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of A')).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc,
        ← Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ), Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    exact (ConcreteCategory.congr_hom h3 x).symm
  refine Rig.IsEtaleOutside.of_ringEquiv α β hcomm ?_
  refine isEtaleOutside_of_forall_etaleAt F (J.map (α : A →+* Γ(Spec (.of A), ⊤))) ?_
  intro x hx
  have hhF : (BigFppfOver.toScheme B S hS).map h = F := by rw [hh]; rfl
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) := by rwa [hhF]
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA str)) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of A)))
  obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS
    (affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str)) x
  rw [← hhF]
  refine etaleAt_of_isEtale_openComplementRestriction B S hS hX' hX f T hT het a'
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS a').mpr ha') a ha h hsq p fun hpT ↦ hx ?_
  have hp1 : Space.pointsMap B S hS _ (yoneda.map h) p ∈
      zeroLocusPoints B S hS hA str J := by
    rwa [← hJ, Set.mem_preimage, ← Function.comp_apply (f := Space.pointsMap B S hS _ a),
      ← Space.pointsMap_comp, hsq]
  have hp2 := (Set.ext_iff.mp (zeroLocusPoints_eq_preimage_pointsToScheme B S hS hA str J) _).mp
    hp1
  have hp3 : F (Space.pointsToScheme B S hS _ p) ∈
      (PrimeSpectrum.zeroLocus (J : Set A) : Set (PrimeSpectrum A)) := by
    have e := Space.pointsToScheme_pointsMap B S hS h p
    rw [hhF] at e
    exact e ▸ hp2
  rw [Scheme.mem_zeroLocus_iff]
  intro s hs
  rw [Ideal.map_comap_of_equiv] at hs
  change α.symm s ∈ J at hs
  have hs' : s = (Scheme.ΓSpecIso (.of A)).inv (α.symm s) := (α.apply_symm_apply s).symm
  rw [hs', basicOpen_eq_of_affine]
  exact fun hmem ↦ hmem (hp3 hs)

/-- **Condition (4) of Stacks 0GCZ for `f_{/T}`.** In the situation of Stacks 0GDB, with `X`
locally Noetherian, `f` locally of finite type and `U' → U` étale — the hypotheses of Stacks
0AR2 — let `{Spec A_i ⟶ X}` be an étale covering of `X` and `{Spec A'_k ⟶ X'}` one of `X'`, each
`Spec A'_k` mapping to `Spec A_{ι k}` by the spectrum of a ring map `φ k` compatibly with `f`.
Then the completed charts `(Spec A'_k)_{/T'} ⟶ X'_{/T'}` form a covering as in Definition 0AIM
whose members factor through the completed charts of `X_{/T}` by maps corresponding to rig-étale
maps in `WAdm^{Noeth}`.

This is the source's reduction of Stacks 0AR2 to the affine case together with the affine case
itself (part (1) of Stacks 0ALQ). -/
theorem correspondsToRigEtaleMapAfterSourceCover_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T) (hXN : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    {Ik : Type (u + 1)} {A' : Ik → Type u} [∀ k, CommRing (A' k)]
    (ι : Ik → Ix) (φ : ∀ k, A (ι k) →+* A' k)
    (hA' : ∀ k, B.Contains (AlgebraicGeometry.Spec (.of (A' k))))
    (a' : ∀ k, yoneda.obj (affineOver B S hS (hA' k)
      (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k))) ⟶ X')
    (ha' : ∀ k, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a' k))
    (hcov' : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun k ↦ Space.sheafifiedULiftMap B S hS (a' k)))
    (h : ∀ k, affineOver B S hS (hA' k) (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k)) ⟶
      affineOver B S hS (hA (ι k)) (str (ι k)))
    (hh : ∀ k, h k = Space.specSiteObjectMap (φ k) (hA (ι k)) (hA' k) (str (ι k)))
    (hsq : ∀ k, yoneda.map (h k) ≫ a (ι k) = a' k ≫ f) :
    CorrespondsToRigEtaleMapAfterSourceCover B S hS (Space.completionSheafMap B S hS f T) := by
  have hAN : ∀ i, IsNoetherianRing (A i) := fun i ↦
    isNoetherianRing_of_isLocallyNoetherian_chart hXN (hA i) (str i) (a i) (ha i)
  have hft : ∀ k, (φ k).FiniteType := fun k ↦
    finiteType_of_isLocallyOfFiniteType_chart f hf (hA (ι k)) (hA' k) (str (ι k)) (φ k)
      (a (ι k)) (ha (ι k)) (a' k) (ha' k) (h k) (hh k) (hsq k)
  have hA'N : ∀ k, IsNoetherianRing (A' k) := fun k ↦
    let : Algebra (A (ι k)) (A' k) := (φ k).toAlgebra
    have : Algebra.FiniteType (A (ι k)) (A' k) := hft k
    Algebra.FiniteType.isNoetherianRing (A (ι k)) (A' k)
  have hsh : ∀ {W : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (hZ : IsAlgebraicSpace B S hS Z) (b : yoneda.obj W ⟶ Z),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS b).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS b).hom hai := fun hZ b hb ↦
    exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS _) hZ b
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS b).mpr hb)
  exact correspondsToNoetherianMapAfterSourceCover_completionSheafMap
    (fun φ ↦ TopologicalRing.IsRigEtaleHom φ)
    propertyInvariantUnderRingEquiv_isRigEtaleHom hX' hX f T hT hA str a
    (fun i ↦ hsh hX (a i) (ha i)) hcov ι φ hA' a' (fun k ↦ hsh hX' (a' k) (ha' k)) hcov' h hh
    hsq fun k J hJ ↦ isRigEtaleHom_adicCompletionMap_of_isEtaleOutside (φ k) J (hft k)
      (isEtaleOutside_of_isEtale_openComplementRestriction_chart hX' hX f T hT het
        (hA (ι k)) (hA' k) (str (ι k)) (φ k) (hft k) (a (ι k)) (ha (ι k)) (a' k) (ha' k) (h k)
        (hh k) (hsq k) J hJ)

/-- **Stacks 0AR2, assembled from the cover.** In the situation of Stacks 0GDB, if `X` is locally
Noetherian, `f` is locally of finite type and `U' → U` is étale, then `f_{/T}` is rig-étale,
given compatible étale atlases of `X` and `X'` read in the value universe of the formal algebraic
spaces.

This is condition (4) of Stacks 0GCZ for `f_{/T}`,
`correspondsToRigEtaleMapAfterSourceCover_completionSheafMap`, followed by the implication
(4) ⟹ (1) of Stacks 0GCZ,
`hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover`. The atlases
are produced by `AlgebraicGeometry.FormalSpace.exists_compatible_affineOver_atlases`. -/
theorem isRigEtale_completionSheafMap_of_atlases
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T) (hXN : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    {Ik : Type (u + 1)} {A' : Ik → Type u} [∀ k, CommRing (A' k)]
    (ι : Ik → Ix) (φ : ∀ k, A (ι k) →+* A' k)
    (hA' : ∀ k, B.Contains (AlgebraicGeometry.Spec (.of (A' k))))
    (a' : ∀ k, yoneda.obj (affineOver B S hS (hA' k)
      (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k))) ⟶ X')
    (ha' : ∀ k, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a' k))
    (hcov' : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun k ↦ Space.sheafifiedULiftMap B S hS (a' k)))
    (h : ∀ k, affineOver B S hS (hA' k) (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k)) ⟶
      affineOver B S hS (hA (ι k)) (str (ι k)))
    (hh : ∀ k, h k = Space.specSiteObjectMap (φ k) (hA (ι k)) (hA' k) (str (ι k)))
    (hsq : ∀ k, yoneda.map (h k) ≫ a (ι k) = a' k ≫ f) :
    IsRigEtale B S hS (Space.completionSheafMap B S hS f T) :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover B S hS _
      (correspondsToRigEtaleMapAfterSourceCover_completionSheafMap hX' hX f T hT hXN hf het
        hA str a ha hcov ι φ hA' a' ha' hcov' h hh hsq))

end AlgebraicGeometry.FormalSpace

end
