module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleComparisonWithEtale
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.InverseImage
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TorAmplitude
import StacksCore.Algebra.Category.ModuleCat.Localization
import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces

/-!
# Reductions modulo powers of an ideal coming from the étale site

Let `X` be a scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K` an object of
`D(X_proétale, Λ)`. Set `Kₙ = K ⊗_Λ^L Λ/Iⁿ`, an object of `D(X_proétale, Λ/Iⁿ)`. If `K₁`

1. lies in the essential image of `ε⁻¹ : D(X_étale, Λ/I) ⥤ D(X_proétale, Λ/I)`, and
2. has Tor amplitude in `[a, ∞)` for some `a`,

then so does `Kₙ`, over `Λ/Iⁿ`, for every `n` (Stacks 09B2).

## Main results

* `AlgebraicGeometry.ProEtale.etaleInverseImage_essImage_restrictScalars_iff`: along a surjective
  ring map, a sheaf of modules on `X_proétale` comes from `X_étale` exactly when its restriction
  of scalars does.
* `AlgebraicGeometry.ProEtale.derivedCategoryBPlus_essImage_tensor_of_isTorsionBySet`: the
  graded pieces `M ⊗_Λ^L K`, `M` a `Λ`-module killed by `I`.
* `AlgebraicGeometry.ProEtale.essImage_mapDerivedCategory_and_hasTorAmplitude_derivedExtendScalars`
  states that if `K₁` comes from `X_étale` and has Tor amplitude in `[a, ∞)`, then so does every
  `Kₙ`.

## Implementation notes

`ε⁻¹` on derived categories is `ε⁻¹` applied termwise,
`CategoryTheory.Functor.mapDerivedCategory`, `Kₙ` is the derived extension of scalars
`Stacks.ModuleSheaf.derivedExtendScalars` along `Λ → Λ/Iⁿ`, and Tor amplitude is
`Stacks.ModuleSheaf.HasTorAmplitude` for the set of degrees `Set.Ici a`.

Assertion (2) for `Kₙ` is the reduction of Tor amplitude modulo the powers of `I`,
`Stacks.ModuleSheaf.HasTorAmplitude.derivedExtendScalars_pow` (Stacks 0942). For assertion (1),
Tor amplitude in `[a, ∞)` puts `K₁` in degrees `≥ a`, so by Stacks 09B1 the question is whether
the cohomology sheaves of `Kₙ` come from `X_étale`
(`DerivedCategoryB.derivedCategoryBPlus_essImage_iff`), and those of `K₁` do. As for Stacks 09BR
the induction on `n` runs over `Λ`: read over `Λ`, `Kₙ` is `Λ/Iⁿ ⊗_Λ^L K`, these objects sit in
the distinguished triangles obtained by tensoring `0 → Iⁿ/Iⁿ⁺¹ → Λ/Iⁿ⁺¹ → Λ/Iⁿ → 0` with `K`,
and the bounded below objects whose cohomology sheaves come from `X_étale` are closed under
extensions, the essential image of `ε⁻¹` being a weak Serre subcategory (Stacks 09B1). The first
vertex is `M ⊗_Λ^L K` for the `Λ/I`-module `M = Iⁿ/Iⁿ⁺¹`, which is `M ⊗_{Λ/I}^L K₁` read over
`Λ` by the projection formula; it is bounded below by the Tor amplitude of `K₁`, and its
cohomology sheaves come from `X_étale` because `K₁` and the constant sheaf `M` do and `ε⁻¹`
commutes with the derived tensor product by a bounded above object
(`Stacks.ModuleSheaf.nonempty_homology_sheafPullback_tensor_iso`). Whether a sheaf of
`Λ/Iⁿ`-modules comes from `X_étale` can be read over `Λ`, since `ε⁻¹` commutes with
restriction of scalars and `ε⁻¹` is fully faithful.

All coefficient rings live in the universe `max (u + 1) w` of the module sections:
`ModuleCat.{s} Λ` is monoidal only for `Λ : Type s`, and the module sections must contain the
universe `u + 1` of the objects of the small étale and pro-étale sites. Every ring is isomorphic
to one in such a universe.

## References

* [Stacks Project, Tag 09B2](https://stacks.math.columbia.edu/tag/09B2)
* [Stacks Project, Tag 09B1](https://stacks.math.columbia.edu/tag/09B1)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.ModuleSheaf DerivedCategoryB

universe w u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory derivedMonoidal
  derivedSymmetric

variable {X : Scheme.{u}}

/-! ### Change of coefficient rings -/

section ChangeOfRings

variable {R S : Type (max (u + 1) w)} [CommRing R] [CommRing S] (f : R →+* S)

/-- **`ε⁻¹` commutes with restriction of scalars**: both composites are left adjoint to
coextension of scalars followed by `ε_*`. -/
def etaleInverseImageCompRestrictScalarsIso :
    Scheme.etaleInverseImage.{u, w} X S ⋙ restrictScalars (Scheme.ProEt.topology X) f ≅
      restrictScalars X.smallEtaleTopology f ⋙ Scheme.etaleInverseImage.{u, w} X R :=
  restrictScalarsSheafPullbackIso f (Scheme.etaleInverseImageAdjunction.{w} X S)
    (Scheme.etaleInverseImageAdjunction.{w} X R)

variable {f}

/-- **Along a surjective ring map, a sheaf of modules on `X_proétale` comes from `X_étale`
exactly when its restriction of scalars does.** If `F|_R ≅ ε⁻¹𝒢`, then `ε⁻¹ε_* F`, read over
`R`, is `ε⁻¹ε_*ε⁻¹𝒢 ≅ ε⁻¹𝒢 ≅ F|_R`, and restriction of scalars is fully faithful. -/
theorem etaleInverseImage_essImage_restrictScalars_iff (hf : Function.Surjective f)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} S)) :
    (Scheme.etaleInverseImage.{u, w} X R).essImage
        ((restrictScalars (Scheme.ProEt.topology X) f).obj F) ↔
      (Scheme.etaleInverseImage.{u, w} X S).essImage F := by
  refine ⟨fun ⟨G, ⟨e⟩⟩ => ?_, fun ⟨G, ⟨e⟩⟩ =>
    ⟨_, ⟨((etaleInverseImageCompRestrictScalarsIso.{w} f).app G).symm ≪≫
      (restrictScalars _ f).mapIso e⟩⟩⟩
  let A := (Scheme.etaleDirectImage.{u, w} X S).obj F
  let eA : (restrictScalars X.smallEtaleTopology f).obj A ≅
      (Scheme.etaleDirectImage.{u, w} X R).obj ((restrictScalars _ f).obj F) := Iso.refl _
  exact ⟨A, ⟨(fullyFaithfulRestrictScalars _ hf).preimageIso
    ((etaleInverseImageCompRestrictScalarsIso.{w} f).app A ≪≫
      (Scheme.etaleInverseImage.{u, w} X R).mapIso
        (eA ≪≫ (Scheme.etaleDirectImage.{u, w} X R).mapIso e.symm ≪≫
          (asIso ((Scheme.etaleInverseImageAdjunction.{w} X R).unit.app G)).symm) ≪≫ e)⟩⟩

/-- **Along a surjective ring map, an object of `D(X_proétale, S)` is bounded below with
cohomology sheaves coming from `X_étale` exactly when its restriction of scalars is**:
restriction of scalars commutes with cohomology and detects the vanishing of a sheaf. -/
theorem derivedCategoryBPlus_essImage_restrictScalars_iff (hf : Function.Surjective f)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} S))) :
    derivedCategoryBPlus (Scheme.etaleInverseImage.{u, w} X R).essImage
        ((restrictScalars (Scheme.ProEt.topology X) f).mapDerivedCategory.obj L) ↔
      derivedCategoryBPlus (Scheme.etaleInverseImage.{u, w} X S).essImage L := by
  let ρ := restrictScalars (Scheme.ProEt.topology X) f
  let e : ∀ i, (DerivedCategory.homologyFunctor _ i).obj (ρ.mapDerivedCategory.obj L) ≅
      ρ.obj ((DerivedCategory.homologyFunctor _ i).obj L) :=
    fun i => (ρ.mapDerivedCategoryHomologyIso i).app L
  have hz : ∀ i, IsZero ((DerivedCategory.homologyFunctor _ i).obj (ρ.mapDerivedCategory.obj L)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ i).obj L) := fun i =>
    ⟨fun h => isZero_of_isZero_restrictScalars_obj f (h.of_iso (e i).symm),
      fun h => (ρ.map_isZero h).of_iso (e i)⟩
  unfold derivedCategoryBPlus derivedCategoryB
  refine and_congr ⟨fun ⟨n, h⟩ => ⟨n, fun m hm => (hz m).1 (h m hm)⟩,
    fun ⟨n, h⟩ => ⟨n, fun m hm => (hz m).2 (h m hm)⟩⟩ (forall_congr' fun i => ?_)
  rw [ObjectProperty.prop_iff_of_iso (Scheme.etaleInverseImage.{u, w} X R).essImage (e i)]
  exact etaleInverseImage_essImage_restrictScalars_iff hf _

end ChangeOfRings

/-! ### The reduction modulo powers of `I` -/

section Reduction

variable {Λ : Type (max (u + 1) w)} [CommRing Λ] (I : Ideal Λ)

/-- The essential image of `ε⁻¹` on sheaves of `Λ`-modules is a weak Serre subcategory
(Stacks 09B1). -/
theorem isWeakSerre_etaleInverseImage_essImage (R : Type (max (u + 1) w)) [CommRing R] :
    WeakSerre.IsWeakSerre (Scheme.etaleInverseImage.{u, w} X R).essImage :=
  have := Scheme.isWeakSerreClass_etaleInverseImage_essImage.{w} X R
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

/-- **The graded pieces.** If `K ⊗_Λ^L Λ/I` comes from `X_étale` and has Tor amplitude in
`[a, ∞)`, then for every `Λ`-module `M` killed by `I` the derived tensor product `M ⊗_Λ^L K` is
bounded below with cohomology sheaves coming from `X_étale`: it is `M ⊗_{Λ/I}^L (K ⊗_Λ^L Λ/I)`
read over `Λ`, which is bounded below by the Tor amplitude, and `ε⁻¹` commutes with the derived
tensor product by the constant sheaf `M`, which comes from `X_étale`. -/
theorem derivedCategoryBPlus_essImage_tensor_of_isTorsionBySet
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (a : ℤ)
    (h₁ : (Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I)).mapDerivedCategory.essImage
      ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K))
    (h₂ : HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K) (Set.Ici a))
    (M : ModuleCat.{max (u + 1) w} Λ) (hkill : Module.IsTorsionBySet Λ M I) :
    derivedCategoryBPlus (Scheme.etaleInverseImage.{u, w} X Λ).essImage
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) _).obj M) ⊗ K) := by
  let J := Scheme.ProEt.topology X
  let π := Ideal.Quotient.mk I
  let ρ := restrictScalars J π
  let K₁ := (derivedExtendScalars J π).obj K
  let : Module (Λ ⧸ I) M := hkill.module
  let M' : ModuleCat.{max (u + 1) w} (Λ ⧸ I) := ModuleCat.of (Λ ⧸ I) M
  let eM : (ModuleCat.restrictScalars π).obj M' ≅ M :=
    LinearEquiv.toModuleIso
      { toFun := fun x => x
        invFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let L₁ : DerivedCategory (Sheaf J (ModuleCat.{max (u + 1) w} (Λ ⧸ I))) :=
    (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf J _).obj M')
  obtain ⟨e⟩ := nonempty_restrictScalars_tensor_derivedExtendScalars_iso π L₁ K
  let e' : (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf J _).obj M) ⊗ K ≅
      ρ.mapDerivedCategory.obj (L₁ ⊗ K₁) :=
    ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf J _).mapIso eM.symm ≪≫
      ((restrictScalarsConstantSheafIso J π).app M').symm) ≪≫
      ((ρ.mapDerivedCategorySingleFunctor 0).app _).symm ⊗ᵢ Iso.refl K) ≪≫ e.symm
  refine (derivedCategoryBPlus_isClosedUnderIsomorphisms _
    (isWeakSerre_etaleInverseImage_essImage.{w} Λ)).of_iso e'.symm ?_
  rw [derivedCategoryBPlus_essImage_restrictScalars_iff Ideal.Quotient.mk_surjective]
  refine ⟨⟨a, fun i hi => (h₂ _ i (by simpa using hi)).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso (β_ L₁ K₁))⟩, fun i => ?_⟩
  -- the cohomology sheaves of `M ⊗_{Λ/I}^L K₁` come from `X_étale`
  obtain ⟨N, ⟨eN⟩⟩ := h₁
  let G := X.etaleToProetale
  have : RepresentablyFlat G := flat_of_preservesFiniteLimits _
  have (V : X.ProEtᵒᵖ) : IsFiltered (CostructuredArrow G.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G (Opposite.unop V))
  have (V : X.ProEtᵒᵖ) : HasColimitsOfShape (CostructuredArrow G.op V)
      (ModuleCat.{max (u + 1) w} (Λ ⧸ I)) :=
    hasColimitsOfShape_of_essentiallySmall.{max (u + 1) w} _ _
  have (V : X.ProEtᵒᵖ) : HasColimitsOfShape (CostructuredArrow G.op V)
      (Type (max (u + 1) w)) :=
    hasColimitsOfShape_of_essentiallySmall.{max (u + 1) w} _ _
  have : (G.sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} (Λ ⧸ I))
      X.smallEtaleTopology J).IsRightAdjoint :=
    (Scheme.etaleInverseImageAdjunction.{w} X (Λ ⧸ I)).isRightAdjoint
  let Φ := G.sheafPullback (ModuleCat.{max (u + 1) w} (Λ ⧸ I)) X.smallEtaleTopology J
  let eΦ : Φ ≅ Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I) :=
    Functor.sheafPullbackConstruction.sheafPullbackIso G _ X.smallEtaleTopology J
  have : PreservesFiniteLimits Φ := preservesFiniteLimits_of_natIso eΦ.symm
  let Lₑ := (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w} (Λ ⧸ I))).obj M')
  obtain ⟨e₁⟩ := nonempty_homology_sheafPullback_tensor_iso G (Λ ⧸ I) X.smallEtaleTopology J
    N Lₑ 0 i
  let eK : Φ.mapDerivedCategory.obj N ≅ K₁ :=
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso Φ _ eΦ).app N ≪≫ eN
  let eL : Φ.mapDerivedCategory.obj Lₑ ≅ L₁ :=
    (Φ.mapDerivedCategorySingleFunctor 0).app _ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
      (eΦ.app _ ≪≫ (etaleInverseImageConstantSheafIso.{w, max (u + 1) w, u}).app M')
  exact ⟨_, ⟨(eΦ.app _).symm ≪≫ e₁ ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso ((eK ⊗ᵢ eL) ≪≫ β_ K₁ L₁)⟩⟩

/-- **The induction on `n`**: if `K ⊗_Λ^L Λ/I` comes from `X_étale` and has Tor amplitude in
`[a, ∞)`, then `Λ/Iⁿ ⊗_Λ^L K` is bounded below with cohomology sheaves coming from `X_étale`, for
every `n`. -/
theorem derivedCategoryBPlus_essImage_tensor_quotient_pow
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (a : ℤ)
    (h₁ : (Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I)).mapDerivedCategory.essImage
      ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K))
    (h₂ : HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K) (Set.Ici a))
    (n : ℕ) :
    derivedCategoryBPlus (Scheme.etaleInverseImage.{u, w} X Λ).essImage
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) _).obj (ModuleCat.of Λ (Λ ⧸ I ^ n))) ⊗ K) := by
  have hB := isWeakSerre_etaleInverseImage_essImage.{w} (X := X) Λ
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorRight (Scheme.ProEt.topology X) Λ K
  let := s
  induction n with
  | zero =>
    have : Subsingleton (Λ ⧸ I ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
    have hz : IsZero ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) _).obj
          (ModuleCat.of Λ (Λ ⧸ I ^ 0))) ⊗ K) :=
      (tensorRight K).map_isZero (Functor.map_isZero _ (Functor.map_isZero _
        (@ModuleCat.isZero_of_subsingleton _ _ _ this)))
    exact ⟨isBoundedBelow_of_isZero hz, fun i =>
      zero_mem_of_isWeakSerre _ hB _ ((DerivedCategory.homologyFunctor _ i).map_isZero hz)⟩
  | succ n ih =>
    obtain ⟨_, _, _, hT⟩ := Stacks.ConstantSheaf.exists_distTriang_map_singleTriangle
      (tensorRight K) ((Stacks.ConstantSheaf.idealPowShortComplex Λ I n).map
        (constantSheaf (Scheme.ProEt.topology X) _))
      ((Stacks.ConstantSheaf.shortExact_idealPowShortComplex Λ I n).map_of_exact _)
    have h := derivedCategoryBPlus_essImage_tensor_of_isTorsionBySet I K a h₁ h₂ _
      (fun x a => Stacks.ConstantSheaf.smul_eq_zero_idealPowSuccQuot Λ I n a a.2 x)
    exact ⟨isBoundedBelow_mem_obj₂_of_distinguished _ hT h.1 ih.1,
      derivedCategoryB_mem_obj₂_of_distinguished _ hB _ hT h.2 ih.2⟩

/-- **Stacks 09B2.** Let `X` be a scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K` an
object of `D(X_proétale, Λ)`. Set `Kₙ = K ⊗_Λ^L Λ/Iⁿ`, the derived extension of scalars of `K`
along `Λ → Λ/Iⁿ`. If `K₁` is in the essential image of `ε⁻¹ : D(X_étale, Λ/I) ⥤
D(X_proétale, Λ/I)` and has Tor amplitude in `[a, ∞)`, then, for every `n`, `Kₙ` is in the
essential image of `ε⁻¹ : D(X_étale, Λ/Iⁿ) ⥤ D(X_proétale, Λ/Iⁿ)` and has Tor amplitude in
`[a, ∞)`.

Here `ε⁻¹` on derived categories is `ε⁻¹` applied termwise, and Tor amplitude in `[a, ∞)` is
`Stacks.ModuleSheaf.HasTorAmplitude` for `Set.Ici a`: `Hⁱ(L ⊗^L F) = 0` for `i < a` and every
sheaf of modules `F`. -/
@[stacks 09B2]
theorem essImage_mapDerivedCategory_and_hasTorAmplitude_derivedExtendScalars
    [IsNoetherianRing Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (a : ℤ)
    (h₁ : (Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I)).mapDerivedCategory.essImage
      ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K))
    (h₂ : HasTorAmplitude (J := Scheme.ProEt.topology X)
      ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K) (Set.Ici a))
    (n : ℕ) :
    (Scheme.etaleInverseImage.{u, w} X (Λ ⧸ I ^ n)).mapDerivedCategory.essImage
        ((derivedExtendScalars _ (Ideal.Quotient.mk (I ^ n))).obj K) ∧
      HasTorAmplitude (J := Scheme.ProEt.topology X)
        ((derivedExtendScalars _ (Ideal.Quotient.mk (I ^ n))).obj K)
        (Set.Ici a) := by
  have hn := h₂.derivedExtendScalars_pow I (IsNoetherian.noetherian I) n
  refine ⟨?_, hn⟩
  obtain ⟨e⟩ := nonempty_restrictScalars_derivedExtendScalars_iso (Ideal.Quotient.mk (I ^ n)) K
  let e' := e ≪≫ ((DerivedCategory.singleFunctor _ 0).mapIso
    ((constantSheaf (Scheme.ProEt.topology X) _).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := Λ) (ModuleCat.of (Λ ⧸ I ^ n) (Λ ⧸ I ^ n))))
    ⊗ᵢ Iso.refl K)
  have h := (derivedCategoryBPlus_isClosedUnderIsomorphisms _
    (isWeakSerre_etaleInverseImage_essImage.{w} Λ)).of_iso e'.symm
    (derivedCategoryBPlus_essImage_tensor_quotient_pow I K a h₁ h₂ n)
  have h' := (derivedCategoryBPlus_essImage_restrictScalars_iff
    (Ideal.Quotient.mk_surjective (I := I ^ n)) _).1 h
  exact ((derivedCategoryBPlus_essImage_iff _
    (Scheme.etaleInverseImageAdjunction.{w} X (Λ ⧸ I ^ n))
    (fun A _ => Scheme.rightAcyclic_etaleInverseImage_obj.{w} X (Λ ⧸ I ^ n) A) _).1 h').2

end Reduction

end AlgebraicGeometry.ProEtale
