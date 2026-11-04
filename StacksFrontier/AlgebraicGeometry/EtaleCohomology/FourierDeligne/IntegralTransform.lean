module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusNatIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# Integral transforms on `D⁺` of étale sheaves of modules

Let `Λ` be a commutative ring, `f : X ⟶ S` and `g : Y ⟶ S` morphisms of schemes, `j` a
compactification of `X` over `S` and `𝓛` a sheaf of `Λ`-modules on `X ×_S Y` such that `- ⊗ 𝓛`
is exact. The *integral transform with kernel `𝓛`* is

`Φ_𝓛(K) = R pr₂! (pr₁⁻¹ K ⊗ 𝓛)`,

with `R pr₂!` computed through the base change of `j` to `X ×_S Y ⟶ Y`. For `X = Y = 𝔸¹_k`,
`S = Spec k` and `𝓛 = m⁻¹ L_ψ` the pullback of an Artin–Schreier sheaf along the multiplication
`m(x, t) = x t`, this is the `ℓ`-adic Fourier transform of Deligne and Laumon at a finite level.

## Main definitions

* `Stacks.EtaleCohomology.IsExactTensorRight`: `- ⊗ N` is additive and exact.
* `Stacks.EtaleCohomology.etaleModuleDerivedTensorRight`: `- ⊗ N` on `D⁺`, degreewise.
* `Stacks.EtaleCohomology.integralTransform`: `Φ_𝓛`.
* `Stacks.EtaleCohomology.DerivedLowerShriekProjectionFormula`: the projection formula
  `Rf_!(M ⊗ f⁻¹ N) ≅ Rf_! M ⊗ N` for `N` étale-locally free of finite rank, as a proposition.

## Main results

* `Stacks.EtaleCohomology.integralTransformCompIso`: `Φ_{𝓛₂} ∘ Φ_{𝓛₁}` is the transform through
  the triple product with kernel `pr₁₂⁻¹ 𝓛₁ ⊗ pr₂₃⁻¹ 𝓛₂`, given the projection formula.

## Implementation notes

The tensor product is that of `CategoryTheory.Sheaf.monoidalCategory`, the sheafified objectwise
tensor product, as in `Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal`.
`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, and so does `Φ_𝓛`.

## References

* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, 1.2]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  isMonoidal_W_etaleModules etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ]

/-- **`- ⊗ N` is exact**: additive, left exact and right exact, as for a sheaf with flat fibres
(`Stacks.EtaleCohomology.preservesFiniteLimits_tensorRight_etaleModules_of_flat`). -/
def IsExactTensorRight {X : Scheme.{u}} (N : EtaleModules.{u, 0} Λ X) : Prop :=
  (MonoidalCategory.tensorRight N).Additive ∧
    PreservesFiniteLimits (MonoidalCategory.tensorRight N) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight N)

/-- **`- ⊗ N` on `D⁺(X_étale, Λ)`**, for `- ⊗ N` exact: it acts degreewise. -/
def etaleModuleDerivedTensorRight {X : Scheme.{u}} (N : EtaleModules.{u, 0} Λ X)
    (hN : IsExactTensorRight Λ N) :
    DerivedCategory.Plus (EtaleModules.{u, 0} Λ X) ⥤
      DerivedCategory.Plus (EtaleModules.{u, 0} Λ X) :=
  haveI := hN.1
  haveI := hN.2.1
  haveI := hN.2.2
  (MonoidalCategory.tensorRight N).mapDerivedCategoryPlus

/-- `- ⊗ (A ⊗ B)` is exact when `- ⊗ A` and `- ⊗ B` are: it is `(- ⊗ A) ⊗ B`. -/
theorem IsExactTensorRight.tensor {X : Scheme.{u}} {A B : EtaleModules.{u, 0} Λ X}
    (hA : IsExactTensorRight Λ A) (hB : IsExactTensorRight Λ B) :
    IsExactTensorRight Λ (A ⊗ B) := by
  have := hA.1; have := hA.2.1; have := hA.2.2
  have := hB.1; have := hB.2.1; have := hB.2.2
  exact ⟨Functor.additive_of_iso (tensorRightTensor A B).symm,
    preservesFiniteLimits_of_natIso (tensorRightTensor A B).symm,
    preservesFiniteColimits_of_natIso (tensorRightTensor A B).symm⟩

/-- **`(- ⊗ A) ⊗ B ≅ - ⊗ (A ⊗ B)` on `D⁺`**, from the associator. -/
def etaleModuleDerivedTensorRightTensorIso {X : Scheme.{u}} {A B : EtaleModules.{u, 0} Λ X}
    (hA : IsExactTensorRight Λ A) (hB : IsExactTensorRight Λ B) :
    etaleModuleDerivedTensorRight Λ A hA ⋙ etaleModuleDerivedTensorRight Λ B hB ≅
      etaleModuleDerivedTensorRight Λ (A ⊗ B) (hA.tensor Λ hB) :=
  haveI := hA.1; haveI := hA.2.1; haveI := hA.2.2
  haveI := hB.1; haveI := hB.2.1; haveI := hB.2.2
  haveI := (hA.tensor Λ hB).1; haveI := (hA.tensor Λ hB).2.1; haveI := (hA.tensor Λ hB).2.2
  Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso (MonoidalCategory.tensorRight A)
      (MonoidalCategory.tensorRight B) ≪≫
    Stacks.DerivedFunctor.mapDerivedCategoryPlusNatIso (tensorRightTensor A B).symm

/-- **The inverse image of a composite on `D⁺`** is the composite of the inverse images. -/
def etaleModuleDerivedInverseImagePlusCompIsoAny {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    etaleModuleDerivedInverseImagePlus.{u, 0} Λ (a ≫ b) ≅
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ b ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ a :=
  Stacks.DerivedFunctor.mapDerivedCategoryPlusNatIso (etaleModuleInverseImageCompIso Λ a b) ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso (etaleModuleInverseImage.{u, 0} Λ b)
      (etaleModuleInverseImage.{u, 0} Λ a)).symm

attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal

/-- On sheaves: `a⁻¹ (- ⊗ N) ≅ a⁻¹(-) ⊗ a⁻¹ N`, the monoidal structure of the inverse image. -/
def etaleModuleInverseImageTensorRightIso {X Y : Scheme.{u}} (a : X ⟶ Y)
    (N : EtaleModules.{u, 0} Λ Y) :
    MonoidalCategory.tensorRight N ⋙ etaleModuleInverseImage.{u, 0} Λ a ≅
      etaleModuleInverseImage.{u, 0} Λ a ⋙
        MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ a).obj N) :=
  NatIso.ofComponents
    (fun M => (Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ a) M N).symm)
    (fun φ => by simp)

/-- **`a⁻¹ (K ⊗ N) ≅ a⁻¹ K ⊗ a⁻¹ N` on `D⁺`**, for `- ⊗ N` and `- ⊗ a⁻¹ N` exact. -/
def etaleModuleDerivedInverseImageTensorRightIso {X Y : Scheme.{u}} (a : X ⟶ Y)
    (N : EtaleModules.{u, 0} Λ Y) (hN : IsExactTensorRight Λ N)
    (haN : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ a).obj N)) :
    etaleModuleDerivedTensorRight Λ N hN ⋙ etaleModuleDerivedInverseImagePlus.{u, 0} Λ a ≅
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ a ⋙ etaleModuleDerivedTensorRight Λ _ haN :=
  haveI := hN.1; haveI := hN.2.1; haveI := hN.2.2
  haveI := haN.1; haveI := haN.2.1; haveI := haN.2.2
  Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso (MonoidalCategory.tensorRight N)
      (etaleModuleInverseImage.{u, 0} Λ a) ≪≫
    Stacks.DerivedFunctor.mapDerivedCategoryPlusNatIso
      (etaleModuleInverseImageTensorRightIso Λ a N) ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso (etaleModuleInverseImage.{u, 0} Λ a)
      (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ a).obj N))).symm

section Transform

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (j : CompactificationOf (Over.mk f))

/-- **The integral transform with kernel `𝓛`**, `Φ_𝓛(K) = R pr₂! (pr₁⁻¹ K ⊗ 𝓛)` from
`D⁺(X_étale, Λ)` to `D⁺(Y_étale, Λ)`, for `𝓛` on `X ×_S Y` with `- ⊗ 𝓛` exact and `R pr₂!`
computed through the base change of the compactification `j` of `X` over `S`. -/
def integralTransform (𝓛 : EtaleModules.{u, 0} Λ (pullback f g)) (h𝓛 : IsExactTensorRight Λ 𝓛) :
    DerivedCategory.Plus (EtaleModules.{u, 0} Λ X) ⥤
      DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y) :=
  etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g) ⋙
    etaleModuleDerivedTensorRight Λ 𝓛 h𝓛 ⋙
      derivedLowerShriek.{u, 0} (pullback.snd f g) (j.baseChange (IsPullback.of_hasPullback f g)) Λ

end Transform

/-- **`N` is étale-locally free of finite rank**: every object of the small étale site has an
étale covering on whose members `N` is constant with value a finite free `Λ`-module. -/
abbrev IsLocallyFreeEtaleModule {Y : Scheme.{u}} (N : EtaleModules.{u, 0} Λ Y) : Prop :=
  Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
    (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N

/-- **The projection formula for `Rf_!` and a locally free sheaf on the base**,
`Rf_!(M ⊗ f⁻¹ N) ≅ Rf_! M ⊗ N` on `D⁺_tors(X_étale, Λ)`, naturally in `M`, for `N` étale-locally
free of finite rank on `Y`. This is form (1) of the projection formula; it is carried as a
hypothesis by the consumers in this directory. -/
def DerivedLowerShriekProjectionFormula : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))
    (N : EtaleModules.{u, 0} Λ Y), IsLocallyFreeEtaleModule Λ N →
    ∀ (hN : IsExactTensorRight Λ N)
      (hfN : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ f).obj N)),
      Nonempty ((isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedTensorRight Λ _ hfN ⋙
          derivedLowerShriek.{u, 0} f j Λ ≅
        (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f j Λ ⋙
          etaleModuleDerivedTensorRight Λ N hN)

section Finite

variable {Λ} [Finite Λ]

/-- Over a finite ring every object of `D⁺` is torsion, so an isomorphism of functors on
`D⁺_tors` is one on `D⁺`. -/
def isoOfIsTorsionPlusι {X : Scheme.{u}} {D : Type*} [Category D]
    {F G : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X) ⥤ D}
    (e : (isTorsionPlus.{u, 0} Λ X).ι ⋙ F ≅ (isTorsionPlus.{u, 0} Λ X).ι ⋙ G) : F ≅ G :=
  have hK : ∀ K, isTorsionPlus.{u, 0} Λ X K := fun K i V x => by
    have := Fintype.ofFinite Λ
    refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun W g _ => ⟨Nat.card Λ, Nat.card_pos, ?_⟩⟩
    rw [← Nat.cast_smul_eq_nsmul Λ, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero, zero_smul]
  NatIso.ofComponents (fun K => e.app ⟨K, hK K⟩)
    (fun {K K'} φ => e.hom.naturality (X := ⟨K, hK K⟩) (Y := ⟨K', hK K'⟩) (ObjectProperty.homMk φ))

end Finite

section Composition

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The triple product `X ×_S Y ×_S Z`, as `(X ×_S Y) ×_Y (Y ×_S Z)`. -/
abbrev tripleProduct : Scheme.{u} := pullback (pullback.snd f g) (pullback.fst g h)

/-- The projection `X ×_S Y ×_S Z ⟶ X ×_S Y`. -/
abbrev tripleProduct₁₂ : tripleProduct f g h ⟶ pullback f g := pullback.fst _ _

/-- The projection `X ×_S Y ×_S Z ⟶ Y ×_S Z`. -/
abbrev tripleProduct₂₃ : tripleProduct f g h ⟶ pullback g h := pullback.snd _ _

variable (jX : CompactificationOf (Over.mk f)) (jY : CompactificationOf (Over.mk g))
  (𝓛₁ : EtaleModules.{u, 0} Λ (pullback f g)) (h₁ : IsExactTensorRight Λ 𝓛₁)
  (𝓛₂ : EtaleModules.{u, 0} Λ (pullback g h)) (h₂ : IsExactTensorRight Λ 𝓛₂)
  (h₁' : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ (tripleProduct₁₂ f g h)).obj 𝓛₁))
  (h₂' : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ (tripleProduct₂₃ f g h)).obj 𝓛₂))
  (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ f g h ≫ pullback.snd g h)))

/-- **The composite of two integral transforms** is the transform from `X` to `Z` through the
triple product with kernel `pr₁₂⁻¹ 𝓛₁ ⊗ pr₂₃⁻¹ 𝓛₂`:

`Φ_{𝓛₂} (Φ_{𝓛₁} K) ≅ R pr₃! (pr₁⁻¹ K ⊗ pr₁₂⁻¹ 𝓛₁ ⊗ pr₂₃⁻¹ 𝓛₂)`,

for `Λ` finite and `𝓛₂` étale-locally free of finite rank. The isomorphism is base change for
`R pr₂!` ([Stacks, Tag 0F7L]) along `pr₁ : Y ×_S Z ⟶ Y`, the projection formula for
`pr₂₃ : X ×_S Y ×_S Z ⟶ Y ×_S Z` and `𝓛₂` (the hypothesis `hproj`), the monoidal structure of the
inverse image and the composition of lower shriek functors ([Stacks, Tag 0F7J]). -/
def integralTransformCompIso [Finite Λ] (hproj : DerivedLowerShriekProjectionFormula.{u} Λ)
    (h𝓛₂ : IsLocallyFreeEtaleModule Λ 𝓛₂)
    [CompactSpace ↥(tripleProduct f g h)] [QuasiSeparatedSpace ↥(tripleProduct f g h)]
    [CompactSpace ↥(pullback g h)] [QuasiSeparatedSpace ↥(pullback g h)] [CompactSpace Z]
    [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g]
    [LocallyOfFiniteType g] :
    integralTransform Λ f g jX 𝓛₁ h₁ ⋙ integralTransform Λ g h jY 𝓛₂ h₂ ≅
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ (tripleProduct₁₂ f g h ≫ pullback.fst f g) ⋙
        etaleModuleDerivedTensorRight Λ _ (h₁'.tensor Λ h₂') ⋙
          derivedLowerShriek.{u, 0} (tripleProduct₂₃ f g h ≫ pullback.snd g h) jQ Λ :=
  let q₁₂ := tripleProduct₁₂ f g h
  let q₂₃ := tripleProduct₂₃ f g h
  let sq : IsPullback q₁₂ q₂₃ (pullback.snd f g) (pullback.fst g h) := IsPullback.of_hasPullback _ _
  let jP := jX.baseChange (IsPullback.of_hasPullback f g)
  let jP' := jY.baseChange (IsPullback.of_hasPullback g h)
  -- base change of `R pr₂!` along `Y ×_S Z ⟶ Y`
  let e₁ : derivedLowerShriek.{u, 0} (pullback.snd f g) jP Λ ⋙
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst g h) ≅
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁₂ ⋙
        derivedLowerShriek.{u, 0} q₂₃ (jP.baseChange sq) Λ :=
    isoOfIsTorsionPlusι (derivedLowerShriekBaseChangeIso Λ sq jP)
  -- the projection formula for `pr₂₃` and `𝓛₂`
  let e₂ : derivedLowerShriek.{u, 0} q₂₃ (jP.baseChange sq) Λ ⋙
      etaleModuleDerivedTensorRight Λ 𝓛₂ h₂ ≅
      etaleModuleDerivedTensorRight Λ _ h₂' ⋙ derivedLowerShriek.{u, 0} q₂₃ (jP.baseChange sq) Λ :=
    (isoOfIsTorsionPlusι (hproj q₂₃ (jP.baseChange sq) 𝓛₂ h𝓛₂ h₂ h₂').some).symm
  -- the composition of lower shriek functors
  let e₃ : derivedLowerShriek.{u, 0} q₂₃ (jP.baseChange sq) Λ ⋙
      derivedLowerShriek.{u, 0} (pullback.snd g h) jP' Λ ≅
      derivedLowerShriek.{u, 0} (q₂₃ ≫ pullback.snd g h) jQ Λ :=
    (isoOfIsTorsionPlusι (derivedLowerShriekCompIso Λ q₂₃ (pullback.snd g h)
      (jP.baseChange sq) jP' jQ)).symm
  Functor.isoWhiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g) ⋙
      etaleModuleDerivedTensorRight Λ 𝓛₁ h₁)
      (Functor.isoWhiskerRight e₁ _) ≪≫
    Functor.isoWhiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g))
      (Functor.isoWhiskerRight (etaleModuleDerivedInverseImageTensorRightIso Λ q₁₂ 𝓛₁ h₁ h₁')
        (derivedLowerShriek.{u, 0} q₂₃ (jP.baseChange sq) Λ ⋙
          etaleModuleDerivedTensorRight Λ 𝓛₂ h₂ ⋙
            derivedLowerShriek.{u, 0} (pullback.snd g h) jP' Λ)) ≪≫
    Functor.isoWhiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g) ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁₂ ⋙ etaleModuleDerivedTensorRight Λ _ h₁')
      (Functor.isoWhiskerRight e₂ (derivedLowerShriek.{u, 0} (pullback.snd g h) jP' Λ)) ≪≫
    Functor.isoWhiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g) ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁₂)
      (Functor.isoWhiskerRight (etaleModuleDerivedTensorRightTensorIso Λ h₁' h₂')
        (derivedLowerShriek.{u, 0} q₂₃ (jP.baseChange sq) Λ ⋙
          derivedLowerShriek.{u, 0} (pullback.snd g h) jP' Λ)) ≪≫
    Functor.isoWhiskerLeft ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g) ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁₂) ⋙
          etaleModuleDerivedTensorRight Λ _ (h₁'.tensor Λ h₂')) e₃ ≪≫
    Functor.associator (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g) ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ q₁₂)
      (etaleModuleDerivedTensorRight Λ _ (h₁'.tensor Λ h₂'))
      (derivedLowerShriek.{u, 0} (q₂₃ ≫ pullback.snd g h) jQ Λ) ≪≫
    Functor.isoWhiskerRight
      (etaleModuleDerivedInverseImagePlusCompIsoAny Λ q₁₂ (pullback.fst f g)).symm
      (etaleModuleDerivedTensorRight Λ _ (h₁'.tensor Λ h₂') ⋙
        derivedLowerShriek.{u, 0} (q₂₃ ≫ pullback.snd g h) jQ Λ)

end Composition

end Stacks.EtaleCohomology

end
