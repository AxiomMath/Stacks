module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.Sets
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageEssentialSurjectivityAbelian
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.ConstructibleDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A constructible sheaf embeds in finite pushforwards of finite constant sheaves (Stacks 09Z7)

Let `X` be a quasi-compact and quasi-separated scheme.
[Stacks, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7) embeds a constructible sheaf on
`X_étale` into finitely many finite pushforwards of finite constant sheaves:

1. a constructible sheaf of sets `ℱ` into a finite product `∏ᵢ fᵢ_* E̲ᵢ`, `Eᵢ` finite sets;
2. a constructible abelian sheaf `ℱ` into a finite direct sum `⨁ᵢ fᵢ_* M̲ᵢ`, `Mᵢ` finite abelian
   groups;
3. a constructible sheaf of `Λ`-modules `ℱ`, `Λ` a Noetherian ring, into a finite direct sum
   `⨁ᵢ fᵢ_* M̲ᵢ`, `Mᵢ` finite `Λ`-modules;

where each `fᵢ : Yᵢ ⟶ X` is finite and of finite presentation.

The proof of (2) and (3) is the source's, by absolute Noetherian approximation. Write
`X = lim_t X_t` with each `X_t` of finite type over `ℤ`, hence Noetherian, and affine transition
morphisms (Stacks 01ZA, `AlgebraicGeometry.exists_isLimit_finiteType`). The constructible `ℱ` is
the inverse image of a constructible `ℱ_t` on some `X_t` (the essential-surjectivity assertion of
Stacks 09YU:
`Stacks.EtaleCohomology.exists_isConstructibleEtaleAbelianSheaf_etaleAbelianInverseImage_iso` and
`Stacks.EtaleCohomology.exists_isConstructibleEtaleModule_etaleModuleInverseImage_iso`), and `ℱ_t`
embeds in a finite sum `⨁ᵢ fᵢ_* M̲ᵢ` with `fᵢ : Yᵢ ⟶ X_t` finite (Stacks 09Z6 (2) and (3)).
Inverse image along `π : X ⟶ X_t` is exact and additive, and carries `fᵢ_* M̲ᵢ` to `gᵢ_* M̲ᵢ` for
the base change `gᵢ : Yᵢ ×_{X_t} X ⟶ X`, which is again finite and of finite presentation: that is
the base change theorem for finite morphisms (Stacks 0959,
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_unconditional`, and for sheaves
of modules `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_app_of_isFinite`).

Part (1) is deduced from part (3) over the finite ring `Λ = ULift (ZMod 2)`, as Stacks 09Z6 (1)
is deduced from Stacks 09Z6 (3) in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.Sets`: `ℱ` embeds in the
free sheaf of `Λ`-modules `Λ[ℱ]`, which is constructible; an embedding of `Λ[ℱ]` into
`⨁ᵢ fᵢ_* M̲ᵢ` gives one of `ℱ` after forgetting the module structure, which commutes with direct
images, carries the finite biproduct to the product and the constant sheaf of modules to the
constant sheaf of sets, and the `Mᵢ` are finite sets since `Λ` is finite. The source also cites
Stacks 0A3U (proper base change for sheaves of sets); Stacks 0959 for finite morphisms is the case
used.

## Main results

* `Stacks.EtaleCohomology.exists_mono_pi_smallEtalePushforward_constantSheaf_of_qcqs` —
  Stacks 09Z7 (1).
* `Stacks.EtaleCohomology.exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf_of_qcqs` —
  Stacks 09Z7 (2).
* `Stacks.EtaleCohomology.exists_mono_biproduct_etaleModuleDirectImage_constantSheaf_of_qcqs` —
  Stacks 09Z7 (3).

## Implementation notes

Constructibility is `Stacks.EtaleCohomology.IsConstructibleEtaleSetSheaf`,
`Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf` and
`Stacks.EtaleCohomology.IsConstructibleEtaleModule`; sheaves of sets take values in
`Type (u + 1)`, abelian sheaves in `AddCommGrpCat.{u + 1}` and the ring `Λ` lives in
`Type (u + 1)`, the universe of Stacks 09Z6 and of the essential-surjectivity assertion of
Stacks 09YU.

## References

* [Stacks Project, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7)
* [Stacks Project, Tag 09Z6](https://stacks.math.columbia.edu/tag/09Z6)
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

attribute [local instance 3000] Abelian.hasFiniteBiproducts

/-- The base change of a finite morphism of finite presentation is again finite and of finite
presentation. -/
private theorem isFinite_and_finitePresentation_pullback_snd {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (π : Z ⟶ X) (hf : IsFinite f) (hfp : FinitePresentation f) :
    IsFinite (pullback.snd f π) ∧ FinitePresentation (pullback.snd f π) :=
  have sq := IsPullback.of_hasPullback f π
  ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq hf,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq hfp.1,
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq hfp.2.1,
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq hfp.2.2⟩

/-- **Stacks Project, Tag 09Z7, part (2).** Let `X` be a quasi-compact and quasi-separated scheme
and `F` a constructible abelian sheaf on `X_étale`. There is an injective map of abelian sheaves
`F ⟶ ⨁ⱼ fⱼ_* Mⱼ` into a finite direct sum, where each `fⱼ : Yⱼ ⟶ X` is finite and of finite
presentation and each `Mⱼ` is a finite abelian group.

The proof descends `F` to a Noetherian stage of an absolute Noetherian approximation of `X`
(Stacks 01ZA, the essential-surjectivity assertion of Stacks 09YU), embeds it there (Stacks 09Z6
(2)), and pulls the embedding back, the inverse image of each finite pushforward being the finite
pushforward along the base change (Stacks 0959). -/
@[stacks 09Z7 "(2)",
  sga "4 IX 2.14" "(ii), special case",
  sga "4 XIV 1.11" "special case",
  sga "4½ Arcata 4.3.2" "(i) ⇒ (ii)"]
theorem exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf_of_qcqs (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    ∃ (J : Type) (_ : Finite J) (Y : J → Scheme.{u}) (f : ∀ j, Y j ⟶ X)
      (_ : ∀ j, IsFinite (f j)) (_ : ∀ j, FinitePresentation (f j))
      (M : J → AddCommGrpCat.{u + 1}) (_ : ∀ j, Finite (M j))
      (m : F ⟶ ⨁ fun j => (etaleAbelianDirectImage.{u, 0} (f j)).obj
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (M j))),
      Mono m := by
  obtain ⟨I, _, _, _, D, c, _, -, -, hnoeth, _, _, ⟨hc⟩, hpt⟩ :=
    exists_isLimit_finiteType_isNoetherian X
  subst hpt
  -- descend `F` to a Noetherian stage and embed it there
  obtain ⟨i, F₀, hF₀, ⟨e⟩⟩ :=
    exists_isConstructibleEtaleAbelianSheaf_etaleAbelianInverseImage_iso D c hc F hF
  have := hnoeth i
  obtain ⟨J, hJ, Y, f, hf, hfp, M, hM, m, hm⟩ :=
    exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf F₀ hF₀
  -- pull the embedding back along `π : X ⟶ X_i`
  let π := c.π.app i
  let L := etaleAbelianInverseImage.{u, 0} π
  have sq : ∀ j, IsPullback (pullback.fst (f j) π) (pullback.snd (f j) π) (f j) π :=
    fun j => IsPullback.of_hasPullback (f j) π
  have hg : ∀ j, IsFinite (pullback.snd (f j) π) := fun j =>
    (isFinite_and_finitePresentation_pullback_snd (f j) π (hf j) (hfp j)).1
  have hgp : ∀ j, FinitePresentation (pullback.snd (f j) π) := fun j =>
    (isFinite_and_finitePresentation_pullback_snd (f j) π (hf j) (hfp j)).2
  -- the inverse image of `fⱼ_* Mⱼ` is `gⱼ_* Mⱼ` (Stacks 0959)
  let β : ∀ j, L.obj ((etaleAbelianDirectImage.{u, 0} (f j)).obj
      ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (M j))) ≅
      (etaleAbelianDirectImage.{u, 0} (pullback.snd (f j) π)).obj
        ((constantSheaf (pullback (f j) π).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (M j)) :=
    fun j =>
      have := isIso_etaleAbelianBaseChange_of_isFinite_unconditional.{u, 0} (f j) π _ _ (sq j)
      asIso ((etaleAbelianBaseChange.{u, 0} (f j) π _ _ (sq j).w).app _) ≪≫
        (etaleAbelianDirectImage.{u, 0} (pullback.snd (f j) π)).mapIso
          ((etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst (f j) π)).app (M j))
  refine ⟨J, hJ, fun j => pullback (f j) π, fun j => pullback.snd (f j) π, hg, hgp, M, hM,
    e.inv ≫ L.map m ≫ (L.mapBiproduct _).hom ≫ (biproduct.mapIso β).hom, ?_⟩
  infer_instance

/-- **Stacks Project, Tag 09Z7, part (3).** Let `X` be a quasi-compact and quasi-separated scheme,
`Λ` a Noetherian ring and `F` a constructible sheaf of `Λ`-modules on `X_étale`. There is an
injective map of sheaves of modules `F ⟶ ⨁ᵢ fᵢ_* M̲ᵢ` into a finite direct sum, where each
`fᵢ : Yᵢ ⟶ X` is finite and of finite presentation and each `Mᵢ` is a finite `Λ`-module.

The proof descends `F` to a Noetherian stage of an absolute Noetherian approximation of `X`
(Stacks 01ZA, the essential-surjectivity assertion of Stacks 09YU), embeds it there (Stacks 09Z6
(3)), and pulls the embedding back, the inverse image of each finite pushforward being the finite
pushforward along the base change (Stacks 0959). The ring `Λ` lives in `Type (u + 1)`, the
universe of Stacks 09Z6 (3). -/
@[stacks 09Z7 "(3)", sga "4 IX 2.14" "(ii), A-modules"]
theorem exists_mono_biproduct_etaleModuleDirectImage_constantSheaf_of_qcqs
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ k, Y k ⟶ X) (_ : ∀ k, IsFinite (f k))
      (_ : ∀ k, FinitePresentation (f k)) (M : Fin n → ModuleCat.{u + 1} Λ)
      (_ : ∀ k, Module.Finite Λ (M k))
      (φ : F ⟶ ⨁ fun k => (etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
        ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k))),
      Mono φ := by
  obtain ⟨I, _, _, _, D, c, _, -, -, hnoeth, _, _, ⟨hc⟩, hpt⟩ :=
    exists_isLimit_finiteType_isNoetherian X
  subst hpt
  -- descend `F` to a Noetherian stage and embed it there
  obtain ⟨i, F₀, hF₀, ⟨e⟩⟩ :=
    exists_isConstructibleEtaleModule_etaleModuleInverseImage_iso Λ D c hc F hF
  have := hnoeth i
  obtain ⟨n, Y, f, hf, hfp, M, hM, m, hm, -, -⟩ :=
    exists_mono_biproduct_etaleModuleDirectImage_constantSheaf_and_nsmul Λ F₀ hF₀
  -- pull the embedding back along `π : X ⟶ X_i`
  let π := c.π.app i
  let L := etaleModuleInverseImage.{u, u + 1} Λ π
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, u + 1} Λ π
  have : L.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  have sq : ∀ k, IsPullback (pullback.fst (f k) π) (pullback.snd (f k) π) (f k) π :=
    fun k => IsPullback.of_hasPullback (f k) π
  have hg : ∀ k, IsFinite (pullback.snd (f k) π) := fun k =>
    (isFinite_and_finitePresentation_pullback_snd (f k) π (hf k) (hfp k)).1
  have hgp : ∀ k, FinitePresentation (pullback.snd (f k) π) := fun k =>
    (isFinite_and_finitePresentation_pullback_snd (f k) π (hf k) (hfp k)).2
  -- the inverse image of `fₖ_* Mₖ` is `gₖ_* Mₖ` (Stacks 0959)
  let β : ∀ k, L.obj ((etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
      ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k))) ≅
      (etaleModuleDirectImage.{u, u + 1} Λ (pullback.snd (f k) π)).obj
        ((constantSheaf (pullback (f k) π).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k)) :=
    fun k =>
      have := hf k
      have := isIso_etaleModuleBaseChange_app_of_isFinite Λ (f k) π _ _ (sq k)
        ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k))
      asIso ((etaleModuleBaseChangeGeneral.{u, u + 1} Λ (f k) π _ _ (sq k).w).app _) ≪≫
        (etaleModuleDirectImage.{u, u + 1} Λ (pullback.snd (f k) π)).mapIso
          ((TorsionModules.etaleModuleInverseImageConstantIso Λ
            (pullback.fst (f k) π)).app (M k))
  refine ⟨n, fun k => pullback (f k) π, fun k => pullback.snd (f k) π, hg, hgp, M, hM,
    e.inv ≫ L.map m ≫ (L.mapBiproduct _).hom ≫ (biproduct.mapIso β).hom, ?_⟩
  infer_instance

/-- **Stacks Project, Tag 09Z7, part (1).** Let `X` be a quasi-compact and quasi-separated scheme
and `F` a constructible sheaf of sets on `X_étale`. There is an injective map of sheaves
`F ⟶ ∏ᵢ fᵢ_* E̲ᵢ` into a finite product, where each `fᵢ : Yᵢ ⟶ X` is finite and of finite
presentation and each `Eᵢ` is a finite set.

As for Stacks 09Z6 (1), the proof goes through part (3) over the finite ring
`Λ = ULift (ZMod 2)`: `F` embeds in the free sheaf of `Λ`-modules `Λ[F]`
(`CategoryTheory.Sheaf.mono_adjunction_free_unit`), which is constructible
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_composeAndSheafify_free`); part (3) embeds
`Λ[F]` in `⨁ᵢ fᵢ_* M̲ᵢ`, and forgetting the module structure carries this to `∏ᵢ fᵢ_* M̲ᵢ` with
the `Mᵢ` finite sets. The sheaves of sets take values in `Type (u + 1)`, the universe of
`AlgebraicGeometry.IsConstructibleSetSheaf`. -/
@[stacks 09Z7 "(1)", sga "4 IX 2.14" "(ii), sheaves of sets"]
theorem exists_mono_pi_smallEtalePushforward_constantSheaf_of_qcqs (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (hF : IsConstructibleEtaleSetSheaf F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ k, Y k ⟶ X) (_ : ∀ k, IsFinite (f k))
      (_ : ∀ k, FinitePresentation (f k)) (E : Fin n → Type (u + 1)) (_ : ∀ k, Finite (E k))
      (φ : F ⟶ ∏ᶜ fun k => (smallEtalePushforward (f k) (Type (u + 1))).obj
        ((constantSheaf (Y k).smallEtaleTopology (Type (u + 1))).obj (E k))),
      Mono φ := by
  let Λ := ULift.{u + 1} (ZMod 2)
  let J := X.smallEtaleTopology
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hφ⟩ :=
    exists_mono_biproduct_etaleModuleDirectImage_constantSheaf_of_qcqs Λ X
      ((Sheaf.composeAndSheafify J (ModuleCat.free Λ)).obj F)
      (isConstructibleEtaleModule_composeAndSheafify_free Λ F hF)
  have hpres : ∀ Z : Scheme.{u},
      Z.smallEtaleTopology.PreservesSheafification (forget (ModuleCat.{u + 1} Λ)) := fun Z =>
    Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat.{u, u + 1, 0} _ Λ
  let Fo : ∀ Z : Scheme.{u},
      EtaleModules.{u, u + 1} Λ Z ⥤ Sheaf Z.smallEtaleTopology (Type (u + 1)) :=
    fun Z => sheafCompose Z.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))
  let G : Fin n → EtaleModules.{u, u + 1} Λ X := fun k =>
    (etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
      ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k))
  let e₁ : (Fo X).obj (⨁ G) ≅ ∏ᶜ fun k => (Fo X).obj (G k) :=
    (Fo X).mapIso (biproduct.isoProduct G) ≪≫ PreservesProduct.iso (Fo X) G
  let e₂ : ∀ k, (Fo X).obj (G k) ≅ (smallEtalePushforward (f k) (Type (u + 1))).obj
      ((constantSheaf (Y k).smallEtaleTopology (Type (u + 1))).obj (M k)) := fun k =>
    have := hpres (Y k)
    (Iso.refl _ : (Fo X).obj (G k) ≅ (smallEtalePushforward (f k) (Type (u + 1))).obj
        ((Fo (Y k)).obj ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (M k)))) ≪≫
      (smallEtalePushforward (f k) (Type (u + 1))).mapIso
        ((constantCommuteCompose (Y k).smallEtaleTopology
          (forget (ModuleCat.{u + 1} Λ))).app (M k))
  have hu : Mono ((Sheaf.adjunction J (ModuleCat.adj Λ)).unit.app F) :=
    have := hpres X
    Sheaf.mono_adjunction_free_unit J Λ F
  have hφ' : Mono ((Fo X).map φ) := Functor.map_mono _ _
  refine ⟨n, Y, f, hf, hfp, fun k => M k, fun k => ?_,
    (Sheaf.adjunction J (ModuleCat.adj Λ)).unit.app F ≫ (Fo X).map φ ≫ e₁.hom ≫
      (Pi.mapIso e₂).hom, ?_⟩
  · have := hM k
    exact Module.finite_of_finite Λ
  · exact mono_comp _ _

end Stacks.EtaleCohomology

end
