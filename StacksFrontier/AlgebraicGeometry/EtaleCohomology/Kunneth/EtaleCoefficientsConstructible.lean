module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.IntegralPushforwardSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapDimensionShifting
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitAtTerminal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.SiteCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePushforwardModuleEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.MainstreamTransportDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentationPushforwardModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreFirstCohomologyInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible sheaves of `𝔽_ℓ`-modules on `D(X_étale, 𝔽_ℓ)`, and [Stacks, Tag 09Z7] (3) there

The derived categories `D(X_étale, Λ)` of `Stacks.EtaleCohomology.EtaleCoefficients` are built
from sheaves of modules over the constant sheaf of rings `Λ̲` on the small model of `X_étale`,
while constructibility (Stacks 03RW), its colimit presentations (Stacks 03SA) and the embedding of
Stacks 09Z7 into finite direct images live on the bounded small étale site of Stacks 021B of a big
étale site containing `X`. For `Λ = 𝔽_ℓ = ℤ/ℓ` the two meet on Mathlib's small étale site, through
the underlying abelian sheaves: `Stacks.EtaleCohomology.EtaleCoefficients.etaleToSheaf` is fully
faithful onto the abelian sheaves killed by `ℓ`, and
`AlgebraicGeometry.SmallEtale.moduleSheafToEtale` carries sheaves of `𝔽_ℓ`-modules on the bounded
site there.

This file

* identifies the underlying abelian sheaf of the structure sheaf `Λ̲` with the constant sheaf
  `ℤ/ℓ` (`etaleToSheafUnitIso`): both the structure sheaf and the sheaf of modules underlying the
  constant sheaf corepresent global sections;
* defines **constructible sheaves of `𝔽_ℓ`-modules** on the model
  (`IsConstructibleEtaleModule`): those whose underlying abelian sheaf is the transport of a
  constructible sheaf of `𝔽_ℓ`-modules on the bounded site;
* proves **[Stacks, Tag 09Z7] (3) on the model**, in the form the dimension shifting of the proof
  of [Stacks, Tag 0F1J] consumes (`exists_shortExact_of_isConstructibleEtaleModule`): over a
  quasi-compact quasi-separated `X`, every constructible `M` sits in a short exact sequence
  `0 → M → I → Q → 0` with `Q` constructible and `I[0] ≅ ⨁ₖ Rπₖ_*𝔽_ℓ̲` for finitely many finite
  `πₖ`. The embedding is Stacks 09Z7 (3) on the bounded site, its target a finite sum of
  `f_*M̲` with `M` a finite `𝔽_ℓ`-vector space, hence a finite sum of `f_*𝔽_ℓ̲`; the cokernel is
  constructible by Stacks 095R and 03RZ;
* proves that **every sheaf of `𝔽_ℓ`-modules on a quasi-compact quasi-separated `X` is a filtered
  colimit of constructible ones** (`exists_isColimit_isConstructibleEtaleModule`, Stacks 03SA (3)
  in the unconditional form
  `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs`,
  transported).

## References

* [Stacks Project, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7)
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` and `derivedPushforward` (`StacksFrontier/CategoryTheory/Sites/Cohomology/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`), through `pushforward`, are stated for
-- the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

-- The constructibility development imports `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing)

/-! ### The structure sheaf is the constant sheaf `ℤ/ℓ` -/

section Unit

variable (ℓ : ℕ) [NeZero ℓ] (Z : Scheme.{u})

/-- The additive map `ℤ/ℓ ⟶ G` sending `1` to `x`, for `x` killed by `ℓ`. -/
def zmodHomOfNsmulEqZero (G : AddCommGrpCat.{u + 1}) (x : G) (hx : ℓ • x = 0) :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)) ⟶ G :=
  AddCommGrpCat.ofHom (((ZMod.lift ℓ ⟨zmultiplesHom G x, by simp [hx]⟩)).comp
    (AddEquiv.ulift.toAddMonoidHom))

/-- The map `zmodHomOfNsmulEqZero ℓ G x hx` sends the class of an integer `k` to `k • x`. -/
theorem zmodHomOfNsmulEqZero_apply (G : AddCommGrpCat.{u + 1}) (x : G) (hx : ℓ • x = 0)
    (k : ℤ) : (zmodHomOfNsmulEqZero ℓ G x hx).hom (ULift.up (k : ZMod ℓ)) = k • x := by
  show (ZMod.lift ℓ ⟨zmultiplesHom G x, by simp [hx]⟩) (k : ZMod ℓ) = k • x
  rw [ZMod.lift_coe]
  rfl

/-- An additive map out of `ℤ/ℓ` into an abelian group killed by `ℓ` is its value at `1`. -/
def zmodHomEquivOfNsmulEqZero (G : AddCommGrpCat.{u + 1}) (hG : ∀ x : G, ℓ • x = 0) :
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)) ⟶ G) ≃ G where
  toFun f := f.hom (1 : ULift.{u + 1} (ZMod ℓ))
  invFun x := zmodHomOfNsmulEqZero ℓ G x (hG x)
  left_inv f := by
    ext ⟨a⟩
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    have hk : (ULift.up (k : ZMod ℓ) : ULift.{u + 1} (ZMod ℓ)) =
        k • (1 : ULift.{u + 1} (ZMod ℓ)) := by
      ext
      simp
    rw [zmodHomOfNsmulEqZero_apply, hk, map_zsmul]
  right_inv x := by
    have h1 : (1 : ULift.{u + 1} (ZMod ℓ)) = ULift.up ((1 : ℤ) : ZMod ℓ) := by
      ext
      simp
    change (zmodHomOfNsmulEqZero ℓ G x (hG x)).hom (1 : ULift.{u + 1} (ZMod ℓ)) = x
    rw [h1, zmodHomOfNsmulEqZero_apply, one_zsmul]

/-- The constant abelian sheaf `ℤ/ℓ` on `Z_étale`. -/
@[sga "7 XXII 2.0"]
abbrev constantZMod : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))

/-- `Z` itself, as a terminal object of its small étale site. -/
abbrev etaleTerminal : Z.Etale := Scheme.Etale.mk (𝟙 Z)

/-- `Z` itself is terminal in its small étale site. -/
def etaleTerminalIsTerminal : IsTerminal (etaleTerminal Z) := by
  have hci : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  exact MorphismProperty.Over.mkIdTerminal _ _

/-- The constant sheaf functor into abelian sheaves on `Z_étale` is additive. -/
private theorem additive_constantSheaf_addCommGrpCat :
    (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The constant sheaf on `ℤ/ℓ` is killed by `ℓ`. -/
theorem nsmul_id_constantZMod_eq_zero : ℓ • 𝟙 (constantZMod ℓ Z) = 0 := by
  let C := constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : C.Additive := additive_constantSheaf_addCommGrpCat Z
  have h : ℓ • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) = 0 := by
    ext ⟨a⟩
    simp
  exact nsmul_id_map_eq_zero ℓ C h

/-- The constant sheaf on `ℤ/ℓ` underlies a sheaf of `ℤ/ℓ̲`-modules. -/
theorem constantZMod_mem_essImage :
    (etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) Z).essImage (constantZMod ℓ Z) :=
  (mem_essImage_etaleToSheaf_iff ℓ Z _).2 (nsmul_id_constantZMod_eq_zero ℓ Z)

/-- **The sheaf of `ℤ/ℓ̲`-modules underlying the constant sheaf `ℤ/ℓ` corepresents global
sections**, as the structure sheaf does: maps out of it are maps out of the constant sheaf of the
underlying abelian sheaves, i.e. additive maps `ℤ/ℓ ⟶ Γ(Z, -)`, i.e. global sections, the
underlying abelian sheaves being killed by `ℓ`. -/
def corepresentableByConstantZMod :
    (_root_.SheafOfModules.evaluation (etaleRing (ULift.{u + 1} (ZMod ℓ)) Z) (op (terminal Z)) ⋙
        forget _).CorepresentableBy (constantZMod_mem_essImage ℓ Z).witness where
  homEquiv {M} := (etaleToSheafZModFullyFaithful ℓ Z).homEquiv.trans
    ((Iso.homCongr (constantZMod_mem_essImage ℓ Z).getIso (Iso.refl _)).trans
      (((constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}
        (etaleTerminalIsTerminal Z)).homEquiv _ _).trans
        (zmodHomEquivOfNsmulEqZero ℓ _ fun x =>
          (nsmul_id_eq_zero_iff ℓ _).1 ((mem_essImage_etaleToSheaf_iff ℓ Z _).1
            ((etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) Z).obj_mem_essImage M)) _ x)))
  homEquiv_comp {M M'} g f := by
    simp only [Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply, Functor.map_comp,
      Iso.homCongr_apply, Iso.refl_hom, Category.comp_id, Category.assoc,
      Adjunction.homEquiv_naturality_right]
    rfl

/-- **The underlying abelian sheaf of the structure sheaf of `(Z_étale, ℤ/ℓ)` is the constant
sheaf `ℤ/ℓ`.** Both the structure sheaf and the sheaf of modules underlying the constant sheaf
corepresent global sections (`Stacks.Sites.ExtensionByZero.corepresentableByUnit`,
`corepresentableByConstantZMod`). -/
def etaleToSheafUnitIso :
    (etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) Z).obj (_root_.SheafOfModules.unit _) ≅
      constantZMod ℓ Z :=
  (etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) Z).mapIso
      ((Stacks.Sites.ExtensionByZero.corepresentableByUnit _ (terminal Z)
        (terminalIsTerminal Z)).uniqueUpToIso (corepresentableByConstantZMod ℓ Z)) ≪≫
    (constantZMod_mem_essImage ℓ Z).getIso

end Unit

/-! ### Constructible sheaves of `𝔽_ℓ`-modules on the model -/

section Constructible

attribute [local instance 3000] Abelian.hasFiniteBiproducts

variable (ℓ : ℕ) [NeZero ℓ] (X : Scheme.{u})

/-- `ULift (ZMod ℓ)` is Noetherian for `ℓ > 0`, being finite. -/
instance isNoetherianRing_uliftZModEtale : IsNoetherianRing (ULift.{u + 1} (ZMod ℓ)) :=
  isNoetherianRing_of_ringEquiv (ZMod ℓ) ULift.ringEquiv.symm

/-- The big étale site of Stacks 021B on which constructibility on `X` is read. -/
abbrev constructibilitySite : BigEtaleSite.{u} := BigEtaleSite.containing X

/-- `X` as an object of `constructibilitySite X`. -/
abbrev constructibilityScheme : (constructibilitySite X).Scheme :=
  (constructibilitySite X).obj X (BigEtaleSite.contains_containing X)

/-- **A constructible sheaf of `ℤ/ℓ̲`-modules on `X_étale`** (Stacks 03RW (3) for `Λ = ℤ/ℓ`), on
the model of `D(X_étale, ℤ/ℓ)`: its underlying abelian sheaf is the transport to Mathlib's small
étale site (`AlgebraicGeometry.SmallEtale.moduleSheafToEtale`) of a constructible sheaf of
`ℤ/ℓ`-modules on the bounded small étale site of `X`. -/
def IsConstructibleEtaleModule
    (M : SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod ℓ)) X)) : Prop :=
  ∃ G : Sheaf (SmallEtale.topology (constructibilitySite X) (constructibilityScheme X).obj
      (constructibilityScheme X).property) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))),
    IsConstructibleModuleSheaf (constructibilitySite X) (constructibilityScheme X)
      (ULift.{u + 1} (ZMod ℓ)) G ∧
    Nonempty ((SmallEtale.moduleSheafToEtale (constructibilitySite X) (constructibilityScheme X)
      (ULift.{u + 1} (ZMod ℓ))).obj G ≅ (etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) X).obj M)

/-- `X` as an object of the constructibility site is quasi-compact if `X` is. -/
private instance compactSpace_constructibilityScheme [CompactSpace X] :
    CompactSpace (constructibilityScheme X).obj := ‹CompactSpace X›

/-- `X` as an object of the constructibility site is quasi-separated if `X` is. -/
private instance quasiSeparatedSpace_constructibilityScheme [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace (constructibilityScheme X).obj := ‹QuasiSeparatedSpace X›

/-- Constructibility on the model is invariant under isomorphism. -/
theorem IsConstructibleEtaleModule.of_iso {M N : SheafOfModules.{u + 1}
    (etaleRing (ULift.{u + 1} (ZMod ℓ)) X)} (e : M ≅ N) (hM : IsConstructibleEtaleModule ℓ X M) :
    IsConstructibleEtaleModule ℓ X N := by
  obtain ⟨G, hG, ⟨eG⟩⟩ := hM
  exact ⟨G, hG, ⟨eG ≪≫ (etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) X).mapIso e⟩⟩

end Constructible

/-! ### Stacks 09Z7 (3) on the model -/

section Embedding

attribute [local instance 3000] Abelian.hasFiniteBiproducts


variable (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}

/-- A prime `ℓ` is nonzero. -/
instance neZero_of_fact_prime : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

/-- A finite `ℤ/ℓ`-module, `ℓ` prime, is a finite sum of copies of `ℤ/ℓ`, as an abelian group. -/
theorem exists_iso_biproduct_of_finite (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    [Module.Finite (ULift.{u + 1} (ZMod ℓ)) M] :
    ∃ r : ℕ, Nonempty ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat).obj M ≅
      ⨁ fun _ : Fin r => AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) := by
  refine ⟨Module.finrank (ULift.{u + 1} (ZMod ℓ)) M, ⟨?_⟩⟩
  let e : M ≅ ⨁ fun _ : Fin (Module.finrank (ULift.{u + 1} (ZMod ℓ)) M) =>
      ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ)) :=
    (Module.finBasis (ULift.{u + 1} (ZMod ℓ)) M).equivFun.toModuleIso ≪≫
      (ModuleCat.biproductIsoPi (fun _ : Fin (Module.finrank (ULift.{u + 1} (ZMod ℓ)) M) =>
        ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ)))).symm
  exact (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat).mapIso e ≪≫
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat).mapBiproduct _

/-- **[Stacks, Tag 09Z7] (3) on `D(X_étale, ℤ/ℓ)`, in the form of the dimension shifting of
[Stacks, Tag 0F1J].** Let `X` be quasi-compact and quasi-separated, `ℓ` a prime and `M` a
constructible sheaf of `ℤ/ℓ̲`-modules on `X_étale`. Then there is a short exact sequence
`0 → M → I → Q → 0` with `Q` constructible and `I[0] ≅ ⨁ₖ Rπₖ_*(ℤ/ℓ̲)` for finitely many finite
morphisms `πₖ : Zₖ ⟶ X`.

The embedding `M ↪ ⨁ f_{k,*}M̲_k` of Stacks 09Z7 (3) on the bounded site has `M_k` a finite
`ℤ/ℓ`-vector space, hence a finite sum of copies of `ℤ/ℓ`, so its target is a finite sum of
`f_*(ℤ/ℓ̲)`; on Mathlib's small étale site that is `⨁ π_*` of the underlying abelian sheaf of the
structure sheaf (`etaleToSheafUnitIso`), which pulls the embedding back to the model. Its cokernel
is the transport of the cokernel on the bounded site, which is constructible by Stacks 095R and
Stacks 03RZ. A direct image along a finite morphism of a sheaf in degree zero is its derived
direct image (`nonempty_singleFunctor_pushforwardTopos_iso`). -/
@[sga "4½ Arcata 4.3.2" "(i) ⇒ (ii)"]
theorem exists_shortExact_of_isConstructibleEtaleModule [CompactSpace X] [QuasiSeparatedSpace X]
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O)) (hM : IsConstructibleEtaleModule ℓ X M) :
    ∃ (S : ShortComplex (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O)))
      (_ : S.ShortExact) (_ : S.X₁ ≅ M), IsConstructibleEtaleModule ℓ X S.X₃ ∧
        ∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (π : ∀ k, Z k ⟶ X) (_ : ∀ k, IsFinite (π k)),
          Nonempty ((DerivedCategory.singleFunctor _ 0).obj S.X₂ ≅
            ⨁ fun k => (pushforward (ULift.{u + 1} (ZMod ℓ)) (π k)).obj
              (unit (ULift.{u + 1} (ZMod ℓ)) (Z k))) := by
  classical
  have hsh : ∀ T : (constructibilitySite X).Scheme,
      HasSheafify (SmallEtale.topology (constructibilitySite X) T.obj T.property)
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) := fun T =>
    SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} _ T _
  obtain ⟨G, hG, ⟨eG⟩⟩ := hM
  obtain ⟨n, Y, f, hf, hfp, Mk, hMk, φ, hφ⟩ :=
    AlgebraicGeometry.exists_mono_biproduct_pushforward_constantSheaf_of_isConstructibleModuleSheaf
      (constructibilitySite X) (ULift.{u + 1} (ZMod ℓ)) (constructibilityScheme X) G hG
  have hcont : ∀ k, (AlgebraicGeometry.smallEtaleBaseChange (constructibilitySite X)
      (f k)).IsContinuous
      (SmallEtale.topology (constructibilitySite X) (constructibilityScheme X).obj
        (constructibilityScheme X).property)
      (SmallEtale.topology (constructibilitySite X) (Y k).obj (Y k).property) := fun k =>
    AlgebraicGeometry.smallEtaleBaseChange_isContinuous _ (f k)
  let T := SmallEtale.moduleSheafToEtale (constructibilitySite X) (constructibilityScheme X)
    (ULift.{u + 1} (ZMod ℓ))
  let F := etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) X
  have h₁ : PreservesColimitsOfSize.{u + 1, u + 1} T :=
    SmallEtale.moduleSheafToEtale_preservesColimits (constructibilitySite X)
      (constructibilityScheme X) (ULift.{u + 1} (ZMod ℓ))
  have : PreservesColimitsOfSize.{0, 0} T := preservesColimitsOfSize_shrink T
  have : T.IsLeftAdjoint := SmallEtale.moduleSheafToEtale_isLeftAdjoint (constructibilitySite X)
    (constructibilityScheme X) (ULift.{u + 1} (ZMod ℓ))
  have : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint T
  have hTb : ∀ G' : Fin n → Sheaf (SmallEtale.topology (constructibilitySite X)
      (constructibilityScheme X).obj (constructibilityScheme X).property)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))), PreservesBiproduct G' T := fun G' =>
    preservesBiproduct_of_preservesCoproduct T
  have hr : ∀ k, ∃ r : ℕ, Nonempty ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      AddCommGrpCat).obj (Mk k) ≅
      ⨁ fun _ : Fin r => AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) := fun k => by
    have := hMk k
    exact exists_iso_biproduct_of_finite ℓ (Mk k)
  choose r er using hr
  -- the target, on Mathlib's small étale site
  let ι := Σ k : Fin n, Fin (r k)
  let π : ∀ p : ι, (Y p.1).obj ⟶ X := fun p => (constructibilitySite X).inclusion.map (f p.1)
  have hπ : ∀ p : ι, IsFinite (π p) := fun p => hf p.1
  let D : ∀ k, Sheaf (Y k).obj.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun k =>
    Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0}
      ((constructibilitySite X).inclusion.map (f k))
  let C : ∀ k, AddCommGrpCat.{u + 1} ⥤ Sheaf (Y k).obj.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    fun k => constantSheaf (Y k).obj.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hC : ∀ k, (C k).Additive := fun k => additive_constantSheaf_addCommGrpCat (Y k).obj
  have hD : ∀ k, (D k).Additive := fun k => by
    have : (D k).IsRightAdjoint :=
      (Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, 0}
        ((constructibilitySite X).inclusion.map (f k))).isRightAdjoint
    have := preservesBinaryBiproducts_of_preservesBinaryProducts (D k)
    exact Functor.additive_of_preservesBinaryBiproducts _
  let I : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O) :=
    ⨁ fun p : ι => (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) (π p)).pushforwardTopos.obj
      (SheafOfModules.unit _)
  let E :=
    T.mapBiproduct _ ≪≫
      biproduct.mapIso (fun k => SmallEtale.moduleSheafToEtaleDirectImageConstantIso
        (constructibilitySite X) (ULift.{u + 1} (ZMod ℓ)) (f k) (Mk k)) ≪≫
      biproduct.mapIso (fun k => (C k ⋙ D k).mapIso (er k).some ≪≫
        (C k ⋙ D k).mapBiproduct _) ≪≫
      biproductBiproductIso _ _ ≪≫
      biproduct.mapIso (fun p : ι => (D p.1).mapIso (etaleToSheafUnitIso ℓ (Y p.1).obj).symm ≪≫
        ((pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod ℓ)) (π p)).app _).symm) ≪≫
      (F.mapBiproduct _).symm
  -- the embedding on the model
  let hF := etaleToSheafZModFullyFaithful ℓ X
  let ψ : M ⟶ I := hF.preimage (eG.inv ≫ T.map φ ≫ E.hom)
  have hψ : F.map ψ = eG.inv ≫ T.map φ ≫ E.hom := hF.map_preimage _
  have : Mono (T.map φ) := mono_moduleSheafToEtale_map (constructibilitySite X)
    (constructibilityScheme X) (ULift.{u + 1} (ZMod ℓ)) φ
  have hψm : Mono ψ := by
    have : Mono (F.map ψ) := by
      rw [hψ]
      infer_instance
    exact F.mono_of_mono_map this
  let S := ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel ψ)
      mono_f := hψm
      epi_g := inferInstanceAs (Epi (cokernel.π ψ)) }
  refine ⟨S, hS, Iso.refl _, ?_, ?_⟩
  · -- the cokernel is constructible
    have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1}
      (constructibilitySite X) (constructibilityScheme X) (ULift.{u + 1} (ZMod ℓ))
    have hconst : ∀ k, IsConstructibleModuleSheaf (constructibilitySite X) (Y k)
        (ULift.{u + 1} (ZMod ℓ))
        ((constantSheaf (SmallEtale.topology (constructibilitySite X) (Y k).obj (Y k).property)
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj (Mk k)) := fun k => by
      have : LocallyOfFinitePresentation ((constructibilitySite X).inclusion.map (f k)) :=
        (hfp k).1
      exact isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant (constructibilitySite X)
        (Y k) _ _ (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_constant.{u,
          u + 1, u + 1} _ _ (hMk k) (Iso.refl _))
    have hpush : ∀ k, IsConstructibleModuleSheaf (constructibilitySite X)
        (constructibilityScheme X) (ULift.{u + 1} (ZMod ℓ))
        (((constructibilitySite X).smallPushforward (f k)
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          ((constantSheaf (SmallEtale.topology (constructibilitySite X) (Y k).obj (Y k).property)
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj (Mk k))) := fun k => by
      have := hf k
      exact isConstructibleModuleSheaf_pushforward_of_isFinite_of_finitePresentation _ _ (f k)
        (hfp k) _ (hconst k)
    have := ObjectProperty.isClosedUnderFiniteProducts_of_isWeakSerreClass
      (fun F' : Sheaf (SmallEtale.topology (constructibilitySite X)
        (constructibilityScheme X).obj (constructibilityScheme X).property)
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) =>
          IsConstructibleModuleSheaf (constructibilitySite X) (constructibilityScheme X)
            (ULift.{u + 1} (ZMod ℓ)) F')
    have hI := ObjectProperty.prop_of_iso _ (biproduct.isoProduct _).symm
      (ObjectProperty.prop_product _ (fun k => hpush k))
    refine ⟨cokernel φ, ObjectProperty.prop_cokernel _ φ hG hI, ⟨?_⟩⟩
    exact PreservesCokernel.iso T φ ≪≫
      cokernel.mapIso (T.map φ) (F.map ψ) eG E (by rw [hψ]; simp) ≪≫
      (PreservesCokernel.iso F ψ).symm
  · -- the middle term in degree zero is a finite sum of derived finite direct images of `ℤ/ℓ̲`
    let eqv := Fintype.equivFin ι
    have : ∀ p : ι, IsIntegralHom (π p) := fun p => by
      have := hπ p
      infer_instance
    refine ⟨Fintype.card ι, fun i => (Y (eqv.symm i).1).obj, fun i => π (eqv.symm i),
      fun i => hπ _, ⟨?_⟩⟩
    exact (DerivedCategory.singleFunctor _ 0).mapBiproduct _ ≪≫
      biproduct.mapIso (fun p => (nonempty_singleFunctor_pushforwardTopos_iso ℓ (π p)
        (SheafOfModules.unit _)).some) ≪≫
      biproduct.whiskerEquiv eqv (fun p => eqToIso (congrArg (fun q : ι =>
        (pushforward (ULift.{u + 1} (ZMod ℓ)) (π q)).obj
          (unit (ULift.{u + 1} (ZMod ℓ)) (Y q.1).obj)) (eqv.symm_apply_apply p)))

end Embedding

/-! ### Sheaves of `ℤ/ℓ̲`-modules as filtered colimits of constructible ones -/

section Colimit

variable (ℓ : ℕ) [NeZero ℓ] {X : Scheme.{u}}

/-- **[Stacks, Tag 03SA] (3) on `D(X_étale, ℤ/ℓ)`.** Over a quasi-compact quasi-separated `X`,
every sheaf of `ℤ/ℓ̲`-modules on `X_étale` is the colimit of a filtered diagram of constructible
ones. Its underlying abelian sheaf, killed by `ℓ`, is a filtered colimit of transports of
constructible sheaves of `ℤ/ℓ`-modules on the bounded site
(`AlgebraicGeometry.SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible`); those lie in
the essential image of the fully faithful `etaleToSheaf`, which reflects colimits. -/
theorem exists_isColimit_isConstructibleEtaleModule [CompactSpace X] [QuasiSeparatedSpace X]
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O)) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O))
      (ι : D ⟶ (Functor.const I).obj M), Nonempty (IsColimit (Cocone.mk M ι)) ∧
        ∀ i, IsConstructibleEtaleModule ℓ X (D.obj i) := by
  have := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} (constructibilitySite X)
    (constructibilityScheme X) (ULift.{u + 1} (ZMod ℓ))
  let F := etaleToSheaf (ULift.{u + 1} (ZMod ℓ)) X
  let T := SmallEtale.moduleSheafToEtale (constructibilitySite X) (constructibilityScheme X)
    (ULift.{u + 1} (ZMod ℓ))
  have hM : ((ℓ : ℤ) • 𝟙 (F.obj M)) = 0 := by
    rw [natCast_zsmul]
    exact (mem_essImage_etaleToSheaf_iff ℓ X _).1 (F.obj_mem_essImage M)
  obtain ⟨I, _, _, D₀, ι₀, ⟨hc⟩, hD⟩ :=
    SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible (constructibilitySite X)
      (constructibilityScheme X) ℓ (F.obj M) hM
  have hG : ∀ i, F.essImage ((D₀ ⋙ T).obj i) := fun i => by
    refine (mem_essImage_etaleToSheaf_iff ℓ X _).2 ?_
    refine (nsmul_id_eq_zero_iff ℓ _).2 fun U x => ?_
    exact nsmul_moduleSheafToEtale_eq_zero (constructibilitySite X) (constructibilityScheme X) ℓ
      (D₀.obj i) U x
  let D := Functor.essImage.liftFunctor (D₀ ⋙ T) F hG
  let α := Functor.essImage.liftFunctorCompIso (D₀ ⋙ T) F hG
  let hF := etaleToSheafZModFullyFaithful ℓ X
  let ι : D ⟶ (Functor.const I).obj M :=
    { app := fun i => hF.preimage ((α.hom ≫ ι₀).app i)
      naturality := fun i j g => hF.map_injective (by
        simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage, Functor.const_obj_map,
          Category.comp_id, Functor.const_obj_obj]
        exact (α.hom ≫ ι₀).naturality g |>.trans (Category.comp_id _)) }
  refine ⟨I, inferInstance, inferInstance, D, ι, ⟨?_⟩, fun i =>
    ⟨D₀.obj i, hD i, ⟨(α.app i).symm⟩⟩⟩
  refine isColimitOfReflects F (IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv α _).symm hc) (Cocone.ext (Iso.refl _) fun i => ?_))
  simp [ι]

end Colimit

end Stacks.EtaleCohomology.EtaleCoefficients

end
