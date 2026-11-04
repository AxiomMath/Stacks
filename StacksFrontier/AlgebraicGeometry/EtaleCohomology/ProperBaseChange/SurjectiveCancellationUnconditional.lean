module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransferUnconditional
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliaryUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveInverseImageFaithful
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Triangulated.DimensionShifting

/-!
# SurjectiveCancellationUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation`, stated
as separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u v

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

section Unit

/-- In a commutative square whose upper path is a composite of two monomorphisms, the first
morphism of the lower path is a monomorphism. -/
private lemma mono_of_comp_eq_comp {C : Type*} [Category* C] {W X Y Z : C} {a : W ⟶ X}
    {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) (ha : Mono a) (hb : Mono b) :
    Mono c :=
  have : Mono (c ≫ d) := h ▸ mono_comp a b
  mono_of_mono c d

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **For a surjective morphism of schemes the unit `A ⟶ f_* f⁻¹ A` of the
inverse-image/direct-image adjunction on abelian sheaves of the small étale sites is a
monomorphism.** Composed with the forgetful functor to sheaves of sets, the unit becomes the unit
for sheaves of sets followed by the direct image of an isomorphism
(`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`), and the unit for sheaves of sets is
a monomorphism (`Stacks.EtaleCohomology.mono_smallEtaleUnit_of_surjective`); the forgetful
functor is faithful, so it reflects monomorphisms. -/
public theorem mono_etaleAbelianUnit_of_surjective_univ [Surjective f]
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Mono ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).unit.app A) := by
  have : (forget AddCommGrpCat.{max (u + 1) v}).PreservesLeftKanExtensions
      (smallEtaleBaseChange f).op := by
    intro P
    have hfil : ∀ V : X.Etaleᵒᵖ,
        IsFiltered (CostructuredArrow (smallEtaleBaseChange f).op V) := fun V =>
      IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange f) V.unop)
    have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) v}) :=
      preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
    infer_instance
  have : X.smallEtaleTopology.PreservesSheafification (forget AddCommGrpCat.{max (u + 1) v}) :=
    GrothendieckTopology.preservesSheafification_forget_addCommGrpCat.{max (u + 1) v} _
  have h := coefficientPullbackComparison_unit (smallEtaleBaseChange f) Y.smallEtaleTopology
    X.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) A
  have hS : Mono ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange f) (Type (max (u + 1) v)) Y.smallEtaleTopology
      X.smallEtaleTopology).unit.app
        ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v})).obj A)) :=
    mono_smallEtaleUnit_of_surjective.{v, u} f _
  have hc : IsIso (coefficientPullbackComparison (smallEtaleBaseChange f) Y.smallEtaleTopology
      X.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) A) := by
    rw [← coefficientPullbackTwoSquare_app]
    infer_instance
  exact (sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v})).mono_of_mono_map
    (mono_of_comp_eq_comp h hS (by infer_instance))

end Unit

section Embedding

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A sheaf on `Y_étale` killed by `n` embeds in the direct image of an injective sheaf of
`ℤ/nℤ`-modules on `X_étale`, when `f : X ⟶ Y` is surjective.** The unit `A ⟶ f_* f⁻¹ A` is a
monomorphism (`Stacks.EtaleCohomology.mono_etaleAbelianUnit_of_surjective_univ`); `f⁻¹ A` is
killed by `n`, so it is the underlying sheaf of a sheaf of `ℤ/nℤ`-modules
(`Stacks.Cohomology.ZModSheaf.torsionSheafToModules`), which embeds in an injective one; and
`f_*` preserves monomorphisms, being a right adjoint. -/
public theorem exists_mono_etaleAbelianDirectImage_toSheaf_injective [Surjective f] (n : ℕ)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (hA : n • 𝟙 A = 0) :
    ∃ (J : SheafOfModules.{max (u + 1) v}
        (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) (_ : Injective J)
      (i : A ⟶ (etaleAbelianDirectImage.{u, v} f).obj ((SheafOfModules.toSheaf _).obj J)),
      Mono i := by
  set A' := (etaleAbelianInverseImage.{u, v} f).obj A
  obtain ⟨J, hJ, i, hi⟩ := exists_mono_toSheaf_injective_univ.{u, v} n A'
    (nsmul_id_map_eq_zero (etaleAbelianInverseImage.{u, v} f) hA)
  refine ⟨J, hJ, (etaleAbelianInverseImageDirectImageAdj.{u, v} f).unit.app A ≫
      (etaleAbelianDirectImage.{u, v} f).map i, ?_⟩
  have := mono_etaleAbelianUnit_of_surjective_univ.{u, v} f A
  have : PreservesLimitsOfSize.{0, 0} (etaleAbelianDirectImage.{u, v} f) :=
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f).rightAdjoint_preservesLimits
  infer_instance

end Embedding

/-- Cancelling three invertible factors from a fourfold composite. -/
private alias isIso_of_comp_four_eq_general := isIso_of_comp_four_eq

section DirectImage

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The base change map of `g` is invertible at the direct image along `f` of an injective
sheaf of `ℤ/nℤ`-modules**, `n > 0`, when cohomology commutes with base change for `f` and for
`g ∘ f`. The underlying sheaf `J` is torsion and acyclic for the direct image, so `Rf_* J` is
`f_* J` in degree zero; by the composition formula
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_compDirectImage_app` the base change map of
`g ∘ f` at `J` is the base change map of `g` at `Rf_* J` between two invertible factors, and it is
invertible, as is the base change map of `f` at `J`. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_directImage_toSheaf
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (hgf : CohomologyCommutesWithBaseChange.{u, v} (f ≫ g))
    {Y' Z' : Scheme.{u}} (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (sq : IsPullback d g' g c)
    {n : ℕ} (hn : 0 < n)
    (J : SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) [Injective J] :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} g c d g' sq.w
      ((etaleAbelianDirectImage.{u, v} f).obj ((SheafOfModules.toSheaf _).obj J))) := by
  have t := IsPullback.of_hasPullback f d
  have s := t.paste_vert sq
  obtain ⟨φ⟩ := nonempty_singleFunctor_iso_etaleAbelianDerivedDirectImage.{u, v} f
    ((SheafOfModules.toSheaf _).obj J)
    (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, v} f n J)
  have hJ := torsionSheafProperty_toSheaf_zmod hn J
  have h₂ := hf d (pullback.fst f d) (pullback.snd f d) t _ hJ
  have h₁ := hgf c (pullback.fst f d) (pullback.snd f d ≫ g') s _ hJ
  unfold etaleAbelianSheafDerivedBaseChange at h₁ h₂ ⊢
  rw [etaleAbelianDerivedBaseChange_compDirectImage_app.{u, v} f g (f ≫ g) rfl c d g'
    (pullback.fst f d) (pullback.snd f d) _ rfl sq.w t.w s.w] at h₁
  exact (NatTrans.isIso_app_iff_of_iso _ φ).mpr (isIso_of_comp_four_eq_general _ _ _ _ _ rfl
    inferInstance inferInstance inferInstance h₁)

end DirectImage

section Bounded

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The base change map of `g` is invertible at every sheaf killed by a positive integer `n`**,
when `f` is surjective and cohomology commutes with base change for `f` and for `g ∘ f`. The
sheaves killed by `n`, placed in degree zero, form a class to which dimension shifting
(`Stacks.Triangulated.isIso_app_of_dimensionShifting`) applies: each embeds in a direct image
along `f` of an injective sheaf of `ℤ/nℤ`-modules
(`Stacks.EtaleCohomology.exists_mono_etaleAbelianDirectImage_toSheaf_injective`), at which the
base change map is invertible
(`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_directImage_toSheaf`), with a
cokernel again killed by `n`. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_comp_of_nsmul_id_eq_zero [Surjective f]
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (hgf : CohomologyCommutesWithBaseChange.{u, v} (f ≫ g))
    {Y' Z' : Scheme.{u}} (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (sq : IsPullback d g' g c)
    (n : ℕ) (hn : 0 < n) (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hA : n • 𝟙 A = 0) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} g c d g' sq.w A) := by
  refine Stacks.Triangulated.isIso_app_of_dimensionShifting
    (etaleAbelianDerivedBaseChange.{u, v} g c d g' sq.w)
    (fun K ↦ ∃ A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      n • 𝟙 A = 0 ∧ K = (DerivedCategory.singleFunctor _ 0).obj A) ?_ ?_ _ ⟨A, hA, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨J, hJ, i, hi⟩ := exists_mono_etaleAbelianDirectImage_toSheaf_injective.{u, v} f n A hA
    have hS := ShortComplex.ShortExact.mk' (S := ShortComplex.mk i (cokernel.π i)
      (cokernel.condition i)) (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i))
      hi inferInstance
    refine ⟨_, _, _, _, _, hS.singleTriangle_distinguished, ?_, cokernel i, ?_, rfl⟩
    · exact isIso_etaleAbelianSheafDerivedBaseChange_directImage_toSheaf.{u, v} f g hf hgf c d
        g' sq hn J
    · exact Stacks.ConstantSheaf.nsmul_id_zero_of_epi (cokernel.π i) n
        (nsmul_id_map_eq_zero (etaleAbelianDirectImage.{u, v} f) (nsmul_id_toSheaf_eq_zero n J))
  · rintro _ ⟨A, -, rfl⟩ q hq
    exact isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg g c d g' sq.w A q hq

end Bounded

section Main

variable {X Y Z : Scheme.{u}}

/-- **[Stacks, Tag 0A4C]: cancelling a surjection from a composite.** Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes. Assume

1. cohomology commutes with base change for `f`,
2. cohomology commutes with base change for `g ∘ f`, and
3. `f` is surjective.

Then cohomology commutes with base change for `g`.

The source assumes `f` and `g` proper; only surjectivity of `f` and quasi-compactness and
quasi-separatedness of `g` are used, so the statement is proved under those weaker hypotheses (a
proper morphism is quasi-compact and quasi-separated). Cohomology commuting with base change is
`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange`: the derived base change map
`c⁻¹ Rg_* F ⟶ Rg'_* d⁻¹ F` is an isomorphism for every cartesian square and every torsion abelian
sheaf `F`, in all degrees at once. -/
@[stacks 0A4C]
public theorem CohomologyCommutesWithBaseChange.of_comp_of_surjective (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [QuasiCompact g] [QuasiSeparated g]
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (hgf : CohomologyCommutesWithBaseChange.{u, v} (f ≫ g)) :
    CohomologyCommutesWithBaseChange.{u, v} g := by
  intro Y' Z' c d g' sq F hF
  exact isIso_etaleAbelianSheafDerivedBaseChange_of_torsionSheafProperty_of_isPullback g c d g'
    sq (fun n hn A hA ↦
      isIso_etaleAbelianSheafDerivedBaseChange_of_comp_of_nsmul_id_eq_zero.{u, v} f g hf hgf c d
        g' sq n hn A hA) F hF

end Main

end Stacks.EtaleCohomology

end
