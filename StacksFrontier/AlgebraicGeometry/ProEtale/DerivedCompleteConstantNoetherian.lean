module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantNoetherianCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantQuotient
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicCompletionCriterion
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteInverseLimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteWeakSerre
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.DerivedProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TowerOfShortExactSequences
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.AdicQuotientsBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.AdicQuotientsTorAmplitude
import StacksCore.Tactic.StacksAttribute

/-!
# Derived completion on a site with enough weakly contractible objects

Let `𝒞` be a site with enough weakly contractible objects, let `Λ` be a Noetherian ring and let
`I ⊂ Λ` be an ideal. Derived completeness of objects of `D(𝒞, Λ)` along `I` — the derived
category of sheaves of modules over the constant sheaf of rings `Λ̲`, complete along the sheaf of
ideals `IΛ̲` — behaves as it does over a ring, because sections over a weakly contractible object
form an exact functor and the weakly contractible objects cover the site. This file collects the
seven assertions of [Stacks, Tag 099Q]:

1. the derived complete sheaves of `Λ`-modules form a weak Serre subcategory of `Mod(𝒞, Λ)`;
2. a sheaf `ℱ` of `Λ`-modules satisfies `ℱ = lim ℱ/Iⁿℱ` if and only if `ℱ` is derived complete
   and `⋂ Iⁿℱ = 0`;
3. the sheaf `Λ̲^∧ = lim (Λ/Iⁿ)̲` is derived complete;
4. the limit of an inverse system of derived complete sheaves of `Λ`-modules is derived
   complete;
5. an object `K` of `D(𝒞, Λ)` is derived complete if and only if every cohomology sheaf `Hᵖ(K)`
   is;
6. a derived complete `K` is bounded above if and only if `K ⊗^𝐋_Λ (Λ/I)̲` is;
7. a derived complete `K` is bounded if `K ⊗^𝐋_Λ (Λ/I)̲` has finite Tor dimension.

Parts (1), (2), (4) and (5) are the statements
`AlgebraicGeometry.RingedSite.derivedCompleteSheaves_isWeakSerreClass`,
`AlgebraicGeometry.RingedSite.isLimit_adicQuotientSystem_iff`,
`AlgebraicGeometry.RingedSite.isDerivedComplete_limit` and
`AlgebraicGeometry.RingedSite.isDerivedComplete_iff_homology` for an arbitrary ringed site and
sheaf of ideals, read at the constant ringed site; for part (2) the finite generation of the
sections of `IΛ̲` over the weakly contractible objects is proved here,
`AlgebraicGeometry.RingedSite.fg_constantIdealSheaf_obj_of_isWeaklyContractible`. Part (3) is
part (4) applied to the tower `(Λ/Iⁿ)̲`, each of whose terms is killed by the `n`-th power of
every local section of `IΛ̲`. Parts (6) and (7) follow the source: a derived complete `K` is the
derived limit of `K ⊗^𝐋 (Λ/Iⁿ)̲` by [Stacks, Tag 099M]; the short exact sequences
`0 → (Iⁿ/Iⁿ⁺¹)̲ → (Λ/Iⁿ⁺¹)̲ → (Λ/Iⁿ)̲ → 0` carry a bound on `K ⊗^𝐋 (Λ/I)̲` to every
`K ⊗^𝐋 (Λ/Iⁿ)̲`, as in [Stacks, Tag 0942]; and a derived limit loses at most one degree from
above and none from below, countable products of sheaves of modules being exact
([Stacks, Tag 0947]).

## Main results

* `AlgebraicGeometry.RingedSite.isWeakSerreClass_isDerivedComplete_constant`: part (1).
* `AlgebraicGeometry.RingedSite.isLimit_adicQuotientSystem_iff_constant`: part (2).
* `AlgebraicGeometry.RingedSite.isDerivedComplete_constantCompletion`: part (3).
* `AlgebraicGeometry.RingedSite.isDerivedComplete_limit_constant`: part (4).
* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff_homology_constant`: part (5).
* `AlgebraicGeometry.RingedSite.isBoundedAbove_iff_constant`: part (6).
* `AlgebraicGeometry.RingedSite.isBounded_of_hasFiniteTorDimension_constant`: part (7).

## Implementation notes

The site is a small category `𝒞 : Type u` with morphisms in `Type u`, and `Λ : Type u`; these
are the universes of the constant ringed site `AlgebraicGeometry.RingedSite.constant` and of
[Stacks, Tag 099M], `AlgebraicGeometry.RingedSite.derivedCompletion_eq_rlim_constantAdicTower`.
"Enough weakly contractible objects" is
`CategoryTheory.GrothendieckTopology.HasEnoughWeaklyContractibleObjects`, [Stacks, Tag 090L].

`D(𝒞, Λ)` is the derived category of sheaves of modules over the ring sheaf of
`AlgebraicGeometry.RingedSite.constant J Λ`, and derived completeness is
`AlgebraicGeometry.RingedSite.IsDerivedComplete` along
`AlgebraicGeometry.RingedSite.constantIdealSheaf J Λ I`, the sheaf of ideals `IΛ̲`; a sheaf of
modules is derived complete when it is so placed in degree zero. In part (2), `Iⁿℱ` is
`AlgebraicGeometry.RingedSite.idealPowerProduct` and the inverse system `ℱ/Iⁿℱ` with its maps
from `ℱ` is `AlgebraicGeometry.RingedSite.adicQuotientSystem`. In part (3), `Λ̲^∧` is the limit
of the constant sheaves of modules of the tower `Stacks.ConstantSheaf.adicQuotientSystem`.

In parts (6) and (7), `K ⊗^𝐋_Λ (Λ/I)̲` is the canonical derived tensor product
`Stacks.SheafOfModules.derivedTensorProductFunctor` of [Stacks, Tag 06YU] with the constant sheaf
of `Λ/I`. Boundedness above is `Stacks.DerivedCategory.IsBoundedAbove`, and "bounded" is
membership in `D^{≥ a} ∩ D^{≤ b}` for some `a` and `b`. Finite Tor dimension in part (7) is taken,
as in the proof of the source and in [Stacks, Tag 0942], for `K ⊗^𝐋_Λ Λ/I` regarded as an object
of `D(𝒞, Λ/I)`: the derived base change `Stacks.Cohomology.derivedCoefficientChange` along
`Λ̲ ⟶ Λ̲/IΛ̲`, and Tor dimension `Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension`
measured against any derived tensor product on `D(𝒞, Λ̲/IΛ̲)`. The ring sheaf `Λ̲/IΛ̲` is
`Stacks.Sites.adicQuotient` of `IΛ̲` at exponent one; on modules it is the constant sheaf of
`Λ/I`, `AlgebraicGeometry.RingedSite.constantQuotientIso`.

Parts (1), (4) and (5) do not use that `Λ` is Noetherian, and parts (2) and (3) only use that `I`
is finitely generated; those hypotheses are dropped.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
-- `adicQuotientRingedSite` and `quotientRingedSite` are ordinary definitions; instance search
-- has to see through them to find the sheafification instances of the underlying site.
attribute [local instance_reducible] Stacks.Sites.quotientRingedSite
  Stacks.Sites.adicQuotientRingedSite

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The derived tensor product of any object with a zero sheaf of modules placed in degree zero
is zero. -/
theorem isZero_tensor_single_of_isZero (T : DerivedTensorProduct.{u, u, u, d} X)
    (K : AlgebraicGeometry.RingedSite.DerivedModules.{u, u, u, d} X)
    {F : AlgebraicGeometry.RingedSite.Modules.{u, u, u} X} (hF : IsZero F) :
    IsZero ((T.tensor.obj K).obj ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  Functor.map_isZero _ (Functor.map_isZero _ hF)

end Stacks.SheafOfModules.DerivedTensorProduct

namespace AlgebraicGeometry.RingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]

/-- **On a weakly contractible object, the sections of `IΛ̲` are the ideal generated by `I`**, so
they form a finitely generated ideal of `Γ(U, Λ̲)` when `I` is finitely generated. With generators
`g_1, …, g_r` of `I`, the sequence `⊕ Λ̲ ⟶ Λ̲ ⟶ (Λ/I)̲` is exact, `IΛ̲` dies in `(Λ/I)̲`, and
evaluation at a weakly contractible object is exact. -/
theorem fg_constantIdealSheaf_obj_of_isWeaklyContractible
    (hJ : J.HasEnoughWeaklyContractibleObjects) {I : Ideal Λ} (hI : I.FG) (U : C)
    (hU : J.IsWeaklyContractible U) :
    ((constantIdealSheaf J Λ I).obj (op U)).FG := by
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  let F := constantModuleFunctor J Λ
  let S := ShortComplex.mk (F.map (idealGeneratorsMap Λ g))
    (F.map (ModuleCat.ofHom (Submodule.mkQ I)))
    (by rw [← Functor.map_comp, idealGeneratorsMap_comp_mkQ Λ g I hg, Functor.map_zero])
  let B : Stacks.WeaklyContractible.WeaklyContractibleTestingFamily C J :=
    ⟨fun U => J.IsWeaklyContractible U, fun h => h, hJ⟩
  have hSU := (ShortComplex.moduleCat_exact_iff _).1 (evaluation_map_exact (constant J Λ) B U hU S
    (S.exact_of_g_is_cokernel (isColimitConstantModuleFunctorMapMkQ J Λ g hg)))
  let ε := constantModuleFunctorUnitIso J Λ
  suffices h : (constantIdealSheaf J Λ I).obj (op U) =
      Submodule.span ((Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj (op U))
        (Set.range fun k => (show (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)).val.obj (op U) from
            constantSectionRingHom J Λ (op U) (g k))) by
    rw [h]
    exact Submodule.fg_span (Set.finite_range _)
  refine le_antisymm (fun x hx => ?_) ((Submodule.span_le).2 ?_)
  · obtain ⟨z, hz⟩ := hSU (ε.inv.val.app (op U) x) (by
      change (constantReduction J Λ I).val.app (op U) x = 0
      exact Stacks.SheafOfModules.val_app_apply_eq_zero _ _
        (constantIdealSheaf_ι_comp_constantReduction J Λ I) (op U) ⟨x, hx⟩)
    have hx' : (F.map (idealGeneratorsMap Λ g) ≫ ε.hom).val.app (op U) z = x := by
      change ε.hom.val.app (op U) ((F.map (idealGeneratorsMap Λ g)).val.app (op U) z) = x
      change (F.map (idealGeneratorsMap Λ g)).val.app (op U) z = _ at hz
      rw [hz]
      change (ε.inv ≫ ε.hom).val.app (op U) x = x
      rw [ε.inv_hom_id]
      rfl
    exact hx' ▸ idealGeneratorsMap_val_app_mem J Λ g (op U) z
  · rintro _ ⟨k, rfl⟩
    exact SheafOfModules.Submodule.mem_generatedBy
      (F := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O))
      (fun p : I × Cᵒᵖ => p.2) (fun p => constantSectionRingHom J Λ p.2 p.1)
      (⟨g k, hg ▸ Ideal.subset_span ⟨k, rfl⟩⟩, op U)

/-- **[Stacks, Tag 099Q] (1).** On a site with enough weakly contractible objects, the derived
complete sheaves of `Λ`-modules form a weak Serre subcategory of `Mod(𝒞, Λ)`. -/
@[stacks 099Q "(1)"]
theorem isWeakSerreClass_isDerivedComplete_constant (hJ : J.HasEnoughWeaklyContractibleObjects)
    (I : Ideal Λ) :
    ObjectProperty.IsWeakSerreClass
      (fun F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) =>
        IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I)
          ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  derivedCompleteSheaves_isWeakSerreClass (constant J Λ) hJ (constantIdealSheaf J Λ I)

/-- **[Stacks, Tag 099Q] (4).** On a site with enough weakly contractible objects, the limit of an
inverse system `… → ℱ₃ → ℱ₂ → ℱ₁` of derived complete sheaves of `Λ`-modules is derived
complete. -/
@[stacks 099Q "(4)"]
theorem isDerivedComplete_limit_constant (hJ : J.HasEnoughWeaklyContractibleObjects)
    (I : Ideal Λ)
    (F : ℕᵒᵖ ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O))
    (hF : ∀ n : ℕ, IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj (F.obj (op n)))) :
    IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj (limit F)) :=
  isDerivedComplete_limit (constant J Λ) hJ (constantIdealSheaf J Λ I) F hF

/-- **[Stacks, Tag 099Q] (5).** On a site with enough weakly contractible objects, an object `K`
of `D(𝒞, Λ)` is derived complete if and only if each cohomology sheaf `Hᵖ(K)` is derived
complete. -/
@[stacks 099Q "(5)"]
theorem isDerivedComplete_iff_homology_constant (hJ : J.HasEnoughWeaklyContractibleObjects)
    (I : Ideal Λ)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O))) :
    IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I) K ↔
      ∀ p : ℤ, IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I)
        ((DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ p).obj K)) :=
  isDerivedComplete_iff_homology (constant J Λ) (constantIdealSheaf J Λ I) hJ K

/-- **[Stacks, Tag 099Q] (2).** On a site with enough weakly contractible objects, a sheaf `ℱ` of
`Λ`-modules satisfies `ℱ = lim ℱ/Iⁿℱ` — the maps `ℱ ⟶ ℱ/Iⁿℱ` form a limit cone — if and only if
`ℱ` is derived complete and `⋂ Iⁿℱ = 0`. Only the finite generation of `I` is used of the
Noetherian hypothesis. -/
@[stacks 099Q "(2)"]
theorem isLimit_adicQuotientSystem_iff_constant (hJ : J.HasEnoughWeaklyContractibleObjects)
    {I : Ideal Λ} (hI : I.FG)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)) :
    Nonempty (IsLimit (Cone.mk F
      (adicQuotientSystem (constant J Λ) (constantIdealSheaf J Λ I) F).quotientMap)) ↔
      IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I)
        ((DerivedCategory.singleFunctor _ 0).obj F) ∧
        (⨅ n : ℕ, idealPowerProduct (constant J Λ) (constantIdealSheaf J Λ I) F n) = ⊥ :=
  isLimit_adicQuotientSystem_iff (constant J Λ) hJ (constantIdealSheaf J Λ I)
    (fun U hU => fg_constantIdealSheaf_obj_of_isWeaklyContractible J Λ hJ hI U hU) F

/-- **[Stacks, Tag 099Q] (3).** On a site with enough weakly contractible objects, the sheaf
`Λ̲^∧ = lim (Λ/Iⁿ)̲` is derived complete. Only the finite generation of `I` is used of the
Noetherian hypothesis. -/
@[stacks 099Q "(3)"]
theorem isDerivedComplete_constantCompletion (hJ : J.HasEnoughWeaklyContractibleObjects)
    {I : Ideal Λ} (hI : I.FG) :
    IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        (limit (Stacks.ConstantSheaf.adicQuotientSystem I ⋙ constantModuleFunctor J Λ))) :=
  isDerivedComplete_limit_constant J Λ hJ I _ fun n =>
    isDerivedComplete_single_of_sectionKills (constant J Λ) (constantIdealSheaf J Λ I) _
      fun _ _ hf => ⟨n, pow_mem_annihilator_of_mem_constantIdealSheaf J Λ hI _ n
        (fun _ ha x => Stacks.ConstantSheaf.smul_adicQuotientSystem_obj I n ha x) hf⟩

section Bounds

/-- The short exact sequence `0 ⟶ (Iⁿ/Iⁿ⁺¹)̲ ⟶ (Λ/Iⁿ⁺¹)̲ ⟶ (Λ/Iⁿ)̲ ⟶ 0` of constant sheaves of
modules: the constant sheaf of `Stacks.ConstantSheaf.adicQuotientSystemShortComplex`. -/
abbrev constantAdicShortComplex (I : Ideal Λ) (n : ℕ) :
    ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)) :=
  (Stacks.ConstantSheaf.adicQuotientSystemShortComplex I n).map (constantModuleFunctor J Λ)

/-- The sequence `constantAdicShortComplex` of constant sheaves is short exact, since the
constant sheaf functor is exact. -/
theorem constantAdicShortComplex_shortExact (I : Ideal Λ) (n : ℕ) :
    (constantAdicShortComplex J Λ I n).ShortExact :=
  (Stacks.ConstantSheaf.adicQuotientSystemShortComplex_shortExact I n).map_of_exact _

/-- The sections of `IΛ̲` kill the graded piece `(Iⁿ/Iⁿ⁺¹)̲`. -/
theorem smul_constantAdicShortComplex_X₁ (I : Ideal Λ) (n : ℕ) (U : Cᵒᵖ)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U)
    (hc : c ∈ (constantIdealSheaf J Λ I).obj U)
    (y : (constantAdicShortComplex J Λ I n).X₁.val.obj U) : c • y = 0 :=
  smul_eq_zero_of_mem_constantIdealSheaf J Λ _
    (fun _ ha m => Stacks.ConstantSheaf.smul_adicQuotientSystemShortComplex_X₁ I n ha m) hc y

/-- The first term `(Λ/I⁰)̲` of the tower of constant sheaves is zero. -/
theorem isZero_constantModuleFunctor_adicQuotientSystem_obj_zero (I : Ideal Λ) :
    IsZero ((constantModuleFunctor J Λ).obj
      ((Stacks.ConstantSheaf.adicQuotientSystem I).obj (op 0))) :=
  (constantModuleFunctor J Λ).map_isZero
    (Stacks.ConstantSheaf.isZero_adicQuotientSystem_obj_zero I)

/-- **The derived limit of the tower `K ⊗^𝐋 (Λ/Iⁿ)̲` of a derived complete `K`, bounded.** If all
the `K ⊗^𝐋 (Λ/Iⁿ)̲` have cohomology in degrees `≥ a`, so has `K`; if they all have cohomology in
degrees `≤ b`, then `K` has cohomology in degrees `≤ b + 1`. This is [Stacks, Tag 099M] together
with the exactness of countable products of sheaves of modules on a site with enough weakly
contractible objects, [Stacks, Tag 0947]. -/
theorem isGE_isLE_of_isDerivedComplete [IsNoetherianRing Λ]
    (hJ : J.HasEnoughWeaklyContractibleObjects) (I : Ideal Λ)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)))
    (hK : IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I) K) :
    (∀ a : ℤ, (∀ n : ℕ, ((constantAdicTower J Λ I K).obj (op n)).IsGE a) → K.IsGE a) ∧
      (∀ b : ℤ, (∀ n : ℕ, ((constantAdicTower J Λ I K).obj (op n)).IsLE b) →
        K.IsLE (b + 1)) := by
  let S : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{u, u, u, u} C J :=
    { B := fun U => J.IsWeaklyContractible U
      isWeaklyContractible := fun _ hU F G φ hφ => hU F G φ hφ
      hasEnoughObjects := hJ
      O := Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O }
  have : HasExactLimitsOfShape (Discrete ℕ)
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)) :=
    Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat
      S.B S.hasEnoughObjects S.isWeaklyContractible
  have : HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O))) :=
    Stacks.WeaklyContractible.hasProductsOfShape_nat_derivedCategory S
  have hlim := (isDerivedComplete_iff_isDerivedLimit_constantAdicTower J Λ I K).1 hK
  exact ⟨fun a ha => Stacks.SmallDerivedCategory.isGE_of_isDerivedLimit _ K hlim a ha,
    fun b hb => Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit _ K hlim b hb⟩

/-- **[Stacks, Tag 099Q] (6).** On a site with enough weakly contractible objects, a derived
complete object `K` of `D(𝒞, Λ)` is bounded above if and only if `K ⊗^𝐋_Λ (Λ/I)̲` is bounded
above. -/
@[stacks 099Q "(6)"]
theorem isBoundedAbove_iff_constant [IsNoetherianRing Λ]
    (hJ : J.HasEnoughWeaklyContractibleObjects) (I : Ideal Λ)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)))
    (hK : IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I) K) :
    Stacks.DerivedCategory.IsBoundedAbove K ↔
      Stacks.DerivedCategory.IsBoundedAbove
        (((Stacks.SheafOfModules.derivedTensorProductFunctor (constant J Λ)).obj K).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantModuleFunctor J Λ).obj (ModuleCat.of Λ (Λ ⧸ I))))) := by
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct (constant J Λ)
  let ℐ := constantIdealSheaf J Λ I
  let M : ℕ → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) :=
    fun n => (constantModuleFunctor J Λ).obj
      ((Stacks.ConstantSheaf.adicQuotientSystem I).obj (op n))
  constructor
  · rintro ⟨b, hb⟩
    have h := isBoundedAboveBy_tensor T hb
      ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantModuleFunctor J Λ).obj (ModuleCat.of Λ (Λ ⧸ I)))) 0).2 inferInstance)
    exact ⟨b, add_zero b ▸ h⟩
  · rintro ⟨b, hb⟩
    have hQ : Stacks.DerivedCategory.IsBoundedAboveBy ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj (cokernel ℐ.ι))) b :=
      hb.of_iso ((T.tensor.obj K).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        (constantQuotientIso J Λ (IsNoetherian.noetherian I)).symm))
    have h₁ (n : ℕ) : Stacks.DerivedCategory.IsBoundedAboveBy ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj (constantAdicShortComplex J Λ I n).X₁)) b :=
      Stacks.Sites.isBoundedAboveBy_tensor_single_of_idealι_app_eq_zero ℐ T K _ b hQ
        (Stacks.Sites.sheafTensor_map_idealι_app_eq_zero ℐ _
          (smul_constantAdicShortComplex_X₁ J Λ I n))
    have h0 : Stacks.DerivedCategory.IsBoundedAboveBy ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj (M 0))) b := fun i _ =>
      Functor.map_isZero _ (isZero_tensor_single_of_isZero T K
        (isZero_constantModuleFunctor_adicQuotientSystem_obj_zero J Λ I))
    obtain ⟨c, hc⟩ := isUniformlyBoundedAbove_tensor_of_tower T K M b
      (constantAdicShortComplex J Λ I) (constantAdicShortComplex_shortExact J Λ I)
      (fun _ => Iso.refl _) (fun _ => Iso.refl _) h0 h₁
    exact ⟨c + 1, (Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE K _).2 <|
      (isGE_isLE_of_isDerivedComplete J Λ hJ I K hK).2 c fun n =>
        (Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ c).1 (hc n)⟩

/-- **[Stacks, Tag 099Q] (7).** On a site with enough weakly contractible objects, a derived
complete object `K` of `D(𝒞, Λ)` is bounded if `K ⊗^𝐋_Λ Λ/I`, as an object of `D(𝒞, Λ/I)`, has
finite Tor dimension, for any derived tensor product `T₁` on `D(𝒞, Λ/I)` against which Tor
dimension is measured. -/
@[stacks 099Q "(7)"]
theorem isBounded_of_hasFiniteTorDimension_constant [IsNoetherianRing Λ]
    (hJ : J.HasEnoughWeaklyContractibleObjects) (I : Ideal Λ)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)))
    (hK : IsDerivedComplete (constant J Λ) (constantIdealSheaf J Λ I) K)
    (T₁ : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, u + 1}
      (Stacks.Sites.adicQuotientRingedSite (constant J Λ) (constantIdealSheaf J Λ I) 1))
    (h : HasFiniteTorDimension.{u, u, u, u + 1} T₁
      ((Stacks.Cohomology.derivedCoefficientChange
        (Stacks.Sites.toAdicQuotient (constantIdealSheaf J Λ I) 1)).obj K)) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct (constant J Λ)
  let ℐ := constantIdealSheaf J Λ I
  let M : ℕ → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) :=
    fun n => (constantModuleFunctor J Λ).obj
      ((Stacks.ConstantSheaf.adicQuotientSystem I).obj (op n))
  obtain ⟨a, b, hab⟩ := h
  have hvan (i : ℤ) (hi : i ∉ Set.Icc a b) (n : ℕ) :
      IsZero (homologyTensorSingle.{u, u, u, u + 1} T K i (M n)) := by
    induction n with
    | zero =>
      exact Functor.map_isZero _ (isZero_tensor_single_of_isZero T K
        (isZero_constantModuleFunctor_adicQuotientSystem_obj_zero J Λ I))
    | succ n ih =>
      exact isZero_homology_tensor_single_X₂ T K i (constantAdicShortComplex_shortExact J Λ I n)
        (Stacks.Sites.isZero_homologyTensorSingle_of_hasTorAmplitude_adicQuotientOne ℐ T T₁ K
          a b i hi hab _ (smul_constantAdicShortComplex_X₁ J Λ I n)) ih
  have hbd := isGE_isLE_of_isDerivedComplete J Λ hJ I K hK
  refine ⟨a, b + 1, hbd.1 a fun n => ?_, hbd.2 b fun n => ?_⟩
  · rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hvan i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega) n
  · rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hvan i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega) n

end Bounds


end AlgebraicGeometry.RingedSite

end
