module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ValuationGermDeathOfLimitVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannCenterStrictHenselizationSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyQcqsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CohomologyVanishingTransport
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianSplitting
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Germs at the centers die along the strict henselizations at the centers

Let `B` be a domain with fraction field `K`, `V ⊆ K` a valuation ring containing `B`, and for
each `a` in the directed set `centerRanges V hV` of images `A_Y ⊆ V` of the local rings at the
centers of `V` on the proper models `Y`, let `A_Y → A_Y^{sh}` be strict henselizations forming
a directed system with colimit `V^{sh}`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.exists_isStrictHenselization_directLimit_centerRanges`).
This file proves the limit layer of Gabber's germ-killing step at `V`
(Travaux de Gabber, Exposé XVIII-A, last remark of §2): the schemes
`Spec (A_Y^{sh} ⊗_B K) = Spec A_Y^{sh} ×_{Spec B} Spec K` form a cofiltered system with affine
transition maps whose limit is `Spec (V^{sh} ⊗_V K)`, so if `H^q(Spec (V^{sh} ⊗_V K), F|) = 0`
then every class of `H^q(Spec (A_Y^{sh} ⊗_B K), F|)` dies on some later level (Stacks 09YQ).

## Main definitions

In the namespace `Stacks.EtaleCohomology.LimitExt`:

* `algebraBaseChangeSystem T p`: for a diagram `T : I ⥤ CommAlgCat R` and `p : X ⟶ Spec R`, the
  diagram of base changes `X ×_{Spec R} Spec T_i`;
* `algebraBaseChangeCone T p c`: the cone over it with apex `X ×_{Spec R} Spec c.pt` for a
  cocone `c`.

In the namespace `AlgebraicGeometry.Scheme.ZariskiRiemann`:

* `level V hV Rsh a`: the scheme `Spec A_a^{sh} ×_{Spec B} Spec K`;
* `levelTransition V hV Rsh fsh hfsh a b hab`: its transition map `level b ⟶ level a`;
* `tensorValuationEquiv`: `S ⊗_V K ≃ₐ[S] S ⊗_B K` for a `V`-algebra `S`.

## Main results

* `Stacks.EtaleCohomology.LimitExt.exists_le_algebraBaseChange_restriction_eq_zero`: **Stacks 09YQ
  for base changes along a filtered colimit of algebras**: a class on `X ×_R Spec T_{i₀}` that
  vanishes on `X ×_R Spec (colim T)` vanishes on some `X ×_R Spec T_i`, `i ≥ i₀`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.valuationSubringBaseMap_mem_centerRanges`: `B ⊆ A_Y`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.exists_le_levelTransition_restriction_eq_zero`: if
  `H^q(Spec (V^{sh} ⊗_V K), F|) = 0` then every class on a level dies on a later level.
* `exists_le_levelTransition_restriction_eq_zero_of_isStrictHenselization` (in the same
  namespace):
  the same, with the hypothesis of
  `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath` (vanishing for every strictly
  henselian ind-étale local `V`-algebra `S`) and `V^{sh}` a strict henselization of `V`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 04GI](https://stacks.math.columbia.edu/tag/04GI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

section BaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Preorder I] (T : I ⥤ CommAlgCat.{u} R)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- The diagram of base changes `i ↦ X ×_{Spec R} Spec T_i` of a scheme `p : X ⟶ Spec R` along
a diagram `T` of `R`-algebras. -/
def algebraBaseChangeSystem : Iᵒᵖ ⥤ Scheme.{u} :=
  T.op ⋙ algSpec (CommRingCat.of R) ⋙ Over.pullback p ⋙ Over.forget X

/-- A level of `algebraBaseChangeSystem` is the fibre product `Spec T_i ×_{Spec R} X`. -/
theorem algebraBaseChangeSystem_obj (i : I) : (algebraBaseChangeSystem T p).obj (op i) =
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i)))) p :=
  rfl

/-- The transition maps of `algebraBaseChangeSystem` cover the morphisms of spectra. -/
@[reassoc]
theorem algebraBaseChangeSystem_map_fst {i j : I} (h : i ⟶ j) :
    (algebraBaseChangeSystem T p).map h.op ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i)))) p =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj j)))) p ≫
        Spec.map (CommRingCat.ofHom (T.map h).hom.toRingHom) := by
  change pullback.lift _ _ _ ≫ _ = _
  exact (pullback.lift_fst _ _ _).trans rfl

/-- The transition maps of `algebraBaseChangeSystem` lie over `X`. -/
@[reassoc]
theorem algebraBaseChangeSystem_map_snd {i j : I} (h : i ⟶ j) :
    (algebraBaseChangeSystem T p).map h.op ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i)))) p =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj j)))) p :=
  Over.w ((Over.pullback p).map ((algSpec (CommRingCat.of R)).map (T.map h).op))

/-- The transition maps of `algebraBaseChangeSystem` are affine, being base changes of morphisms of
affine schemes. -/
instance isAffineHom_algebraBaseChangeSystem_map {i j : Iᵒᵖ} (g : i ⟶ j) :
    IsAffineHom ((algebraBaseChangeSystem T p).map g) := by
  refine MorphismProperty.overPullbackMap (P := @IsAffineHom) p
    ((T.op ⋙ algSpec (CommRingCat.of R)).map g) ?_
  change IsAffineHom (Spec.map _)
  infer_instance

/-- The cone over `algebraBaseChangeSystem T p` with apex `Spec c.pt ×_{Spec R} X`, for a cocone
`c` over `T`. -/
def algebraBaseChangeCone (c : Cocone T) : Cone (algebraBaseChangeSystem T p) :=
  (Over.forget X).mapCone ((Over.pullback p).mapCone ((algSpec (CommRingCat.of R)).mapCone c.op))

/-- The apex of `algebraBaseChangeCone` is `Spec c.pt ×_{Spec R} X`. -/
theorem algebraBaseChangeCone_pt (c : Cocone T) : (algebraBaseChangeCone T p c).pt =
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R c.pt))) p :=
  rfl

/-- The legs of `algebraBaseChangeCone` cover the morphisms of spectra. -/
@[reassoc]
theorem algebraBaseChangeCone_π_app_fst (c : Cocone T) (i : I) :
    (algebraBaseChangeCone T p c).π.app (op i) ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i)))) p =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R c.pt))) p ≫
        Spec.map (CommRingCat.ofHom (c.ι.app i).hom.toRingHom) := by
  change pullback.lift _ _ _ ≫ _ = _
  exact (pullback.lift_fst _ _ _).trans rfl

/-- The legs of `algebraBaseChangeCone` lie over `X`. -/
@[reassoc]
theorem algebraBaseChangeCone_π_app_snd (c : Cocone T) (i : I) :
    (algebraBaseChangeCone T p c).π.app (op i) ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i)))) p =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R c.pt))) p :=
  Over.w ((Over.pullback p).map ((algSpec (CommRingCat.of R)).map (c.ι.app i).op))

variable [IsDirected I (· ≤ ·)] [Nonempty I]

/-- **Base change along a filtered colimit of algebras is a limit**: for a colimit cocone `c`
over a directed diagram `T` of `R`-algebras, `Spec c.pt ×_{Spec R} X` is the limit of the
`Spec T_i ×_{Spec R} X`. -/
def isLimitAlgebraBaseChangeCone {c : Cocone T} (hc : IsColimit c) :
    IsLimit (algebraBaseChangeCone T p c) :=
  haveI : PreservesLimitsOfSize.{u, u} (algSpec (CommRingCat.of R)) :=
    preservesLimitsOfSize_algSpec
  haveI : PreservesLimitsOfShape Iᵒᵖ (Over.forget X) := inferInstance
  isLimitOfPreserves (Over.forget X) (isLimitOfPreserves (Over.pullback p)
    (isLimitOfPreserves (algSpec (CommRingCat.of R)) hc.op))

/-- **Stacks 09YQ, injectivity, for base changes along a filtered colimit of algebras.** Let
`T` be a directed diagram of `R`-algebras with colimit `c`, and `p : X ⟶ Spec R` with `X`
quasi-compact and quasi-separated. A class of `H^q(Spec T_{i₀} ×_R X, G)` whose restriction to
`Spec (colim T) ×_R X` vanishes already restricts to zero on `Spec T_i ×_R X` for some
`i ≥ i₀`. -/
theorem exists_le_algebraBaseChange_restriction_eq_zero [CompactSpace X] [QuasiSeparatedSpace X]
    {c : Cocone T} (hc : IsColimit c) (i₀ : I)
    (G : Sheaf ((algebraBaseChangeSystem T p).obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (ξ : Sheaf.H.{u + 1} G q)
    (hξ : etaleCohomologyRestrictionMap.{u, 0, u + 1} ((algebraBaseChangeCone T p c).π.app (op i₀))
      G q ξ = 0) :
    ∃ (i : I) (h : i₀ ≤ i),
      etaleCohomologyRestrictionMap.{u, 0, u + 1} ((algebraBaseChangeSystem T p).map (homOfLE h).op)
        G q ξ = 0 := by
  have : IsAffineHom
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i₀)))) p) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ p) inferInstance
  have hqc : QuasiCompact
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i₀)))) p) := inferInstance
  have hqs : QuasiSeparated
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (T.obj i₀)))) p) :=
    IsSeparated.instQuasiSeparated _
  have : CompactSpace ((algebraBaseChangeSystem T p).obj (op i₀)) :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ _ hqc _
  have : QuasiSeparatedSpace ((algebraBaseChangeSystem T p).obj (op i₀)) :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ _ inferInstance hqs
  exact exists_le_restriction_eq_zero_of_qcqs _ _ (isLimitAlgebraBaseChangeCone T p hc) i₀ G q ξ hξ

end BaseChange

end Stacks.EtaleCohomology.LimitExt

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

open Stacks.EtaleCohomology Stacks.EtaleCohomology.LimitExt Stacks.StrictHenselization
  Stacks.StrictHenselization.DirectLimit IsLocalRing

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable {B : Type u} [CommRing B] [IsDomain B] (V : ValuationSubring (FractionRing B))
  (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- **`B` lies in every `A_Y`**: the image of `b ∈ B` in `V` lies in the image of the local ring
at the center of `V` on every proper model, the center lying over `Spec V ⟶ Spec B`. -/
theorem valuationSubringBaseMap_mem_centerRanges (a : centerRanges V hV) (b : B) :
    valuationSubringBaseMap V hV b ∈ a.1 := by
  obtain ⟨M, hM⟩ := a.2
  rw [← hM]
  have key : ∀ l : Spec (.of V) ⟶ Spec (.of B), l = M.center V hV ≫ M.f →
      (Scheme.stalkClosedPointTo l).hom.range ≤ M.centerRange V hV := by
    rintro l rfl
    exact range_stalkClosedPointTo_comp_le _ _
  refine key _ (M.center_comp_f V hV).symm
    ⟨(Spec (.of B)).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso (.of B)).inv b), ?_⟩
  simpa using ConcreteCategory.congr_hom
    (Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (valuationSubringBaseMap V hV)))
    ((Scheme.ΓSpecIso (.of B)).inv b)

/-- The ring map `B → A_Y` (`AlgebraicGeometry.Scheme.ZariskiRiemann.valuationSubringBaseMap`
with values in `A_Y`). -/
def centerRangesBaseMap (a : centerRanges V hV) : B →+* a.1 :=
  (valuationSubringBaseMap V hV).codRestrict a.1 (valuationSubringBaseMap_mem_centerRanges V hV a)

section TensorEquiv

variable (S : Type u) [CommRing S] [Algebra V S] [Algebra B S]
  (hS : ∀ b, algebraMap B S b = algebraMap V S (valuationSubringBaseMap V hV b))

include hS in
/-- `S ⊗_V K` is the localization of `S` at the image of `B ∖ 0`: the image of `V ∖ 0` contains
it, and every `v = x / y ∈ V ∖ 0` divides `x = v y ∈ B ∖ 0`. -/
theorem isLocalization_tensor_valuationSubring :
    IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors B))
      (S ⊗[V] FractionRing B) := by
  have hinj : Function.Injective (valuationSubringBaseMap V hV) := fun x y h =>
    IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val h)
  refine (IsLocalization.iff_of_le_of_exists_dvd _
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors V)) ?_ ?_).mpr inferInstance
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨valuationSubringBaseMap V hV b, mem_nonZeroDivisors_of_ne_zero fun h0 => ?_,
      (hS b).symm⟩
    exact nonZeroDivisors.ne_zero hb (hinj (h0.trans (map_zero _).symm))
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := B) (v : FractionRing B)
    have hvy : v * valuationSubringBaseMap V hV y = valuationSubringBaseMap V hV x := by
      apply Subtype.ext
      change (v : FractionRing B) * algebraMap B (FractionRing B) y =
        algebraMap B (FractionRing B) x
      rw [← hxy, div_mul_cancel₀ _
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy)]
    have hx : x ∈ nonZeroDivisors B := by
      refine mem_nonZeroDivisors_of_ne_zero fun hx0 => nonZeroDivisors.ne_zero hv ?_
      apply Subtype.ext
      change (v : FractionRing B) = 0
      rw [← hxy, hx0, map_zero, zero_div]
    exact ⟨algebraMap B S x, ⟨x, hx, rfl⟩,
      ⟨algebraMap V S (valuationSubringBaseMap V hV y), by rw [hS, ← map_mul, hvy]⟩⟩

/-- **`S ⊗_V K ≃ S ⊗_B K`** for a `V`-algebra `S` (with the `B`-algebra structure through
`B → V`): both are the localization of `S` at the image of `B ∖ 0`. -/
def tensorValuationEquiv : S ⊗[V] FractionRing B ≃ₐ[S] S ⊗[B] FractionRing B :=
  haveI := isLocalization_tensor_valuationSubring V hV S hS
  IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (nonZeroDivisors B)) _ _

/-- `tensorValuationEquiv` is the identity on `1 ⊗ x`. -/
theorem tensorValuationEquiv_one_tmul (x : FractionRing B) :
    tensorValuationEquiv V hV S hS (1 ⊗ₜ x) = 1 ⊗ₜ x := by
  have h := IsLocalization.ringHom_ext (nonZeroDivisors B)
    (j := (tensorValuationEquiv V hV S hS).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        FractionRing B →ₐ[V] S ⊗[V] FractionRing B).toRingHom)
    (k := (Algebra.TensorProduct.includeRight :
        FractionRing B →ₐ[B] S ⊗[B] FractionRing B).toRingHom) ?_
  · exact RingHom.congr_fun h x
  · ext b
    have h1 : (1 : S) ⊗ₜ[V] algebraMap B (FractionRing B) b =
        algebraMap S (S ⊗[V] FractionRing B) (algebraMap B S b) := by
      rw [hS]
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := S) (B := FractionRing B)
        (valuationSubringBaseMap V hV b)).symm
    have h2 : (1 : S) ⊗ₜ[B] algebraMap B (FractionRing B) b =
        algebraMap S (S ⊗[B] FractionRing B) (algebraMap B S b) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := S) (B := FractionRing B) b).symm
    change tensorValuationEquiv V hV S hS ((1 : S) ⊗ₜ[V] algebraMap B (FractionRing B) b) =
      (1 : S) ⊗ₜ[B] algebraMap B (FractionRing B) b
    rw [h1, h2, AlgEquiv.commutes]

include hS in
/-- **Vanishing transported to `Spec S ×_B Spec K`.** If `H^q(Spec (S ⊗_V K), F|) = 0` then
`H^q(Spec S ×_{Spec B} Spec K, F|) = 0`: the two schemes are isomorphic over `η = Spec K`
(`pullbackSpecIso` and `AlgebraicGeometry.Scheme.ZariskiRiemann.tensorValuationEquiv`). -/
theorem subsingleton_H_pullback_snd_of_tensor
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hF : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (tensorFractionRingToGeneric V S)).obj F) q)) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B S)))
        (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))))).obj F) q) := by
  let ψ := tensorValuationEquiv V hV S hS
  let φ : CommRingCat.of (S ⊗[V] FractionRing B) ⟶ CommRingCat.of (S ⊗[B] FractionRing B) :=
    CommRingCat.ofHom ψ.toRingEquiv.toRingHom
  have : IsIso φ :=
    ⟨⟨CommRingCat.ofHom ψ.symm.toRingEquiv.toRingHom,
      CommRingCat.hom_ext (RingHom.ext fun x => ψ.symm_apply_apply x),
      CommRingCat.hom_ext (RingHom.ext fun x => ψ.apply_symm_apply x)⟩⟩
  have hring : Spec.map φ ≫ tensorFractionRingToGeneric V S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        FractionRing B →ₐ[B] S ⊗[B] FractionRing B).toRingHom) := by
    rw [tensorFractionRingToGeneric, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext
      (tensorValuationEquiv_one_tmul V hV S hS)))
  have hc : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B S)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))) =
      ((pullbackSpecIso B S (FractionRing B)).hom ≫ Spec.map φ) ≫
        tensorFractionRingToGeneric V S := by
    rw [Category.assoc, hring]
    exact (pullbackSpecIso_hom_snd B S (FractionRing B)).symm
  exact (subsingleton_H_inverseImage_iff_of_isIso F q _ _
    ((pullbackSpecIso B S (FractionRing B)).hom ≫ Spec.map φ) hc).mpr hF

end TensorEquiv

section Levels

variable (Rsh : centerRanges V hV → Type u) [∀ a, CommRing (Rsh a)] [∀ a, Algebra a.1 (Rsh a)]

/-- The ring map `B → A_Y → A_Y^{sh}`. -/
def levelBaseMap (a : centerRanges V hV) : B →+* Rsh a :=
  (algebraMap a.1 (Rsh a)).comp (centerRangesBaseMap V hV a)

/-- **The level at `A_Y`**: the scheme `Spec A_Y^{sh} ×_{Spec B} Spec K`, that is
`Spec (A_Y^{sh} ⊗_B K)`. -/
abbrev level (a : centerRanges V hV) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (levelBaseMap V hV Rsh a)))
    (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))

/-- The projection of a level to `η = Spec K`. -/
abbrev levelToGeneric (a : centerRanges V hV) :
    level V hV Rsh a ⟶ Spec (.of (FractionRing B)) :=
  pullback.snd _ _

variable (fsh : ∀ a b, a ≤ b → Rsh a →+* Rsh b)
  (hfsh : ∀ a b (hab : a ≤ b) x, fsh a b hab (algebraMap a.1 (Rsh a) x) =
    algebraMap b.1 (Rsh b)
      (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h) a b hab x))

include hfsh in
/-- The transition maps `A_Y^{sh} → A_{Y'}^{sh}` are `B`-algebra maps. -/
theorem fsh_levelBaseMap (a b : centerRanges V hV) (hab : a ≤ b) (x : B) :
    fsh a b hab (levelBaseMap V hV Rsh a x) = levelBaseMap V hV Rsh b x := by
  simp only [levelBaseMap, RingHom.comp_apply, hfsh]
  rfl

/-- **The transition map** `level b ⟶ level a` for `a ≤ b`, induced by `A_a^{sh} → A_b^{sh}`. -/
def levelTransition (a b : centerRanges V hV) (hab : a ≤ b) :
    level V hV Rsh b ⟶ level V hV Rsh a :=
  pullback.map _ _ _ _ (Spec.map (CommRingCat.ofHom (fsh a b hab))) (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
        (RingHom.ext fun x => (fsh_levelBaseMap V hV Rsh fsh hfsh a b hab x).symm))
    (by rw [Category.comp_id, Category.id_comp])

/-- The transition map `level b ⟶ level a` lies over `Spec A_b^{sh} ⟶ Spec A_a^{sh}`. -/
@[reassoc (attr := simp)]
theorem levelTransition_fst (a b : centerRanges V hV) (hab : a ≤ b) :
    levelTransition V hV Rsh fsh hfsh a b hab ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (fsh a b hab)) :=
  pullback.lift_fst _ _ _

/-- The transition map `level b ⟶ level a` commutes with the projections to `Spec K`. -/
@[reassoc (attr := simp)]
theorem levelTransition_snd (a b : centerRanges V hV) (hab : a ≤ b) :
    levelTransition V hV Rsh fsh hfsh a b hab ≫ levelToGeneric V hV Rsh a =
      levelToGeneric V hV Rsh b :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

variable [hds : DirectedSystem Rsh fun a b h => fsh a b h]

include hds hfsh in
/-- The directed system `a ↦ A_a^{sh}` as a diagram of `B`-algebras. -/
def levelSystem : centerRanges V hV ⥤ CommAlgCat.{u} B where
  obj a := letI := (levelBaseMap V hV Rsh a).toAlgebra; CommAlgCat.of B (Rsh a)
  map {a b} h :=
    letI := (levelBaseMap V hV Rsh a).toAlgebra
    letI := (levelBaseMap V hV Rsh b).toAlgebra
    CommAlgCat.ofHom
      { toRingHom := fsh a b h.le
        commutes' := fsh_levelBaseMap V hV Rsh fsh hfsh a b h.le }
  map_id _a := ConcreteCategory.hom_ext _ _ fun x =>
    DirectedSystem.map_self (f := fun a b h => fsh a b h) x
  map_comp {_a _b _c} h g := ConcreteCategory.hom_ext _ _ fun x =>
    (DirectedSystem.map_map (f := fun a b h => fsh a b h) h.le g.le x).symm

/-- The level of `algebraBaseChangeSystem` at `a` is `level a`. -/
theorem algebraBaseChangeSystem_levelSystem_obj (a : centerRanges V hV) :
    (algebraBaseChangeSystem (levelSystem V hV Rsh fsh hfsh)
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))).obj (op a) =
      level V hV Rsh a :=
  rfl

/-- The transition maps of `algebraBaseChangeSystem` are the `levelTransition`s. -/
theorem algebraBaseChangeSystem_levelSystem_map (a b : centerRanges V hV) (hab : a ≤ b) :
    (algebraBaseChangeSystem (levelSystem V hV Rsh fsh hfsh)
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))).map (homOfLE hab).op =
      levelTransition V hV Rsh fsh hfsh a b hab := by
  refine pullback.hom_ext ?_ ?_
  · exact (algebraBaseChangeSystem_map_fst _ _ (homOfLE hab)).trans
      (levelTransition_fst V hV Rsh fsh hfsh a b hab).symm
  · exact (algebraBaseChangeSystem_map_snd _ _ (homOfLE hab)).trans
      (levelTransition_snd V hV Rsh fsh hfsh a b hab).symm

variable [Algebra V (colimitRing Rsh fsh)]
  (hpin : ∀ a (x : a.1), algebraMap V (colimitRing Rsh fsh) x =
    colimitOf Rsh fsh a (algebraMap a.1 (Rsh a) x))

/-- The ring map `B → V → colim A_a^{sh}`. -/
def colimitBaseMap : B →+* colimitRing Rsh fsh :=
  (algebraMap V (colimitRing Rsh fsh)).comp (valuationSubringBaseMap V hV)

omit hds in
include hpin in
/-- The maps `A_a^{sh} → colim A_a^{sh}` are `B`-algebra maps. -/
theorem colimitOf_levelBaseMap (a : centerRanges V hV) (x : B) :
    colimitOf Rsh fsh a (levelBaseMap V hV Rsh a x) = colimitBaseMap V hV Rsh fsh x :=
  (hpin a (centerRangesBaseMap V hV a x)).symm

/-- The colimit cocone `A_a^{sh} → colim A_a^{sh}` of `B`-algebras. -/
def levelCocone : Cocone (levelSystem V hV Rsh fsh hfsh) where
  pt := letI := (colimitBaseMap V hV Rsh fsh).toAlgebra; CommAlgCat.of B (colimitRing Rsh fsh)
  ι :=
    { app a :=
        letI := (levelBaseMap V hV Rsh a).toAlgebra
        letI := (colimitBaseMap V hV Rsh fsh).toAlgebra
        CommAlgCat.ofHom
          { toRingHom := colimitOf Rsh fsh a
            commutes' := colimitOf_levelBaseMap V hV Rsh fsh hpin a }
      naturality _a _b h := ConcreteCategory.hom_ext _ _ fun x => Ring.DirectLimit.of_f h.le x }

/-- `colim A_a^{sh}` is the colimit of the `A_a^{sh}` as `B`-algebras. -/
def isColimitLevelCocone : IsColimit (levelCocone V hV Rsh fsh hfsh hpin) where
  desc d :=
    letI := (colimitBaseMap V hV Rsh fsh).toAlgebra
    CommAlgCat.ofHom
      { toRingHom := Ring.DirectLimit.lift Rsh (fun a b h => fsh a b h) d.pt
          (fun a => (d.ι.app a).hom.toRingHom)
          (fun a b hab x => ConcreteCategory.congr_hom (d.w (homOfLE hab)) x)
        commutes' := fun x => by
          obtain ⟨a⟩ := (inferInstance : Nonempty (centerRanges V hV))
          change Ring.DirectLimit.lift _ _ _ _ _ (colimitBaseMap V hV Rsh fsh x) = _
          rw [← colimitOf_levelBaseMap V hV Rsh fsh hpin a x]
          exact (Ring.DirectLimit.lift_of (G := Rsh) (f := fun a b h => fsh a b h) (P := d.pt)
            (g := fun a => (d.ι.app a).hom.toRingHom)
            (fun a b hab x => ConcreteCategory.congr_hom (d.w (homOfLE hab)) x) a _).trans
            ((d.ι.app a).hom.commutes x) }
  fac d a := ConcreteCategory.hom_ext _ _ fun x =>
    Ring.DirectLimit.lift_of (G := Rsh) (f := fun a b h => fsh a b h) (P := d.pt)
      (g := fun a => (d.ι.app a).hom.toRingHom)
      (fun a b hab x => ConcreteCategory.congr_hom (d.w (homOfLE hab)) x) a x
  uniq d m hm := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    obtain ⟨a, x, rfl⟩ := Ring.DirectLimit.exists_of z
    exact (ConcreteCategory.congr_hom (hm a) x).trans
      (Ring.DirectLimit.lift_of (G := Rsh) (f := fun a b h => fsh a b h) (P := d.pt)
        (g := fun a => (d.ι.app a).hom.toRingHom)
        (fun a b hab x => ConcreteCategory.congr_hom (d.w (homOfLE hab)) x) a x).symm

/-- **The cofiltered diagram of the levels** `a ↦ Spec A_a^{sh} ×_{Spec B} Spec K`, with the
transition maps `levelTransition`. -/
def levelDiagram : (centerRanges V hV)ᵒᵖ ⥤ Scheme.{u} where
  obj a := level V hV Rsh a.unop
  map {a b} h := levelTransition V hV Rsh fsh hfsh b.unop a.unop h.unop.le
  map_id a := by
    rw [← algebraBaseChangeSystem_levelSystem_map]
    exact (algebraBaseChangeSystem (levelSystem V hV Rsh fsh hfsh)
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))).map_id a
  map_comp {a b c} h g := by
    rw [← algebraBaseChangeSystem_levelSystem_map, ← algebraBaseChangeSystem_levelSystem_map,
      ← algebraBaseChangeSystem_levelSystem_map]
    exact (algebraBaseChangeSystem (levelSystem V hV Rsh fsh hfsh)
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))).map_comp h g

/-- `levelDiagram` is `algebraBaseChangeSystem` of the diagram `levelSystem` of `B`-algebras. -/
def levelDiagramIso : levelDiagram V hV Rsh fsh hfsh ≅
    algebraBaseChangeSystem (levelSystem V hV Rsh fsh hfsh)
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))) :=
  NatIso.ofComponents (fun a => Iso.refl (level V hV Rsh a.unop)) (fun {a b} h => by
    exact (Category.comp_id _).trans
      ((algebraBaseChangeSystem_levelSystem_map V hV Rsh fsh hfsh b.unop a.unop
        h.unop.le).symm.trans
        (Category.id_comp _).symm))

/-- Each level is affine. -/
instance isAffine_level (a : centerRanges V hV) : IsAffine (level V hV Rsh a) := inferInstance

/-- The transition maps of the levels are affine. -/
instance isAffineHom_levelDiagram_map {a b : (centerRanges V hV)ᵒᵖ} (g : a ⟶ b) :
    IsAffineHom ((levelDiagram V hV Rsh fsh hfsh).map g) :=
  haveI : IsAffine ((levelDiagram V hV Rsh fsh hfsh).obj a) := isAffine_level V hV Rsh a.unop
  haveI : IsAffine ((levelDiagram V hV Rsh fsh hfsh).obj b) := isAffine_level V hV Rsh b.unop
  isAffineHom_of_isAffine _

/-- The limit cone of the levels, with apex `Spec (colim A_a^{sh}) ×_{Spec B} Spec K`. -/
def levelCone : Cone (levelDiagram V hV Rsh fsh hfsh) :=
  (Cone.postcompose (levelDiagramIso V hV Rsh fsh hfsh).inv).obj
    (algebraBaseChangeCone (levelSystem V hV Rsh fsh hfsh)
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))
      (levelCocone V hV Rsh fsh hfsh hpin))

/-- **`Spec (colim A_a^{sh}) ×_{Spec B} Spec K` is the limit of the levels.** -/
def isLimitLevelCone : IsLimit (levelCone V hV Rsh fsh hfsh hpin) :=
  (IsLimit.postcomposeInvEquiv _ _).symm
    (isLimitAlgebraBaseChangeCone _ _ (isColimitLevelCocone V hV Rsh fsh hfsh hpin))

/-- The apex of `levelCone`. -/
theorem levelCone_pt : (levelCone V hV Rsh fsh hfsh hpin).pt =
    pullback (Spec.map (CommRingCat.ofHom (colimitBaseMap V hV Rsh fsh)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))) :=
  rfl

/-- The legs of `levelCone` lie over `η`. -/
theorem levelCone_π_app_levelToGeneric (a : centerRanges V hV) :
    (levelCone V hV Rsh fsh hfsh hpin).π.app (op a) ≫ levelToGeneric V hV Rsh a =
      pullback.snd (Spec.map (CommRingCat.ofHom (colimitBaseMap V hV Rsh fsh)))
        (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))) := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg _ (Category.id_comp _)).trans ?_
  exact algebraBaseChangeCone_π_app_snd _ _ _ a

include hpin in
/-- **Every class on a level dies on a later level, if `H^q` vanishes on the limit.** For the
directed system `a ↦ A_a^{sh}` of strict henselizations at the centers, with colimit
`V^{sh} = colim A_a^{sh}`, and an abelian sheaf `F` on `η = Spec K`: if
`H^q(Spec (V^{sh} ⊗_V K), F|) = 0`, then every class of `H^q(Spec (A_a^{sh} ⊗_B K), F|)`
restricts to zero on `Spec (A_b^{sh} ⊗_B K)` for some `b ≥ a`. The levels form a cofiltered
system with affine transitions whose limit is `Spec V^{sh} ×_B Spec K ≅ Spec (V^{sh} ⊗_V K)`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.isLimitLevelCone`,
`AlgebraicGeometry.Scheme.ZariskiRiemann.tensorValuationEquiv`), and Stacks 09YQ
(`Stacks.EtaleCohomology.LimitExt.exists_le_restriction_eq_zero_of_qcqs`) applies. -/
theorem exists_le_levelTransition_restriction_eq_zero
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hF : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (tensorFractionRingToGeneric V (colimitRing Rsh fsh))).obj F) q))
    (a : centerRanges V hV)
    (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (levelToGeneric V hV Rsh a)).obj F) q) :
    ∃ (b : centerRanges V hV) (hab : a ≤ b),
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (levelTransition V hV Rsh fsh hfsh a b hab) _ q
        ξ = 0 := by
  let : Algebra B (colimitRing Rsh fsh) := (colimitBaseMap V hV Rsh fsh).toAlgebra
  have hlim : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (pullback.snd (Spec.map (CommRingCat.ofHom (colimitBaseMap V hV Rsh fsh)))
        (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))))).obj F) q) :=
    subsingleton_H_pullback_snd_of_tensor V hV (colimitRing Rsh fsh) (fun _ => rfl) F q hF
  have hlim' := (subsingleton_H_iff_of_iso ((etaleAbelianInverseImageCompIso'.{u, 0}
    ((levelCone V hV Rsh fsh hfsh hpin).π.app (op a)) (levelToGeneric V hV Rsh a) _
    (levelCone_π_app_levelToGeneric V hV Rsh fsh hfsh hpin a).symm).app F) q).mp hlim
  have : CompactSpace ((levelDiagram V hV Rsh fsh hfsh).obj (op a)) :=
    inferInstanceAs (CompactSpace (level V hV Rsh a))
  have : QuasiSeparatedSpace ((levelDiagram V hV Rsh fsh hfsh).obj (op a)) :=
    inferInstanceAs (QuasiSeparatedSpace (level V hV Rsh a))
  exact exists_le_restriction_eq_zero_of_qcqs (levelDiagram V hV Rsh fsh hfsh)
    (levelCone V hV Rsh fsh hfsh hpin) (isLimitLevelCone V hV Rsh fsh hfsh hpin) a
    ((etaleAbelianInverseImage.{u, 0} (levelToGeneric V hV Rsh a)).obj F) q ξ
    (hlim'.elim _ _)

include hpin in
/-- **Every class on a level dies on a later level** (the limit layer of
`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath`). If `colim A_a^{sh}` is a strict
henselization of `V` and `H^q(Spec (S ⊗_V K), F|) = 0` for every strictly henselian local
`V`-algebra `S`, ind-étale over `V` with local structure map (the hypothesis of
`CenterLimitGermDeath`), then every class of `H^q(Spec (A_a^{sh} ⊗_B K), F|)` restricts to zero
on `Spec (A_b^{sh} ⊗_B K)` for some `b ≥ a`. -/
theorem exists_le_levelTransition_restriction_eq_zero_of_isStrictHenselization
    [IsLocalRing (colimitRing Rsh fsh)] (κ : Type u) [Field κ]
    [Algebra (maximalIdeal V).ResidueField κ] [IsSepClosure (maximalIdeal V).ResidueField κ]
    (hsh : IsStrictHenselization V κ (colimitRing Rsh fsh))
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hF : ∀ (S : Type u) [CommRing S] [StrictlyHenselianLocalRing S] [Algebra V S]
        [IsLocalHom (algebraMap V S)], StacksDraft.IndEtale V S →
        Subsingleton (Sheaf.H.{u + 1}
          ((etaleAbelianInverseImage.{u, 0} (tensorFractionRingToGeneric V S)).obj F) q))
    (a : centerRanges V hV)
    (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (levelToGeneric V hV Rsh a)).obj F) q) :
    ∃ (b : centerRanges V hV) (hab : a ≤ b),
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (levelTransition V hV Rsh fsh hfsh a b hab) _ q
        ξ = 0 := by
  have : HenselianLocalRing (colimitRing Rsh fsh) := hsh.henselian
  have : IsSepClosed (maximalIdeal (colimitRing Rsh fsh)).ResidueField := hsh.sepClosed
  have : StrictlyHenselianLocalRing (colimitRing Rsh fsh) :=
    { toIsSepClosed := isSepClosed_residueField_of_maximalIdeal (colimitRing Rsh fsh) }
  have : IsLocalHom (algebraMap V (colimitRing Rsh fsh)) := hsh.isLocalHom
  exact exists_le_levelTransition_restriction_eq_zero V hV Rsh fsh hfsh hpin F q
    (hF (colimitRing Rsh fsh) hsh.isFilteredColimitEtale) a ξ

end Levels

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
