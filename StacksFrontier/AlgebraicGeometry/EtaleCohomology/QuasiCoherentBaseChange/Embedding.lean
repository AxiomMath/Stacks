module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Span
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Exact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleGlobalCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Normalized
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderBiproducts
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Embedding a quasi-coherent module into one which is acyclic after base change

Let `X` be a quasi-compact separated scheme, `U₁, …, Uₙ` a finite affine open cover with
inclusions `jᵢ`, and `ℱ` a quasi-coherent `𝒪_X`-module. The unit maps `ℱ ⟶ jᵢ_* jᵢ^* ℱ` combine
into a monomorphism `ℱ ⟶ 𝒢 = ⨁ᵢ jᵢ_* jᵢ^* ℱ`: a section killed by all of them vanishes on every
`Uᵢ`. For an affine morphism `g : Y ⟶ X`, the pullback `g^* (jᵢ_* M)` is `jᵢ'_* (gᵢ^* M)` for the
base-changed affine morphism `jᵢ' : Uᵢ ×_X Y ⟶ Y` with affine source (Stacks 02KG), so its
Zariski cohomology vanishes in positive degrees (Stacks 089W and 01XB), and so does the étale
cohomology of `(g^* 𝒢)ᵉ` (Stacks 03P2).

## Main results

* `AlgebraicGeometry.QcohEtale.subsingleton_etaleH_of_isZero_hgroup`: Zariski vanishing gives
  étale vanishing for `ℱᵉ`.
* `AlgebraicGeometry.QcohEtale.exists_embedding`: the embedding, in the shape of the hypothesis
  `hemb` of `AlgebraicGeometry.QcohEtale.spans_of_forall`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.QcohEtale

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
  HasFiniteBiproducts.of_hasFiniteProducts Stacks.Topology.hasExt_sheafOpens

/-- `Ext` of abelian sheaves at the morphism universe of the small étale site. -/
local instance hasExt_smallEtale_u' (X : Scheme.{u}) :
    HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  haveI : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- `Ext` of abelian sheaves at the object universe of the small étale site. -/
local instance (priority := high) hasExt_smallEtale_succ' (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- **Zariski vanishing gives étale vanishing for `ℱᵉ`** (Stacks 03P2). -/
theorem subsingleton_etaleH_of_isZero_hgroup {Y : Scheme.{u}} (G : Y.Modules)
    [G.IsQuasicoherent] (n : ℕ) (h : IsZero (Hgroup Y.ringCatSheaf ⊤ (n + 1) G)) :
    Subsingleton (Sheaf.H.{u + 1} (etaleSheaf G) (n + 1)) := by
  have : Subsingleton (Sheaf.H.{u, u} (smallEtaleAssociatedSheaf Y G) (n + 1)) :=
    subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup Y G (n + 1) (by omega) h
  exact (smallEtaleSheafHUliftAddEquiv Y (smallEtaleAssociatedSheaf Y G) (n + 1)).symm.toEquiv
    |>.subsingleton

section Zariski

/-- The cohomology of the pushforward of a quasi-coherent module along an affine morphism from an
affine scheme vanishes in positive degrees (Stacks 089W and 01XB). -/
theorem isZero_hgroup_pushforward {U Y : Scheme.{u}} (j : U ⟶ Y) [IsAffineHom j] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] (n : ℕ) (hn : 0 < n) :
    IsZero (Hgroup Y.ringCatSheaf ⊤ n ((Scheme.Modules.pushforward j).obj N)) :=
  IsZero.of_iso
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen U N ⊤ (isAffineOpen_top U) n hn)
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso j n).app ⟨N, inferInstance⟩).symm

/-- The same after pulling back along an affine morphism (Stacks 02KG). -/
theorem isZero_hgroup_pullback_pushforward {U X Y : Scheme.{u}} (j : U ⟶ X) [IsAffineHom j]
    [IsAffine U] (g : Y ⟶ X) [IsAffineHom g] (M : U.Modules) [M.IsQuasicoherent] (n : ℕ)
    (hn : 0 < n) :
    IsZero (Hgroup Y.ringCatSheaf ⊤ n
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward j).obj M))) := by
  have hw : IsPullback (pullback.fst j g) (pullback.snd j g) j g := IsPullback.of_hasPullback j g
  have hiso :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hw M
  have : IsAffineHom (pullback.snd j g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hw ‹IsAffineHom j›
  refine IsZero.of_iso (isZero_hgroup_pushforward (pullback.snd j g)
    ((Scheme.Modules.pullback (pullback.fst j g)).obj M) n hn) ?_
  exact (Hfunctor Y.ringCatSheaf ⊤ n).mapIso
    (@asIso _ _ _ _ ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hw.w).app M)
      hiso)

end Zariski

section Embedding

/-- A composite of two additive functors kills a finite biproduct as soon as it kills each
summand. -/
theorem isZero_obj_obj_biproduct {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E] (H : C ⥤ D) (H' : D ⥤ E) (hH : H.Additive)
    (hH' : H'.Additive) {J : Type} [Fintype J] (f : J → C) [HasBiproduct f]
    (h : ∀ j, IsZero (H'.obj (H.obj (f j)))) : IsZero (H'.obj (H.obj (⨁ f))) := by
  rw [IsZero.iff_id_eq_zero, ← H'.map_id, ← H.map_id, ← biproduct.total, H.map_sum, H'.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [H.map_comp, H'.map_comp, (h j).eq_of_tgt (H'.map (H.map (biproduct.π f j))) 0, zero_comp]

/-- A quasi-compact scheme has a finite affine open cover indexed by `Fin n`. -/
theorem exists_fin_affineCover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.affineOpens), ∀ x : X, ∃ i, x ∈ (U i : X.Opens) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => (V : Set X))
    (fun V => V.1.isOpen) (fun x _ => by
      obtain ⟨V, hV, hx, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  refine ⟨t.card, fun k => (t.equivFin.symm k).1, fun x => ?_⟩
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨V, hV⟩, by simpa using hx⟩

variable {X : Scheme.{u}}

/-- A morphism of modules which vanishes on every member of an open cover vanishes. -/
theorem hom_eq_zero_of_cover {n : ℕ} (U : Fin n → X.affineOpens)
    (hU : ∀ x : X, ∃ i, x ∈ (U i : X.Opens)) {K F : X.Modules} (φ : K ⟶ F)
    (h : ∀ i (W : X.Opens), W ≤ (U i : X.Opens) → φ.app W = 0) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  let Fs := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  refine TopCat.Sheaf.eq_of_locally_eq' Fs (fun i : Fin n => V ⊓ (U i : X.Opens)) V
    (fun i => homOfLE inf_le_left) ?_ (φ.app V x) 0 fun i => ?_
  · intro y hy
    obtain ⟨i, hi⟩ := hU y
    exact Opens.mem_iSup.2 ⟨i, ⟨hy, hi⟩⟩
  · rw [map_zero]
    show F.presheaf.map (homOfLE inf_le_left).op (φ.app V x) = 0
    rw [← Scheme.Modules.Hom.app_presheaf_map, h i _ inf_le_right]
    rfl

/-- In a separated scheme the inclusion of an affine open is an affine morphism. -/
@[sga "6 II 2.2.6"]
theorem isAffineHom_ι_of_isSeparated [IsSeparated (terminal.from X)] (U : X.affineOpens) :
    IsAffineHom (U : X.Opens).ι := by
  exact MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _
    (terminal.from X) inferInstance inferInstance

/-- The target `⨁ᵢ jᵢ_* jᵢ^* ℱ` of the embedding. -/
def embTarget {n : ℕ} (U : Fin n → X.affineOpens) (F : X.Modules) : X.Modules :=
  ⨁ fun i : Fin n => (Scheme.Modules.pushforward (U i : X.Opens).ι).obj
    ((Scheme.Modules.pullback (U i : X.Opens).ι).obj F)

/-- The embedding `ℱ ⟶ ⨁ᵢ jᵢ_* jᵢ^* ℱ`, assembled from the units. -/
def embMap {n : ℕ} (U : Fin n → X.affineOpens) (F : X.Modules) : F ⟶ embTarget U F :=
  biproduct.lift fun i =>
    (Scheme.Modules.pullbackPushforwardAdjunction (U i : X.Opens).ι).unit.app F

/-- The `i`-th component of `embMap U F` is the unit of the adjunction `jᵢ^* ⊣ jᵢ_*` at `ℱ`. -/
theorem embMap_π {n : ℕ} (U : Fin n → X.affineOpens) (F : X.Modules) (i : Fin n) :
    embMap U F ≫ biproduct.π _ i =
      (Scheme.Modules.pullbackPushforwardAdjunction (U i : X.Opens).ι).unit.app F :=
  biproduct.lift_π _ _

/-- **The embedding is a monomorphism.** -/
theorem mono_embMap {n : ℕ} (U : Fin n → X.affineOpens) (hU : ∀ x : X, ∃ i, x ∈ (U i : X.Opens))
    (F : X.Modules) : Mono (embMap U F) := by
  refine Preadditive.mono_of_cancel_zero _ fun {K} φ hφ => ?_
  refine hom_eq_zero_of_cover U hU φ fun i W hW => ?_
  have h1 : φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction (U i : X.Opens).ι).unit.app F =
      0 := by
    refine (congrArg (φ ≫ ·) (embMap_π U F i)).symm.trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ biproduct.π _ i) hφ).trans
      (zero_comp))
  ext x
  have h2 := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ W) x) h1
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.zero_app] at h2
  have hx : (φ.app W) x = 0 := by
    refine Stacks.Descent.unitApp_injective (U i : X.Opens).ι F W
      (by rwa [Scheme.Opens.opensRange_ι]) ?_
    rwa [map_zero, Stacks.Descent.unitApp_def]
  rw [hx]
  rfl

variable [IsSeparated (terminal.from X)]

/-- On a separated scheme, `⨁ᵢ jᵢ_* jᵢ^* ℱ` is quasi-coherent when `ℱ` is. -/
instance isQuasicoherent_embTarget {n : ℕ} (U : Fin n → X.affineOpens) (F : X.Modules)
    [F.IsQuasicoherent] : (embTarget U F).IsQuasicoherent := by
  have : ∀ i, ((Scheme.Modules.pushforward (U i : X.Opens).ι).obj
      ((Scheme.Modules.pullback (U i : X.Opens).ι).obj F)).IsQuasicoherent := fun i => by
    have := isAffineHom_ι_of_isSeparated (U i)
    exact ProperCoherentFiniteType.isQuasicoherent_pushforward _ _ inferInstance
  exact Scheme.Modules.isQuasicoherent_biproduct _

/-- **The embedding, in the shape of the hypothesis `hemb` of
`AlgebraicGeometry.QcohEtale.spans_of_forall`**: every quasi-coherent module `ℱ` on a
quasi-compact separated scheme sits in a short exact sequence `0 → ℱ → 𝒢 → 𝒬 → 0` of
quasi-coherent modules which stays short exact after `ℱ ↦ ℱᵉ`, also after pullback along a flat
affine morphism `g`, and the étale cohomology of `(g^* 𝒢)ᵉ` vanishes in positive degrees. -/
theorem exists_embedding [CompactSpace X] {Y : Scheme.{u}} (g : Y ⟶ X) [Flat g] [IsAffineHom g]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (G Q : X.Modules) (_ : G.IsQuasicoherent) (_ : Q.IsQuasicoherent) (i : F ⟶ G) (p : G ⟶ Q)
      (w : i ≫ p = 0),
      (etaleShortComplex (ShortComplex.mk i p w)).ShortExact ∧
      (etaleShortComplex (pullbackShortComplex g (ShortComplex.mk i p w))).ShortExact ∧
      ∀ q : ℕ, Subsingleton
        (Sheaf.H.{u + 1} (etaleSheaf ((Scheme.Modules.pullback g).obj G)) (q + 1)) := by
  obtain ⟨n, U, hU⟩ := exists_fin_affineCover X
  let S := ShortComplex.mk (embMap U F) (cokernel.π (embMap U F)) (cokernel.condition _)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (embMap U F))
      mono_f := mono_embMap U hU F }
  refine ⟨embTarget U F, cokernel (embMap U F), inferInstance,
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _, embMap U F,
    cokernel.π (embMap U F), cokernel.condition _, shortExact_etaleShortComplex_of_shortExact S hS,
    shortExact_etaleShortComplex_pullback g S hS, fun q => ?_⟩
  apply subsingleton_etaleH_of_isZero_hgroup
  let P : X.Modules ⥤ SheafOfModules.{u} Y.ringCatSheaf := Scheme.Modules.pullback g
  have : P.IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction g).isLeftAdjoint
  have : PreservesBinaryBiproducts P := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  refine isZero_obj_obj_biproduct (C := X.Modules) (D := SheafOfModules.{u} Y.ringCatSheaf) P
    (Hfunctor Y.ringCatSheaf ⊤ (q + 1)) (Functor.additive_of_preservesBinaryBiproducts _)
    (Functor.additive_rightDerived _ _) _ fun j => ?_
  have := isAffineHom_ι_of_isSeparated (U j)
  exact isZero_hgroup_pullback_pushforward _ g _ (q + 1) (by omega)

end Embedding

end AlgebraicGeometry.QcohEtale

end
