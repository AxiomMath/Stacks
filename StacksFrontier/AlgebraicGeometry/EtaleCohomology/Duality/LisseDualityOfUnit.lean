module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLisseDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperLocallyConstantDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFibrationInputs
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseDualityCoverCompactification

/-!
# Poincaré duality with lisse coefficients on a smooth variety, from the constant case

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k`, `Λ = ℤ/ℓ`, and assume
Poincaré duality at `Λ` in dimensions `≤ d` (`Stacks.EtaleCohomology.UnitPoincareDualityUpTo`).
Let `S` be smooth irreducible of dimension `d` over `k`, `j : S → S̄` a compactification of
dimension `≤ d` and `τ` an injective trace on `H^{2d}_c(S) = Ext^{2d}_{S̄}(Λ, j_! Λ)`. For every
locally constant sheaf of finite type `F` on `S`, duality holds at `j_! F`
(`Stacks.EtaleCohomology.lisseDualityOfUnitInput`):

`H^i_c(S, F) × Ext^{2d-i}_{S̄}(j_! F, j_! Λ) → H^{2d}_c(S) → Λ` is perfect.

The proof is the standard dévissage.

* *The cover.* By Tag 0A3R there is a connected finite étale `π : T → S` of degree prime to `ℓ`
  with `π⁻¹F` a successive extension of copies of `Λ_T`. The normalization `T̄` of `S̄` in `T`
  compactifies `T` with `π̄ : T̄ → S̄` finite and `T = T̄ ×_{S̄} S`
  (`Stacks.EtaleCohomology.exists_isPullback_isFinite_of_compactification_of_finiteEtale`).
* *Transport along the cover.* With `Γ : π̄_* j_{T!} π⁻¹Λ ≅ j_! π_* π⁻¹Λ → j_! Λ` the trace of
  `π`, `y ↦ π̄_* y ∘ Γ` is a bijection
  `Ext^q_{T̄}(j_{T!} G, j_{T!} Λ) ≅ Ext^q_{S̄}(π̄_* j_{T!} G, j_! Λ)`
  (`Stacks.EtaleCohomology.bijective_mapExactFunctor_comp_extensionByZeroCoverTraceClass`: both are
  `Ext^q_T(G, π⁻¹Λ)`, as `j_!`, `j_{T!}` are fully faithful and `π_* ⊣ π⁻¹`), so duality on `S̄` at
  `j_! π_* G` is duality on `T̄` at `j_{T!} G` for the induced trace
  (`CategoryTheory.Abelian.Ext.isDualityPerfect_obj_iff_gysinTrace`).
* *The induced trace is injective*: `H^{2d}_c(T)` has `ℓ` elements
  (`Stacks.EtaleCohomology.topCohomologyPointClass`), and the trace does not vanish since the
  transfer `H^{2d}_c(T) → H^{2d}_c(S)` is onto (the trace `π_*Λ → Λ` is onto and
  `H^{2d+1}(S̄, -) = 0`, Tag 095U).
* *On the cover*, duality at `j_{T!} Λ_T` is the hypothesis, for the smooth irreducible `T` of
  dimension `d`, and the five lemma passes it to the successive extension `j_{T!} π⁻¹F`
  (`Stacks.EtaleCohomology.isDualityPerfect_map_of_relSeries_constantRankOneStep`).
* *The resolution.* The trace `π_* π⁻¹F → F` is onto with lisse kernel, and duality at every
  `j_! F` follows by the way-out argument
  (`CategoryTheory.Abelian.Ext.isDualityPerfect_of_resolution`), using `H^{2d+1}(S̄, -) = 0`.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroCoverTraceClass`: the class `Γ`.

## Main results

* `Stacks.EtaleCohomology.bijective_mapExactFunctor_comp_extensionByZeroCoverTraceClass`.
* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_directImage_of_unitPoincareDualityUpTo`.
* `Stacks.EtaleCohomology.lisseDualityOfUnitInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Transfer

variable {S Sb T Tb : Scheme.{u}} (j : S ⟶ Sb) [IsOpenImmersion j] (jT : T ⟶ Tb)
  [IsOpenImmersion jT] (π : T ⟶ S) [IsFinite π] [Etale π] (πb : Tb ⟶ Sb) [IsIntegralHom πb]
  (sq : IsPullback π jT j πb)

/-- **The trace class of a cover, with compact supports**:
`Γ : π̄_* j_{T!} π⁻¹ Λ_S ≅ j_! π_* π⁻¹ Λ_S → j_! Λ_S`, the trace of `π` extended by zero. -/
def extensionByZeroCoverTraceClass :
    Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) πb).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ))))
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := S) ℓ)) 0 :=
  Ext.mk₀ ((inv (extensionByZeroDirectImageNatTrans (ZMod ℓ) j jT π πb sq)).app _ ≫
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).map
      ((etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).counit.app
        (unitSheaf (X := S) ℓ)))

/-- **The duality of the cover, with compact supports**: `y ↦ π̄_* y ∘ Γ` is a bijection
`Ext^q_{T̄}(j_{T!} G, j_{T!} π⁻¹Λ_S) ≅ Ext^q_{S̄}(π̄_* j_{T!} G, j_! Λ_S)`. -/
theorem bijective_mapExactFunctor_comp_extensionByZeroCoverTraceClass
    (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ) :
    Function.Bijective (fun y : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj G)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ))) q =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) πb)).comp
        (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq) (add_zero q)) := by
  let jTS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT
  let jS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j
  let πS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) π
  let πbS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) πb
  let ε := extensionByZeroDirectImageNatTrans (ZMod ℓ) j jT π πb sq
  let B := unitSheaf (X := S) ℓ
  let E := (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj B
  let adjπ := etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π
  have hT := Stacks.ExtAdjunction.mapExtAddHom_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) jT) G E q
  rw [← Function.Bijective.of_comp_iff _ hT]
  have key : ∀ z : Ext G E q,
      ((z.mapExactFunctor jTS).mapExactFunctor πbS).comp
        (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq) (add_zero q) =
      (Ext.mk₀ ((inv ε).app G)).comp
        ((Stacks.ExtAdjunction.extMap adjπ G B q z).mapExactFunctor jS) (zero_add q) := by
    intro z
    rw [extensionByZeroCoverTraceClass, Stacks.ExtAdjunction.extMap_apply,
      Stacks.ExtFunctorial.mapExactFunctor_comp_functor jTS πbS G q z,
      ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
    have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor (inv ε) G q z
    have h1 : (z.mapExactFunctor (jTS ⋙ πbS)).comp (Ext.mk₀ ((inv ε).app E)) (add_zero q) =
        (Ext.mk₀ ((inv ε).app G)).comp (z.mapExactFunctor (πS ⋙ jS)) (zero_add q) :=
      hnat.symm
    rw [h1, Ext.comp_assoc _ _ _ (zero_add q) (add_zero q) (by omega), Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀, Stacks.ExtFunctorial.mapExactFunctor_comp_functor πS jS G q z]
  have hfun : (fun y : Ext (jTS.obj G) (jTS.obj E) q =>
        (y.mapExactFunctor πbS).comp (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq)
          (add_zero q)) ∘ ⇑(jTS.mapExtAddHom G E q) =
      (fun w => (Ext.mk₀ ((inv ε).app G)).comp w (zero_add q)) ∘
        ⇑(jS.mapExtAddHom (πS.obj G) B q) ∘
        ⇑(Stacks.ExtAdjunction.extMap adjπ G B q) :=
    funext key
  rw [hfun]
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q).comp
    ((Stacks.ExtAdjunction.mapExtAddHom_bijective
      (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j) _ _ q).comp
      (Stacks.ExtAdjunction.extMap_bijective adjπ _ _ q))

/-- **The transfer `Ext^n(A, π̄_* j_{T!} π⁻¹Λ_S) → Ext^n(A, j_! Λ_S)` is onto** when `π` is
surjective and `Ext^{n+1}(A, -)` vanishes. -/
private theorem exists_comp_extensionByZeroCoverTraceClass_eq [Surjective π]
    (A : EtaleModules.{u, 0} (ZMod ℓ) Sb) (n : ℕ)
    (hA : ∀ K : EtaleModules.{u, 0} (ZMod ℓ) Sb, Subsingleton (Ext A K (n + 1)))
    (z : Ext A ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := S) ℓ)) n) :
    ∃ x : Ext A ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) πb).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ)))) n,
      x.comp (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq) (add_zero n) = z := by
  let E := (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ)
  let tr := (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).counit.app
    (unitSheaf (X := S) ℓ)
  have : Epi tr := epi_etaleModuleDirectImageInverseImageAdj_counit_app (ZMod ℓ) π _
  let g := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).map tr
  have : Epi g := inferInstance
  let SS := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hSS : SS.ShortExact := { exact := ShortComplex.exact_kernel g }
  obtain ⟨x₂, hx₂⟩ := Ext.surjective_comp_mk₀_g_of_subsingleton hSS A n (hA _) z
  let ε := extensionByZeroDirectImageNatTrans (ZMod ℓ) j jT π πb sq
  have hε : ε.app E ≫ (inv ε).app E = 𝟙 _ := by
    rw [← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
  refine ⟨x₂.comp (Ext.mk₀ (ε.app E)) (add_zero _), ?_⟩
  rw [← hx₂]
  show (x₂.comp (Ext.mk₀ (ε.app E)) (add_zero _)).comp (Ext.mk₀ ((inv ε).app _ ≫ g))
    (add_zero _) = x₂.comp (Ext.mk₀ g) (add_zero _)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, reassoc_of% hε]

/-- **The transported Gysin trace of a cover is injective** when `π` is surjective, `τ` is
injective, `Ext^{n+1}(Λ_{S̄}, -)` vanishes and both top groups have `ℓ` elements. -/
private theorem injective_transportTrace_gysinTrace_extensionByZeroCoverTraceClass [Surjective π]
    (n : ℕ) (hvan : ∀ K : EtaleModules.{u, 0} (ZMod ℓ) Sb,
      Subsingleton (Ext (unitSheaf (X := Sb) ℓ) K (n + 1)))
    (τ : Ext (unitSheaf (X := Sb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := S) ℓ)) n →+ ZMod ℓ)
    (hτ : Function.Injective τ)
    (eO : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) πb).obj (unitSheaf (X := Sb) ℓ) ≅
      unitSheaf (X := Tb) ℓ)
    (eE : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ)) ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj (unitSheaf (X := T) ℓ))
    (hcardT : Nat.card (Ext (unitSheaf (X := Tb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj (unitSheaf (X := T) ℓ)) n) = ℓ)
    (hcardS : Nat.card (Ext (unitSheaf (X := Sb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := S) ℓ)) n) = ℓ) :
    Function.Injective (Ext.transportTrace (Ext.gysinTrace
      (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) πb) (unitSheaf (X := Sb) ℓ) _ _ (add_zero n)
      (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq) τ) eO eE) := by
  have hp : ℓ.Prime := Fact.out
  let ΛSb := unitSheaf (X := Sb) ℓ
  let jTS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT
  let E := (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ)
  let adjb := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) πb
  have : Finite (Ext ΛSb ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
      (unitSheaf (X := S) ℓ)) n) :=
    Nat.finite_of_card_ne_zero (by rw [hcardS]; exact hp.ne_zero)
  have : Nontrivial (Ext ΛSb ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
      (unitSheaf (X := S) ℓ)) n) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardS]; exact hp.one_lt)
  obtain ⟨z, hz⟩ := exists_ne (0 : Ext ΛSb ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
    (unitSheaf (X := S) ℓ)) n)
  obtain ⟨x₁, hx₁⟩ := exists_comp_extensionByZeroCoverTraceClass_eq j jT π πb sq ΛSb n hvan z
  have htg : Ext.gysinTrace adjb ΛSb _ _ (add_zero n)
      (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq) τ
      ((Stacks.ExtAdjunction.extMap adjb ΛSb (jTS.obj E) n x₁).comp
        (Ext.mk₀ (𝟙 (jTS.obj E))) (add_zero _)) ≠ 0 := by
    rw [Ext.gysinTrace_comp_extMap, Ext.mapExactFunctor_mk₀, CategoryTheory.Functor.map_id,
      Ext.mk₀_id_comp, hx₁]
    exact fun h0 => hz (hτ (h0.trans (map_zero τ).symm))
  refine injective_of_prime_card _ hcardT fun h0 => htg ?_
  have := DFunLike.congr_fun h0 (((Ext.mk₀ eO.inv).comp (Stacks.ExtAdjunction.extMap adjb ΛSb
    (jTS.obj E) n x₁) (zero_add _)).comp ((Ext.mk₀ (𝟙 (jTS.obj E))).comp
      (Ext.mk₀ eE.hom) (add_zero 0)) (add_zero _))
  rwa [AddMonoidHom.zero_apply, Ext.transportTrace_comp] at this

/-- **Duality on `S̄` at `j_! π_* G` from duality on `T̄` at `j_{T!} G`** for the transported
Gysin trace, when `Ext^i(Λ_{S̄}, -)` vanishes above `n`. -/
private theorem isDualityPerfect_extensionByZero_directImage_of_transportTrace (n : ℕ)
    (hvan : ∀ (K : EtaleModules.{u, 0} (ZMod ℓ) Sb) (i : ℕ), n < i →
      Subsingleton (Ext (unitSheaf (X := Sb) ℓ) K i))
    (τ : Ext (unitSheaf (X := Sb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := S) ℓ)) n →+ ZMod ℓ)
    (eO : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) πb).obj (unitSheaf (X := Sb) ℓ) ≅
      unitSheaf (X := Tb) ℓ)
    (eE : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ)) ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj (unitSheaf (X := T) ℓ))
    (G : EtaleModules.{u, 0} (ZMod ℓ) T)
    (hG : Ext.IsDualityPerfect (unitSheaf (X := Tb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj (unitSheaf (X := T) ℓ)) n
      (Ext.transportTrace (Ext.gysinTrace
        (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) πb) (unitSheaf (X := Sb) ℓ) _ _ (add_zero n)
        (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq) τ) eO eE)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj G)) :
    Ext.IsDualityPerfect (unitSheaf (X := Sb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := S) ℓ)) n τ
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj G)) :=
  Ext.isDualityPerfect_of_iso
    (asIso ((extensionByZeroDirectImageNatTrans (ZMod ℓ) j jT π πb sq).app G)).symm
    ((Ext.isDualityPerfect_obj_iff_gysinTrace (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) πb)
      (unitSheaf (X := Sb) ℓ) _ _ (add_zero n)
      (extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq) τ _
      (bijective_mapExactFunctor_comp_extensionByZeroCoverTraceClass (ℓ := ℓ) j jT π πb sq G)
      (hvan _) (fun i hi => absurd hi (Nat.not_lt_zero i))).2
      ((Ext.isDualityPerfect_transport_iff _ eO eE _).2 hG))

/-- **The top compactly supported cohomology has `ℓ` elements**, from
`Stacks.EtaleCohomology.TopCohomologyPointClass`. -/
private theorem natCard_ext_unitSheaf_extensionByZero_of_topCohomologyPointClass {k : Type u}
    [Field k] [IsAlgClosed k] (h : TopCohomologyPointClass ℓ k) (d : ℕ) {W : Scheme.{u}}
    (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension d f] [TopologicalSpace.NoetherianSpace W]
    [IrreducibleSpace W] (jc : CompactificationOf (Over.mk f)) :
    Nat.card (Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * d)) = ℓ := by
  obtain ⟨e⟩ := (h d W f jc).1
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod ℓ)

end Transfer

section Cover

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Duality at the direct image of a unipotent sheaf along a finite étale cover**, from duality
at `Λ`. Let `S` be smooth irreducible of dimension `d` over `k` with a compactification
`j : S → S̄` of dimension `≤ d`, `τ` an injective trace on `H^{2d}_c(S)`, `π : T → S` finite étale
with `T` connected and `G` a successive extension of copies of `Λ_T`. If Poincaré duality at `Λ`
holds in dimensions `≤ d`, then duality holds on `S̄` at `j_! π_* G`. -/
theorem isDualityPerfect_extensionByZero_directImage_of_unitPoincareDualityUpTo
    (hℓ : IsUnit (ℓ : k)) (d : ℕ) (hUPD : UnitPoincareDualityUpTo ℓ k d)
    {S : Scheme.{u}} (q : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension d q]
    [TopologicalSpace.NoetherianSpace S] [IrreducibleSpace S]
    (jS : CompactificationOf (Over.mk q)) (hdim : topologicalKrullDim jS.space ≤ d)
    (τ : Ext (unitSheaf (X := jS.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj (unitSheaf (X := S) ℓ))
        (2 * d) →+ ZMod ℓ) (hτ : Function.Injective τ)
    {T : Scheme.{u}} (π : T ⟶ S) [IsFinite π] [Etale π] [ConnectedSpace T]
    (G : EtaleModules.{u, 0} (ZMod ℓ) T) (Xs : RelSeries (ConstantRankOneStep.{0} ℓ G))
    (hhead : IsZero (Subobject.underlying.obj Xs.head)) (hlast : IsIso Xs.last.arrow) :
    Ext.IsDualityPerfect (unitSheaf (X := jS.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj (unitSheaf (X := S) ℓ))
      (2 * d) τ ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj G)) := by
  have : Smooth q := SmoothOfRelativeDimension.smooth d q
  have hTd : SmoothOfRelativeDimension d (π ≫ q) := by
    have : SmoothOfRelativeDimension (0 + d) (π ≫ q) := inferInstance
    rwa [zero_add] at this
  have : Smooth (π ≫ q) := SmoothOfRelativeDimension.smooth d (π ≫ q)
  obtain ⟨Tb, jT, hjT, πb, hπb, sq, hprop, hdimTb⟩ :=
    exists_isPullback_isFinite_of_compactification_of_finiteEtale k q jS π
  have := hjT
  have := hπb
  have := hprop
  have : IsIntegralHom πb := inferInstance
  have : IsIntegral T := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (π ≫ q)
  have : IsNoetherian T := by
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (π ≫ q)
    have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace π
    exact ⟨⟩
  have hTN : TopologicalSpace.NoetherianSpace T := IsNoetherian.noetherianSpace
  have hTI : IrreducibleSpace T := irreducibleSpace_of_isIntegral T
  have hw : jT ≫ πb ≫ jS.toBase = π ≫ q := by
    rw [← Category.assoc, ← sq.w, Category.assoc, CompactificationOf.immersion_comp_toBase']
    rfl
  let jc : CompactificationOf (Over.mk (π ≫ q)) :=
    CompactificationOf.ofFactorization Tb jT (πb ≫ jS.toBase) hw
  have hdimT : topologicalKrullDim Tb ≤ d := hdimTb.trans hdim
  have := IrreducibleSpace.connectedSpace S
  have : Surjective π := surjective_of_finiteEtale_of_connectedSpace π
  have hvanSb : ∀ (K : EtaleModules.{u, 0} (ZMod ℓ) jS.space) (i : ℕ), 2 * d < i →
      Subsingleton (Ext (unitSheaf (X := jS.space) ℓ) K i) := fun K i hi =>
    subsingleton_ext_unitSheaf_of_proper jS.toBase d hdim K i hi
  let eO : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) πb).obj (unitSheaf (X := jS.space) ℓ) ≅
      unitSheaf (X := Tb) ℓ :=
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) πb).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  let eE := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).mapIso (unitSheafInverseImageIso π)
  have ht' := injective_transportTrace_gysinTrace_extensionByZeroCoverTraceClass jS.immersion jT
    π πb sq (2 * d) (fun K => hvanSb K _ (by omega)) τ hτ eO eE
    (natCard_ext_unitSheaf_extensionByZero_of_topCohomologyPointClass
      (topCohomologyPointClass ℓ k hℓ) d (π ≫ q) jc)
    (natCard_ext_unitSheaf_extensionByZero_of_topCohomologyPointClass
      (topCohomologyPointClass ℓ k hℓ) d q jS)
  obtain ⟨hU₁, hU₂⟩ := hUPD d le_rfl T (π ≫ q) jc hdimT _ ht'
  obtain ⟨hG₁, -⟩ := isDualityPerfect_map_of_relSeries_constantRankOneStep
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT) (unitSheaf (X := Tb) ℓ)
    ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj (unitSheaf (X := T) ℓ)) (2 * d) _
    (fun K => subsingleton_ext_unitSheaf_of_proper (πb ≫ jS.toBase) d hdimT _ (2 * d + 1)
      (by omega)) hU₁ hU₂ G Xs hhead hlast
  exact isDualityPerfect_extensionByZero_directImage_of_transportTrace jS.immersion jT π πb sq
    (2 * d) hvanSb τ eO eE G hG₁

end Cover

/-- **Poincaré duality with lisse coefficients on a smooth variety, from the constant case**
(`Stacks.EtaleCohomology.LisseDualityOfUnitInput`): if Poincaré duality at `Λ` holds in
dimensions `≤ d`, then for every smooth irreducible `S` of dimension `d` over `k`, every
compactification `j : S → S̄` of dimension `≤ d`, every injective trace `τ` on `H^{2d}_c(S)` and
every locally constant sheaf of finite type `F` on `S`, duality holds at `j_! F`. -/
theorem lisseDualityOfUnitInput (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k] :
    LisseDualityOfUnitInput ℓ k := by
  intro hℓ d hUPD S q _ _ _ jS hdim τ hτ F hF
  have hp : ℓ.Prime := Fact.out
  have := IrreducibleSpace.connectedSpace S
  let jSS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion
  refine Ext.isDualityPerfect_of_resolution (unitSheaf (X := jS.space) ℓ)
    (jSS.obj (unitSheaf (X := S) ℓ)) (2 * d) τ
    (fun F => ∃ (H' : EtaleModules.{u, 0} (ZMod ℓ) S)
      (_ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology H'),
        F = jSS.obj H')
    ?_ (fun K _ => subsingleton_ext_unitSheaf_of_proper jS.toBase d hdim K (2 * d + 1)
      (by omega))
    (fun M j H φ => exists_extend_zmod H φ) _ ⟨F, hF, rfl⟩
  rintro _ ⟨G, hG, rfl⟩
  obtain ⟨T, π, δ, hfin, het, hconn, -, -, Xs, hhead, hlast⟩ :=
    exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep hp G hG
  have := hfin
  have := het
  have := hconn
  have := surjective_of_finiteEtale_of_connectedSpace π
  let ε := (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).counit.app G
  have : Epi ε := epi_etaleModuleDirectImageInverseImageAdj_counit_app (ZMod ℓ) π G
  have hG₂ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj G)) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules.{u, 0, 0} π
      (ZMod ℓ) _ (isFiniteTypeLocallyConstant_etaleModuleInverseImage π G hG)
  let SV := ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)
  have hSV : SV.ShortExact := { exact := ShortComplex.exact_kernel ε }
  refine ⟨SV.map jSS, hSV.map_of_exact jSS, rfl, ⟨kernel ε, ?_, rfl⟩, ?_⟩
  · exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0}
      S.smallEtaleTopology (ZMod ℓ) ε hG₂ hG
  · exact isDualityPerfect_extensionByZero_directImage_of_unitPoincareDualityUpTo k hℓ d hUPD q jS
      hdim τ hτ π _ Xs hhead hlast

end Stacks.EtaleCohomology

end
