module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoBootstrap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi

/-!
# The depth-two improvement over an affine open: the adic replacement data

Keep the notation of `ImprovingFormalModulesDepthTwoAffine.lean`: `U` is an affine open of `X`
with ring `A₀ = Γ(X, U)` and ideal `I₀ = ℐ(U)`, `(ℱₙ) ⟶ (ℱ'ₙ) ⟶ (ℱ''ₙ)` are the canonical maps of
[Stacks, Tag 0EJF], and `(𝒢ₙ)` is a model of `(ℱ'ₙ)` in `Coh(X, ℐ)`, reached from `(ℱₙ)` by an
epimorphism `φ` of `Coh(X, ℐ)` whose levelwise kernels are killed by a power of `ℐ`.

When the quotients `M''ₙ/M'ₙ = H¹_{T'}(M'ₙ)` form an essentially constant system, the last
paragraph of the proof of [Stacks, Tag 0EJF] produces the module `M'' = lim M''ₙ`: the system
`(M''ₙ)` is pro-isomorphic to `(M''/I₀^{n+1}M'')`, and the induced maps
`Γ(U, ℱₙ) → M''/I₀^{n+1}M''` have kernels and cokernels killed by a fixed power of `I₀`. This
file assembles those statements, over `Γ(X, U)`, in the shape the sheaf-level adic replacement on
`U` consumes.

## Main definitions

* `Stacks.Algebraization.modelReplacementProIso`: the pro-isomorphism
  `(M''ₙ) ≅ (M''/I₀^{n+1}M'')`.
* `Stacks.Algebraization.modelReplacementMap`: the maps `Γ(U, ℱₙ) → M''/I₀^{n+1}M''`.

## Main results

* `Stacks.Algebraization.modelReplacementMap_compatible`: compatibility with the canonical map
  `(ℱₙ) ⟶ (ℱ''ₙ)` through the pro-isomorphism.
* `Stacks.Algebraization.smul_eq_zero_of_modelReplacementMap_eq_zero`,
  `Stacks.Algebraization.smul_mem_range_modelReplacementMap`: the kernels and cokernels of the
  maps `Γ(U, ℱₙ) → M''/I₀^{n+1}M''` are killed by a fixed power of `I₀`.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open InverseSequence

universe u

namespace Stacks.Algebraization

/-- The components of an epimorphism of `Coh(X, ℐ)` are epimorphisms. -/
theorem epi_hom_app_of_epi {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : Stacks.Coherent.CoherentAdicSystems I} (φ : F ⟶ G) [Epi φ] (n : ℕᵒᵖ) :
    Epi (φ.hom.app n) := by
  have h : IsZero (cokernel φ.hom) :=
    ((Preadditive.epi_iff_isZero_cokernel' _
      (Stacks.Coherent.coherentAdicCokernelIsColimit I φ)).trans
      (Stacks.Coherent.isZero_coherentAdicSystems_iff I
        (Stacks.Coherent.coherentAdicCokernel I φ))).1 inferInstance
  exact (Preadditive.epi_iff_isZero_cokernel _).2
    ((Stacks.Coherent.cokernelObjIso φ.hom n).isZero_iff.mp ((Functor.isZero_iff _).mp h n))

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (hdual : HasDualizingComplexOnAffineCover X) (F : Stacks.Coherent.CoherentAdicSystems I)
  {T T' : Set X} (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
  (hTY : T ⊆ I.support) (hTT' : T' ⊆ T)
  (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
  {U : X.Opens} (hU : IsAffineOpen U) (Mo : DepthOneAdicModel F hT)

/-! ### The levels of the formal sections of the model -/

omit [AlgebraicGeometry.IsNoetherian X] in
/-- For `n ≤ m`, the transition map `Γ(U, 𝒢ₘ) → Γ(U, 𝒢ₙ)` sends the level-`m` component of a
formal section of `(𝒢ₙ)` over `U` to its level-`n` component. -/
theorem tr_limitπ_formalSectionsOver (G : Stacks.Coherent.CoherentAdicSystems I) {n m : ℕ}
    (h : n ≤ m) (x : formalSectionsOver G U) :
    tr (G.obj ⋙ sectionsOver U) h (limit.π (G.obj ⋙ sectionsOver U) (op m) x) =
      limit.π (G.obj ⋙ sectionsOver U) (op n) x := by
  rw [tr, ← ConcreteCategory.comp_apply, limit.w]

section Replacement

variable {c : Cone (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).quotientSystem}
  {i : ℕ} {s : (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).quotientSystem.obj (op i) ⟶
    c.pt}
  (hc : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith
    (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).quotientSystem c (op i) s)

variable (U) in
/-- The module `M'' = lim M''ₙ` of compatible families of sections of `(ℱ''ₙ)` over `U`. -/
public abbrev modelReplacement : Type u :=
  Stacks.AdicSystem.compatibleFamilies (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙
    sectionsOver U)

/-- **The pro-isomorphism `(M''ₙ) ≅ (M''/I₀^{n+1}M'')`.** -/
public def modelReplacementProIso :
    ProIso (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙ sectionsOver U)
      (Stacks.AdicSystem.adicQuotientTower (I.ideal ⟨U, hU⟩)
        (modelReplacement hdual F hT hT' hTY himm U)) :=
  (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).replacementProIso hc

/-- The comparison `Γ(U, 𝒢ₙ) = M_𝒢/I₀^{n+1}M_𝒢 → M''/I₀^{n+1}M''`. -/
public def modelLevelsMap :
    Mo.G.obj ⋙ sectionsOver U ⟶ Stacks.AdicSystem.adicQuotientTower (I.ideal ⟨U, hU⟩)
      (modelReplacement hdual F hT hT' hTY himm U) :=
  (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).levelsMap (Mo.G.obj ⋙ sectionsOver U)
    (fun n => (limit.π (Mo.G.obj ⋙ sectionsOver U) (op n)).hom)
    (fun h x => tr_limitπ_formalSectionsOver Mo.G h x)
    (surjective_limitπ_formalSectionsOver Mo.G hU) (ker_limitπ_formalSectionsOver Mo.G hU)

/-- **The maps `Γ(U, ℱₙ) → M''/I₀^{n+1}M''`**, through an epimorphism `φ : (ℱₙ) ⟶ (𝒢ₙ)`. -/
public def modelReplacementMap (φ : F ⟶ Mo.G) :
    F.obj ⋙ sectionsOver U ⟶ Stacks.AdicSystem.adicQuotientTower (I.ideal ⟨U, hU⟩)
      (modelReplacement hdual F hT hT' hTY himm U) :=
  Functor.whiskerRight φ.hom (sectionsOver U) ≫
    modelLevelsMap hdual F hT hT' hTY hTT' himm hU Mo

/-- **Compatibility with the canonical map** `(ℱₙ) ⟶ (ℱ''ₙ)` through the pro-isomorphism, for a
factorization `φ ≫ κ` of the depth-one quotient map. -/
public theorem modelReplacementMap_compatible (φ : F ⟶ Mo.G)
    (hφ : φ.hom ≫ Mo.κ = toImprovedSystem T hT F.obj) (n : ℕ) :
    (sectionsOver U).map ((toCanonicalImprovedSystem hdual F hT hT' hTY himm).app
        (op ((modelReplacementProIso hdual F hT hT' hTY hTT' himm hU Mo hc).α n))) ≫
      (modelReplacementProIso hdual F hT hT' hTY hTT' himm hU Mo hc).φ n =
    (sectionsOver U).map (F.obj.map
        (homOfLE ((modelReplacementProIso hdual F hT hT' hTY hTT' himm hU Mo hc).αle n)).op) ≫
      (modelReplacementMap hdual F hT hT' hTY hTT' himm hU Mo φ).app (op n) := by
  set D := modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo
  set e := modelReplacementProIso hdual F hT hT' hTY hTT' himm hU Mo hc with he
  have hkey : (Functor.whiskerRight (Mo.κ ≫ extendNatTrans hdual F hT hT' hTY himm)
        (sectionsOver U)).app (op (e.α n)) ≫ e.φ n =
      (Mo.G.obj ⋙ sectionsOver U).map (homOfLE (e.αle n)).op ≫
        (modelLevelsMap hdual F hT hT' hTY hTT' himm hU Mo).app (op n) :=
    D.map_comp_replacementProIso_φ (Mo.G.obj ⋙ sectionsOver U)
      (fun n => (limit.π (Mo.G.obj ⋙ sectionsOver U) (op n)).hom)
      (fun h x => tr_limitπ_formalSectionsOver Mo.G h x)
      (surjective_limitπ_formalSectionsOver Mo.G hU) (ker_limitπ_formalSectionsOver Mo.G hU) hc
      (Functor.whiskerRight (Mo.κ ≫ extendNatTrans hdual F hT hT' hTY himm) (sectionsOver U))
      (fun _ _ => rfl) n
  have happ : (toCanonicalImprovedSystem hdual F hT hT' hTY himm).app (op (e.α n)) =
      φ.hom.app (op (e.α n)) ≫ (Mo.κ ≫ extendNatTrans hdual F hT hT' hTY himm).app
        (op (e.α n)) := by
    rw [toUniversalImprovedSystem_app, ← hφ]
    rfl
  rw [happ, Functor.map_comp, Category.assoc]
  change _ ≫ ((Functor.whiskerRight (Mo.κ ≫ extendNatTrans hdual F hT hT' hTY himm)
      (sectionsOver U)).app (op (e.α n)) ≫ e.φ n) = _
  rw [hkey]
  change (sectionsOver U).map (φ.hom.app (op (e.α n))) ≫
      (sectionsOver U).map (Mo.G.obj.map (homOfLE (e.αle n)).op) ≫
        (modelLevelsMap hdual F hT hT' hTY hTT' himm hU Mo).app (op n) = _
  rw [← Category.assoc, ← Functor.map_comp, ← φ.hom.naturality, Functor.map_comp,
    Category.assoc]
  rfl

include hc in
/-- **The kernels of `Γ(U, ℱₙ) → M''/I₀^{n+1}M''` are killed by a fixed power of `I₀`**, when the
levelwise kernels of `φ` are killed by a power of `ℐ`. -/
public theorem smul_eq_zero_of_modelReplacementMap_eq_zero (φ : F ⟶ Mo.G) {cφ : ℕ}
    (hφker : ∀ n : ℕ, idealPowerMultiple I cφ (kernel (φ.hom.app (op n))) = ⊥) (n : ℕ)
    (a : Γ(X, U)) (ha : a ∈ I.ideal ⟨U, hU⟩ ^
      (cφ + ((modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).e + (i + 1))))
    (q : Γ(F.obj.obj (op n), U))
    (hq : ((modelReplacementMap hdual F hT hT' hTY hTT' himm hU Mo φ).app (op n)).hom q = 0) :
    a • q = 0 := by
  set D := modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo
  have hle : I.ideal ⟨U, hU⟩ ^ cφ * I.ideal ⟨U, hU⟩ ^ (D.e + (i + 1)) ≤
      (Submodule.span Γ(X, U) {q}).annihilator := by
    refine Ideal.mul_le.2 fun r hr b hb => ?_
    rw [Submodule.mem_annihilator_span_singleton, mul_smul]
    have h1 : b • ((sectionsOver U).map (φ.hom.app (op n))).hom q = 0 :=
      D.smul_eq_zero_of_levelsMap_eq_zero (Mo.G.obj ⋙ sectionsOver U)
        (fun n => (limit.π (Mo.G.obj ⋙ sectionsOver U) (op n)).hom)
        (fun h x => tr_limitπ_formalSectionsOver Mo.G h x)
        (surjective_limitπ_formalSectionsOver Mo.G hU) (ker_limitπ_formalSectionsOver Mo.G hU)
        hc n hb _ hq
    have h2 : (φ.hom.app (op n)).app U (b • q) = 0 :=
      (((sectionsOver U).map (φ.hom.app (op n))).hom.map_smul b q).trans h1
    obtain ⟨y, hy⟩ := exists_kernel_section (φ.hom.app (op n)) U (b • q) h2
    have h3 : r • y = 0 :=
      affine_sections_annihilated_of_idealPowerMultiple_eq_bot (hφker n) ⟨U, hU⟩ hr y
    change r • (b • q) = 0
    rw [← hy]
    exact (((sectionsOver U).map (kernel.ι (φ.hom.app (op n)))).hom.map_smul r y).symm.trans
      ((congrArg _ h3).trans (map_zero _))
  rw [pow_add] at ha
  exact (Submodule.mem_annihilator_span_singleton _ _).1 (hle ha)

include hc in
/-- **The cokernels of `Γ(U, ℱₙ) → M''/I₀^{n+1}M''` are killed by `I₀^{i+1}`**, for an
epimorphism `φ`. -/
public theorem smul_mem_range_modelReplacementMap (φ : F ⟶ Mo.G) [Epi φ] (n : ℕ) (a : Γ(X, U))
    (ha : a ∈ I.ideal ⟨U, hU⟩ ^ (i + 1))
    (q : (Stacks.AdicSystem.adicQuotientTower (I.ideal ⟨U, hU⟩)
      (modelReplacement hdual F hT hT' hTY himm U)).obj (op n)) :
    a • q ∈ LinearMap.range
      ((modelReplacementMap hdual F hT hT' hTY hTT' himm hU Mo φ).app (op n)).hom := by
  obtain ⟨g, hg⟩ := (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).smul_mem_range_levelsMap
    (Mo.G.obj ⋙ sectionsOver U) (fun n => (limit.π (Mo.G.obj ⋙ sectionsOver U) (op n)).hom)
    (fun h x => tr_limitπ_formalSectionsOver Mo.G h x)
    (surjective_limitπ_formalSectionsOver Mo.G hU) (ker_limitπ_formalSectionsOver Mo.G hU)
    hc n ha q
  have := epi_hom_app_of_epi φ (op n)
  have : (F.obj.obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : (Mo.G.obj.obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  obtain ⟨f, hf⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
    (φ.hom.app (op n)) U hU g
  exact ⟨f, Eq.trans (by rw [← hf]; rfl) hg⟩

include hc in
/-- The terms `M''/I₀^{n+1}M''` are finite over `Γ(X, U)`. -/
public theorem finite_modelReplacement_quotient (n : ℕ) :
    Module.Finite Γ(X, U) (modelReplacement hdual F hT hT' hTY himm U ⧸
      (I.ideal ⟨U, hU⟩ ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (modelReplacement hdual F hT hT' hTY himm U)))) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine (modelExtensionData hdual F hT hT' hTY hTT' himm hU Mo).finite_adicQuotient hc
    (fun k => ?_) n
  have := isCoherent_canonicalImprovedSystem_obj hdual F hT hT' hTY himm (op k)
  have : ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj (op k)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj (op k)).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  exact Stacks.AlgebraicGeometry.CoherentFinite.finite_sections _ hU

end Replacement

end Stacks.Algebraization

end
