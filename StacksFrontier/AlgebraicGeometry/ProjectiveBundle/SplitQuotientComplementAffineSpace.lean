module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementNonvanishing

/-!
# The complement of the projective bundle of a free quotient is an affine space

Let `X` be a scheme and `0 ⟶ 𝒪_X ⟶ F ⟶ G ⟶ 0` a split short exact sequence of quasi-coherent
modules (`Stacks.RelativeProj.UnitSplitting`: `σ : 𝒪_X ⟶ F`, `u : F ⟶ G`, with retractions
`τ : F ⟶ 𝒪_X`, `σ' : G ⟶ F`), so that `F = G ⊕ 𝒪_X`. Let `i : 𝐏(G) ⟶ 𝐏(F)` be the closed
immersion of `Stacks.RelativeProj.projectiveBundleMapOfEpi u` and `U = 𝐏(F) ∖ i(𝐏(G))` its open
complement (`Stacks.RelativeProj.splitQuotientComplement`). If `G` is free with basis
`e : 𝒪_X^{⊕ ι} ≅ G`, then `U ≅ 𝔸(ι; X)` over `X`
(`Stacks.RelativeProj.UnitSplitting.splitQuotientComplementIso`), the `j`-th coordinate being
`λ(σ'(k_j)) / λ(σ)`, with `k_j = e(e_j)` and `λ : π^*F ⟶ 𝒪(1)` the tautological quotient.

The proof is Yoneda with Tag 01O4. A morphism `f : T ⟶ 𝐏(F)` over `g : T ⟶ X` pulls back a
quotient `q_f : g^*F ⟶ f^*𝒪(1)`; it lands in `U` exactly when `μ_f = q_f ∘ g^*σ` is an isomorphism
(`Stacks.RelativeProj.isIso_pullback_map_hyperplane_iff`), and then `q_f` is, up to `μ_f`, the
quotient `ρ_c = g^*τ + c ∘ g^*u : g^*F ⟶ 𝒪_T` of the morphism
`c = μ_f⁻¹ ∘ q_f ∘ g^*σ' : g^*G ⟶ 𝒪_T`
(`Stacks.RelativeProj.UnitSplitting.overQuotientMap_comp_eq_splitQuotientMap`). Conversely every
`c` is reached, by the morphism classifying `ρ_c`. So morphisms `T ⟶ U` over `X` are the morphisms
`g^*G ⟶ 𝒪_T`, compatibly with pullback in `T`, and for `G` free these are the families
`ι → Γ(T, 𝒪_T)`, which are the morphisms `T ⟶ 𝔸(ι; X)` over `X`
(`AlgebraicGeometry.AffineSpace.homOfVector`).

## Main definitions

* `Stacks.RelativeProj.UnitSplitting`: the split short exact sequence `0 ⟶ 𝒪_X ⟶ F ⟶ G ⟶ 0`.
* `Stacks.RelativeProj.UnitSplitting.splitQuotientMap`: the quotient `ρ_c : g^*F ⟶ 𝒪_T`.
* `Stacks.RelativeProj.UnitSplitting.splitCoordMap`: the morphism `c_f : g^*G ⟶ 𝒪_T` of a
  morphism `f : T ⟶ 𝐏(F)` landing in `U`.
* `Stacks.RelativeProj.UnitSplitting.splitClassifyingMorphism`: the morphism classifying `ρ_c`.
* `Stacks.RelativeProj.UnitSplitting.splitQuotientComplementCoord`: the coordinates on `U`.
* `Stacks.RelativeProj.UnitSplitting.splitQuotientComplementIso`: **`U ≅ 𝔸(ι; X)` over `X`.**

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

section Structure

variable {X : Scheme.{u}} {F G : X.Modules}

/-- **A split short exact sequence `0 ⟶ 𝒪_X ⟶ F ⟶ G ⟶ 0`** with `u : F ⟶ G` its quotient map:
`σ : 𝒪_X ⟶ F` and `σ' : G ⟶ F` with retractions `τ : F ⟶ 𝒪_X` and `u`, so that `F = G ⊕ 𝒪_X`. -/
structure UnitSplitting (u : F ⟶ G) where
  /-- The inclusion of `𝒪_X`. -/
  σ : Scheme.unitModule X ⟶ F
  /-- The retraction onto `𝒪_X`. -/
  τ : F ⟶ Scheme.unitModule X
  /-- The section of the quotient map. -/
  σ' : G ⟶ F
  hsplit : τ ≫ σ + u ≫ σ' = 𝟙 F
  hσu : σ ≫ u = 0
  hστ : σ ≫ τ = 𝟙 (Scheme.unitModule X)
  hσ'τ : σ' ≫ τ = 0
  hσ'u : σ' ≫ u = 𝟙 G

end Structure

namespace UnitSplitting

variable {X : Scheme.{u}} {F G : X.Modules} {u : F ⟶ G} (S : UnitSplitting u)

/-! ### The quotients `ρ_c` -/

section Quotients

variable {T : Scheme.{u}} {g : T ⟶ X}

/-- **The quotient `ρ_c = g^*τ + c ∘ g^*u : g^*F ⟶ 𝒪_T`** of a morphism `c : g^*G ⟶ 𝒪_T`. -/
def splitQuotientMap (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    (Scheme.Modules.pullback g).obj F ⟶ Scheme.unitModule T :=
  (Scheme.Modules.pullback g).map S.τ ≫ (Scheme.Modules.pullbackUnitIso g).hom +
    (Scheme.Modules.pullback g).map u ≫ c

/-- `ρ_c ∘ g^*σ` is the comparison `g^*𝒪_X ≅ 𝒪_T`. -/
theorem map_σ_comp_splitQuotientMap
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    (Scheme.Modules.pullback g).map S.σ ≫ S.splitQuotientMap c =
      (Scheme.Modules.pullbackUnitIso g).hom := by
  rw [splitQuotientMap, Preadditive.comp_add, ← Functor.map_comp_assoc, S.hστ,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Functor.map_comp_assoc, S.hσu,
    Functor.map_zero, zero_comp, add_zero]

/-- `ρ_c ∘ g^*σ' = c`. -/
theorem map_σ'_comp_splitQuotientMap
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    (Scheme.Modules.pullback g).map S.σ' ≫ S.splitQuotientMap c = c := by
  rw [splitQuotientMap, Preadditive.comp_add, ← Functor.map_comp_assoc, S.hσ'τ,
    Functor.map_zero, zero_comp, zero_add, ← Functor.map_comp_assoc, S.hσ'u,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- `ρ_c` is a split epimorphism, split by `g^*σ`. -/
instance isSplitEpi_splitQuotientMap
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    IsSplitEpi (S.splitQuotientMap c) :=
  ⟨⟨(Scheme.Modules.pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map S.σ, by
    rw [Category.assoc, map_σ_comp_splitQuotientMap, Iso.inv_hom_id]⟩⟩

/-- **The invertible quotient `ρ_c : g^*F ⟶ 𝒪_T`.** -/
def splitQuotient (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    Stacks.Divisors.InvertibleQuotient T ((Scheme.Modules.pullback g).obj F) where
  L := Scheme.unitModule T
  invertible := (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (Stacks.SheafOfModules.isInvertible_unit _ _)
  q := S.splitQuotientMap c
  epi := inferInstance

/-- The quotient map of the invertible quotient `ρ_c` is `ρ_c`. -/
@[simp] theorem splitQuotient_q (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    (S.splitQuotient c).q = S.splitQuotientMap c :=
  rfl

end Quotients


/-! ### The coordinates of a morphism into the complement -/

section Coordinates

variable [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] {T : Scheme.{u}} {g : T ⟶ X}

/-- **The pulled-back hyperplane section `μ_f = q_f ∘ g^*σ : g^*𝒪_X ⟶ f^*𝒪(1)`** of a morphism
`f : T ⟶ 𝐏(F)` over `g`. -/
def splitHyperplaneMap (f : T ⟶ projectiveBundle X F) (hg : f ≫ projectiveBundleToBase X F = g) :
    (Scheme.Modules.pullback g).obj (Scheme.unitModule X) ⟶
      (Scheme.Modules.pullback f).obj ((tautologicalDatum F).twist) :=
  (Scheme.Modules.pullback g).map S.σ ≫ (tautologicalDatum F).overQuotientMap f hg

omit [G.IsQuasicoherent] [Epi u] in
/-- `μ_f` is the pullback along `f` of the hyperplane section, up to the comparisons. -/
theorem splitHyperplaneMap_eq (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g) :
    S.splitHyperplaneMap f hg =
      (Scheme.Modules.pullbackCongr hg).inv.app (Scheme.unitModule X) ≫
        (Scheme.Modules.pullbackComp f (projectiveBundleToBase X F)).inv.app
          (Scheme.unitModule X) ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map S.σ ≫
            (tautologicalDatum F).univ) := by
  have n₁ := (Scheme.Modules.pullbackCongr hg).inv.naturality S.σ
  have n₂ := (Scheme.Modules.pullbackComp f (projectiveBundleToBase X F)).inv.naturality S.σ
  simp only [Functor.comp_map] at n₁ n₂
  rw [splitHyperplaneMap, TautologicalDatum.overQuotientMap, reassoc_of% n₁, reassoc_of% n₂,
    Functor.map_comp]

/-- **A morphism lands in the complement `U` exactly when `μ_f` is an isomorphism.** -/
theorem isIso_splitHyperplaneMap_iff (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g) :
    IsIso (S.splitHyperplaneMap f hg) ↔ Set.range f.base ⊆ splitQuotientComplement u := by
  have key : IsIso ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map S.σ ≫
        (tautologicalDatum F).univ)) ↔ Set.range f.base ⊆ splitQuotientComplement u :=
    isIso_pullback_map_hyperplane_iff u S.σ S.τ S.σ' S.hsplit S.hσu f
  rw [← key, splitHyperplaneMap_eq]
  constructor
  · intro _
    exact IsIso.of_isIso_comp_left ((Scheme.Modules.pullbackCongr hg).inv.app _ ≫
      (Scheme.Modules.pullbackComp f (projectiveBundleToBase X F)).inv.app _) _
  · intro _
    infer_instance

/-- `μ_f` as an isomorphism, for `f` landing in `U`. -/
def splitHyperplaneIso (f : T ⟶ projectiveBundle X F) (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    (Scheme.Modules.pullback g).obj (Scheme.unitModule X) ≅
      (Scheme.Modules.pullback f).obj ((tautologicalDatum F).twist) :=
  haveI := (S.isIso_splitHyperplaneMap_iff f hg).2 hf
  asIso (S.splitHyperplaneMap f hg)

/-- The underlying morphism of `μ_f` as an isomorphism is `μ_f`. -/
@[simp] theorem splitHyperplaneIso_hom (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    (S.splitHyperplaneIso f hg hf).hom = S.splitHyperplaneMap f hg :=
  rfl

/-- **The coordinate morphism `c_f = μ_f⁻¹ ∘ q_f ∘ g^*σ' : g^*G ⟶ 𝒪_T`** of a morphism
`f : T ⟶ 𝐏(F)` over `g` landing in `U`: on the `j`-th basis vector `k_j` of `G` it is the ratio
`λ(σ'(k_j)) / λ(σ)` of the two pulled-back sections of `𝒪(1)`. -/
def splitCoordMap (f : T ⟶ projectiveBundle X F) (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T :=
  (Scheme.Modules.pullback g).map S.σ' ≫ (tautologicalDatum F).overQuotientMap f hg ≫
    (S.splitHyperplaneIso f hg hf).inv ≫ (Scheme.Modules.pullbackUnitIso g).hom

/-- **The coordinate morphism is the ratio `λ(σ') / λ(σ)`**: `q_f ∘ g^*σ' = μ_f ∘ c_f`, with
`c_f` read through `g^*𝒪_X ≅ 𝒪_T`. -/
theorem map_σ'_comp_overQuotientMap (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    (Scheme.Modules.pullback g).map S.σ' ≫ (tautologicalDatum F).overQuotientMap f hg =
      S.splitCoordMap f hg hf ≫ (Scheme.Modules.pullbackUnitIso g).inv ≫
        S.splitHyperplaneMap f hg := by
  simp only [splitCoordMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← splitHyperplaneIso_hom _ f hg hf, Iso.inv_hom_id, Category.comp_id]

/-- **The quotient a morphism into `U` pulls back is `ρ` of its coordinates**, up to `μ_f`. -/
theorem overQuotientMap_comp_eq_splitQuotientMap (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    (tautologicalDatum F).overQuotientMap f hg ≫ (S.splitHyperplaneIso f hg hf).inv ≫
        (Scheme.Modules.pullbackUnitIso g).hom =
      S.splitQuotientMap (S.splitCoordMap f hg hf) := by
  have e : (Scheme.Modules.pullback g).map S.τ ≫ (Scheme.Modules.pullback g).map S.σ +
      (Scheme.Modules.pullback g).map u ≫ (Scheme.Modules.pullback g).map S.σ' = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, S.hsplit,
      CategoryTheory.Functor.map_id]
  conv_lhs => rw [← Category.id_comp ((tautologicalDatum F).overQuotientMap f hg), ← e]
  rw [splitQuotientMap, splitCoordMap]
  simp only [Preadditive.add_comp, Category.assoc]
  congr 1
  rw [← Category.assoc ((Scheme.Modules.pullback g).map S.σ),
    show (Scheme.Modules.pullback g).map S.σ ≫ (tautologicalDatum F).overQuotientMap f hg =
      (S.splitHyperplaneIso f hg hf).hom from rfl, Iso.hom_inv_id_assoc]

/-- **A morphism pulling back `ρ_c` has coordinates `c`.** If `q_f ≫ α = ρ_c` for an isomorphism
`α : f^*𝒪(1) ≅ 𝒪_T`, then `f` lands in `U` and `c_f = c`. -/
theorem range_subset_of_overQuotientMap_comp_eq (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T)
    (α : (Scheme.Modules.pullback f).obj ((tautologicalDatum F).twist) ≅ Scheme.unitModule T)
    (hα : (tautologicalDatum F).overQuotientMap f hg ≫ α.hom = S.splitQuotientMap c) :
    Set.range f.base ⊆ splitQuotientComplement u := by
  rw [← S.isIso_splitHyperplaneMap_iff f hg]
  have h : S.splitHyperplaneMap f hg ≫ α.hom = (Scheme.Modules.pullbackUnitIso g).hom := by
    rw [splitHyperplaneMap, Category.assoc, hα, map_σ_comp_splitQuotientMap]
  have : IsIso (S.splitHyperplaneMap f hg ≫ α.hom) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ α.hom

/-- If `q_f ≫ α = ρ_c` for an isomorphism `α : f^*𝒪(1) ≅ 𝒪_T`, then `c_f = c`. -/
theorem splitCoordMap_eq_of_overQuotientMap_comp_eq (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T)
    (α : (Scheme.Modules.pullback f).obj ((tautologicalDatum F).twist) ≅ Scheme.unitModule T)
    (hα : (tautologicalDatum F).overQuotientMap f hg ≫ α.hom = S.splitQuotientMap c) :
    S.splitCoordMap f hg hf = c := by
  have h : S.splitHyperplaneMap f hg ≫ α.hom = (Scheme.Modules.pullbackUnitIso g).hom := by
    rw [splitHyperplaneMap, Category.assoc, hα, map_σ_comp_splitQuotientMap]
  have hinv : (S.splitHyperplaneIso f hg hf).inv ≫ (Scheme.Modules.pullbackUnitIso g).hom =
      α.hom := by
    rw [← h, show S.splitHyperplaneMap f hg = (S.splitHyperplaneIso f hg hf).hom from rfl,
      Iso.inv_hom_id_assoc]
  rw [splitCoordMap, hinv, hα, map_σ'_comp_splitQuotientMap]

/-- **Two morphisms into `U` over `X` with the same coordinates are equal.** -/
theorem eq_of_splitCoordMap_eq (f₁ f₂ : T ⟶ projectiveBundle X F)
    (hg₁ : f₁ ≫ projectiveBundleToBase X F = g) (hg₂ : f₂ ≫ projectiveBundleToBase X F = g)
    (hf₁ : Set.range f₁.base ⊆ splitQuotientComplement u)
    (hf₂ : Set.range f₂.base ⊆ splitQuotientComplement u)
    (h : S.splitCoordMap f₁ hg₁ hf₁ = S.splitCoordMap f₂ hg₂ hf₂) : f₁ = f₂ := by
  refine (tautologicalDatum F).eq_of_overQuotient_isEquivalent ((Scheme.Modules.pullback g).obj F)
    (Iso.refl _) f₁ f₂ hg₁ hg₂ ?_
  refine ⟨(S.splitHyperplaneIso f₁ hg₁ hf₁).symm ≪≫ (S.splitHyperplaneIso f₂ hg₂ hf₂), ?_⟩
  have e₁ := S.overQuotientMap_comp_eq_splitQuotientMap f₁ hg₁ hf₁
  have e₂ := S.overQuotientMap_comp_eq_splitQuotientMap f₂ hg₂ hf₂
  rw [h, ← e₂] at e₁
  simp only [TautologicalDatum.overQuotient_q, Iso.refl_hom, Category.id_comp]
  have := e₁ =≫ (Scheme.Modules.pullbackUnitIso g).inv ≫ (S.splitHyperplaneIso f₂ hg₂ hf₂).hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at this
  exact this

end Coordinates

/-! ### Classifying `ρ_c` -/

section Classifying

variable [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] {T : Scheme.{u}}

/-- **The morphism `T ⟶ 𝐏(F)` over `g` classifying the quotient `ρ_c`** (Tag 01O4). -/
def splitClassifyingMorphism (g : T ⟶ X)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) : T ⟶ projectiveBundle X F :=
  ((tautologicalDatum F).classifyingMorphismOver ((Scheme.Modules.pullback g).obj F) (Iso.refl _)
    (S.splitQuotient c)).1

omit [G.IsQuasicoherent] [Epi u] in
/-- The classifying morphism of `ρ_c` lies over `g`. -/
@[reassoc (attr := simp)]
theorem splitClassifyingMorphism_comp (g : T ⟶ X)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    S.splitClassifyingMorphism g c ≫ projectiveBundleToBase X F = g :=
  ((tautologicalDatum F).classifyingMorphismOver ((Scheme.Modules.pullback g).obj F) (Iso.refl _)
    (S.splitQuotient c)).2

omit [G.IsQuasicoherent] [Epi u] in
/-- The classifying morphism of `ρ_c` pulls back `ρ_c`. -/
theorem exists_overQuotientMap_splitClassifyingMorphism_comp (g : T ⟶ X)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    ∃ α : (Scheme.Modules.pullback (S.splitClassifyingMorphism g c)).obj
        (tautologicalDatum F).twist ≅ Scheme.unitModule T,
      (tautologicalDatum F).overQuotientMap (S.splitClassifyingMorphism g c)
          (S.splitClassifyingMorphism_comp g c) ≫ α.hom = S.splitQuotientMap c := by
  obtain ⟨α, hα⟩ := (tautologicalDatum F).overQuotient_classifyingMorphismOver_isEquivalent
    ((Scheme.Modules.pullback g).obj F) (Iso.refl _) (S.splitQuotient c)
  refine ⟨α, ?_⟩
  simp only [TautologicalDatum.overQuotient_q, Iso.refl_hom, Category.id_comp,
    splitQuotient_q] at hα
  exact hα

/-- The classifying morphism of `ρ_c` lands in the complement `U`. -/
theorem range_splitClassifyingMorphism_subset (g : T ⟶ X)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    Set.range (S.splitClassifyingMorphism g c).base ⊆ splitQuotientComplement u := by
  obtain ⟨α, hα⟩ := S.exists_overQuotientMap_splitClassifyingMorphism_comp g c
  exact S.range_subset_of_overQuotientMap_comp_eq _ _ c α hα

/-- **The classifying morphism of `ρ_c` has coordinates `c`.** -/
theorem splitCoordMap_splitClassifyingMorphism (g : T ⟶ X)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    S.splitCoordMap (S.splitClassifyingMorphism g c) (S.splitClassifyingMorphism_comp g c)
      (S.range_splitClassifyingMorphism_subset g c) = c := by
  obtain ⟨α, hα⟩ := S.exists_overQuotientMap_splitClassifyingMorphism_comp g c
  exact S.splitCoordMap_eq_of_overQuotientMap_comp_eq _ _ _ c α hα

/-- **A morphism into `U` over `g` is the classifying morphism of its coordinates.** -/
theorem splitClassifyingMorphism_splitCoordMap (f : T ⟶ projectiveBundle X F) {g : T ⟶ X}
    (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    S.splitClassifyingMorphism g (S.splitCoordMap f hg hf) = f :=
  S.eq_of_splitCoordMap_eq _ _ (S.splitClassifyingMorphism_comp g _) hg
    (S.range_splitClassifyingMorphism_subset g _) hf
    (S.splitCoordMap_splitClassifyingMorphism g _)

end Classifying

/-! ### Pulling back along a morphism of test schemes -/

section Naturality

variable [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] {T T' : Scheme.{u}} {g : T ⟶ X}

/-- **The quotient a composite pulls back** is the pullback of the quotient. -/
theorem overQuotientMap_comp (k : T' ⟶ T) (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g) (hg' : (k ≫ f) ≫ projectiveBundleToBase X F = k ≫ g) :
    (tautologicalDatum F).overQuotientMap (k ≫ f) hg' =
      (Scheme.Modules.pullbackComp k g).inv.app F ≫
        (Scheme.Modules.pullback k).map ((tautologicalDatum F).overQuotientMap f hg) ≫
        (Scheme.Modules.pullbackComp k f).hom.app (tautologicalDatum F).twist := by
  subst hg
  have hA := Stacks.Modules.pullbackComp_congr_assoc k f (projectiveBundleToBase X F) (k ≫ f) rfl
    (f ≫ projectiveBundleToBase X F) rfl (k ≫ f ≫ projectiveBundleToBase X F)
    (Category.assoc _ _ _) F
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hA
  have key : (Scheme.Modules.pullbackCongr hg').inv.app F ≫
      (Scheme.Modules.pullbackComp (k ≫ f) (projectiveBundleToBase X F)).inv.app F =
      (Scheme.Modules.pullbackComp k (f ≫ projectiveBundleToBase X F)).inv.app F ≫
        (Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackComp f (projectiveBundleToBase X F)).inv.app F) ≫
        (Scheme.Modules.pullbackComp k f).hom.app
          ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F) := by
    rw [← cancel_epi ((Scheme.Modules.pullback k).map
      ((Scheme.Modules.pullbackComp f (projectiveBundleToBase X F)).hom.app F) ≫
        (Scheme.Modules.pullbackComp k (f ≫ projectiveBundleToBase X F)).hom.app F),
      Category.assoc, reassoc_of% hA]
    simp [Scheme.Modules.pullbackCongr, ← Functor.map_comp_assoc]
  have n := (Scheme.Modules.pullbackComp k f).hom.naturality (tautologicalDatum F).univ
  simp only [Functor.comp_map] at n
  simp only [TautologicalDatum.overQuotientMap, Functor.map_comp, Category.assoc, n]
  rw [reassoc_of% key]
  simp [Scheme.Modules.pullbackCongr]

/-- The pullback along `k : T' ⟶ T` of a morphism `c : g^*G ⟶ 𝒪_T`, read as a morphism
`(k ≫ g)^*G ⟶ 𝒪_{T'}`. -/
def pullbackCoordMap (k : T' ⟶ T) (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    (Scheme.Modules.pullback (k ≫ g)).obj G ⟶ Scheme.unitModule T' :=
  (Scheme.Modules.pullbackComp k g).inv.app G ≫ (Scheme.Modules.pullback k).map c ≫
    (Scheme.Modules.pullbackUnitIso k).hom

omit [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] in
/-- **`ρ` commutes with pullback.** -/
theorem pullback_map_splitQuotientMap (k : T' ⟶ T)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) :
    (Scheme.Modules.pullbackComp k g).inv.app F ≫
        (Scheme.Modules.pullback k).map (S.splitQuotientMap c) ≫
        (Scheme.Modules.pullbackUnitIso k).hom =
      S.splitQuotientMap (pullbackCoordMap k c) := by
  have n₁ := (Scheme.Modules.pullbackComp k g).inv.naturality S.τ
  have n₂ := (Scheme.Modules.pullbackComp k g).inv.naturality u
  simp only [Functor.comp_map] at n₁ n₂
  have hU := Scheme.Modules.pullbackUnitIso_comp k g
  simp only [splitQuotientMap, pullbackCoordMap, Functor.map_add, Functor.map_comp,
    Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
  rw [← reassoc_of% n₁, ← reassoc_of% n₂, hU]

/-- **The coordinates of a composite** are the pullback of the coordinates. -/
theorem splitCoordMap_comp (k : T' ⟶ T) (f : T ⟶ projectiveBundle X F)
    (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u)
    (hg' : (k ≫ f) ≫ projectiveBundleToBase X F = k ≫ g)
    (hf' : Set.range (k ≫ f).base ⊆ splitQuotientComplement u) :
    S.splitCoordMap (k ≫ f) hg' hf' = pullbackCoordMap k (S.splitCoordMap f hg hf) := by
  refine S.splitCoordMap_eq_of_overQuotientMap_comp_eq _ _ _ _
    (((Scheme.Modules.pullbackComp k f).app (tautologicalDatum F).twist).symm ≪≫
      (Scheme.Modules.pullback k).mapIso
        ((S.splitHyperplaneIso f hg hf).symm ≪≫ Scheme.Modules.pullbackUnitIso g) ≪≫
      Scheme.Modules.pullbackUnitIso k) ?_
  rw [overQuotientMap_comp k f hg hg', ← S.pullback_map_splitQuotientMap k,
    ← S.overQuotientMap_comp_eq_splitQuotientMap f hg hf]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc, Functor.map_comp]

end Naturality

/-! ### Morphisms out of the pullback of a free module -/

section Vectors

variable {ι : Type u} (e : SheafOfModules.free (R := X.ringCatSheaf) ι ≅ G)
  {T T' : Scheme.{u}} {g : T ⟶ X}

/-- **The `j`-th basis vector `k_j : 𝒪_X ⟶ G`** of a basis `e : 𝒪_X^{⊕ ι} ≅ G`. -/
def basisMap (j : ι) : Scheme.unitModule X ⟶ G :=
  SheafOfModules.ιFree j ≫ e.hom

/-- An endomorphism of `𝒪_T` is multiplication by its value on `1`. -/
theorem unitHomEquivTop_app_top_eq_self (φ : Scheme.unitModule T ⟶ Scheme.unitModule T) :
    Scheme.Modules.unitHomEquivTop (Scheme.unitModule T) (φ.app ⊤ (1 : Γ(T, ⊤))) = φ :=
  (Scheme.Modules.unitHomEquivTop (Scheme.unitModule T)).apply_symm_apply φ

/-- The presheaf of a module sends every endomorphism of `⊤` to the identity. -/
private theorem presheaf_map_top_apply (M : T.Modules) (a : op (⊤ : T.Opens) ⟶ op (⊤ : T.Opens))
    (t : Γ(M, ⊤)) : M.presheaf.map a t = t := by
  rw [Subsingleton.elim a (𝟙 _), M.presheaf.map_id, ConcreteCategory.id_apply]

/-- The morphism out of `𝒪_T` of a global section `a` sends the unit section to `a`. -/
theorem unitHomEquivTop_app_top_of_eq_one (M : T.Modules) (a : Γ(M, ⊤)) (r : Γ(T, ⊤))
    (hr : r = 1) : (Scheme.Modules.unitHomEquivTop M a).app ⊤ r = a := by
  subst hr
  have h2 : (Scheme.Modules.unitHomEquivTop M a).app ⊤ (1 : Γ(T, ⊤)) =
      (SheafOfModules.unitHomEquiv M (Scheme.Modules.unitHomEquivTop M a)).val (op ⊤) := rfl
  rw [h2, Scheme.Modules.unitHomEquiv_unitHomEquivTop, Scheme.Modules.sectionsTopEquiv_val]
  exact presheaf_map_top_apply M _ _

/-- **Pulling back an endomorphism of the structure sheaf pulls back its function.** -/
theorem pullback_map_unitModule_app_top_one (k : T' ⟶ T)
    (φ : Scheme.unitModule T ⟶ Scheme.unitModule T) :
    ((Scheme.Modules.pullbackUnitIso k).inv ≫ (Scheme.Modules.pullback k).map φ ≫
        (Scheme.Modules.pullbackUnitIso k).hom).app ⊤ (1 : Γ(T', ⊤)) =
      k.appTop (φ.app ⊤ (1 : Γ(T, ⊤))) := by
  have h := Scheme.Modules.pullbackUnitIso_sections_naturality k (Scheme.unitModule T)
    (Scheme.unitModule T') (Scheme.Modules.pullbackUnitIso k).hom (φ.app ⊤ (1 : Γ(T, ⊤)))
  rw [unitHomEquivTop_app_top_eq_self, Scheme.Modules.pullbackUnitIso_homEquiv] at h
  rw [← h, Iso.inv_hom_id_assoc, unitHomEquivTop_app_top_of_eq_one _ _ _ rfl]
  exact presheaf_map_top_apply _ _ _

/-- **The coordinate vector of a morphism `c : g^*G ⟶ 𝒪_T`**: its values `c(g^*k_j)` on the
pulled-back basis vectors `k_j` of `G`, as global functions on `T`. -/
def coordVector (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) : ι → Γ(T, ⊤) :=
  fun j => ((Scheme.Modules.pullbackUnitIso g).inv ≫
    (Scheme.Modules.pullback g).map (basisMap e j) ≫ c).app ⊤ (1 : Γ(T, ⊤))

/-- **The coordinate vector commutes with pullback.** -/
theorem coordVector_pullbackCoordMap (k : T' ⟶ T)
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) (j : ι) :
    coordVector e (pullbackCoordMap k c) j = k.appTop (coordVector e c j) := by
  have hU := Scheme.Modules.pullbackUnitIso_comp k g
  have hU' : (Scheme.Modules.pullbackUnitIso (k ≫ g)).inv ≫
      (Scheme.Modules.pullbackComp k g).inv.app (Scheme.unitModule X) =
      (Scheme.Modules.pullbackUnitIso k).inv ≫
        (Scheme.Modules.pullback k).map (Scheme.Modules.pullbackUnitIso g).inv := by
    rw [Iso.inv_comp_eq, ← hU]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have n := (Scheme.Modules.pullbackComp k g).inv.naturality (basisMap e j)
  simp only [Functor.comp_map] at n
  have e' : (Scheme.Modules.pullbackUnitIso (k ≫ g)).inv ≫
      (Scheme.Modules.pullback (k ≫ g)).map (basisMap e j) ≫
        pullbackCoordMap k c =
      (Scheme.Modules.pullbackUnitIso k).inv ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackUnitIso g).inv ≫
          (Scheme.Modules.pullback g).map (basisMap e j) ≫ c) ≫
        (Scheme.Modules.pullbackUnitIso k).hom := by
    rw [pullbackCoordMap, reassoc_of% n, reassoc_of% hU']
    simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun φ => φ.app ⊤ (1 : Γ(T', ⊤))) e').trans
    (pullback_map_unitModule_app_top_one k _)

/-- The pullback of the basis presents `g^*G` as a coproduct of copies of `g^*𝒪_X`. -/
def isColimitPullbackBasis (g : T ⟶ X) :
    IsColimit (Cofan.mk ((Scheme.Modules.pullback g).obj G) fun j : ι =>
      (Scheme.Modules.pullback g).map (basisMap e j)) :=
  have hc : IsColimit (Cofan.mk G (basisMap e)) :=
    IsColimit.ofIsoColimit (SheafOfModules.isColimitFreeCofan ι) (Cofan.ext e fun _ => rfl)
  isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback g) _ _ hc

/-- **The morphism `g^*G ⟶ 𝒪_T` with prescribed coordinate vector `v`.** -/
def ofCoordVector (g : T ⟶ X) (v : ι → Γ(T, ⊤)) :
    (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T :=
  Cofan.IsColimit.desc (isColimitPullbackBasis e g) fun j =>
    (Scheme.Modules.pullbackUnitIso g).hom ≫
      Scheme.Modules.unitHomEquivTop (Scheme.unitModule T) (v j)

/-- The morphism with prescribed coordinate vector `v` has coordinate vector `v`. -/
theorem coordVector_ofCoordVector (g : T ⟶ X) (v : ι → Γ(T, ⊤)) :
    coordVector e (ofCoordVector e g v) = v := by
  funext j
  have h : (Scheme.Modules.pullback g).map (basisMap e j) ≫
      ofCoordVector e g v = (Scheme.Modules.pullbackUnitIso g).hom ≫
        Scheme.Modules.unitHomEquivTop (Scheme.unitModule T) (v j) :=
    Cofan.IsColimit.fac (isColimitPullbackBasis e g) (fun j =>
      (Scheme.Modules.pullbackUnitIso g).hom ≫
        Scheme.Modules.unitHomEquivTop (Scheme.unitModule T) (v j)) j
  rw [coordVector, h, Iso.inv_hom_id_assoc]
  exact unitHomEquivTop_app_top_of_eq_one _ _ _ rfl

/-- A morphism `g^*G ⟶ 𝒪_T` is determined by its coordinate vector. -/
theorem coordVector_injective (g : T ⟶ X) :
    Function.Injective (coordVector (T := T) (g := g) e) := by
  intro c c' h
  refine Cofan.IsColimit.hom_ext (isColimitPullbackBasis e g) _ _ fun j => ?_
  have hj := congrFun h j
  have key : (Scheme.Modules.pullback g).map (basisMap e j) ≫ c =
      (Scheme.Modules.pullback g).map (basisMap e j) ≫ c' := by
    rw [← cancel_epi (Scheme.Modules.pullbackUnitIso g).inv,
      ← unitHomEquivTop_app_top_eq_self (_ ≫ _ ≫ c),
      ← unitHomEquivTop_app_top_eq_self ((Scheme.Modules.pullbackUnitIso g).inv ≫ _ ≫ c')]
    exact congrArg _ hj
  exact key

end Vectors

/-! ### The coordinate vector of a morphism into the complement -/

section CoordVector

variable [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] {ι : Type u}
  (e : SheafOfModules.free (R := X.ringCatSheaf) ι ≅ G) {T T' : Scheme.{u}}

/-- **The coordinates of a morphism `f : T ⟶ 𝐏(F)` landing in `U`**: the global functions
`λ(σ'(k_j)) / λ(σ)` on `T`, i.e. the coordinate vector of `c_f`. -/
def splitCoordVector (f : T ⟶ projectiveBundle X F)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) : ι → Γ(T, ⊤) :=
  coordVector e (S.splitCoordMap f rfl hf)

/-- The coordinate vector of `c_f` is the coordinate vector of `f`, for any `g` with
`f ≫ projectiveBundleToBase X F = g`. -/
theorem coordVector_splitCoordMap (f : T ⟶ projectiveBundle X F) {g : T ⟶ X}
    (hg : f ≫ projectiveBundleToBase X F = g)
    (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    coordVector e (S.splitCoordMap f hg hf) = S.splitCoordVector e f hf := by
  subst hg
  rfl

/-- Equal morphisms into `U` have equal coordinates. -/
theorem splitCoordVector_congr {f₁ f₂ : T ⟶ projectiveBundle X F} (h : f₁ = f₂)
    (hf₁ : Set.range f₁.base ⊆ splitQuotientComplement u)
    (hf₂ : Set.range f₂.base ⊆ splitQuotientComplement u) :
    S.splitCoordVector e f₁ hf₁ = S.splitCoordVector e f₂ hf₂ := by
  subst h
  rfl

/-- **Two morphisms into `U` over the same morphism to `X`, with the same coordinates, are
equal.** -/
theorem eq_of_splitCoordVector_eq (f₁ f₂ : T ⟶ projectiveBundle X F)
    (h : f₁ ≫ projectiveBundleToBase X F = f₂ ≫ projectiveBundleToBase X F)
    (hf₁ : Set.range f₁.base ⊆ splitQuotientComplement u)
    (hf₂ : Set.range f₂.base ⊆ splitQuotientComplement u)
    (hv : S.splitCoordVector e f₁ hf₁ = S.splitCoordVector e f₂ hf₂) : f₁ = f₂ :=
  S.eq_of_splitCoordMap_eq f₁ f₂ h rfl hf₁ hf₂ (coordVector_injective e _
    ((S.coordVector_splitCoordMap e f₁ h hf₁).trans hv))

/-- **The coordinates of a composite `k ≫ f` are the pullbacks along `k` of those of `f`.** -/
theorem splitCoordVector_comp (k : T' ⟶ T) (f : T ⟶ projectiveBundle X F)
    (hf : Set.range f.base ⊆ splitQuotientComplement u)
    (hf' : Set.range (k ≫ f).base ⊆ splitQuotientComplement u) (j : ι) :
    S.splitCoordVector e (k ≫ f) hf' j = k.appTop (S.splitCoordVector e f hf j) := by
  rw [← S.coordVector_splitCoordMap e (k ≫ f) (Category.assoc _ _ _) hf',
    S.splitCoordMap_comp k f rfl hf (Category.assoc _ _ _) hf', coordVector_pullbackCoordMap]
  rfl

/-- **The classifying morphism of `ρ_c`, for `c` with coordinate vector `v`, has coordinates
`v`.** -/
theorem splitCoordVector_splitClassifyingMorphism (g : T ⟶ X) (v : ι → Γ(T, ⊤)) :
    S.splitCoordVector e (S.splitClassifyingMorphism g (ofCoordVector e g v))
        (S.range_splitClassifyingMorphism_subset g _) = v := by
  rw [← S.coordVector_splitCoordMap e _ (S.splitClassifyingMorphism_comp g _),
    splitCoordMap_splitClassifyingMorphism, coordVector_ofCoordVector]

end CoordVector

/-! ### The complement is an affine space -/

section AffineSpace

variable [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] {ι : Type u}
  (e : SheafOfModules.free (R := X.ringCatSheaf) ι ≅ G)

/-- A composite with a morphism landing in `U` lands in `U`. -/
theorem range_comp_subset_splitQuotientComplement {T T' : Scheme.{u}} (k : T' ⟶ T)
    (f : T ⟶ projectiveBundle X F) (hf : Set.range f.base ⊆ splitQuotientComplement u) :
    Set.range (k ≫ f).base ⊆ splitQuotientComplement u := by
  rintro _ ⟨p, rfl⟩
  exact hf ⟨k.base p, rfl⟩

/-- The inclusion `U ⟶ 𝐏(F)` lands in `U`. -/
theorem range_splitQuotientComplement_ι :
    Set.range (splitQuotientComplement u).ι.base ⊆ splitQuotientComplement u := by
  rw [Scheme.Opens.range_ι]

/-- **The coordinates on `U = 𝐏(F) ∖ i(𝐏(G))`**: the global functions `λ(σ'(k_j)) / λ(σ)` of the
inclusion `U ⟶ 𝐏(F)`. -/
def splitQuotientComplementCoord : ι → Γ((splitQuotientComplement u).toScheme, ⊤) :=
  S.splitCoordVector e (splitQuotientComplement u).ι range_splitQuotientComplement_ι

/-- The morphism `𝔸(ι; X) ⟶ 𝐏(F)` over `X` classifying the quotient `ρ` of the coordinate
functions. -/
def affineSpaceToProjectiveBundle : 𝔸(ι; X) ⟶ projectiveBundle X F :=
  S.splitClassifyingMorphism (𝔸(ι; X) ↘ X) (ofCoordVector e _ (AffineSpace.coord X))

/-- The morphism `𝔸(ι; X) ⟶ 𝐏(F)` lands in `U`. -/
theorem range_affineSpaceToProjectiveBundle_subset :
    Set.range (S.affineSpaceToProjectiveBundle e).base ⊆ splitQuotientComplement u :=
  S.range_splitClassifyingMorphism_subset _ _

omit [G.IsQuasicoherent] [Epi u] in
/-- The morphism `𝔸(ι; X) ⟶ 𝐏(F)` lies over `X`. -/
theorem affineSpaceToProjectiveBundle_comp :
    S.affineSpaceToProjectiveBundle e ≫ projectiveBundleToBase X F = 𝔸(ι; X) ↘ X :=
  S.splitClassifyingMorphism_comp _ _

/-- The coordinates of the morphism `𝔸(ι; X) ⟶ 𝐏(F)` are the coordinate functions of
`𝔸(ι; X)`. -/
theorem splitCoordVector_affineSpaceToProjectiveBundle :
    S.splitCoordVector e (S.affineSpaceToProjectiveBundle e)
        (S.range_affineSpaceToProjectiveBundle_subset e) = AffineSpace.coord X :=
  S.splitCoordVector_splitClassifyingMorphism e _ _

/-- **The complement of the projective bundle of a free split quotient is an affine space.** For
a split short exact sequence `0 ⟶ 𝒪_X ⟶ F ⟶ G ⟶ 0` with `G` free with basis
`e : 𝒪_X^{⊕ ι} ≅ G`, the open complement `U = 𝐏(F) ∖ i(𝐏(G))` of the closed immersion
`i : 𝐏(G) ⟶ 𝐏(F)` is isomorphic over `X` to `𝔸(ι; X)`, the coordinates being
`λ(σ'(k_j)) / λ(σ)` (`Stacks.RelativeProj.UnitSplitting.splitQuotientComplementCoord`). -/
def splitQuotientComplementIso : (splitQuotientComplement u).toScheme ≅ 𝔸(ι; X) where
  hom := AffineSpace.homOfVector ((splitQuotientComplement u).ι ≫ projectiveBundleToBase X F)
    (S.splitQuotientComplementCoord e)
  inv := IsOpenImmersion.lift (splitQuotientComplement u).ι (S.affineSpaceToProjectiveBundle e)
    (by rw [Scheme.Opens.range_ι]; exact S.range_affineSpaceToProjectiveBundle_subset e)
  hom_inv_id := by
    rw [← cancel_mono (splitQuotientComplement u).ι, Category.assoc, IsOpenImmersion.lift_fac,
      Category.id_comp]
    refine S.eq_of_splitCoordVector_eq e _ _ ?_
      (range_comp_subset_splitQuotientComplement _ _
        (S.range_affineSpaceToProjectiveBundle_subset e))
      range_splitQuotientComplement_ι ?_
    · rw [Category.assoc, affineSpaceToProjectiveBundle_comp, AffineSpace.homOfVector_over]
    · funext j
      rw [S.splitCoordVector_comp e _ _ (S.range_affineSpaceToProjectiveBundle_subset e)
        (range_comp_subset_splitQuotientComplement _ _
          (S.range_affineSpaceToProjectiveBundle_subset e)),
        splitCoordVector_affineSpaceToProjectiveBundle, AffineSpace.homOfVector_appTop_coord]
      rfl
  inv_hom_id := by
    refine AffineSpace.hom_ext ?_ fun j => ?_
    · rw [Category.assoc, AffineSpace.homOfVector_over, IsOpenImmersion.lift_fac_assoc,
        affineSpaceToProjectiveBundle_comp, Category.id_comp]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord,
        Scheme.Hom.id_appTop, CommRingCat.id_apply]
      have h := S.splitCoordVector_comp e (IsOpenImmersion.lift (splitQuotientComplement u).ι
        (S.affineSpaceToProjectiveBundle e)
        (by rw [Scheme.Opens.range_ι]; exact S.range_affineSpaceToProjectiveBundle_subset e))
        (splitQuotientComplement u).ι range_splitQuotientComplement_ι
        (by rw [IsOpenImmersion.lift_fac]; exact S.range_affineSpaceToProjectiveBundle_subset e) j
      rw [S.splitCoordVector_congr e (IsOpenImmersion.lift_fac _ _ _) _
        (S.range_affineSpaceToProjectiveBundle_subset e),
        splitCoordVector_affineSpaceToProjectiveBundle] at h
      exact h.symm

/-- The morphism `U ⟶ 𝔸(ι; X)` is given by the coordinates on `U`. -/
theorem splitQuotientComplementIso_hom :
    (S.splitQuotientComplementIso e).hom = AffineSpace.homOfVector
      ((splitQuotientComplement u).ι ≫ projectiveBundleToBase X F)
      (S.splitQuotientComplementCoord e) :=
  rfl

/-- **The isomorphism `U ≅ 𝔸(ι; X)` is over `X`.** -/
@[reassoc (attr := simp)]
theorem splitQuotientComplementIso_hom_over :
    (S.splitQuotientComplementIso e).hom ≫ 𝔸(ι; X) ↘ X =
      (splitQuotientComplement u).ι ≫ projectiveBundleToBase X F :=
  AffineSpace.homOfVector_over _ _

/-- **The coordinates of `U ≅ 𝔸(ι; X)`**: the `j`-th coordinate function of `𝔸(ι; X)` pulls back
to `λ(σ'(k_j)) / λ(σ)`. -/
@[simp]
theorem splitQuotientComplementIso_hom_appTop_coord (j : ι) :
    (S.splitQuotientComplementIso e).hom.appTop (AffineSpace.coord X j) =
      S.splitQuotientComplementCoord e j :=
  AffineSpace.homOfVector_appTop_coord _ _ j

/-- **The inverse `𝔸(ι; X) ⟶ U ⟶ 𝐏(F)`** classifies the quotient `ρ` of the coordinate
functions. -/
@[reassoc (attr := simp)]
theorem splitQuotientComplementIso_inv_ι :
    (S.splitQuotientComplementIso e).inv ≫ (splitQuotientComplement u).ι =
      S.affineSpaceToProjectiveBundle e :=
  IsOpenImmersion.lift_fac _ _ _

end AffineSpace

end UnitSplitting

end Stacks.RelativeProj

end
