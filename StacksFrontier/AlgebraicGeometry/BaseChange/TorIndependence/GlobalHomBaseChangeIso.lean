module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsPullback
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalHomBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedChangeOfCoefficients
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPerfectHomQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedPullbackAmplitude
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackTensorDual
import StacksCore.Tactic.StacksAttribute

/-!
# Tor-independent base change for global derived hom complexes

Consider a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Spec R' --> Spec R
```

of quasi-compact and quasi-separated schemes with `X` and `Spec R'` Tor independent over
`Spec R`.  For `M, K ∈ D(𝒪_X)` the global hom complex `R Hom_X(M, K) = RΓ(X, R𝓗om(M, K))` of
Cohomology, Section 0B6A is an object of `D(R)`, and the canonical map of global hom complexes
along `g'`, read in `D(R)` and transposed along `- ⊗^𝐋_R R' ⊣ res`, is a map

`R Hom_X(M, K) ⊗^𝐋_R R' ⟶ R Hom_{X'}(L(g')^*M, L(g')^*K)`

of `D(R')`.  It is an isomorphism when `M` is perfect and `K ∈ D_QCoh(𝒪_X)`, and when `M` is
pseudo-coherent, `K ∈ D^+_QCoh(𝒪_X)` and `R'` has finite Tor dimension over `R` (Stacks 0AA7).
The proof factors the map as the base change map `RΓ(X, E) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*E)` at
`E = R𝓗om(M, K)`, which is invertible for `E ∈ D_QCoh(𝒪_X)` by Stacks 08IB and the affine case
of the Leray comparison, followed by derived global sections of the map of Stacks 08I3, which is
invertible by Stacks 0GM7; `R𝓗om(M, K)` has quasi-coherent cohomology by Stacks 0A6H.  The map
of Stacks 0AA7 at `K = Rg'_*L` followed by the map induced by the counit `L(g')^*Rg'_*L ⟶ L` is
the multiplication map, read through the identification
`R Hom_X(M, Rg'_*L) ≅ R Hom_{X'}(L(g')^*M, L)` given by derived global sections of the derived
adjunction isomorphism `R𝓗om(M, Rg'_*L) ≅ Rg'_*R𝓗om(L(g')^*M, L)` (Stacks 0BZA).

## Main definitions

All declarations below live in the namespace `AlgebraicGeometry.GlobalHomBaseChange`.

* `sectionsBaseChangeMap`: the base change map `RΓ(X, E) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*E)`.
* `globalHom`: `R Hom_X(M, K)` as an object of `D(R)`.
* `globalHomBaseChangeMap`: the map of Stacks 0AA7.
* `globalHomAdjunctionMap`: the canonical map `R Hom_X(M, Rg'_*L) ⟶ R Hom_{X'}(L(g')^*M, L)` of
  `D(R)`.

## Main results

* `isIso_sectionsBaseChangeMap`: Tor-independent base change for derived global sections of
  objects of `D_QCoh(𝒪_X)`.
* `isIso_globalHomBaseChangeMap_of_isPerfect`: Stacks 0AA7, case (1).
* `isIso_globalHomBaseChangeMap_of_isPseudoCoherent`: Stacks 0AA7, case (2).
* `isIso_unit_comp_map_homComparison`: for an adjunction `P ⊣ Q` and internal homs with natural
  tensor–hom bijections, `hom(M, Q L) ⟶ Q hom(P M, L)` is an isomorphism.
* `isIso_derivedHomAdjunctionMap`: the derived adjunction isomorphism
  `R𝓗om(M, Rh_*L) ≅ Rh_*R𝓗om(Lh^*M, L)` for a morphism of ringed spaces.
* `isIso_globalHomAdjunctionMap`: the map `R Hom_X(M, Rg'_*L) ⟶ R Hom_{X'}(L(g')^*M, L)` is an
  isomorphism.
* `isIso_globalHomAdjunctionMap_and_globalHomBaseChangeMap_comp_counit`: Stacks 0BZA.

## References

* [Stacks Project, Tag 0AA7](https://stacks.math.columbia.edu/tag/0AA7)
* [Stacks Project, Tag 0BZA](https://stacks.math.columbia.edu/tag/0BZA)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.GlobalHomBaseChange

universe u

/-! ### Transposes of a map out of a right adjoint, abstractly -/

section Mates

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  {L : C ⥤ D} {Γ : D ⥤ C} (aR : L ⊣ Γ) {L' : C' ⥤ D'} {Γ' : D' ⥤ C'} (aR' : L' ⊣ Γ')
  {Lg : D ⥤ D'} {Rg : D' ⥤ D} (ag : Lg ⊣ Rg) {ext : C ⥤ C'} {res : C' ⥤ C} (ae : ext ⊣ res)
  (α : Rg ⋙ Γ ≅ Γ' ⋙ res)

/-- The transpose `ext(Γ N) ⟶ Γ'(Lg N)` of the map `Γ N ⟶ Γ(Rg Lg N) ≅ res Γ'(Lg N)`. -/
def transposeMap (N : D) : ext.obj (Γ.obj N) ⟶ Γ'.obj (Lg.obj N) :=
  (ae.homEquiv (Γ.obj N) (Γ'.obj (Lg.obj N))).symm
    (Γ.map (ag.unit.app N) ≫ α.hom.app (Lg.obj N))

/-- The adjoint of `transposeMap` under `ext ⊣ res` is `Γ N ⟶ Γ(Rg Lg N) ≅ res Γ'(Lg N)`. -/
theorem homEquiv_transposeMap (N : D) :
    ae.homEquiv _ _ (transposeMap ag ae α N) = Γ.map (ag.unit.app N) ≫ α.hom.app (Lg.obj N) := by
  simp [transposeMap]

/-- `transposeMap` is natural in `N`. -/
theorem transposeMap_naturality {N N' : D} (h : N ⟶ N') :
    ext.map (Γ.map h) ≫ transposeMap ag ae α N' = transposeMap ag ae α N ≫ Γ'.map (Lg.map h) := by
  apply (ae.homEquiv _ _).injective
  rw [ae.homEquiv_naturality_left, ae.homEquiv_naturality_right, homEquiv_transposeMap,
    homEquiv_transposeMap]
  have h₁ := ag.unit.naturality h
  have h₂ := α.hom.naturality (Lg.map h)
  dsimp at h₁ h₂
  rw [← Γ.map_comp_assoc, h₁, Γ.map_comp_assoc, h₂, Category.assoc]

/-- **The transpose is invertible at the image of the left adjoint.**  If the units of `L ⊣ Γ` and
of `L' ⊣ Γ'` are invertible, then at `L M` the transpose is, up to these units, `Γ'` of the
conjugate of `α`, an isomorphism between left adjoints. -/
theorem isIso_transposeMap_obj [IsIso aR.unit] [IsIso aR'.unit] (M : C) :
    IsIso (transposeMap ag ae α (L.obj M)) := by
  let τ := ((conjugateIsoEquiv (aR.comp ag) (ae.comp aR')).symm α).hom
  have hτ : IsIso τ := inferInstance
  have key := unit_conjugateEquiv_symm (aR.comp ag) (ae.comp aR') α.hom M
  have hτ' : (conjugateEquiv (aR.comp ag) (ae.comp aR')).symm α.hom = τ := rfl
  rw [hτ'] at key
  simp only [Adjunction.comp_unit_app, Category.assoc, Functor.comp_map] at key
  have h : ext.map (aR.unit.app M) ≫ transposeMap ag ae α (L.obj M) =
      aR'.unit.app (ext.obj M) ≫ Γ'.map (τ.app M) := by
    apply (ae.homEquiv _ _).injective
    rw [ae.homEquiv_naturality_left]
    have e₁ : ae.homEquiv (Γ.obj (L.obj M)) (Γ'.obj (Lg.obj (L.obj M)))
        (transposeMap ag ae α (L.obj M)) =
        Γ.map (ag.unit.app (L.obj M)) ≫ α.hom.app (Lg.obj (L.obj M)) :=
      homEquiv_transposeMap ag ae α (L.obj M)
    have e₂ : ae.homEquiv M (Γ'.obj (Lg.obj (L.obj M)))
        (aR'.unit.app (ext.obj M) ≫ Γ'.map (τ.app M)) =
        ae.unit.app M ≫ res.map (aR'.unit.app (ext.obj M)) ≫ res.map (Γ'.map (τ.app M)) := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp]
    exact (congrArg (fun x => aR.unit.app M ≫ x) e₁).trans (key.trans e₂.symm)
  have : IsIso (aR'.unit.app (ext.obj M) ≫ Γ'.map (τ.app M)) := inferInstance
  rw [← h] at this
  exact IsIso.of_isIso_comp_left (ext.map (aR.unit.app M)) _

/-- **The transpose is invertible wherever the counit of `L ⊣ Γ` is.** -/
theorem isIso_transposeMap [IsIso aR.unit] [IsIso aR'.unit] (N : D) [IsIso (aR.counit.app N)] :
    IsIso (transposeMap ag ae α N) := by
  have h₁ := isIso_transposeMap_obj aR aR' ag ae α (Γ.obj N)
  have h₂ := transposeMap_naturality ag ae α (aR.counit.app N)
  have : IsIso (ext.map (Γ.map (aR.counit.app N)) ≫ transposeMap ag ae α N) := by
    have h₃ : ext.map (Γ.map (aR.counit.app N)) ≫ transposeMap ag ae α N =
        transposeMap ag ae α (L.obj (Γ.obj N)) ≫ Γ'.map (Lg.map (aR.counit.app N)) := h₂
    rw [h₃]; infer_instance
  exact IsIso.of_isIso_comp_left (ext.map (Γ.map (aR.counit.app N))) _

/-- **Invertibility of a transpose from a factorization.**  If `i ≫ θ` factors as
`sp ≫ Γb ≫ lτ ≫ μX`, and `lτ ≫ μX`, `Γb ≫ μS₁` and `sp ≫ μS₀` are re-expressed through `μS₁`,
`res bb` and the transpose `t`, then the transpose of `θ` is `ext i⁻¹ ≫ t ≫ bb ≫ lσ`. -/
theorem isIso_homEquiv_symm_of_factorization {C C' : Type*} [Category C] [Category C']
    {ext : C ⥤ C'} {res : C' ⥤ C} (ae : ext ⊣ res)
    {A A' Y₁ Z₀ Z₁ : C} {B B₀ B₁ : C'} (θ : A ⟶ res.obj B) (i : A' ⟶ A) [IsIso i]
    (sq₁ : A ⟶ Y₁) (μX : Y₁ ⟶ res.obj B) (hθ : θ = sq₁ ≫ μX)
    (sp : A' ⟶ Z₀) (Γb : Z₀ ⟶ Z₁) (lτ : Z₁ ⟶ Y₁) (hC₁ : i ≫ sq₁ = sp ≫ Γb ≫ lτ)
    (μS₀ : Z₀ ⟶ res.obj B₀) (μS₁ : Z₁ ⟶ res.obj B₁) (lσ : B₁ ⟶ B)
    (hC₂ : lτ ≫ μX = μS₁ ≫ res.map lσ) (bb : B₀ ⟶ B₁) (hn : Γb ≫ μS₁ = μS₀ ≫ res.map bb)
    (t : ext.obj A' ⟶ B₀) (ht : ae.homEquiv _ _ t = sp ≫ μS₀) [IsIso t] [IsIso bb] [IsIso lσ] :
    IsIso ((ae.homEquiv A B).symm θ) := by
  have h : θ = inv i ≫ ae.homEquiv _ _ t ≫ res.map (bb ≫ lσ) := by
    rw [← cancel_epi i, IsIso.hom_inv_id_assoc, hθ, reassoc_of% hC₁, hC₂, ht, Category.assoc,
      reassoc_of% hn, res.map_comp]
  have h' : (ae.homEquiv A B).symm θ = ext.map (inv i) ≫ t ≫ bb ≫ lσ := by
    rw [h, ← ae.homEquiv_naturality_right, ← ae.homEquiv_naturality_left, Equiv.symm_apply_apply]
  rw [h']
  infer_instance

end Mates

/-! ### The adjunction isomorphism for internal homs, abstractly -/

section HomAdjunction

open Stacks.Cohomology.DerivedInternalHomPullback
open scoped CategoryTheory.Prod

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] {P : D₁ ⥤ D₂} {Q : D₂ ⥤ D₁} (adj : P ⊣ Q)
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂) (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- **The map `hom(M, Q L) ⟶ Q hom(P M, L)` read on morphisms out of a test object `Z`.**  For
`P ⊣ Q` and internal homs with tensor–hom bijections natural in the source variable (and, on the
target, in the internal-hom variable), postcomposing `u : Z ⟶ hom(M, Q L)` with the adjoint of the
comparison `P hom(M, Q L) ⟶ hom(P M, P Q L)` followed by the counit is the composite of the
bijections `(Z ⟶ hom(M, Q L)) ≃ (Z ⊗ M ⟶ Q L) ≃ (P(Z ⊗ M) ⟶ L) ≃ (P Z ⊗ P M ⟶ L)
≃ (P Z ⟶ hom(P M, L)) ≃ (Z ⟶ Q hom(P M, L))`. -/
theorem comp_unit_comp_map_homComparison
    (hn₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hn₂ : Transpose.TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (ht₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (M : D₁) (L : D₂) {Z : D₁} (u : Z ⟶ (H₁.obj (op M)).obj (Q.obj L)) :
    u ≫ adj.unit.app _ ≫ Q.map (Transpose.homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m M (Q.obj L) ≫
        (H₂.obj (op (P.obj M))).map (adj.counit.app L)) =
      adj.homEquiv _ _ ((e₂ (P.obj Z) (P.obj M) L).symm
        (m.inv.app (Z, M) ≫ (adj.homEquiv _ _).symm (e₁ _ _ _ u))) := by
  have h₁ : u ≫ adj.unit.app _ ≫ Q.map (Transpose.homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m M (Q.obj L) ≫
        (H₂.obj (op (P.obj M))).map (adj.counit.app L)) =
      adj.homEquiv _ _ (P.map u ≫ Transpose.homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m M (Q.obj L) ≫
        (H₂.obj (op (P.obj M))).map (adj.counit.app L)) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit]
  rw [h₁]
  congr 1
  rw [Equiv.eq_symm_apply, ← Category.assoc]
  refine (ht₂ (P.obj Z) (P.obj M) (P.obj (Q.obj L)) L (adj.counit.app L)
    (P.map u ≫ Transpose.homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m M (Q.obj L))).trans ?_
  rw [hn₂ _ _ _ _ (P.map u) (Transpose.homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m M (Q.obj L)),
    Transpose.homComparison_adjoint, Adjunction.homEquiv_counit]
  have h₃ : e₁ _ _ _ u = T₁.map (u ×ₘ 𝟙 M) ≫ Transpose.evaluation H₁ T₁ e₁ M (Q.obj L) := by
    rw [Transpose.evaluation, ← hn₁ _ _ _ _ u (𝟙 _), Category.comp_id]
  have h₂ : T₂.map (P.map u ×ₘ 𝟙 (P.obj M)) ≫ m.inv.app ((H₁.obj (op M)).obj (Q.obj L), M) =
      m.inv.app (Z, M) ≫ P.map (T₁.map (u ×ₘ 𝟙 M)) := by
    rw [← P.map_id]
    exact m.inv.naturality (u ×ₘ 𝟙 M)
  rw [h₃, Transpose.homComparisonDatum, P.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h₂]

/-- **The adjunction isomorphism `hom(M, Q L) ≅ Q hom(P M, L)`, abstractly.**  For `P ⊣ Q` and
internal homs with tensor–hom bijections natural in the source variable (and, on the target, in the
internal-hom variable), the adjoint of the comparison `P hom(M, Q L) ⟶ hom(P M, P Q L)` followed by
the counit `P Q L ⟶ L` is an isomorphism. -/
theorem isIso_unit_comp_map_homComparison
    (hn₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hn₂ : Transpose.TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (ht₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (M : D₁) (L : D₂) :
    IsIso (adj.unit.app _ ≫ Q.map (Transpose.homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m M (Q.obj L) ≫
        (H₂.obj (op (P.obj M))).map (adj.counit.app L))) := by
  refine isIso_of_yoneda_map_bijective _ fun Z => ?_
  have hm : Function.Bijective (fun g : P.obj (T₁.obj (Z, M)) ⟶ L => m.inv.app (Z, M) ≫ g) :=
    ⟨fun a b hab => (cancel_epi (m.inv.app (Z, M))).1 hab,
      fun g => ⟨m.hom.app (Z, M) ≫ g, Iso.inv_hom_id_app_assoc m (Z, M) g⟩⟩
  have hb := (adj.homEquiv _ _).bijective.comp ((e₂ (P.obj Z) (P.obj M) L).symm.bijective.comp
    (hm.comp ((adj.homEquiv _ _).symm.bijective.comp (e₁ Z M (Q.obj L)).bijective)))
  exact (congrArg Function.Bijective (funext fun u =>
    comp_unit_comp_map_homComparison adj H₁ H₂ T₁ T₂ e₁ e₂ m hn₁ hn₂ ht₂ M L u)).mpr hb

end HomAdjunction

/-! ### The affine base -/

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedSectionsPullback

attribute [local instance 10000] HasDerivedCategory.standard

section Setup

variable {R R' : CommRingCat.{u}} (φ : R ⟶ R')

/-- The ring map `R ⟶ Γ(Spec R, 𝒪)`. -/
abbrev specScalars (R : CommRingCat.{u}) :
    R →+* (structureSheafRing (Spec R).toRingedSpace).obj.obj (op ⊤) :=
  (Scheme.ΓSpecIso R).inv.hom

/-- **Derived extension of scalars** `- ⊗^𝐋_R R' : D(R) ⥤ D(R')`, the total left derived functor of
extension of scalars along `φ`. -/
abbrev derivedExtendScalars :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R') :=
  Stacks.CategoryHomology.totalDerivedLeftAdjoint (ModuleCat.extendScalars.{u, u, u} φ.hom)

/-- `- ⊗^𝐋_R R'` is left adjoint to restriction of scalars along `φ`. -/
abbrev derivedExtendScalarsAdjunction :
    derivedExtendScalars φ ⊣ derivedRestrictScalars φ.hom :=
  Stacks.CategoryHomology.totalDerivedLeftAdjointAdjunction
    (ModuleCat.extendScalars.{u, u, u} φ.hom)
    (ModuleCat.extendRestrictScalarsAdj φ.hom)

/-- On the spectrum of a ring the scalars `R ⟶ Γ(Spec R, 𝒪)` are compatible with `Spec φ`. -/
theorem globalRingHom_specMap_comp :
    (globalRingHom (Spec.map φ).toLRSHom.toShHom).comp (specScalars R) =
      (specScalars R').comp φ.hom := by
  have h := Scheme.ΓSpecIso_inv_naturality φ
  exact (congrArg CommRingCat.Hom.hom h).symm

end Setup

section Affine

variable (R : CommRingCat.{u})

/-- `RΓ(Spec R, -) : D(𝒪_{Spec R}) ⥤ D(R)`. -/
abbrev affineSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  derivedScalarSections (Spec R).toRingedSpace (specScalars R)

/-- **The derived Spec–Γ adjunction** of Stacks 06Z0, `M ↦ M̃ ⊣ RΓ(Spec R, -)`. -/
def affineAdjunction :
    (derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι) ⊣ affineSections R :=
  (derivedTildeGlobalSectionsAdjunction R).val

/-- The unit of the derived Spec–Γ adjunction is an isomorphism. -/
instance isIso_affineAdjunction_unit : IsIso (affineAdjunction R).unit :=
  StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit R

/-- The counit of the derived Spec–Γ adjunction is an isomorphism at every object of
`D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves. -/
theorem isIso_affineAdjunction_counit_app
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)))
    (hN : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) n).obj N).IsQuasicoherent) :
    IsIso ((affineAdjunction R).counit.app N) :=
  StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_counit_app R ⟨N, hN⟩

variable {R} {R' : CommRingCat.{u}} (φ : R ⟶ R')

/-- `RΓ(Spec R, R(Spec φ)_* -) ≅ res_φ RΓ(Spec R', -)`. -/
def affinePushforwardIso :
    derivedPushforward (Spec.map φ).toLRSHom.toShHom ⋙ affineSections R ≅
      affineSections R' ⋙ derivedRestrictScalars φ.hom :=
  pushforwardScalarSectionsIso (Spec.map φ).toLRSHom.toShHom (specScalars R) ≪≫
    changeScalarsIso (Spec R').toRingedSpace φ.hom (globalRingHom_specMap_comp φ)

/-- **The affine base change map** `RΓ(Spec R, N) ⊗^𝐋_R R' ⟶ RΓ(Spec R', L(Spec φ)^* N)`, the
transpose of `RΓ(Spec R, N) ⟶ RΓ(Spec R', L(Spec φ)^* N)`. -/
def affineBaseChangeMap
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace))) :=
  transposeMap (derivedAdjunction (Spec.map φ).toLRSHom.toShHom)
    (derivedExtendScalarsAdjunction φ) (affinePushforwardIso φ) N

/-- The adjoint of `affineBaseChangeMap φ N` under `- ⊗^𝐋_R R' ⊣ res` is the map
`RΓ(Spec R, N) ⟶ RΓ(Spec R', L(Spec φ)^* N)` followed by the change of scalars identification. -/
theorem homEquiv_affineBaseChangeMap
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace))) :
    (derivedExtendScalarsAdjunction φ).homEquiv _ _ (affineBaseChangeMap φ N) =
      sectionsPullback (Spec.map φ).toLRSHom.toShHom (specScalars R) N ≫
        (changeScalarsIso (Spec R').toRingedSpace φ.hom (globalRingHom_specMap_comp φ)).hom.app
          ((derivedPullback (Spec.map φ).toLRSHom.toShHom).obj N) := by
  rw [affineBaseChangeMap, homEquiv_transposeMap, sectionsPullback, Category.assoc]
  rfl

/-- **Affine base change for derived global sections.**  For `N` with quasi-coherent cohomology
sheaves on `Spec R`, the map `RΓ(Spec R, N) ⊗^𝐋_R R' ⟶ RΓ(Spec R', L(Spec φ)^* N)` is an
isomorphism. -/
theorem isIso_affineBaseChangeMap
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)))
    (hN : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) n).obj N).IsQuasicoherent) :
    IsIso (affineBaseChangeMap φ N) :=
  have := isIso_affineAdjunction_counit_app R N hN
  isIso_transposeMap (affineAdjunction R) (affineAdjunction R')
    (derivedAdjunction (Spec.map φ).toLRSHom.toShHom) (derivedExtendScalarsAdjunction φ)
    (affinePushforwardIso φ) N

end Affine

section Square

variable {R R' : CommRingCat.{u}} (φ : R ⟶ R') {X X' : Scheme.{u}} (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ Spec.map φ)

/-- **`R`-linear derived global sections** `RΓ(X, -) : D(𝒪_X) ⥤ D(R)` of a scheme over `R`: derived
global sections, with `R` acting through `R ⟶ Γ(Spec R, 𝒪) ⟶ Γ(X, 𝒪_X)`. -/
abbrev linearSections {X : Scheme.{u}} (f : X ⟶ Spec R) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  derivedScalarSections X.toRingedSpace ((globalRingHom f.toLRSHom.toShHom).comp (specScalars R))

/-- The two ring maps `R ⟶ Γ(X', 𝒪_{X'})`, through `Spec φ` and `f'` and through `φ` and `f'`,
agree. -/
theorem globalRingHom_square_comp :
    (globalRingHom f'.toLRSHom.toShHom).comp
        ((globalRingHom (Spec.map φ).toLRSHom.toShHom).comp (specScalars R)) =
      ((globalRingHom f'.toLRSHom.toShHom).comp (specScalars R')).comp φ.hom :=
  congrArg ((globalRingHom f'.toLRSHom.toShHom).comp ·) (globalRingHom_specMap_comp φ)

/-- **The canonical map `RΓ(X, E) ⟶ RΓ(X', L(g')^*E)` of `D(R)`** for a commutative square over
`Spec R' ⟶ Spec R`, the right hand side read in `D(R)` by restriction of scalars along `φ`. -/
def sectionsBaseChange
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (linearSections f).obj E ⟶
      (derivedRestrictScalars φ.hom).obj
        ((linearSections f').obj ((derivedPullback g'.toLRSHom.toShHom).obj E)) :=
  squareSectionsPullback g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      (Spec.map φ).toLRSHom.toShHom (comp_toShHom_of_comm w) (specScalars R) E ≫
    (changeScalarsIso X'.toRingedSpace φ.hom (globalRingHom_square_comp φ f')).hom.app
      ((derivedPullback g'.toLRSHom.toShHom).obj E)

/-- **The base change map `RΓ(X, E) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*E)` of `D(R')`**: the transpose of
`sectionsBaseChange` under `- ⊗^𝐋_R R' ⊣ res`. -/
def sectionsBaseChangeMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedExtendScalars φ).obj ((linearSections f).obj E) ⟶
      (linearSections f').obj ((derivedPullback g'.toLRSHom.toShHom).obj E) :=
  ((derivedExtendScalarsAdjunction φ).homEquiv _ _).symm (sectionsBaseChange φ f f' g' w E)

/-- **Tor-independent base change for derived global sections.**  For a cartesian square of
schemes over `Spec R' ⟶ Spec R` with `f` quasi-compact and quasi-separated and `X`, `Spec R'` Tor
independent over `Spec R`, the base change map `RΓ(X, E) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*E)` is an
isomorphism for every `E` with quasi-coherent cohomology sheaves. -/
theorem isIso_sectionsBaseChangeMap (hsq : IsPullback g' f' f (Spec.map φ)) [QuasiCompact f]
    [QuasiSeparated f] (hTor : TorIndependent f (Spec.map φ))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E).IsQuasicoherent) :
    IsIso (sectionsBaseChangeMap φ f f' g' hsq.w E) := by
  have hN : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) n).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj E)).IsQuasicoherent :=
    isQuasicoherent_derivedPushforward f ⟨E, hE⟩
  have ht := isIso_affineBaseChangeMap φ _ hN
  have hbc := isIso_derivedBaseChangeMap_of_torIndependent hsq hTor E hE
  refine isIso_homEquiv_symm_of_factorization (derivedExtendScalarsAdjunction φ)
    (sectionsBaseChange φ f f' g' hsq.w E)
    ((pushforwardScalarSectionsIso f.toLRSHom.toShHom (specScalars R)).hom.app E) _ _ rfl
    (sectionsPullback (Spec.map φ).toLRSHom.toShHom (specScalars R)
      ((derivedPushforward f.toLRSHom.toShHom).obj E))
    ((derivedScalarSections (Spec R').toRingedSpace
      ((globalRingHom (Spec.map φ).toLRSHom.toShHom).comp (specScalars R))).map
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom (Spec.map φ).toLRSHom.toShHom
          (comp_toShHom_of_comm hsq.w) E))
    ((relPushforwardIso (specScalars R) f'.toLRSHom.toShHom (Spec.map φ).toLRSHom.toShHom).hom.app
      ((derivedPullback g'.toLRSHom.toShHom).obj E))
    (relSectionsPullback_square g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      (Spec.map φ).toLRSHom.toShHom (comp_toShHom_of_comm hsq.w) (specScalars R) E)
    ((changeScalarsIso (Spec R').toRingedSpace φ.hom (globalRingHom_specMap_comp φ)).hom.app _)
    ((changeScalarsIso (Spec R').toRingedSpace φ.hom (globalRingHom_specMap_comp φ)).hom.app _)
    ((pushforwardScalarSectionsIso f'.toLRSHom.toShHom (specScalars R')).hom.app
      ((derivedPullback g'.toLRSHom.toShHom).obj E))
    (pushforwardScalarSectionsIso_changeScalars f'.toLRSHom.toShHom φ.hom
      (globalRingHom_specMap_comp φ) (globalRingHom_square_comp φ f') _)
    ((affineSections R').map
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom (Spec.map φ).toLRSHom.toShHom
          (comp_toShHom_of_comm hsq.w) E))
    ((changeScalarsIso (Spec R').toRingedSpace φ.hom
      (globalRingHom_specMap_comp φ)).hom.naturality _)
    (affineBaseChangeMap φ ((derivedPushforward f.toLRSHom.toShHom).obj E))
    (homEquiv_affineBaseChangeMap φ _)

end Square

section GlobalHom

open Stacks.Cohomology.DerivedInternalHomPullback

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {R R' : CommRingCat.{u}} (φ : R ⟶ R') {X X' : Scheme.{u}} (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ Spec.map φ)

/-- **The global hom complex `R Hom_X(M, K)` of Cohomology, Section 0B6A, as an object of
`D(R)`**: `RΓ(X, R𝓗om(M, K))`, with `R` acting through `R ⟶ Γ(X, 𝒪_X)`. -/
abbrev globalHom (M K : DerivedCategory X.Modules) : DerivedCategory (ModuleCat.{u} R) :=
  (linearSections f).obj (derivedHom X M K)

/-- **The canonical map `R Hom_X(M, K) ⊗^𝐋_R R' ⟶ R Hom_{X'}(L(g')^*M, L(g')^*K)` of `D(R')`.**
The canonical map `R Hom_X(M, K) ⟶ R Hom_{X'}(L(g')^*M, L(g')^*K)` of global hom complexes of
Cohomology, Section 0B6A — derived global sections of the map
`L(g')^*R𝓗om(M, K) ⟶ R𝓗om(L(g')^*M, L(g')^*K)` of Stacks 08I3, precomposed with
`RΓ(X, -) ⟶ RΓ(X', L(g')^* -)` — viewed in `D(R)` by restriction of scalars, and transposed
along the adjunction between `- ⊗^𝐋_R R'` and restriction of scalars. -/
def globalHomBaseChangeMap (M K : DerivedCategory X.Modules) :
    (derivedExtendScalars φ).obj (globalHom f M K) ⟶
      globalHom f' ((derivedPullback g'.toLRSHom.toShHom).obj M)
        ((derivedPullback g'.toLRSHom.toShHom).obj K) :=
  ((derivedExtendScalarsAdjunction φ).homEquiv _ _).symm
    (sectionsBaseChange φ f f' g' w (derivedHom X M K) ≫
      (derivedRestrictScalars φ.hom).map
        ((linearSections f').map (derivedPullbackSheafHomMap g'.toLRSHom.toShHom M K)))

/-- `globalHomBaseChangeMap` is `sectionsBaseChangeMap` at `R𝓗om(M, K)` followed by derived global
sections of the map `L(g')^*R𝓗om(M, K) ⟶ R𝓗om(L(g')^*M, L(g')^*K)`. -/
theorem globalHomBaseChangeMap_eq (M K : DerivedCategory X.Modules) :
    globalHomBaseChangeMap φ f f' g' w M K =
      sectionsBaseChangeMap φ f f' g' w (derivedHom X M K) ≫
        (linearSections f').map (derivedPullbackSheafHomMap g'.toLRSHom.toShHom M K) := by
  rw [globalHomBaseChangeMap, Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- The base change map of global hom complexes is invertible as soon as `R𝓗om(M, K)` has
quasi-coherent cohomology sheaves and the map of Stacks 08I3 is invertible. -/
theorem isIso_globalHomBaseChangeMap_of_isIso (hsq : IsPullback g' f' f (Spec.map φ))
    [QuasiCompact f] [QuasiSeparated f] (hTor : TorIndependent f (Spec.map φ))
    (M K : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
        (derivedHom X M K)).IsQuasicoherent)
    (hc : IsIso (derivedPullbackSheafHomMap g'.toLRSHom.toShHom M K)) :
    IsIso (globalHomBaseChangeMap φ f f' g' hsq.w M K) := by
  rw [globalHomBaseChangeMap_eq]
  exact IsIso.comp_isIso' (isIso_sectionsBaseChangeMap φ f f' g' hsq hTor _ hE)
    (@Functor.map_isIso _ _ _ _ _ _ (linearSections f') _ hc)

/-- **Stacks 0AA7, case (1).**  Let `X' --g'--> X`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'` be a
cartesian square over `Spec φ : Spec R' ⟶ Spec R`, with `f` quasi-compact and quasi-separated and
`X`, `Spec R'` Tor independent over `Spec R`.  For `M` perfect and `K ∈ D_QCoh(𝒪_X)` the canonical
map `R Hom_X(M, K) ⊗^𝐋_R R' ⟶ R Hom_{X'}(L(g')^*M, L(g')^*K)` of `D(R')` is an isomorphism. -/
@[stacks 0AA7 "case (1): M perfect and K in D_QCoh(O_X)"]
theorem isIso_globalHomBaseChangeMap_of_isPerfect (hsq : IsPullback g' f' f (Spec.map φ))
    [QuasiCompact f] [QuasiSeparated f] (hTor : TorIndependent f (Spec.map φ))
    (M K : DerivedCategory X.Modules)
    (hM : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) M)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    IsIso (globalHomBaseChangeMap φ f f' g' hsq.w M K) :=
  isIso_globalHomBaseChangeMap_of_isIso φ f f' g' hsq hTor M K
    (derivedCategoryB_derivedSheafHom_of_isPerfect X M K hM hK)
    (isIso_derivedPullbackSheafHomMap_of_isPerfect g'.toLRSHom.toShHom M hM K)

/-- **Stacks 0AA7, case (2).**  Let `X' --g'--> X`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'` be a
cartesian square over `Spec φ : Spec R' ⟶ Spec R`, with `f` quasi-compact and quasi-separated and
`X`, `Spec R'` Tor independent over `Spec R`.  If `M` is pseudo-coherent, `K ∈ D^+_QCoh(𝒪_X)` and
`R'` has finite Tor dimension over `R`, the canonical map
`R Hom_X(M, K) ⊗^𝐋_R R' ⟶ R Hom_{X'}(L(g')^*M, L(g')^*K)` of `D(R')` is an isomorphism. -/
@[stacks 0AA7 "case (2): M pseudo-coherent, K in D^+_QCoh(O_X), R' of finite tor dimension over R"]
theorem isIso_globalHomBaseChangeMap_of_isPseudoCoherent (hsq : IsPullback g' f' f (Spec.map φ))
    [QuasiCompact f] [QuasiSeparated f] (hTor : TorIndependent f (Spec.map φ))
    (M K : DerivedCategory X.Modules)
    (hM : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) M)
    (hK : DerivedCategoryB.derivedCategoryBPlus (SheafOfModules.isQuasicoherent X.ringCatSheaf) K)
    (hR' : StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical R (algebraComplex R R' φ)) :
    IsIso (globalHomBaseChangeMap φ f f' g' hsq.w M K) := by
  obtain ⟨a, b, hab⟩ :=
    (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      R _).1 hR'
  obtain ⟨n₀, hn₀⟩ := hK.1
  refine isIso_globalHomBaseChangeMap_of_isIso φ f f' g' hsq hTor M K
    (derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X M K hM hK)
    (isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_amplitude g'.toLRSHom.toShHom
      (DerivedPullbackAmplitude.hasDerivedPullbackAmplitude φ f f' g' hsq hTor a b hab) M
      ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' M).2 hM) K
      fun _ => ⟨⊤, trivial, n₀, fun i hi => ?_⟩)
  exact (RingedSpace.restrictModules X.toRingedSpace ⊤).map_isZero (hn₀ i hi)

/-- **The derived adjunction on internal homs** `R𝓗om(M, Rh_*L) ≅ Rh_*R𝓗om(Lh^*M, L)`.  For a
morphism of ringed spaces `h : X ⟶ Y`, `M ∈ D(𝒪_Y)` and `L ∈ D(𝒪_X)`, the adjoint under
`Lh^* ⊣ Rh_*` of the map `Lh^*R𝓗om(M, Rh_*L) ⟶ R𝓗om(Lh^*M, Lh^*Rh_*L) ⟶ R𝓗om(Lh^*M, L)`, the
map of Stacks 08I3 followed by the counit `Lh^*Rh_*L ⟶ L`, is an isomorphism. -/
theorem isIso_derivedHomAdjunctionMap {X₀ Y₀ : RingedSpace.{u, u}} (h : X₀ ⟶ Y₀)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y₀))
    (L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X₀)) :
    IsIso ((derivedAdjunction h).unit.app
        (((Stacks.SheafOfModules.derivedSheafHom Y₀.sheaf).obj (op M)).obj
          ((derivedPushforward h).obj L)) ≫
      (derivedPushforward h).map (derivedPullbackSheafHomMap h M ((derivedPushforward h).obj L) ≫
        ((Stacks.SheafOfModules.derivedSheafHom X₀.sheaf).obj
          (op ((derivedPullback h).obj M))).map ((derivedAdjunction h).counit.app L))) :=
  isIso_unit_comp_map_homComparison (derivedAdjunction h)
    (Stacks.SheafOfModules.derivedSheafHom Y₀.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X₀.sheaf)
    (internalHomTensorUncurried Y₀) (internalHomTensorUncurried X₀) (tensorHomBijection Y₀)
    (tensorHomBijection X₀) (pullbackTensorIso h) (tensorHomEquivNaturalLeft_ringedSpace Y₀)
    (tensorHomEquivNaturalLeft_ringedSpace X₀) (curriedTargetNatural_ringedSpace X₀) M L

/-- **The identification `R Hom_X(M, Rg'_*L) = R Hom_{X'}(L(g')^*M, L)` of `D(R)`**: the canonical
map of global hom complexes of Cohomology, Section 0B6A along `g'`, followed by the map induced by
the counit `L(g')^*Rg'_*L ⟶ L` of `L(g')^* ⊣ Rg'_*`. -/
def globalHomAdjunctionMap (M : DerivedCategory X.Modules) (L : DerivedCategory X'.Modules) :
    globalHom f M ((derivedPushforward g'.toLRSHom.toShHom).obj L) ⟶
      (derivedRestrictScalars φ.hom).obj
        (globalHom f' ((derivedPullback g'.toLRSHom.toShHom).obj M) L) :=
  sectionsBaseChange φ f f' g' w (derivedHom X M ((derivedPushforward g'.toLRSHom.toShHom).obj L)) ≫
    (derivedRestrictScalars φ.hom).map ((linearSections f').map
      (derivedPullbackSheafHomMap g'.toLRSHom.toShHom M
          ((derivedPushforward g'.toLRSHom.toShHom).obj L) ≫
        ((Stacks.SheafOfModules.derivedSheafHom X'.toRingedSpace.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj M))).map
          ((derivedAdjunction g'.toLRSHom.toShHom).counit.app L)))

/-- `(((F.map η ≫ α₁.app A) ≫ α₂.app A) ≫ α₃.app A) ≫ S.map (G.map k)` is
`F.map (η ≫ R.map k) ≫ (α₁ ≪≫ α₂ ≪≫ α₃).app B` for `α₁ : R ⋙ F ≅ G₁`, `α₂ : G₁ ≅ G₂` and
`α₃ : G₂ ≅ G ⋙ S`, so it is invertible as soon as `η ≫ R.map k` is. -/
theorem isIso_map_comp_app_comp_map {D D' E E' : Type*} [Category D] [Category D'] [Category E]
    [Category E'] (F : D ⥤ E) (R : D' ⥤ D) {G₁ G₂ : D' ⥤ E} {G : D' ⥤ E'} {S : E' ⥤ E}
    (α₁ : R ⋙ F ≅ G₁) (α₂ : G₁ ≅ G₂) (α₃ : G₂ ≅ G ⋙ S)
    {N : D} {A B : D'} (η : N ⟶ R.obj A) (k : A ⟶ B) (h : IsIso (η ≫ R.map k)) :
    IsIso ((((F.map η ≫ α₁.hom.app A) ≫ α₂.hom.app A) ≫ α₃.hom.app A) ≫ S.map (G.map k)) := by
  have e : (((F.map η ≫ α₁.hom.app A) ≫ α₂.hom.app A) ≫ α₃.hom.app A) ≫ S.map (G.map k) =
      F.map (η ≫ R.map k) ≫ (α₁ ≪≫ α₂ ≪≫ α₃).hom.app B := by
    have n := (α₁ ≪≫ α₂ ≪≫ α₃).hom.naturality k
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.comp_map] at n
    simp only [Iso.trans_hom, NatTrans.comp_app, F.map_comp, Category.assoc, n]
  rw [e]
  infer_instance

/-- **The bottom map of Stacks 0BZA is an isomorphism**: the canonical map
`R Hom_X(M, Rg'_*L) ⟶ R Hom_{X'}(L(g')^*M, L)` of `D(R)` is `RΓ(X, -)` of the derived adjunction
isomorphism `R𝓗om(M, Rg'_*L) ≅ Rg'_*R𝓗om(L(g')^*M, L)` followed by the identification
`RΓ(X, Rg'_* -) = RΓ(X', -)`, for any commutative square over `Spec R' ⟶ Spec R`. -/
theorem isIso_globalHomAdjunctionMap (M : DerivedCategory X.Modules)
    (L : DerivedCategory X'.Modules) : IsIso (globalHomAdjunctionMap φ f f' g' w M L) := by
  unfold globalHomAdjunctionMap sectionsBaseChange squareSectionsPullback relSectionsPullback
  exact isIso_map_comp_app_comp_map (linearSections f) (derivedPushforward g'.toLRSHom.toShHom)
    _ _ _ _ _ (isIso_derivedHomAdjunctionMap g'.toLRSHom.toShHom M L)

/-- **The square of Stacks 0BZA commutes**: the map of Stacks 0AA7 at `K = Rg'_*L` followed by the
map `a` induced by the counit `L(g')^*Rg'_*L ⟶ L` is `- ⊗^𝐋_R R'` of the map
`R Hom_X(M, Rg'_*L) ⟶ R Hom_{X'}(L(g')^*M, L)` followed by the multiplication map, the counit
`K' ⊗^𝐋_R R' ⟶ K'` of the adjunction between `- ⊗^𝐋_R R'` and restriction of scalars at
`K' = R Hom_{X'}(L(g')^*M, L)`. -/
theorem globalHomBaseChangeMap_comp_counit (M : DerivedCategory X.Modules)
    (L : DerivedCategory X'.Modules) :
    globalHomBaseChangeMap φ f f' g' w M ((derivedPushforward g'.toLRSHom.toShHom).obj L) ≫
        (linearSections f').map (((Stacks.SheafOfModules.derivedSheafHom X'.toRingedSpace.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj M))).map
          ((derivedAdjunction g'.toLRSHom.toShHom).counit.app L)) =
      (derivedExtendScalars φ).map (globalHomAdjunctionMap φ f f' g' w M L) ≫
        (derivedExtendScalarsAdjunction φ).counit.app
          (globalHom f' ((derivedPullback g'.toLRSHom.toShHom).obj M) L) := by
  unfold globalHomBaseChangeMap globalHomAdjunctionMap
  rw [← Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit, Category.assoc,
    ← Functor.map_comp]
  exact congrArg (fun t => (derivedExtendScalars φ).map (_ ≫ (derivedRestrictScalars φ.hom).map t) ≫
    (derivedExtendScalarsAdjunction φ).counit.app _) ((linearSections f').map_comp _ _).symm

/-- **Stacks 0BZA.**  With notation as in Stacks 0AA7, the square

```
R Hom_X(M, Rg'_*L) ⊗^𝐋_R R' ----> R Hom_{X'}(L(g')^*M, L(g')^*Rg'_*L)
        |  μ                                   |  a
        v                                      v
R Hom_X(M, Rg'_*L)  ===========  R Hom_{X'}(L(g')^*M, L)
```

commutes, and its bottom map is the canonical identification.  The bottom map
`R Hom_X(M, Rg'_*L) ⟶ R Hom_{X'}(L(g')^*M, L)` of `D(R)` (`globalHomAdjunctionMap`) is an
isomorphism: it is `RΓ(X, -)` of the derived adjunction isomorphism
`R𝓗om(M, Rg'_*L) ≅ Rg'_*R𝓗om(L(g')^*M, L)` followed by `RΓ(X, Rg'_* -) = RΓ(X', -)`.  The square
says that the map of Stacks 0AA7 at `K = Rg'_*L` followed by the map `a` induced by the counit
`L(g')^*Rg'_*L ⟶ L` is the multiplication map `μ`, the counit `K' ⊗^𝐋_R R' ⟶ K'` of the
adjunction between `- ⊗^𝐋_R R'` and restriction of scalars at `K' = R Hom_{X'}(L(g')^*M, L)`, read
through that identification.  Both hold for every commutative square over `Spec R' ⟶ Spec R`. -/
@[stacks 0BZA]
theorem isIso_globalHomAdjunctionMap_and_globalHomBaseChangeMap_comp_counit
    (M : DerivedCategory X.Modules) (L : DerivedCategory X'.Modules) :
    IsIso (globalHomAdjunctionMap φ f f' g' w M L) ∧
      globalHomBaseChangeMap φ f f' g' w M ((derivedPushforward g'.toLRSHom.toShHom).obj L) ≫
          (linearSections f').map
            (((Stacks.SheafOfModules.derivedSheafHom X'.toRingedSpace.sheaf).obj
              (op ((derivedPullback g'.toLRSHom.toShHom).obj M))).map
              ((derivedAdjunction g'.toLRSHom.toShHom).counit.app L)) =
        (derivedExtendScalars φ).map (globalHomAdjunctionMap φ f f' g' w M L) ≫
          (derivedExtendScalarsAdjunction φ).counit.app
            (globalHom f' ((derivedPullback g'.toLRSHom.toShHom).obj M) L) :=
  ⟨isIso_globalHomAdjunctionMap φ f f' g' w M L, globalHomBaseChangeMap_comp_counit φ f f' g' w M L⟩

end GlobalHom

end AlgebraicGeometry.GlobalHomBaseChange

end
