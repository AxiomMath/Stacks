module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedUniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.SchemeOpenSystemLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingCocycleCompactifications

/-!
# Existence of normalized dualizing complexes

Let `S` be Noetherian with a dualizing complex `ω_S^•` and `X` of finite type over `S`. For the
upper shriek formalism of a choice of compactifications, the local models
`ω_W^• = (W → S)^! ω_S^•` on the opens `W ⊆ X` separated over `S`, with the canonical
comparisons `ω_W^•|_{W'} ≅ ω_{W'}^•`, form a system of locally given objects. Their negative
self-Ext vanishes, `ω_W^•` being dualizing, so they glue along a finite covering of `X` by opens
separated over `S` ([Stacks, Tag 08DG]). The glued complex `K` comes with isomorphisms
`α_W : K|_W ≅ ω_W^•` for *every* open `W` separated over `S`, compatible with restriction: this
is the pair `(K, α_U)` of the discussion before [Stacks, Tag 0AUA], and restricting it to the
members of a covering gives a dualizing complex normalized relative to `ω_S^•` and that covering
([Stacks, Tag 0AU9]).

## Main definitions

* `Stacks.Duality.NormalizedOnOpens`: a dualizing complex normalized relative to `ω_S^•`, with
  isomorphisms `K|_W ≅ ω_W^•` for every open `W` separated over `S`.
* `Stacks.Duality.normalizedDualizingComplexOfCompactifications`: **[Stacks, Tag 0AUA]** for the
  upper shriek functors of compactifications.

## Main results

* `Stacks.Duality.eq_zero_shift_one_of_isDualizingComplex`: `Ext^{-1}(K, K) = 0` for a dualizing
  complex `K`.
* `Stacks.Duality.UpperShriek.exists_localIso_ofCompactifications`: a complex with compatible
  identifications `K|_W ≅ ω_W^•` for every open `W` separated over `S`.
* `Stacks.Duality.Normalized.glueing_spec_ofCompactifications`: the statements of
  [Stacks, Section 0AU5] (dualizing local models, cocycle, normalized complexes are dualizing).
* `Stacks.Duality.Normalized.exists_ofCompactifications`: **[Stacks, Tag 0AU9]** for the upper
  shriek functors of compactifications.
* `Stacks.Duality.Normalized.exists_existsUnique_iso_ofCompactifications`: **[Stacks, Tag 0AU8]**
  for the upper shriek functors of compactifications.
* `Stacks.Duality.NormalizedOnOpens.existsUnique_iso_ofCompactifications`: the dualizing complex
  normalized relative to `ω_S^•` is unique up to unique isomorphism.

## References

* [Stacks Project, Tag 0AU8](https://stacks.math.columbia.edu/tag/0AU8)
* [Stacks Project, Tag 0AU9](https://stacks.math.columbia.edu/tag/0AU9)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StacksDraft.DerivedModel (derivedPullbackCongr)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u w

namespace Stacks.Duality

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A dualizing complex has no `Ext^{-1}`**: every morphism `K[1] ⟶ K` vanishes. This is
`Stacks.Duality.eq_zero_of_isDualizingComplex` on the open `X`, restriction to which is an
equivalence. -/
theorem eq_zero_shift_one_of_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) (g : K⟦(1 : ℤ)⟧ ⟶ K) :
    g = 0 := by
  let L := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (⊤ : X.Opens).ι.toLRSHom.toShHom
  have h0 := eq_zero_of_isDualizingComplex K hK ⊤ ((L.commShiftIso (1 : ℤ)).inv.app K ≫ L.map g)
  have hLg : L.map g = 0 :=
    (Iso.hom_inv_id_app_assoc (L.commShiftIso (1 : ℤ)) K (L.map g)).symm.trans
      ((congrArg (fun t => (L.commShiftIso (1 : ℤ)).hom.app K ≫ t) h0).trans comp_zero)
  exact (Stacks.Cohomology.GlueingComplexes.bijective_map_top (K⟦(1 : ℤ)⟧) K).1
    (hLg.trans (Functor.map_zero _ _ _).symm)

end Standard

namespace UpperShriek

variable {𝒟 : Scheme.{u} → Type*} [∀ X : Scheme.{u}, Category (𝒟 X)] (A : UpperShriek 𝒟)
  {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p) (ω : 𝒟 S)

private theorem restrict_restrict_chase {C : Type*} [Category C] {a₀ a₁ a₂ a₃ b₁ b₂ b₃ b₀ : C}
    (F₁ : a₀ ≅ a₁) (F₂' : a₁ ≅ a₂) (F₃ : a₀ ≅ a₃) (C₁₂K : a₃ ≅ a₂) (x₂ : a₂ ⟶ b₂)
    (x₃ : a₃ ⟶ b₃) (C₁₂ω : b₃ ≅ b₂) (Φ₂' : b₁ ≅ b₂) (Φ₁ : b₀ ≅ b₁) (Φ₃ : b₀ ≅ b₃)
    (hK : F₁.hom ≫ F₂'.hom = F₃.hom ≫ C₁₂K.hom)
    (hω : Φ₁.hom ≫ Φ₂'.hom = Φ₃.hom ≫ C₁₂ω.hom)
    (nat : x₃ ≫ C₁₂ω.hom = C₁₂K.hom ≫ x₂) :
    F₁.hom ≫ (F₂'.hom ≫ x₂ ≫ Φ₂'.inv) ≫ Φ₁.inv = F₃.hom ≫ x₃ ≫ Φ₃.inv := by
  have e₁ : Φ₂'.inv ≫ Φ₁.inv = C₁₂ω.inv ≫ Φ₃.inv := by
    simpa using (congrArg (fun t => Φ₂'.inv ≫ Φ₁.inv ≫ t ≫ C₁₂ω.inv ≫ Φ₃.inv) hω).symm
  have e₂ : x₂ ≫ C₁₂ω.inv = C₁₂K.inv ≫ x₃ := by
    simpa using (congrArg (fun t => C₁₂K.inv ≫ t ≫ C₁₂ω.inv) nat).symm
  simp only [Category.assoc]
  rw [reassoc_of% hK, e₁, reassoc_of% e₂, Iso.hom_inv_id_assoc]

/-- **Restriction of normalization isomorphisms is transitive**: restricting `α : K|_U ≅ ω_U^•`
to `W ≤ U` and then to `W' ≤ W` is restricting it to `W'`. This is the coherence of
[Stacks, Tag 0ATY] for `W' → W → U → X` and for `W' → W → U → S`. -/
theorem restrictLocalIso_restrictLocalIso (K : 𝒟 X) {W' W U : X.Opens} (h₁ : W' ≤ W)
    (h₂ : W ≤ U) (hU : IsShriekable (U.ι ≫ p)) (α : A.restrictTo hp U K ≅ A.localModel hU ω) :
    A.restrictLocalIso hp ω K h₁ (hp.isShriekable_le h₂ hU)
        (A.restrictLocalIso hp ω K h₂ hU α) =
      A.restrictLocalIso hp ω K (h₁.trans h₂) hU α := by
  have hK := A.factorIso_assoc (X.homOfLE_homOfLE h₁ h₂) (X.homOfLE_ι h₂) (X.homOfLE_ι _)
    (X.homOfLE_ι h₁) (hp.isShriekable_homOfLE h₁) (hp.isShriekable_homOfLE h₂)
    (hp.isShriekable_ι U) (hp.isShriekable_homOfLE (h₁.trans h₂)) (hp.isShriekable_ι W)
    (hp.isShriekable_ι W') K
  have hω := A.factorIso_assoc (X.homOfLE_homOfLE h₁ h₂)
    (X.homOfLE_ι_assoc h₂ p)
    (X.homOfLE_ι_assoc (h₁.trans h₂) p)
    (X.homOfLE_ι_assoc h₁ p)
    (hp.isShriekable_homOfLE h₁) (hp.isShriekable_homOfLE h₂) hU
    (hp.isShriekable_homOfLE (h₁.trans h₂)) (hp.isShriekable_le h₂ hU)
    (hp.isShriekable_le (h₁.trans h₂) hU) ω
  have nat := (A.factorIso (X.homOfLE_homOfLE h₁ h₂) (hp.isShriekable_homOfLE h₁)
    (hp.isShriekable_homOfLE h₂) (hp.isShriekable_homOfLE (h₁.trans h₂))).hom.naturality α.hom
  refine Iso.ext ?_
  simp only [restrictLocalIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at nat
  have := restrict_restrict_chase
    ((A.factorIso (X.homOfLE_ι h₁) (hp.isShriekable_homOfLE h₁) (hp.isShriekable_ι W)
      (hp.isShriekable_ι W')).app K)
    ((A.shriek (X.homOfLE h₁) (hp.isShriekable_homOfLE h₁)).mapIso
      ((A.factorIso (X.homOfLE_ι h₂) (hp.isShriekable_homOfLE h₂) (hp.isShriekable_ι U)
        (hp.isShriekable_ι W)).app K))
    ((A.factorIso (X.homOfLE_ι (h₁.trans h₂)) (hp.isShriekable_homOfLE (h₁.trans h₂))
      (hp.isShriekable_ι U) (hp.isShriekable_ι W')).app K)
    ((A.factorIso (X.homOfLE_homOfLE h₁ h₂) (hp.isShriekable_homOfLE h₁)
      (hp.isShriekable_homOfLE h₂) (hp.isShriekable_homOfLE (h₁.trans h₂))).app
        ((A.shriek U.ι (hp.isShriekable_ι U)).obj K))
    ((A.shriek (X.homOfLE h₁) (hp.isShriekable_homOfLE h₁)).map
      ((A.shriek (X.homOfLE h₂) (hp.isShriekable_homOfLE h₂)).map α.hom))
    ((A.shriek (X.homOfLE (h₁.trans h₂)) (hp.isShriekable_homOfLE (h₁.trans h₂))).map α.hom)
    ((A.factorIso (X.homOfLE_homOfLE h₁ h₂) (hp.isShriekable_homOfLE h₁)
      (hp.isShriekable_homOfLE h₂) (hp.isShriekable_homOfLE (h₁.trans h₂))).app
        (A.localModel hU ω))
    ((A.shriek (X.homOfLE h₁) (hp.isShriekable_homOfLE h₁)).mapIso
      ((A.factorIso (X.homOfLE_ι_assoc h₂ p)
        (hp.isShriekable_homOfLE h₂) hU (hp.isShriekable_le h₂ hU)).app ω))
    ((A.factorIso (X.homOfLE_ι_assoc h₁ p)
      (hp.isShriekable_homOfLE h₁) (hp.isShriekable_le h₂ hU)
      (hp.isShriekable_le (h₁.trans h₂) hU)).app ω)
    ((A.factorIso (X.homOfLE_ι_assoc (h₁.trans h₂) p)
      (hp.isShriekable_homOfLE (h₁.trans h₂)) hU (hp.isShriekable_le (h₁.trans h₂) hU)).app ω)
    hK hω nat
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp] using this

/-- Restricting a normalization isomorphism precomposed with an isomorphism of complexes. -/
theorem restrictLocalIso_mapIso_trans {K K' : 𝒟 X} (e : K' ≅ K) {W U : X.Opens} (h : W ≤ U)
    (hU : IsShriekable (U.ι ≫ p)) (β : A.restrictTo hp U K ≅ A.localModel hU ω) :
    A.restrictLocalIso hp ω K' h hU ((A.shriek U.ι (hp.isShriekable_ι U)).mapIso e ≪≫ β) =
      (A.shriek W.ι (hp.isShriekable_ι W)).mapIso e ≪≫ A.restrictLocalIso hp ω K h hU β := by
  have nat := (A.factorIso (X.homOfLE_ι h) (hp.isShriekable_homOfLE h) (hp.isShriekable_ι U)
    (hp.isShriekable_ι W)).hom.naturality e.hom
  simp only [Functor.comp_map] at nat
  refine Iso.ext ?_
  simp only [restrictLocalIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat]

end UpperShriek

namespace SeparatedCovering

/-- The covering by the pairwise intersections of the members of two coverings. -/
def inter {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p) {ι : Type w}
    {J : Type w} (𝒰 : SeparatedCovering p ι) (𝒱 : SeparatedCovering p J) :
    SeparatedCovering p (ι × J) where
  U k := 𝒰.U k.1 ⊓ 𝒱.U k.2
  finite := haveI := 𝒰.finite; haveI := 𝒱.finite; inferInstance
  covers := by rw [← iSup_inf_iSup, 𝒰.covers, 𝒱.covers, top_inf_eq]
  shriekable k := hp.isShriekable_le inf_le_left (𝒰.shriekable k.1)

end SeparatedCovering

namespace Normalized

variable {𝒟 : Scheme.{u} → Type*} [∀ X : Scheme.{u}, Category (𝒟 X)] {A : UpperShriek 𝒟}
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p} {ω : 𝒟 S}

/-- **A normalized complex is normalized relative to every refinement** of its covering: on a
member `W_k` contained in `U_{idx k}`, the normalization is the restriction of `α_{idx k}`. -/
def refine {ι : Type w} {κ : Type w} {𝒰 : SeparatedCovering p ι} (𝒩 : Normalized A hp ω 𝒰)
    (𝒲 : SeparatedCovering p κ) (idx : κ → ι) (hle : ∀ k, 𝒲.U k ≤ 𝒰.U (idx k)) :
    Normalized A hp ω 𝒲 where
  complex := 𝒩.complex
  localIso k := A.restrictLocalIso hp ω 𝒩.complex (hle k) (𝒰.shriekable (idx k))
    (𝒩.localIso (idx k))
  compat k k' := by
    rw [A.restrictLocalIso_restrictLocalIso hp ω, A.restrictLocalIso_restrictLocalIso hp ω,
      ← A.restrictLocalIso_restrictLocalIso hp ω 𝒩.complex
        (le_inf ((inf_le_left : 𝒲.U k ⊓ 𝒲.U k' ≤ _).trans (hle k))
          ((inf_le_right : 𝒲.U k ⊓ 𝒲.U k' ≤ _).trans (hle k')))
        (inf_le_left : 𝒰.U (idx k) ⊓ 𝒰.U (idx k') ≤ _),
      ← A.restrictLocalIso_restrictLocalIso hp ω 𝒩.complex
        (le_inf ((inf_le_left : 𝒲.U k ⊓ 𝒲.U k' ≤ _).trans (hle k))
          ((inf_le_right : 𝒲.U k ⊓ 𝒲.U k' ≤ _).trans (hle k')))
        (inf_le_right : 𝒰.U (idx k) ⊓ 𝒰.U (idx k') ≤ _),
      𝒩.compat (idx k) (idx k')]

end Normalized

namespace UpperShriek

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
  (ωS : quasiCoherentDerivedCategoryPlusOfModel S)

/-- The canonical comparison `ω_W^•|_{W'} ≅ ω_{W'}^•` of the local models on opens `W' ≤ W`
separated over `S`, restriction being derived pullback. -/
def localModelPullbackIso {W' W : X.Opens} (h : W' ≤ W) (hW : IsShriekable (W.ι ≫ p))
    (hW' : IsShriekable (W'.ι ≫ p)) :
    (derivedPullback (X.homOfLE h)).obj ((shriekOf c (W.ι ≫ p) hW).obj ωS).obj.obj ≅
      ((shriekOf c (W'.ι ≫ p) hW').obj ωS).obj.obj :=
  (pullbackOpenIso c (X.homOfLE h) (hp.isShriekable_homOfLE h)
      ((shriekOf c (W.ι ≫ p) hW).obj ωS)).symm ≪≫
    (ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso
      ((factorIsoOf c (X.homOfLE_ι_assoc h p) (hp.isShriekable_homOfLE h) hW hW').app ωS).symm

private theorem cocycle_shriek_chase {D D' : Type*} [Category D] [Category D'] (R : D' ⥤ D)
    {ω₃ a b c' z₃ : D} {s₁ s₂ s₃ : D'}
    (Φ₃ : ω₃ ≅ c') (Φ₁ : ω₃ ≅ a) (G₁ : a ≅ b) (F₁₂ : c' ≅ b) (P₃ : c' ≅ z₃)
    (P₁a : a ≅ R.obj s₁) (P₁b : b ≅ R.obj s₂) (Φ₂ : s₁ ≅ s₂) (P₂ : s₂ ≅ s₃) (cc : R.obj s₃ ≅ z₃)
    (hassoc : Φ₁.hom ≫ G₁.hom = Φ₃.hom ≫ F₁₂.hom)
    (hnat : G₁.hom ≫ P₁b.hom = P₁a.hom ≫ R.map Φ₂.hom)
    (hbridge : P₃.hom = F₁₂.hom ≫ P₁b.hom ≫ R.map P₂.hom ≫ cc.hom) :
    P₃.inv ≫ Φ₃.inv = cc.inv ≫ R.map (P₂.inv ≫ Φ₂.inv) ≫ P₁a.inv ≫ Φ₁.inv := by
  have key : (Φ₁ ≪≫ P₁a ≪≫ R.mapIso (Φ₂ ≪≫ P₂) ≪≫ cc).hom = (Φ₃ ≪≫ P₃).hom := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [hbridge, ← reassoc_of% hassoc, reassoc_of% hnat]
  have := congrArg Iso.inv (Iso.ext key)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] at this
  rw [← this, Functor.map_comp, Category.assoc]

/-- The comparisons of the local models satisfy the cocycle condition: this is the coherence
[Stacks, Tag 0ATY] of the upper shriek functors, read through `j^! = Lj^*` for open immersions. -/
theorem localModelPullbackIso_cocycle {W'' W' W : X.Opens} (h₁ : W'' ≤ W') (h₂ : W' ≤ W)
    (hW : IsShriekable (W.ι ≫ p)) (hW' : IsShriekable (W'.ι ≫ p))
    (hW'' : IsShriekable (W''.ι ≫ p)) :
    (localModelPullbackIso c hp ωS (h₁.trans h₂) hW hW'').hom =
      (derivedPullbackCompIsoCanonical (X.homOfLE h₁).toLRSHom.toShHom
          (X.homOfLE h₂).toLRSHom.toShHom ≪≫
        derivedPullbackCongr (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
          (X.homOfLE_homOfLE h₁ h₂))).inv.app ((shriekOf c (W.ι ≫ p) hW).obj ωS).obj.obj ≫
        (derivedPullback (X.homOfLE h₁)).map (localModelPullbackIso c hp ωS h₂ hW hW').hom ≫
          (localModelPullbackIso c hp ωS h₁ hW' hW'').hom := by
  have hh₁ := hp.isShriekable_homOfLE h₁
  have hh₂ := hp.isShriekable_homOfLE h₂
  have hh₃ := hp.isShriekable_homOfLE (h₁.trans h₂)
  have e₁ := X.homOfLE_ι_assoc h₁ p
  have e₂ := X.homOfLE_ι_assoc h₂ p
  have e₃ := X.homOfLE_ι_assoc (h₁.trans h₂) p
  let K := (shriekOf c (W.ι ≫ p) hW).obj ωS
  have hassoc := congrArg (fun t => t.hom.hom) (factorIsoOf_assoc c (X.homOfLE_homOfLE h₁ h₂) e₂
    e₃ e₁ hh₁ hh₂ hW hh₃ hW' hW'' ωS)
  have hnat : ((shriekOf c (X.homOfLE h₁) hh₁).map
      ((factorIsoOf c e₂ hh₂ hW hW').hom.app ωS)).hom.hom ≫
      (pullbackOpenIso c (X.homOfLE h₁) hh₁ ((shriekOf c (X.homOfLE h₂) hh₂).obj K)).hom =
      (pullbackOpenIso c (X.homOfLE h₁) hh₁ ((shriekOf c (W'.ι ≫ p) hW').obj ωS)).hom ≫
        (derivedPullback (X.homOfLE h₁)).map
          ((factorIsoOf c e₂ hh₂ hW hW').hom.app ωS).hom.hom :=
    congrArg (fun g => g.hom)
      ((shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE h₁) hh₁).hom.naturality
        ((factorIsoOf c e₂ hh₂ hW hW').hom.app ωS))
  have hbridge : (pullbackOpenIso c (X.homOfLE (h₁.trans h₂)) hh₃ K).hom =
      ((factorIsoOf c (X.homOfLE_homOfLE h₁ h₂) hh₁ hh₂ hh₃).hom.app K).hom.hom ≫
        (pullbackOpenIso c (X.homOfLE h₁) hh₁ ((shriekOf c (X.homOfLE h₂) hh₂).obj K)).hom ≫
        (derivedPullback (X.homOfLE h₁)).map (pullbackOpenIso c (X.homOfLE h₂) hh₂ K).hom ≫
        (derivedPullbackCompIsoCanonical (X.homOfLE h₁).toLRSHom.toShHom
            (X.homOfLE h₂).toLRSHom.toShHom ≪≫
          derivedPullbackCongr (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
            (X.homOfLE_homOfLE h₁ h₂))).hom.app K.obj.obj :=
    congrArg (fun f => f.hom)
      (shriekOfIsoPullbackOfIsOpenImmersion_factorIso c (X.homOfLE_homOfLE h₁ h₂) hh₁ hh₂ hh₃ K)
  exact cocycle_shriek_chase (derivedPullback (X.homOfLE h₁))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso ((factorIsoOf c e₃ hh₃ hW hW'').app ωS))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso ((factorIsoOf c e₁ hh₁ hW' hW'').app ωS))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso
      ((shriekOf c (X.homOfLE h₁) hh₁).mapIso ((factorIsoOf c e₂ hh₂ hW hW').app ωS)))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso
      ((factorIsoOf c (X.homOfLE_homOfLE h₁ h₂) hh₁ hh₂ hh₃).app K))
    (pullbackOpenIso c (X.homOfLE (h₁.trans h₂)) hh₃ K)
    (pullbackOpenIso c (X.homOfLE h₁) hh₁ ((shriekOf c (W'.ι ≫ p) hW').obj ωS))
    (pullbackOpenIso c (X.homOfLE h₁) hh₁ ((shriekOf c (X.homOfLE h₂) hh₂).obj K))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso ((factorIsoOf c e₂ hh₂ hW hW').app ωS))
    (pullbackOpenIso c (X.homOfLE h₂) hh₂ K)
    ((derivedPullbackCompIsoCanonical (X.homOfLE h₁).toLRSHom.toShHom
          (X.homOfLE h₂).toLRSHom.toShHom ≪≫
        derivedPullbackCongr (congrArg (fun m : W''.toScheme ⟶ W.toScheme ↦ m.toLRSHom.toShHom)
          (X.homOfLE_homOfLE h₁ h₂))).app K.obj.obj)
    hassoc hnat hbridge

/-- An isomorphism of `D⁺_QCoh` given by an isomorphism of the underlying objects of `D(𝒪_X)`. -/
abbrev plusIsoMk {Z : Scheme.{u}} {A B : quasiCoherentDerivedCategoryPlusOfModel Z}
    (e : A.obj.obj ≅ B.obj.obj) : A ≅ B :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e)

private theorem restrict_localIso_chase {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {k₀ k₁ k₃ o₁ o₂ : D} {y w ω : C} (F₁ : k₀ ⟶ k₁) (ρa : k₁ ≅ L.obj y) (ρω : o₁ ≅ L.obj ω)
    (Φ : o₂ ≅ o₁) (cc : L.obj w ≅ k₃) (ρW : y ⟶ w) (aW : w ⟶ ω) (x : k₁ ⟶ o₁)
    (aW' : k₃ ⟶ o₂) (ρW' : k₀ ⟶ k₃)
    (hnat : x ≫ ρω.hom = ρa.hom ≫ L.map (ρW ≫ aW))
    (hρ : ρW' = F₁ ≫ ρa.hom ≫ L.map ρW ≫ cc.hom)
    (ha : aW' = cc.inv ≫ L.map aW ≫ ρω.inv ≫ Φ.inv) :
    F₁ ≫ x ≫ Φ.inv = ρW' ≫ aW' := by
  have hx : x = ρa.hom ≫ L.map (ρW ≫ aW) ≫ ρω.inv := by
    rw [← reassoc_of% hnat]
    simp
  rw [hx, hρ, ha]
  simp

/-- **The local models are dualizing**: `ω_W^• = (W → S)^! ω_S^•` is a dualizing complex on every
open `W` separated over `S`. -/
private theorem isDualizingComplex_shriekOf_obj
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)) :
    haveI := hp.opens_noetherian W
    IsDualizingComplex ((shriekOf c (W.ι ≫ p) hW).obj ωS).obj.obj := by
  have := hp.base_noetherian
  have := hp.opens_noetherian W
  exact isDualizingComplex_upperShriek_obj
    (ftsHomOf (W.ι ≫ p) hW.separatedFiniteType (isSeparatedFiniteType_id S) (Category.comp_id _))
    (c _ hW) ωS.obj hωS

/-- **The pair `(K, α_U)` of the discussion before [Stacks, Tag 0AUA]**, for the upper shriek
functors of compactifications. In Situation 0AU4, let `X` be of finite type over `S` admitting a
finite covering by opens separated over `S`. There is `K` in `D⁺_QCoh(𝒪_X)` with isomorphisms
`α_W : K|_W ≅ ω_W^• = (W → S)^! ω_S^•` for every open `W` separated over `S`, compatible with
restriction: for `W' ≤ W` the restriction of `α_W` to `W'` is `α_{W'}`. -/
theorem exists_localIso_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    {ι : Type w} (𝒰 : SeparatedCovering p ι) :
    ∃ (K : quasiCoherentDerivedCategoryPlusOfModel X)
      (α : ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        (ofCompactifications c).restrictTo hp W K ≅ (ofCompactifications c).localModel hW ωS),
      ∀ {W' W : X.Opens} (h : W' ≤ W) (hW : IsShriekable (W.ι ≫ p))
        (hW' : IsShriekable (W'.ι ≫ p)),
        (ofCompactifications c).restrictLocalIso hp ωS K h hW (α W hW) = α W' hW' := by
  have := hp.base_noetherian
  have := hp.source_noetherian
  have := 𝒰.finite
  obtain ⟨F, a, ha⟩ := Stacks.Cohomology.GlueingComplexes.exists_solution_locallySmall
    (fun W : X.Opens => IsShriekable (W.ι ≫ p))
    (fun W hW => ((shriekOf c (W.ι ≫ p) hW).obj ωS).obj.obj)
    (fun h hW hW' => localModelPullbackIso c hp ωS h hW hW')
    (fun h₁ h₂ hW hW' hW'' => localModelPullbackIso_cocycle c hp ωS h₁ h₂ hW hW' hW'')
    (fun h hW => hp.isShriekable_le h hW)
    (fun W hW g => by
      have := hp.opens_noetherian W
      exact eq_zero_shift_one_of_isDualizingComplex _
        (isDualizingComplex_standard_of_isDualizingComplex
          (isDualizingComplex_shriekOf_obj c hp ωS hωS W hW)) g)
    𝒰.U 𝒰.shriekable 𝒰.covers
  have hF : IsDualizingComplex F := by
    refine isDualizingComplex_of_isDualizingComplex_restrict 𝒰.U 𝒰.covers fun i => ?_
    have := hp.opens_noetherian (𝒰.U i)
    exact isDualizingComplex_of_iso
      ((derivedRestrictIsoDerivedPullback (𝒰.U i).ι).app F ≪≫ a _ (𝒰.shriekable i)).symm
      (isDualizingComplex_shriekOf_obj c hp ωS hωS _ (𝒰.shriekable i))
  let K : quasiCoherentDerivedCategoryPlusOfModel X :=
    ⟨⟨F, fun i => isQuasicoherent_homology_of_hasDualizingModelOn_cover
      (fun V : X.affineOpens => (V : X.Opens)) (fun V => V.2) (iSup_affineOpens_eq_top X)
      (fun V => hF V V.2) i⟩, isBoundedBelow_of_isDualizingComplex _ hF⟩
  refine ⟨K, fun W hW => plusIsoMk (pullbackOpenIso c W.ι (hp.isShriekable_ι W) K ≪≫ a W hW),
    fun {W' W} h hW hW' => ?_⟩
  have hh := hp.isShriekable_homOfLE h
  refine Iso.ext (ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ ?_))
  have hnat := congrArg (fun g => g.hom)
    ((shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE h) hh).hom.naturality
      (plusIsoMk (pullbackOpenIso c W.ι (hp.isShriekable_ι W) K ≪≫ a W hW) :
        (ofCompactifications c).restrictTo hp W K ≅ (ofCompactifications c).localModel hW ωS).hom)
  have hρ := congrArg (fun f => f.hom)
    (shriekOfIsoPullbackOfIsOpenImmersion_factorIso c (X.homOfLE_ι h) hh (hp.isShriekable_ι W)
      (hp.isShriekable_ι W') K)
  exact restrict_localIso_chase (derivedPullback (X.homOfLE h))
    ((factorIsoOf c (X.homOfLE_ι h) hh (hp.isShriekable_ι W) (hp.isShriekable_ι W')).hom.app
      K).hom.hom
    (pullbackOpenIso c (X.homOfLE h) hh ((shriekOf c W.ι (hp.isShriekable_ι W)).obj K))
    (pullbackOpenIso c (X.homOfLE h) hh ((shriekOf c (W.ι ≫ p) hW).obj ωS))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso
      ((factorIsoOf c (X.homOfLE_ι_assoc h p) hh hW hW').app ωS))
    ((derivedPullbackCompIsoCanonical (X.homOfLE h).toLRSHom.toShHom W.ι.toLRSHom.toShHom ≪≫
      derivedPullbackCongr (congrArg (fun m : W'.toScheme ⟶ X ↦ m.toLRSHom.toShHom)
        (X.homOfLE_ι h))).app F)
    (pullbackOpenIso c W.ι (hp.isShriekable_ι W) K).hom (a W hW).hom _ _ _ hnat hρ (ha h hW hW')

end UpperShriek

namespace Normalized

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Section 0AU5]** for the upper shriek functors of compactifications. In Situation
0AU4, for `X` of finite type over `S` and a finite covering `𝒰` of `X` by opens separated over
`S`: (1) each `ω_i^• = p_i^! ω_S^•` is a dualizing complex on `U_i`; (2)–(3) the canonical
comparisons `φ_{ij}` on `U_i ∩ U_j` (`UpperShriek.overlapCompareRestrict`) satisfy the cocycle
condition on `U_i ∩ U_j ∩ U_k`; and every dualizing complex normalized relative to `ω_S^•` and
`𝒰` is a dualizing complex. -/
theorem glueing_spec_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    {ι : Type w} (𝒰 : SeparatedCovering p ι) :
    (∀ i, haveI := hp.opens_noetherian (𝒰.U i)
      IsDualizingComplex ((UpperShriek.ofCompactifications c).localModel
        (𝒰.shriekable i) ωS).obj.obj) ∧
    (∀ i j k, (UpperShriek.ofCompactifications c).overlapCompareRestrict hp ωS 𝒰 i k
        (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) =
      (UpperShriek.ofCompactifications c).overlapCompareRestrict hp ωS 𝒰 i j
          (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k) inf_le_left ≪≫
        (UpperShriek.ofCompactifications c).overlapCompareRestrict hp ωS 𝒰 j k
          (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) ∧
    (∀ 𝒩 : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰,
      haveI := hp.source_noetherian; IsDualizingComplex 𝒩.complex.obj.obj) := by
  have := hp.base_noetherian
  exact ⟨fun i => UpperShriek.isDualizingComplex_shriekOf_obj c hp ωS hωS _ (𝒰.shriekable i),
    fun i j k => UpperShriek.overlapCompareRestrict_cocycle_ofCompactifications c hp ωS 𝒰 i j k,
    fun 𝒩 => 𝒩.isDualizingComplex_ofCompactifications c hωS⟩

/-- **[Stacks, Tag 0AU9]** for the upper shriek functors of compactifications. In Situation 0AU4,
let `X` be of finite type over `S` and `𝒰` a finite open covering of `X` by schemes separated
over `S`. Then there exists a dualizing complex normalized relative to `ω_S^•` and `𝒰`. -/
theorem exists_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    {ι : Type w} (𝒰 : SeparatedCovering p ι) :
    ∃ 𝒩 : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰,
      haveI := hp.source_noetherian; IsDualizingComplex 𝒩.complex.obj.obj := by
  obtain ⟨K, α, hα⟩ := UpperShriek.exists_localIso_ofCompactifications c hp ωS hωS 𝒰
  let 𝒩 : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰 :=
    { complex := K
      localIso := fun i => α (𝒰.U i) (𝒰.shriekable i)
      compat := fun i j => (hα inf_le_left (𝒰.shriekable i) _).trans
        (hα inf_le_right (𝒰.shriekable j) _).symm }
  exact ⟨𝒩, 𝒩.isDualizingComplex_ofCompactifications c hωS⟩

/-- **[Stacks, Tag 0AU8]** for the upper shriek functors of compactifications. In Situation 0AU4,
let `X` be of finite type over `S` and `𝒰`, `𝒱` two finite open coverings of `X` by schemes
separated over `S`. If `(K, α_i)` is a dualizing complex normalized relative to `ω_S^•` and `𝒰`,
there is a dualizing complex `(K', α'_j)` normalized relative to `ω_S^•` and `𝒱`, and the two are
canonically isomorphic: there is exactly one isomorphism `K ≅ K'` carrying the restriction of
`α_i` to `U_i ∩ V_j` to that of `α'_j`, for all `i` and `j`. -/
theorem exists_existsUnique_iso_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    {ι J : Type w} {𝒰 : SeparatedCovering p ι} (𝒱 : SeparatedCovering p J)
    (𝒩 : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰) :
    ∃ 𝒩' : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒱,
      (haveI := hp.source_noetherian; IsDualizingComplex 𝒩'.complex.obj.obj) ∧
      ∃! e : 𝒩.complex ≅ 𝒩'.complex, ∀ i j,
        ((UpperShriek.ofCompactifications c).shriek (𝒰.U i ⊓ 𝒱.U j).ι
            (hp.isShriekable_ι _)).mapIso e ≪≫
          (UpperShriek.ofCompactifications c).restrictLocalIso hp ωS 𝒩'.complex
            (inf_le_right : 𝒰.U i ⊓ 𝒱.U j ≤ 𝒱.U j) (𝒱.shriekable j) (𝒩'.localIso j) =
        (UpperShriek.ofCompactifications c).restrictLocalIso hp ωS 𝒩.complex
          (inf_le_left : 𝒰.U i ⊓ 𝒱.U j ≤ 𝒰.U i) (𝒰.shriekable i) (𝒩.localIso i) := by
  obtain ⟨𝒩', h𝒩'⟩ := exists_ofCompactifications c hωS 𝒱
  refine ⟨𝒩', h𝒩', ?_⟩
  obtain ⟨e, he, hu⟩ := existsUnique_iso_ofCompactifications c hωS
    (𝒩.refine (𝒰.inter hp 𝒱) Prod.fst fun _ => inf_le_left)
    (𝒩'.refine (𝒰.inter hp 𝒱) Prod.snd fun _ => inf_le_right)
  exact ⟨e, fun i j => he (i, j), fun e' he' => hu e' fun k => he' k.1 k.2⟩

end Normalized

namespace SeparatedCovering

/-- **Finite coverings by opens separated over `S` exist**: the affine opens of `X` are
separated over `S` ([Stacks, Tag 01KV]) and finitely many of them cover `X`. -/
theorem exists_nonempty {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p) :
    ∃ ι : Type u, Nonempty (SeparatedCovering p ι) := by
  have := hp.base_noetherian
  have := hp.source_noetherian
  have := hp.locallyOfFiniteType
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => (V : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  refine ⟨t, ⟨⟨fun V => (V.1 : X.Opens), inferInstance, ?_, fun V => ?_⟩⟩⟩
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨⟨V, hV⟩, hx⟩
  · have : IsAffine (V.1 : X.Opens).toScheme := V.1.2
    have := hp.opens_noetherian (V.1 : X.Opens)
    exact { target_noetherian := hp.base_noetherian
            separatedFiniteType := ⟨⟨inferInstance, inferInstance⟩,
              quasiCompact_of_noetherianSpace_source _⟩ }

/-- The covering obtained by adding one member to a covering. -/
def addOpen {X S : Scheme.{u}} {p : X ⟶ S} {ι : Type w} (𝒰 : SeparatedCovering p ι)
    (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)) : SeparatedCovering p (Option ι) where
  U k := k.elim W 𝒰.U
  finite := haveI := 𝒰.finite; inferInstance
  covers := top_le_iff.mp (𝒰.covers.ge.trans (iSup_le fun i => le_iSup_of_le (some i) le_rfl))
  shriekable
    | none => hW
    | some i => 𝒰.shriekable i

end SeparatedCovering

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **Existence of the dualizing complex normalized relative to `ω_S^•`**, for the upper shriek
functors of compactifications: the content of [Stacks, Tag 0AU9] and [Stacks, Tag 0AU8] behind
Definition [Stacks, Tag 0AUA]. -/
theorem nonempty_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) :
    Nonempty (NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) := by
  obtain ⟨ι, ⟨𝒰⟩⟩ := SeparatedCovering.exists_nonempty hp
  obtain ⟨K, α, hα⟩ := UpperShriek.exists_localIso_ofCompactifications c hp ωS hωS 𝒰
  exact ⟨⟨K, α, hα⟩⟩

/-- A dualizing complex normalized relative to `ω_S^•` is a dualizing complex. -/
theorem isDualizingComplex_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦 : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) :
    haveI := hp.source_noetherian; IsDualizingComplex 𝒦.complex.obj.obj := by
  obtain ⟨ι, ⟨𝒰⟩⟩ := SeparatedCovering.exists_nonempty hp
  exact (𝒦.toNormalized 𝒰).isDualizingComplex_ofCompactifications c hωS

/-- **Uniqueness up to unique isomorphism** of the dualizing complex normalized relative to
`ω_S^•` ([Stacks, Tag 0AU7]): two of them are related by exactly one isomorphism carrying `α_W`
to `α'_W` for every open `W` separated over `S`. -/
theorem existsUnique_iso_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦 𝒦' : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) :
    ∃! e : 𝒦.complex ≅ 𝒦'.complex, ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
      ((UpperShriek.ofCompactifications c).shriek W.ι (hp.isShriekable_ι W)).mapIso e ≪≫
        𝒦'.localIso W hW = 𝒦.localIso W hW := by
  obtain ⟨ι, ⟨𝒰⟩⟩ := SeparatedCovering.exists_nonempty hp
  obtain ⟨e, he, hu⟩ := Normalized.existsUnique_iso_ofCompactifications c hωS
    (𝒦.toNormalized 𝒰) (𝒦'.toNormalized 𝒰)
  refine ⟨e, fun W hW => ?_, fun e' he' => hu e' fun i => he' _ _⟩
  obtain ⟨e₁, he₁, -⟩ := Normalized.existsUnique_iso_ofCompactifications c hωS
    (𝒦.toNormalized (𝒰.addOpen W hW)) (𝒦'.toNormalized (𝒰.addOpen W hW))
  obtain rfl : e₁ = e := hu e₁ fun i => he₁ (some i)
  exact he₁ none

end NormalizedOnOpens

/-- **[Stacks, Tag 0AUA]** for the upper shriek functors of compactifications: the dualizing
complex `ω_X^•` normalized relative to `ω_S^•`, together with its isomorphisms
`α_W : ω_X^•|_W ≅ (W → S)^! ω_S^•` for the opens `W` separated over `S`. It is unique up to unique
isomorphism (`Stacks.Duality.NormalizedOnOpens.existsUnique_iso_ofCompactifications`), and it is
normalized relative to `ω_S^•` and every finite covering of `X` by opens separated over `S`
(`Stacks.Duality.NormalizedOnOpens.toNormalized`). -/
def normalizedDualizingComplexOfCompactifications
    (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
    {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
    (ωS : quasiCoherentDerivedCategoryPlusOfModel S)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) :
    NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS :=
  Classical.choice (NormalizedOnOpens.nonempty_ofCompactifications c hωS)

end Stacks.Duality

end
