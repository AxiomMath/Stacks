module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalEndomorphisms
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexEndomorphisms
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedSheafHomothetyScalars
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedPullbackOpensHomGlueing
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartIso
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexNegativeExt
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexOpenRestriction

/-!
# Uniqueness of relative dualizing complexes

Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)`, `(L, η)` be relative
dualizing complexes for `f` (Stacks 0E2T). This file proves the two steps of the proof of
Stacks 0E2W that take place on a single scheme.

By Stacks 0E2V every endomorphism of `K` is multiplication by a global section `a` of `𝒪_X`, and
pulling it back along `pr₁|_W` multiplies `ξ` by `a`. Since `ξ` is a free generator of
`Hom(Δ_*𝒪_X, L pr₁^*K|_W)` over `Γ(X, 𝒪_X)`, an endomorphism sending `ξ` to `ξ` is the identity;
hence there is at most one isomorphism `K ≅ L` sending `ξ` to `η`. Conversely an isomorphism
`α : K ≅ L` sends `ξ` to `s • η` for a unit `s`, and `s⁻¹ • α` sends `ξ` to `η`.

## Main results

All in the namespace `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex`:

* `eq_id_of_comp_derivedPullbackProjMap_eq`: rigidity of a relative dualizing complex.
* `exists_iso_comp_eq_of_isIso`: an isomorphism can be normalized to send `ξ` to `η`.
* `iso_ext_of_comp_eq`: two isomorphisms sending `ξ` to `η` agree.

## References

* [Stacks Project, Lemma 48.28.4 (Tag 0E2W)](https://stacks.math.columbia.edu/tag/0E2W)
* [Stacks Project, Lemma 48.28.3 (Tag 0E2V)](https://stacks.math.columbia.edu/tag/0E2V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]
  {D : DiagonalOpen f}

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- Pulling back a scalar endomorphism along `pr₁|_W` and composing with `ξ` is `a • ξ`. -/
theorem comp_derivedPullbackProjMap_smul_id
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (a : Γ(X, ⊤)) :
    letI := Scheme.linearOXMod X
    letI := D.proj.linearStructureSheafModules
    ξ ≫ D.derivedPullbackProjMap (a • 𝟙 K) = a • ξ :=
  let := Scheme.linearOXMod X
  let := Scheme.linearStructureSheafRing X
  let := D.proj.linearStructureSheafModules
  let := D.proj.linearStructureSheafRing
  (congrArg (ξ ≫ ·) (Scheme.Hom.derivedPullback_map_smul_id D.proj a K)).trans
    ((Linear.comp_smul _ _ _ _ _ _).trans
      (congrArg (fun t : D.diagonalObject ⟶ D.derivedPullbackProj K => a • t)
        (Category.comp_id ξ)))

/-- **Rigidity.** An endomorphism of a relative dualizing complex `(K, ξ)` which sends `ξ` to
itself is the identity. -/
theorem eq_id_of_comp_derivedPullbackProjMap_eq
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (γ : K ⟶ K) (h : ξ ≫ D.derivedPullbackProjMap γ = ξ) : γ = 𝟙 K := by
  obtain ⟨a, rfl⟩ := Scheme.exists_eq_smul_id_of_isIso_derivedSheafHomothety_oxMod X K
    hK.isIso_derivedSheafHomothety γ
  let := Scheme.linearOXMod X
  let := D.proj.linearStructureSheafModules
  have e := comp_derivedPullbackProjMap_smul_id ξ a
  have ha : a = 1 :=
    (D.existsUnique_eq_smul_of_isIso_diagonalAction hK.isIso_diagonalAction ξ).unique
      (e.symm.trans h).symm (one_smul _ ξ).symm
  subst ha
  exact one_smul _ _

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `L pr₁^*` on morphisms preserves composition. -/
theorem derivedPullbackProjMap_comp {K L M : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    D.derivedPullbackProjMap (φ ≫ ψ) = D.derivedPullbackProjMap φ ≫ D.derivedPullbackProjMap ψ :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    D.proj.toLRSHom.toShHom).map_comp φ ψ

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `L pr₁^*` on morphisms preserves identities. -/
theorem derivedPullbackProjMap_id (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    D.derivedPullbackProjMap (𝟙 K) = 𝟙 (D.derivedPullbackProj K) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    D.proj.toLRSHom.toShHom).map_id K

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `L pr₁^*` of an isomorphism is an isomorphism. -/
theorem isIso_derivedPullbackProjMap {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (α : K ≅ L) : IsIso (D.derivedPullbackProjMap α.hom) :=
  ⟨⟨D.derivedPullbackProjMap α.inv,
    by rw [← derivedPullbackProjMap_comp, α.hom_inv_id, derivedPullbackProjMap_id],
    by rw [← derivedPullbackProjMap_comp, α.inv_hom_id, derivedPullbackProjMap_id]⟩⟩

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- Pulling back a scalar multiple of a morphism along `pr₁|_W` and composing with `ζ` is the
scalar multiple of the composite. -/
theorem comp_derivedPullbackProjMap_smul
    {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) (a : Γ(X, ⊤)) (φ : K ⟶ L) :
    letI := Scheme.linearOXMod X
    letI := D.proj.linearStructureSheafModules
    ζ ≫ D.derivedPullbackProjMap (a • φ) =
      a • (ζ ≫ D.derivedPullbackProjMap φ : D.diagonalObject ⟶ D.derivedPullbackProj L) :=
  let := Scheme.linearOXMod X
  let := Scheme.linearStructureSheafRing X
  let := D.proj.linearStructureSheafModules
  let := D.proj.linearStructureSheafRing
  (congrArg (ζ ≫ ·) (Scheme.Hom.derivedPullback_map_smul D.proj a φ)).trans
    (Linear.comp_smul _ _ _ _ _ _)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The map defined by `ξ ≫ L pr₁^*α` is invertible when that defined by `ξ` is, for `α` an
isomorphism. -/
theorem isIso_diagonalAction_comp {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K} (hξ : IsIso (D.diagonalAction K ξ))
    (α : K ≅ L) : IsIso (D.diagonalAction L (ξ ≫ D.derivedPullbackProjMap α.hom)) := by
  have := isIso_derivedPullbackProjMap (D := D) α
  rw [D.diagonalAction_comp_derivedPullbackProjMap]
  infer_instance

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **Normalization.** If the maps defined by `ξ` and by `η` are invertible, every isomorphism
`K ≅ L` can be rescaled by a unit of `Γ(X, 𝒪_X)` to an isomorphism sending `ξ` to `η`. -/
theorem exists_iso_comp_eq_of_isIso {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    {η : D.diagonalObject ⟶ D.derivedPullbackProj L}
    (hξ : IsIso (D.diagonalAction K ξ)) (hη : IsIso (D.diagonalAction L η)) (α : K ≅ L) :
    ∃ β : K ≅ L, ξ ≫ D.derivedPullbackProjMap β.hom = η := by
  let := Scheme.linearOXMod X
  let := D.proj.linearStructureSheafModules
  have hζ := isIso_diagonalAction_comp hξ α
  obtain ⟨s, hs, -⟩ := D.existsUnique_eq_smul_of_isIso_diagonalAction hη
    (ξ ≫ D.derivedPullbackProjMap α.hom)
  obtain ⟨t, ht, -⟩ := D.existsUnique_eq_smul_of_isIso_diagonalAction hζ η
  have hts : t * s = 1 :=
    (D.existsUnique_eq_smul_of_isIso_diagonalAction hη η).unique
      (ht.trans ((congrArg (t • ·) hs).trans (smul_smul t s η))) (one_smul _ η).symm
  have hst : s * t = 1 := (mul_comm s t).trans hts
  refine ⟨⟨t • α.hom, s • α.inv, ?_, ?_⟩, ?_⟩
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hts, one_smul, α.hom_inv_id]
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hst, one_smul, α.inv_hom_id]
  · exact (comp_derivedPullbackProjMap_smul ξ t α.hom).trans ht.symm

/-- **Uniqueness.** Two isomorphisms between relative dualizing complexes `(K, ξ)` and `(L, η)`
which both send `ξ` to `η` are equal. -/
theorem iso_ext_of_comp_eq {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    {η : D.diagonalObject ⟶ D.derivedPullbackProj L}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    {α β : K ≅ L} (hα : ξ ≫ D.derivedPullbackProjMap α.hom = η)
    (hβ : ξ ≫ D.derivedPullbackProjMap β.hom = η) : α = β := by
  have hγ : ξ ≫ D.derivedPullbackProjMap (α.hom ≫ β.inv) = ξ := by
    rw [derivedPullbackProjMap_comp, ← Category.assoc, hα, ← hβ, Category.assoc,
      ← derivedPullbackProjMap_comp, β.hom_inv_id, derivedPullbackProjMap_id, Category.comp_id]
  have h := eq_id_of_comp_derivedPullbackProjMap_eq hK _ hγ
  ext
  rw [← Category.comp_id α.hom, ← β.inv_hom_id, ← Category.assoc, h, Category.id_comp]

section Glueing

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Scheme.DerivedPullbackOpensGlueing

/-- Vanishing of negative `Ext` transports along isomorphisms in either variable. -/
theorem subsingleton_shiftedHom_of_iso' {𝒞 : Type*} [Category 𝒞] [HasShift 𝒞 ℤ] {A A' B B' : 𝒞}
    (eA : A ≅ A') (eB : B ≅ B') (n : ℤ) (h : Subsingleton (ShiftedHom A' B' n)) :
    Subsingleton (ShiftedHom A B n) :=
  Equiv.subsingleton (eA.homCongr ((shiftFunctor 𝒞 n).mapIso eB))

/-- A morphism of `D(𝒪_X)` whose derived pullbacks to the members of a covering collection of
opens (with intersections unions of members, and no negative self-Ext there) are identities is
the identity. -/
theorem eq_id_of_derivedPullback_opens_eq_id {X : Scheme.{u}} (B : Set X.Opens)
    (hcover : sSup B = ⊤) (hinter : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V = sSup {W | W ∈ B ∧ W ≤ U ⊓ V})
    {M : DerivedCategory X.Modules}
    (hExt : ∀ U ∈ B, ∀ n : ℤ, n < 0 →
      Subsingleton (ShiftedHom ((derivedPullback U.ι.toLRSHom.toShHom).obj M)
        ((derivedPullback U.ι.toLRSHom.toShHom).obj M) n))
    (γ : M ⟶ M) (h : ∀ U ∈ B, (derivedPullback U.ι.toLRSHom.toShHom).map γ = 𝟙 _) :
    γ = 𝟙 M :=
  (existsUnique_hom_of_derivedPullback_opens B hcover hinter hExt (fun U _ => 𝟙 _)
    (fun U _ V _ hVU => by
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id])).unique h
    (fun U _ => CategoryTheory.Functor.map_id _ _)

/-- **Glueing isomorphisms.** A family of isomorphisms between the derived pullbacks of `K` and
`L` to the members of a covering collection of opens, compatible with shrinking, comes from an
isomorphism `K ≅ L`, provided `K` has no negative self-Ext on the members. -/
theorem exists_iso_of_derivedPullback_opens {X : Scheme.{u}} (B : Set X.Opens)
    (hcover : sSup B = ⊤) (hinter : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V = sSup {W | W ∈ B ∧ W ≤ U ⊓ V})
    {K L : DerivedCategory X.Modules}
    (hExt : ∀ U ∈ B, ∀ n : ℤ, n < 0 →
      Subsingleton (ShiftedHom ((derivedPullback U.ι.toLRSHom.toShHom).obj K)
        ((derivedPullback U.ι.toLRSHom.toShHom).obj K) n))
    (α : ∀ U ∈ B, (derivedPullback U.ι.toLRSHom.toShHom).obj K ≅
      (derivedPullback U.ι.toLRSHom.toShHom).obj L)
    (hα : ∀ (U : X.Opens) (hU : U ∈ B) (V : X.Opens) (hV : V ∈ B) (hVU : V ≤ U),
      (resComp hVU K).symm ≪≫ (pullbackLE hVU).mapIso (α U hU) ≪≫ resComp hVU L = α V hV) :
    ∃ e : K ≅ L, ∀ U (hU : U ∈ B), (derivedPullback U.ι.toLRSHom.toShHom).map e.hom =
      (α U hU).hom := by
  have hhom : ∀ (U : X.Opens) (hU : U ∈ B) (V : X.Opens) (hV : V ∈ B) (hVU : V ≤ U),
      (resComp hVU K).inv ≫ (pullbackLE hVU).map (α U hU).hom ≫ (resComp hVU L).hom =
        (α V hV).hom := fun U hU V hV hVU => by
    have h := congrArg Iso.hom (hα U hU V hV hVU)
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h
    exact h
  have hinv : ∀ (U : X.Opens) (hU : U ∈ B) (V : X.Opens) (hV : V ∈ B) (hVU : V ≤ U),
      (resComp hVU L).inv ≫ (pullbackLE hVU).map (α U hU).inv ≫ (resComp hVU K).hom =
        (α V hV).inv := fun U hU V hV hVU => by
    have h := congrArg Iso.inv (hα U hU V hV hVU)
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] at h
    exact h
  obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_derivedPullback_opens B hcover hinter
    (fun U hU n hn => subsingleton_shiftedHom_of_iso' (Iso.refl _) (α U hU).symm n
      (hExt U hU n hn))
    (fun U hU => (α U hU).hom) hhom
  obtain ⟨ψ', hψ', -⟩ := existsUnique_hom_of_derivedPullback_opens B hcover hinter
    (fun U hU n hn => subsingleton_shiftedHom_of_iso' (α U hU).symm (Iso.refl _) n
      (hExt U hU n hn))
    (fun U hU => (α U hU).inv) hinv
  have h₁ : ψ ≫ ψ' = 𝟙 K := eq_id_of_derivedPullback_opens_eq_id B hcover hinter hExt _
    fun U hU => ((derivedPullback U.ι.toLRSHom.toShHom).map_comp ψ ψ').trans
      ((congrArg₂ (· ≫ ·) (hψ U hU) (hψ' U hU)).trans (α U hU).hom_inv_id)
  have h₂ : ψ' ≫ ψ = 𝟙 L := eq_id_of_derivedPullback_opens_eq_id B hcover hinter
      (fun U hU n hn => subsingleton_shiftedHom_of_iso' (α U hU).symm (α U hU).symm n
        (hExt U hU n hn)) _
    fun U hU => ((derivedPullback U.ι.toLRSHom.toShHom).map_comp ψ' ψ).trans
      ((congrArg₂ (· ≫ ·) (hψ' U hU) (hψ U hU)).trans (α U hU).inv_hom_id)
  exact ⟨⟨ψ, ψ', h₁, h₂⟩, hψ⟩

/-- **Glueing the normalized local isomorphisms.** Given a rule `rX` restricting maps
`Δ_*𝒪_X ⟶ L pr₁^*M|_W` to the diagonal open of `U ⟶ X ⟶ S` for every open `U`, which carries
`ξ` and `η` to relative dualizing complexes on every chart (`hK'`, `hL'`), is natural in `M`
(`hnat`) and compatible with shrinking `U` (`hle`), the relative dualizing complexes `(K, ξ)` and
`(L, η)` are related by a unique isomorphism sending `ξ` to `η`. -/
theorem existsUnique_iso_of_restrict {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    {η : D.diagonalObject ⟶ D.derivedPullbackProj L}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (hL : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D L η)
    (rX : ∀ (U : X.Opens) (M : DerivedCategory (OXMod.{u, u} X.toRingedSpace)),
      (D.diagonalObject ⟶ D.derivedPullbackProj M) →
        ((D.restrict U.ι).diagonalObject ⟶
          (D.restrict U.ι).derivedPullbackProj ((derivedPullback U.ι.toLRSHom.toShHom).obj M)))
    (hK' : ∀ U ∈ Scheme.Hom.chartOpens f, IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.restrict U.ι)
      ((derivedPullback U.ι.toLRSHom.toShHom).obj K) (rX U K ξ))
    (hL' : ∀ U ∈ Scheme.Hom.chartOpens f, IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.restrict U.ι)
      ((derivedPullback U.ι.toLRSHom.toShHom).obj L) (rX U L η))
    (hnat : ∀ (U : X.Opens) {M N : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
      (ζ : D.diagonalObject ⟶ D.derivedPullbackProj M) (φ : M ⟶ N),
      rX U N (ζ ≫ D.derivedPullbackProjMap φ) =
        rX U M ζ ≫ (D.restrict U.ι).derivedPullbackProjMap
          ((derivedPullback U.ι.toLRSHom.toShHom).map φ))
    (hle : ∀ {U V : X.Opens} (hVU : V ≤ U) {M N : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
      (ζM : D.diagonalObject ⟶ D.derivedPullbackProj M)
      (ζN : D.diagonalObject ⟶ D.derivedPullbackProj N)
      (φ : (derivedPullback U.ι.toLRSHom.toShHom).obj M ⟶
        (derivedPullback U.ι.toLRSHom.toShHom).obj N),
      rX U M ζM ≫ (D.restrict U.ι).derivedPullbackProjMap φ = rX U N ζN →
        rX V M ζM ≫ (D.restrict V.ι).derivedPullbackProjMap
          ((resComp hVU M).inv ≫ (pullbackLE hVU).map φ ≫ (resComp hVU N).hom) = rX V N ζN) :
    ∃! α : K ≅ L, ξ ≫ D.derivedPullbackProjMap α.hom = η := by
  have hcover : sSup (Scheme.Hom.chartOpens f) = ⊤ := Scheme.Hom.sSup_chartOpens f
  have hinter : ∀ U ∈ Scheme.Hom.chartOpens f, ∀ V ∈ Scheme.Hom.chartOpens f,
      U ⊓ V = sSup {W | W ∈ Scheme.Hom.chartOpens f ∧ W ≤ U ⊓ V} :=
    fun U _ V _ => Scheme.Hom.eq_sSup_chartOpens f (U ⊓ V)
  have hloc : ∀ (U : X.Opens) (hU : U ∈ Scheme.Hom.chartOpens f),
      ∃ β : (derivedPullback U.ι.toLRSHom.toShHom).obj K ≅
          (derivedPullback U.ι.toLRSHom.toShHom).obj L,
        rX U K ξ ≫ (D.restrict U.ι).derivedPullbackProjMap β.hom = rX U L η :=
    fun U hU => exists_iso_comp_eq_of_isIso (hK' U hU).isIso_diagonalAction
      (hL' U hU).isIso_diagonalAction (nonempty_iso_restrict_of_mem_chartOpens hK hL hU).some
  choose α hα using hloc
  obtain ⟨e, he⟩ := exists_iso_of_derivedPullback_opens (Scheme.Hom.chartOpens f) hcover hinter
    (fun U _ n hn => hK.subsingleton_shiftedHom_derivedPullback U hn) α
    (fun U hU V hV hVU => iso_ext_of_comp_eq (hK' V hV)
      (hle hVU ξ η (α U hU).hom (hα U hU)) (hα V hV))
  refine ⟨e, ?_, fun β hβ => iso_ext_of_comp_eq hK hβ ?_⟩
  all_goals
    obtain ⟨γ, hγ⟩ := exists_iso_comp_eq_of_isIso (isIso_diagonalAction_comp
      hK.isIso_diagonalAction e) hL.isIso_diagonalAction (Iso.refl L)
    have hγ1 : γ.hom = 𝟙 L := eq_id_of_derivedPullback_opens_eq_id (Scheme.Hom.chartOpens f)
      hcover hinter (fun U _ n hn => hL.subsingleton_shiftedHom_derivedPullback U hn) γ.hom
      fun U hU => eq_id_of_comp_derivedPullbackProjMap_eq (hL' U hU) _
        ((congrArg (· ≫ (D.restrict U.ι).derivedPullbackProjMap
            ((derivedPullback U.ι.toLRSHom.toShHom).map γ.hom))
          ((hnat U ξ e.hom).trans ((congrArg (fun x => rX U K ξ ≫
            (D.restrict U.ι).derivedPullbackProjMap x) (he U hU)).trans (hα U hU))).symm).trans
          ((hnat U (ξ ≫ D.derivedPullbackProjMap e.hom) γ.hom).symm.trans
            (congrArg (rX U L) hγ)))
    exact ((Category.comp_id _).symm.trans
      (congrArg ((ξ ≫ D.derivedPullbackProjMap e.hom) ≫ ·)
        (derivedPullbackProjMap_id (D := D) L).symm)).trans
      ((congrArg (fun x => (ξ ≫ D.derivedPullbackProjMap e.hom) ≫ D.derivedPullbackProjMap x)
        hγ1.symm).trans hγ)

end Glueing

end AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

end
