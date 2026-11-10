module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveOpenDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerAffineSpaceClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic

/-!
# `H^q_c(𝔸¹, ℤ/ℓ)` through `Ext` on the projective line

Let `Y` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k`, `Λ = ℤ/ℓ`, and `V : U → Y` an open immersion of a nonempty `U` whose complement is a
nonempty finite set of closed points. Then `H^q_c(U, Λ) = Ext^q_Y(Λ_Y, V_! Λ_U)`

* vanishes for `q = 0`: by Poincaré duality it is dual to `Ext²_Y(V_! Λ_U, Λ_Y) = H²(U, Λ)`,
  which vanishes as `U` is affine (Tag 03SC);
* vanishes for `q = 1` as soon as `H¹(U, Λ) = 0`: it is dual to `Ext¹(V_! Λ_U, Λ_Y) = H¹(U, Λ)`;
* vanishes for `q > 2`: `Y` is a curve (Tag 0A53);
* has `ℓ` elements for `q = 2`: it is dual to `Hom(V_! Λ_U, Λ_Y) = End(Λ_U)`.

For the first chart `𝔸¹_k ⊆ ℙ¹_k` the complement is a nonempty finite set of closed points (the
complement of a nonempty open in a Noetherian integral scheme of dimension one, and `𝔸¹_k` is not
proper), and `H¹(𝔸¹_k, Λ) = 0` (Kummer theory); so `H^q_c(𝔸¹_k, ℤ/ℓ)` is `ℤ/ℓ` in degree two
and zero otherwise. This is the computation `RΓ_c(𝔸¹_k̄, Λ) = Λ(-1)[-2]` used in the Fourier
inversion of Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_extensionByZeroOfRestriction_of_curve` and
  `Stacks.EtaleCohomology.natCard_ext_two_unitSheaf_extensionByZeroOfRestriction_of_curve`.
* `Stacks.EtaleCohomology.exists_finset_compl_range_fromAffineSpace`.
* `Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_extensionByZeroOfRestriction_affineChart` and
  `Stacks.EtaleCohomology.natCard_ext_two_unitSheaf_extensionByZeroOfRestriction_affineChart`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

/-- Poincaré duality is perfect for `Ext^•_Y(Λ_Y, V_! Λ_U)`, for some injective trace. -/
private theorem exists_isDualityPerfect_extensionByZeroOfRestriction_of_curve
    (f : Y ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] (hℓ : IsUnit (ℓ : k))
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    {U : Scheme.{u}} (V : U ⟶ Y) [IsOpenImmersion V] (hV : Set.range V.base = (↑S : Set Y)ᶜ)
    [Nonempty U] :
    ∃ t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ,
      Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj
          (unitSheaf (X := Y) ℓ)) := by
  obtain ⟨t, ht⟩ := exists_injective_trace_of_curve f hℓ
  exact ⟨t, (isDualityPerfect_extensionByZeroOfRestriction_unitSheaf_of_isOpenImmersion f hℓ
    (Purity.localPurity (k := k) (ℓ := ℓ) hℓ) t ht S hS V hV).1⟩

include f in
/-- **`Ext^q_Y(Λ_Y, V_! Λ_U) = 0` for `q ≠ 2`**, for an open immersion `V : U → Y` into a smooth
proper curve whose complement is a nonempty finite set of closed points, once `H¹(U, Λ) = 0`. -/
theorem subsingleton_ext_unitSheaf_extensionByZeroOfRestriction_of_curve (hℓ : IsUnit (ℓ : k))
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y)) (hSne : S.Nonempty)
    {U : Scheme.{u}} (V : U ⟶ Y) [IsOpenImmersion V] (hV : Set.range V.base = (↑S : Set Y)ᶜ)
    [Nonempty U] (h1 : Subsingleton (Ext (unitSheaf (X := U) ℓ) (unitSheaf (X := U) ℓ) 1))
    (q : ℕ) (hq : q ≠ 2) :
    Subsingleton (Ext (unitSheaf (X := Y) ℓ)
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj
        (unitSheaf (X := Y) ℓ)) q) := by
  obtain ⟨t, hPD⟩ :=
    exists_isDualityPerfect_extensionByZeroOfRestriction_of_curve f hℓ S hS V hV
  let ΛY := unitSheaf (X := Y) ℓ
  let F := (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj ΛY
  have hdual : ∀ (i j : ℕ) (h : i + j = 2), Subsingleton (Ext F ΛY j) →
      Subsingleton (Ext ΛY F i) := by
    intro i j h hj
    refine ⟨fun x y => (hPD i j h).1 ?_⟩
    ext z
    rw [Subsingleton.elim z 0, map_zero, map_zero]
  rcases (show q = 0 ∨ q = 1 ∨ 2 < q by omega) with rfl | rfl | hq3
  · refine hdual 0 2 rfl ?_
    obtain ⟨e⟩ := nonempty_extensionByZeroOfRestriction_iso_opensRange (ℓ := ℓ) V ΛY
    obtain ⟨s, hs⟩ := hSne
    have hne : V.opensRange ≠ ⊤ := fun h => by
      have hsr : s ∈ Set.range V.base := by
        change s ∈ (V.opensRange : Set Y)
        rw [h]
        trivial
      rw [hV] at hsr
      exact hsr hs
    obtain ⟨x⟩ := ‹Nonempty U›
    have : Nonempty V.opensRange := ⟨⟨V.base x, x, rfl⟩⟩
    have := subsingleton_ext_two_extensionByZeroOfRestriction_of_ne_top (ℓ := ℓ) f V.opensRange
      hne 2 (by omega)
    exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := ΛY) e.hom 2).2.subsingleton
  · refine hdual 1 1 rfl ?_
    let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V
    let A := (etaleModuleRestriction.{u, 0} (ZMod ℓ) V).obj ΛY
    let eA := unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) V
    have : Subsingleton (Ext A (unitSheaf (X := U) ℓ) 1) :=
      (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := unitSheaf (X := U) ℓ)
        eA.inv 1).2.subsingleton
    have : Subsingleton (Ext A A 1) :=
      (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := A) eA.hom 1).2.subsingleton
    exact (Stacks.ExtAdjunction.extMap_bijective adj A ΛY 1).2.subsingleton
  · have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
    exact subsingleton_ext_unitSheaf_of_curve f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le F q hq3

include f in
/-- **`Ext²_Y(Λ_Y, V_! Λ_U)` has `ℓ` elements**, for an open immersion `V : U → Y` of a nonempty
`U` into a smooth proper curve whose complement is a finite set of closed points: by Poincaré
duality it is dual to `Hom(V_! Λ_U, Λ_Y) = End(Λ_U)`, and `U` is connected. -/
theorem natCard_ext_two_unitSheaf_extensionByZeroOfRestriction_of_curve (hℓ : IsUnit (ℓ : k))
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    {U : Scheme.{u}} (V : U ⟶ Y) [IsOpenImmersion V] (hV : Set.range V.base = (↑S : Set Y)ᶜ)
    [Nonempty U] :
    Nat.card (Ext (unitSheaf (X := Y) ℓ)
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj
        (unitSheaf (X := Y) ℓ)) 2) = ℓ := by
  obtain ⟨t, hPD⟩ :=
    exists_isDualityPerfect_extensionByZeroOfRestriction_of_curve f hℓ S hS V hV
  replace hPD := hPD 2 0 rfl
  let ΛY := unitSheaf (X := Y) ℓ
  let F := (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj ΛY
  let A := (etaleModuleRestriction.{u, 0} (ZMod ℓ) V).obj ΛY
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : IsIntegral U := isIntegral_of_isOpenImmersion V
  let eA := unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) V
  have hA0 : Nat.card (Ext A A 0) = ℓ := by
    rw [Nat.card_congr (Ext.homEquiv₀ (X := A) (Y := A)),
      ← Nat.card_congr (Iso.homCongr eA eA)]
    exact natCard_end_unitSheaf (X := U) ℓ
  have hF0 : Nat.card (Ext F ΛY 0) = ℓ :=
    (Nat.card_eq_of_bijective _ (Stacks.ExtAdjunction.extMap_bijective adj A ΛY 0)).symm.trans hA0
  have : Finite (Ext F ΛY 0) := Nat.finite_of_card_ne_zero
    (hF0.trans_ne (Fact.out : ℓ.Prime).ne_zero)
  rw [Nat.card_eq_of_bijective _ hPD, ExtensionTorsor.natCard_addMonoidHom_zmod, hF0]

end Curve

/-! ### The first chart of the projective line -/

section Chart

variable (k : Type u) [Field k]

/-- **The complement of the first chart `𝔸¹_k ⊆ ℙ¹_k` is a nonempty finite set of closed
points**: it is the complement of a nonempty open in a Noetherian integral scheme of dimension
one, and it is not empty because `𝔸¹_k` is not proper over `k`. -/
theorem exists_finset_compl_range_fromAffineSpace :
    ∃ S : Finset (projectiveSpaceOver 1 (Spec (.of k))), (∀ y ∈ S, IsClosed ({y} : Set _)) ∧
      S.Nonempty ∧ Set.range (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).base =
        (↑S : Set (projectiveSpaceOver 1 (Spec (.of k))))ᶜ := by
  let Y := projectiveSpaceOver 1 (Spec (.of k))
  let V : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ⟶ projectiveSpaceOver 1 (Spec (.of k)) :=
    ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))
  have : IsOpenImmersion V := ProjectiveSpace.isOpenImmersion_fromAffineSpace 1 0 (Spec (.of k))
  have := isCurve_projectiveSpaceOver_one k
  have : IsIntegral Y := isIntegral_projectiveSpace_one k
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := {}
  have hdim : topologicalKrullDim Y = 1 := topologicalKrullDim_projectiveSpace_one k
  obtain ⟨a⟩ : Nonempty (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))) := inferInstance
  have hU : V.opensRange ≠ ⊥ := fun h => by
    have : V.base a ∈ (V.opensRange : Set Y) := ⟨a, rfl⟩
    rw [h] at this
    exact this
  have hfin := Stacks.AlgebraicGeometry.AmpleDimensionOne.finite_compl_of_ne_bot Y hdim
    V.opensRange hU
  have hgen : genericPoint Y ∈ (V.opensRange : Set Y) :=
    ((genericPoint_spec Y).mem_open_set_iff V.opensRange.2).2 ⟨V.base a, Set.mem_univ _, a, rfl⟩
  refine ⟨hfin.toFinset, fun y hy => ?_, ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hy
    exact Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint Y hdim
      fun h => hy (h ▸ hgen)
  · by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty, Set.Finite.toFinset_eq_empty, Set.compl_empty_iff] at hS
    have hclosed : IsClosed (Set.range V.base) := by
      change IsClosed (V.opensRange : Set Y)
      rw [hS]
      exact isClosed_univ
    have : IsClosedImmersion V := IsClosedImmersion.of_isPreimmersion _ hclosed
    have hover : V ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) =
        AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k) :=
      ProjectiveSpace.fromAffineSpace_over 1 0 (Spec (.of k))
    have hproper : IsProper (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)) := by
      rw [← hover]
      infer_instance
    exact not_isProper_affineSpace k (ULift.{u} (Fin 1)) hproper
  · rw [Set.Finite.coe_toFinset, compl_compl]
    rfl

variable [IsAlgClosed k]

/-- `j_! j⁻¹ Λ_Y` only depends on the image of the open immersion `j`. -/
theorem nonempty_extensionByZeroOfRestriction_iso_of_range_eq {Y U W : Scheme.{u}} (a : U ⟶ Y)
    (b : W ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b] (h : Set.range a.base = Set.range b.base)
    (F : EtaleModules.{u, 0} (ZMod ℓ) Y) :
    Nonempty ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) a).obj F ≅
      (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) b).obj F) := by
  obtain ⟨ea⟩ := nonempty_extensionByZeroOfRestriction_iso_opensRange (ℓ := ℓ) a F
  obtain ⟨eb⟩ := nonempty_extensionByZeroOfRestriction_iso_opensRange (ℓ := ℓ) b F
  have hab : a.opensRange = b.opensRange := TopologicalSpace.Opens.ext h
  rw [hab] at ea
  exact ⟨ea ≪≫ eb.symm⟩

/-- **`H^q_c(𝔸¹_k, ℤ/ℓ) = Ext^q_{ℙ¹}(Λ, j_! Λ) = 0` for `q ≠ 2`**, for any open immersion `j`
into `ℙ¹_k` with the image of the first chart. -/
theorem subsingleton_ext_unitSheaf_extensionByZeroOfRestriction_affineChart (hℓ : IsUnit (ℓ : k))
    {X : Scheme.{u}} (ι : X ⟶ projectiveSpaceOver 1 (Spec (.of k))) [IsOpenImmersion ι]
    (hι : Set.range ι.base =
      Set.range (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).base)
    (q : ℕ) (hq : q ≠ 2) :
    Subsingleton (Ext (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ)
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) ι).obj
        (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ)) q) := by
  let V : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ⟶ projectiveSpaceOver 1 (Spec (.of k)) :=
    ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))
  have : IsOpenImmersion V := ProjectiveSpace.isOpenImmersion_fromAffineSpace 1 0 (Spec (.of k))
  have := isCurve_projectiveSpaceOver_one k
  obtain ⟨S, hS, hSne, hV⟩ := exists_finset_compl_range_fromAffineSpace k
  have : NeZero (ℓ : k) := ⟨hℓ.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k ℓ
  have h1 := KummerFlag.subsingleton_ext_one_unitSheaf_affineSpace k 1 hζ hℓ
  obtain ⟨e⟩ := nonempty_extensionByZeroOfRestriction_iso_of_range_eq (ℓ := ℓ) ι V hι
    (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ)
  have := subsingleton_ext_unitSheaf_extensionByZeroOfRestriction_of_curve
    (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) hℓ S hS hSne V hV h1 q hq
  exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
    (X := unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ) e.inv q).2.subsingleton

/-- **`H²_c(𝔸¹_k, ℤ/ℓ) = Ext²_{ℙ¹}(Λ, j_! Λ)` has `ℓ` elements**, for any open immersion `j`
into `ℙ¹_k` with the image of the first chart. -/
theorem natCard_ext_two_unitSheaf_extensionByZeroOfRestriction_affineChart (hℓ : IsUnit (ℓ : k))
    {X : Scheme.{u}} (ι : X ⟶ projectiveSpaceOver 1 (Spec (.of k))) [IsOpenImmersion ι]
    (hι : Set.range ι.base =
      Set.range (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).base) :
    Nat.card (Ext (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ)
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) ι).obj
        (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ)) 2) = ℓ := by
  let V : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ⟶ projectiveSpaceOver 1 (Spec (.of k)) :=
    ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))
  have : IsOpenImmersion V := ProjectiveSpace.isOpenImmersion_fromAffineSpace 1 0 (Spec (.of k))
  have := isCurve_projectiveSpaceOver_one k
  obtain ⟨S, hS, -, hV⟩ := exists_finset_compl_range_fromAffineSpace k
  obtain ⟨e⟩ := nonempty_extensionByZeroOfRestriction_iso_of_range_eq (ℓ := ℓ) ι V hι
    (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ)
  exact (Nat.card_eq_of_bijective _ (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
    (X := unitSheaf (X := projectiveSpaceOver 1 (Spec (.of k))) ℓ) e.hom 2)).trans
    (natCard_ext_two_unitSheaf_extensionByZeroOfRestriction_of_curve
      (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) hℓ S hS V hV)

end Chart

end Stacks.EtaleCohomology

end
