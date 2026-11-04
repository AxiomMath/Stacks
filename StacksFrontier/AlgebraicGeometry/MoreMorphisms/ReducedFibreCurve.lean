module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.SmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.FieldTheory.CommonFiniteExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduced fibre theorem over a curve

Let `f : X ⟶ S` be flat and of finite type, and let `S` be Nagata, integral with function field
`K`, and regular of dimension one.  **There is a finite extension `L / K` such that, with `T` the
normalization of `S` in `Spec L` and `Y` the normalization of `X ×_S T`, the morphism `Y ⟶ T` is
smooth at every generic point of every fibre** — provided `X` is quasi-compact (for instance `S`
quasi-compact).  This is Tag 0BRQ, corrected: as stated in the source, without quasi-compactness,
it is false
(`AlgebraicGeometry.not_forall_exists_finiteExtension_smoothAt_genericPoints_fiber_normalization`),
and the source's proof starts from a finite affine open covering of `S`.

The proof is the source's.  Over a nonempty affine open `U` of `S` with Nagata ring of sections
`A`, the ring `A` is a Dedekind domain with fraction field `K`, and the inverse image of `U` in `T`
is `Spec (integralClosure A L)`; so over `U` the normalized base change along `T` is the normalized
base change of Tag 09IL.  Tag 09IL gives an extension `L_U` for each member of a finite cover of
the image of `X`, and an `L` dominating all of them works, because enlarging the extension keeps
the smoothness at the generic points of the fibres.

## Main definitions

* `AlgebraicGeometry.Scheme.genericExtensionHom`: the morphism `Spec L ⟶ S` through the generic
  point; `T` is its relative normalization.

## Main results

* `AlgebraicGeometry.smoothAt_normalization_of_isPullback_of_isOpenImmersion`: smoothness of a
  normalized scheme at the generic points of its fibres is local on the base.
* `AlgebraicGeometry.smoothAt_normalization_pullback_integralClosure_of_algHom`: over a Nagata
  Dedekind base, the property persists when the finite extension is enlarged.
* `AlgebraicGeometry.Scheme.exists_isPullback_genericExtensionHom_fromNormalization`: over a
  nonempty affine open `U`, `T` is `Spec (integralClosure Γ(S, U) L)`.
* `AlgebraicGeometry.exists_finiteExtension_smoothAt_normalization_of_forall_affine`: the gluing
  step, for extensions with any property stable under finite composita, from its affine instances.
* **Tag 0BRQ** (corrected):
  `AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular`
* `AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_normalization_of_compactSpace`:
  the same for a quasi-compact base.

## Implementation notes

"Regular of dimension one" is `AlgebraicGeometry.IsRegular S` (Tag 02IS) together with
`topologicalKrullDim S = 1`, and "Nagata" is `IsNagataScheme S` (Tag 033R), every point having an
affine neighbourhood with Nagata ring of sections; the gluing only uses such neighbourhoods.  The
function field is `S.functionField`, the stalk at the generic point, and the normalization of `S`
in `Spec L` is Mathlib's relative normalization of `S.genericExtensionHom L`.

## References

* [Stacks Project, Tag 0BRQ](https://stacks.math.columbia.edu/tag/0BRQ)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Transport along an open immersion of the base -/

/-- In a cartesian square over an open immersion `g`, the base change of `g` is an open
immersion. -/
private theorem isOpenImmersion_fst_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} [IsOpenImmersion g] (h : IsPullback fst snd f g) :
    IsOpenImmersion fst :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›

/-- In a cartesian square over `g`, a point of `T` whose image lies in the range of `g` lies in
the range of the first projection. -/
private theorem mem_range_of_isPullback {P Q R T : Scheme.{u}} {ψ : P ⟶ T} {c : P ⟶ Q}
    {t : T ⟶ R} {g : Q ⟶ R} (h : IsPullback ψ c t g) {b : T}
    (hb : t.base b ∈ Set.range g.base) : b ∈ Set.range ψ.base := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨c, hc, -⟩ := Scheme.exists_preimage_of_isPullback h b a ha.symm
  exact ⟨c, hc⟩

section OpenTransport

variable {W W' B B' : Scheme.{u}} (ψ' : W' ⟶ W) (p' : W' ⟶ B') (p : W ⟶ B) (ψ : B' ⟶ B)
  [IsOpenImmersion ψ] (hsq : IsPullback ψ' p' p ψ)
  (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
  (hW' : ∀ U : W'.Opens, IsCompact (U : Set W') → (irreducibleComponents U).Finite)

include hsq in
/-- **Smoothness of a normalized scheme at the generic points of its fibres is local on the
base.**  Let `W' = W ×_B B'` be the base change of `p : W ⟶ B` along an open immersion
`ψ : B' ⟶ B`.  If the normalization of `W'` is smooth over `B'` at every generic point of every
fibre, then the normalization of `W` is smooth over `B` at every generic point of every fibre
lying over the image of `ψ`.

Normalization commutes with the smooth base change `W' ⟶ W`
(`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_smooth`), so the normalization of `W'`
is an open subscheme of the normalization of `W`; smoothness at a point and the generic-point
condition only see a neighbourhood of the point. -/
theorem smoothAt_normalization_of_isPullback_of_isOpenImmersion
    (H : ∀ y : W'.normalizationScheme hW',
      (W'.normalization hW' ≫ p').asFiber y ∈
        genericPoints ↥((W'.normalization hW' ≫ p').fiber ((W'.normalization hW' ≫ p').base y)) →
      InfinitesimalLifting.SmoothAt (W'.normalization hW' ≫ p') y)
    (z : W.normalizationScheme hW) (hz : (W.normalization hW ≫ p).base z ∈ Set.range ψ.base)
    (hgen : (W.normalization hW ≫ p).asFiber z ∈
        genericPoints ↥((W.normalization hW ≫ p).fiber ((W.normalization hW ≫ p).base z))) :
    InfinitesimalLifting.SmoothAt (W.normalization hW ≫ p) z := by
  have := isOpenImmersion_fst_of_isPullback hsq
  have hN := isPullback_normalizationSchemeMap_of_smooth ψ' hW
  set e := normalizationSchemeMap ψ' (finite_irreducibleComponents_of_smooth ψ' hW) hW with he
  have := isOpenImmersion_fst_of_isPullback hN
  -- the square of structure morphisms
  have hcomm : e ≫ (W.normalization hW ≫ p) = (W'.normalization hW' ≫ p') ≫ ψ := by
    rw [← Category.assoc, hN.w, Category.assoc, hsq.w, Category.assoc]
  -- `z` comes from the normalization of `W'`
  obtain ⟨b', hb'⟩ := hz
  obtain ⟨w', hw'1, hw'2⟩ := Scheme.exists_preimage_of_isPullback hsq
    ((W.normalization hW).base z) b' (by rw [← Scheme.Hom.comp_apply, hb'])
  obtain ⟨z', hz'1, hz'2⟩ := Scheme.exists_preimage_of_isPullback hN z w' hw'1.symm
  subst hz'1
  have hbase : ∀ a : W'.normalizationScheme hW',
      (W.normalization hW ≫ p).base (e.base a) = ψ.base ((W'.normalization hW' ≫ p').base a) := by
    intro a
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
  -- the generic-point condition upstairs
  have hgen' : (W'.normalization hW' ≫ p').asFiber z' ∈ genericPoints
      ↥((W'.normalization hW' ≫ p').fiber ((W'.normalization hW' ≫ p').base z')) := by
    rw [mem_genericPoints_asFiber_iff] at hgen ⊢
    intro a ha hfa
    refine e.isOpenEmbedding.injective (hgen _ (ha.map e.continuous) ?_)
    rw [hbase, hbase, hfa]
  -- smoothness upstairs, pushed down along the open immersion
  obtain ⟨V, hzV, hV⟩ := H z' hgen'
  refine InfinitesimalLifting.smoothAt_of_smooth_opens _ (e ''ᵁ V) ⟨z', hzV, rfl⟩ ?_
  have hV' : Smooth (V.ι ≫ W'.normalization hW' ≫ p') := by
    have hres : (W'.normalization hW' ≫ p').resLE ⊤ V le_top ≫ (Scheme.topIso _).hom =
        V.ι ≫ W'.normalization hW' ≫ p' := by
      rw [← Category.assoc]
      simpa using Scheme.Hom.resLE_comp_ι (W'.normalization hW' ≫ p') (U := ⊤) (V := V) le_top
    rw [← hres]
    exact MorphismProperty.comp_mem _ _ _ hV inferInstance
  have hι : (e ''ᵁ V).ι = (e.isoImage V).inv ≫ V.ι ≫ e := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoImage_hom_ι]
  rw [hι, Category.assoc, Category.assoc, hcomm, ← Category.assoc V.ι]
  exact MorphismProperty.comp_mem _ _ _ inferInstance
    (MorphismProperty.comp_mem _ _ _ hV' inferInstance)

end OpenTransport

/-! ### Smoothness at generic points survives a further normalized base change -/

section Enlarge

/-- **A normalized base change along an integral closure keeps smoothness at the generic points
of the fibres.**  Let `R` be a Nagata Dedekind domain with fraction field `K`, let
`g : Y ⟶ Spec R` be flat, quasi-compact and locally of finite type with `Y` normal, smooth at
every generic point of every fibre, and let `K₁ / K` be finite with `B` the integral closure of
`R` in `K₁`.  Then the normalization of `Y ×_{Spec R} Spec B` is smooth over `Spec B` at every
generic point of every fibre.

A point `y` of the normalization lies over a point `w` of `Y ×_{Spec R} Spec B`; if `w` is in
the smooth locus of the base change, the normalization is an isomorphism near `y`
(`AlgebraicGeometry.Scheme.smoothAt_normalization_comp_of_mem_preimage_smoothLocus`).  Otherwise
the point `x = pr₁ w` of `Y` is outside the smooth locus of `g`, the smooth locus of a base
change being the preimage of the smooth locus; but by going down `x` is a generic point of its
own fibre (`AlgebraicGeometry.mem_genericPoints_asFiber_normalization_pullbackFst`), where `g`
is smooth by hypothesis. -/
theorem smoothAt_normalization_pullback_integralClosure_of_smoothAt {R : Type u} [CommRing R]
    [IsDedekindDomain R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsNagataRing R) {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) [Flat g]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsNormal Y] (K₁ : Type u) [Field K₁]
    [Algebra K K₁] [FiniteDimensional K K₁] [Algebra R K₁] [IsScalarTower R K K₁]
    (Hg : ∀ x : Y, g.asFiber x ∈ genericPoints ↥(g.fiber (g.base x)) →
      InfinitesimalLifting.SmoothAt g x)
    (hW : ∀ V : (pullback g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).Opens,
        IsCompact (V : Set (pullback g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u})) →
        (irreducibleComponents V).Finite) :
    ∀ y : (pullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).normalizationScheme hW,
      (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁))))).asFiber y ∈
        genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map
          (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))).fiber
            ((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
              (algebraMap R ↥(integralClosure R K₁))))).base y)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd g
        (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))) y := by
  intro y hygen
  have : Module.Finite R ↥(integralClosure R K₁) :=
    module_finite_integralClosure_of_isNagataRing K K₁ hR
  have : IsDedekindDomain ↥(integralClosure R K₁) :=
    isDedekindDomain_integralClosure_of_isNagataRing K K₁ hR
  have : IsNormal (Spec (.of ↥(integralClosure R K₁))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr (integralClosure.flat R K K₁)
  have : IsIntegralHom
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) := by
    rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom]
    exact fun z ↦ Algebra.IsIntegral.isIntegral z
  obtain ⟨hnorm, hflat, hlft, hqc⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K K₁ hR g
  have := hlft
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hNor : IsLocallyNoetherian ((pullback g (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).normalizationScheme hW) :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.normalization _ hW ≫ pullback.snd g
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))))
  by_cases hsm : (Scheme.normalization _ hW).base y ∈
      (pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).smoothLocus
  · exact Scheme.smoothAt_normalization_comp_of_mem_preimage_smoothLocus hW
      (pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))) y hsm
  · exfalso
    have hloc := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback
      (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))) (Or.inl ‹Flat g›)
    rw [hloc] at hsm
    have hy1 := mem_genericPoints_asFiber_comp_of_isIntegralHom
      (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) hygen
    have hcomp : (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁))))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))) =
        (Scheme.normalization _ hW ≫ pullback.fst g (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R K₁))))) ≫ g := by
      rw [Category.assoc, Category.assoc, ← pullback.condition]
    rw [hcomp] at hy1
    have hgx := mem_genericPoints_asFiber_normalization_pullbackFst g
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁)))) hW hNor hy1
    have hx := Hg _ hgx
    rw [show InfinitesimalLifting.SmoothAt g _ = Stacks.SmoothAtJacobian.Condition1 g _ from rfl,
      Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus] at hx
    exact hsm hx

/-- **The reduced fibre property persists under enlarging the extension.**  Let `A` be a Nagata
Dedekind domain with fraction field `K`, let `f : X ⟶ Spec A` be flat, quasi-compact and locally
of finite type, and let `L₀ ⊆ L₁` be finite extensions of `K`.  If the normalization of
`X ×_{Spec A} Spec (integralClosure A L₀)` is smooth over the base at every generic point of every
fibre, then so is the normalization of `X ×_{Spec A} Spec (integralClosure A L₁)`.

This is the remark the source's proof of the curve variant makes about the proof of the reduced
fibre theorem: the smooth locus of the normalized base change along the larger extension contains
the inverse image of the smooth locus along the smaller one.  The two-step normalized base change
along `A ⟶ B₀ ⟶ B₁` is the one-step one
(`AlgebraicGeometry.exists_normalizationScheme_iso_normalization_pullback_tower`), and the second
step keeps smoothness at the generic points of fibres
(`AlgebraicGeometry.smoothAt_normalization_pullback_integralClosure_of_smoothAt`). -/
theorem smoothAt_normalization_pullback_integralClosure_of_algHom {A : Type u} [CommRing A]
    [IsDedekindDomain A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hA : IsNagataRing A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L₀ : Type u) [Field L₀] [Algebra K L₀] [FiniteDimensional K L₀] [Algebra A L₀]
    [IsScalarTower A K L₀]
    (L₁ : Type u) [Field L₁] [Algebra K L₁] [FiniteDimensional K L₁] [Algebra A L₁]
    [IsScalarTower A K L₁] (φ : L₀ →ₐ[K] L₁)
    (H₀ : ∀ hW₀ : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite,
      ∀ z : (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L₀)))) : Scheme.{u}).normalizationScheme hW₀,
      (Scheme.normalization _ hW₀ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₀))))).asFiber z ∈
        genericPoints ↥((Scheme.normalization _ hW₀ ≫ pullback.snd f (Spec.map
          (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀))))).fiber
            ((Scheme.normalization _ hW₀ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap A ↥(integralClosure A L₀))))).base z)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW₀ ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀))))) z)
    (hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₁)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₁)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite) :
    ∀ z : (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L₁)))) : Scheme.{u}).normalizationScheme hW,
      (Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L₁))))).asFiber z ∈
        genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map
          (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₁))))).fiber
            ((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap A ↥(integralClosure A L₁))))).base z)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₁))))) z := by
  -- the tower `K ⟶ L₀ ⟶ L₁`
  let : Algebra L₀ L₁ := φ.toRingHom.toAlgebra
  have : IsScalarTower K L₀ L₁ := IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm
  have : IsScalarTower A L₀ L₁ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L₁, IsScalarTower.algebraMap_apply A K L₀,
      IsScalarTower.algebraMap_apply K L₀ L₁]
  have : FiniteDimensional L₀ L₁ := Module.Finite.of_restrictScalars_finite K L₀ L₁
  -- the base `B₀` and the normalized base change `Y₀` along it
  let : IsDedekindDomain ↥(integralClosure A L₀) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L₀ hA
  have : IsFractionRing ↥(integralClosure A L₀) L₀ :=
    integralClosure.isFractionRing_of_finite_extension K L₀
  have hB₀ : IsNagataRing ↥(integralClosure A L₀) := isNagataRing_integralClosure K L₀ hA
  obtain ⟨hnorm₀, hflat₀, hlft₀, hqc₀⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K L₀ hA f
  have := hnorm₀
  have := hflat₀
  have := hlft₀
  have := hqc₀
  -- the second step keeps smoothness at the generic points of fibres
  have hsm := smoothAt_normalization_pullback_integralClosure_of_smoothAt (K := L₀) hB₀
    ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀)))) :
      Scheme.{u}).normalization
        (finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀)))))) ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀)))))
    L₁ (H₀ _)
  -- the two integral closures of `A` and of `B₀` in `L₁`, identified
  have htower : algebraMap A L₁ = (algebraMap ↥(integralClosure A L₀) L₁).comp
      (algebraMap A ↥(integralClosure A L₀)) := by
    rw [IsScalarTower.algebraMap_eq ↥(integralClosure A L₀) L₀ L₁, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq A ↥(integralClosure A L₀) L₀,
      ← IsScalarTower.algebraMap_eq A L₀ L₁]
  have : IsDedekindDomain ↥(integralClosure ↥(integralClosure A L₀) L₁) :=
    isDedekindDomain_integralClosure_of_isNagataRing L₀ L₁ hB₀
  have : IsDedekindDomain ↥(integralClosure A L₁) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L₁ hA
  have : UniversallyOpen (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(integralClosure A L₀) ↥(integralClosure ↥(integralClosure A L₀) L₁)))) :=
    universallyOpen_specMap_algebraMap_integralClosure L₀ L₁ hB₀
  obtain ⟨ε, hε⟩ :=
    exists_ringEquiv_integralClosure_of_isIntegral A ↥(integralClosure A L₀) L₁ htower
  have : IsIso (CommRingCat.ofHom (ε : ↥(integralClosure A L₁) →+*
      ↥(integralClosure ↥(integralClosure A L₀) L₁))) := (RingEquiv.toCommRingCatIso ε).isIso_hom
  -- the four morphisms of bases: `A ⟶ B₀ ⟶ B₁`, `A ⟶ B` and the identification `B ≅ B₁`
  set i₀ : Spec (.of ↥(integralClosure A L₀)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₀))) with hi₀
  set hb : Spec (.of ↥(integralClosure ↥(integralClosure A L₀) L₁)) ⟶
      Spec (.of ↥(integralClosure A L₀)) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(integralClosure A L₀)
      ↥(integralClosure ↥(integralClosure A L₀) L₁))) with hhb
  set i : Spec (.of ↥(integralClosure A L₁)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L₁))) with hi
  set sb : Spec (.of ↥(integralClosure ↥(integralClosure A L₀) L₁)) ⟶
      Spec (.of ↥(integralClosure A L₁)) :=
    Spec.map (CommRingCat.ofHom (ε : ↥(integralClosure A L₁) →+*
      ↥(integralClosure ↥(integralClosure A L₀) L₁))) with hsb
  have hW₀ : ∀ U : (pullback f i₀ : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f i₀ : Scheme.{u})) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd f i₀)
  set r₀ : (pullback f i₀ : Scheme.{u}).normalizationScheme hW₀ ⟶
      Spec (.of ↥(integralClosure A L₀)) :=
    (pullback f i₀ : Scheme.{u}).normalization hW₀ ≫ pullback.snd f i₀ with hr₀
  have hV₁ : ∀ U : (pullback r₀ hb : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback r₀ hb : Scheme.{u})) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd r₀ hb)
  have hW₁ : ∀ U : (pullback f (hb ≫ i₀) : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f (hb ≫ i₀) : Scheme.{u})) →
      (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd f (hb ≫ i₀))
  -- taking the normalized base change twice along `A ⟶ B₀ ⟶ B₁` is taking it once
  obtain ⟨e, he⟩ :=
    exists_normalizationScheme_iso_normalization_pullback_tower hB₀ f i₀ hW₀ hV₁ hW₁
  obtain ⟨hnorm₂, hflat₂, hlft₂, hqc₂⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback L₀ L₁ hB₀ r₀
  have := hlft₂
  have : LocallyOfFinitePresentation ((pullback r₀ hb : Scheme.{u}).normalization hV₁ ≫
      pullback.snd r₀ hb) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  have : LocallyOfFinitePresentation ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
      pullback.snd f (hb ≫ i₀)) := by
    rw [← he]; infer_instance
  obtain ⟨hnorm₃, hflat₃, hlft₃, hqc₃⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K L₁ hA f
  have := hlft₃
  have : LocallyOfFinitePresentation ((pullback f i : Scheme.{u}).normalization hW ≫
      pullback.snd f i) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  -- across the tower comparison, an isomorphism over `Spec B₁`
  have he' : e.hom ≫ ((pullback r₀ hb : Scheme.{u}).normalization hV₁ ≫ pullback.snd r₀ hb) =
      ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫ pullback.snd f (hb ≫ i₀)) ≫
        (Iso.refl (Spec (.of ↥(integralClosure ↥(integralClosure A L₀) L₁)))).hom :=
    he.trans (Category.comp_id _).symm
  have H : ∀ y : (pullback f (hb ≫ i₀) : Scheme.{u}).normalizationScheme hW₁,
      ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
          pullback.snd f (hb ≫ i₀)).asFiber y ∈
        genericPoints ↥(((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
          pullback.snd f (hb ≫ i₀)).fiber
            (((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
              pullback.snd f (hb ≫ i₀)).base y)) →
      InfinitesimalLifting.SmoothAt ((pullback f (hb ≫ i₀) : Scheme.{u}).normalization hW₁ ≫
        pullback.snd f (hb ≫ i₀)) y := by
    intro y hy
    refine (InfinitesimalLifting.smoothAt_iso_hom_iff e (Iso.refl _) _ _ he' y).mpr
      (hsm hV₁ (e.hom.base y) ?_)
    exact (mem_genericPoints_asFiber_iso_hom_iff e (Iso.refl _) _ _ he' y).mp hy
  -- across the isomorphism of the bases `integralClosure A L₁ ≅ integralClosure B₀ L₁`
  have hj : hb ≫ i₀ = sb ≫ i := by
    rw [hsb, hi, hi₀, hhb, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hε]
  exact smoothAt_normalization_pullback_of_isIso_base f i sb (hb ≫ i₀) hj hW₁ hW H

end Enlarge

/-! ### The normalization of an integral scheme in a finite extension of its function field -/

section GenericExtension

variable (S : Scheme.{u}) [IsIntegral S] (L : Type u) [Field L] [Algebra S.functionField L]

/-- The morphism `Spec L ⟶ S` through the generic point of an integral scheme `S`, for a field
extension `L` of its function field.  The normalization of `S` in `Spec L` (Tag 035H) is the
relative normalization `(S.genericExtensionHom L).normalization` of this morphism. -/
def Scheme.genericExtensionHom : Spec (.of L) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫ S.fromSpecStalk (genericPoint S)

/-- `S.genericExtensionHom L` is quasi-compact: its source `Spec L` is a single point, so every
preimage is finite. -/
instance : QuasiCompact (S.genericExtensionHom L) :=
  ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩

/-- `S.genericExtensionHom L` is quasi-separated, its source `Spec L` being affine. -/
instance : QuasiSeparated (S.genericExtensionHom L) := inferInstance

variable {S L}

/-- Every point of `Spec L` maps to the generic point of `S`, so the preimage of a nonempty open
of `S` is everything. -/
theorem Scheme.genericExtensionHom_preimage_eq_top (U : S.Opens) [Nonempty U] :
    S.genericExtensionHom L ⁻¹ᵁ U = ⊤ := by
  have hη : genericPoint S ∈ U :=
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  refine top_le_iff.mp fun y _ ↦ ?_
  show S.fromSpecStalk (genericPoint S) _ ∈ U
  exact (show _ ⤳ genericPoint S from Scheme.range_fromSpecStalk.subset ⟨_, rfl⟩).mem_open
    U.isOpen hη

/-- The sections of `Spec L` over the preimage of a nonempty open `U` of `S` are `L`, as algebras
over `Γ(S, U)`, the algebra structure on `L` being the one through the function field. -/
def Scheme.genericExtensionHomSectionsAlgEquiv (U : S.Opens) [Nonempty U] :
    letI := ((S.genericExtensionHom L).app U).hom.toAlgebra
    letI : Algebra Γ(S, U) L :=
      ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
    Γ(Spec (.of L), S.genericExtensionHom L ⁻¹ᵁ U) ≃ₐ[Γ(S, U)] L :=
  letI := ((S.genericExtensionHom L).app U).hom.toAlgebra
  letI : Algebra Γ(S, U) L :=
    ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
  AlgEquiv.ofRingEquiv
    (f := ((Spec (.of L)).presheaf.mapIso
      (eqToIso (Scheme.genericExtensionHom_preimage_eq_top (L := L) U).symm).op ≪≫
        Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv) fun a ↦ by
    have hη : genericPoint S ∈ U :=
      ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
    have hle : ⊤ ≤ S.fromSpecStalk (genericPoint S) ⁻¹ᵁ U := by
      intro y _
      change S.fromSpecStalk (genericPoint S) y ∈ U
      exact (show _ ⤳ genericPoint S from Scheme.range_fromSpecStalk.subset ⟨y, rfl⟩).mem_open
        U.isOpen hη
    have key : (S.genericExtensionHom L).app U ≫
        (Spec (.of L)).presheaf.map (eqToHom
          (Scheme.genericExtensionHom_preimage_eq_top (L := L) U).symm).op ≫
        (Scheme.ΓSpecIso (.of L)).hom =
        S.presheaf.germ U (genericPoint S) hη ≫
          CommRingCat.ofHom (algebraMap S.functionField L) := by
      rw [← Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
      simp only [Scheme.genericExtensionHom]
      rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ hle (by simp), Category.assoc]
      rw [show (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))).appLE ⊤ ⊤
          (by simp) = (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))).appTop from
          by simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; exact Category.comp_id _]
      rw [Scheme.ΓSpecIso_naturality, ← Category.assoc]
      exact congrArg (· ≫ CommRingCat.ofHom (algebraMap S.functionField L))
        (fromSpecStalk_appLE_germ S U _ hη hle)
    exact congrArg (fun k : Γ(S, U) ⟶ CommRingCat.of L ↦ k a) key

/-- **Over a nonempty affine open `U` of `S`, the normalization of `S` in `Spec L` is the spectrum
of the integral closure of `Γ(S, U)` in `L`.**  Precisely, there is a morphism
`Spec (integralClosure Γ(S, U) L) ⟶ T` to the normalization `T` of `S` in `Spec L` making the
square with `Spec Γ(S, U) ⟶ S` cartesian, so that it identifies `Spec (integralClosure Γ(S, U) L)`
with the inverse image of `U` in `T`.  The algebra structure on `L` is the one through the
function field. -/
@[ega "IV 8.12.11" "partial"]
theorem Scheme.exists_isPullback_genericExtensionHom_fromNormalization (U : S.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    letI : Algebra Γ(S, U) L :=
      ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
    ∃ ψ : Spec (.of ↥(integralClosure Γ(S, U) L)) ⟶ (S.genericExtensionHom L).normalization,
      IsPullback ψ (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))
        (S.genericExtensionHom L).fromNormalization hU.fromSpec := by
  let : Algebra Γ(S, U) L :=
    ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
  let := ((S.genericExtensionHom L).app U).hom.toAlgebra
  have hI := relativeNormalizationPreimageIso_comp (S.genericExtensionHom L) U hU
  let ε := (Scheme.genericExtensionHomSectionsAlgEquiv (L := L) U).mapIntegralClosure
  let Xε := ε.toRingEquiv.toCommRingCatIso
  have hring : CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)) ≫ Xε.inv =
      CommRingCat.ofHom (algebraMap Γ(S, U)
        ↥(integralClosure Γ(S, U) Γ(Spec (.of L), S.genericExtensionHom L ⁻¹ᵁ U))) := by
    ext a
    exact congrArg Subtype.val (ε.symm.commutes a)
  let e₁ : ((S.genericExtensionHom L).fromNormalization ⁻¹ᵁ U).toScheme ≅
      Spec (.of ↥(integralClosure Γ(S, U) L)) :=
    relativeNormalizationPreimageIso (S.genericExtensionHom L) U hU ≪≫
      (Scheme.Spec.mapIso Xε.op).symm
  refine ⟨e₁.inv ≫ ((S.genericExtensionHom L).fromNormalization ⁻¹ᵁ U).ι, ?_⟩
  refine IsPullback.of_iso
    (isPullback_morphismRestrict (S.genericExtensionHom L).fromNormalization U).flip e₁
    (Iso.refl _) hU.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · rw [← hI]
    simp only [e₁, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv, Category.assoc]
    congr 1
    rw [← hring, Spec.map_comp]
    rfl
  · simp
  · simp

end GenericExtension

/-! ### From an affine open of the base to the whole normalized base change -/

section LocalToGlobal

variable {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) {L : Type u} [Field L]
  [Algebra S.functionField L]

/-- **The normalized base change along `S`'s normalization in `Spec L`, over an affine open.**
Let `U` be a nonempty affine open of `S` with ring of sections `A`, and let `B` be the integral
closure of `A` in `L`.  If the normalization of `(X ×_S Spec A) ×_{Spec A} Spec B` is smooth over
`Spec B` at every generic point of every fibre, then the normalization `Y` of `X ×_S T`, with `T`
the normalization of `S` in `Spec L`, is smooth over `T` at every generic point of every fibre
lying over `U`.

The inverse image of `U` in `T` is `Spec B`
(`AlgebraicGeometry.Scheme.exists_isPullback_genericExtensionHom_fromNormalization`), so the
inverse image of `U` in `X ×_S T` is `(X ×_S Spec A) ×_{Spec A} Spec B`, and the claim is local on
the base (`AlgebraicGeometry.smoothAt_normalization_of_isPullback_of_isOpenImmersion`). -/
theorem smoothAt_normalization_pullback_fromNormalization_of_affine (U : S.Opens)
    (hU : IsAffineOpen U) [Nonempty U]
    (H : letI : Algebra Γ(S, U) L :=
        ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
      ∀ hW₀ : ∀ V : (pullback (pullback.snd f hU.fromSpec) (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)))) : Scheme.{u}).Opens,
        IsCompact (V : Set (pullback (pullback.snd f hU.fromSpec) (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)))) : Scheme.{u})) →
        (irreducibleComponents V).Finite,
      ∀ z : (pullback (pullback.snd f hU.fromSpec) (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)))) : Scheme.{u}).normalizationScheme hW₀,
      (Scheme.normalization _ hW₀ ≫ pullback.snd (pullback.snd f hU.fromSpec) (Spec.map
          (CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))).asFiber z ∈
        genericPoints ↥((Scheme.normalization _ hW₀ ≫ pullback.snd (pullback.snd f hU.fromSpec)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))).fiber
            ((Scheme.normalization _ hW₀ ≫ pullback.snd (pullback.snd f hU.fromSpec) (Spec.map
              (CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))).base z)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW₀ ≫
        pullback.snd (pullback.snd f hU.fromSpec)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))) z)
    (hW : ∀ V : (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u}).Opens,
      IsCompact (V : Set (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u})) →
        (irreducibleComponents V).Finite)
    (z : (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u}).normalizationScheme
      hW)
    (hzU : (S.genericExtensionHom L).fromNormalization.base ((Scheme.normalization _ hW ≫
      pullback.snd f (S.genericExtensionHom L).fromNormalization).base z) ∈ U)
    (hgen : (Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).asFiber z ∈
      genericPoints ↥((Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber
          ((Scheme.normalization _ hW ≫
            pullback.snd f (S.genericExtensionHom L).fromNormalization).base z))) :
    InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫
      pullback.snd f (S.genericExtensionHom L).fromNormalization) z := by
  let : Algebra Γ(S, U) L :=
    ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
  obtain ⟨ψ, hψ⟩ := Scheme.exists_isPullback_genericExtensionHom_fromNormalization (L := L) U hU
  have := isOpenImmersion_fst_of_isPullback hψ
  set c := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)))
  set t := (S.genericExtensionHom L).fromNormalization
  -- the inverse image of `U` in `X ×_S T`
  have hpaste := (IsPullback.of_hasPullback (pullback.snd f hU.fromSpec) c).paste_horiz
    (IsPullback.of_hasPullback f hU.fromSpec)
  let ψ' : pullback (pullback.snd f hU.fromSpec) c ⟶ pullback f t :=
    pullback.lift (pullback.fst _ c ≫ pullback.fst f hU.fromSpec) (pullback.snd _ c ≫ ψ) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, hψ.w])
  have hsq : IsPullback ψ' (pullback.snd (pullback.snd f hU.fromSpec) c) (pullback.snd f t) ψ :=
    IsPullback.of_right (by rw [pullback.lift_fst, hψ.w]; exact hpaste) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f t)
  have := isOpenImmersion_fst_of_isPullback hsq
  refine smoothAt_normalization_of_isPullback_of_isOpenImmersion ψ' _ _ ψ hsq hW
    (finite_irreducibleComponents_of_smooth ψ' hW) (H _) z ?_ hgen
  exact mem_range_of_isPullback hψ (hU.range_fromSpec ▸ hzU)

end LocalToGlobal

/-! ### Gluing over a finite affine cover -/

section Gluing

/-- **The ring of sections of an integral regular scheme of dimension at most one over a nonempty
affine open is a Dedekind domain.**  It is a Noetherian domain, integrally closed because a regular
scheme is normal, and of Krull dimension at most one because `Spec Γ(S, U)` is an open subspace of
`S`. -/
theorem isDedekindDomain_sections_of_isRegular {S : Scheme.{u}} [IsIntegral S] (hR : IsRegular S)
    (hdim : topologicalKrullDim S ≤ 1) (U : S.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsDedekindDomain Γ(S, U) := by
  have := isLocallyNoetherian_of_isRegular hR
  have : IsNormal S := isNormal_of_isRegular S hR
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(S, U) :=
    (isNormal_iff_forall_affineOpen_normal S).mp inferInstance ⟨U, hU⟩ inferInstance
  have hd : ringKrullDim Γ(S, U) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (hU.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hdim
  have : Ring.KrullDimLE 1 Γ(S, U) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hd)
  have : Ring.DimensionLEOne Γ(S, U) := ⟨fun hne hp ↦ hp.isMaximal_of_ne_bot hne⟩
  exact { toIsDomain := inferInstance
          toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance }

/-- Smoothness at the generic points of the fibres, read on the points of the fibres, gives it on
the points of the source that are generic points of their own fibre. -/
theorem smoothAt_of_forall_smoothAt_fiberι {W B : Scheme.{u}} (g : W ⟶ B)
    (H : ∀ (b : B) (y : g.fiber b), y ∈ genericPoints ↥(g.fiber b) →
      InfinitesimalLifting.SmoothAt g (g.fiberι b y))
    (z : W) (hz : g.asFiber z ∈ genericPoints ↥(g.fiber (g.base z))) :
    InfinitesimalLifting.SmoothAt g z := by
  simpa only [g.fiberι_asFiber] using H _ _ hz

/-- **The reduced fibre theorem over a curve, from its affine instances.**  Let `f : X ⟶ S` be
flat, quasi-compact and locally of finite type with `X` quasi-compact, and let `S` be an integral
Nagata scheme, regular of dimension one, with function field `K`.  Let `P` be a property of finite
extensions of `K` such that finitely many extensions with `P` embed into a common one with `P`.
Assume that over every nonempty affine open `U` of `S` with Nagata ring of sections `A` (a
Dedekind domain with fraction field `K`) some finite extension `L_U` with `P` makes the normalized
base change of `X ×_S Spec A` along `Spec (integralClosure A L_U)` smooth at every generic point
of every fibre.  **Then there is a finite extension `L / K` with `P` such that, with `T` the
normalization of `S` in `Spec L`, the normalization `Y` of `X ×_S T` is smooth over `T` at every
generic point of every fibre.**

This is the proof of Tag 0BRQ from Tag 09IL (and of Tag 0BRS from Tag 0BRR, with `P` the
separability of the extension): cover the image of `X` by finitely many affine opens with Nagata
rings, take `L` dominating the `L_U`, and observe that over each `U` the normalized base change
along `L` is the one along `integralClosure A L`
(`AlgebraicGeometry.smoothAt_normalization_pullback_fromNormalization_of_affine`), which is
smooth at the generic points of the fibres because that along the smaller `L_U` is
(`AlgebraicGeometry.smoothAt_normalization_pullback_integralClosure_of_algHom`).

The per-affine hypothesis is stated exactly in the form of the conclusion of Tag 09IL
(`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`)
for `X ×_S Spec A ⟶ Spec A`, with the canonical `Γ(S, U)`-algebra structure on the function field
(`AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen`). -/
theorem exists_finiteExtension_smoothAt_normalization_of_forall_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace X] [IsIntegral S] (hN : IsNagataScheme S) (hR : IsRegular S)
    (hdim : topologicalKrullDim S = 1)
    (P : ∀ (L : Type u) [Field L] [Algebra S.functionField L], Prop)
    (hP : ∀ (ι : Type u) [Finite ι] (F : ι → Type u) [∀ i, Field (F i)]
      [∀ i, Algebra S.functionField (F i)] [∀ i, FiniteDimensional S.functionField (F i)],
      (∀ i, P (F i)) → ∃ (E : Type u) (_ : Field E) (_ : Algebra S.functionField E)
        (_ : FiniteDimensional S.functionField E), P E ∧
          Nonempty (∀ i, F i →ₐ[S.functionField] E))
    (hloc : ∀ (U : S.Opens) (hU : IsAffineOpen U) [Nonempty U], IsNagataRing Γ(S, U) →
      IsDedekindDomain Γ(S, U) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
        (_ : FiniteDimensional S.functionField L) (_ : Algebra Γ(S, U) L)
        (_ : IsScalarTower Γ(S, U) S.functionField L), P L ∧
        ∃ hW : ∀ V : (pullback (pullback.snd f hU.fromSpec) (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)))) : Scheme.{u}).Opens,
          IsCompact (V : Set (pullback (pullback.snd f hU.fromSpec) (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)))) : Scheme.{u})) →
          (irreducibleComponents V).Finite,
        ∀ b : Spec (.of ↥(integralClosure Γ(S, U) L)),
        ∀ y : (Scheme.normalization _ hW ≫ pullback.snd (pullback.snd f hU.fromSpec)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))).fiber
            b,
        y ∈ genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd (pullback.snd f
          hU.fromSpec) (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))).fiber b) →
        InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd (pullback.snd f
            hU.fromSpec) (Spec.map (CommRingCat.ofHom
              (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)))))
          ((Scheme.normalization _ hW ≫ pullback.snd (pullback.snd f hU.fromSpec)
            (Spec.map (CommRingCat.ofHom
              (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))))).fiberι b y)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
      (_ : FiniteDimensional S.functionField L), P L ∧
      ∃ hW : ∀ V : (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u}).Opens,
        IsCompact (V : Set (pullback f (S.genericExtensionHom L).fromNormalization :
          Scheme.{u})) → (irreducibleComponents V).Finite,
      ∀ b : (S.genericExtensionHom L).normalization,
      ∀ y : (Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b,
      y ∈ genericPoints ↥((Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization)
        ((Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiberι b y) := by
  classical
  have := isLocallyNoetherian_of_isRegular hR
  -- a finite cover of the image of `X` by affine opens with Nagata rings of sections
  choose V₀ hxV hVN using hN
  set V : S → S.Opens := fun x ↦ (V₀ x).1 with hVdef
  have hVa : ∀ x, IsAffineOpen (V x) := fun x ↦ (V₀ x).2
  obtain ⟨t, ht⟩ := (isCompact_range f.continuous).elim_finite_subcover
    (fun x ↦ (V x : Set S)) (fun x ↦ (V x).isOpen)
    (fun s _ ↦ Set.mem_iUnion.mpr ⟨s, hxV s⟩)
  have hne : ∀ x : S, Nonempty (V x) := fun x ↦ ⟨⟨x, hxV x⟩⟩
  have hded : ∀ x : S, IsDedekindDomain Γ(S, V x) := fun x ↦
    isDedekindDomain_sections_of_isRegular hR hdim.le _ (hVa x)
  -- the extensions over the members of the cover, and one finite extension dominating them
  choose F hFfield hFalg hFfin hFA hFtower hFP hFgood using
    fun i : t ↦ hloc (V i) (hVa i) (hVN i) (hded i)
  obtain ⟨E, hEfield, hEalg, hEfin, hEP, ⟨φ⟩⟩ := hP t F hFP
  let := hEfield
  let := hEalg
  have := hEfin
  -- the normalization `T` of `S` in `Spec E` is locally Noetherian
  have hψ : ∀ x : S, let : Algebra Γ(S, V x) E :=
      ((algebraMap S.functionField E).comp (algebraMap Γ(S, V x) S.functionField)).toAlgebra
      ∃ ψ : Spec (.of ↥(integralClosure Γ(S, V x) E)) ⟶ (S.genericExtensionHom E).normalization,
        IsPullback ψ (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, V x) ↥(integralClosure Γ(S, V x) E))))
          (S.genericExtensionHom E).fromNormalization (hVa x).fromSpec := fun x ↦
    Scheme.exists_isPullback_genericExtensionHom_fromNormalization (L := E) (V x) (hVa x)
  choose ψ hψ using hψ
  have : ∀ x : S, IsOpenImmersion (ψ x) := fun x ↦ isOpenImmersion_fst_of_isPullback (hψ x)
  have : IsLocallyNoetherian (S.genericExtensionHom E).normalization := by
    refine (isLocallyNoetherian_iff_openCover (Scheme.Cover.mkOfCovers S _ ψ fun b ↦ ?_)).mpr
      fun x ↦ ?_
    · exact ⟨_, mem_range_of_isPullback (hψ _) (by rw [(hVa _).range_fromSpec]; exact hxV _)⟩
    · have := hne x
      let : Algebra Γ(S, V x) E :=
        ((algebraMap S.functionField E).comp (algebraMap Γ(S, V x) S.functionField)).toAlgebra
      have := functionField_isFractionRing_of_isAffineOpen S (V x) (hVa x)
      have : IsScalarTower Γ(S, V x) S.functionField E :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      have := hded x
      have : IsDedekindDomain ↥(integralClosure Γ(S, V x) E) :=
        isDedekindDomain_integralClosure_of_isNagataRing S.functionField E (hVN x)
      show IsLocallyNoetherian (Spec (.of ↥(integralClosure Γ(S, V x) E)))
      infer_instance
  have : IsLocallyNoetherian
      (pullback f (S.genericExtensionHom E).fromNormalization : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd f (S.genericExtensionHom E).fromNormalization)
  refine ⟨E, hEfield, hEalg, hEfin, hEP,
    finite_irreducibleComponents_of_isCompact _, fun b y hy ↦ ?_⟩
  -- the point, read in the ambient scheme, and a member of the cover containing its image
  have hgen := mem_genericPoints_asFiber_fiberι _ b y hy
  set z := (Scheme.normalization _ (finite_irreducibleComponents_of_isCompact
      (pullback f (S.genericExtensionHom E).fromNormalization)) ≫
    pullback.snd f (S.genericExtensionHom E).fromNormalization).fiberι b y with hz
  have hzX : (S.genericExtensionHom E).fromNormalization.base
      ((Scheme.normalization _ (finite_irreducibleComponents_of_isCompact
        (pullback f (S.genericExtensionHom E).fromNormalization)) ≫
      pullback.snd f (S.genericExtensionHom E).fromNormalization).base z) ∈ Set.range f.base := by
    refine ⟨(pullback.fst f (S.genericExtensionHom E).fromNormalization).base
      ((Scheme.normalization _ _).base z), ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
  obtain ⟨i, hit, hiV⟩ := Set.mem_iUnion₂.mp (ht hzX)
  let i' : t := ⟨i, hit⟩
  let := hFfield i'
  let := hFalg i'
  have := hFfin i'
  let := hFA i'
  have := hFtower i'
  have := hded i
  have := functionField_isFractionRing_of_isAffineOpen S (V i) (hVa i)
  let : Algebra Γ(S, V i) E :=
    ((algebraMap S.functionField E).comp (algebraMap Γ(S, V i) S.functionField)).toAlgebra
  have : IsScalarTower Γ(S, V i) S.functionField E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨hW₀, hgood⟩ := hFgood i'
  refine smoothAt_normalization_pullback_fromNormalization_of_affine f (V i) (hVa i) ?_ _ z
    hiV hgen
  exact smoothAt_normalization_pullback_integralClosure_of_algHom (hVN i)
    (pullback.snd f (hVa i).fromSpec) (F i') E (φ i')
    (fun _ z hz ↦ smoothAt_of_forall_smoothAt_fiberι _ hgood z hz)

end Gluing

/-! ### The reduced fibre theorem over a curve -/

/-- **Stacks Project, Tag 0BRQ (variant of the reduced fibre theorem over curves), corrected:
the source omits quasi-compactness, and the statement is false without it.**  Let `f : X ⟶ S` be
flat and of finite type with `X` quasi-compact.  Assume `S` is Nagata, integral with function
field `K`, and regular of dimension `1`.  Then there is a finite extension `L / K` such that, with
`T` the normalization of `S` in `Spec L` (`(S.genericExtensionHom L).normalization`, Tag 035H) and
`ν : Y ⟶ X ×_S T` the normalization, the morphism `g = ν ≫ pr₂ : Y ⟶ T` is smooth at every
generic point of every fibre.

The finiteness witness `hW` is the one the normalization of a scheme takes as an argument; it is a
theorem here (`X ×_S T` is locally Noetherian), not a hypothesis.

**Correction.**  The source states the lemma for arbitrary `S`, and its proof begins "choose a
finite affine open covering of `S`".  Without quasi-compactness the statement is false: this is
`AlgebraicGeometry.not_forall_exists_finiteExtension_smoothAt_genericPoints_fiber_normalization`,
the negation of the statement exactly as the source writes it, in the vocabulary of this theorem.
There `S` is the affine line over a field `k` with infinitely many origins (countably many copies
of `Spec k[t]` glued along `Spec k[t, t⁻¹]`), integral, regular of dimension one and Nagata but not
quasi-compact, and `X` is glued from countably many copies of the plane `Spec k[x, y]` along the
torus `Spec k[x, t, (xt)⁻¹]`, the `n`-th copy lying over the `n`-th copy of the line by
`t = x ^ (n + 1) y`; `f` is flat, affine and of finite type.  Over the `n`-th origin the fibre
contains the line `x = 0` with multiplicity `n + 1`, and smoothness of `g` at the generic points
of the fibres over the points of `T` above it forces `n + 1 ≤ [L : K]`; no `L` serves every `n`.
Quasi-compactness of `S` repairs the statement, and it is enough that `X` be quasi-compact, since
then only the finitely many affine opens of `S` covering the image of `X` matter; with `S`
quasi-compact this is
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_normalization_of_compactSpace`.

The proof is the source's: cover the image of `X` by finitely many affine opens `Spec A_i` with
`A_i` a Nagata Dedekind domain with fraction field `K`, apply Tag 09IL
(`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`)
over each, and take `L` dominating the resulting extensions; this is
`AlgebraicGeometry.exists_finiteExtension_smoothAt_normalization_of_forall_affine`
with the trivial property. -/
@[stacks 0BRQ "corrected statement: the source omits quasi-compactness and is false without it \
(`not_forall_exists_finiteExtension_smoothAt_genericPoints_fiber_normalization`); stated here with \
`X` quasi-compact, which is implied by `S` quasi-compact (see the `_of_compactSpace` corollary)"]
theorem exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace X] [IsIntegral S] (hN : IsNagataScheme S) (hR : IsRegular S)
    (hdim : topologicalKrullDim S = 1) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
      (_ : FiniteDimensional S.functionField L),
      ∃ hW : ∀ V : (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u}).Opens,
        IsCompact (V : Set (pullback f (S.genericExtensionHom L).fromNormalization :
          Scheme.{u})) → (irreducibleComponents V).Finite,
      ∀ b : (S.genericExtensionHom L).normalization,
      ∀ y : (Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b,
      y ∈ genericPoints ↥((Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization)
        ((Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiberι b y) := by
  obtain ⟨L, h₁, h₂, h₃, -, h⟩ :=
    exists_finiteExtension_smoothAt_normalization_of_forall_affine f hN hR
      hdim (fun _ _ _ ↦ True)
      (fun ι _ F _ _ _ _ ↦ by
        obtain ⟨E, hE₁, hE₂, hE₃, hφ⟩ :=
          exists_finiteDimensional_algHom_forall (K := S.functionField) F
        exact ⟨E, hE₁, hE₂, hE₃, trivial, hφ⟩)
      (fun U hU _ hA hD ↦ by
        have := hD
        have := functionField_isFractionRing_of_isAffineOpen S U hU
        obtain ⟨L, h₁, h₂, h₃, h₄, h₅, h⟩ :=
          exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback
            (A := Γ(S, U)) S.functionField hA (pullback.snd f hU.fromSpec)
        exact ⟨L, h₁, h₂, h₃, h₄, h₅, trivial, h⟩)
  exact ⟨L, h₁, h₂, h₃, h⟩

/-- **Tag 0BRQ for a quasi-compact base.**  Let `f : X ⟶ S` be flat and of finite type, and let
`S` be quasi-compact, Nagata, integral with function field `K`, and regular of dimension `1`.
Then there is a finite extension `L / K` such that, with `T` the normalization of `S` in `Spec L`
and `ν : Y ⟶ X ×_S T` the normalization, `Y ⟶ T` is smooth at every generic point of every
fibre.  This is the form in which the source's proof applies; `X` is then quasi-compact, and the
statement is
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular`.
-/
theorem exists_finiteExtension_smoothAt_genericPoints_normalization_of_compactSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace S] [IsIntegral S] (hN : IsNagataScheme S) (hR : IsRegular S)
    (hdim : topologicalKrullDim S = 1) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
      (_ : FiniteDimensional S.functionField L),
      ∃ hW : ∀ V : (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u}).Opens,
        IsCompact (V : Set (pullback f (S.genericExtensionHom L).fromNormalization :
          Scheme.{u})) → (irreducibleComponents V).Finite,
      ∀ b : (S.genericExtensionHom L).normalization,
      ∀ y : (Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b,
      y ∈ genericPoints ↥((Scheme.normalization _ hW ≫
        pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization)
        ((Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiberι b y) :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular f hN hR hdim

end AlgebraicGeometry

end
