module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentRationalIntersectionPoint
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelNumericalTypeGenus
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberGeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Connected
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionPushout
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.NotFromModel
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower

/-!
# Numerical types that are not associated to a model

[Stacks, Tag 0CA7] observes that not every numerical type is the numerical type associated to
a model, over a discrete valuation ring, of a smooth projective geometrically irreducible curve
over its fraction field: there are numerical types of negative genus, and two minimal numerical
types of positive genus, `n = 1, m₁ = 1, a₁₁ = 0, w₁ = 6, g₁ = 1` and
`n = 2, m₁ = m₂ = 1, -a₁₁ = -a₂₂ = a₁₂ = a₂₁ = 6, w₁ = w₂ = 6, g₁ = g₂ = 1`, are not associated
to a model either, because the special fibre would live over an extension of degree six of the
residue field, against its geometric connectedness. The numerical types themselves, with their
minimality and genus, are in
`StacksFrontier/AlgebraicGeometry/SemistableReduction/NumericalType/NotFromModel.lean`.

## Main results

* `AlgebraicGeometry.NumericalType.exists_genus_neg_not_equivalent_associatedNumericalType`:
  a numerical type of negative genus is not the numerical type associated to a model.
* `NumericalType.exists_isMinimal_genus_one_not_equivalent_associatedNumericalType` and
  `NumericalType.exists_isMinimal_genus_seven_not_equivalent_associatedNumericalType` (in the
  namespace `AlgebraicGeometry`): the two minimal numerical types of positive genus named by the
  source are not the numerical type associated to a model.
* `Stacks.Models.RegularProperModelSituation.exists_specialFiberComponentWeight_eq_pow` and
  `Stacks.Models.RegularProperModelSituation.exists_specialFiberComponentWeight_eq_pow_of_two`:
  the geometric input. If `X_k` is a single component of multiplicity one, or consists of two
  components `C₁, C₂` with `(C₁ · C₂) = [κ₁ : k] = [κ₂ : k]`, then `[κ₁ : k]` is a power of the
  exponential characteristic of `k`; six is not.

## Implementation notes

"Not the numerical type associated to a model" is stated in the strongest form: the numerical
type is equivalent ([Stacks, Tag 0C70]) to no numerical type
`Stacks.Models.RegularProperModelSituation.associatedNumericalType` ([Stacks, Tag 0CA5]) of any
regular proper model, over any discrete valuation ring, in the situation of [Stacks, Tag 0C61],
for any enumeration of the components. That situation asks of the generic curve `C` only that it
be smooth and projective with `H⁰(C, 𝒪_C) = K`, which holds for every smooth projective
geometrically irreducible curve, so the statements cover the curves of the source.

The degree-six argument is the source's, made precise: `X_k` is geometrically connected
([Stacks, Tag 0AY8]), so the global functions of the reduced special fibre are geometrically
irreducible over `k` ([Stacks, Tag 0BUG]); the field `κ₁` embeds into them (directly for one
component, by gluing along `C₁ ∩ C₂` ([Stacks, Tag 0C4J]) for two), so `κ₁` is purely
inseparable over `k` ([Stacks, Tag 0G33]), and the degree of a purely inseparable extension is
a power of the characteristic.

## References

* [Stacks Project, Tag 0CA7](https://stacks.math.columbia.edu/tag/0CA7)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Composing a geometrically connected morphism with a surjective closed immersion gives a
geometrically connected morphism: every base change of the closed immersion is a surjective
closed immersion, hence a homeomorphism. -/
private theorem geometricallyConnected_comp_of_isClosedImmersion_of_surjective
    {V X Y : Scheme.{u}} (i : V ⟶ X) (f : X ⟶ Y) [IsClosedImmersion i] [Surjective i]
    [GeometricallyConnected f] : GeometricallyConnected (i ≫ f) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  rw [← (pullbackRightPullbackFstIso f y i).hom.homeomorph.connectedSpace_iff]
  have : ConnectedSpace ↥(pullback f y) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hp : IsHomeomorph (pullback.snd i (pullback.fst f y)) :=
    isHomeomorph_iff_isEmbedding_surjective.2
      ⟨(pullback.snd i (pullback.fst f y)).isClosedEmbedding.isEmbedding,
        (pullback.snd i (pullback.fst f y)).surjective⟩
  exact hp.homeomorph.connectedSpace_iff.2 this

/-- A morphism to the spectrum of a ring factors through the spectrum of the ring of global
functions, by the map it induces on global functions. -/
private theorem toSpecΓ_comp_specMap_appTop {Y : Scheme.{u}} {A : CommRingCat.{u}}
    (y : Y ⟶ Spec A) : Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ y.appTop) = y := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **A geometrically irreducible field of constants has degree a power of the characteristic.**
If the field `κ = Γ(C, 𝒪_C)` of global functions on a component `C` of the special fibre is
geometrically irreducible over `k`, then it is purely inseparable over `k` ([Stacks, Tag 0G33]),
so its degree `[κ : k]` is a power of the exponential characteristic of `k`. -/
theorem exists_specialFiberComponentWeight_eq_pow_of_isGeometricallyIrreducible
    (Z : irreducibleComponents S.specialFiber)
    (hZ : letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
      Algebra.IsGeometricallyIrreducible S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤))
    (q : ℕ) [ExpChar S.k q] :
    ∃ r : ℕ, S.specialFiberComponentWeight Z = q ^ r := by
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  obtain ⟨hfield, hfin⟩ := S.isField_and_finite_globalSections_specialFiberComponent Z
  let : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := hfield.toField
  have : Algebra.IsAlgebraic S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    Algebra.IsAlgebraic.of_finite _ _
  have : IsPurelyInseparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    separableClosure.eq_bot_iff.1
      ((separableClosure.eq_bot_iff_geometricallyIrreducible S.k _).2 hZ)
  exact IsPurelyInseparable.finrank_eq_pow S.k _ q

/-- If the special fibre `X_k` has a single irreducible component `C`, of multiplicity one, then
`C = X_k`: the inclusion of the reduced component into the special fibre is an isomorphism. -/
theorem isIso_specialFiberComponentι_of_subsingleton
    [Subsingleton (irreducibleComponents S.specialFiber)]
    (Z : irreducibleComponents S.specialFiber) (hm : S.specialFiberMultiplicity Z = 1) :
    IsIso (S.specialFiberComponentι Z) := by
  have heq : S.specialFiberIdeal = S.specialFiberComponentIdeal Z := by
    rw [S.specialFiberIdeal_eq_prod, Fintype.prod_subsingleton _ Z, hm, pow_one]
  have hincl : ∀ (I J : S.X.IdealSheafData) (h : I ≤ J), I = J →
      IsIso (Scheme.IdealSheafData.inclusion h) := by
    rintro I J h rfl
    rw [Scheme.IdealSheafData.inclusion_id]
    infer_instance
  have := hincl _ _ (S.specialFiberIdeal_le_specialFiberComponentIdeal Z) heq
  unfold RegularModelSituation.specialFiberComponentι
  infer_instance

/-- **The weight of a reduced irreducible special fibre is a power of the characteristic.** If the
special fibre `X_k` has a single irreducible component `C`, of multiplicity one, then
`[κ : k]`, with `κ = Γ(C, 𝒪_C)`, is a power of the exponential characteristic of `k`.

Indeed `C = X_k` is geometrically connected over `k` by [Stacks, Tag 0AY8], so its field of
global functions `κ` is geometrically irreducible over `k` by [Stacks, Tag 0BUG], that is,
purely inseparable over `k` by [Stacks, Tag 0G33]. -/
theorem exists_specialFiberComponentWeight_eq_pow
    [Subsingleton (irreducibleComponents S.specialFiber)]
    (Z : irreducibleComponents S.specialFiber) (hm : S.specialFiberMultiplicity Z = 1)
    (q : ℕ) [ExpChar S.k q] :
    ∃ r : ℕ, S.specialFiberComponentWeight Z = q ^ r := by
  have hι := S.isIso_specialFiberComponentι_of_subsingleton Z hm
  let : Algebra S.k Γ(S.specialFiber, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop).hom.toAlgebra
  have hX : Algebra.IsGeometricallyIrreducible S.k Γ(S.specialFiber, ⊤) :=
    AlgebraicGeometry.ProperSectionsGeom.isGeometricallyIrreducible_globalSections_of_isProper
      S.k S.specialFiberToSpec
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have hspec : Spec.map (CommRingCat.ofHom
        (algebraMap S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤))) =
      Spec.map (S.specialFiberComponentι Z).appTop ≫
        Spec.map (CommRingCat.ofHom (algebraMap S.k Γ(S.specialFiber, ⊤))) := by
    rw [← Spec.map_comp]
    rfl
  have : IsIso (S.specialFiberComponentι Z).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have : IsIso (Spec.map (S.specialFiberComponentι Z).appTop) := inferInstance
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine S.exists_specialFiberComponentWeight_eq_pow_of_isGeometricallyIrreducible Z ?_ q
  change GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤))))
  rw [hspec, MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible]
  exact hX

/-- Let `C_Z ≠ C_W` be components of the special fibre with `(C_Z · C_W) = [κ_Z : k]`. For any
cartesian square exhibiting `P` as the intersection `C_Z ×_X C_W`, restriction of functions
`κ_Z = Γ(C_Z, 𝒪) ⟶ Γ(P, 𝒪)` is bijective: `Γ(P, 𝒪)` is a `κ_Z`-algebra of `k`-dimension
`(C_Z · C_W)` ([Stacks, Tag 0C64]). -/
private theorem bijective_appTop_of_isPullback [DecidableEq (irreducibleComponents S.specialFiber)]
    {Z W : irreducibleComponents S.specialFiber} (hZW : Z ≠ W)
    (h : S.specialFiberIntersectionMatrix Z W = S.specialFiberComponentWeight Z)
    {P : Scheme.{u}} {a : P ⟶ (S.specialFiberComponentIdeal Z).subscheme}
    {b : P ⟶ (S.specialFiberComponentIdeal W).subscheme}
    (hpb : IsPullback a b (S.specialFiberComponentIdeal Z).subschemeι
      (S.specialFiberComponentIdeal W).subschemeι) :
    Function.Bijective a.appTop := by
  let : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  let : Algebra S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      ((S.componentIntersectionIdeal Z W).subschemeι ≫
        S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have : FiniteDimensional S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    (S.isField_and_finite_globalSections_specialFiberComponent Z).2
  have hdimI : Module.finrank S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) =
      Module.finrank S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := by
    have h1 := S.specialFiberIntersectionMatrix_eq_finrank_globalSections hZW
    rw [h] at h1
    exact_mod_cast h1.symm
  have hpos : 0 < Module.finrank S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    hdimI ▸ S.specialFiberComponentWeight_pos Z
  have : Nontrivial Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    Module.nontrivial_of_finrank_pos hpos
  have : FiniteDimensional S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    Module.finite_of_finrank_pos hpos
  let φ : Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) →ₐ[S.k]
      Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    { (S.componentIntersectionIdeal Z W).subschemeι.appTop.hom with
      commutes' := fun c => rfl }
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hφ : Function.Bijective (S.componentIntersectionIdeal Z W).subschemeι.appTop :=
    ⟨hφinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      hdimI.symm).mp hφinj⟩
  let e : P ≅ (S.componentIntersectionIdeal Z W).subscheme :=
    hpb.isoPullback ≪≫ ((S.specialFiberComponentIdeal W).comapIso
      (S.specialFiberComponentIdeal Z).subschemeι).symm
  have he : e.hom ≫ (S.componentIntersectionIdeal Z W).subschemeι = a := by
    simp [e]
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  rw [← he, Scheme.Hom.comp_appTop]
  exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).comp hφ

/-- If the functions `κ_Z = Γ(C_Z, 𝒪)` on a component `C_Z` of the special fibre extend, along a
morphism `C_Z ⟶ V`, to a scheme `V` proper and geometrically connected over `k`, compatibly with
the structure morphisms, then `[κ_Z : k]` is a power of the exponential characteristic of `k`:
`κ_Z` embeds into `Γ(V, 𝒪)`, which is geometrically irreducible over `k` ([Stacks, Tag 0BUG]). -/
private theorem exists_specialFiberComponentWeight_eq_pow_of_extension
    (Z : irreducibleComponents S.specialFiber) {V : Scheme.{u}} (f : V ⟶ Spec (.of S.k))
    [GeometricallyConnected f] [IsProper f] (j : (S.specialFiberComponentIdeal Z).subscheme ⟶ V)
    (g : V ⟶ Spec Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤))
    (hj : j ≫ g = (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ)
    (hg : g ≫ Spec.map ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.specialFiberComponentToSpec Z).appTop) = f)
    (q : ℕ) [ExpChar S.k q] :
    ∃ r : ℕ, S.specialFiberComponentWeight Z = q ^ r := by
  let : Algebra S.k Γ(V, ⊤) := ((Scheme.ΓSpecIso (.of S.k)).inv ≫ f.appTop).hom.toAlgebra
  have hV : Algebra.IsGeometricallyIrreducible S.k Γ(V, ⊤) :=
    AlgebraicGeometry.ProperSectionsGeom.isGeometricallyIrreducible_globalSections_of_isProper
      S.k f
  let αZ : CommRingCat.of S.k ⟶ Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    (Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := αZ.hom.toAlgebra
  let φ : Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) ⟶ Γ(V, ⊤) :=
    (Scheme.ΓSpecIso _).inv ≫ g.appTop
  have hφj : φ ≫ j.appTop = 𝟙 _ := by
    simp only [φ, Category.assoc, ← Scheme.Hom.comp_appTop, hj, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id]
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg j.appTop hab
    rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hφj] at this
  have hφk : αZ ≫ φ = (Scheme.ΓSpecIso (.of S.k)).inv ≫ f.appTop := by
    rw [← hg, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  let φk : Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) →ₐ[S.k] Γ(V, ⊤) :=
    { φ.hom with commutes' := fun c => congrArg (fun h => h.hom c) hφk }
  exact S.exists_specialFiberComponentWeight_eq_pow_of_isGeometricallyIrreducible Z
    (Stacks.Irreducibility.TrivialSepClosure.isGeometricallyIrreducible_of_injective φk hφinj) q

/-- Let `C_Z ≠ C_W` be components of the special fibre with `(C_Z · C_W) = [κ_Z : k]` and
`(C_W · C_Z) = [κ_W : k]`, where `κ = Γ(C, 𝒪_C)`, and let `f : C_Z ∪ C_W ⟶ Spec k` restrict to
the structure morphisms of the components. Then the functions `κ_Z` on `C_Z` extend to `C_Z ∪ C_W`
over `k`: the intersection `C_Z ∩ C_W` has ring of functions both `κ_Z` and `κ_W`, so the functions
on the two components glue ([Stacks, Tag 0C4J]). -/
private theorem exists_toSpecΓ_extension_inf [DecidableEq (irreducibleComponents S.specialFiber)]
    {Z W : irreducibleComponents S.specialFiber} (hZW : Z ≠ W)
    (hZ : S.specialFiberIntersectionMatrix Z W = S.specialFiberComponentWeight Z)
    (hW : S.specialFiberIntersectionMatrix W Z = S.specialFiberComponentWeight W)
    (f : (S.specialFiberComponentIdeal Z ⊓ S.specialFiberComponentIdeal W).subscheme ⟶
      Spec (.of S.k))
    (hfZ : Scheme.IdealSheafData.inclusion inf_le_left ≫ f = S.specialFiberComponentToSpec Z)
    (hfW : Scheme.IdealSheafData.inclusion inf_le_right ≫ f = S.specialFiberComponentToSpec W) :
    ∃ g : (S.specialFiberComponentIdeal Z ⊓ S.specialFiberComponentIdeal W).subscheme ⟶
        Spec Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤),
      Scheme.IdealSheafData.inclusion inf_le_left ≫ g =
        (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ ∧
      g ≫ Spec.map ((Scheme.ΓSpecIso (.of S.k)).inv ≫
        (S.specialFiberComponentToSpec Z).appTop) = f := by
  let iZ := Scheme.IdealSheafData.inclusion (le_sup_left : S.specialFiberComponentIdeal Z ≤
    S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W)
  let iW := Scheme.IdealSheafData.inclusion (le_sup_right : S.specialFiberComponentIdeal W ≤
    S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W)
  have hpb : IsPullback iZ iW (S.specialFiberComponentIdeal Z).subschemeι
      (S.specialFiberComponentIdeal W).subschemeι :=
    Scheme.IdealSheafData.isPullback_subscheme_sup S.X _ _
  have : IsIso iZ.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).2 (S.bijective_appTop_of_isPullback hZW hZ hpb)
  have : IsIso iW.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (S.bijective_appTop_of_isPullback hZW.symm hW hpb.flip)
  let ψ : Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) ⟶
      Γ((S.specialFiberComponentIdeal W).subscheme, ⊤) := iZ.appTop ≫ inv iW.appTop
  have hψ : ψ ≫ iW.appTop = iZ.appTop := by simp [ψ]
  have hZWι : iZ ≫ S.specialFiberComponentι Z = iW ≫ S.specialFiberComponentι W := by
    apply (cancel_mono S.specialFiberι).1
    simp only [Category.assoc, S.specialFiberComponentι_specialFiberι]
    exact (Scheme.IdealSheafData.inclusion_subschemeι _).trans
      (Scheme.IdealSheafData.inclusion_subschemeι _).symm
  have hZWk : iZ ≫ S.specialFiberComponentToSpec Z = iW ≫ S.specialFiberComponentToSpec W := by
    change _ ≫ S.specialFiberComponentι Z ≫ S.specialFiberToSpec =
      _ ≫ S.specialFiberComponentι W ≫ S.specialFiberToSpec
    rw [← Category.assoc, hZWι, Category.assoc]
  have hψk : ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop) ≫ ψ =
      (Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec W).appTop := by
    rw [← cancel_mono iW.appTop, Category.assoc, hψ]
    simp only [Category.assoc, ← Scheme.Hom.comp_appTop, hZWk]
  have hpo := Scheme.IdealSheafData.isPushout_subscheme_inf
    (S.specialFiberComponentIdeal Z) (S.specialFiberComponentIdeal W)
  have hcond : iZ ≫ (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ =
      iW ≫ (S.specialFiberComponentIdeal W).subscheme.toSpecΓ ≫ Spec.map ψ := by
    rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp, hψ]
  refine ⟨hpo.desc _ _ hcond, hpo.inl_desc _ _ _, hpo.hom_ext ?_ ?_⟩
  · rw [← Category.assoc, hpo.inl_desc, toSpecΓ_comp_specMap_appTop, hfZ]
  · rw [← Category.assoc, hpo.inr_desc, Category.assoc, ← Spec.map_comp, hψk,
      toSpecΓ_comp_specMap_appTop, hfW]

/-- **The weight of a special fibre with two components meeting in their fields of constants is a
power of the characteristic.** Suppose the special fibre has exactly two irreducible components
`C_Z ≠ C_W`, with `(C_Z · C_W) = [κ_Z : k]` and `(C_W · C_Z) = [κ_W : k]`, where
`κ = Γ(C, 𝒪_C)`. Then `[κ_Z : k]` is a power of the exponential characteristic of `k`.

The scheme theoretic intersection `C_Z ∩ C_W` has ring of functions `κ_Z` and also `κ_W`, so
the functions `κ_Z` on `C_Z` and the corresponding functions on `C_W` agree on `C_Z ∩ C_W` and
glue ([Stacks, Tag 0C4J]) to functions on `(X_k)_{red} = C_Z ∪ C_W`. This embeds `κ_Z` into the
global functions of `(X_k)_{red}`, which is geometrically connected over `k`, as `X_k` is
([Stacks, Tag 0AY8]); so `κ_Z` is geometrically irreducible over `k` ([Stacks, Tags 0BUG, 037N])
and hence purely inseparable over `k`. -/
theorem exists_specialFiberComponentWeight_eq_pow_of_two
    [DecidableEq (irreducibleComponents S.specialFiber)]
    {Z W : irreducibleComponents S.specialFiber} (hZW : Z ≠ W)
    (hcover : ∀ Y : irreducibleComponents S.specialFiber, Y = Z ∨ Y = W)
    (hZ : S.specialFiberIntersectionMatrix Z W = S.specialFiberComponentWeight Z)
    (hW : S.specialFiberIntersectionMatrix W Z = S.specialFiberComponentWeight W)
    (q : ℕ) [ExpChar S.k q] :
    ∃ r : ℕ, S.specialFiberComponentWeight Z = q ^ r := by
  have hle : S.specialFiberIdeal ≤
      S.specialFiberComponentIdeal Z ⊓ S.specialFiberComponentIdeal W :=
    le_inf (S.specialFiberIdeal_le_specialFiberComponentIdeal Z)
      (S.specialFiberIdeal_le_specialFiberComponentIdeal W)
  let ρ : (S.specialFiberComponentIdeal Z ⊓ S.specialFiberComponentIdeal W).subscheme ⟶
      S.specialFiber :=
    Scheme.IdealSheafData.inclusion hle ≫ (asIso S.specialFiberι.toImage).inv
  have hρZ : Scheme.IdealSheafData.inclusion (inf_le_left : S.specialFiberComponentIdeal Z ⊓
      S.specialFiberComponentIdeal W ≤ S.specialFiberComponentIdeal Z) ≫ ρ =
      S.specialFiberComponentι Z := by
    simp only [ρ, ← Category.assoc, Scheme.IdealSheafData.inclusion_comp]
    rfl
  have hρW : Scheme.IdealSheafData.inclusion (inf_le_right : S.specialFiberComponentIdeal Z ⊓
      S.specialFiberComponentIdeal W ≤ S.specialFiberComponentIdeal W) ≫ ρ =
      S.specialFiberComponentι W := by
    simp only [ρ, ← Category.assoc, Scheme.IdealSheafData.inclusion_comp]
    rfl
  have : IsClosedImmersion ρ := by
    simp only [ρ]
    infer_instance
  have : Surjective ρ := by
    refine ⟨fun x => ?_⟩
    obtain ⟨Y, hY, hxY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({x} : Set S.specialFiber) isIrreducible_singleton
    have hx : x ∈ (⟨Y, hY⟩ : irreducibleComponents S.specialFiber).1 := hxY rfl
    rcases hcover ⟨Y, hY⟩ with h | h
    · rw [h, ← S.range_specialFiberComponentι, ← hρZ] at hx
      obtain ⟨y, rfl⟩ := hx
      exact ⟨_, rfl⟩
    · rw [h, ← S.range_specialFiberComponentι, ← hρW] at hx
      obtain ⟨y, rfl⟩ := hx
      exact ⟨_, rfl⟩
  have : GeometricallyConnected (ρ ≫ S.specialFiberToSpec) :=
    geometricallyConnected_comp_of_isClosedImmersion_of_surjective ρ S.specialFiberToSpec
  obtain ⟨g, hgZ, hgk⟩ := S.exists_toSpecΓ_extension_inf hZW hZ hW (ρ ≫ S.specialFiberToSpec)
    (by rw [← Category.assoc, hρZ]; rfl) (by rw [← Category.assoc, hρW]; rfl)
  exact S.exists_specialFiberComponentWeight_eq_pow_of_extension Z _ _ g hgZ hgk q

end Stacks.Models.RegularProperModelSituation

namespace AlgebraicGeometry.NumericalType

open Stacks.Models

/-- Equivalent numerical types have the same genus: the relabelling permutes the terms of the
two sums defining it. -/
public theorem Equivalent.genus_eq {T T' : NumericalType} (h : T.Equivalent T') :
    genus T = genus T' := by
  obtain ⟨σ, hm, ha, hw, hg⟩ := h
  unfold genus
  rw [Fintype.sum_equiv σ (fun i => T.multiplicity i * (T.weight i * (T.componentGenus i - 1)))
      (fun i => T'.multiplicity i * (T'.weight i * (T'.componentGenus i - 1)))
      (fun i => by rw [hm, hw, hg]),
    Fintype.sum_equiv σ (fun i => T.multiplicity i * T.intersection i i)
      (fun i => T'.multiplicity i * T'.intersection i i) (fun i => by rw [hm, ha])]

/-- The numerical type associated to a regular proper model has nonnegative genus, being the
genus of the generic curve (Tag 0CA4); so no numerical type of negative genus is equivalent to
it. -/
public theorem not_equivalent_associatedNumericalType_of_genus_neg (T : NumericalType)
    (hT : genus T < 0) (S : RegularProperModelSituation.{u})
    [DecidableEq (irreducibleComponents S.specialFiber)] (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    ¬ (S.associatedNumericalType n e).Equivalent T := fun h => by
  have hg := (S.associatedNumericalType_spec_and_genus n e).2
  rw [h.genus_eq] at hg
  omega

/-- A weight of six is never a power of the exponential characteristic of the field. -/
private lemma not_forall_expChar_exists_pow_eq_six {k : Type*} [Field k] {w : ℕ} (hw : w = 6)
    (h : ∀ (q : ℕ) [ExpChar k q], ∃ r : ℕ, w = q ^ r) : False := by
  obtain ⟨q, hq⟩ := ExpChar.exists k
  obtain ⟨r, hr⟩ := h q
  rw [hw] at hr
  rcases expChar_is_prime_or_one k q with hq | rfl
  · have h2 : q = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1
      (Nat.prime_two.dvd_of_dvd_pow (hr ▸ (by norm_num : 2 ∣ 6)))).symm
    have h3 : q = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1
      (Nat.prime_three.dvd_of_dvd_pow (hr ▸ (by norm_num : 3 ∣ 6)))).symm
    omega
  · simp at hr

/-- **A one-component numerical type of multiplicity one and weight six is not associated to a
model.** No numerical type with `n = 1`, `m₁ = 1` and `w₁ = 6` is equivalent to the numerical
type associated to a regular proper model `X` over a discrete valuation ring of a smooth
projective curve `C` with `H⁰(C, 𝒪_C) = K` (in particular, of a smooth projective geometrically
irreducible curve over the fraction field `K`).

Such an equivalence would make the special fibre `X_k` equal to its unique component, so that it
lives over the field `κ = Γ(X_k, 𝒪)` of degree `6` over `k`; but `X_k` is geometrically
connected (Tag 0AY8), so `κ/k` is purely inseparable, and its degree is a power of the
characteristic. -/
public theorem not_equivalent_associatedNumericalType_of_weight_eq_six (T : NumericalType)
    (hn : T.componentCount = 1) (hm : ∀ i, T.multiplicity i = 1) (hw : ∀ i, T.weight i = 6)
    (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    ¬ (S.associatedNumericalType n e).Equivalent T := by
  rintro ⟨σ, hσm, -, hσw, -⟩
  obtain rfl : n = 1 := (Fin.equiv_iff_eq.1 ⟨σ⟩).trans hn
  have : Subsingleton (irreducibleComponents S.specialFiber) := e.symm.subsingleton
  have hmZ : S.specialFiberMultiplicity (e 0) = 1 := by
    have h : ((S.specialFiberMultiplicity (e 0) : ℕ) : ℤ) = 1 := (hσm 0).trans (hm _)
    exact_mod_cast h
  have hwZ : S.specialFiberComponentWeight (e 0) = 6 := by
    have h : ((S.specialFiberComponentWeight (e 0) : ℕ) : ℤ) = 6 := (hσw 0).trans (hw _)
    exact_mod_cast h
  exact not_forall_expChar_exists_pow_eq_six (k := S.k) hwZ fun q _ =>
    S.exists_specialFiberComponentWeight_eq_pow (e 0) hmZ q

/-- **A two-component numerical type with weights and mutual intersection six is not associated
to a model.** No numerical type with `n = 2`, `w₁ = w₂ = 6` and `a₁₂ = a₂₁ = 6` is equivalent to
the numerical type associated to a regular proper model `X` over a discrete valuation ring of a
smooth projective curve `C` with `H⁰(C, 𝒪_C) = K` (in particular, of a smooth projective
geometrically irreducible curve over the fraction field `K`).

Such an equivalence would give two components `C₁, C₂` of `X_k` with `(C₁ · C₂) = [κ₁ : k] =
[κ₂ : k] = 6`, so that `C₁ ∩ C₂` has ring of functions `κ₁ ≅ κ₂`; the reduced special fibre
`C₁ ∪ C₂` then lives over the field `κ₁` of degree `6` over `k`, against geometric connectedness
of `X_k` (Tag 0AY8). -/
public theorem not_equivalent_associatedNumericalType_of_two_weight_eq_six (T : NumericalType)
    (hn : T.componentCount = 2) (ha : ∀ i j, i ≠ j → T.intersection i j = 6)
    (hw : ∀ i, T.weight i = 6)
    (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    ¬ (S.associatedNumericalType n e).Equivalent T := by
  rintro ⟨σ, -, hσa, hσw, -⟩
  obtain rfl : n = 2 := (Fin.equiv_iff_eq.1 ⟨σ⟩).trans hn
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hcover : ∀ Y, Y = e 0 ∨ Y = e 1 := by
    intro Y
    obtain ⟨i, rfl⟩ := e.surjective Y
    fin_cases i <;> simp
  have hw' : ∀ i, (S.specialFiberComponentWeight (e i) : ℤ) = 6 := fun i => (hσw i).trans (hw _)
  have ha' : ∀ i j, i ≠ j → S.specialFiberIntersectionMatrix (e i) (e j) = 6 := fun i j hij =>
    (hσa i j).trans (ha _ _ (σ.injective.ne hij))
  exact not_forall_expChar_exists_pow_eq_six (k := S.k) (by exact_mod_cast hw' 0) fun q _ =>
    S.exists_specialFiberComponentWeight_eq_pow_of_two (e.injective.ne h01) hcover
      ((ha' 0 1 h01).trans (hw' 0).symm) ((ha' 1 0 h01.symm).trans (hw' 1).symm) q

/-- **Not every numerical type comes from a model**: there is a numerical type of negative genus,
and it is equivalent to no numerical type associated to a regular proper model of a smooth
projective curve over the fraction field of a discrete valuation ring. -/
@[stacks 0CA7 "not every numerical type is the numerical type associated to a model, as there \
  are numerical types of negative genus"]
public theorem exists_genus_neg_not_equivalent_associatedNumericalType :
    ∃ T : NumericalType, genus T < 0 ∧
      ∀ (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]
        (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber),
        ¬ (S.associatedNumericalType n e).Equivalent T := by
  obtain ⟨T, hT⟩ := exists_genus_neg
  exact ⟨T, hT, fun S _ n e => not_equivalent_associatedNumericalType_of_genus_neg T hT S n e⟩

/-- **A minimal numerical type of positive genus not coming from a model**: the data `n = 1`,
`m₁ = 1`, `a₁₁ = 0`, `w₁ = 6`, `g₁ = 1` form a minimal numerical type of genus one which is
equivalent to no numerical type associated to a regular proper model, over a discrete valuation
ring `R`, of a smooth projective curve `C` over the fraction field `K` with `H⁰(C, 𝒪_C) = K`; in
particular of a smooth projective geometrically irreducible curve over `K`. The special fibre of
such a model would live over an extension of degree `6` of the residue field, against its
geometric connectedness. -/
@[stacks 0CA7 "n = 1, m₁ = 1, a₁₁ = 0, w₁ = 6, g₁ = 1 is a minimal numerical type of genus one \
  which is not the numerical type associated to a model"]
public theorem exists_isMinimal_genus_one_not_equivalent_associatedNumericalType :
    ∃ T : NumericalType, T.componentCount = 1 ∧
      (∀ i, T.multiplicity i = 1) ∧
      (∀ i j, T.intersection i j = 0) ∧
      (∀ i, T.weight i = 6) ∧
      (∀ i, T.componentGenus i = 1) ∧
      IsMinimal T ∧ genus T = 1 ∧
      ∀ (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]
        (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber),
        ¬ (S.associatedNumericalType n e).Equivalent T := by
  obtain ⟨T, hn, hm, ha, hw, hg, hmin, hgenus⟩ := exists_isMinimal_genus_one_weight_six
  exact ⟨T, hn, hm, ha, hw, hg, hmin, hgenus, fun S _ n e =>
    not_equivalent_associatedNumericalType_of_weight_eq_six T hn hm hw S n e⟩

/-- **A second minimal numerical type of positive genus not coming from a model**: the data
`n = 2`, `m₁ = m₂ = 1`, `-a₁₁ = -a₂₂ = a₁₂ = a₂₁ = 6`, `w₁ = w₂ = 6`, `g₁ = g₂ = 1` form a minimal
numerical type of genus seven which is equivalent to no numerical type associated to a regular
proper model, over a discrete valuation ring `R`, of a smooth projective curve `C` over the
fraction field `K` with `H⁰(C, 𝒪_C) = K`; in particular of a smooth projective geometrically
irreducible curve over `K`. As for the one-component example, the reduced special fibre of such a
model would live over an extension of degree `6` of the residue field, against its geometric
connectedness. -/
@[stacks 0CA7 "n = 2, m₁ = m₂ = 1, -a₁₁ = -a₂₂ = a₁₂ = a₂₁ = 6, w₁ = w₂ = 6, g₁ = g₂ = 1 is a \
  minimal numerical type of genus seven which is not the numerical type associated to a model"]
public theorem exists_isMinimal_genus_seven_not_equivalent_associatedNumericalType :
    ∃ T : NumericalType, T.componentCount = 2 ∧
      (∀ i, T.multiplicity i = 1) ∧
      (∀ i, T.intersection i i = -6) ∧
      (∀ i j, i ≠ j → T.intersection i j = 6) ∧
      (∀ i, T.weight i = 6) ∧
      (∀ i, T.componentGenus i = 1) ∧
      IsMinimal T ∧ genus T = 7 ∧
      ∀ (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]
        (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber),
        ¬ (S.associatedNumericalType n e).Equivalent T := by
  obtain ⟨T, hn, hm, hd, ha, hw, hg, hmin, hgenus⟩ := exists_isMinimal_genus_seven_weight_six
  exact ⟨T, hn, hm, hd, ha, hw, hg, hmin, hgenus, fun S _ n e =>
    not_equivalent_associatedNumericalType_of_two_weight_eq_six T hn ha hw S n e⟩

end AlgebraicGeometry.NumericalType
