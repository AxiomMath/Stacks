module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.BaseChange
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexFactorization
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# The degree of the intersection with the closure of the complement

Let `X` be a proper scheme over a field `k` and let `C ⊆ X` be a rational tail or a rational
bridge, meeting the closure `X'` of its complement in the closed subscheme `C ∩ X'`. Its degree
`deg(C ∩ X') = dim_k Γ(C ∩ X', 𝒪)` is `[k' : k]` for a rational tail and `2 [k' : k]` for a
rational bridge, where `k' = Γ(C, 𝒪_C)`.

For a rational tail, `C ∩ X'` is the reduced attaching point, which maps isomorphically to
`Spec k'` (`AlgebraicGeometry.isIso_inclusion_comp_toSpecΓ_of_isRationalTail`). For a rational
bridge, `Γ(C ∩ X', 𝒪)` has dimension two over `k'` by definition, and the tower `k ⊆ k'` gives the
factor `[k' : k]`.

## Main results

* `AlgebraicGeometry.finrank_globalSections_intersection_of_isRationalTail`:
  `deg(C ∩ X') = [k' : k]` for a rational tail.
* `AlgebraicGeometry.finrank_globalSections_intersection_of_isRationalBridge`:
  `deg(C ∩ X') = 2 [k' : k]` for a rational bridge.
* `AlgebraicGeometry.eulerCharacteristic_unit_of_isRationalTail`: `χ(C, 𝒪_C) = [k' : k]` for a
  rational tail.
* `AlgebraicGeometry.finrank_cohomologyOverField_comp_SpecMap`: `dim_k Hⁿ = [k' : k] dim_{k'} Hⁿ`
  for a scheme over `k'`.
* `AlgebraicGeometry.finsum_finrank_dualizingSheafOverField_eq_neg`: `χ(ω) = -χ(𝒪)` over a
  subfield of the global functions, when the dualizing sheaf is invertible.
* `AlgebraicGeometry.invertibleCurveDegree_eq_sub_two_mul_of_shortExact`:
  `deg ℒ = χ(𝒪_{C ∩ X'}) - 2 χ(𝒪_C)` for an invertible extension of `𝒪_{C ∩ X'}` by `ω_C`.
* `AlgebraicGeometry.invertibleCurveDegree_eq_neg_of_isRationalTail`: an invertible extension of
  `𝒪_{C ∩ X'}` by `ω_C` on a rational tail has degree `-[k' : k]`; this is the computation of
  [Stacks, Tag 0E63] once the sequence of [Stacks, Tag 0E34] is supplied.
* `AlgebraicGeometry.invertibleCurveDegree_eq_zero_of_isRationalBridge`: the same on a rational
  bridge has degree zero, the computation of [Stacks, Tag 0E64].
* `AlgebraicGeometry.invertibleCurveDegree_eq_of_shortExact`: the degree of an invertible module
  that is an extension of `ι_* 𝒪_P` by a coherent module, through Euler characteristics.

## References

* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The `k`-algebra structure on global sections of `Y` over `k` is the one over `k'` restricted
along `k ⟶ k'`, when `Y ⟶ Spec k` factors through `Spec k'`. -/
private theorem hom_ΓSpecIso_inv_comp_appTop_comp_SpecMap (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {Y : Scheme.{u}} (f' : Y ⟶ Spec (.of k')) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))).appTop).hom =
      ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop).hom.comp (algebraMap k k') := by
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k k'))
  have hnat' : (Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))).appTop =
      CommRingCat.ofHom (algebraMap k k') ≫ (Scheme.ΓSpecIso (.of k')).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, hnat']
  rfl

/-- The structure map to the global sections of `C ∩ X'` factors through those of `C`. -/
private theorem hom_ΓSpecIso_inv_comp_appTop_intersectionWithComplementaryCurveIdeal
    (C : X.IdealSheafData) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom =
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom := by
  rw [← Scheme.IdealSheafData.inclusion_subschemeι (le_sup_left : C ≤ _)]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc]

/-- **The intersection of a rational tail with the closure of its complement has degree
`[k' : k]`.** The inclusion of the reduced attaching point followed by `C ⟶ Spec Γ(C, 𝒪_C)` is
an isomorphism, so `Γ(C, 𝒪_C) ⟶ Γ(C ∩ X', 𝒪)` is an isomorphism of `k`-algebras. -/
theorem finrank_globalSections_intersection_of_isRationalTail {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) :
    letI : Algebra k Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
          (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    letI : Algebra k Γ(C.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    Module.finrank k Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) =
      Module.finrank k Γ(C.subscheme, ⊤) := by
  let I := intersectionWithComplementaryCurveIdeal C
  let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
  let algI : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let algC : Algebra k Γ(C.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  have := isIso_inclusion_comp_toSpecΓ_of_isRationalTail hC
  have : IsIso iC.appTop := by
    have : IsIso (C.subscheme.toSpecΓ.appTop ≫ iC.appTop) := by
      rw [← Scheme.Hom.comp_appTop]
      exact inferInstanceAs (IsIso (Scheme.Γ.map (iC ≫ C.subscheme.toSpecΓ).op))
    have : IsIso C.subscheme.toSpecΓ.appTop := by
      rw [Scheme.toSpecΓ_appTop]
      infer_instance
    exact IsIso.of_isIso_comp_left C.subscheme.toSpecΓ.appTop iC.appTop
  let algCI : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := iC.appTop.hom.toAlgebra
  have : IsScalarTower k Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) :=
    .of_algebraMap_eq fun r => congrArg (· r)
      (hom_ΓSpecIso_inv_comp_appTop_intersectionWithComplementaryCurveIdeal (k := k) C)
  let e : Γ(C.subscheme, ⊤) ≃ₐ[k] Γ(I.subscheme, ⊤) :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k _ _)
      (ConcreteCategory.bijective_of_isIso iC.appTop)
  exact e.toLinearEquiv.finrank_eq.symm

/-- **The intersection of a rational bridge with the closure of its complement has degree
`2 [k' : k]`.** By definition `Γ(C ∩ X', 𝒪)` has dimension two over `k' = Γ(C, 𝒪_C)`, and the
`k`-algebra structures come from the same structure morphism, so the tower law applies. -/
theorem finrank_globalSections_intersection_of_isRationalBridge [IsProper (X ↘ Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    letI : Algebra k Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
          (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    letI : Algebra k Γ(C.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    Module.finrank k Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) =
      2 * Module.finrank k Γ(C.subscheme, ⊤) := by
  let I := intersectionWithComplementaryCurveIdeal C
  let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
  let algI : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let algC : Algebra k Γ(C.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let algCI : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := iC.appTop.hom.toAlgebra
  have : IsScalarTower k Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) :=
    .of_algebraMap_eq fun r => congrArg (· r)
      (hom_ΓSpecIso_inv_comp_appTop_intersectionWithComplementaryCurveIdeal (k := k) C)
  have : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  have h2 : Module.finrank Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) = 2 :=
    hC.intersection_finrank_eq_two
  have : Module.Free Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := Module.Free.of_divisionRing _ _
  rw [← Module.finrank_mul_finrank k Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤), h2, mul_comm]

/-- **The Euler characteristic of the structure sheaf of a rational tail is `[k' : k]`**: its
global sections are `k' = Γ(C, 𝒪_C)` and its genus is zero. -/
theorem eulerCharacteristic_unit_of_isRationalTail [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    letI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
    letI : Algebra k Γ(C.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    eulerCharacteristic k (C.subschemeι ≫ (X ↘ Spec (.of k)))
        (SheafOfModules.unit C.subscheme.ringCatSheaf) =
      (Module.finrank k Γ(C.subscheme, ⊤) : ℤ) := by
  rw [eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus k _
    (le_of_eq (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C
      hC)), hC.genus_eq_zero]
  simp

/-- **The degree of an invertible module that is an extension of a module supported on a closed
subscheme.** Let `Y` be proper of dimension at most one over `k`, and let
`0 ⟶ 𝒜 ⟶ ℒ ⟶ ι_* 𝒪_P ⟶ 0` be a short exact sequence of `𝒪_Y`-modules with `ℒ` invertible, `𝒜`
coherent and `ι : P ⟶ Y` a closed immersion. Then `deg ℒ = χ(𝒜) + χ(P, 𝒪_P) - χ(Y, 𝒪_Y)`, by
additivity of Euler characteristics and their invariance under `ι_*`. This is the shape of the
computation `deg(ω_X|_C) = χ(ω_C) + deg(C ∩ X') - χ(C, 𝒪_C)` in [Stacks, Tag 0E63] and
[Stacks, Tag 0E64]. -/
theorem invertibleCurveDegree_eq_of_shortExact {Y P : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [IsProper g] (hdim : topologicalKrullDim Y ≤ 1) {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 S.X₂]
    [S.X₁.IsCoherent] (ι : P ⟶ Y) [IsClosedImmersion ι]
    (e : S.X₃ ≅ (Scheme.Modules.pushforward ι).obj (SheafOfModules.unit P.ringCatSheaf)) :
    invertibleCurveDegree k g hdim S.X₂ =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k g S.X₁ n) : ℤ)) +
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
          (cohomologyOverField k (ι ≫ g) (SheafOfModules.unit P.ringCatSheaf) n) : ℤ)) -
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
          (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ) := by
  have : IsLocallyNoetherian Y :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k g
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (ι ≫ g)
  have : (SheafOfModules.unit P.ringCatSheaf).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : S.X₃.IsCoherent := isCoherent_of_moduleIso e.symm inferInstance
  have : S.X₂.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k g S.X₂ 1
  have hfin (F : Y.Modules) [F.IsCoherent] (n : ℕ) :
      FiniteDimensional k (cohomologyOverField k g F n) :=
    finiteDimensional_cohomologyOverField_of_isProper k g F n
  have hadd := finsum_alternating_finrank_cohomologyOverField_add_of_shortExact k g hS
    (hfin S.X₁) (hfin S.X₂) (hfin S.X₃) 2
    (fun n hn => isZero_cohomologyOverField_two_le k g hdim _ n hn)
    (fun n hn => isZero_cohomologyOverField_two_le k g hdim _ n hn)
    (fun n hn => isZero_cohomologyOverField_two_le k g hdim _ n hn)
  have h3 : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k g S.X₃ n) : ℤ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k (ι ≫ g) (SheafOfModules.unit P.ringCatSheaf) n) : ℤ) :=
    finsum_congr fun n => by
      rw [finrank_cohomologyOverField_eq_of_iso k g e n]
      exact congrArg (fun m : ℕ => (-1 : ℤ) ^ n * (m : ℤ))
        (finrank_cohomologyOverField_pushforward_of_isClosedImmersion k ι g _ n).symm
  unfold invertibleCurveDegree
  rw [hadd, h3]

/-- The Euler characteristic of the structure sheaf is the dimension of the ring of global
functions when all higher cohomology vanishes. -/
private theorem finsum_alternating_finrank_unit_eq_finrank_of_isZero {P : Scheme.{u}}
    (g : P ⟶ Spec (.of k))
    (hvan : ∀ m : ℕ, 1 ≤ m →
      Limits.IsZero (cohomologyOverField k g (SheafOfModules.unit P.ringCatSheaf) m)) :
    letI : Algebra k Γ(P, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k g (SheafOfModules.unit P.ringCatSheaf) n) : ℤ)) =
      (Module.finrank k Γ(P, ⊤) : ℤ) := by
  have := ModuleCat.subsingleton_of_isZero (hvan 1 le_rfl)
  have h1 : Module.finrank k (cohomologyOverField k g (SheafOfModules.unit P.ringCatSheaf) 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k g _
      (fun m hm => hvan m (by omega)),
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k g, h1]
  simp

/-- **On an affine scheme over a field the Euler characteristic of the structure sheaf is the
dimension of the ring of global functions**, higher cohomology of a quasi-coherent module on an
affine scheme vanishing. -/
theorem finsum_alternating_finrank_unit_eq_finrank_of_isAffine {P : Scheme.{u}} [IsAffine P]
    (g : P ⟶ Spec (.of k)) :
    letI : Algebra k Γ(P, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k g (SheafOfModules.unit P.ringCatSheaf) n) : ℤ)) =
      (Module.finrank k Γ(P, ⊤) : ℤ) := by
  have hvan (m : ℕ) (hm : 1 ≤ m) :
      Limits.IsZero (cohomologyOverField k g (SheafOfModules.unit P.ringCatSheaf) m) :=
    have : (SheafOfModules.unit P.ringCatSheaf).IsQuasicoherent := inferInstance
    isZero_cohomologyOverField_pos_of_isAffine k g _ m hm
  exact finsum_alternating_finrank_unit_eq_finrank_of_isZero g hvan

/-- **Cohomology over a subfield.** For a scheme `X` over a field `k'` and a subfield `k ⊆ k'`,
`dim_k Hⁿ(X, ℱ) = [k' : k] · dim_{k'} Hⁿ(X, ℱ)`: both are the same module over `Γ(X, 𝒪_X)`, with
scalars restricted along `k ⟶ k' ⟶ Γ(X, 𝒪_X)` and along `k' ⟶ Γ(X, 𝒪_X)`. -/
theorem finrank_cohomologyOverField_comp_SpecMap (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {Y : Scheme.{u}} (f' : Y ⟶ Spec (.of k')) (F : Y.Modules) (n : ℕ) :
    Module.finrank k
        (cohomologyOverField k (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) F n) =
      Module.finrank k k' * Module.finrank k' (cohomologyOverField k' f' F n) := by
  rw [cohomologyOverField_eq_restrictScalars_appTop, cohomologyOverField_eq_restrictScalars_appTop]
  rw [hom_ΓSpecIso_inv_comp_appTop_comp_SpecMap]
  let N := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop).hom).obj
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections Y).rightDerived n).obj F)
  change Module.finrank k ((ModuleCat.restrictScalars (algebraMap k k')).obj N) = _
  have : IsScalarTower k k' ((ModuleCat.restrictScalars (algebraMap k k')).obj N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (Module.finrank_mul_finrank k k' ((ModuleCat.restrictScalars (algebraMap k k')).obj N)).symm

/-- **`χ(ω_Y) = -χ(𝒪_Y)` over a subfield of the global functions.** Let `Y` be proper of dimension
at most one over a field `k'` with `H⁰(Y, 𝒪_Y) = k'` and invertible dualizing sheaf, and view `Y`
over a subfield `k ⊆ k'` with `[k' : k]` finite. Over `k'` one has `h⁰(ω) = g` and `h¹(ω) = 1`
(clause (5) of [Stacks, Tag 0BS2]) and `h⁰(𝒪) = 1`, `h¹(𝒪) = g`; the dualizing sheaf over `k` is
the dualizing sheaf over `k'` ([Stacks, Tag 0E32]); and every dimension over `k` is `[k' : k]`
times the one over `k'`. So `χ_k(ω) = [k' : k](g - 1) = -χ_k(𝒪)`. -/
theorem finsum_finrank_dualizingSheafOverField_eq_neg (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsProper f] (f' : Y ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = f) [IsProper f']
    [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)] (hdim : topologicalKrullDim Y ≤ 1)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f')] :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) n) : ℤ)) =
      -∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k f (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ) := by
  have e := Stacks.Duality.dualizingSheafOverFieldFactorIso f
    (CommRingCat.ofHom (algebraMap k k')) f' hf
  subst hf
  have hω (n : ℕ) : Module.finrank k
      (cohomologyOverField k (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
        (Stacks.Duality.dualizingSheafOverField
          (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))) n) =
      Module.finrank k k' * Module.finrank k'
        (cohomologyOverField k' f' (Stacks.Duality.dualizingSheafOverField f') n) := by
    rw [finrank_cohomologyOverField_eq_of_iso k _ e n]
    exact finrank_cohomologyOverField_comp_SpecMap k k' f' _ n
  have hO (n : ℕ) : Module.finrank k
      (cohomologyOverField k (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
        (SheafOfModules.unit Y.ringCatSheaf) n) =
      Module.finrank k k' * Module.finrank k'
        (cohomologyOverField k' f' (SheafOfModules.unit Y.ringCatSheaf) n) :=
    finrank_cohomologyOverField_comp_SpecMap k k' f' _ n
  have hsubω := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k
    (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (Stacks.Duality.dualizingSheafOverField (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (isZero_cohomologyOverField_two_le k _ hdim _)
  have hsubO := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k
    (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) (SheafOfModules.unit Y.ringCatSheaf)
    (isZero_cohomologyOverField_two_le k _ hdim _)
  rw [hsubω, hsubO, hω, hω, hO, hO,
    Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f' hdim,
    finrank_cohomologyOverField_one_dualizingSheafOverField_of_isInvertible k' f' hdim,
    finrank_cohomologyOverField_unit_zero_eq_one, finrank_cohomologyOverField_one_unit_eq_genus]
  push_cast
  ring

/-- **A field `k'` with `Y ⟶ Spec k'` inducing `k' ≅ Γ(Y, 𝒪_Y)` has the dimension of `Γ(Y, 𝒪_Y)`
over a subfield `k`**, when `Y ⟶ Spec k` factors through `Spec k'`. -/
theorem finrank_globalSections_eq_finrank_of_factor (k' : Type u) [Field k'] [Algebra k k']
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (f' : Y ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = g)
    [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)] :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Y, ⊤) = Module.finrank k k' := by
  let algY : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  let e : k' ≃ₐ[k] Γ(Y, ⊤) :=
    AlgEquiv.ofBijective
      { toRingHom := ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop).hom
        commutes' := fun r => by
          change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom r
          rw [← hf, hom_ΓSpecIso_inv_comp_appTop_comp_SpecMap]
          rfl }
      (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop))
  exact e.toLinearEquiv.finrank_eq.symm

/-- **`deg(ω_X|_C) = deg(C ∩ X') - 2 χ(C, 𝒪_C)`.** Let `C ⊆ X` be a closed subscheme of a
proper scheme over `k` of dimension at most one, let `k'` be a field with `C ⟶ Spec k'` over
`Spec k` inducing `k' ≅ Γ(C, 𝒪_C)` and with invertible dualizing sheaf over `k'`, and let
`0 ⟶ ω_C ⟶ ℒ ⟶ 𝒪_{C ∩ X'} ⟶ 0` be a short exact sequence on `C` with `ℒ` invertible. Then
`deg ℒ = χ(𝒪_{C ∩ X'}) - 2 χ(𝒪_C)`: additivity gives `deg ℒ = χ(ω_C) + χ(𝒪_{C ∩ X'}) - χ(𝒪_C)`
and duality `χ(ω_C) = -χ(𝒪_C)`. For `ℒ = ω_X|_C` and the sequence of [Stacks, Tag 0E34] this is
the formula of the proofs of [Stacks, Tag 0E63], [Stacks, Tag 0E64] and [Stacks, Tag 0E3J]. -/
theorem invertibleCurveDegree_eq_sub_two_mul_of_shortExact [IsProper (X ↘ Spec (.of k))]
    (C : X.IdealSheafData) (hCdim : topologicalKrullDim C.subscheme ≤ 1)
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f')]
    {S : ShortComplex C.subscheme.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 S.X₂]
    (e₁ : S.X₁ ≅ Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ (X ↘ Spec (.of k))))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
        (SheafOfModules.unit _)) :
    invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim S.X₂ =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k)))
        (SheafOfModules.unit (intersectionWithComplementaryCurveIdeal C).subscheme.ringCatSheaf)
          n) : ℤ)) -
      2 * ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (C.subschemeι ≫ (X ↘ Spec (.of k))) (SheafOfModules.unit C.subscheme.ringCatSheaf)
          n) : ℤ) := by
  let fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  have : (Stacks.Duality.dualizingSheafOverField f').IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k' f' _ 1
  have : S.X₁.IsCoherent := isCoherent_of_moduleIso
    ((Stacks.Duality.dualizingSheafOverFieldFactorIso fC
      (CommRingCat.ofHom (algebraMap k k')) f' hf).symm ≪≫ e₁.symm) inferInstance
  rw [invertibleCurveDegree_eq_of_shortExact fC hCdim hS _ e₃]
  have hω := finsum_finrank_dualizingSheafOverField_eq_neg k k' fC f' hf hCdim
  have h1 : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k fC S.X₁ n) : ℤ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k fC (Stacks.Duality.dualizingSheafOverField fC) n) : ℤ) :=
    finsum_congr fun n => by rw [finrank_cohomologyOverField_eq_of_iso k fC e₁ n]
  have hIC : Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ fC =
      (intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k)) := by
    simp only [fC, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  rw [h1, hω, hIC]
  ring

/-- **The degree of an extension of `𝒪_{C ∩ X'}` by `ω_C` on a rational tail is `-[k' : k]`**:
in `AlgebraicGeometry.invertibleCurveDegree_eq_sub_two_mul_of_shortExact`, `C ∩ X'` is the
attaching point `Spec k'` and `χ(𝒪_C) = [k' : k]`. For `ℒ = ω_X|_C` this is the computation of
[Stacks, Tag 0E63]. -/
theorem invertibleCurveDegree_eq_neg_of_isRationalTail [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) {C : X.IdealSheafData} (hC : IsRationalTail k X C)
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f')]
    {S : ShortComplex C.subscheme.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 S.X₂]
    (e₁ : S.X₁ ≅ Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ (X ↘ Spec (.of k))))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
        (SheafOfModules.unit _)) :
    invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k)))
        (le_of_eq (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C
          hC)) S.X₂ = -(Module.finrank k k' : ℤ) := by
  rw [invertibleCurveDegree_eq_sub_two_mul_of_shortExact C _ k' f' hf hS e₁ e₃]
  have hO := eulerCharacteristic_unit_of_isRationalTail hdim hC
  unfold eulerCharacteristic at hO
  have hΓ := finrank_globalSections_eq_finrank_of_factor k' _ f' hf
  have hI := finrank_globalSections_intersection_of_isRationalTail hC
  have := isIso_inclusion_comp_toSpecΓ_of_isRationalTail hC
  have : IsAffine (intersectionWithComplementaryCurveIdeal C).subscheme :=
    IsAffine.of_isIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ C.subscheme.toSpecΓ)
  rw [finsum_alternating_finrank_unit_eq_finrank_of_isAffine
    ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))), hI, hO, hΓ]
  ring

/-- **An irreducible component of a Noetherian space lying in a closed set `W` is not contained in
the closure of the complement of `W`**: some nonempty open subset of the component misses the
other components, hence misses `Wᶜ`, hence its closure. -/
theorem not_subset_closure_compl_of_mem_irreducibleComponents {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {Z W : Set T} (hZ : Z ∈ irreducibleComponents T)
    (hZW : Z ⊆ W) : ¬ Z ⊆ closure Wᶜ := by
  intro hsub
  obtain ⟨U, hUo, hUne, hUZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨y, hyU, hyW⟩ := mem_closure_iff.mp (hsub (hUZ hx)) U hUo hx
  exact hyW (hZW (hUZ hyU))

/-- A point lies in the intersection of a closed subscheme with the closure of its complement
iff it lies in both. -/
private theorem mem_support_intersectionWithComplementaryCurveIdeal {Y : Scheme.{u}}
    [IsNoetherian Y] (C : Y.IdealSheafData) (x : Y) :
    x ∈ (intersectionWithComplementaryCurveIdeal C).support ↔
      x ∈ C.support ∧ x ∈ closure ((C.support : Set Y)ᶜ) := by
  change x ∈ (C ⊔ complementaryCurveIdeal C).support ↔ _
  rw [Scheme.IdealSheafData.support_sup]
  refine and_congr_right fun _ => ?_
  change x ∈ ((Scheme.Opens.ι C.support.compl).ker.support : Set Y) ↔ _
  rw [Scheme.Hom.support_ker, Scheme.Opens.range_ι]
  exact Iff.rfl

/-- **The intersection of a closed subscheme with the closure of its complement is
zero-dimensional**, on a Noetherian scheme of dimension at most one: it contains no irreducible
component, so it is a finite set of closed points. -/
theorem topologicalKrullDim_intersectionWithComplementaryCurve_le_zero {Y : Scheme.{u}}
    [IsNoetherian Y] (hdim : topologicalKrullDim Y ≤ 1) (C : Y.IdealSheafData) :
    topologicalKrullDim (intersectionWithComplementaryCurveIdeal C).subscheme ≤ 0 := by
  let I := intersectionWithComplementaryCurveIdeal C
  let T : Set Y := I.support
  have hTC : T ⊆ C.support := fun x hx =>
    ((mem_support_intersectionWithComplementaryCurveIdeal C x).1 hx).1
  have hTcl : T ⊆ closure ((C.support : Set Y)ᶜ) := fun x hx =>
    ((mem_support_intersectionWithComplementaryCurveIdeal C x).1 hx).2
  have hTc : ∀ Z ∈ irreducibleComponents Y, ¬ Z ⊆ T := fun Z hZ hZT =>
    not_subset_closure_compl_of_mem_irreducibleComponents hZ (hZT.trans hTC) (hZT.trans hTcl)
  have hfin : T.Finite :=
    Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim I.support.isClosed
      hTc
  have hcl : ∀ x ∈ T, IsClosed ({x} : Set Y) := fun x hx =>
    Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset hdim
      I.support.isClosed hTc hx
  have : Finite T := hfin.to_subtype
  have ht1 : ∀ x : T, IsClosed ({x} : Set T) := by
    intro x
    have h := (hcl x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ T)))
    have he : (Subtype.val ⁻¹' {x.1} : Set T) = {x} := by
      ext y
      exact ⟨Subtype.ext, fun hy => congrArg Subtype.val hy⟩
    rwa [he] at h
  have : T1Space T := ⟨ht1⟩
  have hrange : (Set.range I.subschemeι : Set Y) = T := I.range_subschemeι
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)).isHomeomorph]
  exact topologicalKrullDim_zero_of_discreteTopology T

/-- **On a zero-dimensional scheme proper over a field the Euler characteristic of the structure
sheaf is the dimension of the ring of global functions**, higher cohomology vanishing by
[Stacks, Tag 02UZ]. -/
theorem finsum_alternating_finrank_unit_eq_finrank_of_topologicalKrullDim_le_zero
    {P : Scheme.{u}} (g : P ⟶ Spec (.of k)) [IsProper g] (hP : topologicalKrullDim P ≤ 0) :
    letI : Algebra k Γ(P, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k g (SheafOfModules.unit P.ringCatSheaf) n) : ℤ)) =
      (Module.finrank k Γ(P, ⊤) : ℤ) := by
  have hvan (m : ℕ) (hm : 1 ≤ m) :
      Limits.IsZero (cohomologyOverField k g (SheafOfModules.unit P.ringCatSheaf) m) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_le k g _ (d := 0)
      (by exact_mod_cast hP) (by omega)
  exact finsum_alternating_finrank_unit_eq_finrank_of_isZero g hvan

/-- **The degree of an extension of `𝒪_{C ∩ X'}` by `ω_C` on a rational bridge is zero.** As for
`AlgebraicGeometry.invertibleCurveDegree_eq_neg_of_isRationalTail`, with `χ(𝒪_C) = [k' : k]`
(genus zero) and `χ(𝒪_{C ∩ X'}) = 2 [k' : k]`, the intersection being zero-dimensional. For
`ℒ = ω_X|_C` and the sequence of [Stacks, Tag 0E34] this is the computation of
[Stacks, Tag 0E64]. -/
theorem invertibleCurveDegree_eq_zero_of_isRationalBridge [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (hCdim : topologicalKrullDim C.subscheme ≤ 1)
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f')]
    {S : ShortComplex C.subscheme.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 S.X₂]
    (e₁ : S.X₁ ≅ Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ (X ↘ Spec (.of k))))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
        (SheafOfModules.unit _)) :
    invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim S.X₂ = 0 := by
  let fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  rw [invertibleCurveDegree_eq_sub_two_mul_of_shortExact C hCdim k' f' hf hS e₁ e₃]
  -- the genus of `C` over `k` vanishes
  have : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) := (isField_of_universallyClosed k fC).toField
  have := Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fC
  have hg : genus fC = 0 :=
    genus_eq_zero_of_genus_eq_zero C.subscheme.toSpecΓ fC hC.genus_eq_zero
  have hO := eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus k fC hCdim
  unfold eulerCharacteristic at hO
  have hΓ := finrank_globalSections_eq_finrank_of_factor k' fC f' hf
  have hI := finrank_globalSections_intersection_of_isRationalBridge hC
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hPdim := topologicalKrullDim_intersectionWithComplementaryCurve_le_zero (le_of_eq hdim) C
  have hP : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k)))
      (SheafOfModules.unit (intersectionWithComplementaryCurveIdeal C).subscheme.ringCatSheaf)
        n) : ℤ)) = 2 * (Module.finrank k k' : ℤ) := by
    rw [finsum_alternating_finrank_unit_eq_finrank_of_topologicalKrullDim_le_zero _ hPdim, hI, hΓ]
    push_cast
    ring
  rw [hP, hO, hg, hΓ]
  push_cast
  ring

/-- **A nonempty proper closed subscheme of a connected scheme meets the closure of its
complement**: the support and the closure of the complement are closed, nonempty and cover the
space. -/
theorem nonempty_intersectionWithComplementaryCurve_of_connectedSpace {Y : Scheme.{u}}
    [IsNoetherian Y] [ConnectedSpace Y] (C : Y.IdealSheafData) (hne : (C.support : Set Y).Nonempty)
    (hC : (C.support : Set Y) ≠ Set.univ) :
    Nonempty (intersectionWithComplementaryCurveIdeal C).subscheme := by
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).mp hC
  have hcover : (C.support : Set Y) ∪ closure ((C.support : Set Y)ᶜ) = Set.univ :=
    Set.eq_univ_of_forall fun z => (em _).imp id fun hz => subset_closure hz
  obtain ⟨z, -, hzcl⟩ := (isPreconnected_closed_iff.mp isPreconnected_univ) _ _
    C.support.isClosed isClosed_closure (by rw [hcover])
    ⟨_, Set.mem_univ _, hne.some_mem⟩
    ⟨y, Set.mem_univ _, subset_closure (show y ∈ (C.support : Set Y)ᶜ from hy)⟩
  have hz : z ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set Y) :=
    (mem_support_intersectionWithComplementaryCurveIdeal C z).2 hzcl
  rw [← Scheme.IdealSheafData.range_subschemeι] at hz
  obtain ⟨w, -⟩ := hz
  exact ⟨w⟩

end AlgebraicGeometry

end
