module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ProjectiveLineEulerBound
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.SectionVanishingCriterion
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvolutionDatum
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyFactorialOpenCover
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCover
public import StacksFrontier.AlgebraicGeometry.Divisors.RationalFunctionZeroDivisor
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaEulerRelation
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaInvolution.ProjectiveInvolution
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaInvolution.ThreefoldInvolution
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.ModelFactorial
public import StacksFrontier.AlgebraicGeometry.Groupoids.FreeInvolutionQuotient
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FiniteSetAffineOpen

/-!
# A projective descent datum along an étale covering which is not effective

Let `k` be a field with `2 ≠ 0`, let `ℙ³_k` carry the involution
`σ : [x : y : z : w] ↦ [y : x : w : z]`, and let `Y ⊆ ℙ³_k` be the open subscheme on which `σ`
acts freely. The quotient `π : Y ⟶ S = Y / σ` is a finite étale double cover. The point
`P = [1 : 0 : 0 : 0]` lies in `Y` and `σ P = Q = [0 : 1 : 0 : 0]`, so `X = Y - {Q}` still maps
onto `S`, and `X ⟶ S` is an étale covering.

Hironaka's threefold `f : V ⟶ ℙ³_k` is, over `ℙ³_k - {Q}`, a projective tower of two blow-ups,
and `σ` lifts to an involution `τ` of `V` over `σ`. The base change `W = X ×_{ℙ³} V ⟶ X` is
projective, and `τ` restricted to the part of `W` over `X ∩ σ⁻¹ X` is an involution `ρ` covering
`σ`. Together with the decomposition `Y ×_S Y = Δ ⨿ Γ_σ`, the involution `ρ` is a descent datum
for `W` relative to `X ⟶ S`.

The datum is not effective. If it were, `W` would be the base change of some `U ⟶ S` along
`X ⟶ S`, and the projection `Φ : W ⟶ U` would be étale and `ρ`-invariant. Let `A ≅ ℙ¹_k` be the
exceptional curve of the model tower over the origin, sitting in `V` over `P` through the chart
`t_P` and over `Q` through `t_Q = τ ∘ t_P`. A function `a` on an affine open of `U` vanishing at
the image of a closed point of `A` but not at the image of its generic point (these differ, as
`Φ` has discrete fibres) pulls back along `Φ` to two functions on `V`, one near `t_P(A)` and one
near `t_Q(A)`, which agree where both are defined by `ρ`-invariance. On the open
`V' = t_P(T) ∪ t_Q(T)`, which is integral and locally factorial, they define one rational
function `h`, and its divisor of zeros `𝒟` is an effective Cartier divisor meeting both copies
of `A` properly. So `𝒪(𝒟)` restricts to ample invertible modules on both copies of `A`, each of
Euler characteristic at least two, against the relation `χ(ℋ|A_P) + χ(ℋ|A_Q) = 2` that holds
for every invertible module `ℋ` on `V'`.

## Main definitions

* `Stacks.Examples.HironakaInvolution.descentProj`: the projective morphism `W ⟶ X`.
* `Stacks.Examples.HironakaInvolution.descentSwap`: the involution `ρ` of the part of `W` over
  `X ∩ σ⁻¹ X`.
* `Stacks.Examples.HironakaInvolution.descentDatum`: the descent datum of `ρ` relative to
  `X ⟶ S`.

## Main results

* `Stacks.Examples.HironakaInvolution.singleton_mem_etalePrecoverage`: `X ⟶ S` is an étale
  covering.
* `Stacks.Examples.HironakaInvolution.isProjective_descentDatum`: the datum is projective.
* `Stacks.Examples.HironakaInvolution.not_isEffective_descentDatum`: the datum is not
  effective.
* `exists_etale_descentData_projective_not_isEffective`, in the namespace
  `Stacks.Examples.NonEffectiveProjectiveDescent`: there are an étale covering `X ⟶ S` and a
  descent datum relative to it, projective over `X`, which is not effective
  ([Stacks, Tag 08KF]).

## Implementation notes

The witness is built over `k = ULift ℚ`, so that it lives in every universe. The rational
function `h` is the common germ, at the generic point of `V'`, of the two pulled back functions;
that the germs agree is checked on the nonempty open of `V'` lying over the part of `W` over
`X ∩ σ⁻¹ X` where the first function is defined, on which the second is the first composed with
`ρ`.

## References

* [Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic (eulerSum)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.Examples.HironakaConicIdealSheaf Stacks.Examples.HironakaConicChart
  Stacks.Examples.HironakaThreefold Stacks.Examples.HironakaNotProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open Deformation.Examples (apply_eq_of_comp_eq)

namespace Stacks.Examples.HironakaInvolution

/-! ### Generalities on points and sections -/

section General

/-- The inclusion of an open subscheme lands in the open. -/
theorem ι_apply_mem {X : Scheme.{u}} (U : X.Opens) (x : U.toScheme) : U.ι x ∈ U := by
  have := Set.mem_range_self (f := U.ι) x
  rw [Scheme.Opens.range_ι] at this
  exact this

/-- In the square `Y ⨿ Y ⇉ Y ⟶ S` of an involution `σ`, the involution lies over `S`. -/
theorem comp_eq_of_isPullback_coprodDesc {Y S : Scheme.{u}} {π : Y ⟶ S} {σ : Y ⟶ Y}
    (hπ : IsPullback (coprod.desc (𝟙 Y) (𝟙 Y)) (coprod.desc (𝟙 Y) σ) π π) : σ ≫ π = π := by
  have h := coprod.inr ≫= hπ.w
  simp only [coprod.inr_desc_assoc, Category.id_comp] at h
  exact h.symm

/-- A point of the image of an open under an open immersion comes from a point of the open. -/
theorem exists_of_mem_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U : X.Opens}
    {v : Y} (hv : v ∈ f ''ᵁ U) : ∃ x ∈ U, f x = v := by
  have hv' : v ∈ (f ''ᵁ U : Set Y) := hv
  rw [Scheme.Hom.coe_image] at hv'
  obtain ⟨x, hx, rfl⟩ := hv'
  exact ⟨x, hx, rfl⟩

/-- In a cartesian square of schemes, a point of the bottom left corner lying over a point of the
top right corner is in the image of the left projection. -/
theorem mem_range_snd_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) {x : X} {y : Y} (hxy : f x = g y) :
    y ∈ Set.range snd := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz]⟩

/-- Two equal morphisms have the same `appLE`. -/
theorem appLE_eq_of_hom_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- **Fibres of a locally quasi-finite morphism are discrete**, so a specialization inside a
fibre is an equality. -/
theorem eq_of_specializes_of_apply_eq {X Y : Scheme.{u}} (Φ : X ⟶ Y) [LocallyQuasiFinite Φ]
    {a b : X} (hab : a ⤳ b) (h : Φ a = Φ b) : a = b := by
  have : DiscreteTopology (Φ ⁻¹' {Φ b}) := (Φ.isDiscrete_preimage_singleton (Φ b)).to_subtype
  have ha : a ∈ Φ ⁻¹' {Φ b} := h
  have hb : b ∈ Φ ⁻¹' {Φ b} := rfl
  have hs : (⟨a, ha⟩ : Φ ⁻¹' {Φ b}) ⤳ ⟨b, hb⟩ := (subtype_specializes_iff _ _).mpr hab
  exact congrArg Subtype.val hs.eq

/-- **Separating a point from a specialization of it by a function.** If `a ⤳ b` are distinct
points of a scheme, there are an affine open `W` containing both and a section of `W`
which does not vanish at `a` and vanishes at `b`. -/
theorem exists_affineOpen_separating {U : Scheme.{u}} {a b : U} (hab : a ⤳ b) (hne : a ≠ b) :
    ∃ (Wa : U.Opens) (fa : Γ(U, Wa)), IsAffineOpen Wa ∧ b ∈ Wa ∧ a ∈ Wa ∧
      a ∈ U.basicOpen fa ∧ b ∉ U.basicOpen fa := by
  obtain ⟨_, ⟨Wa, hWa, rfl⟩, hbWa, -⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ b) isOpen_univ
  have haWa : a ∈ Wa := hab.mem_open Wa.isOpen hbWa
  have hnot : ¬ b ⤳ a := fun hba => hne (hab.antisymm hba).eq
  rw [specializes_iff_forall_open] at hnot
  push Not at hnot
  obtain ⟨O, hO, haO, hbO⟩ := hnot
  obtain ⟨fa, hfaO, hafa⟩ :=
    (hWa : IsAffineOpen Wa).exists_basicOpen_le (V := ⟨O, hO⟩) ⟨a, haO⟩ haWa
  exact ⟨Wa, fa, hWa, hbWa, haWa, hafa, fun h => hbO (hfaO h)⟩

/-- An irreducible scheme of dimension one has a point other than its generic point. -/
theorem exists_ne_genericPoint (X : Scheme.{u}) [IrreducibleSpace X]
    (hX : topologicalKrullDim X = 1) : ∃ x : X, x ≠ genericPoint X := by
  by_contra! h
  have : Subsingleton X := ⟨fun a b => (h a).trans (h b).symm⟩
  have : Subsingleton (TopologicalSpace.IrreducibleCloseds X) := ⟨fun s t => by
    obtain ⟨a, ha⟩ := s.isIrreducible.nonempty
    obtain ⟨b, hb⟩ := t.isIrreducible.nonempty
    refine SetLike.ext fun y => ⟨fun _ => ?_, fun _ => ?_⟩
    · rwa [Subsingleton.elim y b]
    · rwa [Subsingleton.elim y a]⟩
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  rw [topologicalKrullDim, Order.krullDim_eq_zero] at hX
  exact (by norm_num : (0 : WithBot ℕ∞) ≠ 1) hX

variable {V W U : Scheme.{u}}

/-- The section `Φ^* a`, moved from `W` to `V` along an open immersion `ε : W ⟶ V`; it is
defined on the image of `Φ⁻¹ Wa`. -/
def sectionAlong (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U) {Wa : U.Opens} (fa : Γ(U, Wa)) :
    Γ(V, ε ''ᵁ (Φ ⁻¹ᵁ Wa)) :=
  (ε.appIso (Φ ⁻¹ᵁ Wa)).inv (Φ.app Wa fa)

/-- The section `sectionAlong ε Φ fa` vanishes nowhere exactly on the image of the preimage of
the nonvanishing locus of `fa`. -/
theorem basicOpen_sectionAlong (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U) {Wa : U.Opens}
    (fa : Γ(U, Wa)) : V.basicOpen (sectionAlong ε Φ fa) = ε ''ᵁ (Φ ⁻¹ᵁ U.basicOpen fa) := by
  rw [sectionAlong, ← Scheme.image_basicOpen, ← Scheme.preimage_basicOpen]

/-- The open of an open subscheme `V'` of `V` on which `sectionOn V' ε Φ fa` is defined. -/
abbrev opensAlong (V' : V.Opens) (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U) (Wa : U.Opens) :
    V'.toScheme.Opens :=
  V'.ι ⁻¹ᵁ (ε ''ᵁ (Φ ⁻¹ᵁ Wa))

/-- The section `Φ^* a`, moved to an open subscheme `V'` of `V` along `ε : W ⟶ V`. -/
def sectionOn (V' : V.Opens) (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U) {Wa : U.Opens}
    (fa : Γ(U, Wa)) : Γ(V'.toScheme, opensAlong V' ε Φ Wa) :=
  V'.ι.app _ (sectionAlong ε Φ fa)

/-- A point of `V'` lying at `ε w` is in `opensAlong V' ε Φ Wa` iff `Φ w ∈ Wa`. -/
theorem mem_opensAlong_iff (V' : V.Opens) (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U)
    (Wa : U.Opens) {z : V'.toScheme} {w : W} (h : V'.ι z = ε w) :
    z ∈ opensAlong V' ε Φ Wa ↔ Φ w ∈ Wa := by
  change V'.ι z ∈ ε ''ᵁ (Φ ⁻¹ᵁ Wa) ↔ _
  rw [h, Scheme.Hom.apply_mem_image_iff, Scheme.Hom.mem_preimage]

/-- A point of `V'` lying at `ε w` is in the nonvanishing locus of `sectionOn V' ε Φ fa` iff
`Φ w` is in the nonvanishing locus of `fa`. -/
theorem mem_basicOpen_sectionOn_iff (V' : V.Opens) (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U)
    {Wa : U.Opens} (fa : Γ(U, Wa)) {z : V'.toScheme} {w : W} (h : V'.ι z = ε w) :
    z ∈ V'.toScheme.basicOpen (sectionOn V' ε Φ fa) ↔ Φ w ∈ U.basicOpen fa := by
  rw [sectionOn, ← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage, h, basicOpen_sectionAlong,
    Scheme.Hom.apply_mem_image_iff, Scheme.Hom.mem_preimage]

/-- A morphism `j` into `V'` lying over `a ≫ ε` with `a` landing in `Φ⁻¹ Wa` lands in
`opensAlong V' ε Φ Wa`. -/
theorem top_le_preimage_opensAlong (V' : V.Opens) (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U)
    (Wa : U.Opens) {T : Scheme.{u}} (j : T ⟶ V'.toScheme) (a : T ⟶ W) (hj : j ≫ V'.ι = a ≫ ε)
    (h' : ⊤ ≤ (a ≫ Φ) ⁻¹ᵁ Wa) : ⊤ ≤ j ⁻¹ᵁ opensAlong V' ε Φ Wa := by
  intro t _
  have : t ∈ (a ≫ Φ) ⁻¹ᵁ Wa := h' (show t ∈ (⊤ : T.Opens) from trivial)
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply] at this
  change t ∈ j ⁻¹ᵁ opensAlong V' ε Φ Wa
  rw [Scheme.Hom.mem_preimage, mem_opensAlong_iff V' ε Φ Wa (apply_eq_of_comp_eq hj t)]
  exact this

/-- The pullback of `sectionOn V' ε Φ fa` along `j : T ⟶ V'` lying over `a ≫ ε`, as ring maps:
it is the pullback of `fa` along `a ≫ Φ`. -/
theorem appLE_sectionOn_hom (V' : V.Opens) (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U)
    {Wa : U.Opens} {T : Scheme.{u}} (j : T ⟶ V'.toScheme) (a : T ⟶ W) (hj : j ≫ V'.ι = a ≫ ε)
    (h' : ⊤ ≤ (a ≫ Φ) ⁻¹ᵁ Wa) (h : ⊤ ≤ j ⁻¹ᵁ opensAlong V' ε Φ Wa) :
    Φ.app Wa ≫ (ε.appIso (Φ ⁻¹ᵁ Wa)).inv ≫ V'.ι.app (ε ''ᵁ (Φ ⁻¹ᵁ Wa)) ≫
        j.appLE (V'.ι ⁻¹ᵁ (ε ''ᵁ (Φ ⁻¹ᵁ Wa))) ⊤ h =
      (a ≫ Φ).appLE Wa ⊤ h' := by
  have hh₃ : ⊤ ≤ a ⁻¹ᵁ (ε ⁻¹ᵁ (ε ''ᵁ (Φ ⁻¹ᵁ Wa))) := by
    rw [Scheme.Hom.preimage_image_eq]
    exact h'
  have e₁ : V'.ι.app (ε ''ᵁ (Φ ⁻¹ᵁ Wa)) ≫ j.appLE (V'.ι ⁻¹ᵁ (ε ''ᵁ (Φ ⁻¹ᵁ Wa))) ⊤ h =
      ε.app (ε ''ᵁ (Φ ⁻¹ᵁ Wa)) ≫ a.appLE (ε ⁻¹ᵁ (ε ''ᵁ (Φ ⁻¹ᵁ Wa))) ⊤ hh₃ := by
    rw [Scheme.Hom.app_eq_appLE V'.ι, Scheme.Hom.app_eq_appLE ε, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_hom_eq hj _ _ _ _
  rw [e₁, Scheme.Hom.appIso_inv_app_assoc, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE Φ,
    Scheme.Hom.appLE_comp_appLE]

/-- **The pullback of `sectionOn V' ε Φ fa` along `j : T ⟶ V'` lying over `a ≫ ε`** is the
pullback of `fa` along `a ≫ Φ`. -/
theorem appLE_sectionOn (V' : V.Opens) (ε : W ⟶ V) [IsOpenImmersion ε] (Φ : W ⟶ U)
    {Wa : U.Opens} (fa : Γ(U, Wa)) {T : Scheme.{u}} (j : T ⟶ V'.toScheme) (a : T ⟶ W)
    (hj : j ≫ V'.ι = a ≫ ε) (h' : ⊤ ≤ (a ≫ Φ) ⁻¹ᵁ Wa) (h : ⊤ ≤ j ⁻¹ᵁ opensAlong V' ε Φ Wa) :
    j.appLE _ ⊤ h (sectionOn V' ε Φ fa) = (a ≫ Φ).appLE Wa ⊤ h' fa := by
  have := congrArg (fun φ : Γ(U, Wa) ⟶ Γ(T, ⊤) => φ fa) (appLE_sectionOn_hom V' ε Φ j a hj h' h)
  simpa only [CommRingCat.comp_apply, sectionOn, sectionAlong] using this

/-- **Equal germs from a common pullback.** On an integral scheme `Z`, two sections over
nonempty opens have the same image in the function field as soon as they have the same
pullback along an open immersion from a nonempty scheme landing in both opens. -/
theorem germToFunctionField_eq_of_appLE_eq {Z T : Scheme.{u}} [IsIntegral Z] {O₁ O₂ : Z.Opens}
    [Nonempty O₁] [Nonempty O₂] (r₁ : Γ(Z, O₁)) (r₂ : Γ(Z, O₂)) (j : T ⟶ Z) [IsOpenImmersion j]
    (t : T) (h₁ : ⊤ ≤ j ⁻¹ᵁ O₁) (h₂ : ⊤ ≤ j ⁻¹ᵁ O₂)
    (h : j.appLE O₁ ⊤ h₁ r₁ = j.appLE O₂ ⊤ h₂ r₂) :
    Z.germToFunctionField O₁ r₁ = Z.germToFunctionField O₂ r₂ := by
  have ht₁ : j t ∈ O₁ := h₁ (show t ∈ (⊤ : T.Opens) from trivial)
  have ht₂ : j t ∈ O₂ := h₂ (show t ∈ (⊤ : T.Opens) from trivial)
  have hgerm : Z.presheaf.germ O₁ (j t) ht₁ r₁ = Z.presheaf.germ O₂ (j t) ht₂ r₂ := by
    apply (ConcreteCategory.bijective_of_isIso (j.stalkMap t)).1
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply,
      ← T.presheaf.germ_res_apply (homOfLE h₁) t trivial,
      ← T.presheaf.germ_res_apply (homOfLE h₂) t trivial]
    simp only [Scheme.Hom.appLE, CommRingCat.comp_apply] at h
    rw [h]
  have hspec := genericPoint_specializes (j t)
  change Z.presheaf.germ O₁ (genericPoint Z) _ r₁ = Z.presheaf.germ O₂ (genericPoint Z) _ r₂
  rw [← TopCat.Presheaf.germ_stalkSpecializes_apply Z.presheaf ht₁ hspec,
    ← TopCat.Presheaf.germ_stalkSpecializes_apply Z.presheaf ht₂ hspec, hgerm]

end General

/-! ### The étale covering `X ⟶ S` and the projective scheme `W ⟶ X` -/

variable (k : Type u) [Field k]

/-- Membership in `Y - {Q}`. -/
theorem mem_opensAwayQ_iff (x : projectiveThreeSpace k) : x ∈ opensAwayQ k ↔ x ≠ pointQ k := by
  change x ∈ ({pointQ k}ᶜ : Set _) ↔ _
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]

/-- **The open `X`**: the part of the free locus `Y` away from `Q`. -/
abbrev awayQLocus : (freeLocus k).toScheme.Opens :=
  (freeLocus k).ι ⁻¹ᵁ opensAwayQ k

/-- **The scheme `W = X ×_{ℙ³} V`**, as the base change of the tower over `ℙ³ - {Q}`. -/
abbrev descentSpace : Scheme.{u} :=
  pullback ((freeLocus k).ι ∣_ opensAwayQ k) (towerAwayQ k)

/-- **The projection `W ⟶ X`.** -/
def descentProj : descentSpace k ⟶ (awayQLocus k).toScheme :=
  pullback.fst ((freeLocus k).ι ∣_ opensAwayQ k) (towerAwayQ k)

/-- **The open immersion `W ⟶ V`.** -/
def descentEmb : descentSpace k ⟶ hironakaThreefold k :=
  pullback.snd ((freeLocus k).ι ∣_ opensAwayQ k) (towerAwayQ k) ≫ ιAwayQ k

/-- **`W` is `X ×_{ℙ³} V`**, as a cartesian square. -/
theorem isPullback_descent : IsPullback (descentProj k) (descentEmb k)
    ((awayQLocus k).ι ≫ (freeLocus k).ι) (hironakaMorphism k) := by
  have h := (IsPullback.of_hasPullback ((freeLocus k).ι ∣_ opensAwayQ k)
    (towerAwayQ k)).paste_vert (isPullback_awayQ k)
  rw [morphismRestrict_ι] at h
  exact h

/-- The square of `W`. -/
@[reassoc]
theorem descent_w : descentProj k ≫ (awayQLocus k).ι ≫ (freeLocus k).ι =
    descentEmb k ≫ hironakaMorphism k :=
  (isPullback_descent k).w

/-- The square of `W`, on points. -/
theorem descent_w_apply (w : descentSpace k) :
    (freeLocus k).ι ((awayQLocus k).ι (descentProj k w)) =
      hironakaMorphism k (descentEmb k w) := by
  rw [← apply_eq_of_comp_eq (descent_w k) w, Scheme.Hom.comp_apply]

/-- **`W ⟶ X` is projective**, as a base change of the tower over `ℙ³ - {Q}`. -/
theorem isProjective_descentProj : IsProjective (descentProj k) :=
  IsProjective.of_isPullback
    (IsPullback.of_hasPullback ((freeLocus k).ι ∣_ opensAwayQ k) (towerAwayQ k))
    (isProjective_towerAwayQ k)

/-- `W ⟶ V` is an open immersion. -/
instance isOpenImmersion_descentEmb : IsOpenImmersion (descentEmb k) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_descent k) inferInstance

/-- **`X ⟶ S` is surjective**: a point of `Y` over `Q` is exchanged by the involution with a
point over `P`, which lies in `X` and has the same image in `S`. -/
theorem surjective_awayQLocus_ι_comp {S : Scheme.{u}} (π : (freeLocus k).toScheme ⟶ S)
    [Surjective π] (hσπ : freeInvolution k ≫ π = π) :
    Function.Surjective ((awayQLocus k).ι ≫ π) := by
  intro s
  obtain ⟨y, rfl⟩ := π.surjective s
  by_cases hy : (freeLocus k).ι y = pointQ k
  · have hy' : freeInvolution k y ∈ awayQLocus k := by
      change (freeLocus k).ι (freeInvolution k y) ∈ opensAwayQ k
      rw [mem_opensAwayQ_iff, apply_eq_of_comp_eq (freeInvolution_ι k), hy,
        involution_pointQ]
      exact pointP_ne_pointQ k
    obtain ⟨x, hx⟩ : freeInvolution k y ∈ Set.range (awayQLocus k).ι := by
      rw [Scheme.Opens.range_ι]
      exact hy'
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, hσπ]
  · have hy' : y ∈ awayQLocus k := (mem_opensAwayQ_iff k _).mpr hy
    obtain ⟨x, hx⟩ : y ∈ Set.range (awayQLocus k).ι := by
      rw [Scheme.Opens.range_ι]
      exact hy'
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, hx]

/-- **`X ⟶ S` is an étale covering.** -/
theorem singleton_mem_etalePrecoverage {S : Scheme.{u}} (π : (freeLocus k).toScheme ⟶ S)
    [Etale π] [Surjective π]
    (hπ : IsPullback (coprod.desc (𝟙 _) (𝟙 _)) (coprod.desc (𝟙 _) (freeInvolution k)) π π) :
    Presieve.singleton ((awayQLocus k).ι ≫ π) ∈ Scheme.etalePrecoverage S := by
  have hσπ : freeInvolution k ≫ π = π := comp_eq_of_isPullback_coprodDesc hπ
  exact (Scheme.singleton_mem_precoverage_iff (@Etale : MorphismProperty Scheme.{u})
    ((awayQLocus k).ι ≫ π)).mpr ⟨surjective_awayQLocus_ι_comp k π hσπ, inferInstance⟩

/-! ### The involution `ρ` -/

/-- **The lift `τ` of the involution of `ℙ³` to Hironaka's threefold.** -/
abbrev threefoldSwap : hironakaThreefold k ⟶ hironakaThreefold k :=
  threefoldInvolution k (involution k) (involution_comp_involution k)
    (comap_idealSheafC_involution k) (comap_idealSheafD_involution k)
    (involution_preimage_opensAwayQ k) (involution_preimage_opensAwayP k)

/-- `τ` lies over the involution of `ℙ³`. -/
@[reassoc]
theorem threefoldSwap_hironakaMorphism :
    threefoldSwap k ≫ hironakaMorphism k = hironakaMorphism k ≫ involution k :=
  threefoldInvolution_hironakaMorphism k (involution k) (involution_comp_involution k)
    (comap_idealSheafC_involution k) (comap_idealSheafD_involution k)
    (involution_preimage_opensAwayQ k) (involution_preimage_opensAwayP k)

/-- `τ` is an involution. -/
@[reassoc]
theorem threefoldSwap_comp_self : threefoldSwap k ≫ threefoldSwap k = 𝟙 _ :=
  threefoldInvolution_comp_self k (involution k) (involution_comp_involution k)
    (comap_idealSheafC_involution k) (comap_idealSheafD_involution k)
    (involution_preimage_opensAwayQ k) (involution_preimage_opensAwayP k)

/-- **The part `W_O` of `W` over `X ∩ σ⁻¹ X`.** -/
abbrev descentOverlap : (descentSpace k).Opens :=
  involutionOverlap (freeInvolution k) (awayQLocus k) (descentProj k)

/-- The point of `X` obtained by applying `σ` to the image of a point of `W_O`. -/
def overlapShift : (descentOverlap k).toScheme ⟶ (awayQLocus k).toScheme :=
  (descentProj k ≫ (awayQLocus k).ι ≫ freeInvolution k) ∣_ awayQLocus k

/-- `overlapShift` is `σ` applied to the image of a point of `W_O`. -/
@[reassoc]
theorem overlapShift_ι : overlapShift k ≫ (awayQLocus k).ι =
    (descentOverlap k).ι ≫ descentProj k ≫ (awayQLocus k).ι ≫ freeInvolution k :=
  morphismRestrict_ι _ _

/-- The involution `ρ`, as a morphism `W_O ⟶ W`: a point `w` goes to the point of `W` over
`σ (p w)` and over `τ w`. -/
def overlapSwapAux : (descentOverlap k).toScheme ⟶ descentSpace k :=
  (isPullback_descent k).lift (overlapShift k)
    ((descentOverlap k).ι ≫ descentEmb k ≫ threefoldSwap k) (by
      rw [overlapShift_ι_assoc, freeInvolution_ι, descent_w_assoc]
      simp only [Category.assoc, threefoldSwap_hironakaMorphism])

/-- `overlapSwapAux` lies over `overlapShift`. -/
@[reassoc]
theorem overlapSwapAux_fst : overlapSwapAux k ≫ descentProj k = overlapShift k :=
  (isPullback_descent k).lift_fst _ _ _

/-- `overlapSwapAux` lies over `τ`. -/
@[reassoc]
theorem overlapSwapAux_snd : overlapSwapAux k ≫ descentEmb k =
    (descentOverlap k).ι ≫ descentEmb k ≫ threefoldSwap k :=
  (isPullback_descent k).lift_snd _ _ _

/-- `overlapSwapAux` lands in `W_O`. -/
theorem overlapSwapAux_lift_cond :
    overlapSwapAux k ≫ descentProj k ≫ (awayQLocus k).ι ≫ freeInvolution k =
      ((descentOverlap k).ι ≫ descentProj k) ≫ (awayQLocus k).ι := by
  rw [overlapSwapAux_fst_assoc, overlapShift_ι_assoc, freeInvolution_comp_freeInvolution,
    Category.comp_id, Category.assoc]

/-- **The involution `ρ` of `W_O`.** -/
def descentSwap : (descentOverlap k).toScheme ⟶ (descentOverlap k).toScheme :=
  liftInvolutionOverlap (σ := freeInvolution k) (X := awayQLocus k) (p := descentProj k)
    (overlapSwapAux k) ((descentOverlap k).ι ≫ descentProj k) (overlapSwapAux_lift_cond k)

/-- `ρ` followed by the inclusion of `W_O` is `overlapSwapAux`. -/
@[reassoc]
theorem descentSwap_ι : descentSwap k ≫ (descentOverlap k).ι = overlapSwapAux k :=
  liftInvolutionOverlap_ι _ _ _

/-- **`ρ` covers `σ`.** -/
@[reassoc]
theorem descentSwap_proj :
    descentSwap k ≫ (descentOverlap k).ι ≫ descentProj k ≫ (awayQLocus k).ι =
      (descentOverlap k).ι ≫ descentProj k ≫ (awayQLocus k).ι ≫ freeInvolution k := by
  rw [descentSwap_ι_assoc, overlapSwapAux_fst_assoc, overlapShift_ι]

/-- **`ρ` is `τ` on `W_O`.** -/
@[reassoc]
theorem descentSwap_emb :
    descentSwap k ≫ (descentOverlap k).ι ≫ descentEmb k =
      (descentOverlap k).ι ≫ descentEmb k ≫ threefoldSwap k := by
  rw [descentSwap_ι_assoc, overlapSwapAux_snd]

/-- **`ρ` is an involution.** -/
theorem descentSwap_comp_self : descentSwap k ≫ descentSwap k = 𝟙 _ := by
  rw [← cancel_mono (descentOverlap k).ι, Category.id_comp, Category.assoc]
  refine (isPullback_descent k).hom_ext ?_ ?_
  · rw [← cancel_mono (awayQLocus k).ι]
    simp only [Category.assoc]
    rw [descentSwap_proj, descentSwap_proj_assoc, freeInvolution_comp_freeInvolution,
      Category.comp_id]
  · simp only [Category.assoc]
    rw [descentSwap_emb, descentSwap_emb_assoc, threefoldSwap_comp_self, Category.comp_id]

/-- A point `w₁` of `W` with `w₁ = τ w₂` in `V` for some point `w₂` of `W` lies in `W_O`: its
image `p w₁` in `ℙ³` is `σ (p w₂)`, and `σ (p w₁) = p w₂ ≠ Q`. -/
theorem mem_descentOverlap_of_apply_eq {w₁ w₂ : descentSpace k}
    (h : descentEmb k w₁ = threefoldSwap k (descentEmb k w₂)) : w₁ ∈ descentOverlap k := by
  have h₂ : (freeLocus k).ι ((awayQLocus k).ι (descentProj k w₂)) ∈ opensAwayQ k :=
    (descentProj k w₂).2
  change (freeLocus k).ι (freeInvolution k ((awayQLocus k).ι (descentProj k w₁))) ∈ opensAwayQ k
  rw [apply_eq_of_comp_eq (freeInvolution_ι k), descent_w_apply, h,
    apply_eq_of_comp_eq (threefoldSwap_hironakaMorphism k), involution_involution_apply,
    ← descent_w_apply]
  exact h₂

/-! ### The descent datum -/

section Datum

variable {S : Scheme.{u}} (π : (freeLocus k).toScheme ⟶ S)
  (hπ : IsPullback (coprod.desc (𝟙 _) (𝟙 _)) (coprod.desc (𝟙 _) (freeInvolution k)) π π)

/-- **The descent datum of `ρ`** for `W` relative to `X ⟶ S`. -/
def descentDatum :
    DescentData (S := S) (X := fun _ : Unit ↦ (awayQLocus k).toScheme)
      (fun _ ↦ (awayQLocus k).ι ≫ π) :=
  involutionDatum π (freeInvolution k) (freeInvolution_comp_freeInvolution k) hπ (awayQLocus k)
    (descentProj k) (descentSwap k) (descentSwap_proj k) (descentSwap_comp_self k)

/-- **The descent datum of `ρ` is projective over `X`.** -/
theorem isProjective_descentDatum : IsProjective ((descentDatum k π hπ).obj ()).hom := by
  rw [descentDatum, involutionDatum_obj]
  exact isProjective_descentProj k

end Datum

/-! ### The two charts of the model and the open `V'` -/

/-- The chart `t_P` of the model at `P` is an open immersion. -/
instance isOpenImmersion_towerToVP : IsOpenImmersion (towerToVP k) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_towerToVP k) inferInstance

/-- **The chart `t_Q = τ ∘ t_P` of the model at `Q`**, as a cartesian square over the chart
`D₊(X₁)` of `ℙ³`. -/
theorem isPullback_swappedTower : IsPullback (modelTower k) (towerToVP k ≫ threefoldSwap k)
    (chartQ k) (hironakaMorphism k) := by
  have h₂ : IsPullback (hironakaMorphism k) (threefoldSwap k) (involution k)
      (hironakaMorphism k) :=
    IsPullback.of_vert_isIso ⟨(threefoldSwap_hironakaMorphism k).symm⟩
  have h := (isPullback_towerToVP k).paste_vert h₂
  rwa [chartP_comp_involution] at h

/-- **The open `V' = t_P(T) ∪ t_Q(T)` of `V`.** -/
def chartUnion : (hironakaThreefold k).Opens :=
  (towerToVP k).opensRange ⊔ (towerToVP k ≫ threefoldSwap k).opensRange

/-- The points of `V'`. -/
theorem coe_chartUnion : (chartUnion k : Set (hironakaThreefold k)) =
    Set.range (towerToVP k) ∪ Set.range (towerToVP k ≫ threefoldSwap k) := by
  rw [chartUnion, TopologicalSpace.Opens.coe_sup, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange]

/-- `t_P` lands in `V'`. -/
theorem towerToVP_mem_chartUnion (m : modelSpace k) : towerToVP k m ∈ chartUnion k := by
  change _ ∈ (chartUnion k : Set (hironakaThreefold k))
  rw [coe_chartUnion]
  exact Or.inl ⟨m, rfl⟩

/-- `t_Q` lands in `V'`. -/
theorem swapped_mem_chartUnion (m : modelSpace k) :
    (towerToVP k ≫ threefoldSwap k) m ∈ chartUnion k := by
  change _ ∈ (chartUnion k : Set (hironakaThreefold k))
  rw [coe_chartUnion]
  exact Or.inr ⟨m, rfl⟩

/-- A morphism through `t_P` lands in `V'`. -/
theorem comp_towerToVP_apply_mem {T : Scheme.{u}} (a : T ⟶ modelSpace k) (z : T) :
    (a ≫ towerToVP k) z ∈ chartUnion k := by
  rw [Scheme.Hom.comp_apply]
  exact towerToVP_mem_chartUnion k _

/-- A morphism through `t_Q` lands in `V'`. -/
theorem comp_swapped_apply_mem {T : Scheme.{u}} (a : T ⟶ modelSpace k) (z : T) :
    (a ≫ towerToVP k ≫ threefoldSwap k) z ∈ chartUnion k := by
  rw [Scheme.Hom.comp_apply]
  exact swapped_mem_chartUnion k _

/-- **The two charts meet**: the point of `V` over `[1 : 1 : 1 : 0]` reached by `t_P` from a
point over the model point `(0, 0, 1)` is also reached by `t_Q`, from a point over `(1, 1, 0)`. -/
theorem exists_mem_range_inter : ∃ v, v ∈ Set.range (towerToVP k) ∧
    v ∈ Set.range (towerToVP k ≫ threefoldSwap k) := by
  have := Stacks.Examples.HironakaLocalModel.surjective_modelTower k
  obtain ⟨m, hm⟩ := (modelTower k).surjective (modelPoint k ![0, 0, 1])
  refine ⟨towerToVP k m, ⟨m, rfl⟩, ?_⟩
  refine mem_range_snd_of_isPullback (isPullback_swappedTower k)
    (x := modelPoint k ![1, 1, 0]) ?_
  rw [chartQ_modelPoint_eq_pointC₀, pointC₀, ← hm]
  exact apply_eq_of_comp_eq (isPullback_towerToVP k).w m

/-- **`V'` is integral and locally factorial**: it is covered by the images of two open
immersions of the integral, locally factorial source of the model tower, which meet. -/
theorem isIntegral_and_locallyFactorial_chartUnion :
    IsIntegral (chartUnion k).toScheme ∧
      ∀ x : (chartUnion k).toScheme, ∃ U : (chartUnion k).toScheme.affineOpens,
        x ∈ (U : Set (chartUnion k).toScheme) ∧
          UniqueFactorizationMonoid Γ((chartUnion k).toScheme, U) := by
  obtain ⟨v, hv₁, hv₂⟩ := exists_mem_range_inter k
  have hv : v ∈ (chartUnion k : Set (hironakaThreefold k)) := by
    rw [coe_chartUnion]
    exact Or.inl hv₁
  exact isIntegral_and_locallyFactorial_of_openImmersions
    (Stacks.Examples.HironakaLocalModel.exists_affineOpen_uniqueFactorizationMonoid k)
    (towerToVP k) (towerToVP k ≫ threefoldSwap k) (chartUnion k) (coe_chartUnion k).subset
    ⟨v, ⟨hv, hv₁⟩, hv₂⟩

/-! ### The curve `A` inside `W` -/

/-- The point `P`, as a `k`-point of `X`. -/
def pointPAwayQ : Spec (.of k) ⟶ (awayQLocus k).toScheme :=
  IsOpenImmersion.lift ((awayQLocus k).ι ≫ (freeLocus k).ι) (modelKPoint k 0 ≫ chartP k) (by
    rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy⟩ : pointP k ∈ Set.range (freeLocus k).ι := by
      rw [Scheme.Opens.range_ι]
      exact pointP_mem_freeLocus k
    have hmem : y ∈ awayQLocus k := by
      change (freeLocus k).ι y ∈ opensAwayQ k
      rw [hy, mem_opensAwayQ_iff]
      exact pointP_ne_pointQ k
    obtain ⟨x, hx⟩ : y ∈ Set.range (awayQLocus k).ι := by
      rw [Scheme.Opens.range_ι]
      exact hmem
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx, hy, modelKPoint_apply, chartP_origin])

/-- `pointPAwayQ` is the point `P`. -/
theorem pointPAwayQ_ι :
    pointPAwayQ k ≫ (awayQLocus k).ι ≫ (freeLocus k).ι = modelKPoint k 0 ≫ chartP k :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The fibre of the model over the origin lies in `W`**: a morphism `q` to the model lying
over the origin, composed with `t_P`, lifts to `W`. -/
theorem exists_lift_descentSpace {T : Scheme.{u}} (q : T ⟶ modelSpace k) (c : T ⟶ Spec (.of k))
    (h : q ≫ modelTower k = c ≫ modelKPoint k 0) :
    ∃ l : T ⟶ descentSpace k, l ≫ descentEmb k = q ≫ towerToVP k :=
  ⟨(isPullback_descent k).lift (c ≫ pointPAwayQ k) (q ≫ towerToVP k) (by
    simp only [Category.assoc]
    rw [pointPAwayQ_ι, ← (isPullback_towerToVP k).w, ← Category.assoc q (modelTower k) (chartP k),
      h, Category.assoc]),
   (isPullback_descent k).lift_snd _ _ _⟩

/-- The lift to `W` of a closed subscheme of the fibre of the model over the origin is
injective. -/
theorem injective_of_comp_descentEmb {ZO A : Scheme.{u}} {qO : ZO ⟶ modelSpace k}
    {gO : ZO ⟶ Spec (.of k)} (sqO : IsPullback qO gO (modelTower k) (modelKPoint k 0))
    (i : A ⟶ ZO) [IsClosedImmersion i] {l : A ⟶ descentSpace k}
    (hl : l ≫ descentEmb k = i ≫ qO ≫ towerToVP k) : Function.Injective l := by
  have hK' : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (MvPolynomial.eval (0 : Fin 3 → k)))) :=
    IsClosedImmersion.spec_of_surjective _ (fun r => ⟨MvPolynomial.C r, by simp⟩)
  have hK : IsClosedImmersion (modelKPoint k 0) := hK'
  have hq : IsClosedImmersion qO :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) sqO.flip hK
  intro a b hab
  have h := congrArg (descentEmb k) hab
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl] at h
  simp only [Scheme.Hom.comp_apply] at h
  exact i.isClosedEmbedding.injective
    (qO.isClosedEmbedding.injective ((towerToVP k).isOpenEmbedding.injective h))

/-- A scheme isomorphic to `ℙ¹_k` is integral. -/
theorem isIntegral_of_iso_projectiveLine {A : Scheme.{u}}
    (eA : A ≅ AlgebraicGeometry.Proj (polyGrading k 1)) : IsIntegral A := by
  have := Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj k 1
  have : Nonempty A := ⟨eA.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion eA.hom

/-- **An effective Cartier divisor meeting `ℙ¹_k` properly restricts to a module of Euler
characteristic at least two.** If `g : A ⟶ Z` from a scheme `A ≅ ℙ¹_k` sends the generic point
off `𝒟` and some point into `𝒟`, the canonical section of `g^* 𝒪_Z(𝒟)` vanishes somewhere but
not generically, so `g^* 𝒪_Z(𝒟)` is ample, hence has `χ ≥ 2`. -/
theorem two_le_eulerSum_pullback_modulesInvertibleSheaf {A Z : Scheme.{u}} [IrreducibleSpace A]
    (gA : A ⟶ Spec (.of k)) (eA : A ≅ AlgebraicGeometry.Proj (polyGrading k 1))
    (heA : eA.hom ≫ projToSpecCoeff k 1 = gA) (D : Z.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (g : A ⟶ Z) (x : A)
    (hη : g (genericPoint A) ∉ D.supportSet) (hx : g x ∈ D.supportSet) :
    2 ≤ eulerSum k gA
      ((Scheme.Modules.pullback g).obj (Stacks.Divisors.modulesInvertibleSheaf D)) := by
  have := isProper_of_iso_projectiveLine gA eA heA
  have hdim : topologicalKrullDim A = 1 := topologicalKrullDim_of_iso_projectiveLine eA
  have hL := Stacks.Divisors.isInvertible_pullback_modulesInvertibleSheaf D g
  obtain ⟨s, hs⟩ := Stacks.Divisors.exists_section_pullback_modulesInvertibleSheaf D g
  have hgen := Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne_eq_singleton A hdim
  have hamp : Scheme.Modules.IsAmple A
      ((Scheme.Modules.pullback g).obj (Stacks.Divisors.modulesInvertibleSheaf D)) := by
    refine isAmple_of_mem_nonvanishingLocus_genericPointsOne k gA hdim.le _ s ?_ ?_
    · intro ζ hζ
      rw [hgen, Set.mem_singleton_iff] at hζ
      subst hζ
      exact (hs _).mpr hη
    · intro ζ hζ
      rw [hgen, Set.mem_singleton_iff] at hζ
      subst hζ
      exact ⟨x, specializes_iff_mem_closure.mp (genericPoint_specializes x),
        fun hmem => (hs x).mp hmem hx⟩
  have : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible A.presheaf A.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (Stacks.Divisors.modulesInvertibleSheaf D)) := hL
  exact two_le_eulerSum_of_isAmple_of_iso_projectiveLine gA eA heA _ hamp

/-! ### Non-effectivity -/

/-- The open of `W_O` lying in `V'` and over `Wa`. -/
def overlapGood {U : Scheme.{u}} (Φ : descentSpace k ⟶ U) (Wa : U.Opens) :
    (descentOverlap k).toScheme.Opens :=
  ((descentOverlap k).ι ≫ descentEmb k) ⁻¹ᵁ chartUnion k ⊓ ((descentOverlap k).ι ≫ Φ) ⁻¹ᵁ Wa

/-- Membership in `overlapGood`. -/
theorem mem_overlapGood_iff {U : Scheme.{u}} (Φ : descentSpace k ⟶ U) (Wa : U.Opens)
    (t : (descentOverlap k).toScheme) :
    t ∈ overlapGood k Φ Wa ↔ descentEmb k ((descentOverlap k).ι t) ∈ chartUnion k ∧
      Φ ((descentOverlap k).ι t) ∈ Wa := by
  rw [overlapGood, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage,
    Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

/-- **The two pulled back functions have the same germ.** Let `Φ : W ⟶ U` be invariant under
`ρ` and `fa` a section of `U` over `Wa`. On the integral scheme `V'`, the pullbacks of `fa`
through `W ⟶ V` and through `τ ∘ (W ⟶ V)` have the same image in the function field: over the
part of `W_O` in `V'` and over `Wa`, the second is the first composed with `ρ`. -/
theorem germ_sectionOn_eq {U : Scheme.{u}} (Φ : descentSpace k ⟶ U)
    (hinv : (descentOverlap k).ι ≫ Φ = descentSwap k ≫ (descentOverlap k).ι ≫ Φ)
    [IsIntegral (chartUnion k).toScheme] {Wa : U.Opens} (fa : Γ(U, Wa))
    [h₁ : Nonempty (opensAlong (chartUnion k) (descentEmb k) Φ Wa)]
    [h₂ : Nonempty (opensAlong (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ Wa)] :
    (chartUnion k).toScheme.germToFunctionField _ (sectionOn (chartUnion k) (descentEmb k) Φ fa) =
      (chartUnion k).toScheme.germToFunctionField _
        (sectionOn (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ fa) := by
  obtain ⟨⟨z₁, hz₁⟩⟩ := id h₁
  obtain ⟨⟨z₂, hz₂⟩⟩ := id h₂
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter
    (opensAlong (chartUnion k) (descentEmb k) Φ Wa).isOpen
    (opensAlong (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ Wa).isOpen
    ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
  obtain ⟨w₁, hw₁, hw₁z⟩ := exists_of_mem_image (descentEmb k) (U := Φ ⁻¹ᵁ Wa)
    (v := (chartUnion k).ι z) hz.1
  obtain ⟨w₂, -, hw₂z⟩ := exists_of_mem_image (descentEmb k ≫ threefoldSwap k) (U := Φ ⁻¹ᵁ Wa)
    (v := (chartUnion k).ι z) hz.2
  have h₁₂ : descentEmb k w₁ = threefoldSwap k (descentEmb k w₂) := by
    rw [hw₁z, ← hw₂z, Scheme.Hom.comp_apply]
  have hw₁O : w₁ ∈ descentOverlap k := mem_descentOverlap_of_apply_eq k h₁₂
  obtain ⟨t₁, ht₁⟩ : w₁ ∈ Set.range (descentOverlap k).ι := by
    rw [Scheme.Opens.range_ι]
    exact hw₁O
  have ht₁G : t₁ ∈ overlapGood k Φ Wa := by
    refine (mem_overlapGood_iff k Φ Wa _).mpr ⟨?_, ?_⟩
    · rw [ht₁, hw₁z]
      exact ι_apply_mem _ z
    · rw [ht₁]
      exact hw₁
  obtain ⟨t₀, -⟩ : t₁ ∈ Set.range (overlapGood k Φ Wa).ι := by
    rw [Scheme.Opens.range_ι]
    exact ht₁G
  obtain ⟨j, hj⟩ := exists_comp_ι_eq_of_forall_mem (chartUnion k)
    ((overlapGood k Φ Wa).ι ≫ (descentOverlap k).ι ≫ descentEmb k) (fun t => by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact ((mem_overlapGood_iff k Φ Wa _).mp (ι_apply_mem _ t)).1)
  have : IsOpenImmersion (j ≫ (chartUnion k).ι) := by
    rw [hj]
    infer_instance
  have : IsOpenImmersion j := IsOpenImmersion.of_comp j (chartUnion k).ι
  have hj₁ : j ≫ (chartUnion k).ι =
      ((overlapGood k Φ Wa).ι ≫ (descentOverlap k).ι) ≫ descentEmb k := by
    rw [hj, Category.assoc]
  have hj₂ : j ≫ (chartUnion k).ι =
      ((overlapGood k Φ Wa).ι ≫ descentSwap k ≫ (descentOverlap k).ι) ≫
        descentEmb k ≫ threefoldSwap k := by
    rw [hj]
    simp only [Category.assoc, descentSwap_emb_assoc, threefoldSwap_comp_self, Category.comp_id]
  have hΦ : ((overlapGood k Φ Wa).ι ≫ descentSwap k ≫ (descentOverlap k).ι) ≫ Φ =
      ((overlapGood k Φ Wa).ι ≫ (descentOverlap k).ι) ≫ Φ := by
    simp only [Category.assoc]
    rw [← hinv]
  have h'₁ : ⊤ ≤ (((overlapGood k Φ Wa).ι ≫ (descentOverlap k).ι) ≫ Φ) ⁻¹ᵁ Wa := by
    intro t _
    change t ∈ (((overlapGood k Φ Wa).ι ≫ (descentOverlap k).ι) ≫ Φ) ⁻¹ᵁ Wa
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ((mem_overlapGood_iff k Φ Wa _).mp (ι_apply_mem _ t)).2
  have h'₂ : ⊤ ≤ (((overlapGood k Φ Wa).ι ≫ descentSwap k ≫ (descentOverlap k).ι) ≫ Φ) ⁻¹ᵁ
      Wa := by
    rw [hΦ]
    exact h'₁
  have hle₁ := top_le_preimage_opensAlong (chartUnion k) (descentEmb k) Φ Wa j _ hj₁ h'₁
  have hle₂ := top_le_preimage_opensAlong (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ Wa
    j _ hj₂ h'₂
  refine germToFunctionField_eq_of_appLE_eq _ _ j t₀ hle₁ hle₂ ?_
  rw [appLE_sectionOn (chartUnion k) (descentEmb k) Φ fa j _ hj₁ h'₁ hle₁,
    appLE_sectionOn (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ fa j _ hj₂ h'₂ hle₂,
    appLE_eq_of_hom_eq hΦ.symm Wa ⊤ h'₁ h'₂]

/-- **No étale `ρ`-invariant morphism out of `W`.** A locally quasi-finite morphism
`Φ : W ⟶ U` invariant under `ρ` does not exist: it would produce an invertible module on `V'`
restricting to ample modules on both copies of `ℙ¹_k` in the fibres over `P` and `Q`, against
`χ(ℋ|A_P) + χ(ℋ|A_Q) = 2`. -/
theorem false_of_isInvariant {U : Scheme.{u}} (Φ : descentSpace k ⟶ U) [LocallyQuasiFinite Φ]
    (hinv : (descentOverlap k).ι ≫ Φ = descentSwap k ≫ (descentOverlap k).ι ≫ Φ) : False := by
  obtain ⟨ZO, qO, gO, sqO, IA, eA, heA, hrel⟩ := exists_eulerSum_add_eq_two_of_opens k
  have : IsIntegral IA.subscheme := isIntegral_of_iso_projectiveLine k eA
  -- the curve `A` inside `W`
  obtain ⟨jW, hjW⟩ := exists_lift_descentSpace k (IA.subschemeι ≫ qO) (IA.subschemeι ≫ gO)
    (by simp only [Category.assoc, sqO.w])
  have hjW' : jW ≫ descentEmb k = IA.subschemeι ≫ qO ≫ towerToVP k := by
    rw [hjW, Category.assoc]
  have hinj : Function.Injective jW := injective_of_comp_descentEmb k sqO IA.subschemeι hjW'
  -- two points of `A` and their distinct images in `U`
  obtain ⟨x, hx⟩ := exists_ne_genericPoint IA.subscheme
    (topologicalKrullDim_of_iso_projectiveLine eA)
  have hηx : genericPoint IA.subscheme ⤳ x := genericPoint_specializes x
  have hW : jW (genericPoint IA.subscheme) ⤳ jW x := hηx.map jW.continuous
  obtain ⟨Wa, fa, -, hxWa, hηWa, hηfa, hxfa⟩ := exists_affineOpen_separating
    (hW.map Φ.continuous) (fun h => hx (hinj (eq_of_specializes_of_apply_eq Φ hW h)).symm)
  -- the open `V'` and the two copies of `A` in it
  obtain ⟨hIntV, hufdV⟩ := isIntegral_and_locallyFactorial_chartUnion k
  have := hIntV
  obtain ⟨gP, hgP⟩ := exists_comp_ι_eq_of_forall_mem (chartUnion k)
    (IA.subschemeι ≫ qO ≫ towerToVP k)
    (fun z => by
      simpa only [Category.assoc] using comp_towerToVP_apply_mem k (IA.subschemeι ≫ qO) z)
  obtain ⟨gQ, hgQ⟩ := exists_comp_ι_eq_of_forall_mem (chartUnion k)
    (IA.subschemeι ≫ qO ≫ towerToVP k ≫ threefoldSwap k)
    (fun z => by
      simpa only [Category.assoc] using comp_swapped_apply_mem k (IA.subschemeι ≫ qO) z)
  have hPpt : ∀ z, (chartUnion k).ι (gP z) = descentEmb k (jW z) :=
    apply_eq_of_comp_eq (hgP.trans hjW'.symm)
  have hQpt : ∀ z, (chartUnion k).ι (gQ z) = (descentEmb k ≫ threefoldSwap k) (jW z) :=
    apply_eq_of_comp_eq (hgQ.trans
      (show _ = jW ≫ descentEmb k ≫ threefoldSwap k by rw [reassoc_of% hjW']))
  have hP₁ : ∀ z, Φ (jW z) ∈ Wa → gP z ∈ opensAlong (chartUnion k) (descentEmb k) Φ Wa :=
    fun z hz => (mem_opensAlong_iff (chartUnion k) (descentEmb k) Φ Wa (hPpt z)).mpr hz
  have hQ₁ : ∀ z, Φ (jW z) ∈ Wa →
      gQ z ∈ opensAlong (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ Wa :=
    fun z hz => (mem_opensAlong_iff (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ Wa
      (hQpt z)).mpr hz
  have : Nonempty (opensAlong (chartUnion k) (descentEmb k) Φ Wa) := ⟨⟨gP x, hP₁ x hxWa⟩⟩
  have : Nonempty (opensAlong (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ Wa) :=
    ⟨⟨gQ x, hQ₁ x hxWa⟩⟩
  -- the rational function `h` and its divisor of zeros
  have hgerm := germ_sectionOn_eq k Φ hinv fa
  obtain ⟨h, hh⟩ : ∃ h, (chartUnion k).toScheme.germToFunctionField _
      (sectionOn (chartUnion k) (descentEmb k) Φ fa) = h := ⟨_, rfl⟩
  have hh₂ : (chartUnion k).toScheme.germToFunctionField _
      (sectionOn (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ fa) = h := hgerm.symm.trans hh
  have hr0 : sectionOn (chartUnion k) (descentEmb k) Φ fa ≠ 0 := by
    intro h0
    have hmem := (mem_basicOpen_sectionOn_iff (chartUnion k) (descentEmb k) Φ fa
      (hPpt (genericPoint IA.subscheme))).mpr hηfa
    rw [h0, Scheme.basicOpen_zero] at hmem
    exact hmem
  have hne : h ≠ 0 := by
    rw [← hh]
    exact fun h0 => hr0 ((chartUnion k).toScheme.germToFunctionField_injective _
      (by simp [h0]))
  have : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroDivisor h) :=
    Stacks.Divisors.isEffectiveCartierDivisor_zeroDivisor hufdV hne
  have hsuppP : ∀ z, Φ (jW z) ∈ Wa →
      (gP z ∈ (Stacks.Divisors.zeroDivisor h).supportSet ↔ Φ (jW z) ∉ U.basicOpen fa) :=
    fun z hz => by
      rw [Stacks.Divisors.mem_supportSet_zeroDivisor_iff
        (sectionOn (chartUnion k) (descentEmb k) Φ fa) hh (hP₁ z hz),
        mem_basicOpen_sectionOn_iff (chartUnion k) (descentEmb k) Φ fa (hPpt z)]
  have hsuppQ : ∀ z, Φ (jW z) ∈ Wa →
      (gQ z ∈ (Stacks.Divisors.zeroDivisor h).supportSet ↔ Φ (jW z) ∉ U.basicOpen fa) :=
    fun z hz => by
      rw [Stacks.Divisors.mem_supportSet_zeroDivisor_iff
        (sectionOn (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ fa) hh₂ (hQ₁ z hz),
        mem_basicOpen_sectionOn_iff (chartUnion k) (descentEmb k ≫ threefoldSwap k) Φ fa
          (hQpt z)]
  -- both restrictions of `𝒪(𝒟)` are ample, against the Euler-characteristic relation
  have h2P := two_le_eulerSum_pullback_modulesInvertibleSheaf k (IA.subschemeι ≫ gO) eA heA
    (Stacks.Divisors.zeroDivisor h) gP x
    (fun hmem => (hsuppP _ hηWa).mp hmem hηfa) ((hsuppP x hxWa).mpr hxfa)
  have h2Q := two_le_eulerSum_pullback_modulesInvertibleSheaf k (IA.subschemeι ≫ gO) eA heA
    (Stacks.Divisors.zeroDivisor h) gQ x
    (fun hmem => (hsuppQ _ hηWa).mp hmem hηfa) ((hsuppQ x hxWa).mpr hxfa)
  have : Stacks.SheafOfModules.IsInvertible (chartUnion k).toScheme.presheaf
      (chartUnion k).toScheme.ringCatSheaf.2
      (Stacks.Divisors.modulesInvertibleSheaf (Stacks.Divisors.zeroDivisor h)) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Stacks.Divisors.isInvertible_modulesInvertibleSheaf _)
  have key := hrel (hironakaMorphism k) (chartP k) (chartQ k) (towerToVP k)
    (towerToVP k ≫ threefoldSwap k) (isPullback_towerToVP k) (isPullback_swappedTower k)
    (modelKPoint_chartP_eq_chartQ_c₀ k) (modelKPoint_chartP_eq_chartQ_d₀ k) (chartUnion k)
    (fun m _ => towerToVP_mem_chartUnion k m) (fun m _ => swapped_mem_chartUnion k m) gP gQ hgP
    hgQ (Stacks.Divisors.modulesInvertibleSheaf (Stacks.Divisors.zeroDivisor h))
  omega

/-- **The descent datum of `ρ` is not effective.** An effective datum would make `W` a base
change `U ×_S X` with `W ⟶ U` étale and `ρ`-invariant, which
`Stacks.Examples.HironakaInvolution.false_of_isInvariant` excludes. -/
theorem not_isEffective_descentDatum {S : Scheme.{u}} (π : (freeLocus k).toScheme ⟶ S)
    [Etale π]
    (hπ : IsPullback (coprod.desc (𝟙 _) (𝟙 _)) (coprod.desc (𝟙 _) (freeInvolution k)) π π) :
    ¬ (descentDatum k π hπ).IsEffective := by
  intro hD
  obtain ⟨U, g, Φ, hpb, hinv⟩ := exists_isPullback_of_isEffective_involutionDatum π
    (freeInvolution k) (freeInvolution_comp_freeInvolution k) hπ (awayQLocus k) (descentProj k)
    (descentSwap k) (descentSwap_proj k) (descentSwap_comp_self k) hD
  have : Etale Φ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hpb.flip inferInstance
  have : LocallyQuasiFinite Φ := (locallyQuasiFinite_of_etale Φ).2
  exact false_of_isInvariant k Φ hinv

/-- **A non-effective projective étale descent datum, over a field with `2 ≠ 0`.** -/
theorem exists_etale_descentData_projective_not_isEffective_of_two_ne_zero
    (h2 : (2 : k) ≠ 0) :
    ∃ (S X : Scheme.{u}) (f : X ⟶ S)
      (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f)),
      Presieve.singleton f ∈ Scheme.etalePrecoverage S ∧
        IsProjective (D.obj ()).hom ∧ ¬ D.IsEffective := by
  obtain ⟨S, π, hπe, hπs, -, hπ⟩ := exists_etale_quotient_of_free_involution (freeInvolution k)
    (freeInvolution_comp_freeInvolution k)
    (fun c hc => isEmpty_of_comp_freeInvolution_eq k h2 c hc)
    (fun E hE => Proj.exists_isAffineOpen_finite_subset_mvPolynomial k (freeLocus k) E hE)
  have := hπe
  have := hπs
  exact ⟨S, (awayQLocus k).toScheme, (awayQLocus k).ι ≫ π, descentDatum k π hπ,
    singleton_mem_etalePrecoverage k π hπ, isProjective_descentDatum k π hπ,
    not_isEffective_descentDatum k π hπ⟩

end Stacks.Examples.HironakaInvolution

namespace Stacks.Examples.NonEffectiveProjectiveDescent

/-- `2 ≠ 0` in `ULift ℚ`. -/
theorem two_ne_zero_uLift : (2 : ULift.{u} ℚ) ≠ 0 := by
  intro h
  have h' := congrArg (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ) h
  rw [map_ofNat, map_zero] at h'
  norm_num at h'

/-- **There is a non-effective projective descent datum along an étale covering.** There are an
étale covering of a scheme consisting of a single morphism `f : X ⟶ S` and a descent datum
relative to `f` whose scheme over `X` is projective over `X` and which is not effective in the
category of schemes. This is [Stacks, Tag 08KF] with no hypothesis; the witness is built over
`ULift ℚ` by
`HironakaInvolution.exists_etale_descentData_projective_not_isEffective_of_two_ne_zero`. -/
@[stacks 08KF "The source's construction over ℚ: the involution [x:y:z:w] ↦ [y:x:w:z] of ℙ³
acts freely on Y = ℙ³ minus two lines, Y → S = Y/G is an étale double cover, Hironaka's threefold
over ℙ³ carries the lifted involution, and its restriction gives the descent datum. Two choices
differ from the text: the étale covering is the single open Y − {Q} → S (a member of the source's
covering (Y − P) ⊔ (Y − Q), already surjective onto S), and non-effectivity is derived from
χ(H|L₀) + χ(H|g(L₀)) = 2 for invertible H (the Euler-characteristic form of L₀ + g(L₀) ∼ 0) applied
to the divisor of a function on the would-be quotient, instead of degrees of 1-cycles"]
theorem exists_etale_descentData_projective_not_isEffective :
    ∃ (S X : Scheme.{u}) (f : X ⟶ S)
      (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f)),
      Presieve.singleton f ∈ Scheme.etalePrecoverage S ∧
        IsProjective (D.obj ()).hom ∧ ¬ D.IsEffective :=
  HironakaInvolution.exists_etale_descentData_projective_not_isEffective_of_two_ne_zero
    (ULift.{u} ℚ) two_ne_zero_uLift

end Stacks.Examples.NonEffectiveProjectiveDescent

end
