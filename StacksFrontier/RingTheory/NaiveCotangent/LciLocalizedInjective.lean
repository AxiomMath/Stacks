module

public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.JacobiZariski
public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiPresentations
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermDoubleQuasiIso

/-!
# Injectivity on `H₁` of the Jacobi-Zariski comparison, after localization

Let `A → B → C` be ring maps with `B → C` a local complete intersection homomorphism, and let
`A'`, `B'`, `C'` be localizations of `A`, `B`, `C` at multiplicative subsets, compatibly with the
tower.  Then the canonical map of two-term complexes of
`C'`-modules

`NL_{B'/A'} ⊗_{B'} C' ⟶ NL_{C'/A'}`

is **injective on `H₁`**.  This is the sole assertion the six-term exact sequence of
Stacks 00S2 does not contain, it is what puts a zero at the left of that sequence, and over the
stalks of a morphism of schemes it is what makes the canonical map of Stacks 0E1Z to the shifted
cone an isomorphism in the derived category.

The input at the un-localized level is Stacks 07D4
(`RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection`): for a presentation
`α` of `B` over `A` and a *finite* presentation `β` of `C` over `B`, the conormal comparison
`C ⊗_B (I/I²) → K/K²` of the induced presentation `β.comp α` is injective — injective in degree
`1`, before restricting to kernels, hence injective on `H₁`.  The passage to the localizations is
the content of this file, and it is needed because `B' → C'` is *not* of finite type, so
Stacks 07D4 does not apply to the localized tower at all.

## Main results

* `NaiveCotangent.IsQuasiIso.surjective_onH₁_baseChange`: the base change of a
  quasi-isomorphism of two-term complexes along an **arbitrary** ring map is still surjective on
  `H₁`.  Flatness is not needed for this half; `NaiveCotangent.IsQuasiIso.baseChange` needs it
  for the injective half.  The proof is the exactness of the three-term cone of a
  quasi-isomorphism together with right exactness of the tensor product.
* `NaiveCotangent.injective_onH₁_baseChange_of_flat`: a flat base change preserves injectivity
  on `H₁`.
* `NaiveCotangent.nlExtensionBaseChangeMap_comp_cancelBaseChangeChainMap`: the composition
  identity for the base-changed comparison over **three** bases, which
  `StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiPresentations` asks for and which
  `NaiveCotangent.nlExtensionBaseChangeMap_flatBaseLocalizedHom_comp_cancel` is one instance of.
* `NaiveCotangent.injective_onH₁_nlExtensionBaseChangeMap_of_isLocalCompleteIntersection`:
  Stacks 07D4 read on `H₁` over the canonical presentations.
* `NaiveCotangent.injective_onH₁_nlExtensionBaseChangeMap_of_isLocalization_of_lci`: **the main
  result**, the localized statement.

## Implementation notes

The three-term cone of a chain map `f : A ⟶ B` of two-term complexes is
`A.X₁ ⟶ A.X₀ × B.X₁ ⟶ B.X₀`, and `f` is a quasi-isomorphism exactly when that sequence is
exact and its right-hand map is surjective; only those two halves are proved here, in
`NaiveCotangent.exact_coneIn_coneOut` and `NaiveCotangent.surjective_coneOut`, since
injectivity of the left-hand map is the half that does not survive a base change.  The product
forces the four modules of the two complexes into one universe, which is why the statements of
this section are at `NaiveCotangent.TwoTerm.{u, v, v}`, as the elementwise readings of
`StacksFrontier.RingTheory.NaiveCotangent.TwoTermDoubleQuasiIso` already are.

The main theorem is stated for every morphism of extensions between the canonical presentations,
in the style of `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_atPrime`: any two are
homotopic, so the map induced on `H₁` does not depend on the choice, and a consumer reading the
comparison off a stalk has whichever morphism its own construction produced.

The chain of the proof.  Write `P₀` for the canonical presentation of `B` over `A`.  Stacks 07D4
gives injectivity of the degree-`1` component of `NL(P₀) ⊗_B C ⟶ NL(β.comp P₀)`; composing with
the comparison to the canonical presentation of `C` over `A`, which is a quasi-isomorphism by
Stacks 00S1 (4), and using homotopy invariance, gives injectivity on `H₁` of
`NL_{B/A} ⊗_B C ⟶ NL_{C/A}`.  That base changes to `C'` along the flat map `C → C'`, and the
composition identity below rewrites the result as
`NL_{B/A} ⊗_B C' ⟶ NL_{C'/A'}` composed with the cancellation of the intermediate base change;
since `NL_{C/A} ⊗_C C' ⟶ NL_{C'/A'}` is a quasi-isomorphism (localization of base and target),
`NL_{B/A} ⊗_B C' ⟶ NL_{C'/A'}` is injective on `H₁`.  Factoring that same map the other way,
through `NL_{B'/A'} ⊗_{B'} C'`, its first leg is the base change along `B' → C'` — which is
**not** flat — of the localization quasi-isomorphism `NL_{B/A} ⊗_B B' ⟶ NL_{B'/A'}`, and is
therefore surjective on `H₁` by the first result above.  An injective map that factors through a
surjection has its second factor injective, which is the conclusion.

## References

* [Stacks Project, Tag 07D4](https://stacks.math.columbia.edu/tag/07D4), the un-localized
  injectivity.
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), the six-term sequence
  this injectivity extends on the left.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), independence of the
  presentation.
* [Stacks Project, Tag 00S7](https://stacks.math.columbia.edu/tag/00S7) and
  [Stacks Project, Tag 07BS](https://stacks.math.columbia.edu/tag/07BS), localization of the
  target and of the base.
-/

@[expose] public section

universe u v

open Algebra TensorProduct

namespace NaiveCotangent

/-! ### The three-term cone of a chain map of two-term complexes -/

section Cone

variable {S : Type u} [CommRing S] {A B : TwoTerm.{u, v, v} S}

/-- The first map `A₁ ⟶ A₀ × B₁` of the three-term cone of a chain map of two-term complexes. -/
noncomputable def coneIn (f : ChainMap A B) : A.X₁ →ₗ[S] A.X₀ × B.X₁ :=
  LinearMap.prod A.d (-f.f₁)

/-- The second map `A₀ × B₁ ⟶ B₀` of the three-term cone of a chain map of two-term
complexes. -/
noncomputable def coneOut (f : ChainMap A B) : A.X₀ × B.X₁ →ₗ[S] B.X₀ :=
  LinearMap.coprod f.f₀ B.d

@[simp] theorem coneIn_apply (f : ChainMap A B) (x : A.X₁) :
    coneIn f x = (A.d x, -f.f₁ x) := rfl

@[simp] theorem coneOut_apply (f : ChainMap A B) (p : A.X₀ × B.X₁) :
    coneOut f p = f.f₀ p.1 + B.d p.2 := rfl

/-- **The three-term cone of a quasi-isomorphism is exact in the middle.**  An element
`(a, b)` of `A₀ × B₁` with `f₀ a + d b = 0` is `(d x, -f₁ x)` for some `x`: the class of `a` in
`H₀(A)` dies in `H₀(B)`, so `a = d x₀`, and then `f₁ x₀ + b` is a cycle, so it is `f₁` of a cycle
of `A`, which corrects `x₀`. -/
theorem exact_coneIn_coneOut {f : ChainMap A B} (hf : IsQuasiIso f) :
    Function.Exact (coneIn f) (coneOut f) := by
  intro p
  constructor
  · intro hp
    rw [coneOut_apply] at hp
    have hdb : B.d p.2 = f.f₀ (-p.1) := by
      rw [map_neg]
      linear_combination (norm := module) hp
    obtain ⟨z, hz⟩ :=
      Stacks.TwoTermDoubleQuasiIso.exists_d_eq_of_injective_onH₀ hf.2.injective (-p.1) ⟨p.2, hdb⟩
    have hx₀ : A.d (-z) = p.1 := by rw [map_neg, hz, neg_neg]
    have hcyc : B.d (f.f₁ (-z) + p.2) = 0 := by
      rw [map_add, chainMap_comm_apply f (-z), hx₀, hdb, map_neg]
      abel
    obtain ⟨k, hk0, hk⟩ :=
      Stacks.TwoTermDoubleQuasiIso.exists_eq_of_surjective_onH₁ hf.1.surjective _ hcyc
    refine ⟨-z - k, Prod.ext ?_ ?_⟩
    · rw [coneIn_apply, map_sub, hk0, sub_zero, hx₀]
    · rw [coneIn_apply]
      change -f.f₁ (-z - k) = p.2
      rw [map_sub, hk, neg_sub]
      abel
  · rintro ⟨x, rfl⟩
    simp only [coneIn_apply, coneOut_apply, map_neg, chainMap_comm_apply f x, add_neg_cancel]

/-- **The second map of the three-term cone of a quasi-isomorphism is surjective**: every element
of `B₀` is `f₀` of something plus a boundary, which is surjectivity on `H₀`. -/
theorem surjective_coneOut {f : ChainMap A B} (hf : IsQuasiIso f) :
    Function.Surjective (coneOut f) := by
  intro y
  obtain ⟨x, z, hxz⟩ :=
    Stacks.TwoTermDoubleQuasiIso.exists_add_d_eq_of_surjective_onH₀ hf.2.surjective y
  exact ⟨(x, z), hxz⟩

end Cone

/-! ### Base change of a quasi-isomorphism along an arbitrary ring map -/

section ArbitraryBaseChange

variable {S : Type u} [CommRing S] {A B : TwoTerm.{u, v, v} S}
  (T : Type*) [CommRing T] [Algebra S T]

private theorem baseChange_comp_eq {M N P : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] [AddCommGroup P] [Module S P]
    (φ : M →ₗ[S] N) (ψ : N →ₗ[S] P) {χ : M →ₗ[S] P} (h : ψ ∘ₗ φ = χ) (z : T ⊗[S] M) :
    LinearMap.baseChange T ψ (LinearMap.baseChange T φ z) = LinearMap.baseChange T χ z := by
  rw [← h, LinearMap.baseChange_comp, LinearMap.comp_apply]

/-- **A cycle of `B₁ ⊗ T` is the image of a cycle of `A₁ ⊗ T`**, for `f` a quasi-isomorphism and
`T` an arbitrary `S`-algebra.  The three-term cone of a quasi-isomorphism is exact in the middle
with a surjective right-hand map, and that much exactness survives any base change by right
exactness of the tensor product; the inclusion of `y` into `(A₀ × B₁) ⊗ T` is then killed by the
right-hand map, so it is the image of some `w`, and the two projections of that equation say that
`-w` is a cycle mapping to `y`. -/
private theorem exists_cycle_baseChange {f : ChainMap A B} (hf : IsQuasiIso f)
    (y : T ⊗[S] B.X₁) (hy : LinearMap.baseChange T B.d y = 0) :
    ∃ x : T ⊗[S] A.X₁,
      LinearMap.baseChange T A.d x = 0 ∧ LinearMap.baseChange T f.f₁ x = y := by
  have hex := exact_baseChange T (exact_coneIn_coneOut hf) (surjective_coneOut hf)
  have hker : LinearMap.baseChange T (coneOut f)
      (LinearMap.baseChange T (LinearMap.inr S A.X₀ B.X₁) y) = 0 := by
    rw [baseChange_comp_eq T _ _ (χ := B.d) (LinearMap.ext fun _ => by simp), hy]
  obtain ⟨w, hw⟩ := (hex _).mp hker
  have hfst := baseChange_comp_eq T (coneIn f) (LinearMap.fst S A.X₀ B.X₁) (χ := A.d)
    (LinearMap.ext fun _ => rfl) w
  have hsnd := baseChange_comp_eq T (coneIn f) (LinearMap.snd S A.X₀ B.X₁) (χ := -f.f₁)
    (LinearMap.ext fun _ => rfl) w
  have hfstinr := baseChange_comp_eq T (LinearMap.inr S A.X₀ B.X₁) (LinearMap.fst S A.X₀ B.X₁)
    (χ := 0) (LinearMap.ext fun _ => rfl) y
  have hsndinr := baseChange_comp_eq T (LinearMap.inr S A.X₀ B.X₁) (LinearMap.snd S A.X₀ B.X₁)
    (χ := LinearMap.id) (LinearMap.ext fun _ => rfl) y
  rw [hw] at hfst hsnd
  rw [LinearMap.baseChange_zero, LinearMap.zero_apply] at hfstinr
  rw [LinearMap.baseChange_id, LinearMap.id_coe, id_eq] at hsndinr
  rw [LinearMap.baseChange_neg, LinearMap.neg_apply] at hsnd
  refine ⟨-w, ?_, ?_⟩
  · rw [map_neg, ← hfst, hfstinr, neg_zero]
  · rw [map_neg]
    exact hsnd.symm.trans hsndinr

/-- **The base change of a quasi-isomorphism along an arbitrary ring map is surjective on
`H₁`.**  No flatness is needed for this half; it is the half of
`NaiveCotangent.IsQuasiIso.baseChange` that right exactness of the tensor product already gives.
Injectivity on `H₁` is the half that genuinely needs flatness. -/
theorem IsQuasiIso.surjective_onH₁_baseChange {f : ChainMap A B} (hf : IsQuasiIso f) :
    Function.Surjective (f.baseChange T).onH₁ := by
  rintro ⟨y, hy⟩
  have hy' : LinearMap.baseChange T B.d y = 0 := hy
  obtain ⟨x, hx₁, hx₀⟩ := exists_cycle_baseChange T hf y hy'
  exact ⟨⟨x, hx₁⟩, Subtype.ext hx₀⟩

end ArbitraryBaseChange

/-! ### Flat base change preserves injectivity on `H₁` -/

section FlatBaseChange

variable {S : Type*} [CommRing S] {A B : TwoTerm S}
  (T : Type*) [CommRing T] [Algebra S T] [Module.Flat S T]

/-- **A flat base change preserves injectivity on `H₁`.**  For a flat base change the kernel of
the base changed differential is the base change of the kernel, and the base changed inclusion of
the kernel intertwines the base changed degree-`1` component with the base change of the map
induced on `H₁`; both of those stay injective, which is the statement. -/
theorem injective_onH₁_baseChange_of_flat {f : ChainMap A B}
    (hf : Function.Injective f.onH₁) : Function.Injective (f.baseChange T).onH₁ := by
  have hinjB : Function.Injective (LinearMap.baseChange T (H₁ B).subtype) :=
    injective_baseChange_of_flat T Subtype.coe_injective
  have hinjH : Function.Injective (LinearMap.baseChange T f.onH₁) :=
    injective_baseChange_of_flat T hf
  have hsub : ∀ x : T ⊗[S] A.X₁, LinearMap.baseChange T A.d x = 0 →
      ∃ w : T ⊗[S] (H₁ A), LinearMap.baseChange T (H₁ A).subtype w = x := by
    intro x hx
    have h2 : x ∈ LinearMap.ker (LinearMap.baseChange T A.d) := hx
    rw [ker_baseChange_eq_range_baseChange_subtype T A] at h2
    exact LinearMap.mem_range.mp h2
  intro ξ η hξη
  obtain ⟨w, hw⟩ := hsub ξ.1 ξ.2
  obtain ⟨w', hw'⟩ := hsub η.1 η.2
  have key : LinearMap.baseChange T (H₁ B).subtype (LinearMap.baseChange T f.onH₁ w) =
      LinearMap.baseChange T (H₁ B).subtype (LinearMap.baseChange T f.onH₁ w') := by
    rw [← baseChange_f₁_baseChange_subtype T f, ← baseChange_f₁_baseChange_subtype T f, hw, hw']
    exact congrArg Subtype.val hξη
  refine Subtype.ext ?_
  rw [← hw, ← hw']
  exact congrArg (LinearMap.baseChange T (H₁ A).subtype) (hinjH (hinjB key))

end FlatBaseChange

/-! ### The composition identity over three bases -/

section CancelComp

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Extension R S)
variable {R' D : Type*} [CommRing R'] [CommRing D] [Algebra R R'] [Algebra R' D] [Algebra R D]
  [Algebra S D] [IsScalarTower R R' D] {Q : Extension R' D}
variable {R'' C : Type*} [CommRing R''] [CommRing C] [Algebra R' R''] [Algebra R'' C]
  [Algebra R' C] [Algebra D C] [IsScalarTower R' R'' C]
  {Q' : Extension R'' C}
variable [Algebra R R''] [Algebra R C] [Algebra S C] [IsScalarTower R R'' C]
  [IsScalarTower S D C] [IsScalarTower R R' R'']

/-- **Stacks 00S1 (3) for the base-changed comparison, over three bases.**  Let `P`, `Q`, `Q'` be
extensions of `S` over `R`, of `D` over `R'` and of `C` over `R''`, in a tower
`R → R' → R''`, `S → D → C`.  The comparison `NL(P) ⊗_S C ⟶ NL(Q')` of a composite
`P ⟶ Q ⟶ Q'`, read through the cancellation `C ⊗_D (D ⊗_S NL(P)) ≅ C ⊗_S NL(P)` of the
intermediate base change, is the base change to `C` of the comparison `NL(P) ⊗_S D ⟶ NL(Q)`
followed by the comparison `NL(Q) ⊗_D C ⟶ NL(Q')`.

`NaiveCotangent.nlExtensionOverMap_comp_nlExtensionBaseChangeMap` and
`NaiveCotangent.nlExtensionBaseChangeMap_comp_eq` are the two instances of this identity in which
one of the two base changes is trivial, and
`NaiveCotangent.nlExtensionBaseChangeMap_flatBaseLocalizedHom_comp_cancel` is the instance at
flat base change followed by a localization. -/
theorem nlExtensionBaseChangeMap_comp_cancelBaseChangeChainMap (h₁ : P.Hom Q) (h₂ : Q.Hom Q') :
    (nlExtensionBaseChangeMap (T := C) (h₂.comp h₁)).comp
        (cancelBaseChangeChainMap (D := D) (C := C) P) =
      (nlExtensionBaseChangeMap (T := C) h₂).comp
        ((nlExtensionBaseChangeMap (T := D) h₁).baseChange C) := by
  have : IsScalarTower S D Q.Cotangent := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S D Q.CotangentSpace := isScalarTower_left
  have : IsScalarTower S C Q'.Cotangent := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower D C Q'.Cotangent := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S C Q'.CotangentSpace := isScalarTower_left
  have : IsScalarTower D C Q'.CotangentSpace := isScalarTower_left
  refine ChainMap.ext (LinearMap.ext fun z => ?_) (LinearMap.ext fun z => ?_)
  · exact liftBaseChange_cancelBaseChange (Extension.Cotangent.map h₁)
      (Extension.Cotangent.map h₂) (Extension.Cotangent.map (h₂.comp h₁))
      (fun m => DFunLike.congr_fun (Extension.Cotangent.map_comp _ h₁ h₂) m) z
  · exact liftBaseChange_cancelBaseChange (Extension.CotangentSpace.map h₁)
      (Extension.CotangentSpace.map h₂) (Extension.CotangentSpace.map (h₂.comp h₁))
      (fun m => DFunLike.congr_fun (Extension.CotangentSpace.map_comp h₁ h₂) m) z

end CancelComp

/-! ### Stacks 07D4 on `H₁`, over the canonical presentations -/

section Affine

universe w

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **Stacks 07D4, read on `H₁` over the canonical presentations.**  For ring maps `A → B → C`
with `B → C` a local complete intersection homomorphism, the canonical map

`NL_{B/A} ⊗_B C ⟶ NL_{C/A}`

of two-term complexes of `C`-modules is injective on `H₁`.  Together with the six-term exact
sequence of Stacks 00S2 this puts a zero at the left of that sequence.

The statement holds for every morphism of extensions inducing the comparison, any two being
homotopic.  Stacks 07D4 gives injectivity of the whole degree-`1` component for the presentation
`β.comp α` induced by the canonical presentation `α` of `B` over `A` and a finite presentation
`β` of `C` over `B`; the comparison of that presentation with the canonical presentation of `C`
over `A` is a quasi-isomorphism by Stacks 00S1 (4), and injectivity on `H₁` is inherited. -/
@[stacks 07D4 "the zero on the left of the 00S2 sequence, over the canonical presentations"]
theorem injective_onH₁_nlExtensionBaseChangeMap_of_isLocalCompleteIntersection
    (h : RingHom.IsLocalCompleteIntersection (algebraMap B C))
    (hom : (Generators.self A B).toExtension.Hom (Generators.self A C).toExtension) :
    Function.Injective (nlExtensionBaseChangeMap (T := C) hom).onH₁ := by
  classical
  -- a finite presentation of `C` over `B`, which exists because `B → C` is of finite type.
  have hft : Algebra.FiniteType B C := by
    have hf := h.1
    rwa [RingHom.FiniteType, toAlgebra_algebraMap] at hf
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  have hsurj : Function.Surjective
      (MvPolynomial.aeval (R := B) (fun i : Fin n => p (MvPolynomial.X i))) := fun x => by
    obtain ⟨y, hy⟩ := hp x
    exact ⟨y, (congrArg (fun φ => φ y) (MvPolynomial.aeval_unique p)).symm.trans hy⟩
  have key : ∀ β : Generators B C (Fin n),
      Function.Injective (nlExtensionBaseChangeMap (T := C) hom).onH₁ := fun β => by
    -- Stacks 07D4: the degree-`1` component of the comparison for `β.comp α` is injective.
    have h07D4 : Function.Injective
        ((Extension.Cotangent.map (β.toComp (Generators.self A B)).toExtensionHom).liftBaseChange
          C) :=
      RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection
        (Generators.self A B) β h
    -- hence it is injective on `H₁`, `H₁` being a submodule of the degree-`1` term.
    have hinj₁ : Function.Injective (nlExtensionBaseChangeMap (T := C)
        (β.toComp (Generators.self A B)).toExtensionHom).onH₁ := fun x y hxy =>
      Subtype.ext (h07D4 (congrArg Subtype.val hxy))
    -- the comparison of `β.comp α` with the canonical presentation of `C` over `A`.
    have hjq : IsQuasiIso (nlExtensionMap
        (Generators.defaultHom (β.comp (Generators.self A B))
          (Generators.self A C)).toExtensionHom) :=
      nlExtensionMap_isQuasiIso _
        (Generators.defaultHom (Generators.self A C)
          (β.comp (Generators.self A B))).toExtensionHom
    have hinj₂ : Function.Injective (nlExtensionBaseChangeMap (T := C)
        (((Generators.defaultHom (β.comp (Generators.self A B))
            (Generators.self A C)).toExtensionHom).comp
          (β.toComp (Generators.self A B)).toExtensionHom)).onH₁ := by
      rw [← nlExtensionOverMap_comp_nlExtensionBaseChangeMap
        (β.toComp (Generators.self A B)).toExtensionHom
        (Generators.defaultHom (β.comp (Generators.self A B))
          (Generators.self A C)).toExtensionHom]
      intro x y hxy
      simp only [ChainMap.onH₁_comp, LinearMap.comp_apply] at hxy
      exact hinj₁ (hjq.1.injective hxy)
    rw [ChainMap.onH₁_eq_of_homotopic (homotopic_nlExtensionBaseChangeMap (T := C) hom
      ((((Generators.defaultHom (β.comp (Generators.self A B))
          (Generators.self A C)).toExtensionHom).comp
        (β.toComp (Generators.self A B)).toExtensionHom)))]
    exact hinj₂
  exact key (Generators.ofSurjective (fun i : Fin n => p (MvPolynomial.X i)) hsurj)

end Affine

/-! ### The localized statement -/

section AtPrime

section Compose

variable {S : Type*} [CommRing S] {A B D : TwoTerm S}

/-- A composite of chain maps injective on `H₁` is injective on `H₁`. -/
private theorem injective_onH₁_comp {g : ChainMap B D} {f : ChainMap A B}
    (hg : Function.Injective g.onH₁) (hf : Function.Injective f.onH₁) :
    Function.Injective (g.comp f).onH₁ := by
  intro x y hxy
  simp only [ChainMap.onH₁_comp, LinearMap.comp_apply] at hxy
  exact hf (hg hxy)

/-- If a composite is injective on `H₁` and its first factor is surjective on `H₁`, the second
factor is injective on `H₁`. -/
private theorem injective_onH₁_of_comp {g : ChainMap B D} {f : ChainMap A B}
    (hgf : Function.Injective (g.comp f).onH₁) (hf : Function.Surjective f.onH₁) :
    Function.Injective g.onH₁ := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := hf x
  obtain ⟨y', rfl⟩ := hf y
  refine congrArg f.onH₁ (hgf ?_)
  simp only [ChainMap.onH₁_comp, LinearMap.comp_apply]
  exact hxy

end Compose

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {A' B' C' : Type u} [CommRing A'] [CommRing B'] [CommRing C']
  [Algebra A A'] [Algebra B B'] [Algebra C C']
  [Algebra A' B'] [Algebra A' C'] [Algebra B' C']
  [Algebra A B'] [Algebra A C'] [Algebra B C']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [IsScalarTower A A' C']
  [IsScalarTower A C C'] [IsScalarTower B B' C'] [IsScalarTower B C C']
  [IsScalarTower A B C']

/-- **Injectivity on `H₁` of the Jacobi-Zariski comparison for a local complete intersection,
after localization.**  Let `A → B → C` be ring maps with `B → C` a local complete intersection
homomorphism, and let `A'`, `B'`, `C'` be localizations of `A`, `B`, `C` at multiplicative
subsets, in a tower compatible with `A → B → C`.  Then the canonical map of two-term complexes of
`C'`-modules

`NL_{B'/A'} ⊗_{B'} C' ⟶ NL_{C'/A'}`

is injective on `H₁`.

The hypothesis is on `B → C`, not on `B' → C'`: the localized map is not of finite type, so
Stacks 07D4 says nothing about it directly.  The statement holds for every morphism of extensions
inducing the comparison, any two being homotopic.

In the geometric application `A`, `B`, `C` are the sections of `𝒪_Z`, `𝒪_Y`, `𝒪_X` over affine
opens `W`, `U`, `V` with `f(V) ⊆ U` and `g(U) ⊆ W`, and `A'`, `B'`, `C'` are the stalks at a
point of `V` of the three sheaves of rings `f^{-1}g^{-1}𝒪_Z ⟶ f^{-1}𝒪_Y ⟶ 𝒪_X` of
Stacks 0E1Z; the three multiplicative subsets are the complements of the three primes of the
point. -/
theorem injective_onH₁_nlExtensionBaseChangeMap_of_isLocalization_of_lci
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap B C))
    (N : Submonoid A) [IsLocalization N A']
    (M : Submonoid B) [IsLocalization M B']
    (L : Submonoid C) [IsLocalization L C']
    (hom : (Generators.self A' B').toExtension.Hom (Generators.self A' C').toExtension) :
    Function.Injective (nlExtensionBaseChangeMap (T := C') hom).onH₁ := by
  classical
  have hflatC : Module.Flat C C' := IsLocalization.flat C' L
  set P₀ := (Generators.self A B).toExtension with hP₀
  set hBC := (Generators.defaultHom (Generators.self A B)
    (Generators.self A C)).toExtensionHom with hBCdef
  set hCC' := (Generators.defaultHom (Generators.self A C)
    (Generators.self A' C')).toExtensionHom with hCC'def
  set hBB' := (Generators.defaultHom (Generators.self A B)
    (Generators.self A' B')).toExtensionHom with hBB'def
  -- Stacks 07D4 at the un-localized tower, on `H₁`.
  have h₁ : Function.Injective (nlExtensionBaseChangeMap (T := C) hBC).onH₁ :=
    injective_onH₁_nlExtensionBaseChangeMap_of_isLocalCompleteIntersection hlci hBC
  -- base changed along the flat map `C → C'`.
  have h₂ : Function.Injective
      ((nlExtensionBaseChangeMap (T := C) hBC).baseChange C').onH₁ :=
    injective_onH₁_baseChange_of_flat C' h₁
  -- the localization comparison `NL_{C/A} ⊗_C C' ⟶ NL_{C'/A'}` is a quasi-isomorphism.
  have hqC : IsQuasiIso (nlExtensionBaseChangeMap (T := C') hCC') :=
    isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization_of_isLocalization L N hCC'
  -- hence `NL_{B/A} ⊗_B C' ⟶ NL_{C'/A'}` is injective on `H₁`.
  have h₃ : Function.Injective
      (nlExtensionBaseChangeMap (T := C') (hCC'.comp hBC)).onH₁ := by
    refine injective_onH₁_of_comp (f := cancelBaseChangeChainMap (D := C) (C := C') P₀) ?_
      (isQuasiIso_cancelBaseChangeChainMap (D := C) (C := C') P₀).1.surjective
    rw [nlExtensionBaseChangeMap_comp_cancelBaseChangeChainMap P₀ (D := C) (C := C') hBC hCC']
    exact injective_onH₁_comp hqC.1.injective h₂
  -- the localization comparison `NL_{B/A} ⊗_B B' ⟶ NL_{B'/A'}` is a quasi-isomorphism, so its
  -- base change along the (not flat) map `B' → C'` is surjective on `H₁`.
  have hqB : IsQuasiIso (nlExtensionBaseChangeMap (T := B') hBB') :=
    isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization_of_isLocalization M N hBB'
  have hsurj : Function.Surjective
      ((nlExtensionBaseChangeMap (T := B') hBB').baseChange C').onH₁ :=
    IsQuasiIso.surjective_onH₁_baseChange C' hqB
  -- the same map, factored through `NL_{B'/A'} ⊗_{B'} C'`.
  have hinj' : Function.Injective
      ((nlExtensionBaseChangeMap (T := C') hom).comp
        ((nlExtensionBaseChangeMap (T := B') hBB').baseChange C')).onH₁ := by
    rw [← nlExtensionBaseChangeMap_comp_cancelBaseChangeChainMap P₀ (D := B') (C := C') hBB' hom]
    refine injective_onH₁_comp ?_
      (isQuasiIso_cancelBaseChangeChainMap (D := B') (C := C') P₀).1.injective
    rw [ChainMap.onH₁_eq_of_homotopic
      (homotopic_nlExtensionBaseChangeMap (T := C') (hom.comp hBB') (hCC'.comp hBC))]
    exact h₃
  exact injective_onH₁_of_comp hinj' hsurj

end AtPrime

end NaiveCotangent

end
