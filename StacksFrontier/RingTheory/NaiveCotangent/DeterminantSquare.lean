module

public import StacksFrontier.RingTheory.NaiveCotangent.DeterminantLine
public import StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermFlatBaseChange
public import StacksFrontier.RingTheory.TateMap.DetNLBaseChange
public import StacksFrontier.RingTheory.TateMap.DetTransport

/-!
# The determinant of the naive cotangent complex along a square of rings

Consider a commutative square of rings

```
B ──→ B'
↑      ↑
A ──→ A'
```

for which the canonical comparison `NL_{B/A} ⊗_B B' ⟶ NL_{B'/A'}` is a quasi-isomorphism: a
*good square*. This holds when `A → A'` and `B → B'` are localizations (Stacks 00S7, 07BS), and
when `A → B` is flat and `B'` is a localization of `A' ⊗_A B` (Stacks 0FJU, 00S7). For a finite
presentation `P` of `B` over `A` with finite projective conormal module the base change
`NL(P) ⊗_B B'` is then a two-term presentation of `NL_{B'/A'}` by finite projective modules.

## Main definitions

* `NaiveCotangent.IsGoodSquare`: the comparison of naive cotangent complexes along the square is
  a quasi-isomorphism.
* `NaiveCotangent.baseChangeTwoTerm P P' h`: the two-term presentation `NL(P) ⊗_B B'` of
  `NL_{B'/A'}`, read through a presentation `P'` of `B'` over `A'` and a morphism of extensions
  `h : P → P'` over the square.

## Main results

* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare`: over a good square the
  comparison `NL(P) ⊗_B B' ⟶ NL(P')` is a quasi-isomorphism for all presentations `P`, `P'` and
  every morphism of extensions `h : P → P'`.
* `NaiveCotangent.baseChangeTwoTerm_iso_eq`: the identification `NL(P) ⊗_B B' ≅ NL_{B'/A'}` in
  `D(B')` does not depend on `P'` and `h`.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 00S7](https://stacks.math.columbia.edu/tag/00S7)
* [Stacks Project, Tag 0FJU](https://stacks.math.columbia.edu/tag/0FJU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra

namespace NaiveCotangent

universe u

attribute [local instance] HasDerivedCategory.standard

section Composites

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {R' T : Type*} [CommRing R'] [CommRing T] [Algebra R' T] [Algebra S T]
  [Algebra R R'] [Algebra R T] [IsScalarTower R R' T] [IsScalarTower R S T]

omit [IsScalarTower R S T] in
/-- The base change of the map on conormal modules along a composite of morphisms of extensions
factors through the map along the second one. -/
theorem cotangentMap_comp_liftBaseChange {P : Extension R S} {Q Q' : Extension R' T}
    (h : P.Hom Q) (φ : Q.Hom Q') :
    Extension.Cotangent.map φ ∘ₗ (Extension.Cotangent.map h).liftBaseChange T =
      (Extension.Cotangent.map (φ.comp h)).liftBaseChange T := by
  rw [LinearMap.liftBaseChange_comp, ← Extension.Cotangent.map_comp]

omit [IsScalarTower R S T] in
/-- The base change of the map on cotangent spaces along a composite of morphisms of extensions
factors through the map along the second one. -/
theorem cotangentSpaceMap_comp_liftBaseChange {P : Extension R S} {Q Q' : Extension R' T}
    (h : P.Hom Q) (φ : Q.Hom Q') :
    Extension.CotangentSpace.map φ ∘ₗ (Extension.CotangentSpace.map h).liftBaseChange T =
      (Extension.CotangentSpace.map (φ.comp h)).liftBaseChange T := by
  rw [LinearMap.liftBaseChange_comp, ← Extension.CotangentSpace.map_comp]

omit [IsScalarTower R S T] in
/-- The comparison along a morphism of extensions followed by a morphism of extensions of the
target is the comparison along the composite. -/
theorem nlExtensionBaseChangeMap_comp_left {P : Extension R S} {Q Q' : Extension R' T}
    (h : P.Hom Q) (φ : Q.Hom Q') :
    (nlExtensionMap φ).comp (nlExtensionBaseChangeMap (T := T) h) =
      nlExtensionBaseChangeMap (T := T) (φ.comp h) :=
  ChainMap.ext (cotangentMap_comp_liftBaseChange h φ) (cotangentSpaceMap_comp_liftBaseChange h φ)

/-- Precomposing `liftBaseChange` with a `baseChange` is `liftBaseChange` of the composite. -/
private theorem liftBaseChange_comp_baseChange {M₀ M N : Type*} [AddCommGroup M₀] [AddCommGroup M]
    [AddCommGroup N] [Module S M₀] [Module S M] [Module S N] [Module T N]
    [IsScalarTower S T N] (α : M₀ →ₗ[S] M) (f : M →ₗ[S] N) :
    f.liftBaseChange T ∘ₗ α.baseChange T = (f ∘ₗ α).liftBaseChange T := by
  ext
  simp

omit [IsScalarTower R S T] in
/-- Precomposing the base change of the map on conormal modules with the base change of a map
of extensions of the source. -/
theorem liftBaseChange_cotangentMap_comp_baseChange {P₀ P : Extension R S} {Q : Extension R' T}
    (α : P₀.Hom P) (h : P.Hom Q) :
    (Extension.Cotangent.map h).liftBaseChange T ∘ₗ
        LinearMap.baseChange T (Extension.Cotangent.map α) =
      (Extension.Cotangent.map (h.comp α)).liftBaseChange T := by
  rw [liftBaseChange_comp_baseChange]
  exact congrArg _ (Extension.Cotangent.map_comp _ α h).symm

omit [IsScalarTower R S T] in
/-- Precomposing the base change of the map on cotangent spaces with the base change of a map
of extensions of the source. -/
theorem liftBaseChange_cotangentSpaceMap_comp_baseChange {P₀ P : Extension R S}
    {Q : Extension R' T} (α : P₀.Hom P) (h : P.Hom Q) :
    (Extension.CotangentSpace.map h).liftBaseChange T ∘ₗ
        LinearMap.baseChange T (Extension.CotangentSpace.map α) =
      (Extension.CotangentSpace.map (h.comp α)).liftBaseChange T := by
  rw [liftBaseChange_comp_baseChange]
  exact congrArg _ (Extension.CotangentSpace.map_comp α h).symm

omit [IsScalarTower R S T] in
/-- A morphism of extensions of the source followed by the comparison is the comparison along
the composite. -/
theorem nlExtensionBaseChangeMap_comp_right {P₀ P : Extension R S} {Q : Extension R' T}
    (α : P₀.Hom P) (h : P.Hom Q) :
    (nlExtensionBaseChangeMap (T := T) h).comp ((nlExtensionMap α).baseChange T) =
      nlExtensionBaseChangeMap (T := T) (h.comp α) :=
  ChainMap.ext (liftBaseChange_cotangentMap_comp_baseChange α h)
    (liftBaseChange_cotangentSpaceMap_comp_baseChange α h)

/-- The comparison `NL(P) ⊗_S T ⟶ NL(Q)` along a morphism of extensions, with its source written
as the base change `(nlOfExtension P).baseChange T` of the naive cotangent complex of `P`. It is
`NaiveCotangent.nlExtensionBaseChangeMap`, whose source is the same complex by definition. -/
abbrev nlBaseChangeMap {P : Extension R S} {Q : Extension R' T} (h : P.Hom Q) :
    ChainMap ((nlOfExtension P).baseChange T) (nlOfExtension Q) :=
  nlExtensionBaseChangeMap (T := T) h

omit [IsScalarTower R S T] in
/-- Composing the comparison `NL(P) ⊗_S T ⟶ NL(Q)` with the map induced by `Q ⟶ Q'`. -/
theorem nlBaseChangeMap_comp_left {P : Extension R S} {Q Q' : Extension R' T}
    (h : P.Hom Q) (φ : Q.Hom Q') :
    (nlExtensionMap φ).comp (nlBaseChangeMap (T := T) h) = nlBaseChangeMap (T := T) (φ.comp h) :=
  nlExtensionBaseChangeMap_comp_left h φ

omit [IsScalarTower R S T] in
/-- Precomposing the comparison `NL(P) ⊗_S T ⟶ NL(Q)` with the base change of the map induced by
`P₀ ⟶ P`. -/
theorem nlBaseChangeMap_comp_right {P₀ P : Extension R S} {Q : Extension R' T}
    (α : P₀.Hom P) (h : P.Hom Q) :
    (nlBaseChangeMap (T := T) h).comp ((nlExtensionMap α).baseChange T) =
      nlBaseChangeMap (T := T) (h.comp α) :=
  nlExtensionBaseChangeMap_comp_right α h

/-- Any two morphisms of extensions induce homotopic comparison maps. -/
theorem homotopic_nlBaseChangeMap {P : Extension R S} {Q : Extension R' T} (h h' : P.Hom Q) :
    Homotopic (nlBaseChangeMap (T := T) h) (nlBaseChangeMap (T := T) h') :=
  homotopic_nlExtensionBaseChangeMap h h'

end Composites

section ThreeSquares

open TensorProduct

variable {A B A' B' A'' B'' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A' B'] [Algebra A'' B'']
  [Algebra A A'] [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A'']
  [Algebra B B'] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
  [Algebra A B'] [Algebra A' B''] [Algebra A B'']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [IsScalarTower A' A'' B'']
  [IsScalarTower A' B' B''] [IsScalarTower A A'' B''] [IsScalarTower A B B'']

/-- Cancelling the intermediate base change `(NL(P) ⊗_B B') ⊗_{B'} B'' ≅ NL(P) ⊗_B B''`. -/
def cancelBaseChangeTwoTerm (P : Extension A B) :
    ChainMap (((nlOfExtension P).baseChange B').baseChange B'')
      ((nlOfExtension P).baseChange B'') :=
  cancelBaseChangeChainMap (D := B') (C := B'') P

omit [Algebra A B'] [Algebra A B''] [IsScalarTower A B B'] [IsScalarTower A B B''] in
/-- The cancellation of the intermediate base change is bijective in degree `-1`. -/
theorem cancelBaseChangeTwoTerm_f₁_bijective (P : Extension A B) :
    Function.Bijective (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P).f₁ :=
  (AlgebraTensorModule.cancelBaseChange B B' B'' B'' P.Cotangent).bijective

omit [Algebra A B'] [Algebra A B''] [IsScalarTower A B B'] [IsScalarTower A B B''] in
/-- The cancellation of the intermediate base change is bijective in degree `0`. -/
theorem cancelBaseChangeTwoTerm_f₀_bijective (P : Extension A B) :
    Function.Bijective (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P).f₀ :=
  (AlgebraTensorModule.cancelBaseChange B B' B'' B'' P.CotangentSpace).bijective

omit [IsScalarTower A B B'] [IsScalarTower A' B' B''] [IsScalarTower A B B''] in
/-- **The comparison of naive cotangent complexes along a composite of two squares**: the
comparison along the second square after the base change of the comparison along the first is,
after cancelling the intermediate base change, the comparison along the composite. -/
theorem nlBaseChangeMap_comp_baseChange (P : Extension A B) (P' : Extension A' B')
    (P'' : Extension A'' B'') (h : P.Hom P') (k : P'.Hom P'') :
    (nlBaseChangeMap (T := B'') k).comp ((nlBaseChangeMap (T := B') h).baseChange B'') =
      (nlBaseChangeMap (T := B'') (k.comp h)).comp (cancelBaseChangeTwoTerm P) := by
  refine ChainMap.ext (LinearMap.ext fun z => ?_) (LinearMap.ext fun z => ?_)
  · exact (liftBaseChange_cancelBaseChange (Extension.Cotangent.map h)
      (Extension.Cotangent.map k) (Extension.Cotangent.map (k.comp h))
      (fun m => congrArg (fun l => l m) (Extension.Cotangent.map_comp _ h k)) z).symm
  · exact (liftBaseChange_cancelBaseChange (Extension.CotangentSpace.map h)
      (Extension.CotangentSpace.map k) (Extension.CotangentSpace.map (k.comp h))
      (fun m => Extension.CotangentSpace.map_comp_apply h k m) z).symm

end ThreeSquares

/-! ### Good squares -/

section Square

variable (A B A' B' : Type u) [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- A commutative square of rings is *good* when the canonical comparison
`NL_{B/A} ⊗_B B' ⟶ NL_{B'/A'}` of naive cotangent complexes is a quasi-isomorphism, for every
morphism of the canonical presentations inducing it (any two induce homotopic maps). -/
def IsGoodSquare : Prop :=
  ∀ h : (Generators.self A B).toExtension.Hom (Generators.self A' B').toExtension,
    IsQuasiIso (nlBaseChangeMap (T := B') h)

variable {A B A' B'}

/-- Over a good square, the comparison `NL(P) ⊗_B B' ⟶ NL(P')` is a quasi-isomorphism for all
extensions `P` of `B` over `A` and `P'` of `B'` over `A'` admitting morphisms to the canonical
presentations, and every morphism of extensions over the square. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare (hsq : IsGoodSquare A B A' B')
    (P : Extension.{u} A B) (P' : Extension.{u} A' B')
    (ψ : P.Hom (Generators.self A B).toExtension) (ψ' : P'.Hom (Generators.self A' B').toExtension)
    (h : P.Hom P') :
    IsQuasiIso (nlBaseChangeMap (T := B') h) := by
  let hcan := ((Generators.self A B).defaultHom (Generators.self A' B')).toExtensionHom
  have h₁ : IsQuasiIso (nlBaseChangeMap (T := B') (hcan.comp ψ)) := by
    rw [← nlBaseChangeMap_comp_right]
    exact (hsq hcan).comp (isQuasiIso_of_isHomotopyEquiv
      ((nlExtensionMap_isHomotopyEquiv ψ (Extension.defaultHom A B P)).baseChange B'))
  have h₂ : IsQuasiIso (nlBaseChangeMap (T := B') (ψ'.comp h)) :=
    isQuasiIso_nlExtensionBaseChangeMap_congr _ _ h₁
  rw [← nlBaseChangeMap_comp_left] at h₂
  exact Stacks.TateMap.TwoTermHomotopy.isQuasiIso_of_comp (isQuasiIso_of_isHomotopyEquiv
    (nlExtensionMap_isHomotopyEquiv ψ' (Extension.defaultHom A' B' P'))) h₂

/-- The comparison `NL(P) ⊗_B B' ⟶ NL(P')` over a good square is an isomorphism in `D(B')`. -/
theorem isIso_Q_map_nlExtensionBaseChangeMap (hsq : IsGoodSquare A B A' B')
    (P : Extension.{u} A B) (P' : Extension.{u} A' B')
    (ψ : P.Hom (Generators.self A B).toExtension) (ψ' : P'.Hom (Generators.self A' B').toExtension)
    (h : P.Hom P') :
    IsIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom
      (nlBaseChangeMap (T := B') h))) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (Stacks.TwoTermDoubleQuasiIso.quasiIso_mapDouble ComplexShape.upIntRelNegOneZero
      (isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare hsq P P' ψ ψ' h))

/-- The base-changed two-term complex `NL(P) ⊗_B B'` of an extension, in degrees `-1`, `0`. -/
abbrev baseChangeComplex (P : Extension.{u} A B) : CochainComplex (ModuleCat.{u} B') ℤ :=
  Deformation.Artin.twoTermComplex ((nlOfExtension P).baseChange B')

/-- **The identification `NL_{B'/A'} ≅ NL(P) ⊗_B B'` in `D(B')`** over a good square, read
through an extension `P'` of `B'` over `A'` and a morphism of extensions `h : P → P'`. -/
def baseChangeIso (hsq : IsGoodSquare A B A' B') (P : Extension.{u} A B)
    (P' : Extension.{u} A' B') (ψ : P.Hom (Generators.self A B).toExtension)
    (ψ' : P'.Hom (Generators.self A' B').toExtension) (h : P.Hom P') :
    naiveCotangentObject A' B' ≅ DerivedCategory.Q.obj (baseChangeComplex (B' := B') P) :=
  haveI := isIso_Q_map_nlExtensionBaseChangeMap hsq P P' ψ ψ' h
  extensionIso P' ψ' ≪≫ (asIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom
    (nlBaseChangeMap (T := B') h)))).symm

/-- The identification `NL_{B'/A'} ≅ NL(P) ⊗_B B'` does not depend on the extension of `B'` nor
on the morphism of extensions used to define it. -/
theorem baseChangeIso_eq (hsq : IsGoodSquare A B A' B') (P : Extension.{u} A B)
    (P₁ P₂ : Extension.{u} A' B') (ψ : P.Hom (Generators.self A B).toExtension)
    (ψ₁ : P₁.Hom (Generators.self A' B').toExtension)
    (ψ₂ : P₂.Hom (Generators.self A' B').toExtension)
    (h₁ : P.Hom P₁) (h₂ : P.Hom P₂) :
    baseChangeIso hsq P P₁ ψ ψ₁ h₁ = baseChangeIso hsq P P₂ ψ ψ₂ h₂ := by
  let φ := (Extension.defaultHom A' B' P₂).comp ψ₁
  have := isIso_Q_map_nlExtensionBaseChangeMap hsq P P₁ ψ ψ₁ h₁
  have := isIso_Q_map_nlExtensionBaseChangeMap hsq P P₂ ψ ψ₂ h₂
  have hQ : DerivedCategory.Q.map (Deformation.Artin.twoTermHom
        (nlBaseChangeMap (T := B') h₂)) =
      DerivedCategory.Q.map (Deformation.Artin.twoTermHom
        (nlBaseChangeMap (T := B') h₁)) ≫
        DerivedCategory.Q.map (extensionComplexMap φ) := by
    rw [← Functor.map_comp, ← Deformation.Artin.twoTermHom_comp, nlBaseChangeMap_comp_left]
    exact Deformation.Artin.Q_map_twoTermHom_eq_of_homotopic
      (homotopic_nlBaseChangeMap _ _)
  apply Iso.ext
  simp only [baseChangeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [extensionIso_hom_eq P₁ P₂ ψ₁ ψ₂ φ, Category.assoc]
  congr 1
  rw [IsIso.eq_comp_inv, IsIso.inv_comp_eq, hQ]

end Square

/-! ### A surjective span for a quasi-isomorphism of two-term complexes

A quasi-isomorphism `g : C ⟶ D` of two-term complexes is the "quotient" of two surjective ones:
with `S = C ⊕ (D₁ = D₁)`, the projection `S ⟶ C` and the map `S ⟶ D` given by `g` on `C` and by
`(id, d)` on `D₁ = D₁` are degreewise surjective quasi-isomorphisms, and the second is homotopic
to `g` composed with the first. -/

section Span

variable {S : Type*} [CommRing S] {C D : TwoTerm S} (g : ChainMap C D)

/-- The middle term `C ⊕ (D₁ = D₁)` of the surjective span of a chain map `g : C ⟶ D`. -/
abbrev spanTwoTerm (C D : TwoTerm S) : TwoTerm S where
  X₁ := C.X₁ × D.X₁
  X₀ := C.X₀ × D.X₁
  d := LinearMap.prodMap C.d LinearMap.id

/-- The projection `C ⊕ (D₁ = D₁) ⟶ C`. -/
def spanLeft (C D : TwoTerm S) : ChainMap (spanTwoTerm C D) C where
  f₁ := LinearMap.fst S C.X₁ D.X₁
  f₀ := LinearMap.fst S C.X₀ D.X₁
  comm := by ext x <;> rfl

/-- The map `C ⊕ (D₁ = D₁) ⟶ D`, `(c, y) ↦ g(c) + (y, d y)`. -/
def spanRight : ChainMap (spanTwoTerm C D) D where
  f₁ := g.f₁ ∘ₗ LinearMap.fst S C.X₁ D.X₁ + LinearMap.snd S C.X₁ D.X₁
  f₀ := g.f₀ ∘ₗ LinearMap.fst S C.X₀ D.X₁ + D.d ∘ₗ LinearMap.snd S C.X₀ D.X₁
  comm := by
    ext x
    · simp
    · simp

/-- The left leg of the span is surjective in degree `-1`. -/
theorem spanLeft_surjective₁ (C D : TwoTerm S) : Function.Surjective (spanLeft C D).f₁ :=
  fun c => ⟨(c, 0), rfl⟩

/-- The left leg of the span is surjective in degree `0`. -/
theorem spanLeft_surjective₀ (C D : TwoTerm S) : Function.Surjective (spanLeft C D).f₀ :=
  fun c => ⟨(c, 0), rfl⟩

/-- The right leg of the span is surjective in degree `-1`. -/
theorem spanRight_surjective₁ : Function.Surjective (spanRight g).f₁ :=
  fun y => ⟨(0, y), by simp [spanRight]⟩

/-- The right leg of the span of a quasi-isomorphism is surjective in degree `0`. -/
theorem spanRight_surjective₀ (hg : IsQuasiIso g) : Function.Surjective (spanRight g).f₀ := by
  intro z
  obtain ⟨w, hw⟩ := hg.2.2 (Submodule.Quotient.mk z)
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hc : Submodule.Quotient.mk (p := LinearMap.range D.d) (g.f₀ c) =
      Submodule.Quotient.mk z := hw
  rw [Submodule.Quotient.eq] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨(c, -y), ?_⟩
  simp only [spanRight, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, map_neg, hy]
  abel

/-- The projection `C ⊕ (D₁ = D₁) ⟶ C` is a homotopy equivalence. -/
theorem spanLeft_isHomotopyEquiv (C D : TwoTerm S) : IsHomotopyEquiv (spanLeft C D) := by
  let incl : ChainMap C (spanTwoTerm C D) :=
    { f₁ := LinearMap.inl S C.X₁ D.X₁
      f₀ := LinearMap.inl S C.X₀ D.X₁
      comm := by ext x <;> simp }
  refine ⟨incl, ⟨-(LinearMap.inr S C.X₁ D.X₁ ∘ₗ LinearMap.snd S C.X₀ D.X₁), ?_, ?_⟩,
    ⟨0, ?_, ?_⟩⟩ <;> ext x <;> simp [incl, spanLeft, ChainMap.comp, ChainMap.id]

/-- The map `C ⊕ (D₁ = D₁) ⟶ D` is homotopic to `g` composed with the projection. -/
theorem spanRight_homotopic : Homotopic (spanRight g) (g.comp (spanLeft C D)) :=
  ⟨LinearMap.snd S C.X₀ D.X₁, by ext x <;> simp [spanRight, spanLeft, ChainMap.comp],
    by ext x <;> simp [spanRight, spanLeft, ChainMap.comp]⟩

/-- The map `C ⊕ (D₁ = D₁) ⟶ D` is a quasi-isomorphism when `g` is. -/
theorem spanRight_isQuasiIso (hg : IsQuasiIso g) : IsQuasiIso (spanRight g) := by
  have h := hg.comp (isQuasiIso_of_isHomotopyEquiv (spanLeft_isHomotopyEquiv C D))
  refine ⟨?_, ?_⟩
  · rw [ChainMap.onH₁_eq_of_homotopic (spanRight_homotopic g)]
    exact h.1
  · rw [ChainMap.onH₀_eq_of_homotopic (spanRight_homotopic g)]
    exact h.2

end Span

end NaiveCotangent

end
