module

public import StacksFrontier.RingTheory.NaiveCotangent.DeterminantTransport

/-!
# The determinant of the naive cotangent complex along a good square

Let `B` be a syntomic `A`-algebra and consider a commutative square of rings `A → A'`,
`B → B'` with `B'` syntomic over `A'` which is *good* for the naive cotangent complex
(`NaiveCotangent.IsGoodSquare`: the comparison `NL_{B/A} ⊗_B B' ⟶ NL_{B'/A'}` is a
quasi-isomorphism). Then the determinant of the comparison gives a canonical semilinear map
`det(NL_{B/A}) → det(NL_{B'/A'})` which induces `B' ⊗_B det(NL_{B/A}) ≅ det(NL_{B'/A'})`
(More on Algebra, Section 0FJI, and Derived Categories of Schemes, Remark 0FJY, at the level of
rings).

It is computed from any extension `P` of `B` over `A` with finite projective naive cotangent
complex (for instance a finite presentation): `det(NL_{B/A})` is the determinant line of `NL(P)`
(`NaiveCotangent.detNLEquiv`), `det(NL_{B'/A'})` is the determinant line of `NL(P) ⊗_B B'`
(`NaiveCotangent.detNLBaseChangeEquiv`), and the map is the base change of determinant lines.
The result does not depend on `P`.

## Main definitions

* `NaiveCotangent.detNLEquiv P ψ`: `det(NL_{B/A}) ≅ det(NL(P))`.
* `NaiveCotangent.detNLBaseChangeEquiv hsq P ψ`: `det(NL_{B'/A'}) ≅ det(NL(P) ⊗_B B')`.
* `NaiveCotangent.detNLMapOf hsq P ψ`: the base change map computed through `P`.
* `NaiveCotangent.detNLMap hsq`: the base change map `det(NL_{B/A}) → det(NL_{B'/A'})`.
* `NaiveCotangent.detNLBaseChangeLinearEquiv hsq`: `B' ⊗_B det(NL_{B/A}) ≅ det(NL_{B'/A'})`.

## Main results

* `NaiveCotangent.detNLEquiv_apply_of_hom`: the identifications for two extensions differ by
  the transport of determinant lines along the comparison of their naive cotangent complexes.
* `NaiveCotangent.detNLMap_eq`: the base change map does not depend on the extension.
* `NaiveCotangent.detNLMap_deltaNL`: it carries `δ(NL_{B/A})` to `δ(NL_{B'/A'})`.
* `NaiveCotangent.detNLMap_detNLMap`: base change maps compose along composites of good squares.
* `NaiveCotangent.IsGoodSquare.trans`: good squares of syntomic algebras compose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra TwoTermDeterminant
open scoped TensorProduct

namespace NaiveCotangent

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Finiteness of the terms of `NL(P)` -/

section Instances

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (P : Extension.{u} R S)

/-- The conormal term of `NL(P)` is finite when the conormal module is. -/
instance [Module.Finite S P.Cotangent] : Module.Finite S (nlOfExtension P).X₁ :=
  ‹Module.Finite S P.Cotangent›

/-- The conormal term of `NL(P)` is projective when the conormal module is. -/
instance [Module.Projective S P.Cotangent] : Module.Projective S (nlOfExtension P).X₁ :=
  ‹Module.Projective S P.Cotangent›

/-- The cotangent term of `NL(P)` is finite when the cotangent space is. -/
instance [Module.Finite S P.CotangentSpace] : Module.Finite S (nlOfExtension P).X₀ :=
  ‹Module.Finite S P.CotangentSpace›

/-- The cotangent term of `NL(P)` is projective when the cotangent space is. -/
instance [Module.Projective S P.CotangentSpace] : Module.Projective S (nlOfExtension P).X₀ :=
  ‹Module.Projective S P.CotangentSpace›

variable (T : Type u) [CommRing T] [Algebra S T]

/-- The conormal term of `NL(P) ⊗_S T` is finite. -/
instance [Module.Finite S P.Cotangent] : Module.Finite T (nlExtensionBaseChange P T).X₁ :=
  inferInstanceAs (Module.Finite T (T ⊗[S] P.Cotangent))

/-- The conormal term of `NL(P) ⊗_S T` is projective. -/
instance [Module.Projective S P.Cotangent] : Module.Projective T (nlExtensionBaseChange P T).X₁ :=
  inferInstanceAs (Module.Projective T (T ⊗[S] P.Cotangent))

/-- The cotangent term of `NL(P) ⊗_S T` is finite. -/
instance [Module.Finite S P.CotangentSpace] : Module.Finite T (nlExtensionBaseChange P T).X₀ :=
  inferInstanceAs (Module.Finite T (T ⊗[S] P.CotangentSpace))

/-- The cotangent term of `NL(P) ⊗_S T` is projective. -/
instance [Module.Projective S P.CotangentSpace] :
    Module.Projective T (nlExtensionBaseChange P T).X₀ :=
  inferInstanceAs (Module.Projective T (T ⊗[S] P.CotangentSpace))

end Instances

/-! ### Transport along a degreewise-surjective quasi-isomorphism -/

section TransportSurjective

variable {S : Type u} [CommRing S] {C D : TwoTerm.{u, u, u} S}
  [Module.Finite S C.X₁] [Module.Projective S C.X₁] [Module.Finite S C.X₀]
  [Module.Projective S C.X₀]
  [Module.Finite S D.X₁] [Module.Projective S D.X₁] [Module.Finite S D.X₀]
  [Module.Projective S D.X₀]

/-- Along a degreewise-surjective quasi-isomorphism, `detTransport` is the equivalence of
Stacks 0FJJ. -/
theorem detTransport_eq_detEquiv (g : ChainMap C D) (hq : IsQuasiIso g)
    (h₁ : Function.Surjective g.f₁) (h₀ : Function.Surjective g.f₀) :
    detTransport g hq = g.toHom.detEquiv (g.isDegreewiseSurjective_toHom h₁ h₀)
      (ChainMap.isQuasiIso_toHom hq) := by
  ext φ : 1
  rw [detTransport_eq_of_span g hq (ChainMap.id C) g (fun x => ⟨x, rfl⟩) (fun x => ⟨x, rfl⟩)
    (isQuasiIso_of_isHomotopyEquiv ⟨ChainMap.id C, ⟨0, by ext; simp, by ext; simp⟩,
      ⟨0, by ext; simp, by ext; simp⟩⟩) h₁ h₀ hq
    (by rw [Deformation.Artin.twoTermHom_id, CategoryTheory.Functor.map_id, Category.id_comp])]
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  exact TwoTermComplex.Hom.detEquiv_id C.d _ _ ▸ rfl

omit [Module.Finite S C.X₁] [Module.Finite S C.X₀] [Module.Finite S D.X₁] [Module.Finite S D.X₀] in
/-- A quasi-isomorphism of two-term complexes of finite projective modules stays a
quasi-isomorphism after any base change. -/
theorem IsQuasiIso.baseChange_of_finite_projective (T : Type u) [CommRing T] [Algebra S T]
    {g : ChainMap C D} (hq : IsQuasiIso g) : IsQuasiIso (g.baseChange T) := by
  have hl := isQuasiIso_of_isHomotopyEquiv (spanLeft_isHomotopyEquiv C D)
  have hr := spanRight_isQuasiIso g hq
  have hls := (spanLeft C D).isDegreewiseSurjective_toHom (spanLeft_surjective₁ C D)
    (spanLeft_surjective₀ C D)
  have hrs := (spanRight g).isDegreewiseSurjective_toHom (spanRight_surjective₁ g)
    (spanRight_surjective₀ g hq)
  have hl' := ChainMap.isQuasiIso_of_toHom (g := (spanLeft C D).baseChange T)
    ((ChainMap.isQuasiIso_toHom hl).baseChange T hls)
  have hr' := ChainMap.isQuasiIso_of_toHom (g := (spanRight g).baseChange T)
    ((ChainMap.isQuasiIso_toHom hr).baseChange T hrs)
  have hh : Homotopic ((spanRight g).baseChange T) ((g.baseChange T).comp
      ((spanLeft C D).baseChange T)) := by
    rw [← ChainMap.baseChange_comp]
    exact (spanRight_homotopic g).baseChange T
  refine ⟨?_, ?_⟩
  · have e : ((spanRight g).baseChange T).onH₁ =
        (g.baseChange T).onH₁ ∘ₗ ((spanLeft C D).baseChange T).onH₁ := by
      rw [ChainMap.onH₁_eq_of_homotopic hh, ChainMap.onH₁_comp]
    have := hr'.1
    rw [e, LinearMap.coe_comp] at this
    exact (Function.Bijective.of_comp_iff _ hl'.1).mp this
  · have e : ((spanRight g).baseChange T).onH₀ =
        (g.baseChange T).onH₀ ∘ₗ ((spanLeft C D).baseChange T).onH₀ := by
      rw [ChainMap.onH₀_eq_of_homotopic hh, ChainMap.onH₀_comp]
    have := hr'.2
    rw [e, LinearMap.coe_comp] at this
    exact (Function.Bijective.of_comp_iff _ hl'.2).mp this

/-- `detTransport` only depends on the chain map. -/
theorem detTransport_congr {g g' : ChainMap C D} (h : g = g') (hq : IsQuasiIso g)
    (hq' : IsQuasiIso g') : detTransport g hq = detTransport g' hq' := by
  subst h
  rfl

end TransportSurjective

/-! ### The identification with the determinant line of `NL(P)` -/

section Extension

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]

variable (P : Extension.{u} A B) (ψ : P.Hom (Generators.self A B).toExtension)
  [Module.Finite B P.Cotangent] [Module.Projective B P.Cotangent]
  [Module.Finite B P.CotangentSpace] [Module.Projective B P.CotangentSpace]

/-- **`det(NL_{B/A})` is the determinant line of `NL(P)`** for an extension `P` of `B` over `A`
with finite projective naive cotangent complex, admitting a morphism to the canonical
presentation. -/
def detNLEquiv : detNL A B ≃ₗ[B] TwoTermComplex.determinantLine (nlOfExtension P).d :=
  (detPresentationIso (naiveCotangentPerfect A B)
    (ofTwoTerm (nlOfExtension P) (extensionIso P ψ))).trans (doubleEquiv (nlOfExtension P))

/-- The identifications of `det(NL_{B/A})` with the determinant lines of two extensions differ by
the transport of determinant lines along the comparison of their naive cotangent complexes. -/
theorem detNLEquiv_apply_of_hom (P' : Extension.{u} A B)
    (ψ' : P'.Hom (Generators.self A B).toExtension)
    [Module.Finite B P'.Cotangent] [Module.Projective B P'.Cotangent]
    [Module.Finite B P'.CotangentSpace] [Module.Projective B P'.CotangentSpace]
    (φ : P.Hom P') (φ' : P'.Hom P) (x : detNL A B) :
    detNLEquiv P' ψ' x =
      detTransport (nlExtensionMap φ) (nlExtensionMap_isQuasiIso φ φ') (detNLEquiv P ψ x) :=
  doubleEquiv_detPresentationIso_of_isQuasiIso (naiveCotangentPerfect A B) (extensionIso P ψ)
    (extensionIso P' ψ') (nlExtensionMap φ) _ (extensionIso_hom_eq P P' ψ ψ' φ).symm x

/-- Under the identification with the determinant line of a rank-zero `NL(P)`, `δ(NL_{B/A})` is
the canonical element of More on Algebra, Section 0FJI. -/
theorem detNLEquiv_deltaNL [Algebra.QuasiFinite A B]
    (hP : TwoTermComplex.IsRankZero (nlOfExtension P).d) :
    detNLEquiv P ψ (deltaNL A B) = TwoTermComplex.delta (nlOfExtension P).d hP := by
  have h := detPresentationIso_delta (naiveCotangentPerfect A B)
    (ofTwoTerm (nlOfExtension P) (extensionIso P ψ)) (isRankZero_double _ hP)
  simp only [detNLEquiv]
  exact (congrArg (doubleEquiv (nlOfExtension P)) h).trans (doubleEquiv_delta _ hP)

end Extension

/-- A cancellation rule in a category. -/
theorem _root_.CategoryTheory.comp_inv_comp_eq_of_comp_eq {C : Type*} [Category C] {X Y Z W : C}
    (e : X ⟶ W) (b : Y ⟶ W) [IsIso b] (b' : Z ⟶ W) [IsIso b'] (g : Y ⟶ Z) (h : g ≫ b' = b) :
    (e ≫ inv b) ≫ g = e ≫ inv b' := by
  rw [Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq, IsIso.eq_comp_inv, h]

/-! ### The base change map of determinants -/

section Square

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.Syntomic A B] [Algebra.Syntomic A' B']
  (hsq : IsGoodSquare A B A' B')

variable (P : Extension.{u} A B) (ψ : P.Hom (Generators.self A B).toExtension)
  [Module.Finite B P.Cotangent] [Module.Projective B P.Cotangent]
  [Module.Finite B P.CotangentSpace] [Module.Projective B P.CotangentSpace]

/-- The morphism of extensions from `P` to the canonical presentation of `B'` over `A'`, over the
square, through the canonical presentation of `B` over `A`. -/
abbrev squareHom : P.Hom (Generators.self A' B').toExtension :=
  ((Generators.self A B).defaultHom (Generators.self A' B')).toExtensionHom.comp ψ

/-- **`det(NL_{B'/A'})` is the determinant line of `NL(P) ⊗_B B'`** over a good square. -/
def detNLBaseChangeEquiv :
    detNL A' B' ≃ₗ[B'] TwoTermComplex.determinantLine ((nlOfExtension P).baseChange B').d :=
  (detPresentationIso (naiveCotangentPerfect A' B')
    (ofTwoTerm ((nlOfExtension P).baseChange B') (baseChangeIso hsq P
      (Generators.self A' B').toExtension ψ (Extension.Hom.id _) (squareHom P ψ)))).trans
    (doubleEquiv ((nlOfExtension P).baseChange B'))

/-- **The base change map `det(NL_{B/A}) → det(NL_{B'/A'})`** over a good square: the base
change of determinant lines of `NL(P)`, read through the identifications of both sides with
determinant lines. -/
def detNLMapOf : detNL A B →ₛₗ[algebraMap B B'] detNL A' B' :=
  (detNLBaseChangeEquiv hsq P ψ).symm.toLinearMap.comp
    (((nlOfExtension P).detBaseChange B').comp (detNLEquiv P ψ).toLinearMap)

/-- `detNLMapOf` unfolded. -/
theorem detNLMapOf_apply (x : detNL A B) :
    detNLMapOf hsq P ψ x = (detNLBaseChangeEquiv hsq P ψ).symm
      ((nlOfExtension P).detBaseChange B' (detNLEquiv P ψ x)) :=
  rfl

/-- The base change map is semilinear along `B → B'`. -/
theorem detNLMapOf_smul (b : B) (x : detNL A B) :
    detNLMapOf hsq P ψ (b • x) = algebraMap B B' b • detNLMapOf hsq P ψ x :=
  LinearMap.map_smulₛₗ _ b x

omit [Algebra.Syntomic A B] in
/-- The identifications of `det(NL_{B'/A'})` with the determinant lines of `NL(P) ⊗_B B'` and
`NL(Q) ⊗_B B'` differ by the transport along the base change of the comparison of naive
cotangent complexes. -/
theorem detNLBaseChangeEquiv_apply_of_hom (Q : Extension.{u} A B)
    (χ : Q.Hom (Generators.self A B).toExtension)
    [Module.Finite B Q.Cotangent] [Module.Projective B Q.Cotangent]
    [Module.Finite B Q.CotangentSpace] [Module.Projective B Q.CotangentSpace]
    (φ : P.Hom Q) (hq : IsQuasiIso ((nlExtensionMap φ).baseChange B')) (y : detNL A' B') :
    detNLBaseChangeEquiv hsq Q χ y =
      detTransport ((nlExtensionMap φ).baseChange B') hq (detNLBaseChangeEquiv hsq P ψ y) := by
  have := isIso_Q_map_nlExtensionBaseChangeMap hsq P (Generators.self A' B').toExtension ψ
    (Extension.Hom.id _) (squareHom P ψ)
  have := isIso_Q_map_nlExtensionBaseChangeMap hsq Q (Generators.self A' B').toExtension χ
    (Extension.Hom.id _) (squareHom Q χ)
  refine doubleEquiv_detPresentationIso_of_isQuasiIso (naiveCotangentPerfect A' B') _ _
    ((nlExtensionMap φ).baseChange B') hq ?_ y
  have hQ : DerivedCategory.Q.map (Deformation.Artin.twoTermHom
        ((nlExtensionMap φ).baseChange B')) ≫
      DerivedCategory.Q.map (Deformation.Artin.twoTermHom
        (nlBaseChangeMap (T := B') (squareHom (A' := A') (B' := B') Q χ))) =
      DerivedCategory.Q.map (Deformation.Artin.twoTermHom
        (nlBaseChangeMap (T := B') (squareHom (A' := A') (B' := B') P ψ))) := by
    calc _ = DerivedCategory.Q.map (Deformation.Artin.twoTermHom
          ((nlBaseChangeMap (T := B') (squareHom (A' := A') (B' := B') Q χ)).comp
            ((nlExtensionMap φ).baseChange B'))) := by
          rw [← Functor.map_comp, Deformation.Artin.twoTermHom_comp]
      _ = DerivedCategory.Q.map (Deformation.Artin.twoTermHom (nlBaseChangeMap (T := B')
          ((squareHom (A' := A') (B' := B') Q χ).comp φ))) := by
          rw [nlBaseChangeMap_comp_right]
      _ = _ := Deformation.Artin.Q_map_twoTermHom_eq_of_homotopic
          (homotopic_nlBaseChangeMap _ _)
  simp only [baseChangeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  exact comp_inv_comp_eq_of_comp_eq _ _ _ _ hQ

/-- **The base change map does not depend on the extension used to compute it.** -/
theorem detNLMapOf_eq (Q : Extension.{u} A B) (χ : Q.Hom (Generators.self A B).toExtension)
    [Module.Finite B Q.Cotangent] [Module.Projective B Q.Cotangent]
    [Module.Finite B Q.CotangentSpace] [Module.Projective B Q.CotangentSpace] :
    detNLMapOf hsq P ψ = detNLMapOf hsq Q χ := by
  let φ : P.Hom Q := (Extension.defaultHom A B Q).comp ψ
  let φ' : Q.Hom P := (Extension.defaultHom A B P).comp χ
  have hq := nlExtensionMap_isQuasiIso φ φ'
  have hq' := IsQuasiIso.baseChange_of_finite_projective B' hq
  ext x
  rw [detNLMapOf_apply, detNLMapOf_apply]
  refine Eq.symm (((detNLBaseChangeEquiv hsq Q χ).symm_apply_eq).mpr ?_)
  refine Eq.trans ?_ (detNLBaseChangeEquiv_apply_of_hom hsq P ψ Q χ φ hq' _).symm
  refine Eq.trans ?_ (congrArg _ ((detNLBaseChangeEquiv hsq P ψ).apply_symm_apply _)).symm
  refine Eq.trans ?_ (detTransport_baseChange B' (nlExtensionMap φ) hq hq' _).symm
  exact congrArg _ (detNLEquiv_apply_of_hom P ψ Q χ φ φ' x)

omit [Algebra.Syntomic A B] in
/-- Under the identification with the determinant line of a rank-zero `NL(P) ⊗_B B'`,
`δ(NL_{B'/A'})` is the canonical element. -/
theorem detNLBaseChangeEquiv_deltaNL [Algebra.QuasiFinite A' B']
    (hP : TwoTermComplex.IsRankZero (nlOfExtension P).d) :
    detNLBaseChangeEquiv hsq P ψ (deltaNL A' B') =
      TwoTermComplex.delta ((nlOfExtension P).baseChange B').d
        (TwoTermComplex.isRankZero_baseChange B' hP) := by
  have h := detPresentationIso_delta (naiveCotangentPerfect A' B')
    (ofTwoTerm ((nlOfExtension P).baseChange B') (baseChangeIso hsq P
      (Generators.self A' B').toExtension ψ (Extension.Hom.id _) (squareHom P ψ)))
    (isRankZero_double _ (TwoTermComplex.isRankZero_baseChange B' hP))
  simp only [detNLBaseChangeEquiv]
  exact (congrArg (doubleEquiv ((nlOfExtension P).baseChange B')) h).trans
    (doubleEquiv_delta _ (TwoTermComplex.isRankZero_baseChange B' hP))

/-- **The base change map carries `δ(NL_{B/A})` to `δ(NL_{B'/A'})`** (Derived Categories of
Schemes, Remark 0FJY, at the level of rings). -/
theorem detNLMapOf_deltaNL [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A' B']
    (hP : TwoTermComplex.IsRankZero (nlOfExtension P).d) :
    detNLMapOf hsq P ψ (deltaNL A B) = deltaNL A' B' := by
  rw [detNLMapOf_apply, detNLEquiv_deltaNL P ψ hP, LinearEquiv.symm_apply_eq,
    detNLBaseChangeEquiv_deltaNL hsq P ψ hP]
  exact TwoTerm.detBaseChange_delta B' _ hP _

omit [Algebra.Syntomic A B] in
/-- **Reading `det(NL_{B'/A'})` through an extension of `B'`**: for an extension `P'` of `B'` over
`A'` receiving a morphism `h` from `P` over the square, the identification of `det(NL_{B'/A'})`
with the determinant line of `NL(P')` is, on the determinant line of `NL(P) ⊗_B B'`, the transport
along the comparison `NL(P) ⊗_B B' → NL(P')`. -/
theorem detNLEquiv_detNLBaseChangeEquiv_symm (P' : Extension.{u} A' B')
    (ψ' : P'.Hom (Generators.self A' B').toExtension)
    [Module.Finite B' P'.Cotangent] [Module.Projective B' P'.Cotangent]
    [Module.Finite B' P'.CotangentSpace] [Module.Projective B' P'.CotangentSpace]
    (h : P.Hom P') (hq : IsQuasiIso (nlBaseChangeMap (T := B') h))
    (y : TwoTermComplex.determinantLine ((nlOfExtension P).baseChange B').d) :
    detNLEquiv P' ψ' ((detNLBaseChangeEquiv hsq P ψ).symm y) =
      detTransport (nlBaseChangeMap (T := B') h) hq y := by
  obtain ⟨y, rfl⟩ := (detNLBaseChangeEquiv hsq P ψ).surjective y
  rw [LinearEquiv.symm_apply_apply]
  have := isIso_Q_map_nlExtensionBaseChangeMap hsq P P' ψ ψ' h
  simp only [detNLEquiv, detNLBaseChangeEquiv]
  rw [baseChangeIso_eq hsq P _ P' ψ _ ψ' _ h]
  exact doubleEquiv_detPresentationIso_of_isQuasiIso (naiveCotangentPerfect A' B') _ _
    (nlBaseChangeMap (T := B') h) hq
    (by
      simp only [baseChangeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
      exact (Category.assoc _ _ _).trans
        ((congrArg _ (IsIso.inv_hom_id _)).trans (Category.comp_id _))) y

/-- The base change map read through extensions on both sides: the base change of determinant
lines of `NL(P)` followed by the transport along `NL(P) ⊗_B B' → NL(P')`. -/
theorem detNLEquiv_detNLMapOf (P' : Extension.{u} A' B')
    (ψ' : P'.Hom (Generators.self A' B').toExtension)
    [Module.Finite B' P'.Cotangent] [Module.Projective B' P'.Cotangent]
    [Module.Finite B' P'.CotangentSpace] [Module.Projective B' P'.CotangentSpace]
    (h : P.Hom P') (hq : IsQuasiIso (nlBaseChangeMap (T := B') h)) (x : detNL A B) :
    detNLEquiv P' ψ' (detNLMapOf hsq P ψ x) =
      detTransport (nlBaseChangeMap (T := B') h) hq
        ((nlOfExtension P).detBaseChange B' (detNLEquiv P ψ x)) :=
  detNLEquiv_detNLBaseChangeEquiv_symm hsq P ψ P' ψ' h hq _

end Square

/-- A syntomic algebra has a finite presentation whose conormal module and cotangent space are
both finite projective. -/
private theorem exists_generators_finite_projective_cotangentSpace {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Syntomic A B] :
    ∃ (n : ℕ) (P : Generators A B (Fin n)),
      Module.Finite B P.toExtension.Cotangent ∧ Module.Projective B P.toExtension.Cotangent ∧
      Module.Finite B P.toExtension.CotangentSpace ∧
      Module.Projective B P.toExtension.CotangentSpace := by
  obtain ⟨n, P, h₁, h₂⟩ := exists_generators_finite_projective (A := A) (B := B)
  exact ⟨n, P, h₁, h₂, Module.Finite.of_basis P.cotangentSpaceBasis,
    Module.Projective.of_basis P.cotangentSpaceBasis⟩

/-! ### Composition of base change maps -/

section ThreeSquares

variable {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A' B'] [Algebra A'' B'']
  [Algebra A A'] [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A'']
  [Algebra B B'] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
  [Algebra A B'] [Algebra A' B''] [Algebra A B'']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [IsScalarTower A' A'' B'']
  [IsScalarTower A' B' B''] [IsScalarTower A A'' B''] [IsScalarTower A B B'']

omit [Algebra A B'] [Algebra A B''] [IsScalarTower A B B'] [IsScalarTower A B B''] in
/-- Cancelling the intermediate base change of determinant lines: the transport along
`(NL(P) ⊗_B B') ⊗_{B'} B'' ≅ NL(P) ⊗_B B''` of the twice base changed determinant line is the
base change along `B → B''`. -/
theorem detTransport_cancelBaseChangeTwoTerm (P : Extension.{u} A B)
    [Module.Finite B P.Cotangent] [Module.Projective B P.Cotangent]
    [Module.Finite B P.CotangentSpace] [Module.Projective B P.CotangentSpace]
    (hq : IsQuasiIso (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P))
    (φ : TwoTermComplex.determinantLine (nlOfExtension P).d) :
    detTransport (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P) hq
        (((nlOfExtension P).baseChange B').detBaseChange B''
          ((nlOfExtension P).detBaseChange B' φ)) =
      (nlOfExtension P).detBaseChange B'' φ := by
  have hb₁ := cancelBaseChangeTwoTerm_f₁_bijective (B' := B') (B'' := B'') P
  have hb₀ := cancelBaseChangeTwoTerm_f₀_bijective (B' := B') (B'' := B'') P
  rw [detTransport_eq_detEquiv _ hq hb₁.2 hb₀.2]
  have he : (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P).toHom =
      TwoTermComplex.Hom.cancelBaseChange B' B'' (nlOfExtension P).d :=
    TwoTermComplex.Hom.ext_neg_zero rfl rfl
  rw [TwoTermComplex.Hom.detEquiv_congr he _ _
    (TwoTermComplex.Hom.IsDegreewiseSurjective.of_bijective hb₁ hb₀)
    (TwoTermComplex.Hom.isQuasiIso_of_bijective _ hb₁ hb₀)]
  exact TwoTermComplex.Hom.detEquiv_cancelBaseChange B' B'' (nlOfExtension P).d _ _ φ

variable [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A'' B'']
  (hsq₁ : IsGoodSquare A B A' B') (hsq₂ : IsGoodSquare A' B' A'' B'')
  (hsq₃ : IsGoodSquare A B A'' B'')
  (P : Extension.{u} A B) (ψ : P.Hom (Generators.self A B).toExtension)
  [Module.Finite B P.Cotangent] [Module.Projective B P.Cotangent]
  [Module.Finite B P.CotangentSpace] [Module.Projective B P.CotangentSpace]
  (P' : Extension.{u} A' B') (ψ' : P'.Hom (Generators.self A' B').toExtension)
  [Module.Finite B' P'.Cotangent] [Module.Projective B' P'.Cotangent]
  [Module.Finite B' P'.CotangentSpace] [Module.Projective B' P'.CotangentSpace]

/-- **The base change maps compose**: along two good squares `(A, B) → (A', B') → (A'', B'')`
whose composite is good, the base change map along the composite is the composite of the base
change maps. -/
theorem detNLMapOf_detNLMapOf (x : detNL A B) :
    detNLMapOf hsq₂ P' ψ' (detNLMapOf hsq₁ P ψ x) = detNLMapOf hsq₃ P ψ x := by
  obtain ⟨n, P'', h₁, h₂, h₃, h₄⟩ :=
    exists_generators_finite_projective_cotangentSpace (A := A'') (B := B'')
  let ψ'' : P''.toExtension.Hom (Generators.self A'' B'').toExtension :=
    (P''.defaultHom (Generators.self A'' B'')).toExtensionHom
  let h : P.Hom P' := ((Extension.defaultHom A' B' P').comp
    ((Generators.self A B).defaultHom (Generators.self A' B')).toExtensionHom).comp ψ
  let k : P'.Hom P''.toExtension := ((Extension.defaultHom A'' B'' P''.toExtension).comp
    ((Generators.self A' B').defaultHom (Generators.self A'' B'')).toExtensionHom).comp ψ'
  have hq₁ := isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare hsq₁ P P' ψ ψ' h
  have hq₂ := isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare hsq₂ P' P''.toExtension ψ' ψ'' k
  have hq₃ := isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare hsq₃ P P''.toExtension ψ ψ''
    (k.comp h)
  have hq₁' := IsQuasiIso.baseChange_of_finite_projective B'' hq₁
  have hc : IsQuasiIso (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P) :=
    isQuasiIso_cancelBaseChangeChainMap P
  refine (detNLEquiv P''.toExtension ψ'').injective ?_
  rw [detNLEquiv_detNLMapOf hsq₂ P' ψ' P''.toExtension ψ'' k hq₂,
    detNLEquiv_detNLMapOf hsq₃ P ψ P''.toExtension ψ'' (k.comp h) hq₃,
    detNLEquiv_detNLMapOf hsq₁ P ψ P' ψ' h hq₁,
    ← detTransport_baseChange B'' _ hq₁ hq₁',
    ← detTransport_comp _ _ hq₁' hq₂ (hq₂.comp hq₁'),
    detTransport_congr (nlBaseChangeMap_comp_baseChange P P' P''.toExtension h k) _
      (hq₃.comp hc),
    detTransport_comp _ _ hc hq₃, detTransport_cancelBaseChangeTwoTerm]

end ThreeSquares

/-! ### Good squares compose -/

section GoodSquares

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- A square is good as soon as the comparison `NL(P) ⊗_B B' ⟶ NL(P')` is a quasi-isomorphism
for one pair of extensions admitting morphisms to and from the canonical presentations. -/
theorem isGoodSquare_of_isQuasiIso (P : Extension.{u} A B) (P' : Extension.{u} A' B')
    (ψ : P.Hom (Generators.self A B).toExtension)
    (ψ' : P'.Hom (Generators.self A' B').toExtension) (h : P.Hom P')
    (hq : IsQuasiIso (nlBaseChangeMap (T := B') h)) : IsGoodSquare A B A' B' := by
  intro k
  let β := Extension.defaultHom A B P
  have h₁ : IsQuasiIso (nlBaseChangeMap (T := B') ((ψ'.comp h).comp β)) := by
    rw [← nlBaseChangeMap_comp_right, ← nlBaseChangeMap_comp_left]
    exact ((isQuasiIso_of_isHomotopyEquiv (nlExtensionMap_isHomotopyEquiv ψ'
      (Extension.defaultHom A' B' P'))).comp hq).comp
      (isQuasiIso_of_isHomotopyEquiv ((nlExtensionMap_isHomotopyEquiv β ψ).baseChange B'))
  exact isQuasiIso_nlExtensionBaseChangeMap_congr _ _ h₁

end GoodSquares

section GoodSquaresTrans

variable {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A' B'] [Algebra A'' B'']
  [Algebra A A'] [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A'']
  [Algebra B B'] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
  [Algebra A B'] [Algebra A' B''] [Algebra A B'']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [IsScalarTower A' A'' B'']
  [IsScalarTower A' B' B''] [IsScalarTower A A'' B''] [IsScalarTower A B B'']
  [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A'' B'']

omit [Algebra.Syntomic A'' B''] in
/-- **Good squares compose**: the composite of two good squares of syntomic algebras is good. -/
theorem IsGoodSquare.trans (hsq₁ : IsGoodSquare A B A' B') (hsq₂ : IsGoodSquare A' B' A'' B'') :
    IsGoodSquare A B A'' B'' := by
  obtain ⟨n, P, h₁, h₂, h₃, h₄⟩ :=
    exists_generators_finite_projective_cotangentSpace (A := A) (B := B)
  obtain ⟨n', P', h₁', h₂', h₃', h₄'⟩ :=
    exists_generators_finite_projective_cotangentSpace (A := A') (B := B')
  let ψ : P.toExtension.Hom (Generators.self A B).toExtension :=
    (P.defaultHom (Generators.self A B)).toExtensionHom
  let ψ' : P'.toExtension.Hom (Generators.self A' B').toExtension :=
    (P'.defaultHom (Generators.self A' B')).toExtensionHom
  let h : P.toExtension.Hom P'.toExtension := (P.defaultHom P').toExtensionHom
  let k : P'.toExtension.Hom (Generators.self A'' B'').toExtension :=
    (P'.defaultHom (Generators.self A'' B'')).toExtensionHom
  have hq₁ := isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare hsq₁ _ _ ψ ψ' h
  have hq₂ := isQuasiIso_nlExtensionBaseChangeMap_of_isGoodSquare hsq₂ _ _ ψ'
    (Extension.Hom.id _) k
  have hc : IsQuasiIso (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P.toExtension) :=
    isQuasiIso_cancelBaseChangeChainMap P.toExtension
  have hcomp := nlBaseChangeMap_comp_baseChange P.toExtension P'.toExtension
    (Generators.self A'' B'').toExtension h k
  have hq : IsQuasiIso ((nlBaseChangeMap (T := B'') (k.comp h)).comp
      (cancelBaseChangeTwoTerm (B' := B') (B'' := B'') P.toExtension)) := by
    rw [← hcomp]
    exact hq₂.comp (IsQuasiIso.baseChange_of_finite_projective B'' hq₁)
  exact isGoodSquare_of_isQuasiIso P.toExtension _ ψ (Extension.Hom.id _) (k.comp h)
    (IsQuasiIso.of_comp_right hc hq)

end GoodSquaresTrans

/-! ### The base change map -/

section Canonical

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.Syntomic A B] [Algebra.Syntomic A' B']

/-- A finite presentation `B = A[x_1, …, x_n]/I` of a quasi-finite syntomic algebra has a
naive cotangent complex `I/I² → ⨁ᵢ B dxᵢ` of rank zero. -/
theorem isRankZero_nlOfExtension_of_quasiFinite [Algebra.QuasiFinite A B] {n : ℕ}
    (P : Generators A B (Fin n)) :
    TwoTermComplex.IsRankZero (nlOfExtension P.toExtension).d := fun q => by
  have hnt : Nontrivial B := by
    rcases subsingleton_or_nontrivial B with h | h
    · refine absurd ((Ideal.eq_top_iff_one _).mpr ?_) q.isPrime.ne_top
      rw [Subsingleton.elim (1 : B) 0]
      exact Submodule.zero_mem _
    · exact h
  have hS : Module.rankAtStalk P.toExtension.CotangentSpace q = n := by
    simp [Module.finrank_eq_card_basis P.cotangentSpaceBasis]
  exact (Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic P q).trans hS.symm

/-- A chosen finite presentation `B = A[x_1, …, x_n]/I` of a syntomic algebra with finite
projective conormal module. -/
def finitePresentation (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] : Σ n : ℕ, Generators A B (Fin n) :=
  ⟨_, (exists_generators_finite_projective (A := A) (B := B)).choose_spec.choose⟩

/-- The conormal module of the chosen finite presentation is finite. -/
instance (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B] :
    Module.Finite B (finitePresentation A B).2.toExtension.Cotangent :=
  (exists_generators_finite_projective (A := A) (B := B)).choose_spec.choose_spec.1

/-- The conormal module of the chosen finite presentation is projective. -/
instance (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B] :
    Module.Projective B (finitePresentation A B).2.toExtension.Cotangent :=
  (exists_generators_finite_projective (A := A) (B := B)).choose_spec.choose_spec.2

/-- The cotangent space of the chosen finite presentation is finite. -/
instance (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B] :
    Module.Finite B (finitePresentation A B).2.toExtension.CotangentSpace :=
  Module.Finite.of_basis (finitePresentation A B).2.cotangentSpaceBasis

/-- The cotangent space of the chosen finite presentation is projective. -/
instance (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B] :
    Module.Projective B (finitePresentation A B).2.toExtension.CotangentSpace :=
  Module.Projective.of_basis (finitePresentation A B).2.cotangentSpaceBasis

variable (hsq : IsGoodSquare A B A' B')

/-- **The base change map `det(NL_{B/A}) → det(NL_{B'/A'})`** along a good square of syntomic
algebras, semilinear along `B → B'`: the base change of determinant lines of `NL(P)` for a finite
presentation `P` of `B` over `A`, which does not depend on `P` (`NaiveCotangent.detNLMap_eq`). -/
def detNLMap : detNL A B →ₛₗ[algebraMap B B'] detNL A' B' :=
  detNLMapOf hsq (finitePresentation A B).2.toExtension
    ((finitePresentation A B).2.defaultHom (Generators.self A B)).toExtensionHom

/-- The base change map is computed by any extension with finite projective naive cotangent
complex admitting a morphism to the canonical presentation. -/
theorem detNLMap_eq (P : Extension.{u} A B) (ψ : P.Hom (Generators.self A B).toExtension)
    [Module.Finite B P.Cotangent] [Module.Projective B P.Cotangent]
    [Module.Finite B P.CotangentSpace] [Module.Projective B P.CotangentSpace] :
    detNLMap hsq = detNLMapOf hsq P ψ :=
  detNLMapOf_eq hsq _ _ P ψ

/-- **The base change map carries `δ(NL_{B/A})` to `δ(NL_{B'/A'})`** for quasi-finite syntomic
algebras (Derived Categories of Schemes, Remark 0FJY, at the level of rings). -/
theorem detNLMap_deltaNL [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A' B'] :
    detNLMap hsq (deltaNL A B) = deltaNL A' B' := by
  obtain ⟨n, P, h₁, h₂, h₃, h₄⟩ :=
    exists_generators_finite_projective_cotangentSpace (A := A) (B := B)
  rw [detNLMap_eq hsq P.toExtension (P.defaultHom (Generators.self A B)).toExtensionHom]
  exact detNLMapOf_deltaNL hsq _ _ (isRankZero_nlOfExtension_of_quasiFinite P)

/-- **`det(NL_{B'/A'})` is the base change of `det(NL_{B/A})`** along a good square: the base
change map induces `B' ⊗_B det(NL_{B/A}) ≅ det(NL_{B'/A'})`. -/
def detNLBaseChangeLinearEquiv : B' ⊗[B] detNL A B ≃ₗ[B'] detNL A' B' :=
  ((LinearEquiv.baseChange B B' _ _ (detNLEquiv (finitePresentation A B).2.toExtension
      ((finitePresentation A B).2.defaultHom (Generators.self A B)).toExtensionHom)).trans
    (TwoTermComplex.determinantLineBaseChange B' _)).trans
    (detNLBaseChangeEquiv hsq _
      ((finitePresentation A B).2.defaultHom (Generators.self A B)).toExtensionHom).symm

/-- `detNLBaseChangeLinearEquiv` on `1 ⊗ x` is the base change map. -/
theorem detNLBaseChangeLinearEquiv_one_tmul (x : detNL A B) :
    detNLBaseChangeLinearEquiv hsq (1 ⊗ₜ x) = detNLMap hsq x := by
  change (detNLBaseChangeEquiv hsq _ _).symm (TwoTermComplex.determinantLineBaseChange B' _
    (1 ⊗ₜ detNLEquiv _ _ x)) = _
  rw [TwoTermComplex.determinantLineBaseChange_tmul, one_smul]
  rfl

end Canonical

section CanonicalThreeSquares

variable {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A' B'] [Algebra A'' B'']
  [Algebra A A'] [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A'']
  [Algebra B B'] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
  [Algebra A B'] [Algebra A' B''] [Algebra A B'']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [IsScalarTower A' A'' B'']
  [IsScalarTower A' B' B''] [IsScalarTower A A'' B''] [IsScalarTower A B B'']
  [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A'' B'']
  (hsq₁ : IsGoodSquare A B A' B') (hsq₂ : IsGoodSquare A' B' A'' B'')
  (hsq₃ : IsGoodSquare A B A'' B'')

/-- **The base change maps compose** along two good squares of syntomic algebras. -/
theorem detNLMap_detNLMap (x : detNL A B) :
    detNLMap hsq₂ (detNLMap hsq₁ x) = detNLMap hsq₃ x := by
  obtain ⟨n, P, h₁, h₂, h₃, h₄⟩ :=
    exists_generators_finite_projective_cotangentSpace (A := A) (B := B)
  obtain ⟨n', P', h₁', h₂', h₃', h₄'⟩ :=
    exists_generators_finite_projective_cotangentSpace (A := A') (B := B')
  rw [detNLMap_eq hsq₁ P.toExtension (P.defaultHom (Generators.self A B)).toExtensionHom,
    detNLMap_eq hsq₂ P'.toExtension (P'.defaultHom (Generators.self A' B')).toExtensionHom,
    detNLMap_eq hsq₃ P.toExtension (P.defaultHom (Generators.self A B)).toExtensionHom]
  exact detNLMapOf_detNLMapOf hsq₁ hsq₂ hsq₃ _ _ _ _ x

end CanonicalThreeSquares

section Injective

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.Syntomic A B] [Algebra.Syntomic A' B']
  (hsq : IsGoodSquare A B A' B')

/-- Along a good square with `B → B'` bijective, the base change map is injective. -/
theorem detNLMap_injective (hb : Function.Bijective (algebraMap B B')) :
    Function.Injective (detNLMap hsq) := by
  let e : B' ≃ₐ[B] B := (AlgEquiv.ofBijective (Algebra.ofId B B') hb).symm
  let r : B' ⊗[B] detNL A B ≃ₗ[B] detNL A B :=
    (LinearEquiv.rTensor (detNL A B) e.toLinearEquiv).trans (TensorProduct.lid B (detNL A B))
  have hr : ∀ x : detNL A B, r (1 ⊗ₜ x) = x := fun x => by
    simp [r]
  intro x y hxy
  rw [← detNLBaseChangeLinearEquiv_one_tmul, ← detNLBaseChangeLinearEquiv_one_tmul] at hxy
  rw [← hr x, ← hr y, (detNLBaseChangeLinearEquiv hsq).injective hxy]

end Injective

end NaiveCotangent

end
