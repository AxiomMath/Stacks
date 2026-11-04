module

public import StacksFrontier.Homology.TwoTermComplex.LineBaseChange
public import StacksFrontier.RingTheory.TateMap.DetNL
public import StacksFrontier.RingTheory.TateMap.ChartBaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.FlatAlgebraLocalizedTarget
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermFlatBaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso

/-!
# Base change of the determinant of the naive cotangent complex

Let `A → B` and `A' → B'` be syntomic, with a chart base change between them: `B'` is a
principal localization of `A' ⊗_A B`, compatibly with `A' → B'` and `B → B'`. The comparison
`NL_{B/A} ⊗_B B' → NL_{B'/A'}` is a quasi-isomorphism (Stacks 0FK0 on affine charts), so taking
determinants gives an identification `B' ⊗_B det(NL_{B/A}) ≅ det(NL_{B'/A'})` carrying
`δ(NL_{B/A})` to `δ(NL_{B'/A'})` (Stacks, Section 0FKB).

## Main definitions

* `Stacks.TateMap.nlBaseChangeMap`: the comparison `NL(P) ⊗_B B' → NL_{B'/A'}`.
* `Stacks.TateMap.detNLBaseChange`: the identification `B' ⊗_B det(NL_{B/A}) ≅ det(NL_{B'/A'})`.

## Main results

* `Stacks.TateMap.isQuasiIso_nlBaseChangeMap`: the comparison of naive cotangent complexes along
  a chart base change is a quasi-isomorphism.
* `Stacks.TateMap.detNLBaseChange_delta`: `δ(NL_{B/A})` is carried to `δ(NL_{B'/A'})`.
* `Stacks.TateMap.detNLBaseChange_congr`: the identification depends on the square only.

## Implementation notes

The identification is computed on the generators `Stacks.TateMap.gens A B` chosen once for each
syntomic algebra: `NL(P) ⊗_B B'` is a two-term presentation of `NL_{B'/A'}` through the
comparison map, its determinant line is the base change of that of `NL(P)` by
`TwoTermComplex.lineBaseChange`, and the determinant functor identifies its determinant line with
`det(NL_{B'/A'})`. The chart base change is used only to prove that the comparison is a
quasi-isomorphism, a proposition, so two chart base changes of the same square give the same
identification by definition.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
* [Stacks Project, Lemma 0FK0](https://stacks.math.columbia.edu/tag/0FK0)
* [Stacks Project, Section 15.87 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-! ### Base change of homotopy equivalences of two-term complexes -/

namespace NaiveCotangent

variable {S : Type*} [CommRing S] (T : Type*) [CommRing T] [Algebra S T]

/-- Base change of chain maps of two-term complexes commutes with composition. -/
theorem ChainMap.baseChange_comp {X Y Z : TwoTerm S} (g : ChainMap Y Z) (f : ChainMap X Y) :
    (g.comp f).baseChange T = (g.baseChange T).comp (f.baseChange T) :=
  ChainMap.ext (LinearMap.baseChange_comp _ _) (LinearMap.baseChange_comp _ _)

/-- Base change of the identity chain map is the identity chain map. -/
theorem ChainMap.baseChange_id (X : TwoTerm S) :
    (ChainMap.id X).baseChange T = ChainMap.id (X.baseChange T) :=
  ChainMap.ext (LinearMap.baseChange_id) (LinearMap.baseChange_id)

/-- Base change preserves homotopy of chain maps of two-term complexes. -/
theorem Homotopic.baseChange {X Y : TwoTerm S} {f g : ChainMap X Y} (h : Homotopic f g) :
    Homotopic (f.baseChange T) (g.baseChange T) := by
  obtain ⟨k, h₁, h₀⟩ := h
  refine ⟨k.baseChange T, ?_, ?_⟩
  · change LinearMap.baseChange T f.f₁ - LinearMap.baseChange T g.f₁ =
      k.baseChange T ∘ₗ LinearMap.baseChange T X.d
    rw [← LinearMap.baseChange_sub, h₁, LinearMap.baseChange_comp]
  · change LinearMap.baseChange T f.f₀ - LinearMap.baseChange T g.f₀ =
      LinearMap.baseChange T Y.d ∘ₗ k.baseChange T
    rw [← LinearMap.baseChange_sub, h₀, LinearMap.baseChange_comp]

/-- Base change preserves homotopy equivalences of two-term complexes. -/
theorem IsHomotopyEquiv.baseChange {X Y : TwoTerm S} {f : ChainMap X Y}
    (hf : IsHomotopyEquiv f) : IsHomotopyEquiv (f.baseChange T) := by
  obtain ⟨g, h₁, h₂⟩ := hf
  refine ⟨g.baseChange T, ?_, ?_⟩
  · rw [← ChainMap.baseChange_comp, ← ChainMap.baseChange_id]
    exact h₁.baseChange T
  · rw [← ChainMap.baseChange_comp, ← ChainMap.baseChange_id]
    exact h₂.baseChange T

end NaiveCotangent

/-! ### The comparison `NL(P) ⊗_B B' → NL_{B'/A'}` along a chart base change -/

namespace Stacks.TateMap

/-- Base change of a factorisation `h = g ∘ f` of `B`-linear maps into a `B'`-module. -/
private theorem liftBaseChange_eq_comp_baseChange {B B' M N P : Type*} [CommRing B] [CommRing B']
    [Algebra B B'] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module B M] [Module B N]
    [Module B P] [Module B' P] [IsScalarTower B B' P] {f : M →ₗ[B] N} {g : N →ₗ[B] P}
    {h : M →ₗ[B] P} (hfg : h = g ∘ₗ f) :
    h.liftBaseChange B' = g.liftBaseChange B' ∘ₗ f.baseChange B' := by
  subst hfg
  ext x
  simp

attribute [local instance] HasDerivedCategory.standard

section Square

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B']

/-- The comparison `NL(P) ⊗_B B' → NL_{B'/A'}` of a family of generators of `B` over `A` with the
canonical presentation of `B'` over `A'`. -/
def nlBaseChangeMap {ι : Type} (P : Algebra.Generators A B ι) :
    NaiveCotangent.ChainMap (NaiveCotangent.nlExtensionBaseChange P.toExtension B')
      (NaiveCotangent.NL (NaiveCotangent.canonicalGenerators A' B')) :=
  NaiveCotangent.nlExtensionBaseChangeMap
    (P.defaultHom (Algebra.Generators.self A' B')).toExtensionHom

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Base change of the naive cotangent complex along a chart base change.** For `B` flat over
`A` and `B'` a principal localization of `A' ⊗_A B`, the comparison `NL(P) ⊗_B B' → NL_{B'/A'}`
is a quasi-isomorphism. -/
theorem isQuasiIso_nlBaseChangeMap [Module.Flat A B] (D : ChartBaseChange A B A' B')
    {ι : Type} (P : Algebra.Generators A B ι) :
    NaiveCotangent.IsQuasiIso (nlBaseChangeMap (B' := B') (A' := A') P) := by
  let := D.algebra
  have := D.isLocalization
  have : IsScalarTower B (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap B B' x = algebraMap (A' ⊗[A] B) B' ((1 : A') ⊗ₜ[A] x)
    rw [D.base_right]
  have : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq fun y => by
    change algebraMap A' B' y = algebraMap (A' ⊗[A] B) B' (y ⊗ₜ[A] (1 : B))
    rw [D.base_left]
  let h₁ : P.toExtension.Hom (Algebra.Generators.self A B).toExtension :=
    (P.defaultHom (Algebra.Generators.self A B)).toExtensionHom
  let h₀ : (Algebra.Generators.self A B).toExtension.Hom
      (Algebra.Generators.self A' B').toExtension :=
    ((Algebra.Generators.self A B).defaultHom (Algebra.Generators.self A' B')).toExtensionHom
  have q₀ := NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_algebra
    (R := A) (A := B) (B := A') (C := B') (Submonoid.powers D.elt) h₀
  have q₁ : NaiveCotangent.IsQuasiIso ((NaiveCotangent.nlExtensionMap h₁).baseChange B') :=
    NaiveCotangent.isQuasiIso_of_isHomotopyEquiv
      ((NaiveCotangent.nlExtensionMap_isHomotopyEquiv h₁
        ((Algebra.Generators.self A B).defaultHom P).toExtensionHom).baseChange B')
  have hcomp : NaiveCotangent.nlExtensionBaseChangeMap (T := B') (h₀.comp h₁) =
      (NaiveCotangent.nlExtensionBaseChangeMap (T := B') h₀).comp
        ((NaiveCotangent.nlExtensionMap h₁).baseChange B') := by
    exact NaiveCotangent.ChainMap.ext
      (liftBaseChange_eq_comp_baseChange (Algebra.Extension.Cotangent.map_comp _ h₁ h₀))
      (liftBaseChange_eq_comp_baseChange (Algebra.Extension.CotangentSpace.map_comp h₁ h₀))
  refine NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_congr _ (h₀.comp h₁) ?_
  rw [hcomp]
  exact q₀.comp q₁

end Square

/-! ### Chosen generators -/

section Choice

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]

/-- The number of variables of the chosen family of generators of a syntomic algebra. -/
def genCard : ℕ := (exists_generators_finite_projective A B).choose

/-- A family of generators of a syntomic algebra with finite projective conormal module, chosen
once. -/
def gens : Algebra.Generators A B (Fin (genCard A B)) :=
  (exists_generators_finite_projective A B).choose_spec.choose

/-- The conormal module of the chosen generators is finite. -/
instance : Module.Finite B (gens A B).toExtension.Cotangent :=
  (exists_generators_finite_projective A B).choose_spec.choose_spec.1

/-- The conormal module of the chosen generators is projective. -/
instance : Module.Projective B (gens A B).toExtension.Cotangent :=
  (exists_generators_finite_projective A B).choose_spec.choose_spec.2

end Choice

/-- The two-term complex `I/I² → ⨁ᵢ B dxᵢ` of a finite family of generators of a quasi-finite
syntomic algebra has rank zero. -/
theorem isRankZero_cotangentComplex_of_quasiFinite {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Syntomic A B] [Algebra.QuasiFinite A B] {n : ℕ}
    (P : Algebra.Generators A B (Fin n)) :
    TwoTermComplex.IsRankZero P.toExtension.cotangentComplex := by
  intro q
  rw [Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic P q]
  have hnt : Nontrivial B := by
    rcases subsingleton_or_nontrivial B with h | h
    · refine absurd ((Ideal.eq_top_iff_one _).mpr ?_) q.isPrime.ne_top
      rw [Subsingleton.elim (1 : B) 0]
      exact Submodule.zero_mem _
    · exact h
  simp [Module.finrank_eq_card_basis P.cotangentSpaceBasis]

/-! ### The base change of `det(NL_{B/A})` -/

section BaseChange

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']

section Square

variable [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.Syntomic A B]

/-- `NL(P) ⊗_B B'` for the chosen generators `P` of `B` over `A`. -/
abbrev nlBaseChangeTwoTerm : NaiveCotangent.TwoTerm.{u, u, u} B' :=
  NaiveCotangent.nlExtensionBaseChange (gens A B).toExtension B'

/-- The degree-one term `B' ⊗_B I/I²` of `NL(P) ⊗_B B'` is finite. -/
instance : Module.Finite B' (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B')).X₁ :=
  inferInstanceAs (Module.Finite B' (B' ⊗[B] (gens A B).toExtension.Cotangent))

/-- The degree-one term `B' ⊗_B I/I²` of `NL(P) ⊗_B B'` is projective. -/
instance : Module.Projective B' (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B')).X₁ :=
  inferInstanceAs (Module.Projective B' (B' ⊗[B] (gens A B).toExtension.Cotangent))

/-- The degree-zero term `B' ⊗_B ⨁ᵢ B dxᵢ` of `NL(P) ⊗_B B'` is finite. -/
instance : Module.Finite B' (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B')).X₀ :=
  inferInstanceAs (Module.Finite B' (B' ⊗[B] (gens A B).toExtension.CotangentSpace))

/-- The degree-zero term `B' ⊗_B ⨁ᵢ B dxᵢ` of `NL(P) ⊗_B B'` is projective. -/
instance : Module.Projective B' (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B')).X₀ :=
  inferInstanceAs (Module.Projective B' (B' ⊗[B] (gens A B).toExtension.CotangentSpace))

/-- `NL(P) ⊗_B B'` as a two-term presentation of `NL_{B'/A'}`, given that the comparison is an
isomorphism in the derived category. -/
def nlBaseChangePresentation
    (hq : IsIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (A' := A') (B' := B')
      (gens A B))))) :
    TwoTermDeterminant.TwoTermPresentation (NaiveCotangent.naiveCotangentObject A' B') :=
  conePresentation nlBaseChangeTwoTerm
    (asIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (gens A B))))).symm

/-- Degree `-1` of the cochain model of `NL(P) ⊗_B B'` is finite. -/
instance : Module.Finite B' ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).X (-1)) :=
  Module.Finite.equiv (coneNegOneIso nlBaseChangeTwoTerm).toLinearEquiv

/-- Degree `-1` of the cochain model of `NL(P) ⊗_B B'` is projective. -/
instance : Module.Projective B'
    ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).X (-1)) :=
  Module.Projective.of_equiv (coneNegOneIso nlBaseChangeTwoTerm).toLinearEquiv

/-- Degree `0` of the cochain model of `NL(P) ⊗_B B'` is finite. -/
instance : Module.Finite B' ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).X 0) :=
  Module.Finite.equiv (coneZeroIso nlBaseChangeTwoTerm).toLinearEquiv

/-- Degree `0` of the cochain model of `NL(P) ⊗_B B'` is projective. -/
instance : Module.Projective B' ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).X 0) :=
  Module.Projective.of_equiv (coneZeroIso nlBaseChangeTwoTerm).toLinearEquiv

/-- Degree `-1` of the cochain model of `NL(P) ⊗_B B'`. -/
def bcConeNegOneEquiv :
    (B' ⊗[B] (gens A B).toExtension.Cotangent) ≃ₗ[B']
      (cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).X (-1) :=
  (coneNegOneIso nlBaseChangeTwoTerm).toLinearEquiv

/-- Degree `0` of the cochain model of `NL(P) ⊗_B B'`. -/
def bcConeZeroEquiv :
    (B' ⊗[B] (gens A B).toExtension.CotangentSpace) ≃ₗ[B']
      (cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).X 0 :=
  (coneZeroIso nlBaseChangeTwoTerm).toLinearEquiv

omit [Algebra A B'] [IsScalarTower A B B'] in
/-- Under `bcConeNegOneEquiv` and `bcConeZeroEquiv`, the differential of the cochain model of
`NL(P) ⊗_B B'` is the base change of the differential `I/I² → ⨁ᵢ B dxᵢ`. -/
theorem bcCone_d_comm :
    ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).d (-1) 0).hom ∘ₗ
        (bcConeNegOneEquiv (A := A) (B := B) (B' := B')).toLinearMap =
      (bcConeZeroEquiv (A := A) (B := B) (B' := B')).toLinearMap ∘ₗ
        (gens A B).toExtension.cotangentComplex.baseChange B' := by
  ext x
  exact cone_d_coneNegOneIso_hom (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B')) x

/-- The base change of `det(NL_{B/A})` along a square whose comparison of naive cotangent
complexes is an isomorphism in the derived category. -/
def detNLBaseChangeOfIsIso [Algebra.Syntomic A' B']
    (hq : IsIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (A' := A') (B' := B')
      (gens A B))))) :
    B' ⊗[B] detNL A B ≃ₗ[B'] detNL A' B' :=
  ((LinearEquiv.baseChange B B' _ _ (detNLEquiv (gens A B))).trans
    (TwoTermComplex.lineBaseChange B' (gens A B).toExtension.cotangentComplex)).trans
    ((TwoTermComplex.lineCongr ((gens A B).toExtension.cotangentComplex.baseChange B')
      ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).d (-1) 0).hom
      bcConeNegOneEquiv bcConeZeroEquiv).trans
      (TwoTermDeterminant.detPresentationIso (nlObject A' B')
        (nlBaseChangePresentation hq)).symm)

omit [Algebra A B'] [IsScalarTower A B B'] in
/-- The two-term complex `NL(P) ⊗_B B'` of a quasi-finite syntomic algebra has rank zero. -/
theorem isRankZero_nlBaseChangeTwoTerm [Algebra.QuasiFinite A B] :
    TwoTermComplex.IsRankZero ((gens A B).toExtension.cotangentComplex.baseChange B') := by
  intro p
  rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_baseChange]
  exact isRankZero_cotangentComplex_of_quasiFinite (gens A B) _

/-- The base change of `det(NL_{B/A})` carries `δ(NL_{B/A})` to `δ(NL_{B'/A'})`. -/
theorem detNLBaseChangeOfIsIso_deltaNL [Algebra.Syntomic A' B'] [Algebra.QuasiFinite A B]
    [Algebra.QuasiFinite A' B']
    (hq : IsIso (DerivedCategory.Q.map (coneMap (nlBaseChangeMap (A' := A') (B' := B')
      (gens A B))))) :
    detNLBaseChangeOfIsIso hq (1 ⊗ₜ deltaNL A B) = deltaNL A' B' := by
  have h₀ := isRankZero_cotangentComplex_of_quasiFinite (gens A B)
  have h₁ := isRankZero_nlBaseChangeTwoTerm (A := A) (B := B) (B' := B')
  have h₂ : TwoTermComplex.IsRankZero
      ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).d (-1) 0).hom := fun p =>
    ((ProjectiveDeterminant.rankAtStalk_congr
      (bcConeNegOneEquiv (A := A) (B := B) (B' := B')) p).symm.trans (h₁ p)).trans
      (ProjectiveDeterminant.rankAtStalk_congr (bcConeZeroEquiv (A := A) (B := B) (B' := B')) p)
  have k3 := TwoTermComplex.lineCongr_delta _ _ _ _ bcCone_d_comm h₁ h₂
  have k4 : (TwoTermDeterminant.detPresentationIso (nlObject A' B')
      (nlBaseChangePresentation hq)).symm (TwoTermComplex.delta
        ((cone (nlBaseChangeTwoTerm (A := A) (B := B) (B' := B'))).d (-1) 0).hom h₂) =
        deltaNL A' B' :=
    (LinearEquiv.symm_apply_eq _).2 (TwoTermDeterminant.detPresentationIso_delta (nlObject A' B')
      (nlBaseChangePresentation hq) h₂).symm
  simp only [detNLBaseChangeOfIsIso, LinearEquiv.trans_apply]
  rw [LinearEquiv.baseChange_tmul, detNLEquiv_deltaNL (gens A B) h₀,
    TwoTermComplex.lineBaseChange_delta B' _ h₀ h₁]
  exact (congrArg (TwoTermDeterminant.detPresentationIso (nlObject A' B')
    (nlBaseChangePresentation hq)).symm k3).trans k4

end Square

/-- **The base change of `det(NL_{B/A})`** along a chart base change of syntomic algebras,
`B' ⊗_B det(NL_{B/A}) ≅ det(NL_{B'/A'})`. It is the determinant of the comparison
`NL_{B/A} ⊗_B B' → NL_{B'/A'}` of Stacks 0FK0, computed on the chosen generators of `B`
over `A`. The chart base change enters only through the proof that the comparison is a
quasi-isomorphism, so the identification depends on the square alone
(`detNLBaseChange_congr`). -/
def detNLBaseChange [Algebra.Syntomic A B] [Algebra.Syntomic A' B']
    (D : ChartBaseChange A B A' B') : B' ⊗[B] detNL A B ≃ₗ[B'] detNL A' B' :=
  letI : Algebra A B' := ((algebraMap B B').comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun a =>
    D.algebraMap_comm a
  detNLBaseChangeOfIsIso
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_coneMap (isQuasiIso_nlBaseChangeMap D (gens A B))))

/-- The base change of `det(NL_{B/A})` does not depend on the chart base change datum, only on
the square of rings. -/
theorem detNLBaseChange_congr [Algebra.Syntomic A B] [Algebra.Syntomic A' B']
    (D D' : ChartBaseChange A B A' B') : detNLBaseChange D = detNLBaseChange D' :=
  rfl

/-- **The base change of `det(NL_{B/A})` carries `δ(NL_{B/A})` to `δ(NL_{B'/A'})`.** -/
theorem detNLBaseChange_delta [Algebra.Syntomic A B] [Algebra.Syntomic A' B']
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A' B'] (D : ChartBaseChange A B A' B') :
    detNLBaseChange D (1 ⊗ₜ deltaNL A B) = deltaNL A' B' := by
  let : Algebra A B' := ((algebraMap B B').comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun a =>
    D.algebraMap_comm a
  exact detNLBaseChangeOfIsIso_deltaNL _

end BaseChange

end Stacks.TateMap
