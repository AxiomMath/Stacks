module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpiTowerLimit
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.StrictProLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The completed naive cotangent complex as a derived limit

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `B` be an `I`-adically complete
`A`-algebra of finite type modulo `I`, presented as `B = A⟨x₁, …, x_r⟩ / J`.  Writing
`Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`, the completed naive cotangent complex is the derived inverse
limit of the naive cotangent complexes of the reductions,

`NL^∧_{B/A} = R lim NL_{Bₙ/Aₙ}`  in  `D(B)`.

That is Stacks 0AJS (2).  The proof assembles four ingredients.  The two inverse systems
`{NL^∧_{B/A} ⊗_B Bₙ}` and `{NL_{Bₙ/Aₙ}}` of two-term complexes are strictly pro-isomorphic by
Stacks 0AJS (1); an interleaving with a uniform shift transports limit cones, so the two
systems have the same inverse limit on the nose.  The first system has an evident limit, namely
`NL^∧_{B/A}` itself, because both of its terms are `I`-adically complete: `J / J²` and
`⨁ᵢ B dxᵢ` are finite modules over the Noetherian ring `B`, in which `IB` lies in the Jacobson
radical, so their adic filtrations are separated and Stacks 031B applies.  Finally the
transition maps of `{NL_{Bₙ/Aₙ}}` are surjections, so its ordinary inverse limit computes its
derived inverse limit.

## Main definitions

* `NaiveCotangent.TwoTerm.cochainComplexFunctor`: two-term complexes of `S`-modules, read
  functorially as cochain complexes of `S`-modules concentrated in degrees `-1` and `0`, with
  both terms lifted to a common universe.
* `NaiveCotangent.TwoTerm.quotProj` and `NaiveCotangent.TwoTerm.modIdealTowerCone`: the
  canonical surjection onto a quotient complex, and the cone it gives over the system of
  reductions `{X ⊗_S S/𝔞ⁿ}`.

## Main results

* `Stacks.LocalCohomology.isLimitPostcomposeOfInterleaved`: an interleaving with a uniform
  shift transports a limit cone from one inverse sequence to the other, so strictly
  pro-isomorphic inverse sequences have the same inverse limit.
* `AdicCompletion.isLimitOfAdicQuotientSystem`: an `I`-adically complete module is the inverse
  limit of its tower of adic quotients.
* `Rig.AdicFiniteTypeAlgebra.isAdicComplete_of_finite`: every finite module over an object of
  the category of Stacks 0AL4 over a Noetherian base is `I`-adically complete.
* `Rig.CompletedPolynomialPresentation.isAdicComplete_cotangent`: the conormal module `J / J²`
  of a completed polynomial presentation is `I`-adically complete.
* `Rig.CompletedNaiveCotangentComplex.isLimitCompletedReductionTowerCone`: `NL^∧_{B/A}` is the
  inverse limit of `{NL^∧_{B/A} ⊗_B Bₙ}`, and
  `Rig.CompletedNaiveCotangentComplex.nonempty_isLimit_reductionTowerCone`: it is also the
  inverse limit of `{NL_{Bₙ/Aₙ}}`.
* `Rig.CompletedNaiveCotangentComplex.isDerivedLimit_reductionTower`: **Stacks 0AJS (2)**.

## Implementation notes

The cochain-complex realization is `HomologicalComplex.double`, which is how
`Rig.CompletedNaiveCotangentComplex.cochainComplex` is already built, so the functor agrees
with it on the two-term reading of `NL^∧_{B/A}` by definition.  The limit property of a cone of
cochain complexes is checked degreewise; in the degrees other than `-1` and `0` every term is a
zero object, and in the two interesting degrees the comparison equivalences that identify the
system with a tower of adic quotients absorb both the universe lift and the `eqToHom` of the
`double` construction.

The inverse system `{NL_{Bₙ/Aₙ}}` is `Rig.CompletedNaiveCotangentComplex.reductionTower`, which
realises `NL_{Bₙ/Aₙ}` as a quotient of `NL^∧_{B/A}`, with the canonical surjections between
nested quotients as transition maps.  That each level is the naive cotangent complex of the
induced presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ` is the second half of
`Rig.CompletedNaiveCotangentComplex.nonempty_iso_reductionTower`; that those identifications
carry the transition maps induced by morphisms of presentations to the canonical surjections is
*not* proved, the two agreeing only up to homotopy by Stacks 00S1 (2).

The limit property of the cone over `{NL_{Bₙ/Aₙ}}` is stated as a `Nonempty` because the shift
making the two systems interleave is the Artin–Rees constant, which is only known to exist.

## References

* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
* [Stacks Project, Tag 031B](https://stacks.math.columbia.edu/tag/031B)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open ComplexShape (upIntRelNegOneZero)

/-! ## Limits of diagrams of zero objects -/

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- A cone with zero vertex over a diagram of zero objects is a limit cone. -/
public def isLimitOfIsZero {F : J ⥤ D} (s : Cone F) (hpt : IsZero s.pt)
    (hF : ∀ j, IsZero (F.obj j)) : IsLimit s where
  lift _ := 0
  fac _ j := (hF j).eq_of_tgt _ _
  uniq _ _ _ := hpt.eq_of_tgt _ _

omit [HasZeroMorphisms D] in
/-- Every morphism into a zero object is an epimorphism. -/
public theorem epi_of_isZero_tgt {X Y : D} (hY : IsZero Y) (f : X ⟶ Y) : Epi f :=
  ⟨fun g h _ => hY.eq_of_src g h⟩

end CategoryTheory.Limits

/-! ## Limits are transported along a strict pro-isomorphism -/

namespace Stacks.LocalCohomology

universe v u

variable {C : Type u} [Category.{v} C]

/-- **Strictly pro-isomorphic inverse sequences have the same inverse limit.**  Let `X` and `Y`
be inverse sequences interleaved by natural families `φₙ : Xₙ ⟶ Yₙ` and `ψₙ : Y_{n+c} ⟶ Xₙ`
with a uniform shift `c`, as in `Stacks.LocalCohomology.nonempty_iso_of_interleaved`.  Then
composing a limit cone over `X` with `φ` produces a limit cone over `Y`. -/
public def isLimitPostcomposeOfInterleaved {X Y : Functor ℕᵒᵖ C} (c : ℕ)
    (φ : NatTrans X Y) (ψ : NatTrans (shiftedInverseSequence Y c) X)
    (hXY : ∀ n : ℕ, φ.app (op (n + c)) ≫ ψ.app (op n) =
      X.map (opHomOfLE (Nat.le_add_right n c)))
    (hYX : ∀ n : ℕ, ψ.app (op n) ≫ φ.app (op n) =
      Y.map (opHomOfLE (Nat.le_add_right n c)))
    {s : Cone X} (hs : IsLimit s) : IsLimit ((Cone.postcompose φ).obj s) where
  lift t := hs.lift ((Cone.postcompose ψ).obj (t.whisker (inverseSequenceShift c)))
  fac t j := by
    have key : ∀ n : ℕ,
        hs.lift ((Cone.postcompose ψ).obj (t.whisker (inverseSequenceShift c))) ≫
          ((Cone.postcompose φ).obj s).π.app (op n) = t.π.app (op n) := by
      intro n
      have hfac := hs.fac ((Cone.postcompose ψ).obj (t.whisker (inverseSequenceShift c))) (op n)
      change hs.lift _ ≫ s.π.app (op n) ≫ φ.app (op n) = _
      rw [← Category.assoc, hfac]
      change (t.π.app (op (n + c)) ≫ ψ.app (op n)) ≫ φ.app (op n) = _
      rw [Category.assoc, hYX n]
      exact t.w (opHomOfLE (Nat.le_add_right n c))
    exact key j.unop
  uniq t m hm := by
    refine hs.uniq ((Cone.postcompose ψ).obj (t.whisker (inverseSequenceShift c))) m
      fun j => ?_
    have key : ∀ n : ℕ, m ≫ s.π.app (op n) = t.π.app (op (n + c)) ≫ ψ.app (op n) := by
      intro n
      have h1 : m ≫ s.π.app (op (n + c)) ≫ φ.app (op (n + c)) = t.π.app (op (n + c)) :=
        hm (op (n + c))
      have h2 : s.π.app (op (n + c)) ≫ φ.app (op (n + c)) ≫ ψ.app (op n) = s.π.app (op n) := by
        rw [hXY n]
        exact s.w (opHomOfLE (Nat.le_add_right n c))
      rw [← h1, Category.assoc, Category.assoc, h2]
    exact key j.unop

end Stacks.LocalCohomology

/-! ## An adically complete module is the limit of its adic quotients -/

namespace AdicCompletion

universe t w u

/-- **An `I`-adically complete module is the inverse limit of its tower of adic quotients.**
Let `T` be an inverse sequence of `R`-modules identified level by level with the tower
`M ⧸ IⁿM` of an `I`-adically complete module `M`, compatibly with the transition maps, and let
`s` be a cone over `T` whose vertex is identified with `M` and whose legs are the quotient
maps.  Then `s` is a limit cone. -/
public def isLimitOfAdicQuotientSystem {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type w} [AddCommGroup M] [Module R M] [IsAdicComplete I M]
    {T : ℕᵒᵖ ⥤ ModuleCat.{t} R} {s : Cone T} (hv : s.pt ≃ₗ[R] M)
    (e : ∀ n : ℕ, T.obj (op n) ≃ₗ[R] M ⧸ (I ^ n • (⊤ : Submodule R M)))
    (hmap : ∀ {m n : ℕ} (h : m ≤ n) (x : T.obj (op n)),
      e m ((T.map (opHomOfLE h)) x) = Submodule.factorPow I M h (e n x))
    (hleg : ∀ (n : ℕ) (x : s.pt),
      e n (s.π.app (op n) x) = (I ^ n • (⊤ : Submodule R M)).mkQ (hv x)) :
    IsLimit s := by
  have hcompat : ∀ (t : Cone T) {m n : ℕ} (hle : m ≤ n),
      transitionMap I M hle ∘ₗ ((e n).toLinearMap ∘ₗ (t.π.app (op n)).hom) =
        (e m).toLinearMap ∘ₗ (t.π.app (op m)).hom := by
    intro t m n hle
    refine LinearMap.ext fun x => ?_
    have hw := congrArg (fun g : t.pt ⟶ T.obj (op m) => g.hom x) (t.w (opHomOfLE hle))
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hw
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [← hw, hmap hle]
  refine
    { lift := fun t => ModuleCat.ofHom (hv.symm.toLinearMap ∘ₗ
        (ofLinearEquiv I M).symm.toLinearMap ∘ₗ
          lift I (fun n => (e n).toLinearMap ∘ₗ (t.π.app (op n)).hom) (hcompat t))
      fac := ?_
      uniq := ?_ }
  · intro t j
    have key : ∀ n : ℕ, ModuleCat.ofHom (hv.symm.toLinearMap ∘ₗ
        (ofLinearEquiv I M).symm.toLinearMap ∘ₗ
          lift I (fun n => (e n).toLinearMap ∘ₗ (t.π.app (op n)).hom) (hcompat t)) ≫
            s.π.app (op n) = t.π.app (op n) := by
      intro n
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      refine (e n).injective ?_
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
      rw [hleg n, hv.apply_symm_apply, ← eval_of, of_ofLinearEquiv_symm]
      rfl
    exact key j.unop
  · intro t m hm
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have hval : of I M (hv (m.hom x)) =
        lift I (fun n => (e n).toLinearMap ∘ₗ (t.π.app (op n)).hom) (hcompat t) x := by
      refine AdicCompletion.ext fun n => ?_
      have h1 := hleg n (m.hom x)
      have h2 := congrArg (fun g : t.pt ⟶ T.obj (op n) => g.hom x) (hm (op n))
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h2
      change Submodule.mkQ _ (hv (m.hom x)) = (e n) ((t.π.app (op n)).hom x)
      rw [← h1, h2]
    simp only [ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [← hval, ofLinearEquiv_symm_of, hv.symm_apply_apply]

end AdicCompletion

/-! ## Two-term complexes as cochain complexes, functorially -/

namespace NaiveCotangent

universe u v w a b

/-- A linear map read between universe lifts of its source and target. -/
public def uliftMap {S : Type*} [CommRing S] {M N : Type*}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) :
    ULift.{a} M →ₗ[S] ULift.{b} N :=
  ULift.moduleEquiv.symm.toLinearMap.comp (f.comp ULift.moduleEquiv.toLinearMap)

namespace TwoTerm

variable {S : Type u} [CommRing S]

/-- The differential of a two-term complex, with both terms lifted to a common universe. -/
public def uliftD (X : TwoTerm.{u, v, w} S) : ULift.{w} X.X₁ →ₗ[S] ULift.{v} X.X₀ :=
  ULift.moduleEquiv.symm.toLinearMap.comp (X.d.comp ULift.moduleEquiv.toLinearMap)

/-- The degree-`1` component of a chain map, lifted to a common universe. -/
public def uliftF₁ {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) :
    ULift.{w} X.X₁ →ₗ[S] ULift.{w} Y.X₁ := uliftMap f.f₁

/-- The degree-`0` component of a chain map, lifted to a common universe. -/
public def uliftF₀ {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) :
    ULift.{v} X.X₀ →ₗ[S] ULift.{v} Y.X₀ := uliftMap f.f₀

/-- The lifted differential `uliftD` acts on `ULift.up x` as the differential on `x`. -/
@[simp] public theorem uliftD_up (X : TwoTerm.{u, v, w} S) (x : X.X₁) :
    X.uliftD (ULift.up x) = ULift.up (X.d x) := rfl

/-- The lifted degree-`1` component `uliftF₁ f` acts on `ULift.up x` as `f.f₁` on `x`. -/
@[simp] public theorem uliftF₁_up {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) (x : X.X₁) :
    uliftF₁ f (ULift.up x) = ULift.up (f.f₁ x) := rfl

/-- The lifted degree-`0` component `uliftF₀ f` acts on `ULift.up x` as `f.f₀` on `x`. -/
@[simp] public theorem uliftF₀_up {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) (x : X.X₀) :
    uliftF₀ f (ULift.up x) = ULift.up (f.f₀ x) := rfl

private theorem uliftD_comm {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) :
    Y.uliftD.comp (uliftF₁ f) = (uliftF₀ f).comp X.uliftD := by
  refine LinearMap.ext fun x => ?_
  have h := congrArg (fun m => m x.down) f.comm
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  exact congrArg ULift.up h

/-- A two-term complex of `S`-modules, read as a cochain complex with the degree-`1` term in
cohomological degree `-1` and the degree-`0` term in cohomological degree `0`, both lifted to a
common universe. -/
public abbrev cochainComplexOf (X : TwoTerm.{u, v, w} S) :
    CochainComplex (ModuleCat.{max v w} S) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom X.uliftD) upIntRelNegOneZero

/-- The identification of the degree-`-1` term of `X.cochainComplexOf` with the lift of `X₁`. -/
public abbrev cochainIso₁ (X : TwoTerm.{u, v, w} S) :
    X.cochainComplexOf.X (-1) ≅ ModuleCat.of S (ULift.{w} X.X₁) :=
  HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom X.uliftD) upIntRelNegOneZero

/-- The identification of the degree-`0` term of `X.cochainComplexOf` with the lift of `X₀`. -/
public abbrev cochainIso₀ (X : TwoTerm.{u, v, w} S) :
    X.cochainComplexOf.X 0 ≅ ModuleCat.of S (ULift.{v} X.X₀) :=
  HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom X.uliftD) upIntRelNegOneZero negOne_ne_zero

/-- The degree-`-1` term of the cochain-complex realization of a two-term complex is the
degree-`1` term of the complex. -/
public def cochainEquiv₁ (X : TwoTerm.{u, v, w} S) : X.cochainComplexOf.X (-1) ≃ₗ[S] X.X₁ :=
  X.cochainIso₁.toLinearEquiv.trans ULift.moduleEquiv

/-- The degree-`0` term of the cochain-complex realization of a two-term complex is the
degree-`0` term of the complex. -/
public def cochainEquiv₀ (X : TwoTerm.{u, v, w} S) : X.cochainComplexOf.X 0 ≃ₗ[S] X.X₀ :=
  X.cochainIso₀.toLinearEquiv.trans ULift.moduleEquiv

/-- The cochain map induced by a chain map of two-term complexes. -/
public def cochainMapOf {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) :
    X.cochainComplexOf ⟶ Y.cochainComplexOf :=
  HomologicalComplex.mkHomFromDouble upIntRelNegOneZero negOne_ne_zero
    (ModuleCat.ofHom (uliftF₁ f) ≫ Y.cochainIso₁.inv)
    (ModuleCat.ofHom (uliftF₀ f) ≫ Y.cochainIso₀.inv)
    (by
      rw [HomologicalComplex.double_d (ModuleCat.ofHom Y.uliftD) upIntRelNegOneZero negOne_ne_zero]
      simp only [Category.assoc, cochainIso₁, cochainIso₀, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun g => g ≫ _) (ModuleCat.hom_ext (uliftD_comm f)))
    (fun _ _ => by
      rw [HomologicalComplex.double_d_eq_zero₀ (ModuleCat.ofHom Y.uliftD) upIntRelNegOneZero _ _
        negOne_ne_zero.symm, comp_zero])

/-- The degree-`-1` component of `cochainMapOf f` is `uliftF₁ f`, read through the identifications
`cochainIso₁` of the degree-`-1` terms. -/
@[simp] public theorem cochainMapOf_f_negOne {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) :
    (cochainMapOf f).f (-1) =
      X.cochainIso₁.hom ≫ ModuleCat.ofHom (uliftF₁ f) ≫ Y.cochainIso₁.inv :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

/-- The degree-`0` component of `cochainMapOf f` is `uliftF₀ f`, read through the identifications
`cochainIso₀` of the degree-`0` terms. -/
@[simp] public theorem cochainMapOf_f_zero {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y) :
    (cochainMapOf f).f 0 =
      X.cochainIso₀.hom ≫ ModuleCat.ofHom (uliftF₀ f) ≫ Y.cochainIso₀.inv :=
  HomologicalComplex.mkHomFromDouble_f₁ _ _ _ _ _ _

/-- A morphism of modules which is the conjugate of a lifted linear map by identifications with
universe lifts acts, read through those identifications, as the linear map. -/
private theorem down_hom_apply_of_eq_comp {P Q : ModuleCat.{max a b} S} {M N : Type a}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (eP : P ≅ ModuleCat.of S (ULift.{b} M)) (eQ : Q ≅ ModuleCat.of S (ULift.{b} N))
    (g : M →ₗ[S] N) (F : P ⟶ Q) (hF : F = eP.hom ≫ ModuleCat.ofHom (uliftMap g) ≫ eQ.inv)
    (x : P) : (eQ.hom (F x)).down = g (eP.hom x).down := by
  subst hF
  have := congrArg (fun h : _ ⟶ ModuleCat.of S (ULift.{b} N) => h.hom (uliftMap g (eP.hom x)))
    eQ.inv_hom_id
  exact congrArg ULift.down this

/-- The degree-`-1` component of the cochain realization of a chain map, read through the
identifications of the degree-`1` terms, is the degree-`1` component of the chain map. -/
public theorem cochainEquiv₁_cochainMapOf {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y)
    (x : X.cochainComplexOf.X (-1)) :
    Y.cochainEquiv₁ (((cochainMapOf f).f (-1)) x) = f.f₁ (X.cochainEquiv₁ x) :=
  down_hom_apply_of_eq_comp X.cochainIso₁ Y.cochainIso₁ f.f₁ _ (cochainMapOf_f_negOne f) x

/-- The degree-`0` component of the cochain realization of a chain map, read through the
identifications of the degree-`0` terms, is the degree-`0` component of the chain map. -/
public theorem cochainEquiv₀_cochainMapOf {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y)
    (x : X.cochainComplexOf.X 0) :
    Y.cochainEquiv₀ (((cochainMapOf f).f 0) x) = f.f₀ (X.cochainEquiv₀ x) :=
  down_hom_apply_of_eq_comp X.cochainIso₀ Y.cochainIso₀ f.f₀ _ (cochainMapOf_f_zero f) x

/-- The cochain map of the identity chain map is the identity. -/
public theorem cochainMapOf_id (X : TwoTerm.{u, v, w} S) :
    cochainMapOf (ChainMap.id X) = 𝟙 X.cochainComplexOf := by
  refine HomologicalComplex.from_double_hom_ext (i₀ := -1) (i₁ := 0) ?_ ?_
  · rw [cochainMapOf_f_negOne, HomologicalComplex.id_f,
      show ModuleCat.ofHom (uliftF₁ (ChainMap.id X)) =
          𝟙 (ModuleCat.of S (ULift.{w} X.X₁)) from
        ModuleCat.hom_ext (LinearMap.ext fun _ => rfl),
      Category.id_comp, Iso.hom_inv_id]
  · rw [cochainMapOf_f_zero, HomologicalComplex.id_f,
      show ModuleCat.ofHom (uliftF₀ (ChainMap.id X)) =
          𝟙 (ModuleCat.of S (ULift.{v} X.X₀)) from
        ModuleCat.hom_ext (LinearMap.ext fun _ => rfl),
      Category.id_comp, Iso.hom_inv_id]

/-- The cochain map of a composite of chain maps is the composite of the cochain maps. -/
public theorem cochainMapOf_comp {X Y Z : TwoTerm.{u, v, w} S} (f : ChainMap X Y)
    (g : ChainMap Y Z) :
    cochainMapOf (ChainMap.comp g f) = cochainMapOf f ≫ cochainMapOf g := by
  refine HomologicalComplex.from_double_hom_ext (i₀ := -1) (i₁ := 0) ?_ ?_
  · rw [HomologicalComplex.comp_f, cochainMapOf_f_negOne, cochainMapOf_f_negOne,
      cochainMapOf_f_negOne,
      show ModuleCat.ofHom (uliftF₁ (ChainMap.comp g f)) =
          ModuleCat.ofHom (uliftF₁ f) ≫ ModuleCat.ofHom (uliftF₁ g) from
        ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rw [HomologicalComplex.comp_f, cochainMapOf_f_zero, cochainMapOf_f_zero,
      cochainMapOf_f_zero,
      show ModuleCat.ofHom (uliftF₀ (ChainMap.comp g f)) =
          ModuleCat.ofHom (uliftF₀ f) ≫ ModuleCat.ofHom (uliftF₀ g) from
        ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **Two-term complexes of `S`-modules, read as cochain complexes.**  The degree-`1` term sits
in cohomological degree `-1` and the degree-`0` term in cohomological degree `0`, both lifted
to a common universe, and every other term is zero. -/
public def cochainComplexFunctor (S : Type u) [CommRing S] :
    TwoTerm.{u, v, w} S ⥤ CochainComplex (ModuleCat.{max v w} S) ℤ where
  obj X := X.cochainComplexOf
  map f := cochainMapOf f
  map_id X := cochainMapOf_id X
  map_comp f g := cochainMapOf_comp f g

/-- The functor `cochainComplexFunctor S` sends a two-term complex to its cochain realization
`cochainComplexOf`. -/
@[simp] public theorem cochainComplexFunctor_obj (X : TwoTerm.{u, v, w} S) :
    (cochainComplexFunctor S).obj X = X.cochainComplexOf := rfl

/-- The functor `cochainComplexFunctor S` sends a chain map to its cochain realization
`cochainMapOf`. -/
@[simp] public theorem cochainComplexFunctor_map {X Y : TwoTerm.{u, v, w} S} (f : X ⟶ Y) :
    (cochainComplexFunctor S).map f = cochainMapOf f := rfl

/-- Away from the degrees `-1` and `0` the cochain-complex realization of a two-term complex
is zero. -/
public theorem isZero_cochainComplexOf_X (X : TwoTerm.{u, v, w} S) {i : ℤ}
    (h₀ : i ≠ -1) (h₁ : i ≠ 0) : IsZero (X.cochainComplexOf.X i) :=
  HomologicalComplex.isZero_double_X _ upIntRelNegOneZero i h₀ h₁

/-! ## The canonical cone over the system of reductions -/

variable (X : TwoTerm.{u, v, w} S)

/-- The cone over the system of reductions `{X ⊗_S S/𝔞ⁿ}` with vertex `X`, whose legs are the
reduction maps. -/
public def modIdealTowerCone (𝔞 : Ideal S) : Cone (X.modIdealTower 𝔞) where
  pt := X
  π :=
    { app := fun n => X.quotProj _ _ (X.smul_top_le_comap_d (𝔞 ^ n.unop))
      naturality := fun _ _ _ => by
        refine ChainMap.ext ?_ ?_ <;>
          exact LinearMap.ext fun z => rfl }

/-- Each leg of `modIdealTowerCone` is the quotient map in degree `1`. -/
@[simp] public theorem modIdealTowerCone_π_app_f₁ (𝔞 : Ideal S) (n : ℕᵒᵖ) :
    ((X.modIdealTowerCone 𝔞).π.app n).f₁ = Submodule.mkQ _ := rfl

/-- Each leg of `modIdealTowerCone` is the quotient map in degree `0`. -/
@[simp] public theorem modIdealTowerCone_π_app_f₀ (𝔞 : Ideal S) (n : ℕᵒᵖ) :
    ((X.modIdealTowerCone 𝔞).π.app n).f₀ = Submodule.mkQ _ := rfl

/-! ## Epimorphisms and interleavings -/

/-- A surjective linear map stays surjective after lifting source and target to universes. -/
private theorem surjective_uliftMap {S : Type*} [CommRing S] {M N : Type*}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] {f : M →ₗ[S] N}
    (h : Function.Surjective f) : Function.Surjective (uliftMap.{a, b} f) := fun y => by
  obtain ⟨x, hx⟩ := h y.down
  exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-- If the degree-`1` component of a chain map is surjective, so is its lift `uliftF₁ f`. -/
public theorem surjective_uliftF₁ {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y)
    (h : Function.Surjective f.f₁) : Function.Surjective (uliftF₁ f) :=
  surjective_uliftMap h

/-- If the degree-`0` component of a chain map is surjective, so is its lift `uliftF₀ f`. -/
public theorem surjective_uliftF₀ {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y)
    (h : Function.Surjective f.f₀) : Function.Surjective (uliftF₀ f) :=
  surjective_uliftMap h

/-- A chain map which is surjective in both degrees realizes an epimorphism of cochain
complexes. -/
public theorem epi_cochainMapOf {X Y : TwoTerm.{u, v, w} S} (f : ChainMap X Y)
    (h₁ : Function.Surjective f.f₁) (h₀ : Function.Surjective f.f₀) :
    Epi (cochainMapOf f) := by
  refine HomologicalComplex.epi_of_epi_f _ fun i => ?_
  by_cases hm1 : i = -1
  · subst hm1
    rw [cochainMapOf_f_negOne]
    have : Epi (ModuleCat.ofHom (uliftF₁ f)) :=
      (ModuleCat.epi_iff_surjective _).2 (surjective_uliftF₁ f h₁)
    infer_instance
  · by_cases h0 : i = 0
    · subst h0
      rw [cochainMapOf_f_zero]
      have : Epi (ModuleCat.ofHom (uliftF₀ f)) :=
        (ModuleCat.epi_iff_surjective _).2 (surjective_uliftF₀ f h₀)
      infer_instance
    · exact epi_of_isZero_tgt (isZero_cochainComplexOf_X Y hm1 h0) _

variable (𝔞 : Ideal S) (c : ℕ) (U : ℕ → Submodule S X.X₁) (hU : Antitone U)
  (hd : ∀ n, U n ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₀).comap X.d)
  (hlo : ∀ n, (𝔞 ^ n • ⊤ : Submodule S X.X₁) ≤ U n)
  (hhi : ∀ n, U (n + c) ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₁))

/-- The first composite of the interleaving of
`NaiveCotangent.TwoTerm.nonempty_iso_proObj_quotTower` is the transition map of the system of
reductions `{X ⊗_S S/𝔞ⁿ}`. -/
public theorem modIdealToQuot_comp_quotShiftToModIdeal (n : ℕ) :
    (X.modIdealToQuot 𝔞 U hU hd hlo).app (op (n + c)) ≫
        (X.quotShiftToModIdeal 𝔞 c U hU hd hhi).app (op n) =
      (X.modIdealTower 𝔞).map (opHomOfLE (Nat.le_add_right n c)) := by
  refine ChainMap.ext ?_ ?_ <;>
    exact LinearMap.ext fun z => by
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z; rfl

/-- The second composite of the interleaving of
`NaiveCotangent.TwoTerm.nonempty_iso_proObj_quotTower` is the transition map of the system of
quotients `{X / (Uₙ, 𝔞ⁿ X₀)}`. -/
public theorem quotShiftToModIdeal_comp_modIdealToQuot (n : ℕ) :
    (X.quotShiftToModIdeal 𝔞 c U hU hd hhi).app (op n) ≫
        (X.modIdealToQuot 𝔞 U hU hd hlo).app (op n) =
      (X.quotTower 𝔞 U hU hd).map (opHomOfLE (Nat.le_add_right n c)) := by
  refine ChainMap.ext ?_ ?_ <;>
    exact LinearMap.ext fun z => by
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z; rfl

end TwoTerm

end NaiveCotangent

/-! ## Adic completeness of the terms of the completed naive cotangent complex -/

namespace Rig

namespace AdicFiniteTypeAlgebra

universe u v w

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Every finite module over an object `B` of the category of Stacks 0AL4 whose base ring is
Noetherian is `I`-adically complete: `B` is Noetherian and `IB` lies in its Jacobson radical,
so the adic filtration of a finite module is separated and Stacks 031B applies. -/
@[ega "0 7.3.6" "more general", ega "0 7.8.1", ega "IV 18.5.16" "more general"]
public theorem isAdicComplete_of_finite [IsNoetherianRing A]
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (M : Type w) [AddCommGroup M]
    [Module B.carrier M] [Module.Finite B.carrier M] :
    IsAdicComplete B.adicIdeal M := by
  have hB : IsAdicComplete B.adicIdeal B.carrier := B.isAdicallyComplete
  have hhaus : IsHausdorff B.adicIdeal M :=
    IsHausdorff.of_le_jacobson _ _ (IsAdicComplete.le_jacobson_bot _)
  exact isAdicComplete_of_iInf_smul_eq_bot B.adicIdeal hhaus.iInf_pow_smul

end AdicFiniteTypeAlgebra

namespace CompletedPolynomialPresentation

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  (P : CompletedPolynomialPresentation I B)

/-- The conormal module `J / J²` of a completed polynomial presentation is a finite
`B`-module: `J` is an ideal of the Noetherian ring `A⟨x⟩`, hence finitely generated. -/
public theorem finite_cotangent [IsNoetherianRing A] :
    Module.Finite B.carrier P.extension.Cotangent := by
  have : IsNoetherianRing P.extension.Ring := AdicCompletion.isNoetherianRing _
  exact Algebra.Extension.Cotangent.finite (IsNoetherian.noetherian _)

/-- The conormal module `J / J²` of a completed polynomial presentation is `I`-adically
complete, being a finite module over `B`. -/
public theorem isAdicComplete_cotangent [IsNoetherianRing A] :
    IsAdicComplete B.adicIdeal P.extension.Cotangent := by
  have := P.finite_cotangent
  exact B.isAdicComplete_of_finite _

/-- The degree-`0` term `⨁ᵢ B dxᵢ` of the completed naive cotangent complex of a presentation
is `I`-adically complete, being a finite free `B`-module. -/
public theorem isAdicComplete_differentials [IsNoetherianRing A] :
    IsAdicComplete B.adicIdeal (Fin P.variableCount → B.carrier) :=
  B.isAdicComplete_of_finite _

end CompletedPolynomialPresentation

/-! ## Stacks 0AJS (2) -/

namespace CompletedNaiveCotangentComplex

universe u v

open NaiveCotangent NaiveCotangent.TwoTerm Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  {P : CompletedPolynomialPresentation I B}

/-- The cochain-complex realization of the two-term reading of `NL^∧_{B/A}` is `NL^∧_{B/A}`
read as a cochain complex. -/
public theorem cochainComplexOf_twoTerm (K : CompletedNaiveCotangentComplex P) :
    K.twoTerm.cochainComplexOf = K.cochainComplex := rfl

/-- The cone over `{NL^∧_{B/A} ⊗_B Bₙ}`, realized by cochain complexes, with vertex
`NL^∧_{B/A}` and the reduction maps as legs. -/
public def completedReductionTowerCone (K : CompletedNaiveCotangentComplex P) :
    Cone (K.completedReductionTower ⋙ cochainComplexFunctor B.carrier) :=
  (cochainComplexFunctor B.carrier).mapCone (K.twoTerm.modIdealTowerCone B.adicIdeal)

/-- **`NL^∧_{B/A}` is the inverse limit of `{NL^∧_{B/A} ⊗_B Bₙ}`.**  Both terms of
`NL^∧_{B/A}` are finite modules over the Noetherian ring `B`, hence `I`-adically complete, so
the limit is computed degreewise by the adic completeness of `J / J²` and of `⨁ᵢ B dxᵢ`. -/
public def isLimitCompletedReductionTowerCone [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) : IsLimit K.completedReductionTowerCone := by
  have h₁ : IsAdicComplete B.adicIdeal P.extension.Cotangent := P.isAdicComplete_cotangent
  have h₀ : IsAdicComplete B.adicIdeal (Fin P.variableCount → B.carrier) :=
    P.isAdicComplete_differentials
  refine HomologicalComplex.isLimitOfEval _ _ fun i => ?_
  by_cases hm1 : i = -1
  · subst hm1
    exact AdicCompletion.isLimitOfAdicQuotientSystem B.adicIdeal
      (M := P.extension.Cotangent)
      K.twoTerm.cochainEquiv₁
      (fun n => (K.twoTerm.modIdeal (B.adicIdeal ^ n)).cochainEquiv₁)
      (fun h x =>
        cochainEquiv₁_cochainMapOf (K.twoTerm.modIdealMap (Ideal.pow_le_pow_right h)) x)
      (fun _ x => cochainEquiv₁_cochainMapOf (K.twoTerm.quotProj _ _ _) x)
  · by_cases h0 : i = 0
    · subst h0
      exact AdicCompletion.isLimitOfAdicQuotientSystem B.adicIdeal
        (M := Fin P.variableCount → B.carrier)
        K.twoTerm.cochainEquiv₀
        (fun n => (K.twoTerm.modIdeal (B.adicIdeal ^ n)).cochainEquiv₀)
        (fun h x =>
          cochainEquiv₀_cochainMapOf (K.twoTerm.modIdealMap (Ideal.pow_le_pow_right h)) x)
        (fun _ x => cochainEquiv₀_cochainMapOf (K.twoTerm.quotProj _ _ _) x)
    · exact isLimitOfIsZero _ (isZero_cochainComplexOf_X K.twoTerm hm1 h0)
        fun _ => isZero_cochainComplexOf_X _ hm1 h0

/-- The cone over `{NL_{Bₙ/Aₙ}}`, realized by cochain complexes, with vertex `NL^∧_{B/A}`: the
leg at level `n` is the reduction of `NL^∧_{B/A}` modulo the image of `J ∩ Iⁿ A⟨x⟩` in degree
`-1` and modulo `IⁿB` in degree `0`. -/
public def reductionTowerCone (K : CompletedNaiveCotangentComplex P) :
    Cone (K.reductionTower ⋙ cochainComplexFunctor B.carrier) :=
  (Cone.postcompose (Functor.whiskerRight
    (K.twoTerm.modIdealToQuot B.adicIdeal P.conormalSub P.conormalSub_antitone
      K.conormalSub_le_comap_differential P.smul_top_le_conormalSub)
    (cochainComplexFunctor B.carrier))).obj K.completedReductionTowerCone

/-- **`NL^∧_{B/A}` is the inverse limit of `{NL_{Bₙ/Aₙ}}`.**  The two systems
`{NL^∧_{B/A} ⊗_B Bₙ}` and `{NL_{Bₙ/Aₙ}}` are strictly pro-isomorphic by Stacks 0AJS (1), and
an interleaving with a uniform shift transports the limit cone of the first system to a limit
cone of the second. -/
public theorem nonempty_isLimit_reductionTowerCone [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) : Nonempty (IsLimit K.reductionTowerCone) := by
  obtain ⟨c, -, hc⟩ := P.exists_conormalSub_le_smul_top
  have hhi : ∀ n : ℕ, P.conormalSub (n + c) ≤
      (B.adicIdeal ^ n • ⊤ : Submodule B.carrier P.extension.Cotangent) := by
    intro n
    have h := hc (n + c) (Nat.le_add_left c n)
    rwa [Nat.add_sub_cancel] at h
  refine ⟨isLimitPostcomposeOfInterleaved c
    (Functor.whiskerRight
      (K.twoTerm.modIdealToQuot B.adicIdeal P.conormalSub P.conormalSub_antitone
        K.conormalSub_le_comap_differential P.smul_top_le_conormalSub)
      (cochainComplexFunctor B.carrier))
    (Functor.whiskerRight (K.twoTerm.quotShiftToModIdeal B.adicIdeal c P.conormalSub
      P.conormalSub_antitone K.conormalSub_le_comap_differential hhi)
      (cochainComplexFunctor B.carrier)) (fun n => ?_) (fun n => ?_)
    K.isLimitCompletedReductionTowerCone⟩
  all_goals rw [Functor.whiskerRight_app, Functor.whiskerRight_app,
    ← (cochainComplexFunctor B.carrier).map_comp]
  · rw [K.twoTerm.modIdealToQuot_comp_quotShiftToModIdeal B.adicIdeal c P.conormalSub
        P.conormalSub_antitone K.conormalSub_le_comap_differential
        P.smul_top_le_conormalSub hhi n]
    rfl
  · rw [K.twoTerm.quotShiftToModIdeal_comp_modIdealToQuot B.adicIdeal c P.conormalSub
        P.conormalSub_antitone K.conormalSub_le_comap_differential
        P.smul_top_le_conormalSub hhi n]
    rfl

/-- **Stacks 0AJS (2).**  Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an object of
the category of Stacks 0AL4, presented as `B = A⟨x₁, …, x_r⟩ / J`.  Then the completed naive
cotangent complex is the derived inverse limit of the naive cotangent complexes of the
reductions, `NL^∧_{B/A} = R lim NL_{Bₙ/Aₙ}` in `D(B)`: the inverse system `{NL_{Bₙ/Aₙ}}` has
surjective transition maps and `NL^∧_{B/A}` is its ordinary inverse limit. -/
@[stacks 0AJS "part (2)"]
public theorem isDerivedLimit_reductionTower [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} B.carrier)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedLimit ((K.reductionTower ⋙ cochainComplexFunctor B.carrier) ⋙
      DerivedCategory.Q) (DerivedCategory.Q.obj K.cochainComplex) := by
  have hepi : ∀ n : ℕ, Epi ((K.reductionTower ⋙ cochainComplexFunctor B.carrier).map
      (homOfLE (Nat.le_succ n)).op) := fun _ =>
    epi_cochainMapOf _ (K.twoTerm.surjective_quotByMap_f₁ _ _ _ _)
      (K.twoTerm.surjective_quotByMap_f₀ _ _ _ _)
  obtain ⟨hlim⟩ := K.nonempty_isLimit_reductionTowerCone
  exact DerivedCategory.isDerivedLimit_of_limit_cone_of_epi _ K.reductionTowerCone hlim

end CompletedNaiveCotangentComplex

end Rig

end
