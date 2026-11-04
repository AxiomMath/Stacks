module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essentially of finite type and of finite presentation are stable under composition

All rings are commutative with unit; a ring map is a unital ring homomorphism `f : R -> S`,
and `S` is viewed as an `R`-algebra via `f`.

An `R`-algebra `A` is *of finite type* if it is generated as an `R`-algebra by finitely many
elements, i.e. there is a surjective `R`-algebra map `R[x_1, ..., x_n] ->> A`, and *of finite
presentation* if it is `R`-isomorphic to `R[x_1, ..., x_n] / I` for a finitely generated ideal
`I`. A *localization* of a ring `A` is `T^{-1} A` for a multiplicatively closed subset `T`
containing `1`, together with the canonical map `A -> T^{-1} A`; following the Stacks
convention `T` is an arbitrary multiplicative subset, not necessarily a prime complement.

Then (Stacks tag 00QM) `R -> S` is *essentially of finite type* if `S` is, up to `R`-algebra
isomorphism, a localization of an `R`-algebra of finite type, and *essentially of finite
presentation* if `S` is, up to `R`-algebra isomorphism, a localization of an `R`-algebra of
finite presentation. Both classes are stable under composition; this is Stacks tag 07DS,
Lemma 10.54.2.

For "essentially of finite type" we use Mathlib's `RingHom.EssFiniteType`, whose definition —
an algebra is a localization of a finitely generated subalgebra — matches tag 00QM (1), so the
first statement is `RingHom.EssFiniteType.comp`. Mathlib has no predicate for "essentially of
finite presentation", so `RingHom.EssentiallyOfFinitePresentation` is introduced here after
tag 00QM (2): there is an intermediate `R`-algebra `A` of finite presentation, `S` carries a
compatible `A`-algebra structure (`IsScalarTower R A S`, so `R -> S` factors through `A`), and
`S` is a localization `T^{-1} A` of `A` at some submonoid `T`, encoded by `IsLocalization T S`.
Up to `R`-algebra isomorphism that is precisely the tag 00QM (2) condition.
-/

@[expose] public section

universe u v w uC

/-- A ring map `f : R -> S` is *essentially of finite presentation* if `S` is,
as an `R`-algebra, a localization of an `R`-algebra of finite presentation.

Concretely: there exist an `R`-algebra `A` of finite presentation, a compatible
`A`-algebra structure on `S` (so that the structure map `R -> S` agrees with
`R -> A -> S`), and a submonoid `T` of `A` exhibiting `S` as the localization
`T^{-1} A`. This is the Stacks Tag 00QM (2) condition, stated up to `R`-algebra
isomorphism. -/
def RingHom.EssentiallyOfFinitePresentation {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra A S)
    (_ : IsScalarTower R A S) (_ : Algebra.FinitePresentation R A) (T : Submonoid A),
    IsLocalization T S

/-- Re-present a finitely presented localization witness in a smaller universe. -/
private theorem essFP_reuniverse_aux
    {R : Type u} {T : Type w} [CommRing R] [CommRing T] [Algebra R T]
    (C : Type uC) [CommRing C] [Algebra R C] [Algebra C T]
    [IsScalarTower R C T] [Algebra.FinitePresentation R C]
    (U : Submonoid C) [IsLocalization U T] :
    ∃ (A' : Type (max u w)) (_ : CommRing A') (_ : Algebra R A') (_ : Algebra A' T)
      (_ : IsScalarTower R A' T) (_ : Algebra.FinitePresentation R A') (U' : Submonoid A'),
      IsLocalization U' T := by
  -- `Algebra.FinitePresentation.iff` gives `n`, an ideal `I` with `I.FG`, and an `R`-algebra
  -- isomorphism `MvPolynomial (Fin n) R ⧸ I ≃ₐ[R] C`. Take
  -- `A' := ULift.{w} (MvPolynomial (Fin n) R ⧸ I)` and pull the `C`-algebra structure on `T`
  -- back to `A'` along the resulting `e : A' ≃ₐ[R] C`, with `U' := U.comap e`. The same
  -- pullback instance is used for the tower and the localization, to avoid a diamond.
  obtain ⟨n, I, fpIso, hIfg⟩ := Algebra.FinitePresentation.iff.mp ‹Algebra.FinitePresentation R C›
  let ue : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    ULift.algEquiv
  let e : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R] C := ue.trans fpIso
  let eR : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) ≃+* C := e.toRingEquiv
  let instA'T : Algebra (ULift.{w} (MvPolynomial (Fin n) R ⧸ I)) T :=
    ((algebraMap C T).comp
      (eR : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) →+* C)).toAlgebra
  refine ⟨ULift.{w} (MvPolynomial (Fin n) R ⧸ I), inferInstance, inferInstance, instA'T, ?_,
    Algebra.FinitePresentation.equiv e.symm,
    Submonoid.comap (eR : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) →+* C) U, ?_⟩
  · refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    change algebraMap R T a =
      (algebraMap C T) (e (algebraMap R (ULift.{w} (MvPolynomial (Fin n) R ⧸ I)) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  · exact IsLocalization.of_ringEquiv_left (M₁ := U) (e := eR)
      (Submonoid.map_comap_eq_of_surjective eR.surjective _) fun _ => rfl

-- needed: the `rw` in `essFP_descent` matches only when defeq unfolds the localization
-- `IsLocalization` data past the default transparency
set_option backward.isDefEq.respectTransparency false in
/-- **Descent of finite presentation along a localization (Stacks Tag 053N).**
If `S` is a localization of `A` at the submonoid `M`, and `B` is a finitely
presented `S`-algebra, then `B` is itself the localization (at some submonoid
`N`) of a finitely presented `A`-algebra `B₀`.

Mathematical argument (Stacks Tag 053N specialized to localizations).
Write `S = M⁻¹A`.  Because `B` is finitely presented over `S` there are
generators `b₁,…,bₙ ∈ B` and relations `r₁,…,r_k ∈ S[x₁,…,xₙ]` with
`B ≅ S[x₁,…,xₙ]/(r₁,…,r_k)`.  Each coefficient of each `rⱼ` lies in `S = M⁻¹A`,
hence is of the form `aᵢ/mᵢ` with `aᵢ ∈ A`, `mᵢ ∈ M`.  Clearing these finitely
many denominators (multiply each `rⱼ` by the product of the relevant `mᵢ`,
which is a unit in `S` and therefore does not change the ideal it generates over
`S`) we obtain relations `r̃ⱼ ∈ A[x₁,…,xₙ]`.  Set
`B₀ := A[x₁,…,xₙ]/(r̃₁,…,r̃_k)`, a finitely presented `A`-algebra.  Base change
along `A → S = M⁻¹A` localizes `A[x]` at (the image of) `M`, and since the
`r̃ⱼ` and `rⱼ` generate the same ideal after inverting `M`, we get
`M⁻¹B₀ ≅ S[x]/(r) ≅ B` as `A`-algebras.  Concretely the canonical map
`B₀ → B` exhibits `B` as the localization of `B₀` at `N := (algebraMap A B₀) '' M`
(the image of `M` in `B₀`), because inverting `M` on `B₀ = A[x]/(r̃)` produces
`S[x]/(r) = B`.  This is exactly the localization-base-change fact `IsLocalization` enjoys:
`B = N⁻¹ B₀` with `N` the image submonoid of `M`. -/
@[ega "IV 18.6.1" "partial"]
theorem essFP_descent
    {A : Type u} [CommRing A] (M : Submonoid A)
    {S : Type v} [CommRing S] [Algebra A S] [IsLocalization M S]
    (B : Type w) [CommRing B] [Algebra S B] [Algebra A B] [IsScalarTower A S B]
    [Algebra.FinitePresentation S B] :
    ∃ (B₀ : Type (max u w)) (_ : CommRing B₀) (_ : Algebra A B₀)
      (_ : Algebra.FinitePresentation A B₀) (_ : Algebra B₀ B)
      (_ : IsScalarTower A B₀ B) (N : Submonoid B₀),
      IsLocalization N B := by
  -- Present `B ≅ S[x₁..xₙ]/I` over `S` (`Algebra.FinitePresentation.iff`), descend the
  -- f.g. relations from `S[x]` to `A[x]` by clearing denominators to get a f.g. ideal
  -- `J` with `J.map = I`, set `C₀ := A[x]/J` (Type u), prove `B = N⁻¹ C₀` via
  -- `IsLocalization.of_surjective`, then re-present `C₀` in `Type (max u w)` via `ULift`.
  classical
  obtain ⟨n, I, eB, hIfg⟩ := Algebra.FinitePresentation.iff.mp ‹Algebra.FinitePresentation S B›
  let instPAPS : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) :=
    MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := Fin n) M S
  let gB : MvPolynomial (Fin n) S →+* B := (eB.toAlgHom.toRingHom).comp (Ideal.Quotient.mk I)
  have hgB_surj : Function.Surjective gB := eB.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker gB = I := by
    change RingHom.ker ((eB.toAlgHom.toRingHom).comp (Ideal.Quotient.mk I)) = I
    rw [← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot eB.toAlgHom.toRingHom).mp eB.injective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  obtain ⟨J, hJfg, hJmap⟩ :
      ∃ J : Ideal (MvPolynomial (Fin n) A),
        J.FG ∧ J.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S)) = I := by
    obtain ⟨s, hs⟩ := hIfg
    let W := M.map (MvPolynomial.C (σ := Fin n))
    let num : MvPolynomial (Fin n) S → MvPolynomial (Fin n) A :=
      fun g => (IsLocalization.surj W g).choose.fst
    let den : MvPolynomial (Fin n) S → W := fun g => (IsLocalization.surj W g).choose.snd
    have hnum : ∀ g, g * algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) (den g)
        = algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) (num g) :=
      fun g => (IsLocalization.surj W g).choose_spec
    refine ⟨Ideal.span (num '' ↑s), Submodule.fg_span (s.finite_toSet.image num), ?_⟩
    rw [Ideal.map_span, ← hs]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨a, ⟨g, hg, rfl⟩, rfl⟩
      rw [← hnum]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span hg)
    · rw [Ideal.span_le]
      intro g hg
      obtain ⟨u, hu⟩ := (IsLocalization.map_units (MvPolynomial (Fin n) S) (den g) :
        IsUnit (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) (den g)))
      have hgmem : algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) (num g)
          ∈ Ideal.span ((algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S)) '' (num ''
              ↑s)) :=
        Ideal.subset_span ⟨num g, ⟨g, hg, rfl⟩, rfl⟩
      have hg2 : g = (↑u⁻¹ : MvPolynomial (Fin n) S)
          * algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) (num g) := by
        rw [← hnum, ← hu, mul_comm g (↑u : MvPolynomial (Fin n) S), ← mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_mul]
      rw [hg2]; exact Ideal.mul_mem_left _ _ hgmem
  have fpAC₀ : Algebra.FinitePresentation A (MvPolynomial (Fin n) A ⧸ J) :=
    Algebra.FinitePresentation.quotient hJfg
  let φPA : MvPolynomial (Fin n) A →+* B :=
    gB.comp (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S))
  have hJle : J ≤ RingHom.ker φPA := fun x hx => by
    change gB (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) x) = 0
    rw [← RingHom.mem_ker, hker, ← hJmap]
    exact Ideal.mem_map_of_mem _ hx
  let φC₀ : (MvPolynomial (Fin n) A ⧸ J) →+* B := Ideal.Quotient.lift J φPA hJle
  let instC₀B : Algebra (MvPolynomial (Fin n) A ⧸ J) B := φC₀.toAlgebra
  have towerAC₀B : IsScalarTower A (MvPolynomial (Fin n) A ⧸ J) B := by
    refine @IsScalarTower.of_algebraMap_eq A (MvPolynomial (Fin n) A ⧸ J) B _ _ _ _ instC₀B _
      (fun a => ?_)
    change algebraMap A B a = gB (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S)
      (algebraMap A (MvPolynomial (Fin n) A) a))
    rw [← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S),
      IsScalarTower.algebraMap_apply A S (MvPolynomial (Fin n) S)]
    change algebraMap A B a = eB (algebraMap S (MvPolynomial (Fin n) S ⧸ I) (algebraMap A S a))
    rw [eB.commutes, ← IsScalarTower.algebraMap_apply A S B]
  have locNB : IsLocalization
      ((M.map (MvPolynomial.C (σ := Fin n))).map (Ideal.Quotient.mk J)) B := by
    refine IsLocalization.of_surjective (M.map (MvPolynomial.C (σ := Fin n)))
      (MvPolynomial (Fin n) S) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective gB hgB_surj ?_ ?_
    · refine RingHom.ext fun x => ?_
      change gB (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) S) x)
        = φC₀ (Ideal.Quotient.mk J x)
      rw [Ideal.Quotient.lift_mk]
      rfl
    · rw [hker, Ideal.mk_ker, hJmap]
  -- Re-present `C₀ : Type u` in `Type (max u w)`.
  obtain ⟨B₀, _, _, _, _, hfp, N, _⟩ :=
    essFP_reuniverse_aux (R := A) (T := B) (MvPolynomial (Fin n) A ⧸ J)
      ((M.map (MvPolynomial.C (σ := Fin n))).map (Ideal.Quotient.mk J))
  exact ⟨B₀, inferInstance, inferInstance, hfp, inferInstance, inferInstance, N, inferInstance⟩

/-- **Universe re-presentation for essentially-finite-presentation witnesses.**
A finitely presented `R`-algebra `C` together with a localization `IsLocalization U T`
of it can always be re-presented by a finitely presented `R`-algebra `A'` living
in the smaller universe `Type (max u w)` (where `R : Type u`, `T : Type w`),
carrying a compatible `T`-localization structure.  Indeed every finitely
presented `R`-algebra is `R`-isomorphic to `MvPolynomial ι R ⧸ I` with `ι`
finite and `I` finitely generated, an object in `Type u ⊆ Type (max u w)`;
transport the algebra structure on `T` and the localization data across this
`R`-algebra isomorphism. -/
theorem essFP_reuniverse
    {R : Type u} {T : Type w} [CommRing R] [CommRing T] [Algebra R T]
    (C : Type uC) [CommRing C] [Algebra R C] [Algebra C T]
    [IsScalarTower R C T] [Algebra.FinitePresentation R C]
    (U : Submonoid C) [IsLocalization U T] :
    ∃ (A' : Type (max u w)) (_ : CommRing A') (_ : Algebra R A') (_ : Algebra A' T)
      (_ : IsScalarTower R A' T) (_ : Algebra.FinitePresentation R A') (U' : Submonoid A'),
      IsLocalization U' T :=
  essFP_reuniverse_aux C U

/-- **Statement 1.** The class of ring maps essentially of finite type is
preserved under composition (Stacks Tag 07DS, first assertion). -/
@[stacks 07DS "(1)", ega "IV 1.3.9"]
theorem essFiniteType_comp {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.EssFiniteType) (hg : g.EssFiniteType) : (g.comp f).EssFiniteType :=
  hf.comp hg

/-- **Statement 2.** The class of ring maps essentially of finite presentation
is preserved under composition (Stacks Tag 07DS, second assertion).

The proof combines Stacks tag 053N, transitivity of finite presentation,
localization-of-localization, and a universe re-presentation:

1. Unpack `hf`: f.p. `R`-algebra `A`, with `S = M⁻¹A` (`IsLocalization M S`).
   Unpack `hg`: f.p. `S`-algebra `B`, with `T = N₂⁻¹B` (`IsLocalization N₂ T`).
2. `A` acts on `B` through `S` (`IsScalarTower A S B`).
3. `essFP_descent M B`: descend `B` to a f.p. `A`-algebra `B₀` with
   `B = N⁻¹B₀` (`IsLocalization N B`).
4. `Algebra.FinitePresentation.trans R A B₀`: since `A` is f.p./R and `B₀` is
   f.p./A, `B₀` is f.p./R.
5. localization-of-localization: `B = N⁻¹B₀` and `T = N₂⁻¹B`, so
   `T = U⁻¹B₀` for `U := localizationLocalizationSubmodule N N₂`
   (`IsLocalization.localization_localization_isLocalization`).
6. `essFP_reuniverse`: re-present the f.p. `R`-algebra `B₀ : Type (max u v w)`
   (with its localization `IsLocalization U T`) by a f.p. `R`-algebra
   `A' : Type (max u w)` carrying `IsLocalization U' T`, matching the universe
   demanded by `RingHom.EssentiallyOfFinitePresentation` for `g.comp f : R →+* T`. -/
@[stacks 07DS "(2)"]
theorem essFinitePresentation_comp {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.EssentiallyOfFinitePresentation) (hg : g.EssentiallyOfFinitePresentation) :
    (g.comp f).EssentiallyOfFinitePresentation := by
  -- Set up the algebra structures coming from the ring maps.
  let := f.toAlgebra
  let := g.toAlgebra
  let := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Unpack the two hypotheses.
  obtain ⟨A, instA, algRA, algAS, towerRAS, fpRA, M, locMS⟩ := hf
  obtain ⟨B, instB, algSB, algBT, towerSBT, fpSB, N₂, locN₂T⟩ := hg
  -- `A` acts on `B` through `S`.
  let : Algebra A B := ((algebraMap S B).comp (algebraMap A S)).toAlgebra
  have : IsScalarTower A S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Step 3: descend `B` to a f.p. `A`-algebra `B₀` with `B = N⁻¹ B₀`.
  obtain ⟨B₀, instB₀, algAB₀, fpAB₀, algB₀B, towerAB₀B, N, locNB⟩ :=
    essFP_descent (S := S) M B
  -- Step 5: assemble the algebra/scalar-tower data so that `T` is a localization
  -- of `B₀` (localization of a localization).
  -- `R → B₀` is the composite `R → A → B₀`.
  let : Algebra R B₀ := ((algebraMap A B₀).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A B₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra B₀ T := ((algebraMap B T).comp (algebraMap B₀ B)).toAlgebra
  have : IsScalarTower B₀ B T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Step 4: `B₀` is f.p. over `R` by transitivity through `A`.
  have : Algebra.FinitePresentation R B₀ := Algebra.FinitePresentation.trans R A B₀
  -- `R → T` factors through `B₀`. The structure map `R → T` is
  -- `algebraMap R T = (g.comp f)` which equals `R → A → S → B → T = R → A → B₀ → B → T`,
  -- and `R → A → B₀ → T` is exactly `algebraMap R B₀` composed with `algebraMap B₀ T`.
  have : IsScalarTower R B₀ T := IsScalarTower.of_algebraMap_eq fun x => by
    -- Compatibility of structure maps; both sides reduce to the common composite
    -- `R → A → B₀ → B → T`.
    change algebraMap R T x = algebraMap B T (algebraMap B₀ B (algebraMap A B₀ (algebraMap R A x)))
    rw [← IsScalarTower.algebraMap_apply A B₀ B, IsScalarTower.algebraMap_apply A S B,
      IsScalarTower.algebraMap_apply R S T, IsScalarTower.algebraMap_apply S B T,
      IsScalarTower.algebraMap_apply R A S]
  -- Step 5: `T` is a localization of `B₀` at `U := localizationLocalizationSubmodule N N₂`,
  -- by the localization-of-localization principle applied to `IsLocalization N B`
  -- (B = N⁻¹B₀) and `IsLocalization N₂ T` (T = N₂⁻¹B).
  have := IsLocalization.localization_localization_isLocalization N N₂ T
  -- Step 6: re-present `B₀ : Type (max u v w)` in `Type (max u w)`.
  exact essFP_reuniverse B₀ (IsLocalization.localizationLocalizationSubmodule N N₂)

/-! ### Transport along a lifting of universes -/

universe x y

/-- **Essential finite presentation is preserved by lifting both rings into larger universes.**
`ULift R → ULift S` is `R → S` read through the lifting isomorphisms, so the intermediate algebra
`A` of the definition may simply be lifted too: `ULift A` is of finite presentation over `ULift R`
because it is `R`-isomorphic to `A`, hence of finite presentation over `R`, and `ULift R` is of
finite type over `R`; and the localization transports along the two surjections `A → ULift A` and
`S → ULift S`.

This is what reduces a statement about rings and modules in several universes to the same statement
in one universe, which is the shape the spreading-out results 00QV and 00QX have. -/
public lemma RingHom.EssentiallyOfFinitePresentation.ulift {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) :
    letI : Algebra (ULift.{x} R) (ULift.{y} S) := ULift.algebra' R (ULift.{y} S)
    (algebraMap (ULift.{x} R) (ULift.{y} S)).EssentiallyOfFinitePresentation := by
  let algR'S' : Algebra (ULift.{x} R) (ULift.{y} S) := ULift.algebra' R (ULift.{y} S)
  let eS : ULift.{y} S ≃+* S := ULift.ringEquiv
  let algRS : Algebra R S := (algebraMap R S).toAlgebra
  obtain ⟨A, instA, instRA, instAS, instTow, instFP, T, instLoc⟩ := hS
  let eA : ULift.{max u v x y} A ≃+* A := ULift.ringEquiv
  let algR'A' : Algebra (ULift.{x} R) (ULift.{max u v x y} A) :=
    ULift.algebra' R (ULift.{max u v x y} A)
  let algA'S' : Algebra (ULift.{max u v x y} A) (ULift.{y} S) :=
    ULift.algebra' A (ULift.{y} S)
  let algR'S'' : Algebra (ULift.{x} R) (ULift.{y} S) :=
    (algebraMap (ULift.{x} R) (ULift.{y} S)).toAlgebra
  have hftRR' : Algebra.FiniteType R (ULift.{x} R) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId R (ULift.{x} R)) fun z => ⟨z.down, rfl⟩
  have hfpRA' : Algebra.FinitePresentation R (ULift.{max u v x y} A) :=
    Algebra.FinitePresentation.equiv (ULift.algEquiv (R := R) (A := A)).symm
  have htowRR'A' : IsScalarTower R (ULift.{x} R) (ULift.{max u v x y} A) :=
    ⟨fun a b c => by
      ext
      exact mul_smul a b.down c.down⟩
  have hfpR'A' : Algebra.FinitePresentation (ULift.{x} R) (ULift.{max u v x y} A) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R
      (ULift.{x} R) (ULift.{max u v x y} A)
  have hlocA' : IsLocalization
      (Submonoid.map (eA.symm : A →+* ULift.{max u v x y} A) T) (ULift.{y} S) :=
    IsLocalization.of_surjective T S (eA.symm : A →+* ULift.{max u v x y} A) eA.symm.surjective
      (eS.symm : S →+* ULift.{y} S) eS.symm.surjective rfl
      (((RingHom.injective_iff_ker_eq_bot _).mp eS.symm.injective).trans_le bot_le)
  refine ⟨ULift.{max u v x y} A, inferInstance, algR'A', algA'S', ?_, hfpR'A',
    Submonoid.map (eA.symm : A →+* ULift.{max u v x y} A) T, hlocA'⟩
  refine IsScalarTower.of_algebraMap_eq fun z => ?_
  ext
  exact IsScalarTower.algebraMap_apply R A S z.down
