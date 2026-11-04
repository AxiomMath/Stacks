module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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

/-!
# A local homomorphism as a colimit of local maps essentially of finite type
-/

/-!
# A local homomorphism is a colimit of maps essentially of finite type over `ℤ`

All rings are commutative with unit and all ring homomorphisms send `1` to `1`.

A local ring is a ring with exactly one maximal ideal `m_R`, and a ring homomorphism
`φ : R → S` between local rings is a local homomorphism when `φ(m_R) ⊆ m_S`, equivalently
`φ⁻¹(m_S) = m_R`.

A ring homomorphism `R → S` is essentially of finite type when `S` is, as an `R`-algebra, a
localization of an `R`-algebra of finite type, equivalently
`S ≅ T⁻¹(R[x_1,…,x_n]/I)` for some `n`, ideal `I` and multiplicative set `T`. A ring `A` is
essentially of finite type over `ℤ` when the unique map `ℤ → A` is.

A system of ring maps over a directed set `(Λ, ≤)` consists of directed systems of rings
`(R_λ, r_{λμ})` and `(S_λ, s_{λμ})` together with a morphism of directed systems
`ψ = (ψ_λ : R_λ → S_λ)`. Its colimit is the induced map `colim R_λ → colim S_λ`.

## Main result

Let `φ : R → S` be a local homomorphism of local rings. Then there exist a directed set
`(Λ, ≤)` and a system of local homomorphisms `ψ_λ : R_λ → S_λ` of local rings such that

1. the colimit of the system `R_λ → S_λ` is `R → S`;
2. each `R_λ` is essentially of finite type over `ℤ`; and
3. each `S_λ` is essentially of finite type over `R_λ`, via `ψ_λ`.

## Notation

The Mathlib names used are `IsLocalRing` for a local ring; `IsLocalHom f` for a local
homomorphism, which for local rings is equivalent to `f(m_R) ⊆ m_S` and to
`f⁻¹(m_S) = m_R`; `RingHom.EssFiniteType f` for essentially of finite type;
`Ring.DirectLimit G f` for the colimit of a directed system of commutative rings, with
structure maps `Ring.DirectLimit.of`, universal map `Ring.DirectLimit.lift` and functorial
map `Ring.DirectLimit.map`; `DirectedSystem G f` for the directed-system laws `f_{ii} = id`
and `f_{jk} ∘ f_{ij} = f_{ik}`; and `IsDirectedOrder Λ` together with `Nonempty Λ` for a
directed set. Essentially of finite type over `ℤ` is `(Int.castRingHom A).EssFiniteType`.
-/

@[expose] public section


universe u

/-- The `IsLocalization.lift` of an injective ring hom is injective. -/
private theorem lift_injective_of_injective {A S P : Type*} [CommRing A] [CommRing S]
    [CommRing P] [Algebra A S] {M : Submonoid A} [IsLocalization M S] {g : A →+* P}
    (hg : ∀ y : M, IsUnit (g y)) (hinj : Function.Injective g) :
    Function.Injective (IsLocalization.lift hg : S →+* P) :=
  (IsLocalization.lift_injective_iff (S := S) hg).2 fun x y =>
    ⟨fun h => by
      rw [← IsLocalization.lift_eq (S := S) hg x, ← IsLocalization.lift_eq (S := S) hg y, h],
      fun h => by rw [hinj h]⟩

namespace Stacks.EssentialFiniteness.LocalColimitSystem

/-!
## The witness

Throughout fix a local homomorphism `φ : R → S` of local rings.

* The **index set** `Λ = Index` is the set of pairs `(A, B)` of *finitely
  generated* sub-`ℤ`-algebras `A ⊆ R`, `B ⊆ S` with `φ(A) ⊆ B`, ordered by
  componentwise inclusion.  (We use finitely generated sub-`ℤ`-algebras directly
  rather than finite generating subsets; the two index sets are cofinal and give
  the same colimit, and this presentation makes the order and the transition maps
  cleaner.)
* For a sub-`ℤ`-algebra `A ⊆ R` of a local ring `R`, `locAt R A` is the
  localization of `A` at the contracted prime `A ∩ 𝔪_R = (𝔪_R).comap A.val`.
  This is a local ring (`Localization.AtPrime.isLocalRing`).
* `transMap` is the transition map `locAt R A → locAt R A'` for `A ≤ A'`,
  induced by the inclusion `A ↪ A'` (elements outside the contracted prime of
  `A` stay outside that of `A'`, so the universal property of localization
  applies).
* `psiMap` is the local homomorphism `locAt R A → locAt S B` induced by `φ`
  (using `φ(A) ⊆ B` and `φ⁻¹(𝔪_S) = 𝔪_R`).
-/

/-- The local ring attached to a sub-`ℤ`-algebra `A` of a local ring `R`:
the localization of `A` at the prime `A ∩ 𝔪_R`. -/
noncomputable abbrev locAt (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Subalgebra ℤ R) : Type u :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).comap A.val)

/-- The canonical map `locAt R A → R`, extending the inclusion `A → R`. -/
noncomputable def locAt.toRing (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Subalgebra ℤ R) : locAt R A →+* R :=
  IsLocalization.lift (M := ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl) (g := A.val)
    fun y => IsLocalRing.notMem_maximalIdeal.mp y.property

/-- The canonical map `locAt R A → R` restricts to the inclusion on `A`. -/
@[simp]
theorem locAt.toRing_algebraMap (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Subalgebra ℤ R) (x : A) : locAt.toRing R A (algebraMap A (locAt R A) x) = x :=
  IsLocalization.lift_eq _ _

/-- The canonical map `locAt R A → R` is injective. -/
theorem locAt.toRing_injective (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Subalgebra ℤ R) : Function.Injective (locAt.toRing R A) :=
  lift_injective_of_injective (S := locAt R A)
    (M := ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl) _ Subtype.val_injective

/-- Every `r : R` is the image of an element of `locAt R A` for some finitely generated `A`. -/
private theorem exists_fg_toRing_eq (R : Type u) [CommRing R] [IsLocalRing R] (r : R) :
    ∃ A : Subalgebra ℤ R, A.FG ∧ ∃ x : locAt R A, locAt.toRing R A x = r :=
  let A : Subalgebra ℤ R := Algebra.adjoin ℤ (({r} : Finset R) : Set R)
  ⟨A, Subalgebra.fg_adjoin_finset _, algebraMap A (locAt R A) ⟨r, Algebra.subset_adjoin (by simp)⟩,
    locAt.toRing_algebraMap R A _⟩

/-- The transition map `locAt R A → locAt R A'` for an inclusion `A ≤ A'` of
sub-`ℤ`-algebras of the local ring `R`. -/
noncomputable def transMap (R : Type u) [CommRing R] [IsLocalRing R]
    (A A' : Subalgebra ℤ R) (h : A ≤ A') :
    locAt R A →+* locAt R A' :=
  IsLocalization.lift (M := ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl)
    (g := (algebraMap A' (locAt R A')).comp (Subalgebra.inclusion h)) fun y => by
      rw [RingHom.comp_apply]
      exact IsLocalization.map_units (M := ((IsLocalRing.maximalIdeal R).comap A'.val).primeCompl)
        _ ⟨_, IsLocalRing.notMem_maximalIdeal.2
          ((IsLocalRing.notMem_maximalIdeal (x := A.val y)).mp y.property)⟩

/-- The transition map restricts to the inclusion `A ↪ A'`. -/
@[simp]
theorem transMap_algebraMap (R : Type u) [CommRing R] [IsLocalRing R]
    (A A' : Subalgebra ℤ R) (h : A ≤ A') (x : A) :
    transMap R A A' h (algebraMap A (locAt R A) x) =
      algebraMap A' (locAt R A') (Subalgebra.inclusion h x) := by
  rw [transMap, IsLocalization.lift_eq]; rfl

/-- The transition map for `A ≤ A` is the identity. -/
theorem transMap_self (R : Type u) [CommRing R] [IsLocalRing R] (A : Subalgebra ℤ R)
    (h : A ≤ A) : transMap R A A h = RingHom.id _ :=
  IsLocalization.ringHom_ext ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl <| by
    ext; simp

/-- The transition maps compose. -/
theorem transMap_comp_transMap (R : Type u) [CommRing R] [IsLocalRing R]
    (A A' A'' : Subalgebra ℤ R) (h : A ≤ A') (h' : A' ≤ A'') :
    (transMap R A' A'' h').comp (transMap R A A' h) = transMap R A A'' (h.trans h') :=
  IsLocalization.ringHom_ext ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl <| by
    ext; simp

/-- The transition maps are compatible with the canonical maps to `R`. -/
@[simp]
theorem locAt.toRing_transMap (R : Type u) [CommRing R] [IsLocalRing R]
    (A A' : Subalgebra ℤ R) (h : A ≤ A') (x : locAt R A) :
    locAt.toRing R A' (transMap R A A' h x) = locAt.toRing R A x := by
  refine DFunLike.congr_fun (IsLocalization.ringHom_ext
    ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl (j := (locAt.toRing R A').comp _)
    (k := locAt.toRing R A) ?_) x
  ext; simp

/-- The induced local homomorphism `locAt R A → locAt S B` whenever `φ(A) ⊆ B`. -/
noncomputable def psiMap (R S : Type u) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
    (A : Subalgebra ℤ R) (B : Subalgebra ℤ S) (hc : ∀ x ∈ A, φ x ∈ B) :
    locAt R A →+* locAt S B :=
  IsLocalization.lift (M := ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl)
    (g := (algebraMap B (locAt S B)).comp
      ((φ.comp A.val).codRestrict B fun x => (hc x x.2 : φ.comp A.val x ∈ B)))
    fun y => by
      rw [RingHom.comp_apply]
      exact IsLocalization.map_units (M := ((IsLocalRing.maximalIdeal S).comap B.val).primeCompl)
        _ ⟨_, IsLocalRing.notMem_maximalIdeal.2
          ((IsLocalRing.notMem_maximalIdeal.mp y.property).map φ)⟩

section PsiMap
variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  (φ : R →+* S) [IsLocalHom φ] (A : Subalgebra ℤ R) (B : Subalgebra ℤ S)
  (hc : ∀ x ∈ A, φ x ∈ B)

/-- `psiMap` restricts to `φ` on `A`. -/
@[simp]
theorem psiMap_algebraMap (x : A) :
    psiMap R S φ A B hc (algebraMap A (locAt R A) x) =
      algebraMap B (locAt S B) ⟨φ x, hc x x.2⟩ := by
  rw [psiMap, IsLocalization.lift_eq]; rfl

/-- `psiMap` is a local homomorphism. -/
theorem psiMap_isLocalHom : IsLocalHom (psiMap R S φ A B hc) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl a
  rw [psiMap, IsLocalization.lift_mk'] at ha
  have hx := isUnit_of_mul_isUnit_left ha
  rw [RingHom.comp_apply, IsLocalization.AtPrime.isUnit_to_map_iff (locAt S B)
    ((IsLocalRing.maximalIdeal S).comap B.val)] at hx
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  exact fun h => hx ((map_mem_nonunits_iff φ _).2 h)

/-- `psiMap` is compatible with `φ` and the canonical maps to `R` and `S`. -/
theorem locAt.toRing_psiMap (x : locAt R A) :
    φ (locAt.toRing R A x) = locAt.toRing S B (psiMap R S φ A B hc x) := by
  refine DFunLike.congr_fun (IsLocalization.ringHom_ext
    ((IsLocalRing.maximalIdeal R).comap A.val).primeCompl (j := φ.comp (locAt.toRing R A))
    (k := (locAt.toRing S B).comp (psiMap R S φ A B hc)) ?_) x
  ext; simp

end PsiMap

/-- If `A` is finitely generated, `locAt R A` is essentially of finite type over `ℤ`. -/
theorem locAt_essFiniteType (R : Type u) [CommRing R] [IsLocalRing R] (A : Subalgebra ℤ R)
    (hA : A.FG) : (Int.castRingHom (locAt R A)).EssFiniteType := by
  have := (Subalgebra.fg_iff_finiteType A).mp hA
  have : Algebra.EssFiniteType ℤ (locAt R A) :=
    Algebra.instEssFiniteTypeLocalization (R := ℤ) (S := A) _
  rw [Subsingleton.elim (Int.castRingHom _) (algebraMap ℤ (locAt R A))]
  exact RingHom.essFiniteType_algebraMap.mpr this

/-- A ring hom `φ` maps the bottom sub-`ℤ`-algebra into every sub-`ℤ`-algebra `B`. -/
theorem map_mem_of_mem_bot {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (B : Subalgebra ℤ S) : ∀ x ∈ (⊥ : Subalgebra ℤ R), φ x ∈ B := fun x hx => by
  obtain ⟨n, rfl⟩ := Algebra.mem_bot.1 hx
  simp

/-- The index set `Λ`: pairs of finitely generated sub-`ℤ`-algebras `(A, B)` of
`R`, `S` with `φ(A) ⊆ B`, ordered componentwise. -/
abbrev Index (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S) : Type u :=
  { p : Subalgebra ℤ R × Subalgebra ℤ S // p.fst.FG ∧ p.snd.FG ∧ ∀ x ∈ p.fst, φ x ∈ p.snd }

/-- The index set is directed: take componentwise joins of sub-`ℤ`-algebras. -/
instance instIsDirectedIndex (R S : Type u) [CommRing R] [CommRing S]
    (φ : R →+* S) : IsDirectedOrder (Index R S φ) := by
  constructor
  rintro ⟨⟨A, B⟩, hA, hB, hc⟩ ⟨⟨A', B'⟩, hA', hB', hc'⟩
  refine ⟨⟨(A ⊔ A', B ⊔ B'), hA.sup hA', hB.sup hB', fun x hx => ?_⟩,
    ⟨le_sup_left, le_sup_left⟩, ⟨le_sup_right, le_sup_right⟩⟩
  exact (sup_le (fun y hy => le_sup_left (a := B) (hc y hy))
    (fun y hy => le_sup_right (b := B') (hc' y hy)) : A ⊔ A' ≤ (B ⊔ B').comap φ.toIntAlgHom) hx

/-- The index set is nonempty: the pair of bottom subalgebras `(⊥, ⊥)` qualifies. -/
instance instNonemptyIndex (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S) :
    Nonempty (Index R S φ) :=
  ⟨⟨(⊥, ⊥), Subalgebra.fg_bot, Subalgebra.fg_bot, map_mem_of_mem_bot φ ⊥⟩⟩

section Witness
variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  (φ : R →+* S) [IsLocalHom φ]

/-- The family `R_λ = locAt R A` of local rings. -/
noncomputable abbrev locR (i : Index R S φ) : Type u := locAt R i.val.fst

/-- The family `S_λ = locAt S B` of local rings. -/
noncomputable abbrev locS (i : Index R S φ) : Type u := locAt S i.val.snd

/-- The transition maps `r_{λμ}`. -/
noncomputable def transR (i j : Index R S φ) (h : i ≤ j) : locR R S φ i →+* locR R S φ j :=
  transMap R i.val.fst j.val.fst h.1

/-- The transition maps `s_{λμ}`. -/
noncomputable def transS (i j : Index R S φ) (h : i ≤ j) : locS R S φ i →+* locS R S φ j :=
  transMap S i.val.snd j.val.snd h.2

/-- The family `ψ_λ : R_λ → S_λ` of local homomorphisms. -/
noncomputable def psi (i : Index R S φ) : locR R S φ i →+* locS R S φ i :=
  psiMap R S φ i.val.fst i.val.snd i.property.right.right

/-! ### Properties of the witness -/

/-- **(loc-hom)** Each `ψ_λ` is a local homomorphism. -/
theorem psi_isLocalHom (i : Index R S φ) : IsLocalHom (psi R S φ i) :=
  psiMap_isLocalHom R S φ _ _ _

omit [IsLocalRing S] [IsLocalHom φ] in
/-- **(dir-sys R)** The maps `r_{λμ}` form a directed system. -/
theorem transR_directedSystem :
    DirectedSystem (locR R S φ) (fun i j h => ⇑(transR R S φ i j h)) :=
  ⟨fun _ x => DFunLike.congr_fun (transMap_self R _ _) x,
    fun _ _ _ hij hjk x => DFunLike.congr_fun (transMap_comp_transMap R _ _ _ hij.1 hjk.1) x⟩

omit [IsLocalRing R] [IsLocalHom φ] in
/-- **(dir-sys S)** The maps `s_{λμ}` form a directed system. Same argument as
`transR_directedSystem`, for `S`. -/
theorem transS_directedSystem :
    DirectedSystem (locS R S φ) (fun i j h => ⇑(transS R S φ i j h)) :=
  ⟨fun _ x => DFunLike.congr_fun (transMap_self S _ _) x,
    fun _ _ _ hij hjk x => DFunLike.congr_fun (transMap_comp_transMap S _ _ _ hij.2 hjk.2) x⟩

/-- **(squares)** The squares commute: `ψ` is a morphism of directed systems,
`s_{λμ} ∘ ψ_λ = ψ_μ ∘ r_{λμ}`. -/
theorem psi_commutes :
    ∀ i j (h : i ≤ j),
      (psi R S φ j).comp (transR R S φ i j h) = (transS R S φ i j h).comp (psi R S φ i) :=
  fun i _ _ => IsLocalization.ringHom_ext
    ((IsLocalRing.maximalIdeal R).comap i.val.fst.val).primeCompl <| by
      ext; simp [psi, transR, transS]

omit [IsLocalRing S] [IsLocalHom φ] in
/-- **(2) ess. finite type over ℤ.** Each `R_λ = locAt R A` is essentially of
finite type over `ℤ`. -/
theorem locR_essFiniteType (i : Index R S φ) :
    (Int.castRingHom (locR R S φ i)).EssFiniteType :=
  locAt_essFiniteType R _ i.property.1

/-- **(3) ess. finite type over R_λ.** Each `ψ_λ : R_λ → S_λ` is essentially of
finite type. -/
theorem psi_essFiniteType (i : Index R S φ) :
    (psi R S φ i).EssFiniteType := by
  refine RingHom.EssFiniteType.of_comp (Int.castRingHom (locR R S φ i)) ?_
  rw [Subsingleton.elim ((psi R S φ i).comp _) (Int.castRingHom _)]
  exact locAt_essFiniteType S _ i.property.2.1

omit [IsLocalRing S] [IsLocalHom φ] in
/-- The maps `r_{λμ}` are compatible with the canonical maps to `R`. -/
@[simp]
theorem locAt.toRing_transR (i j : Index R S φ) (h : i ≤ j) (x : locR R S φ i) :
    locAt.toRing R j.val.fst (transR R S φ i j h x) = locAt.toRing R i.val.fst x :=
  locAt.toRing_transMap R _ _ h.1 x

omit [IsLocalRing R] [IsLocalHom φ] in
/-- The maps `s_{λμ}` are compatible with the canonical maps to `S`. -/
@[simp]
theorem locAt.toRing_transS (i j : Index R S φ) (h : i ≤ j) (x : locS R S φ i) :
    locAt.toRing S j.val.snd (transS R S φ i j h x) = locAt.toRing S i.val.snd x :=
  locAt.toRing_transMap S _ _ h.2 x

omit [IsLocalRing S] [IsLocalHom φ] in
/-- The canonical maps `R_λ → R` induce a bijection `colim R_λ → R`: each is injective, and
every `r ∈ R` lies in the finitely generated `ℤ[r]`. -/
theorem liftR_bijective :
    Function.Bijective (Ring.DirectLimit.lift (locR R S φ) (fun i j h => ⇑(transR R S φ i j h)) R
      (fun i => locAt.toRing R i.val.fst) (locAt.toRing_transR R S φ)) := by
  refine ⟨Ring.DirectLimit.lift_injective _ _ _ fun _ => locAt.toRing_injective R _, fun r => ?_⟩
  obtain ⟨A, hA, x, hx⟩ := exists_fg_toRing_eq R r
  exact ⟨Ring.DirectLimit.of _ _ ⟨(A, A.map φ.toIntAlgHom), hA, hA.map _,
    fun x hx => Subalgebra.mem_map.2 ⟨x, hx, rfl⟩⟩ x, by rw [Ring.DirectLimit.lift_of]; exact hx⟩

omit [IsLocalRing R] [IsLocalHom φ] in
/-- The canonical maps `S_λ → S` induce a bijection `colim S_λ → S`: each is injective, and
every `s ∈ S` lies in the finitely generated `ℤ[s]`. -/
theorem liftS_bijective :
    Function.Bijective (Ring.DirectLimit.lift (locS R S φ) (fun i j h => ⇑(transS R S φ i j h)) S
      (fun i => locAt.toRing S i.val.snd) (locAt.toRing_transS R S φ)) := by
  refine ⟨Ring.DirectLimit.lift_injective _ _ _ fun _ => locAt.toRing_injective S _, fun s => ?_⟩
  obtain ⟨B, hB, x, hx⟩ := exists_fg_toRing_eq S s
  exact ⟨Ring.DirectLimit.of _ _ ⟨(⊥, B), Subalgebra.fg_bot, hB, map_mem_of_mem_bot φ B⟩ x,
    by rw [Ring.DirectLimit.lift_of]; exact hx⟩

/-- `φ` intertwines the structure maps `locAt.toRing` with `psi`, pointwise at a stage. -/
theorem locAt.toRing_psi (i : Index R S φ) (x : locR R S φ i) :
    φ (locAt.toRing R i.val.fst x) = locAt.toRing S i.val.snd (psi R S φ i x) :=
  locAt.toRing_psiMap R S φ _ _ _ x

/-- The intertwining identity of `lift_comp_map`, read off at a single stage `i`. -/
theorem lift_map_of (i : Index R S φ) (x : locR R S φ i) :
    φ (Ring.DirectLimit.lift (locR R S φ) (fun i j h => ⇑(transR R S φ i j h)) R
        (fun i => locAt.toRing R i.val.fst) (locAt.toRing_transR R S φ)
        (Ring.DirectLimit.of _ _ i x)) =
      Ring.DirectLimit.lift (locS R S φ) (fun i j h => ⇑(transS R S φ i j h)) S
        (fun i => locAt.toRing S i.val.snd) (locAt.toRing_transS R S φ)
        (Ring.DirectLimit.map (psi R S φ) (psi_commutes R S φ)
          (Ring.DirectLimit.of _ _ i x)) := by
  rw [Ring.DirectLimit.map_apply_of, Ring.DirectLimit.lift_of, Ring.DirectLimit.lift_of]
  exact locAt.toRing_psi R S φ i x

/-- The induced maps `colim R_λ → R` and `colim S_λ → S` intertwine `colim ψ_λ` with `φ`. -/
theorem lift_comp_map :
    φ.comp (Ring.DirectLimit.lift (locR R S φ) (fun i j h => ⇑(transR R S φ i j h)) R
      (fun i => locAt.toRing R i.val.fst) (locAt.toRing_transR R S φ)) =
    (Ring.DirectLimit.lift (locS R S φ) (fun i j h => ⇑(transS R S φ i j h)) S
      (fun i => locAt.toRing S i.val.snd) (locAt.toRing_transS R S φ)).comp
      (Ring.DirectLimit.map (psi R S φ) (psi_commutes R S φ)) := by
  refine Ring.DirectLimit.hom_ext_iff.2 fun i => RingHom.ext fun x => ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact lift_map_of R S φ i x

/-- **(1) colimit isomorphism.** There are ring isomorphisms
`eR : colim R_λ ≃+* R` and `eS : colim S_λ ≃+* S` identifying the colimit map
`Ring.DirectLimit.map ψ hψ` with `φ`. -/
theorem colimit_iso :
    ∃ (eR : Ring.DirectLimit (locR R S φ) (fun i j h => ⇑(transR R S φ i j h)) ≃+* R)
       (eS : Ring.DirectLimit (locS R S φ) (fun i j h => ⇑(transS R S φ i j h)) ≃+* S),
       φ.comp eR.toRingHom
         = eS.toRingHom.comp (Ring.DirectLimit.map (psi R S φ) (psi_commutes R S φ)) :=
  ⟨RingEquiv.ofBijective _ (liftR_bijective R S φ),
    RingEquiv.ofBijective _ (liftS_bijective R S φ), lift_comp_map R S φ⟩

end Witness

end Stacks.EssentialFiniteness.LocalColimitSystem

open Stacks.EssentialFiniteness.LocalColimitSystem in
/-- A local homomorphism `φ : R → S` of local rings is the colimit, over a directed
set `Λ`, of a system of local homomorphisms `ψ_λ : R_λ → S_λ` of local rings
such that each `R_λ` is essentially of finite type over `ℤ` and each `S_λ` is
essentially of finite type over `R_λ` (via `ψ_λ`).

The data is bundled in the existential as:
* `Λ` with a `Preorder`, `Nonempty` and `IsDirectedOrder` instance — the
  directed set;
* `Rl`, `Sl` — the families of local rings, with their `CommRing` and
  `IsLocalRing` structure;
* `rf`, `sf` — the transition maps, forming directed systems (`dsR`, `dsS`);
* `ψ` — the family of local homomorphisms (`instLH`), commuting with the
  transition maps (`hψ`).

Condition (1) is encoded by the existence of ring isomorphisms
`eR : colim R_λ ≃+* R` and `eS : colim S_λ ≃+* S` identifying the colimit map
`Ring.DirectLimit.map ψ hψ` with `φ`, i.e. `φ ∘ eR = eS ∘ (colim ψ)`. -/
@[stacks 00QT]
theorem exists_essFiniteType_directedSystem_colimit
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] :
    ∃ (Λ : Type u) (instP : Preorder Λ),
    ∃ (_ : Nonempty Λ) (_ : @IsDirectedOrder Λ instP.toLE)
      (Rl : Λ → Type u) (Sl : Λ → Type u)
      (_ : ∀ i, CommRing (Rl i)) (_ : ∀ i, CommRing (Sl i))
      (rf : ∀ i j, i ≤ j → (Rl i →+* Rl j))
      (sf : ∀ i j, i ≤ j → (Sl i →+* Sl j))
      (_ : ∀ i, @IsLocalRing (Rl i) _)
      (_ : ∀ i, @IsLocalRing (Sl i) _)
      (ψ : ∀ i, Rl i →+* Sl i)
      (_ : ∀ i, IsLocalHom (ψ i))
      -- `rf`, `sf` form directed systems of rings
      (_ : @DirectedSystem Λ instP Rl (fun i j h => ⇑(rf i j h)))
      (_ : @DirectedSystem Λ instP Sl (fun i j h => ⇑(sf i j h)))
      -- the squares commute: `ψ` is a morphism of directed systems
      (hψ : ∀ i j (h : i ≤ j), (ψ j).comp (rf i j h) = (sf i j h).comp (ψ i)),
      -- (1) the colimit of the system `R_λ → S_λ` is equal to `φ : R → S`
      (∃ (eR : Ring.DirectLimit Rl (fun i j h => ⇑(rf i j h)) ≃+* R)
         (eS : Ring.DirectLimit Sl (fun i j h => ⇑(sf i j h)) ≃+* S),
         φ.comp eR.toRingHom = eS.toRingHom.comp (Ring.DirectLimit.map ψ hψ)) ∧
      -- (2) each `R_λ` is essentially of finite type over `ℤ`
      (∀ i, (Int.castRingHom (Rl i)).EssFiniteType) ∧
      -- (3) each `S_λ` is essentially of finite type over `R_λ` (via `ψ_λ`)
      (∀ i, (ψ i).EssFiniteType) :=
  ⟨Index R S φ, inferInstance, instNonemptyIndex R S φ,
    instIsDirectedIndex R S φ, locR R S φ, locS R S φ,
    (fun _ => inferInstance), (fun _ => inferInstance),
    transR R S φ, transS R S φ,
    (fun _ => inferInstance), (fun _ => inferInstance),
    psi R S φ, psi_isLocalHom R S φ,
    transR_directedSystem R S φ, transS_directedSystem R S φ, psi_commutes R S φ,
    ⟨colimit_iso R S φ, locR_essFiniteType R S φ, psi_essFiniteType R S φ⟩⟩

end

/-!
# Colimits and maps essentially of finite type

Let `φ : R → S` be a local homomorphism of local rings which is essentially of finite type.

## Main result

There exist a directed set `(Λ, ≤)` and a system of local homomorphisms
`φ_λ : R_λ → S_λ` of local rings over `(Λ, ≤)`, all transition maps local, such that

1. the colimit of the system is canonically isomorphic to `φ : R → S`; in particular
   `colim R_λ ≅ R` and `colim S_λ ≅ S`;
2. each `R_λ` is essentially of finite type over `ℤ`;
3. each `S_λ` is essentially of finite type over `R_λ`; and
4. for each `λ ≤ μ`, the canonical map `S_λ ⊗_{R_λ} R_μ → S_μ` presents `S_μ` as the
   localization of a quotient of `S_λ ⊗_{R_λ} R_μ`.

## Modelling

A directed set `(Λ, ≤)` is a type `Λ` with a `PartialOrder` that is `Nonempty` and
`IsDirected` for `≤`. Such a `Λ` is automatically a category and is `IsFiltered`, so
colimits over it are exactly filtered colimits.

A system of local homomorphisms `R_λ → S_λ` over `(Λ, ≤)` is a pair of functors
`Rf Sf : Λ ⥤ CommRingCat` together with a natural transformation `φsys : Rf ⟶ Sf`.
Functoriality of `Rf` and `Sf` encodes the transition maps and their compatibility with
composition, and naturality of `φsys` encodes the commuting squares. The colimit of the
system is the induced map `colimit Rf ⟶ colimit Sf`, and saying it equals `φ : R → S`
means, up to canonical isomorphism, that there are isomorphisms `colimit Rf ≅ R` and
`colimit Sf ≅ S` intertwining `colimMap φsys` with `algebraMap R S`.

Being essentially of finite type is `Algebra.EssFiniteType`: a ring map `A → B` is
essentially of finite type exactly when `B` is a localization of a finitely generated
`A`-subalgebra of `B`.

The tensor product `S_λ ⊗_{R_λ} R_μ` is the pushout in `CommRingCat` of `φ_λ : R_λ → S_λ`
and the transition map `R_λ → R_μ`, the pushout of two ring maps out of a common base being
their tensor product over that base. The canonical map to `S_μ` is `pushout.desc` built from
the transition map `S_λ → S_μ` and `φ_μ : R_μ → S_μ`, whose compatibility is exactly the
naturality of `φsys`.

Saying that `C` is the localization of a quotient of `B` along a ring map `desc : B → C`
means: there are an ideal `I ⊆ B`, a submonoid `T ⊆ B ⧸ I` and a ring map
`g : B ⧸ I → C` such that `B → C` factors as `B → B ⧸ I → C`, i.e.
`g ∘ (B → B ⧸ I) = desc`, and `C` is the localization of `B ⧸ I` at `T`. This says exactly
`C ≅ T⁻¹(B ⧸ I)` compatibly with the canonical map. It is genuinely weaker than asking `C`
to be a localization of `B` itself, and a bare quotient `B → B ⧸ I` is the case `T = {1}`.

## The construction

The index set is `Λ := Finset R`, the finite subsets of `R` ordered by inclusion, a
nonempty directed `PartialOrder` and hence a filtered category. For `A : Finset R`:

* `R'_A := Algebra.adjoin ℤ (↑A : Set R) ⊆ R` is a finite-type `ℤ`-subalgebra, and `R_A` is
  `R'_A` localized at the contracted prime `R'_A ∩ 𝔪_R`, a local ring.
* `S'_A := Algebra.adjoin ℤ (φ '' A ∪ {x₁,…,xₙ}) ⊆ S`, where `x₁,…,xₙ` witness that `S` is
  a localization of a finite-type `R`-subalgebra — they exist because `R → S` is
  essentially of finite type — and `S_A` is `S'_A` localized at the contracted prime
  `S'_A ∩ 𝔪_S`.
* Transition maps for `A ⊆ B` are induced by the subalgebra inclusions and functoriality of
  localization, and `φ_A : R_A → S_A` is induced by `R'_A ⊆ S'_A`.
-/

@[expose] public section


open CategoryTheory Limits

/-- Condition (4) for a pair `i ≤ j`: the canonical map
`S_i ⊗_{R_i} R_j → S_j` (realized as the `pushout.desc` out of the pushout of
`φ_i : R_i → S_i` and the transition map `R_i → R_j`) exhibits `S_j` as the
localization of a quotient of `S_i ⊗_{R_i} R_j`.

Concretely: there is an ideal `I` of `B := S_i ⊗_{R_i} R_j`, a submonoid
`T ⊆ B ⧸ I`, and a ring map `g : B ⧸ I → S_j` such that the canonical map
`B → S_j` factors as `B → B ⧸ I → S_j` and `S_j` is the localization of
`B ⧸ I` at `T`. -/
def Stacks.EssentialFiniteness.LocalColimit.LocalizationOfQuotient
    {Λ : Type} [PartialOrder Λ] {Rf Sf : Λ ⥤ CommRingCat} (φsys : Rf ⟶ Sf)
    {i j : Λ} (h : i ≤ j) : Prop :=
  -- `B = S_i ⊗_{R_i} R_j`, the pushout of `φ_i` and the transition map `R_i → R_j`.
  let B : CommRingCat := pushout (φsys.app i) (Rf.map h.hom)
  -- The canonical map `B ⟶ S_j`.
  let desc : B ⟶ Sf.obj j :=
    pushout.desc (Sf.map h.hom) (φsys.app j) (φsys.naturality h.hom).symm
  -- There is an ideal `I`, a submonoid `T` of `B ⧸ I`, and a factorization
  -- `g : B ⧸ I → S_j` of `desc` exhibiting `S_j` as `T⁻¹(B ⧸ I)`.
  ∃ (I : Ideal B) (T : Submonoid (B ⧸ I)) (g : (B ⧸ I) →+* Sf.obj j),
    g.comp (Ideal.Quotient.mk I) = desc.hom ∧
    @IsLocalization _ _ T _ _ g.toAlgebra

namespace Stacks.EssentialFiniteness.LocalColimit

/-- The colimit descent map composed with the leg at `A` is the cocone leg at `A`. -/
private theorem colimit_desc_apply_ι {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat)
    (c : Cocone F) (A : J) (y : F.obj A) :
    (ConcreteCategory.hom (colimit.desc F c)) ((ConcreteCategory.hom (colimit.ι F A)) y) =
      (ConcreteCategory.hom (c.ι.app A)) y :=
  ConcreteCategory.congr_hom (colimit.ι_desc c A) y

/-- The legs of a cocone are compatible with the maps of the diagram. -/
private theorem cocone_leg_map {J : Type} [SmallCategory J] {F : J ⥤ CommRingCat} (c : Cocone F)
    {A B : J} (h : A ⟶ B) (y : F.obj A) :
    (ConcreteCategory.hom (c.ι.app B)) ((ConcreteCategory.hom (F.map h)) y) =
      (ConcreteCategory.hom (c.ι.app A)) y := by
  simp

/-- If every element of the cocone point lies in the image of a leg, the descent map out of the
colimit is surjective. -/
private theorem colimit_desc_surjective {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat)
    (c : Cocone F)
    (h : ∀ r : c.pt, ∃ (A : J) (y : F.obj A), (ConcreteCategory.hom (c.ι.app A)) y = r) :
    Function.Surjective (ConcreteCategory.hom (colimit.desc F c)) := fun r => by
  obtain ⟨A, y, hy⟩ := h r
  exact ⟨(ConcreteCategory.hom (colimit.ι F A)) y, by rwa [colimit_desc_apply_ι]⟩

/-- If the descent map out of the colimit is bijective, the colimit is the cocone point, via the
legs. -/
private theorem colimit_desc_iso {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat)
    (c : Cocone F) (h : Function.Bijective (ConcreteCategory.hom (colimit.desc F c))) :
    ∃ i : colimit F ≅ c.pt, ∀ A, colimit.ι F A ≫ i.hom = c.ι.app A :=
  have := (ConcreteCategory.isIso_iff_bijective _).mpr h
  ⟨asIso (colimit.desc F c), fun A => colimit.ι_desc c A⟩

/-- If all legs of a cocone over a filtered diagram are injective, so is the descent map. -/
private theorem colimit_desc_injective {J : Type} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat) (c : Cocone F) (hc : ∀ A, Function.Injective (c.ι.app A)) :
    Function.Injective (ConcreteCategory.hom (colimit.desc F c)) := by
  have htc := isColimitOfPreserves (forget CommRingCat) (colimit.isColimit F)
  intro x₁ x₂ hx
  obtain ⟨A, yA, rfl⟩ := Types.jointly_surjective _ htc x₁
  obtain ⟨B, yB, rfl⟩ := Types.jointly_surjective _ htc x₂
  rw [Types.FilteredColimit.isColimit_eq_iff _ htc]
  exact ⟨IsFiltered.max A B, IsFiltered.leftToMax A B, IsFiltered.rightToMax A B, hc _ (by
    change (ConcreteCategory.hom (c.ι.app _)) ((ConcreteCategory.hom (F.map _)) yA) =
      (ConcreteCategory.hom (c.ι.app _)) ((ConcreteCategory.hom (F.map _)) yB)
    rw [cocone_leg_map, cocone_leg_map]
    exact (colimit_desc_apply_ι F c A yA).symm.trans (hx.trans (colimit_desc_apply_ι F c B yB)))⟩

/-- Index set of the system: finite subsets of `R`, ordered by inclusion.  This
is a nonempty directed partial order, hence filtered. -/
abbrev Idx (R : Type) [CommRing R] := Finset R

/-- The contracted maximal prime of the `ℤ`-subalgebra `R'_A = adjoin ℤ ↑A`,
i.e. the preimage of the maximal ideal `𝔪_R` under `R'_A ↪ R`.  Defined as an
`abbrev` so its `IsPrime` instance is found automatically. -/
noncomputable abbrev RA {R : Type} [CommRing R] [IsLocalRing R] (A : Finset R) :
    Ideal (Algebra.adjoin ℤ (↑A : Set R)) :=
  (IsLocalRing.maximalIdeal R).comap (algebraMap (Algebra.adjoin ℤ (↑A : Set R)) R)

/-- The subalgebra inclusion `R'_A → R'_B` for `A ⊆ B` (as a ring hom). -/
noncomputable def Rincl {R : Type} [CommRing R] {A B : Finset R} (h : A ⟶ B) :
    Algebra.adjoin ℤ (↑A : Set R) →+* Algebra.adjoin ℤ (↑B : Set R) :=
  (Subalgebra.inclusion (Algebra.adjoin_mono (by exact_mod_cast h.le)) :
    Algebra.adjoin ℤ (↑A : Set R) →ₐ[ℤ] Algebra.adjoin ℤ (↑B : Set R))

/-- The contracted prime `RA A` is the contraction of `RA B` along `Rincl h`
(this is the compatibility condition needed for functoriality of localization). -/
theorem RA_eq_comap_Rincl {R : Type} [CommRing R] [IsLocalRing R] {A B : Finset R} (h : A ⟶ B) :
    RA A = Ideal.comap (Rincl h) (RA B) := by
  rw [Ideal.comap_comap]
  rfl

/-- The functor `A ↦ R_A` of source rings, where `R_A` is `Algebra.adjoin ℤ ↑A` localized
at its contracted maximal prime, with transition maps induced by the inclusions
`A ⊆ B`. -/
noncomputable def Rfun (R : Type) [CommRing R] [IsLocalRing R] : Idx R ⥤ CommRingCat where
  obj A := CommRingCat.of (Localization.AtPrime (RA A))
  map {A B} h := CommRingCat.ofHom
    (Localization.localRingHom (RA A) (RA B) (Rincl h) (RA_eq_comap_Rincl h))
  map_id A := by
    rw [← CommRingCat.ofHom_id]; congr 1
    rw [← Localization.localRingHom_id (RA A)]; congr 1
  map_comp {A B C} f g := by
    rw [← CommRingCat.ofHom_comp]; congr 1
    rw [← Localization.localRingHom_comp (RA A) (RA B) (RA C) (Rincl f) (RA_eq_comap_Rincl f)
      (Rincl g) (RA_eq_comap_Rincl g)]
    congr 1

/-- A finite generating set `x₁,…,xₙ ∈ S` witnessing that `S` is essentially of
finite type over `R`: `S` is the localization of `Algebra.adjoin R ↑(Sgens hft)`.
Extracted from `hft.cond`. -/
noncomputable abbrev Sgens {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (hft : Algebra.EssFiniteType R S) : Finset S := hft.cond.choose

/-- The target generating set in `S` for index `A`: the images `φ '' A` of `A`
together with the fixed essential-finite-type generators `xᵢ`. -/
def Sset {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (hft : Algebra.EssFiniteType R S) (A : Finset R) : Set S :=
  (algebraMap R S) '' (↑A : Set R) ∪ (↑(Sgens hft) : Set S)

/-- The contracted maximal prime of the `ℤ`-subalgebra `S'_A = adjoin ℤ (Sset A)`,
i.e. the preimage of `𝔪_S` under `S'_A ↪ S`.  An `abbrev` so its `IsPrime`
instance is found automatically. -/
noncomputable abbrev SA {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (hft : Algebra.EssFiniteType R S) (A : Finset R) :
    Ideal (Algebra.adjoin ℤ (Sset hft A)) :=
  (IsLocalRing.maximalIdeal S).comap (algebraMap (Algebra.adjoin ℤ (Sset hft A)) S)

/-- `Sset` is monotone in `A` (since `φ '' A` grows and the `xᵢ` are fixed). -/
theorem Sset_mono {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (hft : Algebra.EssFiniteType R S) {A B : Finset R} (h : A ⟶ B) :
    Sset hft A ⊆ Sset hft B :=
  Set.union_subset_union_left _ (Set.image_mono (by exact_mod_cast h.le))

/-- The subalgebra inclusion `S'_A → S'_B` for `A ⊆ B` (as a ring hom). -/
noncomputable def Sincl {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (hft : Algebra.EssFiniteType R S) {A B : Finset R} (h : A ⟶ B) :
    Algebra.adjoin ℤ (Sset hft A) →+* Algebra.adjoin ℤ (Sset hft B) :=
  (Subalgebra.inclusion (Algebra.adjoin_mono (Sset_mono hft h)) :
    Algebra.adjoin ℤ (Sset hft A) →ₐ[ℤ] Algebra.adjoin ℤ (Sset hft B))

/-- The contracted prime `SA A` is the contraction of `SA B` along `Sincl h`
(the compatibility condition needed for functoriality of localization). -/
theorem SA_eq_comap_Sincl {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    (hft : Algebra.EssFiniteType R S) {A B : Finset R} (h : A ⟶ B) :
    SA hft A = Ideal.comap (Sincl hft h) (SA hft B) := by
  rw [Ideal.comap_comap]
  rfl

/-- The functor `A ↦ S_A` of target rings, where `S_A` is
`Algebra.adjoin ℤ (φ '' A ∪ {xᵢ})` localized at its contracted maximal prime, with
transition maps induced by the inclusions. The generating set `xᵢ` of `S` over `R` comes
from `hft : EssFiniteType R S`. -/
noncomputable def Sfun (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) : Idx R ⥤ CommRingCat where
  obj A := CommRingCat.of (Localization.AtPrime (SA hft A))
  map {A B} h := CommRingCat.ofHom
    (Localization.localRingHom (SA hft A) (SA hft B) (Sincl hft h) (SA_eq_comap_Sincl hft h))
  map_id A := by
    rw [← CommRingCat.ofHom_id]; congr 1
    rw [← Localization.localRingHom_id (SA hft A)]; congr 1
  map_comp {A B C} f g := by
    rw [← CommRingCat.ofHom_comp]; congr 1
    rw [← Localization.localRingHom_comp (SA hft A) (SA hft B) (SA hft C) (Sincl hft f)
      (SA_eq_comap_Sincl hft f) (Sincl hft g) (SA_eq_comap_Sincl hft g)]
    congr 1

/-- The ring hom `R'_A = adjoin ℤ ↑A → S'_A = adjoin ℤ (Sset A)` induced by
`algebraMap R S`.  Since `algebraMap R S` sends `↑A` into `Sset A`, it maps the
subalgebra `adjoin ℤ ↑A ⊆ R` into the subalgebra `adjoin ℤ (Sset A) ⊆ S`. -/
noncomputable def φincl {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (hft : Algebra.EssFiniteType R S) (A : Finset R) :
    Algebra.adjoin ℤ (↑A : Set R) →+* Algebra.adjoin ℤ (Sset hft A) :=
  let f : R →ₐ[ℤ] S := (algebraMap R S).toIntAlgHom
  have hsub : Subalgebra.map f (Algebra.adjoin ℤ (↑A : Set R)) ≤
      Algebra.adjoin ℤ (Sset hft A) := by
    rw [← Algebra.adjoin_image]
    exact Algebra.adjoin_mono fun _ ⟨a, ha, h⟩ => Or.inl ⟨a, ha, h⟩
  ((f.comp (Subalgebra.val _)).codRestrict (Algebra.adjoin ℤ (Sset hft A))
    (fun x => hsub ⟨x.val, x.property, rfl⟩)).toRingHom

/-- The underlying element of `φincl hft A x` in `S` is `algebraMap R S` applied
to the underlying element of `x` in `R`. -/
@[simp] theorem φincl_coe {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (hft : Algebra.EssFiniteType R S) (A : Finset R)
    (x : Algebra.adjoin ℤ (↑A : Set R)) :
    ((φincl hft A x : Algebra.adjoin ℤ (Sset hft A)) : S) = algebraMap R S (x : R) := rfl

/-- The localization monoid `(RA A).primeCompl` maps into `(SA hft A).primeCompl`
under `φincl hft A`.  This holds *without* `φ` being local: if `x` lifts to a unit
of `R`, its image lifts to a unit of `S`, hence lies outside `𝔪_S`. -/
theorem φhle {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) (A : Finset R) :
    (RA A).primeCompl ≤ Submonoid.comap (φincl hft A) (SA hft A).primeCompl := by
  intro x hx
  simp only [Ideal.primeCompl, Submonoid.mem_comap, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe] at hx ⊢
  have hunit : IsUnit (algebraMap (Algebra.adjoin ℤ (↑A : Set R)) R x) :=
    IsLocalRing.notMem_maximalIdeal.mp hx
  exact IsLocalRing.notMem_maximalIdeal.mpr (hunit.map (algebraMap R S))

-- needed: without it `φsys` fails (2 sites): Tactic `rewrite` failed: Did not find an occurrence
-- of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `φsys : Rfun ⟶ Sfun`, whose component at `A` is
`φ_A : R_A → S_A`, induced by `R'_A ⊆ S'_A`, and whose naturality squares record
compatibility of `φ` with the transition maps. -/
noncomputable def φsys (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) :
    Rfun R ⟶ Sfun R S hft where
  app A := CommRingCat.ofHom
    (IsLocalization.map (Localization.AtPrime (SA hft A)) (φincl hft A) (φhle hft A))
  naturality {A B} h := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
    change RingHom.comp _
        (Localization.localRingHom (RA A) (RA B) (Rincl h) (RA_eq_comap_Rincl h)) =
      RingHom.comp
        (Localization.localRingHom (SA hft A) (SA hft B) (Sincl hft h) (SA_eq_comap_Sincl hft h)) _
    simp only [CommRingCat.hom_ofHom]
    -- the underlying square: `φincl B ∘ Rincl h = Sincl h ∘ φincl A` (both restrict `algebraMap R
    -- S`)
    have key : (φincl hft B).comp (Rincl h) = (Sincl hft h).comp (φincl hft A) := by
      ext x; rfl
    -- both sides are ring homs out of `Localization.AtPrime (RA A)`; check via algebraMap
    apply IsLocalization.ringHom_ext (RA A).primeCompl
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    unfold Localization.localRingHom
    rw [IsLocalization.map_comp, IsLocalization.map_comp]
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, IsLocalization.map_comp,
        IsLocalization.map_comp]
    rw [RingHom.comp_assoc, RingHom.comp_assoc, key]

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S]

/-- Each `R_A` is a local ring (localization at a prime).
Hint: `Localization.AtPrime.isLocalRing`; reduce `Rfun.obj A` to the underlying
`Localization.AtPrime` ring. -/
lemma isLocalRing_Rfun (i : Idx R) : IsLocalRing ((Rfun R).obj i) :=
  Localization.AtPrime.isLocalRing (RA i)

/-- Each `S_A` is a local ring. -/
lemma isLocalRing_Sfun (hft : Algebra.EssFiniteType R S) (i : Idx R) :
    IsLocalRing ((Sfun R S hft).obj i) :=
  Localization.AtPrime.isLocalRing (SA hft i)

/-- Each component `φ_A : R_A → S_A` is a local homomorphism, because it
sends the contracted prime `R'_A ∩ 𝔪_R` into `S'_A ∩ 𝔪_S` (as `φ(𝔪_R) ⊆ 𝔪_S`
since `φ` is local) and respects the localizations. -/
lemma isLocalHom_φsys (hφ : IsLocalHom (algebraMap R S)) (hft : Algebra.EssFiniteType R S)
    (i : Idx R) :
    IsLocalHom ((φsys R S hft).app i).hom := by
  have hbij (y : R) : y ∈ IsLocalRing.maximalIdeal R ↔
      algebraMap R S y ∈ IsLocalRing.maximalIdeal S := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun hy hu => hy (isUnit_of_map_unit _ y hu), fun hy hu => hy (hu.map _)⟩
  have hcomap : RA i = Ideal.comap (φincl hft i) (SA hft i) := by
    refine Ideal.ext fun x => ?_
    show algebraMap (Algebra.adjoin ℤ (↑i : Set R)) R x ∈ IsLocalRing.maximalIdeal R ↔
      algebraMap (Algebra.adjoin ℤ (Sset hft i)) S (φincl hft i x) ∈ IsLocalRing.maximalIdeal S
    exact hbij _
  exact Localization.isLocalHom_localRingHom (RA i) (SA hft i) (φincl hft i) hcomap

/-- Each transition map `R_A → R_B` (`A ⊆ B`) is a local homomorphism:
the inclusion `R'_A ⊆ R'_B` contracts `R'_B ∩ 𝔪_R` to `R'_A ∩ 𝔪_R`. -/
lemma isLocalHom_Rfun_map (i j : Idx R) (h : i ≤ j) :
    IsLocalHom ((Rfun R).map h.hom).hom :=
  Localization.isLocalHom_localRingHom (RA i) (RA j) (Rincl h.hom) (RA_eq_comap_Rincl h.hom)

/-- Each transition map `S_A → S_B` (`A ⊆ B`) is a local homomorphism. -/
lemma isLocalHom_Sfun_map (hft : Algebra.EssFiniteType R S) (i j : Idx R) (h : i ≤ j) :
    IsLocalHom ((Sfun R S hft).map h.hom).hom :=
  Localization.isLocalHom_localRingHom (SA hft i) (SA hft j) (Sincl hft h.hom)
    (SA_eq_comap_Sincl hft h.hom)

/-! ### Identifying the colimits

The identification of the colimit of the system with `φ : R → S` factors through:
* `Rleg` and `Sleg`, the cocone legs `R_A → R` and `S_A → S`, obtained from
  `IsLocalization.lift` because the prime complement of the contracted maximal ideal maps
  to units, `R` and `S` being local;
* `Rcolimit_desc_iso`, that the colimit of `Rfun` is `of R`, with the leg property;
* `Scolimit_desc_iso`, the same for `Sfun` and `of S` — the harder half, whose
  surjectivity uses `EssFiniteType.cond`; and
* `intertwine_leg`, the per-`A` compatibility square.

`colimit_iso` assembles these by `colimit.hom_ext`.
-/

/-- The cocone leg `R_A → R`, the `IsLocalization.lift` of the
subalgebra inclusion `R'_A ↪ R`. Legal because `R` is local: the prime-complement
of the contracted maximal ideal maps to units of `R`
(`IsLocalRing.notMem_maximalIdeal`). -/
noncomputable def Rleg (R : Type) [CommRing R] [IsLocalRing R] (A : Idx R) :
    Localization.AtPrime (RA A) →+* R :=
  IsLocalization.lift (M := (RA A).primeCompl) (S := Localization.AtPrime (RA A))
    (g := algebraMap (Algebra.adjoin ℤ (↑A : Set R)) R)
    (fun y => IsLocalRing.notMem_maximalIdeal.mp y.property)

/-- The cocone leg `S_A → S`, the `IsLocalization.lift` of the
subalgebra inclusion `S'_A ↪ S`. Legal because `S` is local. -/
noncomputable def Sleg (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) (A : Idx R) :
    Localization.AtPrime (SA hft A) →+* S :=
  IsLocalization.lift (M := (SA hft A).primeCompl) (S := Localization.AtPrime (SA hft A))
    (g := algebraMap (Algebra.adjoin ℤ (Sset hft A)) S)
    (fun y => IsLocalRing.notMem_maximalIdeal.mp y.property)

-- needed: without it `Rcocone` fails (2 sites): Tactic `rewrite` failed: Did not find an
-- occurrence of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- The cocone on `Rfun R` with vertex `R` whose legs are the maps `Rleg`. -/
noncomputable def Rcocone : Cocone (Rfun R) where
  pt := CommRingCat.of R
  ι := {
    app := fun A => CommRingCat.ofHom (Rleg R A)
    naturality := by
      intro A B h
      apply CommRingCat.hom_ext
      rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
      change RingHom.comp (Rleg R B)
        (Localization.localRingHom (RA A) (RA B) (Rincl h) (RA_eq_comap_Rincl h)) =
        RingHom.comp _ (Rleg R A)
      apply IsLocalization.ringHom_ext (RA A).primeCompl
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply,
        Localization.localRingHom_to_map, Rleg, IsLocalization.lift_eq]
      change algebraMap (Algebra.adjoin ℤ (↑B : Set R)) R (Rincl h x) = _
      rfl
  }

/-- The colimit descent map composed with the leg at `A` is the cocone leg `Rleg R A`. -/
lemma Rdesc_apply_ι (A : Idx R) (y : Localization.AtPrime (RA A)) :
    (ConcreteCategory.hom (colimit.desc (Rfun R) (Rcocone R)))
        ((ConcreteCategory.hom (colimit.ι (Rfun R) A)) y) = Rleg R A y :=
  colimit_desc_apply_ι (Rfun R) (Rcocone R) A y

/-- Every `r : R` is in the image of the leg at the singleton index `{r}`. -/
lemma Rleg_singleton_surj (r : R) :
    ∃ y : Localization.AtPrime (RA ({r} : Finset R)), Rleg R ({r} : Finset R) y = r := by
  refine ⟨algebraMap (Algebra.adjoin ℤ (↑({r} : Finset R) : Set R))
    (Localization.AtPrime (RA ({r} : Finset R))) ⟨r, Algebra.subset_adjoin (by simp)⟩, ?_⟩
  rw [Rleg, IsLocalization.lift_eq]
  rfl

/-- The map `colimit (Rfun R) → R` induced by the cocone `Rcocone` is surjective. -/
lemma Rdesc_surjective :
    Function.Surjective (ConcreteCategory.hom (colimit.desc (Rfun R) (Rcocone R))) :=
  colimit_desc_surjective _ _ fun r =>
    let ⟨y, hy⟩ := Rleg_singleton_surj R r
    ⟨_, y, hy⟩

/-- Each cocone leg `R_A → R` is injective, `R_A` being a localization of a subring of `R`. -/
lemma Rleg_injective (A : Idx R) : Function.Injective (Rleg R A) :=
  lift_injective_of_injective (S := Localization.AtPrime (RA A)) (M := (RA A).primeCompl) _
    Subtype.val_injective

/-- The cocone legs are compatible with the transition maps of `Rfun R`. -/
lemma Rleg_map {A B : Idx R} (h : A ⟶ B) (y : Localization.AtPrime (RA A)) :
    Rleg R B ((ConcreteCategory.hom ((Rfun R).map h)) y) = Rleg R A y :=
  cocone_leg_map (Rcocone R) h y

-- needed: without it `Rdesc_injective` fails: Tactic `rewrite` failed: Did not find an occurrence
-- of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- The map `colimit (Rfun R) → R` induced by the cocone `Rcocone` is injective. -/
lemma Rdesc_injective :
    Function.Injective (ConcreteCategory.hom (colimit.desc (Rfun R) (Rcocone R))) :=
  colimit_desc_injective _ _ (Rleg_injective R)

/-- The map `colimit (Rfun R) → R` induced by the cocone `Rcocone` is bijective. -/
lemma Rdesc_bijective :
    Function.Bijective (ConcreteCategory.hom (colimit.desc (Rfun R) (Rcocone R))) :=
  ⟨Rdesc_injective R, Rdesc_surjective R⟩

-- needed: without it `Rcolimit_desc_iso` fails: failed to synthesize instance of type class
set_option backward.isDefEq.respectTransparency false in
/-- The colimit of `Rfun R` is isomorphic to `R`, compatibly with the legs `Rleg`. -/
lemma Rcolimit_desc_iso :
    ∃ iR : colimit (Rfun R) ≅ CommRingCat.of R,
      ∀ A : Idx R, colimit.ι (Rfun R) A ≫ iR.hom = CommRingCat.ofHom (Rleg R A) :=
  colimit_desc_iso (Rfun R) (Rcocone R) (Rdesc_bijective R)

-- needed: without it `Scocone` fails (2 sites): Tactic `rewrite` failed: Did not find an
-- occurrence of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- The cocone on `Sfun R S hft` with vertex `S` whose legs are the maps `Sleg`. -/
noncomputable def Scocone (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) : Cocone (Sfun R S hft) where
  pt := CommRingCat.of S
  ι := {
    app := fun A => CommRingCat.ofHom (Sleg R S hft A)
    naturality := by
      intro A B h
      apply CommRingCat.hom_ext
      rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
      change RingHom.comp (Sleg R S hft B)
        (Localization.localRingHom (SA hft A) (SA hft B) (Sincl hft h) (SA_eq_comap_Sincl hft h)) =
        RingHom.comp _ (Sleg R S hft A)
      apply IsLocalization.ringHom_ext (SA hft A).primeCompl
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply,
        Localization.localRingHom_to_map, Sleg, IsLocalization.lift_eq]
      change algebraMap (Algebra.adjoin ℤ (Sset hft B)) S (Sincl hft h x) = _
      rfl
  }

/-- The colimit descent map composed with the leg at `A` is the cocone leg `Sleg R S hft A`. -/
lemma Sdesc_apply_ι (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S)
    (A : Idx R) (y : Localization.AtPrime (SA hft A)) :
    (ConcreteCategory.hom (colimit.desc (Sfun R S hft) (Scocone R S hft)))
        ((ConcreteCategory.hom (colimit.ι (Sfun R S hft) A)) y) = Sleg R S hft A y :=
  colimit_desc_apply_ι (Sfun R S hft) (Scocone R S hft) A y

/-- Each cocone leg `S_A → S` is injective, `S_A` being a localization of a subring of `S`. -/
lemma Sleg_injective (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S)
    (A : Idx R) : Function.Injective (Sleg R S hft A) :=
  lift_injective_of_injective (S := Localization.AtPrime (SA hft A)) (M := (SA hft A).primeCompl) _
    Subtype.val_injective

-- needed: without it `Sleg_map` fails: Tactic `rewrite` failed: Did not find an occurrence of the
-- pat…
set_option backward.isDefEq.respectTransparency false in
/-- The cocone legs are compatible with the transition maps of `Sfun R S hft`. -/
lemma Sleg_map (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S)
    {A B : Idx R} (h : A ⟶ B) (y : Localization.AtPrime (SA hft A)) :
    Sleg R S hft B ((ConcreteCategory.hom ((Sfun R S hft).map h)) y) = Sleg R S hft A y :=
  cocone_leg_map (Scocone R S hft) h y

/-- Elements of `Algebra.adjoin ℤ (Sset hft A)` and `Algebra.adjoin ℤ (Sset hft B)` both lie in
`Algebra.adjoin ℤ (Sset hft (A ∪ B))`. -/
private theorem mem_adjoin_Sset_union {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [DecidableEq R] (hft : Algebra.EssFiniteType R S) {A B : Finset R} {x y : S}
    (hx : x ∈ Algebra.adjoin ℤ (Sset hft A)) (hy : y ∈ Algebra.adjoin ℤ (Sset hft B)) :
    x ∈ Algebra.adjoin ℤ (Sset hft (A ∪ B)) ∧ y ∈ Algebra.adjoin ℤ (Sset hft (A ∪ B)) :=
  ⟨Algebra.adjoin_mono (Sset_mono hft (homOfLE Finset.subset_union_left)) hx,
    Algebra.adjoin_mono (Sset_mono hft (homOfLE Finset.subset_union_right)) hy⟩

/-- Any element of `Algebra.adjoin R (Sgens hft)` already lies in `Algebra.adjoin ℤ (Sset hft A)`
for some finite `A ⊆ R`: absorb the finitely many `R`-coefficients of a representative into
the index. -/
lemma absorb (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) (a : S)
    (ha : a ∈ Algebra.adjoin R (↑(Sgens hft) : Set S)) :
    ∃ A : Finset R, a ∈ Algebra.adjoin ℤ (Sset hft A) := by
  classical
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨∅, Algebra.subset_adjoin (Or.inr hx)⟩
  | algebraMap r => exact ⟨{r}, Algebra.subset_adjoin (Or.inl ⟨r, by simp, rfl⟩)⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨A, hA⟩ := ihx
      obtain ⟨B, hB⟩ := ihy
      have := mem_adjoin_Sset_union hft hA hB
      exact ⟨A ∪ B, Subalgebra.add_mem _ this.1 this.2⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨A, hA⟩ := ihx
      obtain ⟨B, hB⟩ := ihy
      have := mem_adjoin_Sset_union hft hA hB
      exact ⟨A ∪ B, Subalgebra.mul_mem _ this.1 this.2⟩

/-- Every `σ : S` is in the image of some cocone leg `S_A → S`. Writing `σ` as a fraction over
`Algebra.adjoin R (Sgens hft)` and absorbing numerator and denominator into a common index `A`
puts `σ` in the image of `S_A`. -/
lemma Sleg_surj (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) (σ : S) :
    ∃ (A : Idx R) (y : Localization.AtPrime (SA hft A)), Sleg R S hft A y = σ := by
  classical
  have hspec := hft.cond.choose_spec
  set D := Algebra.adjoin R (↑(Sgens hft) : Set S) with hD
  obtain ⟨⟨d, m⟩, hdm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (Algebra.adjoin R (↑(Sgens hft) : Set S)) S) (IsUnit.submonoid S))
        σ
  obtain ⟨Ad, hAd⟩ := absorb R S hft (algebraMap D S d) d.property
  obtain ⟨Am, hAm⟩ := absorb R S hft (algebraMap D S m) m.val.property
  refine ⟨Ad ∪ Am, ?_⟩
  obtain ⟨hdmem, hmmem⟩ := mem_adjoin_Sset_union hft hAd hAm
  set d' : Algebra.adjoin ℤ (Sset hft (Ad ∪ Am)) := ⟨algebraMap D S d, hdmem⟩ with hd'
  set m' : Algebra.adjoin ℤ (Sset hft (Ad ∪ Am)) := ⟨algebraMap D S (m : D), hmmem⟩ with hm'
  have hmunit : IsUnit (algebraMap D S (m : D)) := m.property
  have hval_m : algebraMap (Algebra.adjoin ℤ (Sset hft (Ad ∪ Am))) S m' = algebraMap D S (m :
      D) := by
    rw [Subalgebra.algebraMap_apply]
  have hval_d : algebraMap (Algebra.adjoin ℤ (Sset hft (Ad ∪ Am))) S d' = algebraMap D S d := by
    rw [Subalgebra.algebraMap_apply]
  have hm'compl : m' ∈ (SA hft (Ad ∪ Am)).primeCompl := by
    show m' ∉ SA hft (Ad ∪ Am)
    intro hmem
    exact IsLocalRing.notMem_maximalIdeal.mpr hmunit (hval_m ▸ hmem)
  refine ⟨IsLocalization.mk' (Localization.AtPrime (SA hft (Ad ∪ Am))) d' ⟨m', hm'compl⟩, ?_⟩
  rw [Sleg, IsLocalization.lift_mk'_spec]
  show algebraMap (Algebra.adjoin ℤ (Sset hft (Ad ∪ Am))) S d'
      = algebraMap (Algebra.adjoin ℤ (Sset hft (Ad ∪ Am))) S m' * σ
  rw [hval_d, hval_m, ← hdm]; ring

/-- The map `colimit (Sfun R S hft) → S` induced by the cocone `Scocone` is surjective. -/
lemma Sdesc_surjective (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) :
    Function.Surjective (ConcreteCategory.hom (colimit.desc (Sfun R S hft) (Scocone R S hft))) :=
  colimit_desc_surjective _ _ (Sleg_surj R S hft)

-- needed: without it `Sdesc_injective` fails: Tactic `rewrite` failed: Did not find an occurrence
-- of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- The map `colimit (Sfun R S hft) → S` induced by the cocone `Scocone` is injective. -/
lemma Sdesc_injective (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) :
    Function.Injective (ConcreteCategory.hom (colimit.desc (Sfun R S hft) (Scocone R S hft))) :=
  colimit_desc_injective _ _ (Sleg_injective R S hft)

/-- The map `colimit (Sfun R S hft) → S` induced by the cocone `Scocone` is bijective. -/
lemma Sdesc_bijective (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hft : Algebra.EssFiniteType R S) :
    Function.Bijective (ConcreteCategory.hom (colimit.desc (Sfun R S hft) (Scocone R S hft))) :=
  ⟨Sdesc_injective R S hft, Sdesc_surjective R S hft⟩

-- needed: without it `Scolimit_desc_iso` fails: failed to synthesize instance of type class
set_option backward.isDefEq.respectTransparency false in
/-- The colimit of `Sfun` is `CommRingCat.of S`, via the legs `Sleg`.
Same shape as for `Rfun`, but the surjectivity half is harder: it uses `EssFiniteType.cond`
(`S` is the localization of `adjoin R (Sgens hft)` at the units-submonoid), the
local-ring identity `Submonoid.comap g (IsUnit.submonoid S) = (Ideal.comap g 𝔪_S).primeCompl`,
and absorption of a fraction's numerator/denominator into `S'_A` for `A` = the
finite set of `R`-coefficients appearing in a chosen polynomial representative
(`IsLocalization.mk'_surjective` on the `EssFiniteType` localization). -/
lemma Scolimit_desc_iso (hft : Algebra.EssFiniteType R S) :
    ∃ iS : colimit (Sfun R S hft) ≅ CommRingCat.of S,
      ∀ A : Idx R, colimit.ι (Sfun R S hft) A ≫ iS.hom = CommRingCat.ofHom (Sleg R S hft A) :=
  colimit_desc_iso (Sfun R S hft) (Scocone R S hft) (Sdesc_bijective R S hft)

-- needed: without it `intertwine_leg` fails: unknown metavariable `?_uniq.37847`
set_option backward.isDefEq.respectTransparency false in
/-- The per-`A` compatibility square `φ ∘ Rleg_A = Sleg_A ∘ φ_A`.
Both sides are ring maps out of the localization `R_A`; by
`IsLocalization.ringHom_ext` it suffices to check after the localization map
`R'_A → R_A`, where it reduces to `algebraMap R S ∘ (R'_A ↪ R) = (S'_A ↪ S) ∘ φincl`
(`IsLocalization.lift_eq`, `IsLocalization.map_comp`, and `φincl_coe`/`rfl`). -/
lemma intertwine_leg (hft : Algebra.EssFiniteType R S) (A : Idx R) :
    (algebraMap R S).comp (Rleg R A)
      = (Sleg R S hft A).comp ((φsys R S hft).app A).hom := by
  -- x ∈ R'_A to algebraMap R S x; denominators discharged by ringHom_ext + φhle.)
  apply IsLocalization.ringHom_ext (RA A).primeCompl
  ext x
  unfold Rleg Sleg φsys
  simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    IsLocalization.lift_eq, IsLocalization.map_eq]
  rfl

/-- Condition (1): the colimit of the system recovers `φ : R → S`. There are isomorphisms
`colimit Rfun ≅ R` and `colimit Sfun ≅ S` intertwining `colimMap φsys` with
`algebraMap R S`. It is assembled from `Rcolimit_desc_iso`, `Scolimit_desc_iso` and
`intertwine_leg` by `colimit.hom_ext`. -/
lemma colimit_iso (hft : Algebra.EssFiniteType R S) :
    ∃ (iR : colimit (Rfun R) ≅ CommRingCat.of R)
      (iS : colimit (Sfun R S hft) ≅ CommRingCat.of S),
      iR.inv ≫ colimMap (φsys R S hft) ≫ iS.hom = CommRingCat.ofHom (algebraMap R S) := by
  -- EssFiniteType.cond + local-ring identity comap f IsUnit.submonoid = (comap f 𝔪).primeCompl;
  -- square direction-coherent of R ⟶ of S. Hardest subgoal; no counterexample.)
  obtain ⟨iR, hiR⟩ := Rcolimit_desc_iso R
  obtain ⟨iS, hiS⟩ := Scolimit_desc_iso R S hft
  refine ⟨iR, iS, ?_⟩
  -- It suffices to prove `colimMap φsys ≫ iS.hom = iR.hom ≫ ofHom (algebraMap R S)`,
  -- then cancel the iso `iR` on the left.
  have key : colimMap (φsys R S hft) ≫ iS.hom
      = iR.hom ≫ CommRingCat.ofHom (algebraMap R S) := by
    refine colimit.hom_ext fun A => ?_
    -- LHS at leg A: ι A ≫ colimMap φsys ≫ iS.hom = φsys.app A ≫ ι_S A ≫ iS.hom
    --             = φsys.app A ≫ ofHom (Sleg A)   (ι_colimMap, hiS)
    rw [← Category.assoc, ι_colimMap, Category.assoc, hiS]
    -- RHS at leg A: ι A ≫ iR.hom ≫ ofHom (algebraMap R S)
    --             = ofHom (Rleg A) ≫ ofHom (algebraMap R S)
    rw [← Category.assoc, hiR]
    -- Reduce to the hom-level square, `intertwine_leg`.
    apply CommRingCat.hom_ext
    exact (intertwine_leg R S hft A).symm
  -- Now use `key` to finish: iR.inv ≫ (iR.hom ≫ ofHom φ) = ofHom φ.
  rw [key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Condition (2): each `R_A` is essentially of finite type over `ℤ`.
`R'_A = Algebra.adjoin ℤ ↑A` is of finite type over `ℤ` (finite generators); its
localization `R_A` is then essentially of finite type over `ℤ`
(`Algebra.EssFiniteType.of_isLocalization` ∘ `EssFiniteType.comp`). -/
lemma essFiniteType_Rfun (i : Idx R) :
    Algebra.EssFiniteType ℤ ((Rfun R).obj i) := by
  -- R'_i = adjoin ℤ ↑i is finite type over ℤ (finite generators).
  have hftZR : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (↑i : Set R)) :=
    Algebra.FiniteType.adjoin_of_finite i.finite_toSet
  -- ess finite type ℤ → R'_i
  have eftZR : Algebra.EssFiniteType ℤ (Algebra.adjoin ℤ (↑i : Set R)) :=
    Algebra.EssFiniteType.of_finiteType _ _
  -- ess finite type R'_i → R_i (localization at RA i)
  have eftRloc : Algebra.EssFiniteType (Algebra.adjoin ℤ (↑i : Set R))
      (Localization.AtPrime (RA i)) :=
    Algebra.EssFiniteType.of_isLocalization _ (RA i).primeCompl
  -- compose ℤ → R'_i → R_i
  have eftZloc : Algebra.EssFiniteType ℤ (Localization.AtPrime (RA i)) :=
    Algebra.EssFiniteType.comp ℤ (Algebra.adjoin ℤ (↑i : Set R))
      (Localization.AtPrime (RA i))
  -- the goal's ℤ-algebra instance on the carrier agrees with the localization's
  -- (both are the canonical int-algebra; transfer along subsingleton).
  have hsub : (OreLocalization.instAlgebra : Algebra ℤ (Localization.AtPrime (RA i)))
      = (Ring.toIntAlgebra _) := Subsingleton.elim _ _
  rwa [hsub] at eftZloc

omit [IsLocalRing R] [IsLocalRing S] in
/-- `S'_A = adjoin ℤ (Sset A)` is essentially of finite type over `R'_A = adjoin ℤ ↑A`
via `φincl`. -/
lemma essFiniteType_adjoin_Sset (hft : Algebra.EssFiniteType R S) (i : Idx R) :
    letI := (φincl hft i).toAlgebra
    Algebra.EssFiniteType (Algebra.adjoin ℤ (↑i : Set R)) (Algebra.adjoin ℤ (Sset hft i)) := by
  let := (φincl hft i).toAlgebra
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Sset hft i)) :=
    .adjoin_of_finite (((Finset.finite_toSet i).image _).union (Finset.finite_toSet _))
  have : IsScalarTower ℤ (Algebra.adjoin ℤ (↑i : Set R)) (Algebra.adjoin ℤ (Sset hft i)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show algebraMap ℤ _ x = (φincl hft i) (algebraMap ℤ _ x)
    simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  have : Algebra.FiniteType (Algebra.adjoin ℤ (↑i : Set R)) (Algebra.adjoin ℤ (Sset hft i)) :=
    .of_restrictScalars_finiteType ℤ _ _
  exact .of_finiteType _ _

/-- Condition (3): each `S_A` is essentially of finite type over `R_A`,
with the `R_A`-algebra structure induced by `φ_A`.  `S'_A` is finite type over
`R'_A` (generators `φ(a), xᵢ`), so the localization `S_A` is essentially of
finite type over `R_A`. -/
lemma essFiniteType_Sfun (hft : Algebra.EssFiniteType R S) (i : Idx R) :
    letI : Algebra ((Rfun R).obj i) ((Sfun R S hft).obj i) := ((φsys R S hft).app i).hom.toAlgebra
    Algebra.EssFiniteType ((Rfun R).obj i) ((Sfun R S hft).obj i) := by
  let inst : Algebra ((Rfun R).obj i) ((Sfun R S hft).obj i) :=
    ((φsys R S hft).app i).hom.toAlgebra
  let algRS : Algebra (Algebra.adjoin ℤ (↑i : Set R)) (Algebra.adjoin ℤ (Sset hft i)) :=
    (φincl hft i).toAlgebra
  have eftRS := essFiniteType_adjoin_Sset R S hft i
  have eftSSloc : Algebra.EssFiniteType (Algebra.adjoin ℤ (Sset hft i))
      (Localization.AtPrime (SA hft i)) :=
    Algebra.EssFiniteType.of_isLocalization _ (SA hft i).primeCompl
  let algRSi : Algebra (Algebra.adjoin ℤ (↑i : Set R)) (Localization.AtPrime (SA hft i)) :=
    (((φsys R S hft).app i).hom.comp
      (algebraMap (Algebra.adjoin ℤ (↑i : Set R)) (Localization.AtPrime (RA i)))).toAlgebra
  have hsquare : ((φsys R S hft).app i).hom.comp
      (algebraMap (Algebra.adjoin ℤ (↑i : Set R)) (Localization.AtPrime (RA i)))
      = (algebraMap (Algebra.adjoin ℤ (Sset hft i)) (Localization.AtPrime (SA hft i))).comp
        (φincl hft i) := by
    show (IsLocalization.map (Localization.AtPrime (SA hft i)) (φincl hft i) (φhle hft i)).comp
        (algebraMap (Algebra.adjoin ℤ (↑i : Set R)) (Localization.AtPrime (RA i))) = _
    exact IsLocalization.map_comp (φhle hft i)
  let algRRi : Algebra (Algebra.adjoin ℤ (↑i : Set R)) (Localization.AtPrime (RA i)) :=
    inferInstance
  have istRi : @IsScalarTower (Algebra.adjoin ℤ (↑i : Set R)) (Localization.AtPrime (RA i))
      (Localization.AtPrime (SA hft i)) algRRi.toSMul inst.toSMul algRSi.toSMul :=
    @IsScalarTower.of_algebraMap_eq' _ _ _ _ _ _ algRRi inst algRSi rfl
  have istSi : @IsScalarTower (Algebra.adjoin ℤ (↑i : Set R)) (Algebra.adjoin ℤ (Sset hft i))
      (Localization.AtPrime (SA hft i)) algRS.toSMul _ algRSi.toSMul :=
    @IsScalarTower.of_algebraMap_eq' _ _ _ _ _ _ algRS _ algRSi hsquare
  have eftRSi : @Algebra.EssFiniteType (Algebra.adjoin ℤ (↑i : Set R))
      (Localization.AtPrime (SA hft i)) _ _ algRSi :=
    @Algebra.EssFiniteType.comp (Algebra.adjoin ℤ (↑i : Set R)) (Algebra.adjoin ℤ (Sset hft i))
      (Localization.AtPrime (SA hft i)) _ _ _ algRS algRSi _ istSi eftRS eftSSloc
  exact @Algebra.EssFiniteType.of_comp (Algebra.adjoin ℤ (↑i : Set R))
    (Localization.AtPrime (RA i)) (Localization.AtPrime (SA hft i)) _ _ _ algRRi algRSi inst
    istRi eftRSi

/-- General localization-from-injective-map criterion: an injective ring hom
`g : A →+* C` whose image is "cofinal up to units" (every `c : C` is `g a / g t`
with `g t` a unit) exhibits `C` as the localization of `A` at `T = (units).comap g`. -/
lemma isLocalization_of_injective_surjUpToUnit
    {A C : Type} [CommRing A] [CommRing C] (g : A →+* C) (hg : Function.Injective g)
    (hsurj : ∀ c : C, ∃ (a : A) (t : A), IsUnit (g t) ∧ g a = g t * c) :
    @IsLocalization _ _ ((IsUnit.submonoid C).comap g) _ _ g.toAlgebra := by
  let := g.toAlgebra
  have halg : ∀ x : A, algebraMap A C x = g x := fun x => rfl
  refine ⟨?_, ?_, ?_⟩
  · exact fun y => y.property
  · intro c
    obtain ⟨a, t, ht, hat⟩ := hsurj c
    refine ⟨⟨a, ⟨t, ht⟩⟩, ?_⟩
    rw [halg, halg, hat]; ring
  · intro x y hxy
    rw [halg, halg] at hxy
    exact ⟨1, by simp [hg hxy]⟩

-- needed: without it `localizationOfQuotient_holds` fails (5 sites): Tactic `rewrite` failed: Did
-- not find an occurrence of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- Condition (4): for `A ⊆ B`, `S_B` is the localization of a quotient of
`S_A ⊗_{R_A} R_B`.  Argument: the algebraic map `S'_A ⊗_{R'_A} R'_B → S'_B` is
surjective (the generators of `S'_B` are images of generators of `S'_A` together
with elements of `R'_B`); passing to localizations, `S_B` is a localization of a
quotient of the pushout `S_A ⊗_{R_A} R_B`.  Take `I = ker` of the induced map and
`T` the image of the localization monoid. -/
lemma localizationOfQuotient_holds (hft : Algebra.EssFiniteType R S) (i j : Idx R) (h : i ≤ j) :
    -- Stacks 00QU (4), a true theorem. Strategy: I = ker desc, g = Quotient.lift
    -- (injective), T = {t : B/I | IsUnit (g t)} (or image of localization denoms);
    -- IsLocalization T g via 3-field constructor — surj uses S'_j ring-generated
    -- by image of pushout.inl (S_i side) and pushout.inr (R_j side), all in range desc.)
    Stacks.EssentialFiniteness.LocalColimit.LocalizationOfQuotient (φsys R S hft) h := by
  unfold Stacks.EssentialFiniteness.LocalColimit.LocalizationOfQuotient
  set B : CommRingCat := pushout ((φsys R S hft).app i) ((Rfun R).map h.hom) with hB
  set desc : B ⟶ (Sfun R S hft).obj j :=
    pushout.desc ((Sfun R S hft).map h.hom) ((φsys R S hft).app j)
      ((φsys R S hft).naturality h.hom).symm with hdesc
  -- key range lemma
  have hrange : ∀ e : Algebra.adjoin ℤ (Sset hft j),
      algebraMap (Algebra.adjoin ℤ (Sset hft j)) (Localization.AtPrime (SA hft j)) e
        ∈ Set.range desc.hom := by
    -- the two legs, at the level of underlying ring homs
    have leg_inl : desc.hom.comp (pushout.inl ((φsys R S hft).app i)
        ((Rfun R).map h.hom)).hom = ((Sfun R S hft).map h.hom).hom := by
      have hh := pushout.inl_desc ((Sfun R S hft).map h.hom) ((φsys R S hft).app j)
        ((φsys R S hft).naturality h.hom).symm
      have := congrArg CommRingCat.Hom.hom hh
      rwa [CommRingCat.hom_comp] at this
    have leg_inr : desc.hom.comp (pushout.inr ((φsys R S hft).app i)
        ((Rfun R).map h.hom)).hom = ((φsys R S hft).app j).hom := by
      have hh := pushout.inr_desc ((Sfun R S hft).map h.hom) ((φsys R S hft).app j)
        ((φsys R S hft).naturality h.hom).symm
      have := congrArg CommRingCat.Hom.hom hh
      rwa [CommRingCat.hom_comp] at this
    -- the range as a Subring; suffices to show membership there.
    suffices hsuff : ∀ (s : S) (hs : s ∈ Algebra.adjoin ℤ (Sset hft j)),
        algebraMap (Algebra.adjoin ℤ (Sset hft j)) (Localization.AtPrime (SA hft j)) ⟨s, hs⟩
          ∈ desc.hom.range by
      rintro ⟨e, he⟩
      have := hsuff e he
      rwa [RingHom.mem_range, ← Set.mem_range] at this
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with ⟨a, haj, rfl⟩ | hxg
        · -- x = algebraMap R S a, a ∈ j : use the R_j leg (inr)
          have hain : a ∈ Algebra.adjoin ℤ (↑j : Set R) := Algebra.subset_adjoin haj
          rw [RingHom.mem_range]
          refine ⟨(pushout.inr ((φsys R S hft).app i) ((Rfun R).map h.hom)).hom
            (algebraMap (Algebra.adjoin ℤ (↑j : Set R)) (Localization.AtPrime (RA j)) ⟨a, hain⟩),
                ?_⟩
          have hcf := RingHom.congr_fun leg_inr
            (algebraMap (Algebra.adjoin ℤ (↑j : Set R)) (Localization.AtPrime (RA j)) ⟨a, hain⟩)
          refine Eq.trans hcf ?_
          show (IsLocalization.map (Localization.AtPrime (SA hft j)) (φincl hft j) (φhle hft j) :
              Localization.AtPrime (RA j) →+* Localization.AtPrime (SA hft j))
              (algebraMap (Algebra.adjoin ℤ (↑j : Set R)) (Localization.AtPrime (RA j)) ⟨a, hain⟩)
            = _
          rw [IsLocalization.map_eq (φhle hft j) ⟨a, hain⟩]
          congr 1
        · -- x ∈ Sgens hft ⊆ Sset hft i : use the S_i leg (inl)
          have hxi : x ∈ Sset hft i := Or.inr hxg
          have hxin : x ∈ Algebra.adjoin ℤ (Sset hft i) := Algebra.subset_adjoin hxi
          rw [RingHom.mem_range]
          refine ⟨(pushout.inl ((φsys R S hft).app i) ((Rfun R).map h.hom)).hom
            (algebraMap (Algebra.adjoin ℤ (Sset hft i)) (Localization.AtPrime (SA hft i))
              ⟨x, hxin⟩), ?_⟩
          have hcf := RingHom.congr_fun leg_inl
            (algebraMap (Algebra.adjoin ℤ (Sset hft i)) (Localization.AtPrime (SA hft i)) ⟨x, hxin⟩)
          refine Eq.trans hcf ?_
          show ((Sfun R S hft).map h.hom).hom _ = _
          unfold Sfun
          rw [CommRingCat.hom_ofHom,
            Localization.localRingHom_to_map (SA hft i) (SA hft j) (Sincl hft h.hom)
              (SA_eq_comap_Sincl hft h.hom) ⟨x, hxin⟩]
          congr 1
    | algebraMap r =>
        rw [RingHom.mem_range]
        refine ⟨(r : B), ?_⟩
        rw [map_intCast]
        rw [show algebraMap (Algebra.adjoin ℤ (Sset hft j)) (Localization.AtPrime (SA hft j))
              ⟨(algebraMap ℤ S) r, _⟩ = (algebraMap ℤ (Localization.AtPrime (SA hft j))) r by
            rw [IsScalarTower.algebraMap_apply ℤ (Algebra.adjoin ℤ (Sset hft j))
              (Localization.AtPrime (SA hft j)) r]
            rfl]
        rw [eq_intCast]
    | add x y hx hy ihx ihy =>
        have heq : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : Algebra.adjoin ℤ (Sset hft j))
            = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
        rw [heq, map_add]
        exact Subring.add_mem _ ihx ihy
    | mul x y hx hy ihx ihy =>
        have heq : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : Algebra.adjoin ℤ (Sset hft j))
            = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [heq, map_mul]
        exact Subring.mul_mem _ ihx ihy
  -- surjectivity up to units of desc.hom
  have hsurj : ∀ c : (Sfun R S hft).obj j, ∃ (x y : B),
      IsUnit (desc.hom y) ∧ desc.hom x = desc.hom y * c := by
    intro c
    obtain ⟨⟨d, m⟩, hdm⟩ := IsLocalization.surj (S := Localization.AtPrime (SA hft j))
      (SA hft j).primeCompl c
    obtain ⟨x, hx⟩ := hrange d
    obtain ⟨y, hy⟩ := hrange (m : Algebra.adjoin ℤ (Sset hft j))
    refine ⟨x, y, ?_, ?_⟩
    · rw [hy]
      exact IsLocalization.map_units (Localization.AtPrime (SA hft j)) m
    · rw [hx, hy, mul_comm]; exact hdm.symm
  refine ⟨RingHom.ker desc.hom, (IsUnit.submonoid _).comap (RingHom.kerLift desc.hom),
    RingHom.kerLift desc.hom, ?_, ?_⟩
  · ext x; rw [RingHom.comp_apply, RingHom.kerLift_mk]
  · apply isLocalization_of_injective_surjUpToUnit
    · exact RingHom.kerLift_injective desc.hom
    · intro c
      obtain ⟨x, y, hyunit, hxy⟩ := hsurj c
      refine ⟨Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y, ?_, ?_⟩
      · rwa [RingHom.kerLift_mk]
      · rw [RingHom.kerLift_mk, RingHom.kerLift_mk]; exact hxy

end Stacks.EssentialFiniteness.LocalColimit

/-- Let `φ : R → S` be a local homomorphism of local rings
which is essentially of finite type.  Then `φ` is a filtered colimit of a system
of local homomorphisms `φ_λ : R_λ → S_λ` of local rings, where each `R_λ` is
essentially of finite type over `ℤ`, each `S_λ` is essentially of finite type
over `R_λ`, and for `λ ≤ μ` the map `S_λ ⊗_{R_λ} R_μ → S_μ` realizes `S_μ` as a
localization of a quotient of `S_λ ⊗_{R_λ} R_μ`. -/
@[stacks 00QU]
theorem exists_colimit_presentation_of_essFiniteType
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] (hφ : IsLocalHom (algebraMap R S))
    (hft : Algebra.EssFiniteType R S) :
    ∃ (Λ : Type) (_ : PartialOrder Λ) (_ : IsDirected Λ (· ≤ ·)) (_ : Nonempty Λ)
      (Rf Sf : Λ ⥤ CommRingCat) (φsys : Rf ⟶ Sf),
      -- each `R_λ`, `S_λ` is a local ring
      (∀ i, IsLocalRing (Rf.obj i)) ∧ (∀ i, IsLocalRing (Sf.obj i)) ∧
      -- each `φ_λ` is a local homomorphism
      (∀ i, IsLocalHom (φsys.app i).hom) ∧
      -- each transition map is a local homomorphism
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (Rf.map h.hom).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (Sf.map h.hom).hom) ∧
      -- (1) the colimit of the system is `φ : R → S` (up to canonical isomorphism)
      (∃ (iR : colimit Rf ≅ CommRingCat.of R) (iS : colimit Sf ≅ CommRingCat.of S),
        iR.inv ≫ colimMap φsys ≫ iS.hom = CommRingCat.ofHom (algebraMap R S)) ∧
      -- (2) each `R_λ` is essentially of finite type over `ℤ`
      (∀ i, Algebra.EssFiniteType ℤ (Rf.obj i)) ∧
      -- (3) each `S_λ` is essentially of finite type over `R_λ`
      (∀ i, letI : Algebra (Rf.obj i) (Sf.obj i) := (φsys.app i).hom.toAlgebra
        Algebra.EssFiniteType (Rf.obj i) (Sf.obj i)) ∧
      -- (4) for `i ≤ j`, `S_j` is the localization of a quotient of `S_i ⊗_{R_i} R_j`
      (∀ (i j : Λ) (h : i ≤ j), Stacks.EssentialFiniteness.LocalColimit.LocalizationOfQuotient φsys
        h) :=
  -- `LocalizationOfQuotient` satisfiable via I=ker, T=⊥; condition (1) square
  -- direction-coherent).
  -- Assemble the system from the construction in the `Stacks.EssentialFiniteness.LocalColimit`
  -- namespace:
  -- index set `Finset R`, functors `Rfun`/`Sfun`, nat. transf. `φsys`, and the
  -- named property lemmas above.
  ⟨Stacks.EssentialFiniteness.LocalColimit.Idx R, inferInstance, inferInstance,
    inferInstance,
    Stacks.EssentialFiniteness.LocalColimit.Rfun R, Stacks.EssentialFiniteness.LocalColimit.Sfun R S
      hft, Stacks.EssentialFiniteness.LocalColimit.φsys R S hft,
    Stacks.EssentialFiniteness.LocalColimit.isLocalRing_Rfun R,
      Stacks.EssentialFiniteness.LocalColimit.isLocalRing_Sfun R S hft,
    Stacks.EssentialFiniteness.LocalColimit.isLocalHom_φsys R S hφ hft,
      Stacks.EssentialFiniteness.LocalColimit.isLocalHom_Rfun_map R,
    Stacks.EssentialFiniteness.LocalColimit.isLocalHom_Sfun_map R S hft,
      Stacks.EssentialFiniteness.LocalColimit.colimit_iso R S hft,
    Stacks.EssentialFiniteness.LocalColimit.essFiniteType_Rfun R,
      Stacks.EssentialFiniteness.LocalColimit.essFiniteType_Sfun R S hft,
    Stacks.EssentialFiniteness.LocalColimit.localizationOfQuotient_holds R S hft⟩

end
