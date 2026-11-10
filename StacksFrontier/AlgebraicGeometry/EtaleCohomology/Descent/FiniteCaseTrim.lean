module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseIdempotents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.ShrunkStagePrime

/-!
# Trimming the two decompositions: the finite and integral cases of property (B)

This file completes the finite case of property (B) for the étale topology, [Stacks, Tag 04DQ],
and with it the integral case, [Stacks, Tag 04DR]. What remained was the single ring-theoretic
statement `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents`: given the output of
the étale local structure theorem [Stacks, Tag 00UL] — a base `A'` with a prime `p'`, a
module-finite `A'`-algebra `P`, an étale `P`-algebra `E` whose spectrum surjects onto `Spec P`,
and two complete orthogonal families of idempotents `b` of `P` and `c` of `E` carrying the
finiteness and residue-field information of that theorem — one must produce a single `a ∉ p'`
after whose inversion `P` becomes a finite product of `E`-algebras.

## The shape of the argument

The decomposition asked for is the one the family `b` already gives: by
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver` one
inversion in the base turns `b` into a complete orthogonal family of `P[1/a]` indexed by exactly
those factors `P[1/b i]` that carry a prime over `p'`, and
`Stacks.EtaleCohomology.completeOrthogonalIdempotentsAlgEquivPi` then writes `P[1/a]` as the
product of those factors. All that is missing is that each factor be an algebra over `E`,
compatibly with `P`; that is the content of `Stacks.EtaleCohomology.SubordinateFactor`, and
proving it one index at a time — the per-index trivialisation
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_bijective_awayMap_algebraMap_of_etale_pair` —
is what this file does.

The per-index step compares the factor `F = P[1/β]` of the first decomposition, for
`β = b i.castSucc`, with a factor of the second. It needs `F → D` to be defined at all, that is
it needs `D` to be an algebra over `F`, and this is where the naive choice `D = E[1/γ]` for a
matching `γ = c j.castSucc` fails: the image of `β` in `E[1/γ]` is an idempotent, not a unit, so
there is no map `P[1/β] → E[1/γ]`. The remedy used here is not to shrink the base and re-enter
the whole argument over `A'[1/a]`, but to *shrink the covering factor instead*: the comparison is
made with

  `D = E[1/(γ · β)]`,

the localisation of `E` away from the product of the two idempotents. The image of `β` in `D` is
then invertible, because it divides the unit `γ · β`, so `D` is an `F`-algebra by the universal
property of `F`; and `D` is still module-finite over `A'`, because `γ · β` is again an idempotent
and so `D` is a quotient of the module-finite algebra `E[1/γ]`, which is
`Stacks.EtaleCohomology.moduleFinite_away_mul_of_isIdempotentElem`. Every other hypothesis of the
per-index trivialisation transports to `D` without further shrinking: a prime of `D` avoiding
`γ · β` avoids `γ`, so uniqueness over `p'` is inherited, and the residue field at a prime of `D`
is the residue field of its contraction to `E`, because `E → D` is a localisation and hence
surjective on stalks.

The finitely many elements of `A'` produced, one for each surviving index, are combined into one
by `Stacks.EtaleCohomology.exists_notMem_forall_dvd_of_forall_exists`, which is why the per-index
statements are proved for every multiple of the element they produce.

## Main definitions

* `Stacks.EtaleCohomology.SubordinateFactor`: the factor of an algebra `X` over `P` cut out by an
  idempotent is, as a `P`-algebra, an algebra over `E` compatibly with `P`.

## Main results

* `Stacks.EtaleCohomology.moduleFinite_away_mul_of_isIdempotentElem`: localising away from the
  product of two idempotents preserves module-finiteness over the base.
* `Stacks.EtaleCohomology.awayAlgebraOfIsUnit` and
  `Stacks.EtaleCohomology.isScalarTower_awayAlgebraOfIsUnit`: an algebra in which an element is
  invertible is an algebra over the localisation away from that element.
* `Stacks.EtaleCohomology.exists_notMem_forall_dvd_subordinateFactor_of_etale_pair`: **the
  per-index step.** With the two factors `F` and `D` given abstractly, one inversion in the base
  makes the factor of `P[1/a]` cut out by the idempotent an algebra over `E`.
* `Stacks.EtaleCohomology.exists_notMem_forall_dvd_subordinateFactor`: the same with the two
  factors taken to be `P[1/β]` and `E[1/(γ · β)]`, which is the form the local structure theorem
  delivers its data in.
* `Stacks.EtaleCohomology.hasFiniteCaseDecompositionOfIdempotents`: the trimming problem
  `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents` is solved.
* `Stacks.EtaleCohomology.hasPropertyB_of_isFinite`: **property (B) for a finite morphism of
  schemes**, [Stacks, Tag 04DQ].
* `Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom`: **property (B) for an integral morphism
  of schemes**, [Stacks, Tag 04DR].

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
* [Stacks Project, Tag 00UL](https://stacks.math.columbia.edu/tag/00UL)
-/

@[expose] public section

open AlgebraicGeometry

universe u v w t

namespace Stacks.EtaleCohomology

section Away

/-- **Localising away from the product of two idempotents preserves module-finiteness.** If `R` is
an algebra over `A` whose localisation away from an idempotent `e₁` is module-finite over `A`, then
its localisation away from `e₁ * e₂` is module-finite over `A` for every idempotent `e₂`.

Both `e₁ * e₂` and `e₁` become invertible in `R[1/(e₁ * e₂)]`, so that ring receives a map from
`R[1/e₁]`; the map is surjective because `R → R[1/(e₁ * e₂)]` already is, the element inverted
being idempotent.

In the finite case of property (B), [Stacks, Tag 04DQ], this is what makes the covering factor
`E[1/(c j · b i)]` used in `Stacks.EtaleCohomology.exists_notMem_forall_dvd_subordinateFactor`
module-finite over the base: the étale local structure theorem [Stacks, Tag 00UL] supplies
module-finiteness of `E[1/c j]` only, and the further localisation is away from an idempotent and
therefore a quotient. -/
theorem moduleFinite_away_mul_of_isIdempotentElem {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] {e₁ e₂ : R} (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂)
    [Module.Finite A (Localization.Away e₁)] :
    Module.Finite A (Localization.Away (e₁ * e₂)) := by
  have h : IsIdempotentElem (e₁ * e₂) := h₁.mul h₂
  have hunit : IsUnit (algebraMap R (Localization.Away (e₁ * e₂)) e₁) :=
    IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_right e₁ e₂)
  let g : Localization.Away e₁ →ₐ[A] Localization.Away (e₁ * e₂) :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom A R _) e₁ hunit
  refine Module.Finite.of_surjective g.toLinearMap fun z => ?_
  obtain ⟨r, rfl⟩ :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (S := Localization.Away (e₁ * e₂)) _ h z
  exact ⟨algebraMap R _ r, IsLocalization.Away.lift_eq _ hunit r⟩

/-- **A localisation away from an element acts on any algebra in which that element is
invertible.** If `S` is the localisation of `R` away from `x` and `T` is an `R`-algebra in which
the image of `x` is a unit, then `T` is an `S`-algebra, by the universal property of `S`.

This is the algebra structure the per-index step of the finite case of property (B),
[Stacks, Tag 04DQ], puts on the covering factor `E[1/(γ · β)]` over the factor `P[1/β]`: the image
of `β` divides the unit `γ · β` and is therefore invertible, which is precisely why the covering
factor is cut down by the *product* of the two idempotents and not by `γ` alone. -/
@[instance_reducible]
noncomputable def awayAlgebraOfIsUnit {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (x : R) [IsLocalization.Away x S]
    (hx : IsUnit (algebraMap R T x)) : Algebra S T :=
  (IsLocalization.Away.lift x hx).toAlgebra

/-- **The algebra structure of `Stacks.EtaleCohomology.awayAlgebraOfIsUnit` is compatible with the
base.** The map `S → T` it installs restricts on `R` to the structure map of `T`, which is the
defining property of the lift out of a localisation. -/
theorem isScalarTower_awayAlgebraOfIsUnit {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (x : R) [IsLocalization.Away x S]
    (hx : IsUnit (algebraMap R T x)) :
    letI := awayAlgebraOfIsUnit (S := S) x hx
    IsScalarTower R S T :=
  let := awayAlgebraOfIsUnit (S := S) x hx
  .of_algebraMap_eq fun z => (IsLocalization.Away.lift_eq x hx z).symm

/-- **Removing the middle ring of a tower of towers.** If `A → R → S`, `R → S → T` and `A → R → T`
are scalar towers then so is `A → S → T`: both composites `A → T` factor through `R`, and the two
factorisations agree because `A → R → S → T` is `A → R → T`.

This is how the tower `A' → P[1/β] → E[1/(γ · β)]` is obtained in the per-index step of
[Stacks, Tag 04DQ] from the tower over `P` supplied by
`Stacks.EtaleCohomology.isScalarTower_awayAlgebraOfIsUnit`: the per-index trivialisation needs the
tower over the *base*, since the element it produces is inverted there. -/
theorem isScalarTower_of_isScalarTower_mid {A R S T : Type*} [CommRing A] [CommRing R]
    [CommRing S] [CommRing T] [Algebra A R] [Algebra A S] [Algebra A T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower A R S] [IsScalarTower R S T]
    [IsScalarTower A R T] :
    IsScalarTower A S T :=
  .of_algebraMap_eq fun z => by
    rw [IsScalarTower.algebraMap_apply A R T z, IsScalarTower.algebraMap_apply R S T,
      IsScalarTower.algebraMap_apply A R S]

end Away

section Subordinate

/-- **A factor of a `P`-algebra subordinate to the covering `E`.** For an algebra `X` over `P` and
an element `ε` of `X`, this says that the factor `X ⧸ (1 - ε)` of `X` cut out by `ε` — the
localisation `X[1/ε]` when `ε` is idempotent — is, as a `P`-algebra, isomorphic to an algebra over
`E` compatibly with `P`.

This is exactly what the finite case of property (B), [Stacks, Tag 04DQ], asks of each factor of
the decomposition it produces: the decomposition must be *subordinate* to the étale covering, which
means each of its pieces carries a morphism to the covering over the base, and a factor is a piece
of the decomposition only once it has such a structure. The statement is phrased with an auxiliary
ring `G` rather than as an algebra structure on the quotient itself so that the factor produced by
the per-index comparison — a localisation of the covering side — can be handed over as it stands,
with no transport of algebra structures along an isomorphism. -/
def SubordinateFactor (P E X : Type u) [CommRing P] [CommRing E] [CommRing X] [Algebra P E]
    [Algebra P X] (ε : X) : Prop :=
  ∃ (G : Type u) (_ : CommRing G) (_ : Algebra P G) (_ : Algebra E G) (_ : IsScalarTower P E G),
    Nonempty ((X ⧸ Ideal.span {1 - ε}) ≃ₐ[P] G)

/-- **Reindexing a product of algebras along a universe lift.** The `L`-indexed product of a
family of `R`-algebras is the `ULift L`-indexed product of the same family read through
`ULift.down`, as `R`-algebras.

The ring-theoretic statements of the finite case of property (B), [Stacks, Tag 04DQ], ask for a
decomposition indexed by a type in the same universe as the rings, while the index type the
decomposition of [Stacks, Tag 00UL] comes with is a subtype of `Fin n` and therefore lives in
`Type 0`. This is the bookkeeping that bridges the two. -/
def piULiftAlgEquiv (R : Type*) [CommSemiring R] {L : Type v} (G : L → Type w)
    [∀ l, Semiring (G l)] [∀ l, Algebra R (G l)] :
    ((l : L) → G l) ≃ₐ[R] ((l : ULift.{t} L) → G l.down) where
  toFun x l := x l.down
  invFun y l := y (ULift.up l)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end Subordinate

section PerIndex

/-- **The per-index step of the finite case of property (B), with the two factors given
abstractly.** In the situation of the étale local structure theorem [Stacks, Tag 00UL] — a base
`A'` with a prime `p'`, a `P`-algebra `E` which is étale, the factor `F = P[1/x]` of a
decomposition of `P` at an idempotent `x`, module-finite over `A'` and with `t` as its only prime
over `p'`, and a factor `D = E[1/y]` of a decomposition of the covering, module-finite over `F`,
with a prime `s` over `t`, at most one prime over `p'` and `κ(s)/κ(p')` purely inseparable — there
is a single `a ∉ p'` such that, for every multiple `a'` of `a`, the factor of `P[1/a']` cut out by
`x` is subordinate to the covering `E`.

The comparison itself is
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_bijective_awayMap_algebraMap_of_etale_pair`, which
makes `F[1/a'] → D[1/a']` bijective. What is added here is the identification of its source with
the factor of `P[1/a']`: both `P[1/a'] ⧸ (1 - x)` and `F[1/a'] = P[1/x][1/a']` are localisations of
`P` away from `a' · x` — the first because `x` is idempotent, by
`IsLocalization.Away.quotient_of_isIdempotentElem`, and both by `IsLocalization.Away.mul` — hence
canonically isomorphic as `P`-algebras. The ring handed over as the `E`-algebra is `D[1/a']`, which
is an algebra over `E` through `D` and over `P` compatibly. -/
theorem exists_notMem_forall_dvd_subordinateFactor_of_etale_pair
    {A' P E F D : Type u} [CommRing A'] [CommRing P] [CommRing E] [CommRing F] [CommRing D]
    [Algebra A' P] [Algebra A' F] [Algebra A' D]
    [Algebra P E] [Algebra P F] [Algebra P D] [Algebra E D] [Algebra F D]
    [IsScalarTower A' P F] [IsScalarTower A' P D]
    [IsScalarTower P E D] [IsScalarTower P F D] [IsScalarTower A' F D]
    [Algebra.Etale P E] [Module.Finite F D] [Module.Finite A' F]
    (p' : Ideal A') [p'.IsPrime]
    (x : P) (hx : IsIdempotentElem x) [IsLocalization.Away x F] (y : E)
    [IsLocalization.Away y D]
    (t : Ideal F) [t.IsPrime] [t.LiesOver p'] (s : Ideal D) [s.IsPrime] [s.LiesOver t]
    [s.LiesOver p']
    [Algebra (Localization.AtPrime p') (Localization.AtPrime t)]
    [IsScalarTower A' (Localization.AtPrime p') (Localization.AtPrime t)]
    [Algebra (Localization.AtPrime t) (Localization.AtPrime s)]
    [IsScalarTower F (Localization.AtPrime t) (Localization.AtPrime s)]
    [Algebra (Localization.AtPrime p') (Localization.AtPrime s)]
    [IsScalarTower A' (Localization.AtPrime p') (Localization.AtPrime s)]
    (huniqF : ∀ u : Ideal F, u.IsPrime → u.LiesOver p' → u = t)
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (hres : IsPurelyInseparable p'.ResidueField s.ResidueField) :
    ∃ a ∉ p', ∀ a' : A', a ∣ a' →
      SubordinateFactor P E (Localization.Away (algebraMap A' P a'))
        (algebraMap P (Localization.Away (algebraMap A' P a')) x) := by
  obtain ⟨a, hap, hbij⟩ :=
    exists_notMem_forall_dvd_bijective_awayMap_algebraMap_of_etale_pair p' x y t s huniqF huniq
      hres
  refine ⟨a, hap, fun a' hdvd => ?_⟩
  have hidem : IsIdempotentElem
      (algebraMap P (Localization.Away (algebraMap A' P a')) x) := hx.map _
  have : IsLocalization.Away (algebraMap P (Localization.Away (algebraMap A' P a')) x)
      (Localization.Away (algebraMap A' P a') ⧸
        Ideal.span {1 - algebraMap P (Localization.Away (algebraMap A' P a')) x}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem hidem
  have : IsLocalization.Away (algebraMap A' P a' * x)
      (Localization.Away (algebraMap A' P a') ⧸
        Ideal.span {1 - algebraMap P (Localization.Away (algebraMap A' P a')) x}) :=
    IsLocalization.Away.mul' (Localization.Away (algebraMap A' P a')) _ _ _
  have : IsLocalization.Away (algebraMap P F (algebraMap A' P a'))
      (Localization.Away (algebraMap A' F a')) := by
    rw [← IsScalarTower.algebraMap_apply]; infer_instance
  have : IsLocalization.Away (algebraMap A' P a' * x)
      (Localization.Away (algebraMap A' F a')) :=
    IsLocalization.Away.mul F (Localization.Away (algebraMap A' F a')) x (algebraMap A' P a')
  refine ⟨Localization.Away (algebraMap F D (algebraMap A' F a')), inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨?_⟩⟩
  refine (IsLocalization.algEquiv (Submonoid.powers (algebraMap A' P a' * x))
    (Localization.Away (algebraMap A' P a') ⧸
      Ideal.span {1 - algebraMap P (Localization.Away (algebraMap A' P a')) x})
    (Localization.Away (algebraMap A' F a'))).trans ?_
  exact AlgEquiv.ofBijective
    (Localization.awayMapₐ (IsScalarTower.toAlgHom P F D) (algebraMap A' F a'))
    (hbij a' hdvd)

/-- **The per-index step of the finite case of property (B).** Let `A'` be a base with a prime
`p'`, let `P` be module-finite over `A'` and `E` étale over `P`, let `β` be an idempotent of `P`
whose factor `P[1/β]` is module-finite over `A'` and carries at most one prime over `p'`, and let
`γ` be an idempotent of `E` whose factor `E[1/γ]` is module-finite over `A'` and carries at most
one prime over `p'`, with purely inseparable residue field there. Suppose `q` is a prime of `P`
over `p'` avoiding `β` and `sE` a prime of `E` over `q` avoiding `γ`. Then one inversion in the
base — and every further one — makes the factor of `P[1/a']` cut out by `β` subordinate to the
covering `E`.

This is `Stacks.EtaleCohomology.exists_notMem_forall_dvd_subordinateFactor_of_etale_pair` with the
two factors chosen: `F = P[1/β]` and, crucially, `D = E[1/(γ · β)]` rather than `E[1/γ]`. The
product of the two idempotents is again an idempotent, and the point of taking it is that it makes
`D` an algebra over `F` — the image of `β` divides the unit `γ · β` — without shrinking the base
first, while keeping `D` module-finite over `A'` by
`Stacks.EtaleCohomology.moduleFinite_away_mul_of_isIdempotentElem`. The remaining hypotheses
transport to `D` unchanged: a prime of `D` avoiding `γ · β` contracts to a prime of `E` avoiding
`γ`, which gives uniqueness over `p'` through
`Stacks.EtaleCohomology.forall_eq_of_forall_eq_away`, and the residue field at a prime of `D` is
that of its contraction because `E → D` is a localisation, which is
`Stacks.EtaleCohomology.isPurelyInseparable_residueField_of_surjectiveOnStalks`. -/
theorem exists_notMem_forall_dvd_subordinateFactor
    {A' P E : Type u} [CommRing A'] [CommRing P] [CommRing E]
    [Algebra A' P] [Algebra A' E] [Algebra P E] [IsScalarTower A' P E]
    [Module.Finite A' P] [Algebra.Etale P E]
    (p' : Ideal A') [p'.IsPrime]
    {β : P} (hβ : IsIdempotentElem β) [Module.Finite A' (Localization.Away β)]
    {γ : E} (hγ : IsIdempotentElem γ) [Module.Finite A' (Localization.Away γ)]
    (q : Ideal P) [q.IsPrime] [q.LiesOver p'] (hβq : β ∉ q)
    (sE : Ideal E) [sE.IsPrime] [sE.LiesOver q] [sE.LiesOver p'] (hγs : γ ∉ sE)
    (hbuniq : ∀ q₁ q₂ : Ideal P, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      β ∉ q₁ → β ∉ q₂ → q₁ = q₂)
    (hcuniq : ∀ u₁ u₂ : Ideal E, u₁.IsPrime → u₂.IsPrime → u₁.LiesOver p' → u₂.LiesOver p' →
      γ ∉ u₁ → γ ∉ u₂ → u₁ = u₂)
    (hcres : letI := Localization.AtPrime.algebraOfLiesOver p' sE
      IsPurelyInseparable p'.ResidueField sE.ResidueField) :
    ∃ a ∉ p', ∀ a' : A', a ∣ a' →
      SubordinateFactor P E (Localization.Away (algebraMap A' P a'))
        (algebraMap P (Localization.Away (algebraMap A' P a')) β) := by
  have hβ' : IsIdempotentElem (algebraMap P E β) := hβ.map _
  have hunitE : IsUnit (algebraMap E (Localization.Away (γ * algebraMap P E β))
      (algebraMap P E β)) :=
    IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_left (algebraMap P E β) γ)
  have hunit : IsUnit (algebraMap P (Localization.Away (γ * algebraMap P E β)) β) := by
    rw [IsScalarTower.algebraMap_apply P E (Localization.Away (γ * algebraMap P E β))]
    exact hunitE
  let : Algebra (Localization.Away β) (Localization.Away (γ * algebraMap P E β)) :=
    awayAlgebraOfIsUnit β hunit
  have : IsScalarTower P (Localization.Away β) (Localization.Away (γ * algebraMap P E β)) :=
    isScalarTower_awayAlgebraOfIsUnit β hunit
  have : IsScalarTower A' (Localization.Away β) (Localization.Away (γ * algebraMap P E β)) :=
    isScalarTower_of_isScalarTower_mid (R := P)
  have : Module.Finite A' (Localization.Away (γ * algebraMap P E β)) :=
    moduleFinite_away_mul_of_isIdempotentElem hγ hβ'
  have : Module.Finite (Localization.Away β) (Localization.Away (γ * algebraMap P E β)) :=
    moduleFinite_of_moduleFinite_base A' _ _
  have hβnotsE : algebraMap P E β ∉ sE := notMem_algebraMap_of_liesOver q sE hβq
  have hynot : γ * algebraMap P E β ∉ sE := fun hm =>
    (‹sE.IsPrime›.mem_or_mem hm).elim hγs hβnotsE
  have : (q.map (algebraMap P (Localization.Away β))).IsPrime :=
    isPrime_map_algebraMap_of_notMem β q hβq
  have : (q.map (algebraMap P (Localization.Away β))).LiesOver p' :=
    liesOver_map_algebraMap_of_notMem β p' q hβq
  have : (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))).IsPrime :=
    isPrime_map_algebraMap_of_notMem _ sE hynot
  have hsE : (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))).under E = sE :=
    under_map_algebraMap_of_notMem _ sE hynot
  have hsP : (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))).under P = q := by
    rw [← Ideal.under_under (A := P) (B := E)
      (𝔓 := sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))), hsE]
    exact (sE.over_def q).symm
  have : (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))).LiesOver
      (q.map (algebraMap P (Localization.Away β))) := by
    refine ⟨?_⟩
    rw [← IsLocalization.map_under (Submonoid.powers β) (Localization.Away β)
      ((sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))).under
        (Localization.Away β)), Ideal.under_under, hsP]
  have : (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))).LiesOver p' :=
    Ideal.LiesOver.trans _ (q.map (algebraMap P (Localization.Away β))) p'
  have huniqF :=
    forall_eq_map_of_forall_eq_away (S := Localization.Away β) β p' hbuniq q hβq
  have huniqD := forall_eq_of_forall_eq_away
    (S := Localization.Away (γ * algebraMap P E β)) (γ * algebraMap P E β) p'
    (fun u₁ u₂ h₁ h₂ o₁ o₂ n₁ n₂ => hcuniq u₁ u₂ h₁ h₂ o₁ o₂
      (fun hm => n₁ (Ideal.mul_mem_right _ _ hm)) (fun hm => n₂ (Ideal.mul_mem_right _ _ hm)))
  let := Localization.AtPrime.algebraOfLiesOver p' (q.map (algebraMap P (Localization.Away β)))
  let := Localization.AtPrime.algebraOfLiesOver (q.map (algebraMap P (Localization.Away β)))
    (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β))))
  let := Localization.AtPrime.algebraOfLiesOver p'
    (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β))))
  have hresD : IsPurelyInseparable p'.ResidueField
      (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))).ResidueField :=
    isPurelyInseparable_residueField_of_surjectiveOnStalks p'
      (IsScalarTower.toAlgHom A' E (Localization.Away (γ * algebraMap P E β)))
      (RingHom.surjectiveOnStalks_of_isLocalization
        (Submonoid.powers (γ * algebraMap P E β)) _) sE _ hsE.symm hcres
  exact exists_notMem_forall_dvd_subordinateFactor_of_etale_pair p' β hβ
    (γ * algebraMap P E β) (q.map (algebraMap P (Localization.Away β)))
    (sE.map (algebraMap E (Localization.Away (γ * algebraMap P E β)))) huniqF huniqD hresD

end PerIndex

section Main

open Classical in
/-- **The trimming problem of the finite case of property (B) is solved.** This is
`Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents`: given the two complete
orthogonal families of idempotents that the étale local structure theorem [Stacks, Tag 00UL]
attaches to a module-finite `A'`-algebra `P` and to an étale `P`-algebra `E` surjective on
spectra, one localisation of `A'` outside the chosen prime `p'` turns `P` into a finite product of
`E`-algebras.

The index set is the set of those indices `i` of the `b`-family whose factor `P[1/b i]` really
does carry a prime over `p'`; by
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver` one
inversion in the base kills all the other factors, so that `b` restricted to that set is still a
complete orthogonal family of `P[1/a]` and
`Stacks.EtaleCohomology.completeOrthogonalIdempotentsAlgEquivPi` exhibits `P[1/a]` as the product
of the corresponding factors. Each of those factors is made an algebra over `E` by
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_subordinateFactor`, whose two inputs at the index
`i` are the prime of `P` over `p'` that the index was chosen for and a prime of `E` above it lying
in one of the finite factors of the `c`-family, supplied by
`Stacks.EtaleCohomology.exists_liesOver_notMem_castSucc`. The finitely many elements of `A'` so
produced are multiplied into one by
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_of_forall_exists`, which is legitimate because
every statement involved holds not only at the element it produces but at all of its multiples. -/
theorem hasFiniteCaseDecompositionOfIdempotents :
    HasFiniteCaseDecompositionOfIdempotents.{u} := by
  intro A' P E _ _ _ _ _ _ _ _ _ hsurj p' _ n b c hb hc hbfin hbuniq hbres hblast
    hcfin hcuniq hcres hclast
  have hper : ∀ l : {i : Fin n // ∃ q : Ideal P, ∃ _ : q.IsPrime,
        q.LiesOver p' ∧ b i.castSucc ∉ q},
      ∃ a ∉ p', ∀ a' : A', a ∣ a' →
        SubordinateFactor P E (Localization.Away (algebraMap A' P a'))
          (algebraMap P (Localization.Away (algebraMap A' P a')) (b l.1.castSucc)) := by
    intro l
    obtain ⟨q, hq, hqo, hbq⟩ := l.2
    have := hq
    have := hqo
    obtain ⟨sE, hsEp, hsEo, j, hjs⟩ := exists_liesOver_notMem_castSucc p' hc hclast hsurj q
    have := hsEp
    have := hsEo
    have : sE.LiesOver p' := Ideal.LiesOver.trans sE q p'
    have := hbfin l.1
    have := hcfin j
    exact exists_notMem_forall_dvd_subordinateFactor p' (hb.idem _) (hc.idem _) q hbq sE hjs
      (hbuniq l.1) (hcuniq j) (hcres j sE hsEp ‹_› hjs)
  obtain ⟨a₁, ha₁, hfam⟩ :=
    exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver p' hb hblast
  obtain ⟨a₂, ha₂, hsub⟩ := exists_notMem_forall_dvd_of_forall_exists p' _ hper
  choose G hGring hGalgP hGalgE hGtower hGequiv using hsub (a₁ * a₂) (dvd_mul_left a₂ a₁)
  let instGring := hGring
  let instGalgP := hGalgP
  let instGalgE := hGalgE
  let instGtower := hGtower
  refine ⟨a₁ * a₂, fun hmem => (‹p'.IsPrime›.mem_or_mem hmem).elim ha₁ ha₂,
    ULift.{u} {i : Fin n // ∃ q : Ideal P, ∃ _ : q.IsPrime, q.LiesOver p' ∧ b i.castSucc ∉ q},
    inferInstance, fun l => G l.down, fun l => hGring l.down, fun l => hGalgP l.down,
    fun l => hGalgE l.down, fun l => hGtower l.down, ⟨?_⟩⟩
  exact ((completeOrthogonalIdempotentsAlgEquivPi (A := P)
      (hfam (a₁ * a₂) (dvd_mul_right a₁ a₂))).trans
    (AlgEquiv.piCongrRight fun l => (hGequiv l).some)).trans (piULiftAlgEquiv P G)

/-- **Property (B) for a finite morphism of schemes.** Every étale covering of the base change of
a finite morphism admits, after a further étale covering of the base, a componentwise subordinate
disjoint-union decomposition.

This is [Stacks, Tag 04DQ]. It is
`Stacks.EtaleCohomology.hasPropertyB_of_isFinite_of_idempotents` with its one remaining input,
`Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents`, discharged by
`Stacks.EtaleCohomology.hasFiniteCaseDecompositionOfIdempotents`. -/
@[stacks 04DQ]
theorem hasPropertyB_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] : HasPropertyB f :=
  hasPropertyB_of_isFinite_of_idempotents hasFiniteCaseDecompositionOfIdempotents f

/-- **Property (B) for an integral morphism of schemes.** Every étale covering of the base change
of an integral morphism admits, after a further étale covering of the base, a componentwise
subordinate disjoint-union decomposition.

This is [Stacks, Tag 04DR]. The integral case is deduced from the finite case
`Stacks.EtaleCohomology.hasPropertyB_of_isFinite` by the limit argument
`Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_finite`: an integral morphism over an
affine base is a directed limit of finite ones, a finite affine étale cover of the limit descends
to a finite stage, and the decomposition supplied there is transported back. -/
@[stacks 04DR]
theorem hasPropertyB_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    HasPropertyB f :=
  hasPropertyB_of_isIntegralHom_of_finite
    (fun _ _ g hg => @hasPropertyB_of_isFinite _ _ g hg) f

end Main

end Stacks.EtaleCohomology

end
