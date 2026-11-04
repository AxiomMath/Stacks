module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic

/-!
# The Chern classes of a finite locally free module as bivariant classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `O_X`-module of rank `r` and
let `0 ≤ p ≤ r`. **Stacks 0B7H** says that the rule assigning to `f : X' ⟶ X` the operation

  `c_p(f^*ℰ) ∩ - : CH_k(X') ⟶ CH_{k-p}(X')`

is a bivariant class of degree `p`, that is, an element of `A^p(X ⟶ X)`.

Its cap operation is forced by the characterization of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic`, so the content of the lemma is the
three naturality axioms of Stacks 0B76: the projection formula of Stacks 02U9, the flat-pullback
identity of Stacks 02U8 and the Gysin identity of Stacks 0B7G. Each of those is an identity on
the test scheme `X'`, while the axioms of a bivariant class are identities on the chosen
categorical pullback `X ×_X X'`; this file transports all three across the isomorphism
`X ×_X X' ≅ X'` and assembles the class.

## Main definitions

* `Stacks.Chow.IdentityCapRule.FlatNaturality` — **Stacks 02U8 read on the test schemes**: an
  identity cap rule commutes with flat pullback of fixed relative dimension.
* `Stacks.Chow.IdentityCapRule.GysinNaturality` — **Stacks 0B7G read on the test schemes**: an
  identity cap rule commutes with the Gysin map of a Gysin system.
* `Stacks.Chow.GysinSystem.IsNaturalUnderInverseIso` — the isomorphism case of Stacks 02TA for a
  Gysin system, with the invertible module given on the source of the isomorphism.
* `Stacks.Chow.chernIdentityCapRuleOfRank` — the rule `α ↦ c_j(g^*ℰ) ∩ α` of a module that is
  finite locally free of rank `r`.
* `Stacks.Chow.chernClassBivariant` — **Stacks 0B7H**, the bivariant class `c_j(ℰ) ∈ A^j(X)`.

## Main results

* `Stacks.Chow.pullbackPreservesRank_of_isFiniteLocallyFreeOfRank` — a finite locally free module
  of rank `r` pulls back to one of rank `r`, so the rank hypothesis of the Chern class operations
  is automatic for such a module.
* `Stacks.Chow.IdentityCapRule.transportFlatNaturality` — **axiom (2) of Stacks 0B76 from Stacks
  02U8**: the flat-pullback identity on the test schemes implies the one on the chosen pullbacks.
  The transport is the isomorphism case of Stacks 02RG.
* `Stacks.Chow.IdentityCapRule.transportGysinNaturality` — **axiom (3) of Stacks 0B76 from Stacks
  0B7G**: the Gysin identity on the test schemes implies the one on the chosen pullbacks, granted
  the isomorphism case of Stacks 02TA for the Gysin system.
* `Stacks.Chow.isChernClassBivariant_chernClassBivariant` — **Stacks 0B7H**: the class
  constructed below caps by `c_j(g^*ℰ) ∩ -` on every test scheme, so it is the bivariant Chern
  class.
* `Stacks.Chow.chernClassBivariant_cap` — its cap operation.
* `Stacks.Chow.eq_chernClassBivariant` — it is the only bivariant class with that property.

## Implementation notes

### Transporting the flat axiom: the isomorphism case of Stacks 02RG

The flat axiom of a bivariant class compares the cap operation on `X ×_X T'` with the one on
`X ×_X T` along a flat `h' : X ×_X T' ⟶ X ×_X T`. Reading both through
`Stacks.Chow.IdentityCapRule.transport` turns the comparison into the statement that flat
pullback along `h'` commutes with pushforward along the two base-change isomorphisms, which is
Stacks 02RG for a square whose two proper legs are isomorphisms. That case is
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`, and
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso_square` supplies the instance
of Stacks 02S1 the transported pullback needs. Nothing about Chern classes enters, so the
transport is proved for an arbitrary identity cap rule.

### Transporting the Gysin axiom, and why one hypothesis on the Gysin system remains

The Gysin axiom is stated against a `Stacks.Chow.GysinSystem`, which supplies a first Chern class
component rule of Stacks 02SO for every scheme and every invertible module on it. The axiom
compares the Gysin map on the test scheme `T` with the Gysin map on `X ×_X T`, and those are two
*unrelated* members of that data: nothing in `Stacks.Chow.GysinSystem` relates them, and the
counterexample recorded in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward` shows that nothing can. So the
transport needs the isomorphism case of Stacks 02TA for the system, exactly as
`Stacks.Chow.bivariantRestriction` and `Stacks.Chow.bivariantTransport` do.

`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` is that case for a module pulled back to
*both* sides of the isomorphism, which is the shape a restriction produces. Here the module lives
on the test scheme itself and only its pullback to `X ×_X T` is a pullback, so the hypothesis
needed is the asymmetric form `Stacks.Chow.GysinSystem.IsNaturalUnderInverseIso`: for an
isomorphism `u : A ⟶ B` over the base with inverse `w` and an invertible module `L` on `A`, the
Gysin map of `(w^*L, w^*s)` on `B` is the Gysin map of `(L, s)` on `A` conjugated by `u`.

### The heavy step is hoisted

The final identity is an equality between two compositions of Gysin maps, cap operations and
pushforwards along isomorphisms, in which the zero schemes and the pulled-back modules occur only
as the schemes the Chow groups are taken on. It is therefore proved as a statement about four
abstract families of homomorphisms between Chow groups, in which none of those terms appears, and
instantiated at the use site.

## References

* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Pushforward along an isomorphism and a change of degree -/

/-- Pushforward along an isomorphism carries a heterogeneous equality of Chow classes in two
equal degrees to a heterogeneous equality of their images. -/
private theorem heq_chowPushforwardOfIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) {i j : ℤ} (hij : i = j)
    {a : chowGroup C sA i} {b : chowGroup C sA j} (hab : HEq a b) :
    HEq (chowPushforwardOfIso C sA sB u hu i a) (chowPushforwardOfIso C sA sB u hu j b) := by
  subst hij
  exact heq_of_eq (congrArg (fun x ↦ chowPushforwardOfIso C sA sB u hu i x) (eq_of_heq hab))

/-- The public form of `heq_chowPushforwardOfIso`. -/
alias heq_chowPushforwardOfIso_of_heq := heq_chowPushforwardOfIso

/-- Pushforward along an isomorphism commutes with transport of a Chow class along an equality of
degrees. -/
private theorem chowPushforwardOfIso_eq_mp (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) {i j : ℤ} (hij : i = j)
    (a : chowGroup C sA i) :
    chowPushforwardOfIso C sA sB u hu j (Eq.mp (congrArg (chowGroup C sA) hij) a) =
      Eq.mp (congrArg (chowGroup C sB) hij) (chowPushforwardOfIso C sA sB u hu i a) := by
  subst hij
  rfl

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-! ### Stacks 02U8 on the test schemes, and its transport -/

/-- **Stacks 0B76 (2) read on the test schemes.** The flat-pullback identity for an identity cap
rule: the rule commutes with flat pullback of relative dimension `r` along a morphism
`h : T' ⟶ T` of test schemes.

For the Chern classes this is Stacks 02U8. It is an `HEq` because the flat pullback of a
`k`-cycle has degree `k + r`, so the two sides sit in degrees `(k + r) - p` and `(k - p) + r`,
which are the same integer and not the same term. Both instances of Stacks 02S1 are quantified
over, as they are in the corresponding field of `Stacks.Chow.BivariantClass`. -/
def IdentityCapRule.FlatNaturality (op : IdentityCapRule C sX p) : Prop :=
  ∀ {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
      (by simp [Category.assoc]) r hr k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
      (by simp [Category.assoc]) r hr (k - p))
    (α : chowGroup C (g ≫ sX) k),
    HEq
      (op (h ≫ g) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r hr k hfac α))
      (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r hr (k - p)
        hfacp (op g k α))

/-- **Stacks 0B76 (2) read on the test schemes**, carried under the data of a base change of the
flat morphism. This is `Stacks.Chow.IdentityCapRule.FlatNaturality` with four further hypotheses
— a base change `h'` of `h` to the chosen pullbacks, the cartesian square it fills, its
compatibility with the projections, and its relative dimension — none of which occurs in the
conclusion.

Those hypotheses are inert and the predicate is therefore weaker than
`Stacks.Chow.IdentityCapRule.FlatNaturality`; it exists because the relative dimension of a base
change cannot be *produced* in this repository, Stacks 02NK being absent, so a consumer that has
only the flat axiom of a bivariant class — where `h'` and its relative dimension are quantified
over, for exactly that reason — can establish this form and not the unconditional one. It is
nonetheless enough to run the transport below, which is given `h'` and `hr'` by the axiom it is
proving. -/
def IdentityCapRule.FlatNaturalityAlongBaseChange (op : IdentityCapRule C sX p) : Prop :=
  ∀ {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
    (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g))
    (_hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g)) (k : ℤ),
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (_hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
        (by simp [Category.assoc]) r hr k)
      (hfacp : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
        (by simp [Category.assoc]) r hr (k - p))
      (α : chowGroup C (g ≫ sX) k),
      HEq
        (op (h ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r hr k hfac α))
        (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r hr (k - p)
          hfacp (op g k α))

/-- The unconditional flat-pullback identity on the test schemes gives the one carried under the
data of a base change: the extra hypotheses are not used. -/
theorem IdentityCapRule.FlatNaturality.alongBaseChange {op : IdentityCapRule C sX p}
    (hop : op.FlatNaturality C sX p) : op.FlatNaturalityAlongBaseChange C sX p := by
  intro T T' g _ h _ _ r hr _h' _sq _hfst k _hr' hfac hfacp α
  exact hop g h r hr k hfac hfacp α

/-- **Axiom (2) of Stacks 0B76 for a transported rule.** If an identity cap rule commutes with
flat pullback on the test schemes — Stacks 02U8 for the Chern classes — then its transport to the
chosen pullbacks satisfies the flat-pullback axiom of a bivariant class.

The content is the transport. The cartesian square gives `h ≫ e⁻¹ = e'⁻¹ ≫ h'` for the two
base-change isomorphisms `e : X ×_X T ≅ T` and `e' : X ×_X T' ≅ T'`, and the isomorphism case of
Stacks 02RG, `Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`, moves the flat pullback past
them; the instance of Stacks 02S1 for `h` in the shifted degree is derived from the one for `h'`
by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso_square`. -/
theorem IdentityCapRule.transportFlatNaturalityAlongBaseChange (op : IdentityCapRule C sX p)
    (hop : op.FlatNaturalityAlongBaseChange C sX p) : op.TransportFlatNaturality C sX p := by
  intro T T' g _ h _ _ r hr h' sq hfst k
  let _ : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  let _ : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  intro hr' hfac hfac' α
  have hinv := identityBaseChangeIso_hom_comp C sX g
  have hu := identityBaseChangeIso_hom_comp C sX (h ≫ g)
  have hm : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hh : h ≫ g ≫ sX = (h ≫ g) ≫ sX := (Category.assoc h g sX).symm
  have hmove : h ≫ (identityBaseChangeIso g).inv =
      (identityBaseChangeIso (h ≫ g)).inv ≫ h' := by
    have hsq : (identityBaseChangeIso (h ≫ g)).hom ≫ h = h' ≫ (identityBaseChangeIso g).hom :=
      sq.w
    rw [Iso.comp_inv_eq, Category.assoc, ← hsq, Iso.inv_hom_id_assoc]
  have hfacp : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h hh r
      hr (k - p) :=
    flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C (g ≫ sX) ((h ≫ g) ≫ sX)
      (pullback.fst (𝟙 X) g ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX)
      (identityBaseChangeIso g).inv hinv (identityBaseChangeIso (h ≫ g)).inv hu h hh h' hm
      hmove r hr hr' (k - p) hfac'
  have h02RG := flatPullbackChow_chowPushforwardOfIso C (g ≫ sX) ((h ≫ g) ≫ sX)
    (pullback.fst (𝟙 X) g ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX)
    (identityBaseChangeIso g).inv hinv (identityBaseChangeIso (h ≫ g)).inv hu h hh h' hm
    hmove r hr hr' (k - p) hfacp hfac' (op g k α)
  exact HEq.trans
    (heq_chowPushforwardOfIso C ((h ≫ g) ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX)
      (identityBaseChangeIso (h ≫ g)).inv hu
      (show k + (r : ℤ) - p = k - p + (r : ℤ) by omega)
      (hop g h r hr h' sq hfst k hr' hfac hfacp α))
    (heq_of_eq h02RG.symm)

/-- **Axiom (2) of Stacks 0B76 for a transported rule**, from the unconditional flat-pullback
identity on the test schemes. -/
theorem IdentityCapRule.transportFlatNaturality (op : IdentityCapRule C sX p)
    (hop : op.FlatNaturality C sX p) : op.TransportFlatNaturality C sX p :=
  IdentityCapRule.transportFlatNaturalityAlongBaseChange C sX p op
    (IdentityCapRule.FlatNaturality.alongBaseChange C sX p hop)

/-! ### The isomorphism case of Stacks 02TA for a Gysin system -/

/-- **The isomorphism case of Stacks 02TA for a Gysin system**, with the invertible module given
on the source of the isomorphism: for an isomorphism `u : A ⟶ B` over the base with inverse `w`,
an invertible module `L` on `A` and a global section `s` of it, the Gysin map of `(w^*L, w^*s)`
on `B` is the Gysin map of `(L, s)` on `A` conjugated by `u` and by a morphism `j` of the two
zero schemes lying over `u`.

The morphism `j` is quantified over, and it is constrained by `_hsq` to lie over `u` and not
merely over the base scheme: without that square the assertion is false, since `j` would then be
an arbitrary morphism of the two zero schemes over `C.S` (for `u = 𝟙` and `Z(s)` two points over
a field, the swap of the two points), and it is also what makes the predicate provable — by the
monicity of a closed immersion `j` is then inverse to the morphism of Remark 0B6Y for `w`.
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` carries the same square for the same two
reasons.

This is the shape in which Stacks 02TA is needed to transport the Gysin axiom of a bivariant
class across the base change of an identity morphism; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass`. The symmetric form, where
the module is pulled back to both sides, is
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`. -/
def GysinSystem.IsNaturalUnderInverseIso {C : ChowSituation.{u}} (G : GysinSystem C) : Prop :=
  ∀ {A B : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (u : A ⟶ B) [IsIso u] (w : B ⟶ A) (_huw : u ≫ w = 𝟙 A)
    (hu : u ≫ pB = pA) (L : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
      ((Scheme.Modules.pullback w).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ)
    (j : (Stacks.Divisors.zeroScheme A L s).subscheme ⟶
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
        (AlgebraicGeometry.pullbackGlobalSections w L s)).subscheme)
    [IsProper j]
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
          (AlgebraicGeometry.pullbackGlobalSections w L s)).subschemeι ≫ pB) =
        (Stacks.Divisors.zeroScheme A L s).subschemeι ≫ pA)
    (_hsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
          (AlgebraicGeometry.pullbackGlobalSections w L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A L s).subschemeι ≫ u)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ pA)
      ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
        (AlgebraicGeometry.pullbackGlobalSections w L s)).subschemeι ≫ pB) j hj k)
    (α : chowGroup C pA (k + 1)),
    G.onChow pB ((Scheme.Modules.pullback w).obj L)
        (AlgebraicGeometry.pullbackGlobalSections w L s) k
        (chowPushforwardOfIso C pA pB u hu (k + 1) α) =
      properChowPushforward C ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback w).obj L)
          (AlgebraicGeometry.pullbackGlobalSections w L s)).subschemeι ≫ pB) j hj k hfac
        (G.onChow pA L s k α)

/-! ### Stacks 0B7G on the test schemes, and its transport -/

/-- **Stacks 0B76 (3) read on the test schemes.** The Gysin identity for an identity cap rule:
the rule commutes with the Gysin map of the zero scheme of a section of an invertible module on a
test scheme.

For the Chern classes this is Stacks 0B7G, `c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`, read against the
Gysin map that the Gysin system `G` provides. The transport of degrees is the one the axiom of a
bivariant class carries: `(k + 1) - p` and `(k - p) + 1` are the same integer and not the same
term. -/
def IdentityCapRule.GysinNaturality (op : IdentityCapRule C sX p) (G : GysinSystem C) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (N : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (k : ℤ) (α : chowGroup C (g ≫ sX) (k + 1)),
    op ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) k (G.onChow (g ≫ sX) N s k α) =
      G.onChow (g ≫ sX) N s (k - p)
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) (by omega : k + 1 - p = k - p + 1))
          (op g (k + 1) α))

/-- The algebraic skeleton of the Gysin transport: two Gysin-like families of homomorphisms
intertwined by pushforward along an isomorphism, a cap operation commuting with the first family,
and the conclusion that the pushforward of the capped class is the cap of the pushforward.

Stated for abstract families, so that neither the zero schemes nor the pulled-back modules of the
Gysin axiom appear; it is instantiated at those in
`Stacks.Chow.IdentityCapRule.transportGysinNaturality`. -/
private theorem gysin_transport_aux (C : ChowSituation.{u}) {A B A' B' : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB']
    (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) (v : A' ⟶ B') [IsIso v] (hv : v ≫ sB' = sA')
    (p k : ℤ) (GA : ∀ m : ℤ, chowGroup C sA (m + 1) →+ chowGroup C sA' m)
    (GB : ∀ m : ℤ, chowGroup C sB (m + 1) →+ chowGroup C sB' m)
    (opA : ∀ m : ℤ, chowGroup C sA' m →+ chowGroup C sA' (m - p))
    (opT : ∀ m : ℤ, chowGroup C sA m →+ chowGroup C sA (m - p))
    (hop : ∀ α : chowGroup C sA (k + 1), opA k (GA k α) =
      GA (k - p) (Eq.mp (congrArg (chowGroup C sA) (show k + 1 - p = k - p + 1 by omega))
        (opT (k + 1) α)))
    (hgys : ∀ γ : chowGroup C sA (k - p + 1),
      GB (k - p) (chowPushforwardOfIso C sA sB u hu (k - p + 1) γ) =
        chowPushforwardOfIso C sA' sB' v hv (k - p) (GA (k - p) γ))
    (α : chowGroup C sA (k + 1)) :
    chowPushforwardOfIso C sA' sB' v hv (k - p) (opA k (GA k α)) =
      GB (k - p) (Eq.mp (congrArg (chowGroup C sB) (show k + 1 - p = k - p + 1 by omega))
        (chowPushforwardOfIso C sA sB u hu (k + 1 - p) (opT (k + 1) α))) := by
  rw [hop α, ← chowPushforwardOfIso_eq_mp C sA sB u hu
    (show k + 1 - p = k - p + 1 by omega) (opT (k + 1) α), hgys]

/-- **Axiom (3) of Stacks 0B76 for a transported rule.** If an identity cap rule commutes with
the Gysin maps of a Gysin system on the test schemes — Stacks 0B7G for the Chern classes — and
that system satisfies the isomorphism case of Stacks 02TA, then the transport of the rule to the
chosen pullbacks satisfies the Gysin axiom of a bivariant class.

The two Gysin maps the axiom compares live on the test scheme and on its identity base change, so
the transport is exactly the isomorphism case of Stacks 02TA; the remaining step is to compose
the two pushforwards along isomorphisms into one, by functoriality of proper pushforward. -/
theorem IdentityCapRule.transportGysinNaturality (op : IdentityCapRule C sX p)
    (G : GysinSystem C) (hop : op.GysinNaturality C sX p G)
    (hiso : G.IsNaturalUnderInverseIso) : op.TransportGysinNaturality C sX p G := by
  intro T g _ N _ _ s k
  dsimp only
  intro e he hbase hfac α
  have hug := identityBaseChangeIso_hom_comp C sX g
  have hDinv :=
    identityBaseChangeIso_hom_comp C sX ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)
  have hv : ((identityBaseChangeIso
        ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)).inv ≫ e.hom) ≫
      ((Stacks.Divisors.zeroScheme (pullback (𝟙 X) g)
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s)).subschemeι ≫
          pullback.fst (𝟙 X) g ≫ sX) =
      (Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g ≫ sX := by
    rw [Category.assoc, hbase, hDinv, Category.assoc]
  have hcomp := DFunLike.congr_fun
    (properChowPushforward_comp C
      ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g ≫ sX)
      (pullback.fst (𝟙 X) ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback (𝟙 X) g)
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s)).subschemeι ≫
          pullback.fst (𝟙 X) g ≫ sX)
      (identityBaseChangeIso ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)).inv e.hom
      hDinv hbase (k - p)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
        ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g ≫ sX)
        (pullback.fst (𝟙 X) ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) ≫ sX)
        (identityBaseChangeIso ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)).inv hDinv
        (k - p))
      hfac)
    (op ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) k (G.onChow (g ≫ sX) N s k α))
  refine hcomp.trans ?_
  refine gysin_transport_aux C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX)
    ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g ≫ sX)
    ((Stacks.Divisors.zeroScheme (pullback (𝟙 X) g)
      ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s)).subschemeι ≫
        pullback.fst (𝟙 X) g ≫ sX)
    (identityBaseChangeIso g).inv hug
    ((identityBaseChangeIso ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)).inv ≫ e.hom) hv
    p k (fun m ↦ G.onChow (g ≫ sX) N s m)
    (fun m ↦ G.onChow (pullback.fst (𝟙 X) g ≫ sX)
      ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s) m)
    (fun m ↦ op ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) m) (fun m ↦ op g m)
    (hop g N s k) (fun γ ↦ ?_) α
  exact hiso (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) (identityBaseChangeIso g).inv
    (pullback.snd (𝟙 X) g) (identityBaseChangeIso g).inv_hom_id hug N s (k - p)
    ((identityBaseChangeIso ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)).inv ≫ e.hom) hv
    (by
      rw [Category.assoc, he]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, bivariantBaseChangeMap, pullback.lift_fst, Category.comp_id,
          fst_eq_identityBaseChangeIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
          Category.assoc, fst_eq_identityBaseChangeIso_hom g]
        simp
      · rw [Category.assoc, bivariantBaseChangeMap, pullback.lift_snd]
        simp)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
      ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback (𝟙 X) g)
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s)).subschemeι ≫
          pullback.fst (𝟙 X) g ≫ sX)
      ((identityBaseChangeIso ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)).inv ≫ e.hom)
      hv (k - p)) γ

/-! ### The bivariant Chern classes of Stacks 0B7H -/

variable (F : X.Modules) (r : ℕ)

/-- **Stacks 02U9, the rank of a pullback.** The pullback of a finite locally free module of rank
`r` along any morphism to `X` is again finite locally free of rank `r`, so the rank hypothesis
the Chern class operations carry is automatic for such a module. -/
theorem pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    PullbackPreservesRank F r :=
  fun g ↦ AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r

variable (G : GysinSystem C) (cap : HigherChernCapRule C r)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-- The identity cap rule of degree `j` of a module that is finite locally free of rank `r`:
`α ↦ c_j(g^*ℰ) ∩ α` on the Chow groups of each test scheme `g : T ⟶ X`. -/
def chernIdentityCapRuleOfRank (j : Fin (r + 1)) : IdentityCapRule C sX (j : ℤ) :=
  chernIdentityCapRule C sX F r cap
    (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j

variable (j : Fin (r + 1))
  (hproper : IdentityCapRule.ProperNaturality C sX (j : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap j))
  (hflat : IdentityCapRule.FlatNaturality C sX (j : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap j))
  (hgysin : IdentityCapRule.GysinNaturality C sX (j : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap j) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-- **Stacks 0B7H.** The `j`-th Chern class of a finite locally free module of rank `r` as a
bivariant class of degree `j` for the identity of `X`: the rule that assigns to `f : X' ⟶ X` the
operation `c_j(f^*ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')` is an element of `A^j(X ⟶ X)`.

Its cap operation is the one forced by the characterization of Stacks 0B7H, and the three
naturality axioms of Stacks 0B76 for it are the projection formula of Stacks 02U9, the
flat-pullback identity of Stacks 02U8 and the Gysin identity of Stacks 0B7G, each read on the
test schemes and transported here to the chosen pullbacks. -/
def chernClassBivariant : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ) :=
  IdentityCapRule.toBivariantClass C sX (j : ℤ) (chernIdentityCapRuleOfRank C sX F r cap j) G
    hproper
    (IdentityCapRule.transportFlatNaturality C sX (j : ℤ)
      (chernIdentityCapRuleOfRank C sX F r cap j) hflat)
    (IdentityCapRule.transportGysinNaturality C sX (j : ℤ)
      (chernIdentityCapRuleOfRank C sX F r cap j) G hgysin hiso)

/-- The cap operation of the bivariant `j`-th Chern class is the transport of
`α ↦ c_j(g^*ℰ) ∩ α` to the chosen pullback `X ×_X T`. -/
theorem chernClassBivariant_cap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso).cap g k =
      chernClassBivariantCap C sX F r cap
        (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j g k :=
  rfl

/-- **Stacks 0B7H.** The class constructed above is the bivariant `j`-th Chern class of `ℰ`: on
every test scheme `g : T ⟶ X` and in every degree, pushing `c_j(ℰ) ∩ α` forward along the
projection `X ×_X T ⟶ T` gives `c_j(g^*ℰ) ∩ α`. -/
theorem isChernClassBivariant_chernClassBivariant :
    IsChernClassBivariant C sX F r G cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j
      (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso) :=
  (isChernClassBivariant_iff C sX F r G cap
    (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j _).2
    fun {_T} g _ k ↦ chernClassBivariant_cap C sX F r G cap j hproper hflat hgysin hiso g k

/-- **Stacks 0B7H, uniqueness.** The bivariant `j`-th Chern class is the only bivariant class of
degree `j` for the identity of `X` that caps by `c_j(g^*ℰ) ∩ -` on every test scheme. -/
theorem eq_chernClassBivariant
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ))
    (hc : IsChernClassBivariant C sX F r G cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j c) :
    c = chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso :=
  eq_of_isChernClassBivariant C sX F r G cap
    (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j hc
    (isChernClassBivariant_chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso)

end Stacks.Chow

end
