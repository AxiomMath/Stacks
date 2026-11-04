module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Chern classes as bivariant classes: the cap rule of an identity morphism

Stacks 0B77 and Stacks 0B7H both produce a bivariant class for an **identity** morphism: the
first Chern class of an invertible module, respectively the `j`-th Chern class of a finite
locally free module of rank `r`, viewed as an element of `A^p(X ⟶ X)`. A bivariant class for
`f : X ⟶ Y` caps into the Chow group of the *chosen categorical pullback* `X ×_Y T`, so for
`f = 𝟙 X` its cap operation lands in `A_{k-p}(X ×_X T)` while a Chern class operation is given
on `A_{k-p}(T)`. The two are identified by `pullback.snd (𝟙 X) g`, which is an isomorphism.

This file isolates that identification. An *identity cap rule* of degree `p` is a rule assigning
to every `g : T ⟶ X` locally of finite type and every `k` an additive map
`A_k(T) ⟶ A_{k-p}(T)`; `Stacks.Chow.IdentityCapRule.transport` carries it to the chosen
pullbacks, which is the only shape in which it can be a cap operation of
`Stacks.Chow.BivariantClass`. The transport is a bijection onto the operations into the pullback,
so the Stacks characterization of `c₁` or of `c_j` as a bivariant class **determines the class
uniquely**, and the proper-pushforward axiom of Stacks 0B76 for the transported rule follows from
the projection formula for the rule itself.

## Main definitions

* `Stacks.Chow.IdentityCapRule` — a rule `A_k(T) ⟶ A_{k-p}(T)` for every test scheme
  `g : T ⟶ X` over `X` and every `k`.
* `Stacks.Chow.IdentityCapRule.transport` — the same rule read as an operation into the Chow
  group of the chosen pullback `X ×_X T`, which is what Stacks 0B76 needs.
* `Stacks.Chow.IdentityCapRule.ProperNaturality` — Stacks 0B76 (1) read on the test schemes.
* `Stacks.Chow.HigherChernCapRule` — **Stacks 02U5 and 02U7 as a single datum**: the cap product
  with the Chern classes of a finite locally free module of rank `r`, descended to Chow groups,
  for every scheme locally of finite type over the base; the rule of Stacks 02U6 is
  `Stacks.Chow.GenuineChern.chernCap`.
* `Stacks.Chow.chernClassBivariantCap` — the cap operation of the bivariant Chern class of
  Stacks 0B7H, forced by the characterization below.
* `Stacks.Chow.IsChernClassBivariant` — **the characterization of Stacks 0B7H**: that a bivariant
  class of degree `j` for `𝟙 X` caps by intersection with the `j`-th Chern class of the
  pulled-back module on every test scheme.

## Main results

* `Stacks.Chow.chowPushforwardOfIso_identityBaseChange_bijective` — pushing forward along
  `X ×_X T ⟶ T` is a bijection of Chow groups.
* `Stacks.Chow.IdentityCapRule.pushforward_transport` — the transport is undone by that
  pushforward, so `Stacks.Chow.IdentityCapRule.transport` is a section of it.
* `Stacks.Chow.BivariantClass.eq_of_pushforward_cap_eq` — **uniqueness for an identity
  morphism**: a bivariant class for `𝟙 X` is determined by the operations it induces on the test
  schemes. This is what makes the characterizations of Stacks 0B77 and 0B7H pin a class down.
* `Stacks.Chow.IdentityCapRule.transport_proper_naturality` — **Stacks 0B76 (1) for the
  transported rule**, from the projection formula for the rule itself. The transport is the
  content: the two sides differ by pushing forward along the two base-change isomorphisms, and
  the cartesian square makes `h ≫ e⁻¹ = e'⁻¹ ≫ h'`.
* `Stacks.Chow.isChernClassBivariant_iff` — the characterization of Stacks 0B7H holds exactly
  when the cap operation **is** `Stacks.Chow.chernClassBivariantCap`; so Stacks 0B7H has at most
  one solution and its cap operation is forced.
* `Stacks.Chow.eq_of_isChernClassBivariant` — uniqueness in Stacks 0B7H.

## Implementation notes

### The Chern cap rule is a parameter, the rank preservation is quantified

`Stacks.Chow.HigherChernCapRule` is **data**, so it is a parameter and not quantified over, for
the reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`:

> For a `Prop` hypothesis, `(∀ h, P h) ↔ P h₀` by proof irrelevance, so quantifying is free.
> For **data**, `∀ G, P G` is strictly **stronger** than `P G₀`. Hence: data ⇒ parameter,
> `Prop` ⇒ quantify.

Quantifying it would ask the bivariant class to be compatible with every candidate Chern cap
rule, including non-geometric ones, which is as unfaithful to Stacks 0B7H as weakening it. The
rule is **global** — a rule for every scheme locally of finite type over the base, not only for
`X` — because the cap operation of a bivariant class is an operation on *every* test scheme, and
Stacks 0FDZ compares bivariant classes over different schemes at the same rule.

It carries no `Prop` fields and is therefore a plain `Pi` type rather than a structure: there is
nothing to bundle with it. The rank preservation of Stacks 02U9, which is needed even to *state*
the characterization — the module on the test scheme is `g^*F`, and that it still has rank `r` is
not an instance in this repository — is a `Prop`, so it is quantified at the declarations that
need it, under the name `hrank`.

`Stacks.Chow.PullbackPreservesRank` is the *only* hypothesis the module `F` carries below: no
declaration takes `[AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]` as well.
That is a generalization and not a weakening — the instance would be unused, and the rank
preservation already asserts what every declaration needs, namely that the module on each test
scheme has rank `r`.

### What is still missing for the existence half of Stacks 0B7H

The characterization below forces the cap operation, so constructing the bivariant class of
Stacks 0B7H is exactly filling the three naturality fields of `Stacks.Chow.BivariantClass` for
`Stacks.Chow.chernClassBivariantCap`. The source proof of Stacks 0B7H invokes Stacks 02U7, 02U9,
02U8 and 0B7G, which are the three naturalities of the cap product itself; the extra work is the
transport across the base-change isomorphism. This file does the first of the three; the other
two are
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass`, which assembles the class:

* **Proper** (Stacks 02U9, the projection formula). Done here:
  `Stacks.Chow.IdentityCapRule.transport_proper_naturality`. The transport needs only
  functoriality of proper pushforward, Stacks 02R5, which is proved in this repository, and
  Stacks 02S2 for the base-change isomorphisms, which
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport` supplies outright.
* **Flat** (Stacks 02U8). Done by
  `Stacks.Chow.IdentityCapRule.transportFlatNaturality`. The transport needs flat pullback to
  commute with proper pushforward in a cartesian square whose two proper legs are isomorphisms,
  which is the case of Stacks 02RG carried by
  `Stacks.Chow.flatPullbackChow_chowPushforwardOfIso` of
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange`.
* **Gysin** (Stacks 0B7G). Done by
  `Stacks.Chow.IdentityCapRule.transportGysinNaturality`. The transport needs the Gysin map to
  commute with proper pushforward along an isomorphism, which is the isomorphism case of Stacks
  02TA; the two Gysin maps it compares are unrelated members of the data of a
  `Stacks.Chow.GysinSystem`, so that case is carried as a hypothesis on the system, in the shape
  `Stacks.Chow.GysinSystem.IsNaturalUnderInverseIso`.

None of the three transports is about Chern classes; they are properties of the identity base
change alone. That is why this file, and the one that completes them, state them in terms of an
arbitrary `Stacks.Chow.IdentityCapRule`, so that Stacks 0B77 can use them too.

### Where Stacks 0B7H and 0B77 are registered

The declarations below are stated for an arbitrary `Stacks.Chow.HigherChernCapRule`. The tags are
registered on the classes built from the cap products of Stacks 02U6:
`Stacks.Chow.GenuineChern.chernClassBivariantClass` and
`Stacks.Chow.GenuineChern.firstChernClassBivariantClass`.

## References

* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-! ### Cap rules for an identity morphism -/

/-- An *identity cap rule* of degree `p` on `X`: a rule assigning to every morphism
`g : T ⟶ X` locally of finite type and every `k` an additive map `A_k(T) ⟶ A_{k-p}(T)`.

This is the shape in which the Stacks Project writes the cap operation of a bivariant class for
the identity of `X` — on the test scheme itself rather than on the chosen pullback `X ×_X T`. -/
abbrev IdentityCapRule : Type (u + 1) :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (g ≫ sX) k →+ chowGroup C (g ≫ sX) (k - p)

/-- Pushing forward along the projection `X ×_X T ⟶ T` of the identity base change is a bijection
of Chow groups: that projection is an isomorphism, and Stacks 02S2 holds for an isomorphism
outright. -/
theorem chowPushforwardOfIso_identityBaseChange_bijective {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    Function.Bijective (chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
      (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g) k) :=
  (chowGroupEquivOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
    (identityBaseChangeIso_hom_comp_base C sX g) k).bijective

/-- The cap operation into the Chow group of the chosen pullback that an identity cap rule
provides: push the value of the rule forward along the base-change isomorphism `T ≅ X ×_X T`.

This needs no instance of Stacks 02S2, because the morphism pushed along is an isomorphism; see
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport`. -/
def IdentityCapRule.transport (op : IdentityCapRule C sX p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sX) k →+ chowGroup C (pullback.fst (𝟙 X) g ≫ sX) (k - p) :=
  (chowPushforwardOfIso C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) (identityBaseChangeIso g).inv
    (identityBaseChangeIso_hom_comp C sX g) (k - p)).comp (op g k)

/-- Functoriality of proper pushforward on Chow groups, stated on elements for a composite given
as any morphism `m` equal to `f ≫ g`. -/
private theorem properChowPushforward_comp_apply_of_eq {A B D : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S)
    [LocallyOfFiniteType sD] (f : A ⟶ B) [IsProper f] (g : B ⟶ D) [IsProper g] (m : A ⟶ D)
    [IsProper m] (hm : f ≫ g = m) (hf : f ≫ sB = sA) (hg : g ≫ sD = sB) (hm' : m ≫ sD = sA)
    (k : ℤ) (hfacf : ProperPushforwardFactorsThroughRationalEquivalence C sA sB f hf k)
    (hfacg : ProperPushforwardFactorsThroughRationalEquivalence C sB sD g hg k)
    (hfacm : ProperPushforwardFactorsThroughRationalEquivalence C sA sD m hm' k)
    (α : chowGroup C sA k) :
    properChowPushforward C sB sD g hg k hfacg (properChowPushforward C sA sB f hf k hfacf α) =
      properChowPushforward C sA sD m hm' k hfacm α := by
  subst hm
  exact DFunLike.congr_fun (properChowPushforward_comp C sA sB sD f g hf hg k hfacf hfacg) α

/-- Pushing the transported rule forward along `X ×_X T ⟶ T` returns the rule. So the
characterizations of Stacks 0B77 and Stacks 0B7H, which are stated in exactly this shape, say
precisely that the cap operation is the transport of the Chern class operation. -/
theorem IdentityCapRule.pushforward_transport (op : IdentityCapRule C sX p) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C sX g) (k - p)
        (op.transport C sX p g k α) =
      op g k α := by
  have hinv : (identityBaseChangeIso g).inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX :=
    identityBaseChangeIso_hom_comp C sX g
  have hhom : (identityBaseChangeIso g).hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX g
  rw [IdentityCapRule.transport, AddMonoidHom.coe_comp, Function.comp_apply, chowPushforwardOfIso,
    chowPushforwardOfIso,
    properChowPushforward_comp_apply_of_eq C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
      (identityBaseChangeIso g).inv (identityBaseChangeIso g).hom (𝟙 T) (Iso.inv_hom_id _) hinv
      hhom (Category.id_comp (g ≫ sX)) (k - p) _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C (g ≫ sX) (g ≫ sX) (𝟙 T)
        (Category.id_comp (g ≫ sX)) (k - p)),
    properChowPushforward_id]
  rfl

/-- An operation into the Chow group of the chosen pullback is the transport of an identity cap
rule exactly when pushing it forward along `X ×_X T ⟶ T` gives that rule. -/
theorem IdentityCapRule.eq_transport_iff (op : IdentityCapRule C sX p) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (F : chowGroup C (g ≫ sX) k →+ chowGroup C (pullback.fst (𝟙 X) g ≫ sX) (k - p)) :
    (∀ α, chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
        (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g) (k - p)
        (F α) = op g k α) ↔
      F = op.transport C sX p g k := by
  refine ⟨fun h ↦ AddMonoidHom.ext fun α ↦ ?_, fun h α ↦ ?_⟩
  · exact (chowPushforwardOfIso_identityBaseChange_bijective C sX g (k - p)).1
      ((h α).trans (op.pushforward_transport C sX p g k α).symm)
  · rw [h]
    exact op.pushforward_transport C sX p g k α

/-- The canonical base-change map between two identity base changes is the conjugate of the
morphism of test schemes by the two base-change isomorphisms: `e'⁻¹ ≫ bc = h ≫ e⁻¹`.

This is the square the Gysin axiom of a bivariant class for `𝟙 X` produces, read through the
isomorphisms `X ×_X T ≅ T`; it is what says the morphism of zero schemes the axiom supplies lies
over the base-change isomorphism and not merely over the base scheme. -/
theorem identityBaseChangeIso_inv_bivariantBaseChangeMap {T T' : Scheme.{u}} (g : T ⟶ X)
    (h : T' ⟶ T) :
    (identityBaseChangeIso (h ≫ g)).inv ≫ bivariantBaseChangeMap (𝟙 X) g h =
      h ≫ (identityBaseChangeIso g).inv := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bivariantBaseChangeMap, pullback.lift_fst, Category.comp_id,
      fst_eq_identityBaseChangeIso_hom (h ≫ g), ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp, Category.assoc, fst_eq_identityBaseChangeIso_hom g]
    simp
  · rw [Category.assoc, bivariantBaseChangeMap, pullback.lift_snd]
    simp

/-! ### Uniqueness of a bivariant class for an identity morphism -/

/-- **Uniqueness for Stacks 0B77 and Stacks 0B7H.** Two bivariant classes of degree `p` for
`𝟙 X` are equal as soon as the operations they induce on every test scheme agree, where "induce"
means pushing the cap operation forward along the base-change isomorphism `X ×_X T ⟶ T`.

This is what makes the Stacks characterizations of the bivariant Chern classes pin a class down:
that projection is an isomorphism of Chow groups, so the cap operation can be read off it. -/
theorem BivariantClass.eq_of_pushforward_cap_eq (G : GysinSystem C)
    (c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p)
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k),
      chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
          (identityBaseChangeIso_hom_comp_base C sX g) (k - p) (c.cap g k α) =
        chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
          (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g) (k - p)
          (d.cap g k α)) :
    c = d :=
  BivariantClass.ext C G sX sX (𝟙 X) (Category.id_comp sX) p
    fun {T} g _ k α ↦
      (chowPushforwardOfIso_identityBaseChange_bijective C sX g (k - p)).1 (h (T := T) g k α)

/-! ### The proper-pushforward axiom of Stacks 0B76 for a transported rule -/

/-- **Stacks 0B76 (1) read on the test schemes.** The projection formula for an identity cap
rule: the rule commutes with proper pushforward along a morphism `h : T' ⟶ T` of test schemes.

For the Chern classes this is Stacks 02U9. Both instances of Stacks 02S2 are quantified over, as
they are in the corresponding field of `Stacks.Chow.BivariantClass`; by proof irrelevance that is
equivalent to the unconditional statement. -/
def IdentityCapRule.ProperNaturality (op : IdentityCapRule C sX p) : Prop :=
  ∀ {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
      (by simp [Category.assoc]) k)
    (hfacp : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
      (by simp [Category.assoc]) (k - p))
    (α : chowGroup C ((h ≫ g) ≫ sX) k),
    op g k (properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) k hfac
        α) =
      properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) (k - p) hfacp
        (op (h ≫ g) k α)

/-- **Stacks 0B76 (1) for the transport of an identity cap rule.** If the rule satisfies the
projection formula on the test schemes, its transport to the chosen pullbacks satisfies the
proper-pushforward axiom of a bivariant class. This is the statement of the `proper_naturality`
field of `Stacks.Chow.BivariantClass` at `f = 𝟙 X` and `cap = op.transport`.

The content is the transport. The cartesian square of the axiom gives
`e' ≫ h = h' ≫ e` for the two base-change isomorphisms `e : X ×_X T ≅ T` and
`e' : X ×_X T' ≅ T'`, hence `h ≫ e⁻¹ = e'⁻¹ ≫ h'`; functoriality of proper pushforward
(Stacks 02R5) then turns both sides into the pushforward along that one morphism. The instance of
Stacks 02S2 for `h` that the projection formula needs is *derived*, not assumed: it is the one for
`h'` composed with the two isomorphisms, for which Stacks 02S2 is unconditional. -/
theorem IdentityCapRule.transport_proper_naturality (op : IdentityCapRule C sX p)
    (hop : op.ProperNaturality C sX p) {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [IsProper h] (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
    (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g))
    (hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C ((h ≫ g) ≫ sX) k),
      op.transport C sX p g k (properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h
          (by simp [Category.assoc]) k hfac α) =
        properChowPushforward C (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - p) hfac' (op.transport C sX p (h ≫ g) k α) := by
  let _ : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  intro hfac hfac' α
  -- names for the four structure morphisms and the two base-change isomorphisms
  set e : pullback (𝟙 X) g ≅ T := identityBaseChangeIso g
  set e' : pullback (𝟙 X) (h ≫ g) ≅ T' := identityBaseChangeIso (h ≫ g)
  have hu : e'.inv ≫ pullback.fst (𝟙 X) (h ≫ g) ≫ sX = (h ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp C sX (h ≫ g)
  have hv : e.hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX g
  have hinv : e.inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX :=
    identityBaseChangeIso_hom_comp C sX g
  have hm : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hh : h ≫ g ≫ sX = (h ≫ g) ≫ sX := by simp [Category.assoc]
  -- the cartesian square, read through the two isomorphisms
  have hsq : e'.hom ≫ h = h' ≫ e.hom := sq.w
  have hconj : e'.inv ≫ h' ≫ e.hom = h := by
    rw [← hsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hmove : h ≫ e.inv = e'.inv ≫ h' :=
    calc h ≫ e.inv = (e'.inv ≫ h' ≫ e.hom) ≫ e.inv := by rw [hconj]
      _ = e'.inv ≫ h' ≫ e.hom ≫ e.inv := by simp only [Category.assoc]
      _ = e'.inv ≫ h' := by rw [Iso.hom_inv_id, Category.comp_id]
  -- Stacks 02S2 for `h` in degree `k - p`, derived from the one for `h'`
  have hfacp : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
      hh (k - p) :=
    properPushforwardFactorsThroughRationalEquivalence_congr C ((h ≫ g) ≫ sX) (g ≫ sX)
      (e'.inv ≫ h' ≫ e.hom) h hconj _ hh (k - p)
      (properPushforwardFactorsThroughRationalEquivalence_isIso_comp_isIso C ((h ≫ g) ≫ sX)
        (g ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) e'.inv h' e.hom
        hu hm hv (k - p) hfac')
  -- rewrite the left-hand side by the projection formula and then by functoriality
  rw [IdentityCapRule.transport, AddMonoidHom.coe_comp, Function.comp_apply,
    hop g h k hfac hfacp α]
  have hhe : (h ≫ e.inv) ≫ pullback.fst (𝟙 X) g ≫ sX = (h ≫ g) ≫ sX := by
    rw [Category.assoc, hinv, hh]
  have hfacm := properPushforwardFactorsThroughRationalEquivalence_comp C ((h ≫ g) ≫ sX) (g ≫ sX)
    (pullback.fst (𝟙 X) g ≫ sX) h e.inv hh hinv (k - p) hfacp
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C (g ≫ sX)
      (pullback.fst (𝟙 X) g ≫ sX) e.inv hinv (k - p))
  rw [chowPushforwardOfIso, properChowPushforward_comp_apply_of_eq C ((h ≫ g) ≫ sX) (g ≫ sX)
    (pullback.fst (𝟙 X) g ≫ sX) h e.inv (h ≫ e.inv) rfl hh hinv hhe (k - p) hfacp
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C (g ≫ sX)
      (pullback.fst (𝟙 X) g ≫ sX) e.inv hinv (k - p)) hfacm (op (h ≫ g) k α),
    IdentityCapRule.transport, AddMonoidHom.coe_comp, Function.comp_apply, chowPushforwardOfIso,
    properChowPushforward_comp_apply_of_eq C ((h ≫ g) ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX)
      (pullback.fst (𝟙 X) g ≫ sX) e'.inv h' (h ≫ e.inv) hmove.symm hu hm hhe (k - p)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C ((h ≫ g) ≫ sX)
        (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) e'.inv hu (k - p)) hfac' hfacm (op (h ≫ g) k α)]

/-! ### The bivariant Chern classes of Stacks 0B7H -/

/-- **Stacks 02U5 and 02U7 as a single datum.** The cap product with the Chern classes of a
finite locally free module of rank `r`, descended to Chow groups: for every scheme locally of
finite type over the base, every such module on it, every `k` and every `0 ≤ j ≤ r`, an additive
map `A_k(T) ⟶ A_{k-j}(T)`.

The declarations of this directory are stated for an arbitrary such rule. The rule given by the
projective space bundle formula, the cap products of Stacks 02U6, is
`Stacks.Chow.GenuineChern.chernCap`. -/
abbrev HigherChernCapRule (r : ℕ) : Type (u + 1) :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (k : ℤ)
    (j : Fin (r + 1)),
    chowGroup C q k →+ chowGroup C q (k - (j : ℤ))

variable (F : X.Modules) (r : ℕ)

/-- **Stacks 02U9, rank preservation.** That the pullback of a finite locally free module of rank
`r` along any morphism to `X` again has rank `r`. This is not an instance in this repository, and
it is needed even to state Stacks 0B7H, since the operation on a test scheme `g : T ⟶ X` is the
one of the module `g^*F`. It is a `Prop`, hence quantified over. -/
abbrev PullbackPreservesRank : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj F) r

/-- The identity cap rule of degree `j` given by intersection with the `j`-th Chern class of the
pulled-back module on each test scheme: `α ↦ c_j(g^*F) ∩ α`. -/
def chernIdentityCapRule (cap : HigherChernCapRule C r)
    (hrank : PullbackPreservesRank F r) (j : Fin (r + 1)) :
    IdentityCapRule C sX (j : ℤ) := fun {_T} g _ k ↦
  letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj F) r := hrank g
  cap (g ≫ sX) ((Scheme.Modules.pullback g).obj F) k j

/-- **Stacks 0B7H, the cap operation.** The cap operation of the bivariant `j`-th Chern class:
intersection with `c_j(g^*F)` on the test scheme, pushed forward to the chosen pullback
`X ×_X T`. The characterization below forces it. -/
def chernClassBivariantCap (cap : HigherChernCapRule C r) (hrank : PullbackPreservesRank F r)
    (j : Fin (r + 1)) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sX) k →+ chowGroup C (pullback.fst (𝟙 X) g ≫ sX) (k - (j : ℤ)) :=
  IdentityCapRule.transport C sX (j : ℤ) (chernIdentityCapRule C sX F r cap hrank j) g k

/-- **Stacks 0B7H.** The characterization of the bivariant `j`-th Chern class: a bivariant class
`c` of degree `j` for `𝟙 X` is *the* `j`-th Chern class of `F` when, for every test scheme
`g : T ⟶ X` and every `k`, pushing `c ∩ α` forward along the projection `X ×_X T ⟶ T` gives
`c_j(g^*F) ∩ α`.

No instance of Stacks 02S2 is needed for the projection, because it is an isomorphism. For the
cap products of Stacks 02U6 the class is `Stacks.Chow.GenuineChern.chernClass`. -/
def IsChernClassBivariant (G : GysinSystem C) (cap : HigherChernCapRule C r)
    (hrank : PullbackPreservesRank F r) (j : Fin (r + 1))
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ)) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k),
    letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback g).obj F) r := hrank g
    chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C sX g) (k - (j : ℤ)) (c.cap g k α) =
      cap (g ≫ sX) ((Scheme.Modules.pullback g).obj F) k j α

/-- **Stacks 0B7H, the cap operation is forced.** A bivariant class satisfies the characterization
of Stacks 0B7H exactly when its cap operation is `Stacks.Chow.chernClassBivariantCap`. So the
construction asked for by Stacks 0B7H has no freedom left in it: only the three naturality axioms
of Stacks 0B76 remain to be checked. -/
theorem isChernClassBivariant_iff (G : GysinSystem C) (cap : HigherChernCapRule C r)
    (hrank : PullbackPreservesRank F r) (j : Fin (r + 1))
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ)) :
    IsChernClassBivariant C sX F r G cap hrank j c ↔
      ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
        c.cap g k = chernClassBivariantCap C sX F r cap hrank j g k := by
  refine ⟨fun h {T} g _ k ↦ ?_, fun h {T} g _ k α ↦ ?_⟩
  · exact (IdentityCapRule.eq_transport_iff C sX (j : ℤ)
      (chernIdentityCapRule C sX F r cap hrank j) g k (c.cap g k)).1 fun α ↦ h (T := T) g k α
  · exact ((IdentityCapRule.eq_transport_iff C sX (j : ℤ)
      (chernIdentityCapRule C sX F r cap hrank j) g k (c.cap g k)).2 (h (T := T) g k)) α

/-- **Uniqueness in Stacks 0B7H.** Two bivariant classes satisfying the characterization of the
`j`-th Chern class of `F` are equal. -/
theorem eq_of_isChernClassBivariant (G : GysinSystem C) (cap : HigherChernCapRule C r)
    (hrank : PullbackPreservesRank F r) (j : Fin (r + 1))
    {c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (j : ℤ)}
    (hc : IsChernClassBivariant C sX F r G cap hrank j c)
    (hd : IsChernClassBivariant C sX F r G cap hrank j d) : c = d :=
  BivariantClass.eq_of_pushforward_cap_eq C sX (j : ℤ) G c d
    fun {T} g _ k α ↦ (hc (T := T) g k α).trans (hd (T := T) g k α).symm

/-- **Stacks 0B76 (1) for the bivariant Chern classes.** Granted the projection formula of Stacks
02U9 for the Chern cap rule, the forced cap operation of Stacks 0B7H satisfies the
proper-pushforward axiom of a bivariant class. -/
theorem chernClassBivariantCap_proper_naturality (cap : HigherChernCapRule C r)
    (hrank : PullbackPreservesRank F r) (j : Fin (r + 1))
    (hproper : IdentityCapRule.ProperNaturality C sX (j : ℤ)
      (chernIdentityCapRule C sX F r cap hrank j))
    {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g)
    (sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g))
    (hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - (j : ℤ)))
      (α : chowGroup C ((h ≫ g) ≫ sX) k),
      chernClassBivariantCap C sX F r cap hrank j g k
          (properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) k
            hfac α) =
        properChowPushforward C (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - (j : ℤ)) hfac'
          (chernClassBivariantCap C sX F r cap hrank j (h ≫ g) k α) :=
  IdentityCapRule.transport_proper_naturality C sX (j : ℤ)
    (chernIdentityCapRule C sX F r cap hrank j) hproper g h h' sq hfst k

end Stacks.Chow

end
