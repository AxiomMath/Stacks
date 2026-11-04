module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ModificationProperties
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
import StacksCore.Tactic.StacksAttribute

/-!
# Rational singularities and local birational extensions

[Stacks, Tag 0BG0] says that a two-dimensional normal local domain `B` which is essentially of
finite type and birational over a two-dimensional normal local Nagata domain `A` defining a
rational singularity again defines a rational singularity.  The source proves it by realizing
`B` as the local ring `𝒪_{X, x}` of a normal projective modification `f : X ⟶ Spec(A)` at a
closed point `x`, spreading a normal modification `Y ⟶ Spec(𝒪_{X, x})` out to a modification
`g : X' ⟶ X` which is an isomorphism over `X ∖ {x}`, and transporting the vanishing
`H¹(X', 𝒪_{X'}) = 0` — supplied by the hypothesis on `A` — down to `H¹(Y, 𝒪_Y) = 0`.

This file formalizes that argument in its local-ring form: the base is a normal scheme `X` with a
morphism to `Spec(A)` and a closed point `x`, and the conclusion is that `𝒪_{X, x}` defines a
rational singularity.  The spreading-out step is proved from [Stacks, Tag 0B3X] and
[Stacks, Tag 0BFN]; three further inputs of the source's proof are carried as named hypotheses,
each of them a result that is absent from this development.  See the implementation notes.

## Main definitions

* `AlgebraicGeometry.IsZeroFirstStructureSheafCohomology` — the vanishing `H¹(X, 𝒪_X) = 0`, in
  the spelling in which `AlgebraicGeometry.DefinesRationalSingularity` asserts it.
* `AlgebraicGeometry.ModificationIsFinitePresentationAway`,
  `AlgebraicGeometry.SpreadOutIsNormalModification`,
  `AlgebraicGeometry.SpreadOutVanishingDescends` — the three carried hypotheses.

## Main results

* `AlgebraicGeometry.exists_isPullback_fromSpecStalk_of_isProper` — the spreading-out step: a
  proper, finitely presented morphism to `Spec(𝒪_{X, x})` which is an isomorphism over the
  punctured spectrum is the base change of a proper, finitely presented morphism to `X` which is
  an isomorphism over `X ∖ {x}`.
* `AlgebraicGeometry.definesRationalSingularity_stalk` — [Stacks, Tag 0BG0] in its local-ring
  form, granted the three carried hypotheses.

## Implementation notes

The vanishing `H¹(X, 𝒪_X) = 0` is used in the spelling of
`AlgebraicGeometry.DefinesRationalSingularity`, namely as `Subsingleton` of Mathlib's
`CategoryTheory.Sheaf.H` in degree one of the abelian sheaf underlying `𝒪_X`; so the predicate
of this file is literally the body of that definition, and no comparison of cohomology theories
is needed.  Each carried hypothesis is stated for a square witnessed by
`CategoryTheory.IsPullback` rather than for the chosen pullback of the library, so that it is
invariant under isomorphism of the base-changed scheme and can be instantiated at the scheme
`Y` actually given, with no transport of cohomology along an isomorphism of schemes.

**What is proved.**  Spreading out: the equivalence of [Stacks, Tag 0B3X] is essentially
surjective, which produces `g : X' ⟶ X` of finite presentation, an isomorphism over `X ∖ {x}`,
together with an isomorphism of its base change along `Spec 𝒪_{X, x} ⟶ X` with the given `Y`;
properness of `g` is [Stacks, Tag 0BFN].  The main theorem then assembles: the spread-out `g` is
produced, the hypothesis on `A` is applied to the modification `g ≫ f` of `Spec(A)` to get
`H¹(X', 𝒪_{X'}) = 0`, and the descent hypothesis returns `H¹(Y, 𝒪_Y) = 0`.

**What is carried.**  Three statements, none of them the assertion of [Stacks, Tag 0BG0] itself.

* `ModificationIsFinitePresentationAway`: a normal modification of `Spec(𝒪_{X, x})` is of finite
  presentation and an isomorphism over the punctured spectrum.  Over a two-dimensional normal
  local Noetherian domain this holds because a modification is of finite type over a Noetherian
  base, and because the punctured spectrum is a one-dimensional normal scheme, over which a
  proper birational morphism is an isomorphism.  Neither half is in this development.
* `SpreadOutIsNormalModification`: Step 4 of the source's proof.  The local rings of the
  spread-out `X'` are those of `X` away from `x` and those of `Y` above `x`, so `X'` is normal
  and `g ≫ f` is again a modification.  The identification of the local rings of a base change
  along `Spec 𝒪_{X, x} ⟶ X` is not in this development.
* `SpreadOutVanishingDescends`: the cohomological input, which is the first conclusion of
  [Stacks, Tag 0AXF] — the short exact sequence
  `0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ 0` — together with the
  identification of the stalk of `R¹g_*𝒪_{X'}` at `x` with `H¹(Y, 𝒪_Y)`.  Of [Stacks, Tag 0AXF]
  only the second and third conclusions are available here, as
  `…TwoModifications.topologicalKrullDim_supp_rightDerived_one_pushforward_le_zero` and
  `…TwoModifications.nonempty_generatingSections_rightDerived_one_pushforward`; the first is
  recorded there as not proved, its right-hand exactness resting on [Stacks, Tag 02V7] in fibre
  dimension one, hence on the theorem on formal functions [Stacks, Tag 02OD] and on
  [Stacks, Tag 02O5].

**What is not formalized at all.**  Steps 1 and 2 of the source's proof, which realize a
two-dimensional normal local domain `B` essentially of finite type and birational over `A` as
`𝒪_{X, x}` for a *normal projective* modification `X ⟶ Spec(A)`: write `B = C_𝔮`, embed
`Spec(C)` in `𝐀ⁿ_A`, take the closure in `𝐏ⁿ_A`, see that `x` is closed by
[Stacks, Tag 02JU] and [Stacks, Tag 01TE], and replace `X` by its normalization, which is finite
by [Stacks, Tag 035S] and projective by [Stacks, Tag 0B46].  The projective closure of an affine
scheme in `𝐏ⁿ_A` is not available in this development, so the theorem below is stated for a
given `X` and `x` rather than for a given `B`.  Its hypotheses are correspondingly minimal:
nothing is assumed about `A` beyond its being a domain, and `X` is only assumed normal.

## References

* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0B3X](https://stacks.math.columbia.edu/tag/0B3X)
* [Stacks Project, Tag 0BFN](https://stacks.math.columbia.edu/tag/0BFN)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open GlueingNearPoint

/-! ### The vanishing of the first cohomology of the structure sheaf -/

/-- The first cohomology of the structure sheaf of `X` vanishes, in the spelling in which
`AlgebraicGeometry.DefinesRationalSingularity` asserts it: the degree-one `Sheaf.H` of the
abelian sheaf underlying `𝒪_X` is a subsingleton. -/
abbrev IsZeroFirstStructureSheafCohomology (X : Scheme.{u}) : Prop :=
  letI : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  letI : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  Subsingleton (Sheaf.H.{u, u, u, u}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj X.sheaf) 1)

/-- An integral domain defines a rational singularity exactly when the first cohomology of the
structure sheaf of every normal modification of its spectrum vanishes. -/
theorem definesRationalSingularity_iff (A : Type u) [CommRing A] [IsDomain A] :
    DefinesRationalSingularity A ↔
      ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
        IsZeroFirstStructureSheafCohomology X :=
  Iff.rfl

/-! ### Spreading out a modification of the local ring at a closed point -/

/-- Properness of the structure morphism of an object of `Over T` depends only on its
isomorphism class. -/
private theorem isProper_hom_of_iso {T : Scheme.{u}} {V W : Over T} (e : V ≅ W)
    (h : IsProper W.hom) : IsProper V.hom := by
  have : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  rw [← Over.w e.hom]
  infer_instance

/-- **Spreading out a modification of `Spec 𝒪_{X, x}`.**  Let `x` be a closed point of a scheme
`X` whose open complement has quasi-compact inclusion.  A proper morphism `p : Y ⟶ Spec 𝒪_{X, x}`
of finite presentation which is an isomorphism over the punctured spectrum is the base change
along `Spec 𝒪_{X, x} ⟶ X` of a proper morphism `g : X' ⟶ X` of finite presentation which is an
isomorphism over `X ∖ {x}`.

This is the essential surjectivity of the equivalence of [Stacks, Tag 0B3X], together with the
properness criterion of [Stacks, Tag 0BFN]. -/
@[ega "IV 8.1.2" "special case"]
theorem exists_isPullback_fromSpecStalk_of_isProper (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) (hqc : QuasiCompact (puncturedOpen hx).ι)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (X.presheaf.stalk x))
    (hp : IsFinitePresentationAway ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx) (Over.mk p))
    (hproper : IsProper p) :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ X) (q : Y ⟶ X'),
      IsFinitePresentationAway (puncturedOpen hx) (Over.mk g) ∧ IsProper g ∧
        IsPullback q p g (X.fromSpecStalk x) := by
  have : (finitePresentationAwayBaseChange X x hx).IsEquivalence :=
    finitePresentationAwayBaseChange_isEquivalence X x hx hqc
  set F := finitePresentationAwayBaseChange X x hx with hFdef
  -- The given morphism, as an object of the local category.
  let W : FinitePresentationAway ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx) := ⟨Over.mk p, hp⟩
  -- Its preimage under the equivalence, and the comparison isomorphism.
  let Z : FinitePresentationAway (puncturedOpen hx) := F.objPreimage W
  let e : (IsFinitePresentationAway ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx)).ι.obj (F.obj Z) ≅
      (IsFinitePresentationAway ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx)).ι.obj W :=
    (IsFinitePresentationAway ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx)).ι.mapIso
      (F.objObjPreimageIso W)
  -- The base change of `Z` is the chosen pullback of its structure morphism.
  have hsnd : ((IsFinitePresentationAway
      ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx)).ι.obj (F.obj Z)).hom =
      pullback.snd Z.obj.hom (X.fromSpecStalk x) := rfl
  -- Properness of the spread-out morphism, by Tag 0BFN.
  have hZproper : IsProper Z.obj.hom := by
    refine (isProper_iff_isProper_baseChange X x hx hqc Z).mpr ?_
    exact isProper_hom_of_iso e hproper
  have hiso : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  -- The comparison isomorphism exhibits `Y` as the chosen pullback.
  have key : ∃ α : Y ⟶ pullback Z.obj.hom (X.fromSpecStalk x), IsIso α ∧
      α ≫ pullback.snd Z.obj.hom (X.fromSpecStalk x) = p := by
    refine ⟨e.inv.left, hiso, ?_⟩
    rw [← hsnd]
    exact Over.w e.inv
  obtain ⟨α, hαiso, hα⟩ := key
  have _ : IsIso α := hαiso
  refine ⟨Z.obj.left, Z.obj.hom, α ≫ pullback.fst Z.obj.hom (X.fromSpecStalk x),
    Z.property, hZproper, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso α) rfl hα
  rw [Category.assoc, pullback.condition, ← Category.assoc, hα]

/-! ### The three carried hypotheses -/

/-- **A carried hypothesis.**  Every normal modification of the spectrum of the local ring
`𝒪_{X, x}` is of finite presentation and an isomorphism over the punctured spectrum.

For a two-dimensional normal local Noetherian domain this holds: a modification is of finite
type over a Noetherian base, hence of finite presentation, and the punctured spectrum is a
one-dimensional normal scheme, over which a proper birational morphism is an isomorphism. -/
def ModificationIsFinitePresentationAway {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) [IsDomain ↥(X.presheaf.stalk x)] : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (p : Y ⟶ Spec (.of ↥(X.presheaf.stalk x))), IsNormal Y →
    IsModification p →
      IsFinitePresentationAway ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx) (Over.mk p)

/-- **A carried hypothesis: Step 4 of the source's proof of [Stacks, Tag 0BG0].**  If a proper
morphism `g : X' ⟶ X` has a normal base change `Y` along `Spec 𝒪_{X, x} ⟶ X`, then `X'` is
normal and `g ≫ f` is a modification of `Spec(A)`.

The source's reason: the local rings of `X'` are those of `X` at the points outside `x` and
those of `Y` at the points above `x`, and both `X` and `Y` are normal.  The identification of
the local rings of a base change along `Spec 𝒪_{X, x} ⟶ X` is not in this development. -/
def SpreadOutIsNormalModification {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) : Prop :=
  ∀ ⦃X' Y : Scheme.{u}⦄ (g : X' ⟶ X) (p : Y ⟶ Spec (X.presheaf.stalk x)) (q : Y ⟶ X'),
    IsPullback q p g (X.fromSpecStalk x) → IsProper g → IsNormal Y →
      IsNormal X' ∧ IsModification (g ≫ f)

/-- **A carried hypothesis: the first conclusion of [Stacks, Tag 0AXF] with flat base change.**
If `g : X' ⟶ X` is proper with normal source, `g ≫ f` is a modification of `Spec(A)`, and `Y` is
the base change of `g` along `Spec 𝒪_{X, x} ⟶ X`, then the vanishing of `H¹(X', 𝒪_{X'})` implies
the vanishing of `H¹(Y, 𝒪_Y)`.

The source's reason: the short exact sequence
`0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ 0` of [Stacks, Tag 0AXF] makes
`R¹g_*𝒪_{X'}` have no global sections, and it is generated by global sections, so it vanishes;
its stalk at `x` is `H¹(Y, 𝒪_Y)`.  Only the second and third conclusions of
[Stacks, Tag 0AXF] are available in this development. -/
def SpreadOutVanishingDescends {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) : Prop :=
  ∀ ⦃X' Y : Scheme.{u}⦄ (g : X' ⟶ X) (p : Y ⟶ Spec (X.presheaf.stalk x)) (q : Y ⟶ X'),
    IsPullback q p g (X.fromSpecStalk x) → IsProper g → IsNormal X' → IsNormal Y →
      IsModification (g ≫ f) →
        IsZeroFirstStructureSheafCohomology X' → IsZeroFirstStructureSheafCohomology Y

/-! ### Tag 0BG0 in its local-ring form -/

/-- **[Stacks, Tag 0BG0], local-ring form.**  Let `A` be a domain defining a rational
singularity, `X` a normal scheme with a morphism `f : X ⟶ Spec(A)`, and `x ∈ X` a closed point
whose open complement has quasi-compact inclusion.  Then the local ring `𝒪_{X, x}` defines a
rational singularity.

A normal modification of `Spec 𝒪_{X, x}` is spread out to a proper morphism `g : X' ⟶ X` which
is an isomorphism over `X ∖ {x}` by [Stacks, Tag 0B3X] and [Stacks, Tag 0BFN]; the hypothesis on
`A` applies to the modification `g ≫ f`, and the vanishing descends to the base change. -/
@[stacks 0BG0 "the local-ring form: `𝒪_{X, x}` defines a rational singularity for a closed point \
`x` of a normal scheme `X` over `Spec(A)`.  Proved: the spreading out of a normal modification \
of `Spec 𝒪_{X, x}` to a proper modification of `X` (Tags 0B3X and 0BFN) and the application of \
the hypothesis on `A` to it.  Carried as named hypotheses: `ModificationIsFinitePresentationAway` \
(a normal modification of a two-dimensional normal local ring is of finite presentation and an \
isomorphism over the punctured spectrum), `SpreadOutIsNormalModification` (Step 4 of the \
source's proof: the local rings of the spread-out scheme), and `SpreadOutVanishingDescends` (the \
first conclusion of Tag 0AXF, absent from this development, together with the identification of \
the stalk of `R¹g_*𝒪_{X'}` with `H¹(Y, 𝒪_Y)`).  Not formalized: Steps 1 and 2, which realize a \
two-dimensional normal local domain essentially of finite type and birational over `A` as such \
an `𝒪_{X, x}` by taking the closure of `Spec(C) ⊆ 𝐀ⁿ_A` in `𝐏ⁿ_A` and normalizing"]
theorem definesRationalSingularity_stalk {A : Type u} [CommRing A] [IsDomain A]
    {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A)) (x : X)
    (hx : IsClosed ({x} : Set X)) (hqc : QuasiCompact (puncturedOpen hx).ι)
    (hA : DefinesRationalSingularity A)
    (hfp : ModificationIsFinitePresentationAway x hx)
    (hnormal : SpreadOutIsNormalModification f x)
    (hdescend : SpreadOutVanishingDescends f x) :
    DefinesRationalSingularity ↥(X.presheaf.stalk x) := by
  intro Y hYnormal p hp
  have := hYnormal
  obtain ⟨X', g, q, -, hgproper, hsq⟩ :=
    exists_isPullback_fromSpecStalk_of_isProper X x hx hqc p (hfp p hYnormal hp) hp.isProper
  obtain ⟨hX'normal, hmod⟩ := hnormal g p q hsq hgproper hYnormal
  have := hX'normal
  exact hdescend g p q hsq hgproper hX'normal hYnormal hmod (hA X' (g ≫ f) hmod)

end AlgebraicGeometry

end
