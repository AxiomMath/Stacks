module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeStack

/-! # Gluing the pairs of a descent datum of descent pairs

This continues the third stage of the construction of the stackification of a fibred category
(`StacksFrontier/CategoryTheory/Sites/Stackification/StageThree.lean`) with the first half of item 3
of the list of obligations left there: the object that a descent datum *of descent pairs* must
descend to.

## The statement that is being aimed at is not the obvious one

It is tempting to aim at `CategoryTheory.Functor.HasEffectiveDescent` for
`CategoryTheory.Functor.descentPairProj` with no hypothesis on the source beyond fibredness. **That
statement is false**, and the following is a complete refutation rather than a difficulty.

Let `F` be a presheaf of sets on the site and let `p` be the fibred category of its elements:
objects the pairs `(U, s)` with `s ∈ F U`, and a morphism `(U, s) ⟶ (V, t)` over `u : U ⟶ V`
exactly when `F u t = s`. This is fibred in sets, so every hom-set of a fibre is a subsingleton, a
`CategoryTheory.Functor.SieveDescentDatum` for it relative to a sieve `R` on `U` is exactly a
matching family of `F` over `R` — the gluing isomorphisms carry no information and their existence
*is* the matching condition — and two `CategoryTheory.Functor.DescentPair`s over `U` are isomorphic
exactly when their matching families agree on a common covering refinement. In other words
`DescentPair p J` over `U` is the plus construction `F⁺(U)`, and since a fibre of
`descentPairProj` is a setoid, a descent datum for `descentPairProj` relative to `R` is a matching
family of `F⁺` over `R` and it is effective exactly when that family has an amalgamation. So

  `HasEffectiveDescent (descentPairProj p J) J` for this `p` ⟺ `F⁺` is a sheaf,

and `F⁺` is a sheaf only when `F` is separated: for a general presheaf the plus construction has to
be applied twice. Hence effective descent for the third stage genuinely needs a hypothesis on the
source, and the hypothesis is the one the first two stages exist to produce — that the morphism
presheaves of the source are sheaves. This is also what Stacks 02ZN says: stage three is carried
out "in the case where the morphism presheaves are all sheaves", which is what the first two stages
reduce to.

The hypothesis is available, for the source that Stacks 02ZN applies stage three to, as
`CategoryTheory.Functor.locallyEqual_stageTwoProj_iff` (separatedness) and
`CategoryTheory.Functor.exists_amalgamation_stageTwoProj` (gluing).

## What is proved here

The object of the base, the covering sieve and the objects of the amalgamated pair — everything
about the descent of a datum of pairs that needs no sheaf hypothesis at all.

Let `D` be a descent datum for `descentPairProj p J` relative to a covering sieve `R` on `U`. For
an arrow `f : V ⟶ U` of `R` it attaches an object of the fibre of `descentPairProj` over `V`, that
is a descent pair whose object of the base is *propositionally* `V`;
`CategoryTheory.Functor.SieveDescentDatum.pairAt` normalises it to a pair whose object of the base
is `V` on the nose, by pulling back along the transport, which
`CategoryTheory.Functor.DescentPair.pullback` records literally. The sieve of the amalgamated pair
is then the sieve `CategoryTheory.Functor.SieveDescentDatum.glueSieve` of all composites `g ≫ f`
with `f` an arrow of `R` and `g` an arrow of the sieve of `pairAt f`, and it is a covering sieve by
the transitivity axiom (`CategoryTheory.Functor.SieveDescentDatum.glueSieve_mem`). An arrow of it
factors as such a composite in possibly many ways, so the object attached to it is read off a
chosen factorisation: `CategoryTheory.Functor.SieveDescentDatum.GlueFactorization`,
`CategoryTheory.Functor.SieveDescentDatum.factor` and
`CategoryTheory.Functor.SieveDescentDatum.glueObj`.

## Obligations that remain

The following are **not** proved here, and no declaration here may be read as claiming them. This
file is *not* Stacks 02ZN and carries no `@[stacks 02ZN]` tag.

1. The gluing isomorphisms of the amalgamated datum, which is where the sheaf hypothesis enters and
   which is the whole remaining content. Two factorisations `(f₁, g₁)` and `(f₂, g₂)` of two arrows
   of the glued sieve, and a pair of morphisms `ε₁`, `ε₂` into their sources agreeing over `U`,
   are compared by the gluing isomorphism of `D` read at the arrows `ε₁ ≫ g₁` and `ε₂ ≫ g₂` of
   `R`. That isomorphism is an isomorphism of *pairs* over the common source `Z`, hence a
   `CategoryTheory.Functor.DescentMor`, hence a family of isomorphisms of objects of the fibres of
   `p` indexed by a covering sieve of `Z` and no isomorphism over `Z` itself — one passes from the
   pairs to the objects by `CategoryTheory.Functor.SieveDescentDatum.contract`, and the family is
   compatible by `CategoryTheory.Functor.SieveDescentDatum.contract_glue`. Amalgamating it into a
   single isomorphism over `Z` is exactly the gluing half of the sheaf condition for the morphism
   presheaves of `p`, and it is the step that the refutation above shows cannot be avoided.
2. The cocycle condition and the compatibility with base change of the amalgamated datum. Both are
   equations between morphisms of one fibre, so both follow from item 1 together with the
   separatedness half of the sheaf condition, applied over the covering sieve on which the two
   sides are constructed.
3. Effectiveness itself: the cartesian morphism from `pairAt f` to the amalgamated pair, over `f`.
   Its morphism datum is defined on the sieve of `pairAt f` and attaches to an arrow `g` the
   comparison of `pairAt f`'s object at `g` with the object the amalgamated datum attaches to
   `g ≫ f`, which is item 1 again, for the two factorisations `(f, g)` and the chosen one.
4. `CategoryTheory.Functor.HasEffectiveDescent` for
   `CategoryTheory.Functor.stageThreeProj`, obtained from 1–3 by feeding in
   `CategoryTheory.Functor.locallyEqual_stageTwoProj_iff` and
   `CategoryTheory.Functor.exists_amalgamation_stageTwoProj`; and then
   `CategoryTheory.Functor.IsStack`, which also needs the `CategoryTheory.Functor.IsMorSheaf` half.

## References

This is part of the proof of Stacks 02ZN. Nothing in this file may be read as claiming
Stacks 02ZN, or any of the statements 02ZP, 0435, 0436, 04WJ that go with it.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

namespace SieveDescentDatum

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮} {U : 𝒮} {R : Sieve U}

/-! ### The pairs of a descent datum of pairs, normalised -/

/-- The descent pair that a descent datum of descent pairs attaches to an arrow `f : V ⟶ U` of its
sieve, normalised so that its object of the base is `V` on the nose.

The datum attaches an object of the fibre of `CategoryTheory.Functor.descentPairProj` over `V`,
which is a pair together with a *propositional* identification of its object of the base with `V`;
pulling back along the transport turns that into an identification on the nose, because
`CategoryTheory.Functor.DescentPair.pullback` records the object of the base literally. -/
@[reducible]
def pairAt (D : SieveDescentDatum (p.descentPairProj J) R) {V : 𝒮} (f : V ⟶ U)
    (hf : R.arrows f) : DescentPair p J :=
  (D.obj f hf).1.pullback (eqToHom (show V = (D.obj f hf).1.pt from (D.obj f hf).2.symm))

/-- The object of the base of the normalised pair attached to `f : V ⟶ U` is `V`. -/
@[simp]
theorem pairAt_pt (D : SieveDescentDatum (p.descentPairProj J) R) {V : 𝒮} (f : V ⟶ U)
    (hf : R.arrows f) : (D.pairAt f hf).pt = V := rfl

/-- The normalised pair is a pullback of the pair the datum attaches to the arrow, along an
isomorphism of the base; so nothing is lost by normalising. -/
theorem pairAt_eq_pullback (D : SieveDescentDatum (p.descentPairProj J) R) {V : 𝒮} (f : V ⟶ U)
    (hf : R.arrows f) :
    D.pairAt f hf =
      (D.obj f hf).1.pullback (eqToHom (show V = (D.obj f hf).1.pt from (D.obj f hf).2.symm)) :=
  rfl

/-- The sieve of the normalised pair is a covering sieve of the source of the arrow. -/
theorem pairAt_sieve_mem (D : SieveDescentDatum (p.descentPairProj J) R) {V : 𝒮} (f : V ⟶ U)
    (hf : R.arrows f) : (D.pairAt f hf).sieve ∈ J V :=
  (D.pairAt f hf).sieve_mem

/-! ### The covering sieve of the amalgamated pair -/

/-- The sieve of the pair that a descent datum of descent pairs amalgamates to: the composites
`g ≫ f` of an arrow `f` of the sieve the datum is relative to with an arrow `g` of the sieve of the
pair attached to `f`.

This is the smallest sieve that can carry the amalgamated datum: the objects the amalgamated datum
must restrict to are the objects of the pairs `D.pairAt f`, and those are indexed by the arrows of
the sieves of those pairs. -/
def glueSieve (D : SieveDescentDatum (p.descentPairProj J) R) : Sieve U where
  arrows W h := ∃ (V : 𝒮) (f : V ⟶ U) (hf : R.arrows f) (g : W ⟶ V),
    (D.pairAt f hf).sieve.arrows g ∧ g ≫ f = h
  downward_closed := by
    rintro W W' h ⟨V, f, hf, g, hg, rfl⟩ k
    exact ⟨V, f, hf, k ≫ g, (D.pairAt f hf).sieve.downward_closed hg k, assoc k g f⟩

/-- A composite of an arrow of the sieve with an arrow of the sieve of the pair attached to it is
an arrow of the glued sieve. -/
theorem mem_glueSieve (D : SieveDescentDatum (p.descentPairProj J) R) {V : 𝒮} (f : V ⟶ U)
    (hf : R.arrows f) {W : 𝒮} (g : W ⟶ V) (hg : (D.pairAt f hf).sieve.arrows g) :
    D.glueSieve.arrows (g ≫ f) :=
  ⟨V, f, hf, g, hg, rfl⟩

/-- The sieve of the pair attached to an arrow of the sieve refines the pullback of the glued sieve
along that arrow. -/
theorem pairAt_sieve_le_glueSieve_pullback (D : SieveDescentDatum (p.descentPairProj J) R)
    {V : 𝒮} (f : V ⟶ U) (hf : R.arrows f) :
    (D.pairAt f hf).sieve ≤ D.glueSieve.pullback f :=
  fun _ g hg ↦ D.mem_glueSieve f hf g hg

/-- **The glued sieve is a covering sieve.** The sieve the datum is relative to is covering, and
along each of its arrows the glued sieve is refined by the sieve of the pair attached to that
arrow, which is covering; so the transitivity axiom applies. -/
theorem glueSieve_mem (D : SieveDescentDatum (p.descentPairProj J) R) (hR : R ∈ J U) :
    D.glueSieve ∈ J U :=
  J.transitive hR _ fun _ f hf ↦
    J.superset_covering (D.pairAt_sieve_le_glueSieve_pullback f hf) (D.pairAt_sieve_mem f hf)

/-! ### The objects of the amalgamated datum -/

/-- A factorisation of an arrow of `CategoryTheory.Functor.SieveDescentDatum.glueSieve` as an arrow
of the sieve of one of the pairs of the datum followed by the corresponding arrow of the sieve the
datum is relative to.

An arrow of the glued sieve may factor in many ways, and the object the amalgamated datum attaches
to it is read off one chosen factorisation (`CategoryTheory.Functor.SieveDescentDatum.glueObj`). -/
structure GlueFactorization (D : SieveDescentDatum (p.descentPairProj J) R) {W : 𝒮} (h : W ⟶ U)
    where
  /-- The source of the arrow of the sieve the datum is relative to. -/
  src : 𝒮
  /-- The arrow of the sieve the datum is relative to. -/
  arr : src ⟶ U
  /-- It is one of that sieve's arrows. -/
  mem : R.arrows arr
  /-- The arrow of the sieve of the pair attached to it. -/
  loc : W ⟶ src
  /-- It is one of that sieve's arrows. -/
  loc_mem : (D.pairAt arr mem).sieve.arrows loc
  /-- The two compose to the given arrow. -/
  fac : loc ≫ arr = h

/-- Every arrow of the glued sieve admits a factorisation; this is the content of its definition,
restated so that a factorisation can be chosen from it. -/
theorem nonempty_glueFactorization (D : SieveDescentDatum (p.descentPairProj J) R) {W : 𝒮}
    {h : W ⟶ U} (hh : D.glueSieve.arrows h) : Nonempty (D.GlueFactorization h) := by
  obtain ⟨V, f, hf, g, hg, hfac⟩ := hh
  exact ⟨⟨V, f, hf, g, hg, hfac⟩⟩

/-- The chosen factorisation of an arrow of the glued sieve. -/
noncomputable def factor (D : SieveDescentDatum (p.descentPairProj J) R) {W : 𝒮} {h : W ⟶ U}
    (hh : D.glueSieve.arrows h) : D.GlueFactorization h :=
  (D.nonempty_glueFactorization hh).some

/-- The two arrows of the chosen factorisation of `h` compose to `h`. -/
@[simp]
theorem factor_fac (D : SieveDescentDatum (p.descentPairProj J) R) {W : 𝒮} {h : W ⟶ U}
    (hh : D.glueSieve.arrows h) : (D.factor hh).loc ≫ (D.factor hh).arr = h :=
  (D.factor hh).fac

/-- The object of the fibre of `p` that a factorisation of an arrow of the glued sieve names: the
object that the pair attached to the arrow of `R` attaches to the arrow of its own sieve. -/
def objOfFactorization (D : SieveDescentDatum (p.descentPairProj J) R) {W : 𝒮} {h : W ⟶ U}
    (F : D.GlueFactorization h) : p.Fiber W :=
  (D.pairAt F.arr F.mem).datum.obj F.loc F.loc_mem

/-- **The object the amalgamated descent datum attaches to an arrow of the glued sieve**: the
object named by the chosen factorisation of that arrow. -/
noncomputable def glueObj (D : SieveDescentDatum (p.descentPairProj J) R) {W : 𝒮} {h : W ⟶ U}
    (hh : D.glueSieve.arrows h) : p.Fiber W :=
  D.objOfFactorization (D.factor hh)

/-- The object attached to an arrow of the glued sieve is the object named by its chosen
factorisation. -/
theorem glueObj_eq_objOfFactorization (D : SieveDescentDatum (p.descentPairProj J) R) {W : 𝒮}
    {h : W ⟶ U} (hh : D.glueSieve.arrows h) :
    D.glueObj hh = D.objOfFactorization (D.factor hh) :=
  rfl

end SieveDescentDatum

end CategoryTheory.Functor
