module
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.FiniteCoveringsInverseSystem
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-! # The colimit of a cofiltered system of sites is a site

Let `D` be an inverse system of sites with finite coverings (Stacks 0A34): a cofiltered index
category `D.I`, for each `i` a site `(D.C i, D.J i)` each of whose coverings has a finite index
set, and for each `a : i ⟶ j` a continuous functor `D.u a : D.C j ⥤ D.C i`, compatibly with
composition. Let `C` be the colimit of the underlying categories, with canonical functors
`u i : D.C i ⥤ C`: the objects of `C` are the objects of the `D.C i`, and the morphisms are
`C (u i X, u i Y) = colim_{a : j ⟶ i} D.C j ((D.u a) X, (D.u a) Y)`.

Call a family of morphisms of `C` with fixed target a *covering* when it is the image under some
`u i` of a covering of `D.C i`. The result of this file is that these families are the coverings
of a site in the sense of Stacks 00VH: a one-element family given by an isomorphism is a covering,
coverings are stable under refinement by coverings, and for a covering `R` of `X` and any
`f : Y ⟶ X` the fibre products of the members of `R` with `f` exist and again form a covering,
of `Y`.

## Main results

* `InverseSystemOfFiniteSites.exists_precoverage_of_colimit`: the images of the coverings of the
  members of an inverse system of sites with finite coverings are the coverings of a site
  structure on the colimit of the underlying categories (Stacks 09YL).
* `InverseSystemOfSites.exists_precoverage_of_colimit`: the images of the coverings of the members
  of an inverse system of sites with finite coverings are the coverings of a site structure on the
  colimit of the underlying categories (Stacks 09YL).

## Implementation notes

A site in the sense of Stacks 00VH is a `CategoryTheory.Precoverage` satisfying the three fields of
`CategoryTheory.Pretopology`, namely `Pretopology.has_isos`, `Pretopology.transitive` and
`Pretopology.pullbacks`. It is not stated here as a `Pretopology` because that structure
presupposes `Limits.HasPullbacks C`, whereas a colimit of sites has only the fibre products that
axiom (3) demands; accordingly axiom (3) is split into the existence of those fibre products
(`Precoverage.HasPullbacks`) and the statement that they form a covering
(`Presieve.pullbackArrows`), which together are `Precoverage.pullbackArrows_mem`. For the same
reason the classes `Precoverage.IsStableUnderComposition` and
`Precoverage.IsStableUnderBaseChange` are not the axioms here: both quantify over an arbitrary
index type while membership sees only the set of arrows, so they also assert that an infinite
reindexing of a covering is a covering, which is false for a collection each of whose members has
finitely many arrows.

The coverings of `D.C i` are the *finite* covering presieves of `D.J i`, that is the members of
both `(D.J i).toPrecoverage` and `Precoverage.finite (D.C i)`. This is the collection Stacks 0A34
supplies, and `InverseSystemOfSites.finiteCoverings` is what makes it generate `D.J i`. The
finiteness is load-bearing rather than decorative: axiom (2) is proved by pushing a covering and
each of the coverings refining it into a common member of the system, which needs the index set of
the first family to be finite.

The argument of this file never looks at that generation statement, only at the other fields of the
system. It is therefore run on `InverseSystemOfFiniteSites`, which carries the same data with the
weaker, source-faithful requirement that every covering sieve merely *contain* a finite covering
family; Stacks 09YL for `InverseSystemOfSites` is then its special case along
`InverseSystemOfSites.toInverseSystemOfFiniteSites`.

That `C` is the colimit of the `D.C i` is spelled out as `hobj`, `hhom` and `hhom_inj` — every
object of `C` comes from some `D.C i`, every morphism between objects coming from `D.C i` comes
from `D.C j` for some `a : j ⟶ i`, and two morphisms of `D.C i` with the same image already agree
in some `D.C j` — rather than taken from `Limits.colimit`: Mathlib's colimits of categories
(`Cat.instHasColimits`) are constructed through nerves of simplicial sets and describe neither the
objects nor the morphisms of the colimit, while these three facts are exactly what the source's
proof uses. The dependent statement Stacks 0A35 is phrased against the same data.

On faithfulness:
* No hypothesis is dead: `hu`, `hobj`, `hhom` and `hhom_inj` together say exactly that `u`
  exhibits `C` as the colimit of the system, and both the covering families of the conclusion and
  the fibre products it produces are built out of them.
* The site data is the source's: the topologies, the cofiltered index category and the finiteness
  of the coverings are those of `D`, whose transition functors are its continuous `D.u a` rather
  than arbitrary functors.
* The precoverage is pinned, not merely asserted to exist: the first clause determines it uniquely
  as the union of the images of the coverings of the `D.C i`, which is part (2) of the statement.
* The instantiation is not degenerate: take for `D.I` a one-object category, for `D.C` a single
  category carrying the trivial topology (whose covering sieves are generated by the identity,
  hence finite), `D.u` the identity functor, and `C` that same category with `u` the identity
  functor; the colimit hypotheses hold and the coverings produced are the finite coverings of that
  site.

## References

* [Stacks 09YL](https://stacks.math.columbia.edu/tag/09YL)
-/

namespace CategoryTheory.Sites.InverseSystem

section

universe w' w v u u₁ u₂ u₃
open CategoryTheory
open CategoryTheory Limits

namespace Stacks.Sites.ColimitSite

@[expose] public section

section GeneralPresieves

variable {V : Type u} [Category.{v} V]

/-- Transporting a family of arrows along an equality of its target composes its members with the
corresponding `eqToHom`. -/
private lemma cast_ofArrows {X X' : V} (h : X = X') {ι : Type*} (W : ι → V) (f : ∀ q, W q ⟶ X) :
    h ▸ Presieve.ofArrows W f = Presieve.ofArrows W (fun q => f q ≫ eqToHom h) := by
  subst h
  simp

/-- Two families of arrows with the same index type, equal sources and equal members are the same
presieve. -/
private lemma ofArrows_congr {X : V} {ι : Type*} {W W' : ι → V} (f : ∀ q, W q ⟶ X)
    (f' : ∀ q, W' q ⟶ X) (hW : ∀ q, W q = W' q) (hf : ∀ q, f q = eqToHom (hW q) ≫ f' q) :
    Presieve.ofArrows W f = Presieve.ofArrows W' f' := by
  have hWW : W = W' := funext hW
  subst hWW
  have hff : f = f' := funext fun q => by simpa using hf q
  rw [hff]

/-- A one-element family is a finite presieve. -/
private lemma singleton_mem_finite {A B : V} (g : A ⟶ B) :
    Presieve.singleton g ∈ Precoverage.finite V B := by
  rw [← Presieve.ofArrows_pUnit.{0}]
  exact Precoverage.ofArrows_mem_finite _ _

/-- **The refinement of a family of arrows by families of arrows is the family of the composites**,
indexed by the pairs. Only the values of the refinement `T` at the members of the family enter, so
the hypothesis is that `T` is a family of arrows at those, rather than at every arrow of the
presieve as in `CategoryTheory.Presieve.ofArrows_bind`, which asks for `T` in that shape and is
therefore not applicable to a refinement that is merely known to consist of coverings. -/
private lemma bind_ofArrows {X : V} {ι : Type*} {W : ι → V} (f : ∀ p, W p ⟶ X)
    (T : ∀ ⦃Y : V⦄ (g : Y ⟶ X), Presieve.ofArrows W f g → Presieve Y) {σ : ι → Type*}
    {Z : ∀ p, σ p → V} (k : ∀ p q, Z p q ⟶ W p)
    (hT : ∀ p, T (f p) (Presieve.ofArrows.mk p) = Presieve.ofArrows (Z p) (k p)) :
    (Presieve.ofArrows W f).bind T =
      Presieve.ofArrows (fun P : (p : ι) × σ p => Z P.1 P.2) (fun P => k P.1 P.2 ≫ f P.1) := by
  refine
    le_antisymm ?_ fun Y' k' ⟨P⟩ =>
      ⟨W P.1, k P.1 P.2, f P.1, Presieve.ofArrows.mk P.1, by
        rw [hT P.1]; exact Presieve.ofArrows.mk P.2, rfl⟩
  rintro Y' k' ⟨A, a, b, ⟨p⟩, hab, rfl⟩
  rw [hT p] at hab
  obtain ⟨q⟩ := hab
  exact Presieve.ofArrows.mk (⟨p, q⟩ : (p : ι) × σ p)

/-- Composing a family of arrows with an isomorphism of the base does not change the sieve it
generates, up to pulling back along the isomorphism. -/
private lemma generate_ofArrows_comp_iso {A A' : V} (e : A ≅ A') {ι : Type*} (W : ι → V)
    (f : ∀ q, W q ⟶ A) :
    Sieve.generate (Presieve.ofArrows W (fun q => f q ≫ e.hom)) =
      Sieve.pullback e.inv (Sieve.generate (Presieve.ofArrows W f)) := by
  have key := Sieve.pullback_ofArrows_of_iso W f e.symm
  simpa using key.symm

/-- A covering family stays covering after composing its members with an isomorphism of the
base. -/
private lemma ofArrows_comp_iso_mem (J : GrothendieckTopology V) {A A' : V} (e : A ≅ A')
    {ι : Type*} {W : ι → V} (f : ∀ q, W q ⟶ A) (h : Presieve.ofArrows W f ∈ J.toPrecoverage A) :
    Presieve.ofArrows W (fun q => f q ≫ e.hom) ∈ J.toPrecoverage A' := by
  rw [GrothendieckTopology.mem_toPrecoverage_iff] at h ⊢
  rw [generate_ofArrows_comp_iso e W f]
  exact J.pullback_stable _ h

/-- Composing a family of arrows with isomorphisms of their sources does not change the sieve it
generates. -/
private lemma generate_ofArrows_iso_comp {A : V} {ι : Type*} {W W' : ι → V} (e : ∀ q, W' q ≅ W q)
    (f : ∀ q, W q ⟶ A) :
    Sieve.generate (Presieve.ofArrows W' (fun q => (e q).hom ≫ f q)) =
      Sieve.generate (Presieve.ofArrows W f) := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro q
    exact ⟨_, (e q).hom, f q, Presieve.ofArrows.mk q, rfl⟩
  · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro q
    exact ⟨_, (e q).inv, (e q).hom ≫ f q, Presieve.ofArrows.mk q, by simp⟩

/-- A covering family stays covering after composing its members with isomorphisms of their
sources. -/
private lemma ofArrows_iso_comp_mem (J : GrothendieckTopology V) {A : V} {ι : Type*} {W W' : ι → V}
    (e : ∀ q, W' q ≅ W q) (f : ∀ q, W q ⟶ A) (h : Presieve.ofArrows W f ∈ J.toPrecoverage A) :
    Presieve.ofArrows W' (fun q => (e q).hom ≫ f q) ∈ J.toPrecoverage A := by
  rw [GrothendieckTopology.mem_toPrecoverage_iff] at h ⊢
  rw [generate_ofArrows_iso_comp e f]
  exact h

end GeneralPresieves

section System

variable (D : InverseSystemOfFiniteSites.{u₁, u₂, u₃})

/-- The transition functor of a composite in the index category, on objects. -/
private lemma u_comp_obj {i j k : D.I} (b : k ⟶ j) (a : j ⟶ i) (Z : D.C i) :
    (D.u (b ≫ a)).obj Z = (D.u b).obj ((D.u a).obj Z) :=
  Functor.congr_obj (D.comp b a) Z

/-- The transition functor of a composite in the index category, on morphisms. -/
private lemma u_comp_map {i j k : D.I} (b : k ⟶ j) (a : j ⟶ i) {Z Z' : D.C i} (h : Z ⟶ Z') :
    (D.u (b ≫ a)).map h =
      eqToHom (u_comp_obj D b a Z) ≫
        (D.u b).map ((D.u a).map h) ≫ eqToHom (u_comp_obj D b a Z').symm :=
  Functor.congr_hom (D.comp b a) h

/-- Two morphisms of a member with the same image further down the system still have the same image
even further down. -/
private lemma u_map_eq_of_map_eq {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) {Z Z' : D.C i}
    {h h' : Z ⟶ Z'} (e : (D.u a).map h = (D.u a).map h') :
    (D.u (b ≫ a)).map h = (D.u (b ≫ a)).map h' := by
  rw [u_comp_map D b a h, u_comp_map D b a h', e]

/-- **Finitely many levels admit a common level below all of them and below a given one.** The
index category is cofiltered, so this is `CategoryTheory.IsCofiltered.inf_objs_exists` for the
finite set of levels involved. -/
private lemma exists_cone_obj {n : Type*} [Finite n] (i : D.I) (lv : n → D.I) :
    ∃ m : D.I, Nonempty (m ⟶ i) ∧ ∀ k, Nonempty (m ⟶ lv k) := by
  classical
  cases nonempty_fintype n
  obtain ⟨m, hm⟩ :=
    IsCofiltered.inf_objs_exists (C := D.I) (insert i (Finset.image lv Finset.univ))
  exact ⟨m, hm (by simp), fun k => hm (by simp)⟩

/-- **Two pairs of morphisms of a member, each pair agreeing further down the index category, agree
at one arrow.** -/
private lemma exists_map_eq_two {i : D.I} {Z₁ Z₁' Z₂ Z₂' : D.C i} {h₁ h₁' : Z₁ ⟶ Z₁'}
    {h₂ h₂' : Z₂ ⟶ Z₂'} (H₁ : ∃ (j : D.I) (a : j ⟶ i), (D.u a).map h₁ = (D.u a).map h₁')
    (H₂ : ∃ (j : D.I) (a : j ⟶ i), (D.u a).map h₂ = (D.u a).map h₂') :
    ∃ (j : D.I) (a : j ⟶ i),
      (D.u a).map h₁ = (D.u a).map h₁' ∧ (D.u a).map h₂ = (D.u a).map h₂' := by
  obtain ⟨j₁, a₁, e₁⟩ := H₁
  obtain ⟨j₂, a₂, e₂⟩ := H₂
  obtain ⟨j, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  refine ⟨j, b₁ ≫ a₁, u_map_eq_of_map_eq D a₁ b₁ e₁, ?_⟩
  rw [hb]
  exact u_map_eq_of_map_eq D a₂ b₂ e₂

/-- **Finitely many pairs of morphisms of a member, each pair agreeing further down the index
category, agree at one arrow.** -/
private lemma exists_map_eq_forall {n : Type*} [Finite n] {i : D.I} {Z Z' : n → D.C i}
    {h h' : ∀ k, Z k ⟶ Z' k}
    (H : ∀ k, ∃ (j : D.I) (a : j ⟶ i), (D.u a).map (h k) = (D.u a).map (h' k)) :
    ∃ (j : D.I) (a : j ⟶ i), ∀ k, (D.u a).map (h k) = (D.u a).map (h' k) := by
  choose lv arr harr using H
  obtain ⟨m, a₀, b, hb⟩ := IsCofiltered.wideCospan arr
  refine ⟨m, a₀, fun k => ?_⟩
  rw [← hb k]
  exact u_map_eq_of_map_eq D (arr k) (b k) (harr k)

/-- The square `p₁ p₂ γ φ` of the member `D.C m` *stays a fibre product below `m`*: its image under
any two transition functors `D.u a`, `D.u b` with `a : n ⟶ m` and `b : k ⟶ n` is again a fibre
product. Two transitions rather than one, because a datum of `C` is brought to the member over a
composite `b ≫ a` of index arrows, and `D.u (b ≫ a)` is `D.u a ⋙ D.u b`. -/
private def IsPullbackBelow {m : D.I} {P Am Bm Cm : D.C m} (p₁ : P ⟶ Bm) (p₂ : P ⟶ Cm)
    (γ : Bm ⟶ Am) (φ : Cm ⟶ Am) : Prop :=
  ∀ ⦃n k : D.I⦄ (a : n ⟶ m) (b : k ⟶ n),
    IsPullback ((D.u b).map ((D.u a).map p₁)) ((D.u b).map ((D.u a).map p₂))
      ((D.u b).map ((D.u a).map γ)) ((D.u b).map ((D.u a).map φ))

/-- **A fibre product of a member preserved by every transition below that member stays a fibre
product below it.** Preservation is condition (2) of continuity in the sense of Stacks 00WV, which
Situation 0A34 records as `InverseSystemOfFiniteSites.preservesPullbacks`; the two-step form is
that condition for the composite `b ≫ a`, read through `InverseSystemOfFiniteSites.comp`. -/
private lemma isPullbackBelow_of_preservesLimit {m : D.I} {P Am Bm Cm : D.C m} {p₁ : P ⟶ Bm}
    {p₂ : P ⟶ Cm} {γ : Bm ⟶ Am} {φ : Cm ⟶ Am} (h : IsPullback p₁ p₂ γ φ)
    (hpres : ∀ ⦃n : D.I⦄ (a : n ⟶ m), PreservesLimit (cospan φ γ) (D.u a)) :
    IsPullbackBelow D p₁ p₂ γ φ := by
  intro n k a b
  have : PreservesLimit (cospan φ γ) (D.u a ⋙ D.u b) := by
    rw [← D.comp b a]
    exact hpres (b ≫ a)
  exact (Functor.map_isPullback (D.u a ⋙ D.u b) h.flip).flip

end System

section Colimit

variable {C : Type w} [Category.{w'} C]

/-- The hypotheses of Stacks 09YL that say that the functors `u i : D.C i ⥤ C` exhibit `C` as the
colimit of the underlying categories of the inverse system `D`: they are compatible with the
transition functors, every object of `C` comes from some `D.C i`, and the morphisms of `C` between
objects coming from `D.C i` are the colimit over `a : j ⟶ i` of the morphisms of `D.C j` between
the transported objects. -/
private structure IsColimitOfSystem (D : InverseSystemOfFiniteSites.{u₁, u₂, u₃})
    (u : ∀ i, D.C i ⥤ C) :
    Prop where
  /-- The functors `u i` are compatible with the transition functors of the system. -/
  hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j
  /-- Every object of `C` comes from some member of the system. -/
  hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X
  /-- Every morphism of `C` between objects coming from `D.C i` comes from `D.C j` for some
  `a : j ⟶ i`. -/
  hhom :
    ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
        (u j).map g =
          eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm
  /-- Two morphisms of `D.C i` with the same image in `C` agree already in some `D.C j`. -/
  hhom_inj :
    ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
      (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂

/-- The morphism `g` of the member `D.C i` is a *lift* of the morphism `f` of `C`: the functor
`u i` identifies the source and target of `g` with those of `f`, and carries `g` to `f`. -/
private def IsLift {D : InverseSystemOfFiniteSites.{u₁, u₂, u₃}} (u : ∀ i, D.C i ⥤ C) {X Y : C}
    (f : X ⟶ Y) {i : D.I} {A B : D.C i} (g : A ⟶ B) : Prop :=
  ∃ (hA : (u i).obj A = X) (hB : (u i).obj B = Y), (u i).map g = eqToHom hA ≫ f ≫ eqToHom hB.symm

/-- The coverings of the colimit `C`: the images under the `u i` of the coverings of the `D.C i`,
that is of the finite covering presieves of the `D.J i`. -/
private def colimitPrecoverage (D : InverseSystemOfFiniteSites.{u₁, u₂, u₃})
    (u : ∀ i, D.C i ⥤ C) :
    Precoverage C
    where
  coverings X :=
    {R |
      ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
        S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i)}

variable {D : InverseSystemOfFiniteSites.{u₁, u₂, u₃}} {u : ∀ i, D.C i ⥤ C}

/-- The defining property of `colimitPrecoverage`, which is the first clause of the conclusion of
Stacks 09YL. -/
private lemma mem_colimitPrecoverage_iff {X : C} {R : Presieve X} :
    R ∈ colimitPrecoverage D u X ↔
      ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
        S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i) :=
  Iff.rfl

/-- The image of a covering of a member of the system is a covering of the colimit. -/
private lemma map_mem_colimitPrecoverage {i : D.I} {A : D.C i} {S : Presieve A}
    (hS : S ∈ (D.J i).toPrecoverage A) (hfin : S ∈ Precoverage.finite (D.C i) A) :
    S.map (u i) ∈ colimitPrecoverage D u ((u i).obj A) :=
  ⟨i, A, rfl, S, hS, hfin, rfl⟩

/-- **A covering of the colimit is the image of a finite family of arrows of a member.** This is
the description of `colimitPrecoverage` that the two remaining axioms use: `Precoverage.finite`
says that a presieve has finitely many arrows, and this replaces it by the finite family of arrows
those are. -/
private lemma mem_colimitPrecoverage_iff_ofArrows {X : C} {R : Presieve X} :
    R ∈ colimitPrecoverage D u X ↔
      ∃ (i : D.I) (A : D.C i) (h : (u i).obj A = X) (α : Type u₃) (_ : Finite α) (B : α → D.C i) (g
        : ∀ p, B p ⟶ A),
        Presieve.ofArrows B g ∈ (D.J i).toPrecoverage A ∧
          R =
            Presieve.ofArrows (fun p => (u i).obj (B p))
              (fun p => (u i).map (g p) ≫ eqToHom h) := by
  constructor
  · rintro ⟨i, A, h, S, hS, hfin, rfl⟩
    obtain ⟨α, hα, B, g, rfl⟩ :
      ∃ (α : Type u₃) (_ : Finite α) (B : α → D.C i) (g : ∀ p, B p ⟶ A),
        Presieve.ofArrows B g = S :=
      ⟨S.uncurry, (show S.uncurry.Finite from hfin).to_subtype, fun p => p.1.1, fun p => p.1.2, by
        refine le_antisymm ?_ ?_
        · rintro Z k ⟨p⟩
          exact p.2
        · exact fun Z k hk => Presieve.ofArrows.mk' (⟨⟨Z, k⟩, hk⟩ : S.uncurry) rfl (by simp)⟩
    exact ⟨i, A, h, α, hα, B, g, hS, by rw [Presieve.map_ofArrows, cast_ofArrows]⟩
  · rintro ⟨i, A, h, α, hα, B, g, hS, rfl⟩
    refine ⟨i, A, h, Presieve.ofArrows B g, hS, Precoverage.ofArrows_mem_finite B g, ?_⟩
    rw [Presieve.map_ofArrows, cast_ofArrows]

/-- Transporting an object of `D.C i` further down the index category does not change its image
in `C`. -/
private lemma IsColimitOfSystem.obj_map (hC : IsColimitOfSystem D u) {i j : D.I} (a : j ⟶ i)
    (A : D.C i) : (u j).obj ((D.u a).obj A) = (u i).obj A :=
  Functor.congr_obj (hC.hu a) A

/-- Transporting a morphism of `D.C i` further down the index category does not change its image
in `C`. -/
private lemma IsColimitOfSystem.map_map (hC : IsColimitOfSystem D u) {i j : D.I} (a : j ⟶ i)
    {A B : D.C i} (g : A ⟶ B) :
    (u j).map ((D.u a).map g) =
      eqToHom (hC.obj_map a A) ≫ (u i).map g ≫ eqToHom (hC.obj_map a B).symm :=
  Functor.congr_hom (hC.hu a) g

/-- A morphism of a member of the system is a lift of its own image. -/
private lemma isLift_map {i : D.I} {A B : D.C i} (g : A ⟶ B) : IsLift u ((u i).map g) g :=
  ⟨rfl, rfl, by simp⟩

/-- The image of a morphism of a member, read as a morphism between chosen presentations. -/
private lemma isLift_map_comp_eqToHom {i : D.I} {A B : D.C i} (g : A ⟶ B) {X Y : C}
    (hA : (u i).obj A = X) (hB : (u i).obj B = Y) :
    IsLift u (eqToHom hA.symm ≫ (u i).map g ≫ eqToHom hB) g :=
  ⟨hA, hB, by simp⟩

/-- Reading off the defining equation of a lift for chosen presentations of the source and the
target. -/
private lemma IsLift.map_eq {X Y : C} {f : X ⟶ Y} {i : D.I} {A B : D.C i} {g : A ⟶ B}
    (hg : IsLift u f g) (hA : (u i).obj A = X) (hB : (u i).obj B = Y) :
    (u i).map g = eqToHom hA ≫ f ≫ eqToHom hB.symm := by
  obtain ⟨_, _, h⟩ := hg
  exact h

/-- **A morphism of `C` is determined by any of its lifts.** -/
private lemma IsLift.eq {X Y : C} {f f' : X ⟶ Y} {i : D.I} {A B : D.C i} {g : A ⟶ B}
    (hg : IsLift u f g) (hg' : IsLift u f' g) : f = f' := by
  obtain ⟨hA, hB, h⟩ := hg
  have h' := hg'.map_eq hA hB
  subst hA hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h h'
  rw [← h, h']

/-- The identity is a lift of the identity. -/
private lemma isLift_id {i : D.I} (A : D.C i) {X : C} (hA : (u i).obj A = X) :
    IsLift u (𝟙 X) (𝟙 A) :=
  ⟨hA, hA, by simp⟩

/-- Lifts compose. -/
private lemma IsLift.comp {X Y Z : C} {f : X ⟶ Y} {f' : Y ⟶ Z} {i : D.I} {A B E : D.C i}
    {g : A ⟶ B} {g' : B ⟶ E} (hg : IsLift u f g) (hg' : IsLift u f' g') :
    IsLift u (f ≫ f') (g ≫ g') := by
  obtain ⟨hA, hB, h⟩ := hg
  obtain ⟨hB', hE, h'⟩ := hg'
  refine ⟨hA, hE, ?_⟩
  rw [Functor.map_comp, h, h']
  simp

/-- Transporting a lift along equalities of the source and the target objects. -/
private lemma IsLift.congr_src_tgt {X Y : C} {f : X ⟶ Y} {i : D.I} {A B A' B' : D.C i} {g : A ⟶ B}
    (hg : IsLift u f g) (hA : A' = A) (hB : B = B') :
    IsLift u f (eqToHom hA ≫ g ≫ eqToHom hB) := by
  subst hA hB
  simpa using hg

/-- Transporting a lift along an equality of the target object. -/
private lemma IsLift.congr_tgt {X Y : C} {f : X ⟶ Y} {i : D.I} {A B B' : D.C i} {g : A ⟶ B}
    (hg : IsLift u f g) (hB : B = B') : IsLift u f (g ≫ eqToHom hB) := by
  subst hB
  simpa using hg

/-- A lift of `f` is a lift of `f` composed with an identification of its target. -/
private lemma IsLift.comp_eqToHom {X Y Y' : C} {f : X ⟶ Y} {i : D.I} {A B : D.C i} {g : A ⟶ B}
    (hg : IsLift u f g) (h : Y = Y') : IsLift u (f ≫ eqToHom h) g := by
  subst h
  simpa using hg

/-- A lift may be pushed further down the index category. -/
private lemma IsLift.step (hC : IsColimitOfSystem D u) {X Y : C} {f : X ⟶ Y} {i : D.I}
    {A B : D.C i} {g : A ⟶ B} (hg : IsLift u f g) {j : D.I} (a : j ⟶ i) :
    IsLift u f ((D.u a).map g) := by
  obtain ⟨hA, hB, hg⟩ := hg
  refine ⟨(hC.obj_map a A).trans hA, (hC.obj_map a B).trans hB, ?_⟩
  rw [hC.map_map a g, hg]
  simp

/-- **Composing a lift with the image of a morphism of the member it lives over.** The morphism of
`C` gains a factor `(u m).map ψ` and the lift the factor `(D.u c).map ψ`; this is the step that
turns a lift of a cone in `C` into a cone in a member. -/
private lemma IsLift.comp_u_map (hC : IsColimitOfSystem D u) {m k : D.I} {c : k ⟶ m} {Z Z' : D.C m}
    {W : C} {q : W ⟶ (u m).obj Z} {Wk : D.C k} {σ : Wk ⟶ (D.u c).obj Z} (hσ : IsLift u q σ)
    (ψ : Z ⟶ Z') : IsLift u (q ≫ (u m).map ψ) (σ ≫ (D.u c).map ψ) :=
  hσ.comp ((isLift_map ψ).step hC c)

/-- A lift living over `a : j ⟶ i` may be pushed to any `c : k ⟶ i` factoring through `a`. -/
private lemma IsLift.exists_step (hC : IsColimitOfSystem D u) {X Y : C} {f : X ⟶ Y} {i : D.I}
    {A B : D.C i} {j : D.I} {a : j ⟶ i} {g : (D.u a).obj A ⟶ (D.u a).obj B} (hg : IsLift u f g)
    {k : D.I} (b : k ⟶ j) (c : k ⟶ i) (hbc : b ≫ a = c) :
    ∃ g' : (D.u c).obj A ⟶ (D.u c).obj B, IsLift u f g' := by
  subst hbc
  exact
    ⟨eqToHom (u_comp_obj D b a A) ≫ (D.u b).map g ≫ eqToHom (u_comp_obj D b a B).symm,
      (hg.step hC b).congr_src_tgt _ _⟩

/-- The source of a lift presents the source of the morphism it lifts. -/
private lemma IsLift.objEq_src {X Y : C} {f : X ⟶ Y} {i : D.I} {A B : D.C i} {g : A ⟶ B}
    (hg : IsLift u f g) : (u i).obj A = X := by
  obtain ⟨h, _, _⟩ := hg
  exact h

/-- **Two lifts of one morphism agree further down the index category.** -/
private lemma IsLift.exists_map_eq (hC : IsColimitOfSystem D u) {X Y : C} {f : X ⟶ Y} {i : D.I}
    {A B : D.C i} {g g' : A ⟶ B} (hg : IsLift u f g) (hg' : IsLift u f g') :
    ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g = (D.u a).map g' := by
  obtain ⟨hA, hB, h⟩ := hg
  exact hC.hhom_inj i A B g g' (h.trans (hg'.map_eq hA hB).symm)

/-- **Every morphism of `C` between objects presented at one member has a lift.** This is the
hypothesis `hhom`, read through `IsLift`. -/
private lemma exists_isLift' (hC : IsColimitOfSystem D u) {i : D.I} {A B : D.C i} {X Y : C}
    (hA : (u i).obj A = X) (hB : (u i).obj B = Y) (f : X ⟶ Y) :
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj A ⟶ (D.u a).obj B), IsLift u f g := by
  subst hA hB
  obtain ⟨j, a, g, hg⟩ := hC.hhom i A B f
  exact ⟨j, a, g, hC.obj_map a A, hC.obj_map a B, hg⟩

/-- Every object of `C` is presented at a member of the system lying below a given one. -/
private lemma exists_obj_below (hC : IsColimitOfSystem D u) (m : D.I) (W : C) :
    ∃ (n : D.I) (_ : n ⟶ m) (Wn : D.C n), (u n).obj Wn = W := by
  obtain ⟨l, W₀, hW₀⟩ := hC.hobj W
  obtain ⟨n, e, d, -⟩ := IsCofilteredOrEmpty.cone_objs (C := D.I) l m
  exact ⟨n, d, (D.u e).obj W₀, (hC.obj_map e W₀).trans hW₀⟩

/-- **Finitely many morphisms of `C` between objects presented at one member have lifts over one
arrow of the index category.** This is the source's remark that a finite diagram of `C` is the
image of a diagram of a single member. -/
private lemma exists_isLift_forall (hC : IsColimitOfSystem D u) {n : Type*} [Finite n] {i : D.I}
    {A B : n → D.C i} {Xs Ys : n → C} (hA : ∀ k, (u i).obj (A k) = Xs k)
    (hB : ∀ k, (u i).obj (B k) = Ys k) (f : ∀ k, Xs k ⟶ Ys k) :
    ∃ (j : D.I) (a : j ⟶ i) (g : ∀ k, (D.u a).obj (A k) ⟶ (D.u a).obj (B k)),
      ∀ k, IsLift u (f k) (g k) := by
  classical
  choose lv arr g hg using fun k => exists_isLift' hC (hA k) (hB k) (f k)
  obtain ⟨m, a₀, b, hb⟩ := IsCofiltered.wideCospan arr
  choose g' hg' using fun k => (hg k).exists_step hC (b k) a₀ (hb k)
  exact ⟨m, a₀, g', hg'⟩

/-- **Two morphisms of `C` between objects presented at one member have lifts over one arrow of
the index category.** -/
private lemma exists_isLift_two (hC : IsColimitOfSystem D u) {i : D.I} {A B A' B' : D.C i}
    {X Y X' Y' : C} (hA : (u i).obj A = X) (hB : (u i).obj B = Y) (hA' : (u i).obj A' = X')
    (hB' : (u i).obj B' = Y') (f : X ⟶ Y) (f' : X' ⟶ Y') :
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj A ⟶ (D.u a).obj B) (g' :
      (D.u a).obj A' ⟶ (D.u a).obj B'), IsLift u f g ∧ IsLift u f' g' := by
  obtain ⟨j₁, a₁, g₁, hg₁⟩ := exists_isLift' hC hA hB f
  obtain ⟨j₂, a₂, g₂, hg₂⟩ := exists_isLift' hC hA' hB' f'
  obtain ⟨m, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  obtain ⟨G, hG⟩ := hg₁.exists_step hC b₁ (b₁ ≫ a₁) rfl
  obtain ⟨G', hG'⟩ := hg₂.exists_step hC b₂ (b₁ ≫ a₁) hb.symm
  exact ⟨m, b₁ ≫ a₁, G, G', hG, hG'⟩

/-- **Two morphisms of `C` out of a common source into objects presented at one member have lifts
over one arrow of the index category, out of one object.** Both halves of the descent of a fibre
product start here: a cone in `C` over the image of a cospan of the member `m` becomes, at some
member `k` below `m`, a cone over the image of that cospan under `D.u c`. -/
private lemma exists_isLift_pair (hC : IsColimitOfSystem D u) {m : D.I} (Z Z' : D.C m) {W : C}
    (q : W ⟶ (u m).obj Z) (q' : W ⟶ (u m).obj Z') :
    ∃ (k : D.I) (c : k ⟶ m) (Wk : D.C k) (σ : Wk ⟶ (D.u c).obj Z) (σ' : Wk ⟶ (D.u c).obj Z'),
      IsLift u q σ ∧ IsLift u q' σ' := by
  obtain ⟨n, a, Wn, hW⟩ := exists_obj_below hC m W
  obtain ⟨k, b, σ, σ', hσ, hσ'⟩ :=
    exists_isLift_two hC hW (hC.obj_map a Z) hW (hC.obj_map a Z') q q'
  exact
    ⟨k, b ≫ a, (D.u b).obj Wn, σ ≫ eqToHom (u_comp_obj D b a Z).symm,
      σ' ≫ eqToHom (u_comp_obj D b a Z').symm, hσ.congr_tgt _, hσ'.congr_tgt _⟩

/-- Every morphism of `C` into an object presented at a member has a lift over an arrow of the
index category into that member. -/
private lemma exists_isLift_of_hom (hC : IsColimitOfSystem D u) {i : D.I} (A : D.C i) {X Y : C}
    (hA : (u i).obj A = X) (f : Y ⟶ X) :
    ∃ (m : D.I) (c : m ⟶ i) (Ym : D.C m) (φ : Ym ⟶ (D.u c).obj A), IsLift u f φ := by
  obtain ⟨n, α, Wn, hW⟩ := exists_obj_below hC i Y
  obtain ⟨m, a, φ, hφ⟩ := exists_isLift' hC hW ((hC.obj_map α A).trans hA) f
  exact ⟨m, a ≫ α, (D.u a).obj Wn, φ ≫ eqToHom (u_comp_obj D a α A).symm, hφ.congr_tgt _⟩

/-- **Lifts of finitely many isomorphisms of `C` are isomorphisms further down the index
category.** Given a lift `g k` of `ee k` and a lift `g' k` of its inverse, the two composites are
lifts of the identities, hence agree with the identities at some arrow of the index category by
the injectivity hypothesis, and at one such arrow for all `k` at once (`exists_map_eq_forall`);
there `g k` and `g' k` are mutually inverse.

This is what makes two presentations of one object of `C` comparable: they need not be related by
any morphism at either level, and an isomorphism between them exists only further down the
system. -/
private lemma exists_isIso_map_forall (hC : IsColimitOfSystem D u) {n : Type*} [Finite n] {i : D.I}
    {As Bs : n → D.C i} {Xs Ys : n → C} {ee : ∀ k, Xs k ≅ Ys k} {g : ∀ k, As k ⟶ Bs k}
    {g' : ∀ k, Bs k ⟶ As k} (hg : ∀ k, IsLift u (ee k).hom (g k))
    (hg' : ∀ k, IsLift u (ee k).inv (g' k)) :
    ∃ (j : D.I) (a : j ⟶ i), ∀ k, IsIso ((D.u a).map (g k)) := by
  classical
  obtain ⟨j₁, a₁, hid₁⟩ :=
    exists_map_eq_forall D (h := fun k => g k ≫ g' k) (h' := fun k => 𝟙 _) fun k =>
      IsLift.exists_map_eq hC (by simpa using (hg k).comp (hg' k)) (isLift_id _ (hg k).objEq_src)
  obtain ⟨j₂, a₂, hid₂⟩ :=
    exists_map_eq_forall D (h := fun k => g' k ≫ g k) (h' := fun k => 𝟙 _) fun k =>
      IsLift.exists_map_eq hC (by simpa using (hg' k).comp (hg k)) (isLift_id _ (hg' k).objEq_src)
  obtain ⟨j, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  refine ⟨j, b₁ ≫ a₁, fun k => ⟨(D.u (b₁ ≫ a₁)).map (g' k), ?_, ?_⟩⟩
  · simpa using u_map_eq_of_map_eq D a₁ b₁ (hid₁ k)
  · rw [hb]
    simpa using u_map_eq_of_map_eq D a₂ b₂ (hid₂ k)

/-- An isomorphism whose `hom` is a lift of `f` transports along equalities of its source and its
target to an isomorphism whose `hom` is again a lift of `f`. -/
private lemma exists_iso_of_isLift {i : D.I} {A B A' B' : D.C i} {X Y : C} {f : X ⟶ Y} (F : A ⟶ B)
    [IsIso F] (hF : IsLift u f F) (hA : A' = A) (hB : B = B') : ∃ E : A' ≅ B', IsLift u f E.hom :=
  ⟨eqToIso hA ≪≫ asIso F ≪≫ eqToIso hB, hF.congr_src_tgt hA hB⟩

/-- **Finitely many isomorphisms of `C` between objects presented at members of the system come
from isomorphisms of a single member.** The isomorphisms and their inverses are lifted to one
member (`exists_isLift_forall`), where the lifts are isomorphisms further down
(`exists_isIso_map_forall`). -/
private lemma exists_iso_forall (hC : IsColimitOfSystem D u) {n : Type*} [Finite n] {i : D.I}
    {lv : n → D.I} (Ob : ∀ k, D.C (lv k)) (Bs : n → D.C i) {Xs Ys : n → C}
    (hOb : ∀ k, (u (lv k)).obj (Ob k) = Xs k) (hBs : ∀ k, (u i).obj (Bs k) = Ys k)
    (ee : ∀ k, Xs k ≅ Ys k) :
    ∃ (m : D.I) (c : m ⟶ i) (d : ∀ k, m ⟶ lv k) (E :
      ∀ k, (D.u (d k)).obj (Ob k) ≅ (D.u c).obj (Bs k)), ∀ k, IsLift u (ee k).hom (E k).hom := by
  classical
  obtain ⟨m₀, ⟨c₀⟩, hd₀⟩ := exists_cone_obj D i lv
  have d₀ : ∀ k, m₀ ⟶ lv k := fun k => (hd₀ k).some
  have hA₁ : ∀ k, (u m₀).obj ((D.u (d₀ k)).obj (Ob k)) = Xs k := fun k =>
    (hC.obj_map (d₀ k) (Ob k)).trans (hOb k)
  have hB₁ : ∀ k, (u m₀).obj ((D.u c₀).obj (Bs k)) = Ys k := fun k =>
    (hC.obj_map c₀ (Bs k)).trans (hBs k)
  -- lifts of `ee k` and of its inverse over the single arrow `b₁ ≫ a₁`
  obtain ⟨m₁, a₁, G, hG⟩ := exists_isLift_forall hC hA₁ hB₁ fun k => (ee k).hom
  obtain ⟨m₂, a₂, G', hG'⟩ := exists_isLift_forall hC hB₁ hA₁ fun k => (ee k).inv
  obtain ⟨m₃, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  choose g hg using fun k => (hG k).exists_step hC b₁ (b₁ ≫ a₁) rfl
  choose g' hg' using fun k => (hG' k).exists_step hC b₂ (b₁ ≫ a₁) hb.symm
  -- further down the lifts are isomorphisms, and there the objects are those of one member
  obtain ⟨l, a, hiso⟩ := exists_isIso_map_forall hC hg hg'
  choose E hE using fun k =>
    exists_iso_of_isLift ((D.u a).map (g k)) ((hg k).step hC a)
      ((u_comp_obj D (a ≫ b₁ ≫ a₁) (d₀ k) (Ob k)).trans (u_comp_obj D a (b₁ ≫ a₁) _))
      (((u_comp_obj D (a ≫ b₁ ≫ a₁) c₀ (Bs k)).trans (u_comp_obj D a (b₁ ≫ a₁) _)).symm)
  exact ⟨l, (a ≫ b₁ ≫ a₁) ≫ c₀, fun k => (a ≫ b₁ ≫ a₁) ≫ d₀ k, E, hE⟩

/-- An isomorphism of `C` is the image of an isomorphism of a member of the system: it and its
inverse are lifted over one arrow of the index category, and the lift of the isomorphism is an
isomorphism further down. -/
private lemma exists_isLift_isIso (hC : IsColimitOfSystem D u) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    ∃ (i : D.I) (A B : D.C i) (g : A ⟶ B), IsIso g ∧ IsLift u f g := by
  obtain ⟨i, A, hA⟩ := hC.hobj X
  obtain ⟨j, B, hB⟩ := hC.hobj Y
  obtain ⟨l, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  have hA' : (u l).obj ((D.u a).obj A) = X := (hC.obj_map a A).trans hA
  have hB' : (u l).obj ((D.u b).obj B) = Y := (hC.obj_map b B).trans hB
  obtain ⟨m, c, g, g', hg, hg'⟩ := exists_isLift_two hC hA' hB' hB' hA' f (inv f)
  obtain ⟨m', e, hiso⟩ :=
    exists_isIso_map_forall hC (n := Unit) (ee := fun _ => asIso f) (fun _ => hg) fun _ => hg'
  exact ⟨m', _, _, (D.u e).map g, hiso (), hg.step hC e⟩

/-- A one-element family given by a covering morphism of a member of the system is a covering of
the colimit. -/
private lemma singleton_mem_colimitPrecoverage {X Y : C} {f : X ⟶ Y} {i : D.I} {A B : D.C i}
    {g : A ⟶ B} (hg : IsLift u f g) (hmem : Presieve.singleton g ∈ (D.J i).toPrecoverage B) :
    Presieve.singleton f ∈ colimitPrecoverage D u Y := by
  obtain ⟨hA, hB, hgeq⟩ := hg
  subst hA hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hgeq
  have h := map_mem_colimitPrecoverage (u := u) hmem (singleton_mem_finite g)
  rwa [Presieve.map_singleton, hgeq] at h

/-- **Axiom (1) of Stacks 00VH for the colimit**: a one-element family given by an isomorphism is a
covering. An isomorphism of `C` is the image of an isomorphism `g` of some `D.C i`
(`exists_isLift_isIso`), and `{g}` is a covering of `D.C i` because a Grothendieck topology has
isomorphisms. -/
private lemma hasIsos_colimitPrecoverage (hC : IsColimitOfSystem D u) :
    (colimitPrecoverage D u).HasIsos := by
  constructor
  intro S T f hf
  obtain ⟨i, A, B, g, hiso, hlift⟩ := exists_isLift_isIso hC f
  exact singleton_mem_colimitPrecoverage hlift (Precoverage.mem_coverings_of_isIso g)

/-- The image under a transition functor of a finite covering family is a finite covering family:
Stacks 00WV (1) for the morphism of sites `f_a`, which Situation 0A34 records as
`InverseSystemOfFiniteSites.coverPreserving`. -/
private lemma ofArrows_map_mem {i m : D.I} (a : m ⟶ i) {A : D.C i} {ι : Type*} [Finite ι]
    (B : ι → D.C i) (g : ∀ q, B q ⟶ A) (h : Presieve.ofArrows B g ∈ (D.J i).toPrecoverage A) :
    Presieve.ofArrows (fun q => (D.u a).obj (B q)) (fun q => (D.u a).map (g q)) ∈
      (D.J m).toPrecoverage ((D.u a).obj A) := by
  have h2 := (D.coverPreserving a A ⟨h, Precoverage.ofArrows_mem_finite B g⟩).1
  rwa [Presieve.map_ofArrows] at h2

/-- **Axiom (2) of Stacks 00VH for the colimit**: coverings are stable under refinement by
coverings. The covering `R` of `X` and, since its index set is finite, all the coverings refining
it come from a single member of the system, where the claim is axiom (2) for that member. -/
private lemma bind_mem_colimitPrecoverage (hC : IsColimitOfSystem D u) (X : C) (R : Presieve X)
    (T : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Presieve Y) (hR : R ∈ colimitPrecoverage D u X)
    (hT : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : R f), T f hf ∈ colimitPrecoverage D u Y) :
    R.bind T ∈ colimitPrecoverage D u X := by
  classical
  obtain ⟨i, A, hA, α, hα, B, g, hS, hReq⟩ := mem_colimitPrecoverage_iff_ofArrows.1 hR
  subst hReq
  -- present the covering that refines the `p`-th member of `R`
  choose lv Ob hOb β hβ V κ hcov hTeq using fun p : α =>
    mem_colimitPrecoverage_iff_ofArrows.1
      (hT ((u i).map (g p) ≫ eqToHom hA) (Presieve.ofArrows.mk p))
  -- compare the presentations of the sources of the members of `R` with `B`
  obtain ⟨m, c, d, E, hE⟩ := exists_iso_forall hC Ob B hOb (fun p => rfl) (fun p => Iso.refl _)
  have hAm : (u m).obj ((D.u c).obj A) = X := (hC.obj_map c A).trans hA
  refine
    mem_colimitPrecoverage_iff_ofArrows.2
      ⟨m, (D.u c).obj A, hAm, (p : α) × β p, inferInstance, fun P => (D.u (d P.1)).obj (V P.1 P.2),
        fun P => ((D.u (d P.1)).map (κ P.1 P.2) ≫ (E P.1).hom) ≫ (D.u c).map (g P.1), ?_, ?_⟩
  · -- it is a covering: axiom (2) for the member `D.C m`
    exact
      Precoverage.comp_mem_coverings (X := fun p => (D.u c).obj (B p)) (f := fun p =>
        (D.u c).map (g p)) (hf := ofArrows_map_mem c B g hS) (σ := β) (Y := fun p q =>
        (D.u (d p)).obj (V p q)) (g := fun p q => (D.u (d p)).map (κ p q) ≫ (E p).hom) (hg :=
        fun p =>
        ofArrows_comp_iso_mem (D.J m) (E p) _ (ofArrows_map_mem (d p) (V p) (κ p) (hcov p)))
  · -- its image is the refinement, arrow by arrow
    rw [bind_ofArrows _ T (fun p q => (u (lv p)).map (κ p q) ≫ eqToHom (hOb p)) hTeq]
    refine ofArrows_congr _ _ (fun P => (hC.obj_map (d P.1) (V P.1 P.2)).symm) fun P => ?_
    have l :
      IsLift u ((u (lv P.1)).map (κ P.1 P.2) ≫ eqToHom (hOb P.1))
        ((D.u (d P.1)).map (κ P.1 P.2) ≫ (E P.1).hom) := by
      simpa using
        ((((isLift_map (κ P.1 P.2)).comp_eqToHom (hOb P.1)).step hC (d P.1)).comp (hE P.1))
    exact
      IsLift.eq (l.comp (((isLift_map (g P.1)).comp_eqToHom hA).step hC c))
        (isLift_map_comp_eqToHom _ (hC.obj_map (d P.1) (V P.1 P.2)) hAm)

/-- **The image of a square staying a fibre product below its member is weakly universal in `C`.**
A cone in `C` over the image of the cospan factors through the image of the apex.

This is one half of the point at which filtered colimits commuting with finite limits is used: the
cone comes from a cone at some member `k` below `m` (`exists_isLift_pair`), where the transported
square is still a fibre product, and the factorisation it provides there has the required image
because a morphism of `C` is determined by any of its lifts. -/
private lemma exists_lift_of_isPullbackBelow (hC : IsColimitOfSystem D u) {m : D.I}
    {P Am Bm Cm : D.C m} {p₁ : P ⟶ Bm} {p₂ : P ⟶ Cm} {γ : Bm ⟶ Am} {φ : Cm ⟶ Am}
    (hPB : IsPullbackBelow D p₁ p₂ γ φ) {W : C} (q₁ : W ⟶ (u m).obj Bm) (q₂ : W ⟶ (u m).obj Cm)
    (hq : q₁ ≫ (u m).map γ = q₂ ≫ (u m).map φ) :
    ∃ r : W ⟶ (u m).obj P, r ≫ (u m).map p₁ = q₁ ∧ r ≫ (u m).map p₂ = q₂ := by
  obtain ⟨k, c, Wk, σ₁, σ₂, hσ₁, hσ₂⟩ := exists_isLift_pair hC Bm Cm q₁ q₂
  have h₁ : IsLift u (q₂ ≫ (u m).map φ) (σ₁ ≫ (D.u c).map γ) := hq ▸ hσ₁.comp_u_map hC γ
  -- the two lifted legs of the cone agree at some member below `k`, where it is a cone
  obtain ⟨l, e, he⟩ := IsLift.exists_map_eq hC h₁ (hσ₂.comp_u_map hC φ)
  obtain ⟨ρ, hρ₁, hρ₂⟩ := (hPB c e).exists_lift _ _ (by simpa only [Functor.map_comp] using he)
  have hsrc : (u l).obj ((D.u e).obj Wk) = W := (hC.obj_map e Wk).trans hσ₁.objEq_src
  have htgt : (u l).obj ((D.u e).obj ((D.u c).obj P)) = (u m).obj P :=
    (hC.obj_map e _).trans (hC.obj_map c P)
  refine ⟨eqToHom hsrc.symm ≫ (u l).map ρ ≫ eqToHom htgt, ?_, ?_⟩
  · have L := (isLift_map_comp_eqToHom ρ hsrc htgt).comp (((isLift_map p₁).step hC c).step hC e)
    rw [hρ₁] at L
    exact L.eq (hσ₁.step hC e)
  · have L := (isLift_map_comp_eqToHom ρ hsrc htgt).comp (((isLift_map p₂).step hC c).step hC e)
    rw [hρ₂] at L
    exact L.eq (hσ₂.step hC e)

/-- **The image of a square staying a fibre product below its member is jointly monic in `C`.** Two
morphisms of `C` into the image of the apex agreeing after both projections are equal.

This is the other half: the two morphisms have lifts out of one object of a member `k` below `m`,
each pair of lifted composites agrees still further down (`exists_map_eq_two`), and there the
transported square is a fibre product, so the lifts themselves agree. -/
private lemma hom_ext_of_isPullbackBelow (hC : IsColimitOfSystem D u) {m : D.I}
    {P Am Bm Cm : D.C m} {p₁ : P ⟶ Bm} {p₂ : P ⟶ Cm} {γ : Bm ⟶ Am} {φ : Cm ⟶ Am}
    (hPB : IsPullbackBelow D p₁ p₂ γ φ) {W : C} {r r' : W ⟶ (u m).obj P}
    (h₁ : r ≫ (u m).map p₁ = r' ≫ (u m).map p₁) (h₂ : r ≫ (u m).map p₂ = r' ≫ (u m).map p₂) :
    r = r' := by
  obtain ⟨k, c, Wk, ρ, ρ', hρ, hρ'⟩ := exists_isLift_pair hC P P r r'
  have k₁ : IsLift u (r' ≫ (u m).map p₁) (ρ ≫ (D.u c).map p₁) := h₁ ▸ hρ.comp_u_map hC p₁
  have k₂ : IsLift u (r' ≫ (u m).map p₂) (ρ ≫ (D.u c).map p₂) := h₂ ▸ hρ.comp_u_map hC p₂
  obtain ⟨l, e, he₁, he₂⟩ :=
    exists_map_eq_two D (IsLift.exists_map_eq hC k₁ (hρ'.comp_u_map hC p₁))
      (IsLift.exists_map_eq hC k₂ (hρ'.comp_u_map hC p₂))
  have hmono : (D.u e).map ρ = (D.u e).map ρ' :=
    (hPB c e).hom_ext (by simpa only [Functor.map_comp] using he₁)
      (by simpa only [Functor.map_comp] using he₂)
  have L := hρ.step hC e
  rw [hmono] at L
  exact L.eq (hρ'.step hC e)

/-- **The image of a fibre product of a member is a fibre product in `C`.** The two projections of
a fibre product of a member `D.C m`, provided every transition functor `D.u a` with `a : n ⟶ m`
preserves it, exhibit its image as a fibre product in `C`. This is the point at which filtered
colimits commuting with finite limits is used; the two halves are
`exists_lift_of_isPullbackBelow` and `hom_ext_of_isPullbackBelow`. -/
private lemma isPullback_u_map (hC : IsColimitOfSystem D u) {m : D.I} {Am Bm Cm : D.C m}
    (γ : Bm ⟶ Am) (φ : Cm ⟶ Am) [HasPullback γ φ]
    (hpres : ∀ ⦃n : D.I⦄ (a : n ⟶ m), PreservesLimit (cospan φ γ) (D.u a)) :
    IsPullback ((u m).map (pullback.fst γ φ)) ((u m).map (pullback.snd γ φ)) ((u m).map γ)
      ((u m).map φ) :=
  have hPB := isPullbackBelow_of_preservesLimit D (IsPullback.of_hasPullback γ φ) hpres
  IsPullback.mk' (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])
    (fun {_W} {_r _r'} h₁ h₂ => hom_ext_of_isPullbackBelow hC hPB h₁ h₂)
    (fun {_W} q₁ q₂ hq => exists_lift_of_isPullbackBelow hC hPB q₁ q₂ hq)

/-- **The image of a fibre product of a member is a fibre product of the morphisms it lifts.** -/
private lemma exists_isPullback_of_isLift (hC : IsColimitOfSystem D u) {m : D.I} {Am Bm Cm : D.C m}
    (γ : Bm ⟶ Am) (φ : Cm ⟶ Am) [HasPullback γ φ]
    (hpres : ∀ ⦃n : D.I⦄ (a : n ⟶ m), PreservesLimit (cospan φ γ) (D.u a)) {X Y Z : C} {g : Y ⟶ X}
    {f : Z ⟶ X} (hg : IsLift u g γ) (hf : IsLift u f φ) :
    ∃ (p₁ : (u m).obj (pullback γ φ) ⟶ Y) (p₂ : (u m).obj (pullback γ φ) ⟶ Z),
      IsPullback p₁ p₂ g f ∧ IsLift u p₁ (pullback.fst γ φ) ∧ IsLift u p₂ (pullback.snd γ φ) := by
  obtain ⟨hY, hX, hge⟩ := hg
  obtain ⟨hZ, _, hfe⟩ := hf
  subst hY hX hZ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hge hfe
  subst hge hfe
  exact ⟨_, _, isPullback_u_map hC γ φ hpres, isLift_map _, isLift_map _⟩

/-- **The data underlying axiom (3).** A covering of `X` and a morphism `f : Y ⟶ X` come from a
single member of the system, where the fibre products of the covering with the morphism exist —
that is axiom (3) of Stacks 00VH for the member — and are preserved by every transition functor
below it, which is condition (2) of continuity in the sense of Stacks 00WV. -/
private lemma exists_pullback_data (hC : IsColimitOfSystem D u) {X Y : C} (f : Y ⟶ X)
    (R : Presieve X) (hR : R ∈ colimitPrecoverage D u X) :
    ∃ (m : D.I) (Am Ym : D.C m) (hAm : (u m).obj Am = X) (_ : (u m).obj Ym = Y) (φ : Ym ⟶ Am) (_ :
      IsLift u f φ) (α : Type u₃) (_ : Finite α) (Bm : α → D.C m) (γ : ∀ p, Bm p ⟶ Am) (_ :
      Presieve.ofArrows Bm γ ∈ (D.J m).toPrecoverage Am) (_ : ∀ p, HasPullback (γ p) φ) (_ :
      ∀ (p : α) ⦃n : D.I⦄ (a : n ⟶ m), PreservesLimit (cospan φ (γ p)) (D.u a)),
      R =
        Presieve.ofArrows (fun p => (u m).obj (Bm p))
          (fun p => (u m).map (γ p) ≫ eqToHom hAm) := by
  obtain ⟨i, A, hA, α, hα, B, g, hS, hReq⟩ := mem_colimitPrecoverage_iff_ofArrows.1 hR
  obtain ⟨m, c, Ym, φ, hφ⟩ := exists_isLift_of_hom hC A hA f
  have hAm : (u m).obj ((D.u c).obj A) = X := (hC.obj_map c A).trans hA
  have hcov' :
    Presieve.ofArrows (fun p => (D.u c).obj (B p)) (fun p => (D.u c).map (g p)) ∈
      ((D.J m).toPrecoverage ⊓ Precoverage.finite (D.C m)) ((D.u c).obj A) :=
    ⟨ofArrows_map_mem c B g hS, Precoverage.ofArrows_mem_finite _ _⟩
  have := D.hasPullbacks m
  -- the fibre products the member has along `φ`; the presieve is named because
  -- `Presieve.hasPullback` cannot infer it from the membership proof alone
  have hpbfam :
    (Presieve.ofArrows (fun p => (D.u c).obj (B p)) (fun p => (D.u c).map (g p))).HasPullbacks φ :=
    Precoverage.hasPullbacks_of_mem φ hcov'
  refine
    ⟨m, (D.u c).obj A, Ym, hAm, hφ.objEq_src, φ, hφ, α, hα, fun p => (D.u c).obj (B p), fun p =>
      (D.u c).map (g p), hcov'.1, fun p =>
      Presieve.HasPullbacks.hasPullback (self := hpbfam) φ (Presieve.ofArrows.mk p), fun p n a =>
      D.preservesPullbacks a hcov' (Presieve.ofArrows.mk p) φ, ?_⟩
  rw [hReq]
  refine ofArrows_congr _ _ (fun p => (hC.obj_map c (B p)).symm) (fun p => ?_)
  rw [hC.map_map c (g p)]
  simp

/-- **Axiom (3) of Stacks 00VH for the colimit**, existence half: the fibre product of a member of
a covering of `X` with an arbitrary morphism `f : Y ⟶ X` exists. Both come from a single member of
the system, the fibre product is taken there, and its image is a fibre product in `C`
(`isPullback_u_map`). -/
private lemma hasPullbacks_colimitPrecoverage (hC : IsColimitOfSystem D u) :
    (colimitPrecoverage D u).HasPullbacks := by
  refine ⟨fun {X₀ Y₀ R f} hR => ?_⟩
  obtain ⟨m, Am, Ym, hAm, hYm, φ, hφ, α, hα, Bm, γ, hcov, hpb, hpres, hReq⟩ :=
    exists_pullback_data hC f R hR
  refine ⟨fun {Z h} hh => ?_⟩
  rw [hReq] at hh
  obtain ⟨p, rfl, hheq⟩ := Presieve.ofArrows_surj _ _ hh
  obtain ⟨p₁, p₂, hPB, -, -⟩ :=
    exists_isPullback_of_isLift hC (γ p) φ (hpres p) ((isLift_map (γ p)).comp_eqToHom hAm) hφ
  rw [hheq]
  simpa only [eqToHom_refl, Category.id_comp] using hPB.hasPullback

/-- **Axiom (3) of Stacks 00VH for the colimit**, covering half: the fibre products of a covering
of `X` with a morphism `f : Y ⟶ X` again form a covering, of `Y`. Downstairs they are the fibre
products of a covering of a member along a morphism of that member, which cover by
`Precoverage.pullbackArrows_mem`, and their images are the fibre products of `C` up to the
isomorphisms `exists_iso_forall` descends. -/
private lemma pullbackArrows_mem_colimitPrecoverage (hC : IsColimitOfSystem D u) (X Y : C)
    (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f] (hR : R ∈ colimitPrecoverage D u X) :
    R.pullbackArrows f ∈ colimitPrecoverage D u Y := by
  classical
  obtain ⟨m, Am, Ym, hAm, hYm, φ, hφ, α, hα, Bm, γ, hcov, hpb, hpres, hReq⟩ :=
    exists_pullback_data hC f R hR
  subst hReq
  -- the covering is named because `Presieve.hasPullback` cannot infer it from the membership
  -- proof alone
  have hmemR :
    ∀ p,
      Presieve.ofArrows (fun q => (u m).obj (Bm q)) (fun q => (u m).map (γ q) ≫ eqToHom hAm)
        ((u m).map (γ p) ≫ eqToHom hAm) :=
    fun p => Presieve.ofArrows.mk p
  have : ∀ p, HasPullback ((u m).map (γ p) ≫ eqToHom hAm) f := fun p =>
    Presieve.HasPullbacks.hasPullback f (hmemR p)
  -- the fibre products of the covering, taken in the member
  have hdown :
    Presieve.ofArrows (fun p => pullback (γ p) φ) (fun p => pullback.snd (γ p) φ) ∈
      (D.J m).toPrecoverage Ym := by
    rw [Presieve.ofArrows_pullback]
    exact Precoverage.pullbackArrows_mem φ hcov
  -- their images are the fibre products of `C`
  have H :
    ∀ p,
      ∃ (p₁ : (u m).obj (pullback (γ p) φ) ⟶ (u m).obj (Bm p)) (p₂ :
        (u m).obj (pullback (γ p) φ) ⟶ Y),
        IsPullback p₁ p₂ ((u m).map (γ p) ≫ eqToHom hAm) f ∧
          IsLift u p₂ (pullback.snd (γ p) φ) := by
    intro p
    obtain ⟨p₁, p₂, hPB, -, hL⟩ :=
      exists_isPullback_of_isLift hC (γ p) φ (hpres p) ((isLift_map (γ p)).comp_eqToHom hAm) hφ
    exact ⟨p₁, p₂, hPB, hL⟩
  choose p₁ p₂ hPB hL using H
  have hiso :
    ∀ p,
      ∃ ε : pullback ((u m).map (γ p) ≫ eqToHom hAm) f ≅ (u m).obj (pullback (γ p) φ),
        ε.hom ≫ p₂ p = pullback.snd _ f :=
    fun p =>
    ⟨(IsPullback.of_hasPullback _ f).isoIsPullback _ _ (hPB p),
      IsPullback.isoIsPullback_hom_snd _ _ _ _⟩
  choose ε hε using hiso
  have hobj :
    ∀ p, ∃ (l : D.I) (Obl : D.C l), (u l).obj Obl = pullback ((u m).map (γ p) ≫ eqToHom hAm) f :=
    fun p => hC.hobj _
  choose lv Obl hObl using hobj
  obtain ⟨m₂, c₂, d₂, E, hE⟩ :=
    exists_iso_forall hC Obl (fun p => pullback (γ p) φ) hObl (fun p => rfl) ε
  have h₂ : (u m₂).obj ((D.u c₂).obj Ym) = Y := (hC.obj_map c₂ Ym).trans hYm
  refine
    mem_colimitPrecoverage_iff_ofArrows.2
      ⟨m₂, (D.u c₂).obj Ym, h₂, α, hα, fun p => (D.u (d₂ p)).obj (Obl p), fun p =>
        (E p).hom ≫ (D.u c₂).map (pullback.snd (γ p) φ), ?_, ?_⟩
  · exact
      ofArrows_iso_comp_mem (D.J m₂) E _
        (ofArrows_map_mem c₂ (fun p => pullback (γ p) φ) (fun p => pullback.snd (γ p) φ) hdown)
  · rw [← Presieve.ofArrows_pullback]
    refine
      ofArrows_congr _ _ (fun p => ((hC.obj_map (d₂ p) (Obl p)).trans (hObl p)).symm) (fun p => ?_)
    rw [← hε p]
    exact
      IsLift.eq ((hE p).comp ((hL p).step hC c₂))
        (isLift_map_comp_eqToHom _ ((hC.obj_map (d₂ p) (Obl p)).trans (hObl p)) h₂)

end Colimit

end

end Stacks.Sites.ColimitSite

@[expose] public section

open Stacks.Sites.ColimitSite in
/-- **Colimits of sites.** Let `D` be an inverse system of sites with finite coverings over a
cofiltered index category (Stacks 0A34) — so each covering sieve of `D.J i` contains a finite
covering family, which is what makes the coverings of Stacks 00VH generate `D.J i` — and let the
functors `u i : D.C i ⥤ C` exhibit `C` as the colimit of the underlying categories: they are
compatible with the transition functors (`hu`), every object of `C` comes from some `D.C i`
(`hobj`), and the morphisms of `C` between objects coming from `D.C i` are the colimit over
`a : j ⟶ i` of the morphisms of `D.C j` between the transported objects (`hhom`, `hhom_inj`).

Then the families of morphisms of `C` that are images under the `u i` of the (finite) coverings of
the `D.C i` are the coverings of a site structure on `C` in the sense of Stacks 00VH: they contain
every one-element family given by an isomorphism, they are stable under refinement by coverings,
and for every covering of `X` and every `f : Y ⟶ X` the fibre products of the members of the
covering with `f` exist and again form a covering, of `Y`.

This is the form of Stacks 09YL that applies to an inverse system of étale sites;
`InverseSystemOfSites.exists_precoverage_of_colimit` below is its special case for a system all of
whose covering sieves happen to be finitely generated. -/
@[stacks 09YL]
public theorem InverseSystemOfFiniteSites.exists_precoverage_of_colimit {C : Type w}
    [Category.{w'} C] (D : InverseSystemOfFiniteSites) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
    (hhom :
      ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
        ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
          (u j).map g =
            eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)
    (hhom_inj :
      ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
        (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂) :
    ∃ K : Precoverage C,
      -- the coverings of `C` are the images of the finite coverings of the `D.C i`
      (∀ (X : C) (R : Presieve X),
          R ∈ K X ↔
            ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
              S ∈ (D.J i).toPrecoverage Y ∧
                S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i)) ∧
        -- Stacks 00VH (1): a one-element family given by an isomorphism is a covering
        K.HasIsos ∧
        -- Stacks 00VH (2): coverings are stable under refinement by coverings
        (∀ (X : C) (R : Presieve X) (T : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Presieve Y),
          R ∈ K X → (∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : R f), T f hf ∈ K Y) → R.bind T ∈ K X) ∧
        -- Stacks 00VH (3): the fibre products of a covering along any morphism exist, and cover
        ∃ _ : K.HasPullbacks,
          ∀ (X Y : C) (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f],
            R ∈ K X → R.pullbackArrows f ∈ K Y := by
  have hC : IsColimitOfSystem D u := ⟨hu, hobj, hhom, hhom_inj⟩
  refine
    ⟨colimitPrecoverage D u, fun X R => mem_colimitPrecoverage_iff, hasIsos_colimitPrecoverage hC,
      bind_mem_colimitPrecoverage hC, hasPullbacks_colimitPrecoverage hC, fun X Y f R _ hR =>
      pullbackArrows_mem_colimitPrecoverage hC X Y f R hR⟩

open Stacks.Sites.ColimitSite in
/-- **Colimits of sites.** Let `D` be an inverse system of sites with finite coverings over a
cofiltered index category (Stacks 0A34), and let the functors `u i : D.C i ⥤ C` exhibit `C` as the
colimit of the underlying categories: they are compatible with the transition functors (`hu`),
every object of `C` comes from some `D.C i` (`hobj`), and the morphisms of `C` between objects
coming from `D.C i` are the colimit over `a : j ⟶ i` of the morphisms of `D.C j` between the
transported objects (`hhom`, `hhom_inj`).

Then the families of morphisms of `C` that are images under the `u i` of the (finite) coverings of
the `D.C i` are the coverings of a site structure on `C` in the sense of Stacks 00VH: they contain
every one-element family given by an isomorphism, they are stable under refinement by coverings,
and for every covering of `X` and every `f : Y ⟶ X` the fibre products of the members of the
covering with `f` exist and again form a covering, of `Y`. -/
@[stacks 09YL, sga "4 VI 8.3.3" "2) (PT0),(PT1)"]
public theorem InverseSystemOfSites.exists_precoverage_of_colimit {C : Type w} [Category.{w'} C]
    (D : InverseSystemOfSites) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
    (hhom :
      ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
        ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
          (u j).map g =
            eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)
    (hhom_inj :
      ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
        (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂) :
    ∃ K : Precoverage C,
      -- the coverings of `C` are the images of the finite coverings of the `D.C i`
      (∀ (X : C) (R : Presieve X),
          R ∈ K X ↔
            ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
              S ∈ (D.J i).toPrecoverage Y ∧
                S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i)) ∧
        -- Stacks 00VH (1): a one-element family given by an isomorphism is a covering
        K.HasIsos ∧
        -- Stacks 00VH (2): coverings are stable under refinement by coverings
        (∀ (X : C) (R : Presieve X) (T : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Presieve Y),
          R ∈ K X → (∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : R f), T f hf ∈ K Y) → R.bind T ∈ K X) ∧
        -- Stacks 00VH (3): the fibre products of a covering along any morphism exist, and cover
        ∃ _ : K.HasPullbacks,
          ∀ (X Y : C) (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f],
            R ∈ K X → R.pullbackArrows f ∈ K Y :=
  InverseSystemOfFiniteSites.exists_precoverage_of_colimit D.toInverseSystemOfFiniteSites u hu hobj
    hhom hhom_inj

end

end

end CategoryTheory.Sites.InverseSystem
