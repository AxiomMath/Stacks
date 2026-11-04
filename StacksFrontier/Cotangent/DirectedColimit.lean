module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Finsupp.Ext
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Cotangent.StandardResolutionSquareFunctoriality

/-!
# The cotangent complex commutes with directed colimits

Let `A i → B i` be a system of ring maps over a directed index set `I`, with `Ainf` a colimit of
the `A i` and `Binf` a colimit of the `B i`. The functoriality of the cotangent complex in the
*pair* of rings turns the commutative squares `A i → A j`, `B i → B j` of the system into maps
`L_{B i⁄A i} → L_{B j⁄A j}`, and the squares comparing a stage with the colimit into maps
`L_{B i⁄A i} → L_{Binf⁄Ainf}`. This file proves that those maps exhibit `L_{Binf⁄Ainf}` as the
colimit of the `L_{B i⁄A i}`.

The proof is degreewise and completely explicit. In simplicial degree `n` the term of the
cotangent complex is free over `B` on the variables of the polynomial algebra `P_n`, by
`KaehlerDifferential.basisOfMvPolynomialAlgEquiv`; the canonical maps take basis vectors to
basis vectors, so the question reduces to the colimit of the systems of coefficients and of
variables. The variables of `P_{n+1}` are the elements of `P_n`, so an induction on `n` — whose
step is that a directed colimit of polynomial rings on a directed colimit of variable types is
the polynomial ring on the colimits — identifies the colimit of the systems of variables. The
free modules on these are then handled by the corresponding statement for finitely supported
functions.

## Main definitions

* `IsDirectedColimitOfTypes`: the elementwise criterion for a family of maps `g i : F i → X` to
  exhibit `X` as the colimit of a directed system of types.
* `CommAlgCat.cotangentComplexAb` and `CommAlgCat.cotangentComplexAbMap`: the cotangent complex
  and the map induced by a square of ring maps, read on underlying abelian groups.
* `CommAlgCat.cotangentComplexBasis`: the basis of the degree-`-n` term of the cotangent complex
  indexed by the variables of the degree-`n` term of the standard resolution.

## Main results

* `IsDirectedColimitOfTypes.mvPolynomial` and `IsDirectedColimitOfTypes.finsupp`: polynomial
  rings and finitely supported functions commute with directed colimits of coefficients and of
  index types.
* `CommAlgCat.standardResolutionSquareMap_isDirectedColimit`: each term of the standard
  resolution commutes with directed colimits.
* `CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb`: in every degree the canonical maps
  exhibit `L_{Binf⁄Ainf}` as the directed colimit of the `L_{B i⁄A i}`.
* `CommAlgCat.cotangentComplex_colimit`: the diagram of cotangent complexes formed by those maps
  is a colimit diagram of complexes of abelian groups.

## Implementation notes

The two colimit rings appear as hypotheses rather than as a construction: `Ainf` and `Binf` with
the comparison squares `cocone i`, required to be colimits in the elementwise sense of
`IsDirectedColimitOfTypes`. That is strictly more general than fixing the model
`Ring.DirectLimit`, and it leaves the universe of the colimit rings free rather than tying it to
the index set. The identity and cocycle conditions of the system are contained in the colimit
hypotheses on the two systems of rings, so they are not separate ambient data.

Since the term of `L_{B i⁄A i}` in degree `n` is a module over the varying ring `B i`, the
system and its colimit are taken at the level of abelian groups. This loses nothing: the
forgetful functor to abelian groups is faithful and preserves filtered colimits, the maps of the
system are maps of modules by construction, and the action of `Binf` is determined by the
actions of the `B i`.

`IsDirectedColimitOfTypes` is stated for maps of types so that one predicate serves the two
systems of rings and the system of abelian groups in degree `n`; for rings and for abelian
groups it is the usual criterion. It is deliberately *not* the `IsDirectedColimit` of
`StacksFrontier.RingTheory.Algebra.DirectLimit.Descent`, which is a predicate on a system of
algebras over a fixed base ring and cannot express a system of abelian groups.

The two base rings `A i` and `Ainf` are unrelated, so they live in independent universes, and
the module universe of the algebras is independent of both. The *categorical* packaging of the
result — `CommAlgCat.cotangentComplexAbFunctor`, its cocone and
`CommAlgCat.isColimit_cotangentComplexAbCocone` — is stated with all three universes equal, for
a technical reason and not a mathematical one: with the module universe written `max u w v`, a
universe variable of one of these declarations occurs only underneath a `max`, and applying one
to another leaves the unifier a constraint `max ?a ?b =?= max u w v` that it cannot solve. The
mathematics is the fully general degreewise statement
`CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb`, which keeps the three universes
independent.

## References

* [Stacks Project, Tag 08S9](https://stacks.math.columbia.edu/tag/08S9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w


/-- `IsDirectedColimitOfTypes f g` asserts that the maps `g i : F i → X` exhibit `X` as the colimit
of the directed system `(F, f)`: the transition maps `f` form a directed system, the `g i`
form a cocone over it, they are jointly surjective, and two elements of one stage with the
same image in `X` already agree at a later stage.

The predicate is stated for maps of types, which for a system of rings or of abelian groups
is the usual criterion, since the forgetful functors to sets preserve filtered colimits. -/
structure IsDirectedColimitOfTypes {I : Type*} [Preorder I] {F : I → Type*} {X : Type*}
    (f : ∀ i j, i ≤ j → F i → F j) (g : ∀ i, F i → X) : Prop where
  /-- The transition map along `i ≤ i` is the identity. -/
  map_id (i : I) (a : F i) : f i i le_rfl a = a
  /-- The transition maps respect composition. -/
  map_comp (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (a : F i) :
    f j k hjk (f i j hij a) = f i k (hij.trans hjk) a
  /-- The maps `g i` form a cocone over the system. -/
  comp (i j : I) (hij : i ≤ j) (a : F i) : g j (f i j hij a) = g i a
  /-- Every element of `X` comes from some stage. -/
  jointly_surjective (b : X) : ∃ i, ∃ a : F i, g i a = b
  /-- Two elements of one stage with the same image in `X` agree at a later stage. -/
  exists_eq (i : I) (a b : F i) (h : g i a = g i b) :
    ∃ j, ∃ hij : i ≤ j, f i j hij a = f i j hij b

/-- Two elements of a stage that agree at some later stage `j` agree at every stage after `j`. -/
private theorem IsDirectedColimitOfTypes.map_eq_map_of_le {I : Type*} [Preorder I]
    {F : I → Type*} {X : Type*} {f : ∀ i j, i ≤ j → F i → F j} {g : ∀ i, F i → X}
    (h : IsDirectedColimitOfTypes f g) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) {a b : F i}
    (hab : f i j hij a = f i j hij b) : f i k (hij.trans hjk) a = f i k (hij.trans hjk) b := by
  rw [← h.map_comp i j k hij hjk, ← h.map_comp i j k hij hjk, hab]

/-- The cotangent complex `L_{B⁄A}` as a complex of abelian groups. -/
noncomputable def CommAlgCat.cotangentComplexAb (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) : CochainComplex AddCommGrpCat.{max u v} ℤ :=
  ((forget₂ (ModuleCat.{max u v} B) AddCommGrpCat.{max u v}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (CommAlgCat.cotangentComplex.{u, v} A B)

/-- The canonical map `L_{B⁄A} → L_{B'⁄A'}` of complexes of abelian groups induced by a
commutative square of ring maps, read on underlying abelian groups. -/
noncomputable def CommAlgCat.cotangentComplexAbMap {A : Type u} [CommRing A] {A' : Type w}
    [CommRing A'] {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}
    (sq : CommAlgCat.AlgebraSquare.{u, v, w} A A' B B') :
    CommAlgCat.cotangentComplexAb.{u, max w v} A B ⟶
      CommAlgCat.cotangentComplexAb.{w, max u v} A' B' where
  f n := AddCommGrpCat.ofHom
    ((CommAlgCat.squareFunctoriality sq).complexMap.f n).hom.toAddMonoidHom
  comm' i j hij := by
    ext a
    exact ConcreteCategory.congr_hom
      ((CommAlgCat.squareFunctoriality sq).complexMap.comm' i j hij) a

section PolynomialColimits

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable {R : I → Type*} [∀ i, CommRing (R i)] {Rinf : Type*} [CommRing Rinf]
variable {X : I → Type*} {Xinf : Type*}
variable (fR : ∀ i j : I, i ≤ j → R i →+* R j) (gR : ∀ i, R i →+* Rinf)
variable (fX : ∀ i j : I, i ≤ j → X i → X j) (gX : ∀ i, X i → Xinf)

/-- The transition maps of the directed system of polynomial rings induced by a directed system
of coefficient rings and a directed system of variable types: coefficients are mapped and
variables renamed. -/
noncomputable def mvPolynomialSystemMap {i j : I} (h : i ≤ j) :
    MvPolynomial (X i) (R i) →+* MvPolynomial (X j) (R j) :=
  CommAlgCat.mvPolynomialMapRename (fR i j h) (fX i j h)

/-- The comparison maps from the stages of that system of polynomial rings to the polynomial
ring on the colimit of the variable types over the colimit of the coefficient rings. -/
noncomputable def mvPolynomialSystemCocone (i : I) :
    MvPolynomial (X i) (R i) →+* MvPolynomial Xinf Rinf :=
  CommAlgCat.mvPolynomialMapRename (gR i) (gX i)

omit [IsDirectedOrder I] [Nonempty I] in
/-- The transition maps act on constants by the transition maps of the coefficients. -/
theorem mvPolynomialSystemMap_C {i j : I} (h : i ≤ j) (r : R i) :
    mvPolynomialSystemMap fR fX h (MvPolynomial.C r) = MvPolynomial.C (fR _ _ h r) :=
  CommAlgCat.mvPolynomialMapRename_C _ _ r

omit [IsDirectedOrder I] [Nonempty I] in
/-- The transition maps send variables to variables. -/
theorem mvPolynomialSystemMap_X {i j : I} (h : i ≤ j) (x : X i) :
    mvPolynomialSystemMap fR fX h (MvPolynomial.X x) = MvPolynomial.X (fX _ _ h x) :=
  CommAlgCat.mvPolynomialMapRename_X _ _ x

omit [IsDirectedOrder I] [Nonempty I] in
/-- The transition maps of the system of polynomial rings compose. -/
theorem mvPolynomialSystemMap_comp
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i => gR i))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) gX)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (p : MvPolynomial (X i) (R i)) :
    mvPolynomialSystemMap fR fX hjk (mvPolynomialSystemMap fR fX hij p) =
      mvPolynomialSystemMap fR fX (hij.trans hjk) p := by
  have hfun : (mvPolynomialSystemMap fR fX hjk).comp (mvPolynomialSystemMap fR fX hij) =
      mvPolynomialSystemMap fR fX (hij.trans hjk) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mvPolynomialSystemMap, hR.map_comp]
    · intro x
      simp [mvPolynomialSystemMap, hX.map_comp]
  exact DFunLike.congr_fun hfun p

omit [IsDirectedOrder I] [Nonempty I] in
/-- The transition map of the system of polynomial rings along `i ≤ i` is the identity. -/
theorem mvPolynomialSystemMap_id
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i => gR i))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) gX)
    {i : I} (h : i ≤ i) (p : MvPolynomial (X i) (R i)) :
    mvPolynomialSystemMap fR fX h p = p := by
  have hfun : mvPolynomialSystemMap fR fX h = RingHom.id (MvPolynomial (X i) (R i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mvPolynomialSystemMap, hR.map_id]
    · intro x
      simp [mvPolynomialSystemMap, hX.map_id]
  exact DFunLike.congr_fun hfun p

omit [IsDirectedOrder I] [Nonempty I] in
/-- The comparison maps form a cocone over the system of polynomial rings. -/
theorem mvPolynomialSystemCocone_comp
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i => gR i))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) gX)
    {i j : I} (hij : i ≤ j) (p : MvPolynomial (X i) (R i)) :
    mvPolynomialSystemCocone gR gX j (mvPolynomialSystemMap fR fX hij p) =
      mvPolynomialSystemCocone gR gX i p := by
  have hfun : (mvPolynomialSystemCocone gR gX j).comp (mvPolynomialSystemMap fR fX hij) =
      mvPolynomialSystemCocone gR gX i := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mvPolynomialSystemMap, mvPolynomialSystemCocone, hR.comp]
    · intro x
      simp [mvPolynomialSystemMap, mvPolynomialSystemCocone, hX.comp]
  exact DFunLike.congr_fun hfun p

omit [Nonempty I] in
/-- Every polynomial over the colimit of the coefficient rings in the colimit of the variable
types comes from some stage of the system. -/
theorem mvPolynomialSystemCocone_jointly_surjective
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i => gR i))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) gX) :
    ∀ p : MvPolynomial Xinf Rinf, ∃ i r, mvPolynomialSystemCocone gR gX i r = p := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
      obtain ⟨i, ri, hr⟩ := hR.jointly_surjective r
      exact ⟨i, MvPolynomial.C ri, by simp [mvPolynomialSystemCocone, hr]⟩
  | add p q hp hq =>
      obtain ⟨i, pi, hpi⟩ := hp
      obtain ⟨j, qj, hqj⟩ := hq
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, mvPolynomialSystemMap fR fX hik pi + mvPolynomialSystemMap fR fX hjk qj, ?_⟩
      simp only [map_add]
      rw [mvPolynomialSystemCocone_comp (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX hik pi,
        mvPolynomialSystemCocone_comp (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX hjk qj,
        hpi, hqj]
  | mul_X p x hp =>
      obtain ⟨i, pi, hpi⟩ := hp
      obtain ⟨j, xj, hxj⟩ := hX.jointly_surjective x
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, mvPolynomialSystemMap fR fX hik pi * MvPolynomial.X (fX _ _ hjk xj), ?_⟩
      simp only [map_mul]
      rw [← mvPolynomialSystemMap_X fR fX hjk xj,
        mvPolynomialSystemCocone_comp (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX hik pi,
        mvPolynomialSystemCocone_comp (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX hjk
          (MvPolynomial.X xj),
        hpi]
      have hx : mvPolynomialSystemCocone gR gX j (MvPolynomial.X xj) =
          MvPolynomial.X (gX j xj) := by simp [mvPolynomialSystemCocone]
      rw [hx, hxj]

/-- Two polynomials of one stage with the same image under the comparison map already agree at a
later stage of the system. -/
theorem mvPolynomialSystemMap_eventually_eq
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i => gR i))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) gX)
    {i : I} (p q : MvPolynomial (X i) (R i))
    (heq : mvPolynomialSystemCocone gR gX i p = mvPolynomialSystemCocone gR gX i q) :
    ∃ j, ∃ hij : i ≤ j, mvPolynomialSystemMap fR fX hij p = mvPolynomialSystemMap fR fX hij q := by
  classical
  obtain ⟨s, p', q', hp, hq⟩ := MvPolynomial.exists_finset_rename₂ p q
  let S := {x // x ∈ s}
  let rel : Setoid S := {
    r := fun x y => gX i x.1 = gX i y.1
    iseqv := by
      constructor
      · intro x
        rfl
      · intro x y h
        exact h.symm
      · intro x y z hxy hyz
        exact hxy.trans hyz }
  let Q := Quotient rel
  have hpair : ∀ x y : S,
      ∃ j, ∃ hij : i ≤ j,
        (gX i x.1 = gX i y.1 → fX i j hij x.1 = fX i j hij y.1) := by
    intro x y
    by_cases hxy : gX i x.1 = gX i y.1
    · obtain ⟨j, hij, h⟩ := hX.exists_eq i x.1 y.1 hxy
      exact ⟨j, hij, fun _ => h⟩
    · exact ⟨i, le_rfl, fun heq => False.elim (hxy heq)⟩
  choose j hjle hjEq using hpair
  let js : Finset I := Finset.univ.image (fun z : S × S => j z.1 z.2)
  obtain ⟨l, hl⟩ := Finset.exists_le (insert i js)
  have hil : i ≤ l := hl i (Finset.mem_insert_self i js)
  have hjl (x y : S) : j x y ≤ l :=
    hl (j x y) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩))
  have realize (x y : S) (hxy : gX i x.1 = gX i y.1) :
      fX i l hil x.1 = fX i l hil y.1 :=
    hX.map_eq_map_of_le (hjle x y) (hjl x y) (hjEq x y hxy)
  let xbar : Q → X l := Quotient.lift (fun x : S => fX i l hil x.1)
    (by intro x y h; exact realize x y h)
  let gbar : Q → Xinf := Quotient.lift (fun x : S => gX i x.1)
    (by intro x y h; exact h)
  have hgbar_inj : Function.Injective gbar := by
    intro a b hab
    exact (Quotient.inductionOn₂
      (motive := fun a b => gbar a = gbar b → a = b) a b
      (fun x y hxy => Quotient.sound hxy)) hab
  let pQ : MvPolynomial Q (R i) := MvPolynomial.rename (fun x : S => Quotient.mk rel x) p'
  let qQ : MvPolynomial Q (R i) := MvPolynomial.rename (fun x : S => Quotient.mk rel x) q'
  have hcocone (r : MvPolynomial S (R i)) :
      mvPolynomialSystemCocone gR gX i (MvPolynomial.rename (↑) r) =
        MvPolynomial.rename gbar (MvPolynomial.map (gR i)
          (MvPolynomial.rename (fun x : S => Quotient.mk rel x) r)) := by
    have hfun : (mvPolynomialSystemCocone gR gX i).comp (MvPolynomial.rename (↑)).toRingHom =
        (MvPolynomial.rename gbar).toRingHom.comp
          ((MvPolynomial.map (gR i)).comp
            (MvPolynomial.rename (fun x : S => Quotient.mk rel x)).toRingHom) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [mvPolynomialSystemCocone]
      · intro x
        simp [mvPolynomialSystemCocone, gbar, rel]
    exact DFunLike.congr_fun hfun r
  have hQ : MvPolynomial.map (gR i) pQ = MvPolynomial.map (gR i) qQ := by
    apply MvPolynomial.rename_injective gbar hgbar_inj
    rw [← hcocone, ← hcocone, ← hp, ← hq]
    exact heq
  let t := pQ.support ∪ qQ.support
  have hcoeffAll : ∀ d : Q →₀ ℕ, gR i (pQ.coeff d) = gR i (qQ.coeff d) := by
    intro d
    exact congrArg (MvPolynomial.coeff d) hQ
  choose k hk hkeq using fun d : Q →₀ ℕ => hR.exists_eq i (pQ.coeff d) (qQ.coeff d)
    (hcoeffAll d)
  obtain ⟨m, hm⟩ := Finset.exists_le (insert l (t.image k))
  have hml : l ≤ m := hm l (Finset.mem_insert_self l _)
  have hkm (d : Q →₀ ℕ) (hd : d ∈ t) : k d ≤ m :=
    hm (k d) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d, hd, rfl⟩))
  have hcoeffStage (d : Q →₀ ℕ) (hd : d ∈ t) :
      fR i m (le_trans hil hml) (pQ.coeff d) =
        fR i m (le_trans hil hml) (qQ.coeff d) :=
    hR.map_eq_map_of_le (hk d) (hkm d hd) (hkeq d)
  have hpolyStage : MvPolynomial.map (fR i m (le_trans hil hml)) pQ =
      MvPolynomial.map (fR i m (le_trans hil hml)) qQ := by
    apply MvPolynomial.ext
    intro d
    by_cases hd : d ∈ t
    · simpa only [MvPolynomial.coeff_map] using hcoeffStage d hd
    · have hp0 : pQ.coeff d = 0 := by
        by_contra hne
        exact hd (Finset.mem_union.mpr (Or.inl (MvPolynomial.mem_support_iff.mpr hne)))
      have hq0 : qQ.coeff d = 0 := by
        by_contra hne
        exact hd (Finset.mem_union.mpr (Or.inr (MvPolynomial.mem_support_iff.mpr hne)))
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, hp0, hq0]
  let xbarM : Q → X m := fun z => fX l m hml (xbar z)
  have hfun : (mvPolynomialSystemMap fR fX (le_trans hil hml)).comp
      (MvPolynomial.rename (fun x : S => x.1)).toRingHom =
      (MvPolynomial.rename xbarM).toRingHom.comp
        ((MvPolynomial.map (fR i m (le_trans hil hml))).comp
          (MvPolynomial.rename (fun x : S => Quotient.mk rel x)).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [mvPolynomialSystemMap]
    · intro x
      show MvPolynomial.rename (fX i m (le_trans hil hml))
          (MvPolynomial.map (fR i m (le_trans hil hml))
            (MvPolynomial.rename (fun y : S => y.1) (MvPolynomial.X x))) =
        MvPolynomial.rename xbarM
          (MvPolynomial.map (fR i m (le_trans hil hml))
            (MvPolynomial.rename (fun y : S => Quotient.mk rel y) (MvPolynomial.X x)))
      simp only [MvPolynomial.rename_X, MvPolynomial.map_X]
      show MvPolynomial.X (R := R m) (fX i m (le_trans hil hml) x.1) =
        MvPolynomial.X (R := R m) (fX l m hml (fX i l hil x.1))
      exact congrArg (fun z : X m => MvPolynomial.X (R := R m) z)
        (hX.map_comp i l m hil hml x.1).symm
  have hleft (r : MvPolynomial S (R i)) :
      mvPolynomialSystemMap fR fX (le_trans hil hml) (MvPolynomial.rename (fun x : S => x.1) r) =
        MvPolynomial.rename xbarM (MvPolynomial.map (fR i m (le_trans hil hml))
          (MvPolynomial.rename (fun x : S => Quotient.mk rel x) r)) :=
    DFunLike.congr_fun hfun r
  refine ⟨m, le_trans hil hml, ?_⟩
  rw [hp, hq, hleft, hleft]
  exact congrArg _ hpolyStage

/-- Polynomial rings commute with directed colimits of coefficient rings and of variable types:
the comparison maps exhibit `MvPolynomial Xinf Rinf` as the directed colimit of the
`MvPolynomial (X i) (R i)`. -/
theorem IsDirectedColimitOfTypes.mvPolynomial
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i => gR i))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) gX) :
    IsDirectedColimitOfTypes
      (fun _ _ h p => mvPolynomialSystemMap fR fX h p)
      (fun i p => mvPolynomialSystemCocone gR gX i p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i p
    exact mvPolynomialSystemMap_id (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX
      (le_rfl : i ≤ i) p
  · intro i j k hij hjk p
    exact mvPolynomialSystemMap_comp (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX hij hjk p
  · intro i j hij p
    exact mvPolynomialSystemCocone_comp (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX hij p
  · exact mvPolynomialSystemCocone_jointly_surjective (fR := fR) (gR := gR) (fX := fX)
      (gX := gX) hR hX
  · intro i p q heq
    exact mvPolynomialSystemMap_eventually_eq (fR := fR) (gR := gR) (fX := fX) (gX := gX) hR hX
      p q heq

/-- The property of being a directed colimit transfers along compatible bijections of the stages
and of the colimits. -/
theorem IsDirectedColimitOfTypes.of_equiv
    {I : Type*} [Preorder I] {F G : I → Type*} {X Y : Type*}
    (f : ∀ i j, i ≤ j → F i → F j) (g : ∀ i, F i → X)
    (f' : ∀ i j, i ≤ j → G i → G j) (g' : ∀ i, G i → Y)
    (e : ∀ i, F i ≃ G i) (eInf : X ≃ Y)
    (hG : IsDirectedColimitOfTypes f' g')
    (hf : ∀ i j (h : i ≤ j) a, e j (f i j h a) = f' i j h (e i a))
    (hg : ∀ i a, eInf (g i a) = g' i (e i a)) :
    IsDirectedColimitOfTypes f g := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i a
    apply (e i).injective
    rw [hf i i le_rfl a]
    simpa using hG.map_id i (e i a)
  · intro i j k hij hjk a
    apply (e k).injective
    rw [hf j k hjk, hf i j hij, hf i k (hij.trans hjk)]
    exact hG.map_comp i j k hij hjk (e i a)
  · intro i j hij a
    apply eInf.injective
    rw [hg j (f i j hij a), hf i j hij, hG.comp i j hij, hg i a]
  · intro x
    obtain ⟨i, y, hy⟩ := hG.jointly_surjective (eInf x)
    refine ⟨i, (e i).symm y, ?_⟩
    apply eInf.injective
    rw [hg, (e i).apply_symm_apply, hy]
  · intro i a b hab
    obtain ⟨j, hij, hstage⟩ := hG.exists_eq i (e i a) (e i b) (by rw [← hg, ← hg, hab])
    exact ⟨j, hij, (e j).injective (by rw [hf, hf, hstage])⟩


end PolynomialColimits


namespace CommAlgCat

variable {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
  {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}

/-- A ring map of algebras identified with polynomial rings, which is compatible with the structure
maps and sends variables to variables, is read in these identifications as a map renaming
variables and mapping coefficients. -/
private theorem algEquiv_conj_eq_mvPolynomialMapRename {R R' P P' X X' : Type*} [CommRing R]
    [CommRing R'] [CommRing P] [CommRing P'] [Algebra R P] [Algebra R' P']
    (e : P ≃ₐ[R] MvPolynomial X R) (e' : P' ≃ₐ[R'] MvPolynomial X' R') (φ : P →+* P')
    (σ : R →+* R') (m : X → X') (hφ : ∀ a, φ (algebraMap R P a) = algebraMap R' P' (σ a))
    (hX : ∀ x, φ (e.symm (MvPolynomial.X x)) = e'.symm (MvPolynomial.X (m x))) :
    e'.toRingHom.comp (φ.comp e.symm.toRingHom) = mvPolynomialMapRename σ m := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun x => ?_)
  · change e' (φ (e.symm (MvPolynomial.C a))) = _
    rw [mvPolynomialMapRename_C, ← MvPolynomial.algebraMap_eq, e.symm.commutes, hφ, e'.commutes,
      MvPolynomial.algebraMap_eq]
  · change e' (φ (e.symm (MvPolynomial.X x))) = _
    rw [hX, e'.apply_symm_apply, mvPolynomialMapRename_X]

/-- If `e' ∘ φ ∘ e.symm` is `ψ` pointwise, then `e' (φ p) = ψ (e p)`. -/
private theorem apply_comp_equiv_symm {P Q P' Q' : Type*} (e : P ≃ Q) (e' : P' → Q') (φ : P → P')
    (ψ : Q → Q') (h : ∀ q, e' (φ (e.symm q)) = ψ q) (p : P) : e' (φ p) = ψ (e p) := by
  simpa using h (e p)

/-- Read through the identifications `P₀ = A[B]` and `P'₀ = A'[B']`, the induced map of standard
resolutions in degree zero is the map which sends the coefficients by `sq.base` and renames the
variables by `sq.map`. -/
theorem standardResolutionZeroAlgEquiv_conj (sq : AlgebraSquare.{u, v, w} A A' B B') :
    (standardResolutionZeroAlgEquiv.{w, max u v} A' B').toRingHom.comp
        ((standardResolutionSquareMap.{u, v, w} sq (op ⦋0⦌)).comp
          (standardResolutionZeroAlgEquiv.{u, max w v} A B).symm.toRingHom) =
      mvPolynomialMapRename sq.base sq.map :=
  algEquiv_conj_eq_mvPolynomialMapRename _ _ _ _ _
    (standardResolutionSquareMap_algebraMap sq _) (standardResolutionSquareMap_zero_X sq)

/-- Read through the identifications `P_{n+1} = A[P_n]` and `P'_{n+1} = A'[P'_n]`, the induced map
of standard resolutions in degree `n + 1` is the map which sends the coefficients by `sq.base` and
renames the variables by the degree-`n` map. -/
theorem standardResolutionSuccAlgEquiv_conj (sq : AlgebraSquare.{u, v, w} A A' B B') (n : ℕ) :
    (standardResolutionSuccAlgEquiv.{w, max u v} A' B' n).toRingHom.comp
        ((standardResolutionSquareMap.{u, v, w} sq (op ⦋n + 1⦌)).comp
          (standardResolutionSuccAlgEquiv.{u, max w v} A B n).symm.toRingHom) =
      mvPolynomialMapRename sq.base (standardResolutionSquareMap.{u, v, w} sq (op ⦋n⦌)) :=
  algEquiv_conj_eq_mvPolynomialMapRename _ _ _ _ _
    (standardResolutionSquareMap_algebraMap sq _) (standardResolutionSquareMap_succ_X sq n)

end CommAlgCat

section System

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {A : I → Type u} [∀ i, CommRing (A i)] {B : ∀ i, CommAlgCat.{max u w v} (A i)}
  {Ainf : Type w} [CommRing Ainf] {Binf : CommAlgCat.{max u w v} Ainf}
  (sq : ∀ ⦃i j : I⦄, i ≤ j →
    CommAlgCat.AlgebraSquare.{u, max w v, u} (A i) (A j) (B i) (B j))
  (cocone : ∀ i, CommAlgCat.AlgebraSquare.{u, max u v, w} (A i) Ainf (B i) Binf)
/-- In every degree `n`, the maps of standard resolutions induced by the comparison squares
exhibit the degree-`n` term of the standard resolution of `Binf` over `Ainf` as the directed
colimit of the degree-`n` terms of the standard resolutions of the `B i` over the `A i`. -/
theorem CommAlgCat.standardResolutionSquareMap_isDirectedColimit
    (hA : IsDirectedColimitOfTypes (fun _ _ h a => (sq h).base a)
      (fun i a => (cocone i).base a))
    (hB : IsDirectedColimitOfTypes (fun _ _ h b => (sq h).map b)
      (fun i b => (cocone i).map b)) :
    ∀ n : ℕ, IsDirectedColimitOfTypes
      (fun _ _ h p => (CommAlgCat.squareFunctoriality.{u, max w v, u} (sq h)).resolution
        (op ⦋n⦌) p)
      (fun i p => (CommAlgCat.squareFunctoriality.{u, max u v, w} (cocone i)).resolution
        (op ⦋n⦌) p) := by
  intro n
  induction n with
  | zero =>
      let e : ∀ i, (CommAlgCat.standardResolution.{u, max w v} (A i) (B i)).left.obj
          (op ⦋0⦌) ≃ MvPolynomial (B i) (A i) :=
        fun i => CommAlgCat.standardResolutionZeroAlgEquiv.{u, max w v} (A i) (B i)
      let eInf : (CommAlgCat.standardResolution.{w, max u v} Ainf Binf).left.obj
          (op ⦋0⦌) ≃ MvPolynomial Binf Ainf :=
        CommAlgCat.standardResolutionZeroAlgEquiv.{w, max u v} Ainf Binf
      have hPoly := IsDirectedColimitOfTypes.mvPolynomial
        (fR := fun i j h => (sq h).base)
        (gR := fun i => (cocone i).base)
        (fX := fun i j h => (sq h).map)
        (gX := fun i => (cocone i).map) hA hB
      apply IsDirectedColimitOfTypes.of_equiv
        (f := fun i j h p => (CommAlgCat.squareFunctoriality.{u, max w v, u} (sq h)).resolution
          (op ⦋0⦌) p)
        (g := fun i p => (CommAlgCat.squareFunctoriality.{u, max u v, w} (cocone i)).resolution
          (op ⦋0⦌) p)
        (f' := fun i j h p => mvPolynomialSystemMap (fR := fun i j h => (sq h).base)
          (fX := fun i j h => (sq h).map) h p)
        (g' := fun i p => mvPolynomialSystemCocone (gR := fun i => (cocone i).base)
          (gX := fun i => (cocone i).map) i p)
        e eInf hPoly
      · intro i j h p
        refine apply_comp_equiv_symm (e i) (e j) _ _ (fun q => ?_) p
        exact DFunLike.congr_fun (CommAlgCat.standardResolutionZeroAlgEquiv_conj (sq h)) q
      · intro i p
        refine apply_comp_equiv_symm (e i) eInf _ _ (fun q => ?_) p
        exact DFunLike.congr_fun (CommAlgCat.standardResolutionZeroAlgEquiv_conj (cocone i)) q
  | succ n ih =>
      let e : ∀ i, (CommAlgCat.standardResolution.{u, max w v} (A i) (B i)).left.obj
          (op ⦋n + 1⦌) ≃ MvPolynomial
            ((CommAlgCat.standardResolution.{u, max w v} (A i) (B i)).left.obj (op ⦋n⦌)) (A i) :=
        fun i => CommAlgCat.standardResolutionSuccAlgEquiv.{u, max w v} (A i) (B i) n
      let eInf : (CommAlgCat.standardResolution.{w, max u v} Ainf Binf).left.obj
          (op ⦋n + 1⦌) ≃ MvPolynomial
            ((CommAlgCat.standardResolution.{w, max u v} Ainf Binf).left.obj (op ⦋n⦌)) Ainf :=
        CommAlgCat.standardResolutionSuccAlgEquiv.{w, max u v} Ainf Binf n
      have hPoly := IsDirectedColimitOfTypes.mvPolynomial
        (fR := fun i j h => (sq h).base)
        (gR := fun i => (cocone i).base)
        (fX := fun i j h =>
          (CommAlgCat.squareFunctoriality.{u, max w v, u} (sq h)).resolution (op ⦋n⦌))
        (gX := fun i =>
          (CommAlgCat.squareFunctoriality.{u, max u v, w} (cocone i)).resolution (op ⦋n⦌)) hA ih
      apply IsDirectedColimitOfTypes.of_equiv
        (f := fun i j h p => (CommAlgCat.squareFunctoriality.{u, max w v, u} (sq h)).resolution
          (op ⦋n + 1⦌) p)
        (g := fun i p => (CommAlgCat.squareFunctoriality.{u, max u v, w} (cocone i)).resolution
          (op ⦋n + 1⦌) p)
        (f' := fun i j h p => mvPolynomialSystemMap (fR := fun i j h => (sq h).base)
          (fX := fun i j h =>
            (CommAlgCat.squareFunctoriality.{u, max w v, u} (sq h)).resolution (op ⦋n⦌)) h p)
        (g' := fun i p => mvPolynomialSystemCocone (gR := fun i => (cocone i).base)
          (gX := fun i =>
            (CommAlgCat.squareFunctoriality.{u, max u v, w} (cocone i)).resolution (op ⦋n⦌)) i p)
        e eInf hPoly
      · intro i j h p
        refine apply_comp_equiv_symm (e i) (e j) _ _ (fun q => ?_) p
        exact DFunLike.congr_fun (CommAlgCat.standardResolutionSuccAlgEquiv_conj (sq h) n) q
      · intro i p
        refine apply_comp_equiv_symm (e i) eInf _ _ (fun q => ?_) p
        exact DFunLike.congr_fun (CommAlgCat.standardResolutionSuccAlgEquiv_conj (cocone i) n) q

/-! The cotangent module of a polynomial stage is free on its variables. -/

/-- The basis of `Ω[P⁄A]` indexed by `X`, for an `A`-algebra `P` identified with the polynomial
ring `MvPolynomial X A` by `E`. -/
noncomputable def KaehlerDifferential.basisOfMvPolynomialAlgEquiv
    {A : Type u} [CommRing A] {P : Type v} [CommRing P] [Algebra A P]
    {X : Type w} (E : P ≃ₐ[A] MvPolynomial X A) :
    Module.Basis X P (KaehlerDifferential A P) := by
  let Q := MvPolynomial X A
  letI : Algebra P Q := E.toRingHom.toAlgebra
  letI : IsScalarTower A P Q := IsScalarTower.of_algebraMap_eq fun a => (E.commutes a).symm
  letI : Algebra Q P := E.symm.toRingHom.toAlgebra
  letI : IsScalarTower A Q P := IsScalarTower.of_algebraMap_eq fun a => (E.symm.commutes a).symm
  let f := KaehlerDifferential.map A A P Q
  let g := KaehlerDifferential.map A A Q P
  let kE : KaehlerDifferential A P ≃ₗ[P] KaehlerDifferential A Q := by
    refine
      { toFun := f
        invFun := g
        left_inv := ?_
        right_inv := ?_
        map_add' := fun x y => f.map_add x y
        map_smul' := fun c x => f.map_smul c x }
    · intro x
      have hx : x ∈ Submodule.span P (Set.range (KaehlerDifferential.D A P)) := by
        rw [KaehlerDifferential.span_range_derivation]
        trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨p, rfl⟩
        simp only [f, g, KaehlerDifferential.map_D]
        change KaehlerDifferential.D A P (E.symm (E p)) = KaehlerDifferential.D A P p
        rw [E.symm_apply_apply]
      · simp [f, g]
      · intro x y _ _ hx hy
        simp [map_add, hx, hy]
      · intro c x _ hx
        rw [f.map_smul]
        change g (E c • f x) = c • x
        rw [g.map_smul, hx]
        change E.symm (E c) • x = c • x
        rw [E.symm_apply_apply]
    · intro x
      have hx : x ∈ Submodule.span Q (Set.range (KaehlerDifferential.D A Q)) := by
        rw [KaehlerDifferential.span_range_derivation]
        trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨q, rfl⟩
        simp only [f, g, KaehlerDifferential.map_D]
        change KaehlerDifferential.D A Q (E (E.symm q)) = KaehlerDifferential.D A Q q
        rw [E.apply_symm_apply]
      · simp [f, g]
      · intro x y _ _ hx hy
        simp [map_add, hx, hy]
      · intro c x _ hx
        rw [g.map_smul]
        change f (E.symm c • g x) = c • x
        rw [f.map_smul, hx]
        change E (E.symm c) • x = c • x
        rw [E.apply_symm_apply]
  let bQ := KaehlerDifferential.mvPolynomialBasis A X
  let bQ' : Module.Basis X P (KaehlerDifferential A Q) :=
    bQ.mapCoeffs E.symm.toRingEquiv (by
      intro c x
      change E (E.symm c) • x = c • x
      rw [E.apply_symm_apply])
  exact bQ'.map kE.symm

/-- The basis vector indexed by `x` is the differential of the element corresponding to the
variable `x`. -/
theorem KaehlerDifferential.basisOfMvPolynomialAlgEquiv_apply
    {A : Type u} [CommRing A] {P : Type v} [CommRing P] [Algebra A P]
    {X : Type w} (E : P ≃ₐ[A] MvPolynomial X A) (x : X) :
    KaehlerDifferential.basisOfMvPolynomialAlgEquiv E x =
      KaehlerDifferential.D A P (E.symm (MvPolynomial.X x)) := by
  let Q := MvPolynomial X A
  let : Algebra P Q := E.toRingHom.toAlgebra
  let : IsScalarTower A P Q := IsScalarTower.of_algebraMap_eq fun a => (E.commutes a).symm
  let : Algebra Q P := E.symm.toRingHom.toAlgebra
  let : IsScalarTower A Q P := IsScalarTower.of_algebraMap_eq fun a => (E.symm.commutes a).symm
  simp only [KaehlerDifferential.basisOfMvPolynomialAlgEquiv, Module.Basis.map_apply,
    Module.Basis.mapCoeffs_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  show KaehlerDifferential.map A A Q P
    (KaehlerDifferential.D A Q (MvPolynomial.X x)) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- The basis of the degree-zero term of the cotangent complex indexed by `B`, the variables of
the degree-zero term of the standard resolution. -/
noncomputable def CommAlgCat.cotangentTermBasisZero
    (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    Module.Basis B B (CommAlgCat.cotangentTerm.{u, v} A B (op ⦋0⦌)) := by
  let P := (CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋0⦌)
  let E := CommAlgCat.standardResolutionZeroAlgEquiv.{u, v} A B
  letI : Algebra P B := (CommAlgCat.standardResolutionAugmentationHom A B (op ⦋0⦌)).toAlgebra
  exact (KaehlerDifferential.basisOfMvPolynomialAlgEquiv (A := A) E).baseChange B

/-- The basis of the degree-`(n + 1)` term of the cotangent complex indexed by the degree-`n` term
of the standard resolution, the variables of its degree-`(n + 1)` term. -/
noncomputable def CommAlgCat.cotangentTermBasisSucc
    (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ) :
    Module.Basis ((CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋n⦌)) B
      (CommAlgCat.cotangentTerm.{u, v} A B (op ⦋n + 1⦌)) := by
  let P := (CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋n + 1⦌)
  let E := CommAlgCat.standardResolutionSuccAlgEquiv.{u, v} A B n
  letI : Algebra P B := (CommAlgCat.standardResolutionAugmentationHom A B (op ⦋n + 1⦌)).toAlgebra
  exact (KaehlerDifferential.basisOfMvPolynomialAlgEquiv (A := A) E).baseChange B

/-- The basis vector of the degree-zero term indexed by `b` is the differential of the variable
`b`. -/
theorem CommAlgCat.cotangentTermBasisZero_apply
    (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (b : B) :
    CommAlgCat.cotangentTermBasisZero.{u, v} A B b =
      CommAlgCat.cotangentTermDifferential.{u, v} A B (op ⦋0⦌)
        ((CommAlgCat.standardResolutionZeroAlgEquiv.{u, v} A B).symm
          (MvPolynomial.X b)) := by
  let P := (CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋0⦌)
  let E := CommAlgCat.standardResolutionZeroAlgEquiv.{u, v} A B
  let : Algebra P B := (CommAlgCat.standardResolutionAugmentationHom A B (op ⦋0⦌)).toAlgebra
  show (KaehlerDifferential.basisOfMvPolynomialAlgEquiv (A := A) E).baseChange B b = _
  rw [Module.Basis.baseChange_apply, KaehlerDifferential.basisOfMvPolynomialAlgEquiv_apply]
  rfl

/-- The basis vector of the degree-`(n + 1)` term indexed by `p` is the differential of the
variable `p`. -/
theorem CommAlgCat.cotangentTermBasisSucc_apply
    (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ)
    (p : (CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋n⦌)) :
    CommAlgCat.cotangentTermBasisSucc.{u, v} A B n p =
      CommAlgCat.cotangentTermDifferential.{u, v} A B (op ⦋n + 1⦌)
        (CommAlgCat.standardResolutionX.{u, v} A B n p) := by
  let P := (CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋n + 1⦌)
  let E := CommAlgCat.standardResolutionSuccAlgEquiv.{u, v} A B n
  let : Algebra P B := (CommAlgCat.standardResolutionAugmentationHom A B (op ⦋n + 1⦌)).toAlgebra
  show (KaehlerDifferential.basisOfMvPolynomialAlgEquiv (A := A) E).baseChange B p = _
  rw [Module.Basis.baseChange_apply, KaehlerDifferential.basisOfMvPolynomialAlgEquiv_apply]
  rfl

/-- The transition maps of the directed system of finitely supported functions induced by a
directed system of coefficient rings and a directed system of index types. -/
noncomputable def finsuppSystemMap
    {I : Type*} [Preorder I] {R : I → Type*} [∀ i, CommRing (R i)] {X : I → Type*}
    (fR : ∀ i j, i ≤ j → R i →+* R j)
    (fX : ∀ i j, i ≤ j → X i → X j) {i j : I} (h : i ≤ j) :
    (X i →₀ R i) →+ (X j →₀ R j) :=
  Finsupp.mapDomainMapRange (fR i j h) (fX i j h)

/-- The comparison maps from the stages of that system to the finitely supported functions on
the colimit of the index types with values in the colimit of the coefficient rings. -/
noncomputable def finsuppSystemCocone
    {I : Type*} {R : I → Type*} [∀ i, CommRing (R i)] {Rinf : Type*} [CommRing Rinf]
    {X : I → Type*} {Xinf : Type*}
    (gR : ∀ i, R i →+* Rinf) (gX : ∀ i, X i → Xinf) (i : I) :
    (X i →₀ R i) →+ (Xinf →₀ Rinf) :=
  Finsupp.mapDomainMapRange (gR i) (gX i)

/-- The transition maps send `single x c` to `single (fX i j h x) (fR i j h c)`. -/
theorem finsuppSystemMap_single
    {I : Type*} [Preorder I] {R : I → Type*} [∀ i, CommRing (R i)] {X : I → Type*}
    (fR : ∀ i j, i ≤ j → R i →+* R j) (fX : ∀ i j, i ≤ j → X i → X j)
    {i j : I} (h : i ≤ j) (x : X i) (c : R i) :
    finsuppSystemMap fR fX h (Finsupp.single x c) =
      Finsupp.single (fX i j h x) (fR i j h c) :=
  Finsupp.mapDomainMapRange_single _ _ x c

/-- The comparison maps send `single x c` to `single (gX i x) (gR i c)`. -/
theorem finsuppSystemCocone_single
    {I : Type*} {R : I → Type*} [∀ i, CommRing (R i)] {Rinf : Type*} [CommRing Rinf]
    {X : I → Type*} {Xinf : Type*}
    (gR : ∀ i, R i →+* Rinf) (gX : ∀ i, X i → Xinf) (i : I)
    (x : X i) (c : R i) :
    finsuppSystemCocone gR gX i (Finsupp.single x c) =
      Finsupp.single (gX i x) (gR i c) :=
  Finsupp.mapDomainMapRange_single _ _ x c

/-- The transition maps of the system of finitely supported functions compose. -/
theorem finsuppSystemMap_comp
    {I : Type*} [Preorder I] {R : I → Type*} [∀ i, CommRing (R i)] {Rinf : Type*}
    [CommRing Rinf] {X : I → Type*} {Xinf : Type*}
    (fR : ∀ i j, i ≤ j → R i →+* R j) (gR : ∀ i, R i →+* Rinf)
    (fX : ∀ i j, i ≤ j → X i → X j) (gX : ∀ i, X i → Xinf)
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i x => gR i x))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) (fun i x => gX i x))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (finsuppSystemMap fR fX hjk).comp (finsuppSystemMap fR fX hij) =
      finsuppSystemMap fR fX (hij.trans hjk) := by
  apply Finsupp.addHom_ext
  intro x c
  simp only [AddMonoidHom.comp_apply, finsuppSystemMap_single]
  rw [hR.map_comp, hX.map_comp]

/-- The comparison maps form a cocone over the system of finitely supported functions. -/
theorem finsuppSystemCocone_comp
    {I : Type*} [Preorder I] {R : I → Type*} [∀ i, CommRing (R i)]
    {Rinf : Type*} [CommRing Rinf] {X : I → Type*} {Xinf : Type*}
    (fR : ∀ i j, i ≤ j → R i →+* R j) (gR : ∀ i, R i →+* Rinf)
    (fX : ∀ i j, i ≤ j → X i → X j) (gX : ∀ i, X i → Xinf)
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i x => gR i x))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) (fun i x => gX i x))
    {i j : I} (hij : i ≤ j) :
    (finsuppSystemCocone gR gX j).comp (finsuppSystemMap fR fX hij) =
      finsuppSystemCocone gR gX i := by
  apply Finsupp.addHom_ext
  intro x c
  simp only [AddMonoidHom.comp_apply, finsuppSystemMap_single, finsuppSystemCocone_single]
  rw [hR.comp, hX.comp]

/-- Every finitely supported function on `Xinf` with values in `Rinf` comes from some stage of
the system. -/
theorem finsuppSystemCocone_jointly_surjective
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {R : I → Type*} [∀ i, CommRing (R i)] {Rinf : Type*} [CommRing Rinf]
    {X : I → Type*} {Xinf : Type*}
    (fR : ∀ i j, i ≤ j → R i →+* R j) (gR : ∀ i, R i →+* Rinf)
    (fX : ∀ i j, i ≤ j → X i → X j) (gX : ∀ i, X i → Xinf)
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i x => gR i x))
    (hX : IsDirectedColimitOfTypes (fun i j h => fX i j h) (fun i x => gX i x)) :
    ∀ p : Xinf →₀ Rinf, ∃ i q, finsuppSystemCocone gR gX i q = p := by
  classical
  intro p
  induction p using Finsupp.induction_linear with
  | zero =>
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨i, 0, by simp [finsuppSystemCocone]⟩
  | add p q hp hq =>
      obtain ⟨i, pi, hpi⟩ := hp
      obtain ⟨j, qj, hqj⟩ := hq
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, finsuppSystemMap fR fX hik pi + finsuppSystemMap fR fX hjk qj, ?_⟩
      rw [map_add]
      show ((finsuppSystemCocone gR gX k).comp (finsuppSystemMap fR fX hik)) pi +
        ((finsuppSystemCocone gR gX k).comp (finsuppSystemMap fR fX hjk)) qj = _
      rw [finsuppSystemCocone_comp fR gR fX gX hR hX hik,
        finsuppSystemCocone_comp fR gR fX gX hR hX hjk, hpi, hqj]
  | single x c =>
      obtain ⟨i, xi, hxi⟩ := hX.jointly_surjective x
      obtain ⟨j, cj, hcj⟩ := hR.jointly_surjective c
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, Finsupp.single (fX i k hik xi) (fR j k hjk cj), ?_⟩
      rw [finsuppSystemCocone_single, hX.comp i k hik xi, hR.comp j k hjk cj, hxi, hcj]

/-- The additive embedding of `X →₀ R` into `MvPolynomial X R` sending `single x c` to the
monomial `c • X x`. -/
noncomputable def mvPolynomialOfFinsupp {R X : Type*} [CommRing R] :
    (X →₀ R) →+ MvPolynomial X R where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.embDomain
    ⟨fun x => Finsupp.single x 1,
      Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0)⟩ p)
  map_zero' := by simp
  map_add' := by intro p q; simp only [Finsupp.embDomain_add, AddMonoidAlgebra.ofCoeff_add]

/-- The embedding sends `single x c` to the monomial of degree `single x 1` with coefficient
`c`. -/
theorem mvPolynomialOfFinsupp_single {R X : Type*} [CommRing R] (x : X) (c : R) :
    mvPolynomialOfFinsupp (Finsupp.single x c) = MvPolynomial.monomial (Finsupp.single x 1) c := by
  show AddMonoidAlgebra.ofCoeff (Finsupp.embDomain _ (Finsupp.single x c)) = _
  rw [Finsupp.embDomain_single]
  rfl

/-- The embedding of finitely supported functions into polynomials is injective. -/
theorem mvPolynomialOfFinsupp_injective {R X : Type*} [CommRing R] :
    Function.Injective (mvPolynomialOfFinsupp : (X →₀ R) → MvPolynomial X R) := by
  intro p q h
  exact Finsupp.embDomain_inj.mp (congrArg AddMonoidAlgebra.coeff h)

/-- The embedding intertwines the transition maps of the two systems. -/
theorem mvPolynomialOfFinsupp_systemMap
    {I : Type*} [Preorder I] {R : I → Type*} [∀ i, CommRing (R i)] {X : I → Type*}
    (fR : ∀ i j, i ≤ j → R i →+* R j) (fX : ∀ i j, i ≤ j → X i → X j)
    (i j : I) (h : i ≤ j) (p : X i →₀ R i) :
    mvPolynomialOfFinsupp (finsuppSystemMap fR fX h p) =
      mvPolynomialSystemMap fR fX h (mvPolynomialOfFinsupp p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single x c =>
      simp [finsuppSystemMap_single, mvPolynomialOfFinsupp_single, mvPolynomialSystemMap,
        CommAlgCat.mvPolynomialMapRename, MvPolynomial.rename_monomial, Finsupp.mapDomain_single]

/-- The embedding intertwines the comparison maps of the two systems. -/
theorem mvPolynomialOfFinsupp_systemCocone
    {I : Type*} {R : I → Type*} [∀ i, CommRing (R i)] {Rinf : Type*} [CommRing Rinf]
    {X : I → Type*} {Xinf : Type*}
    (gR : ∀ i, R i →+* Rinf) (gX : ∀ i, X i → Xinf) (i : I) (p : X i →₀ R i) :
    mvPolynomialOfFinsupp (finsuppSystemCocone gR gX i p) =
      mvPolynomialSystemCocone gR gX i (mvPolynomialOfFinsupp p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single x c =>
      simp [finsuppSystemCocone_single, mvPolynomialOfFinsupp_single, mvPolynomialSystemCocone,
        CommAlgCat.mvPolynomialMapRename, MvPolynomial.rename_monomial, Finsupp.mapDomain_single]

section FinsuppColimits

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable {R : I → Type*} [∀ i, CommRing (R i)] {Rinf : Type*} [CommRing Rinf]
variable {X : I → Type*} {Xinf : Type*}
variable (fR : ∀ i j : I, i ≤ j → R i →+* R j) (gR : ∀ i, R i →+* Rinf)
variable (fX : ∀ i j : I, i ≤ j → X i → X j) (gX : ∀ i, X i → Xinf)

/-- Finitely supported functions commute with directed colimits of coefficient rings and of
index types: the comparison maps exhibit `Xinf →₀ Rinf` as the directed colimit of the
`X i →₀ R i`. -/
theorem IsDirectedColimitOfTypes.finsupp
    (hR : IsDirectedColimitOfTypes (fun i j h => fR i j h) (fun i x => gR i x))
    (hX : IsDirectedColimitOfTypes fX gX) :
    IsDirectedColimitOfTypes (fun _ _ h p => finsuppSystemMap fR fX h p)
      (fun i p => finsuppSystemCocone gR gX i p) := by
  have hP := IsDirectedColimitOfTypes.mvPolynomial fR gR fX gX hR hX
  refine ⟨?_, ?_, ?_, finsuppSystemCocone_jointly_surjective fR gR fX gX hR hX, ?_⟩
  · intro i p
    apply mvPolynomialOfFinsupp_injective
    rw [mvPolynomialOfFinsupp_systemMap, hP.map_id]
  · intro i j k hij hjk p
    exact DFunLike.congr_fun (finsuppSystemMap_comp fR gR fX gX hR hX hij hjk) p
  · intro i j hij p
    exact DFunLike.congr_fun (finsuppSystemCocone_comp fR gR fX gX hR hX hij) p
  · intro i p q hpq
    have he : mvPolynomialSystemCocone gR gX i (mvPolynomialOfFinsupp p) =
        mvPolynomialSystemCocone gR gX i (mvPolynomialOfFinsupp q) := by
      rw [← mvPolynomialOfFinsupp_systemCocone, ← mvPolynomialOfFinsupp_systemCocone, hpq]
    obtain ⟨j, hij, h⟩ := hP.exists_eq i _ _ he
    refine ⟨j, hij, mvPolynomialOfFinsupp_injective ?_⟩
    simpa only [mvPolynomialOfFinsupp_systemMap] using h

end FinsuppColimits

/-- The variables of the degree-`n` term of the standard resolution of `B` over `A`: `B` in
degree zero and the degree-`n` term in degree `n + 1`. -/
noncomputable def CommAlgCat.standardResolutionVariables (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) : ℕ → Type (max u v)
  | 0 => B
  | n + 1 => (CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋n⦌)

/-- The map of variables of the standard resolutions induced by a commutative square of ring
maps: `s.map` in degree zero and the degree-`n` map of standard resolutions in degree `n + 1`. -/
noncomputable def CommAlgCat.standardResolutionVariableMap
    {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
    {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}
    (s : CommAlgCat.AlgebraSquare.{u, v, w} A A' B B') :
    (n : ℕ) → CommAlgCat.standardResolutionVariables.{u, max w v} A B n →
      CommAlgCat.standardResolutionVariables.{w, max u v} A' B' n
  | 0 => s.map
  | n + 1 => (CommAlgCat.squareFunctoriality s).resolution (op ⦋n⦌)

/-- The basis of the degree-`-n` term of the cotangent complex `L_{B⁄A}` over `B`, indexed by the
variables of the degree-`n` term of the standard resolution. -/
noncomputable def CommAlgCat.cotangentComplexBasis (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    Module.Basis (CommAlgCat.standardResolutionVariables.{u, v} A B n) B
      ((CommAlgCat.cotangentComplex.{u, v} A B).X (-(n : ℤ))) := by
  let b : Module.Basis (CommAlgCat.standardResolutionVariables.{u, v} A B n) B
      (CommAlgCat.cotangentTerm A B (op ⦋n⦌)) := match n with
    | 0 => CommAlgCat.cotangentTermBasisZero.{u, v} A B
    | k + 1 => CommAlgCat.cotangentTermBasisSucc.{u, v} A B k
  exact b.map (CategoryTheory.Iso.toLinearEquiv
    (CommAlgCat.cotangentComplex_degreeIso A B n).symm)

/-- In degree zero the basis is the transport of `CommAlgCat.cotangentTermBasisZero`. -/
theorem CommAlgCat.cotangentComplexBasis_zero_apply (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (x : B) :
    CommAlgCat.cotangentComplexBasis.{u, v} A B 0 x =
      (CategoryTheory.Iso.toLinearEquiv
        (CommAlgCat.cotangentComplex_degreeIso A B 0).symm)
        (CommAlgCat.cotangentTermBasisZero.{u, v} A B x) := by
  rfl

/-- In degree `-(n + 1)` the basis is the transport of `CommAlgCat.cotangentTermBasisSucc`. -/
theorem CommAlgCat.cotangentComplexBasis_succ_apply (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ)
    (x : (CommAlgCat.standardResolution.{u, v} A B).left.obj (op ⦋n⦌)) :
    CommAlgCat.cotangentComplexBasis.{u, v} A B (n + 1) x =
      (CategoryTheory.Iso.toLinearEquiv
        (CommAlgCat.cotangentComplex_degreeIso A B (n + 1)).symm)
        (CommAlgCat.cotangentTermBasisSucc.{u, v} A B n x) := by
  rfl

/-- The map of cotangent complexes induced by a square sends the basis vector indexed by `x` to
the basis vector indexed by the image of `x` under the map of variables. -/
theorem CommAlgCat.cotangentComplexBasis_map
    {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
    {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}
    (s : CommAlgCat.AlgebraSquare.{u, v, w} A A' B B') (n : ℕ)
    (x : CommAlgCat.standardResolutionVariables.{u, max w v} A B n) :
    (CommAlgCat.cotangentComplexAbMap s).f (-(n : ℤ))
        (CommAlgCat.cotangentComplexBasis.{u, max w v} A B n x) =
      CommAlgCat.cotangentComplexBasis.{w, max u v} A' B' n
        (CommAlgCat.standardResolutionVariableMap s n x) := by
  apply (CategoryTheory.Iso.toLinearEquiv
    (CommAlgCat.cotangentComplex_degreeIso A' B' n)).injective
  cases n with
  | zero =>
      change B at x
      show (CommAlgCat.cotangentComplex_degreeIso A' B' 0).toLinearEquiv
        ((CommAlgCat.cotangentComplexAbMap s).f 0 (CommAlgCat.cotangentComplexBasis A B 0 x)) =
        (CommAlgCat.cotangentComplex_degreeIso A' B' 0).toLinearEquiv
          (CommAlgCat.cotangentComplexBasis A' B' 0 (s.map x))
      rw [CommAlgCat.cotangentComplexBasis_zero_apply, CommAlgCat.cotangentComplexBasis_zero_apply]
      rw [CommAlgCat.cotangentTermBasisZero_apply, CommAlgCat.cotangentTermBasisZero_apply]
      show (CommAlgCat.cotangentComplex_degreeIso A' B' 0).hom
        ((CommAlgCat.squareFunctoriality s).complexMap.f 0
          ((CommAlgCat.cotangentComplex_degreeIso A B 0).inv
            (CommAlgCat.cotangentTermDifferential A B (op ⦋0⦌)
              ((CommAlgCat.standardResolutionZeroAlgEquiv A B).symm (MvPolynomial.X x))))) = _
      refine ((CommAlgCat.squareFunctoriality s).complexMap_differential 0 _).trans ?_
      rw [(CommAlgCat.squareFunctoriality s).resolution_zero_X]
      exact (CategoryTheory.Iso.toLinearEquiv
        (CommAlgCat.cotangentComplex_degreeIso A' B' 0)).apply_symm_apply _ |>.symm
  | succ n =>
      change (CommAlgCat.standardResolution.{u, max w v} A B).left.obj (op ⦋n⦌) at x
      show (CommAlgCat.cotangentComplex_degreeIso A' B' (n + 1)).toLinearEquiv
        ((CommAlgCat.cotangentComplexAbMap s).f (-(n + 1 : ℕ) : ℤ)
          (CommAlgCat.cotangentComplexBasis A B (n + 1) x)) =
        (CommAlgCat.cotangentComplex_degreeIso A' B' (n + 1)).toLinearEquiv
          (CommAlgCat.cotangentComplexBasis A' B' (n + 1)
            ((CommAlgCat.squareFunctoriality s).resolution (op ⦋n⦌) x))
      rw [CommAlgCat.cotangentComplexBasis_succ_apply, CommAlgCat.cotangentComplexBasis_succ_apply]
      rw [CommAlgCat.cotangentTermBasisSucc_apply, CommAlgCat.cotangentTermBasisSucc_apply]
      show (CommAlgCat.cotangentComplex_degreeIso A' B' (n + 1)).hom
        ((CommAlgCat.squareFunctoriality s).complexMap.f (-(n + 1 : ℕ) : ℤ)
          ((CommAlgCat.cotangentComplex_degreeIso A B (n + 1)).inv
            (CommAlgCat.cotangentTermDifferential A B (op ⦋n + 1⦌)
              (CommAlgCat.standardResolutionX A B n x)))) = _
      refine ((CommAlgCat.squareFunctoriality s).complexMap_differential (n + 1) _).trans ?_
      rw [(CommAlgCat.squareFunctoriality s).resolution_succ_X]
      exact (CategoryTheory.Iso.toLinearEquiv
        (CommAlgCat.cotangentComplex_degreeIso A' B' (n + 1))).apply_symm_apply _ |>.symm

/-- An additive map `f`, semilinear over `r`, sending each basis vector `b x` to the basis vector
`b' (g x)` acts on coordinates by mapping coefficients by `r` and renaming indices by `g`. -/
theorem Module.Basis.repr_map_eq
    {S T X Y M N : Type*} [CommRing S] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module T N]
    (b : Module.Basis X S M) (b' : Module.Basis Y T N)
    (r : S →+* T) (f : M →+ N) (g : X → Y)
    (hf : ∀ c m, f (c • m) = r c • f m)
    (hb : ∀ x, f (b x) = b' (g x)) (m : M) :
    b'.repr (f m) =
      Finsupp.mapDomainMapRange r g (b.repr m) := by
  obtain ⟨p, rfl⟩ := b.repr.symm.surjective m
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single x c =>
      simp [hf, hb, Module.Basis.repr_self]

/-- In the bases `CommAlgCat.cotangentComplexBasis`, the map of cotangent complexes induced by a
square acts on coordinates by mapping coefficients by `s.map` and renaming indices by the map of
variables. -/
theorem CommAlgCat.cotangentComplexBasis_repr_map
    {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
    {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}
    (s : CommAlgCat.AlgebraSquare.{u, v, w} A A' B B') (n : ℕ)
    (m : (CommAlgCat.cotangentComplexAb.{u, max w v} A B).X (-(n : ℤ))) :
    (CommAlgCat.cotangentComplexBasis.{w, max u v} A' B' n).repr
        ((CommAlgCat.cotangentComplexAbMap s).f (-(n : ℤ)) m) =
      Finsupp.mapDomainMapRange s.map (CommAlgCat.standardResolutionVariableMap s n)
        ((CommAlgCat.cotangentComplexBasis.{u, max w v} A B n).repr m) := by
  apply Module.Basis.repr_map_eq (CommAlgCat.cotangentComplexBasis.{u, max w v} A B n)
    (CommAlgCat.cotangentComplexBasis.{w, max u v} A' B' n) s.map
    ((CommAlgCat.squareFunctoriality s).complexMap.f (-(n : ℤ))).hom.toAddMonoidHom
    (CommAlgCat.standardResolutionVariableMap s n)
  · intro c x
    exact ((CommAlgCat.squareFunctoriality s).complexMap.f (-(n : ℤ))).hom.map_smul c x
  · exact CommAlgCat.cotangentComplexBasis_map s n


/-- Let `A i → B i` be a system of ring maps over a directed index set `I`, with `Ainf` the
colimit of the `A i` and `Binf` the colimit of the `B i`. Then in every degree the canonical
maps induced by the comparison squares exhibit `L_{Binf⁄Ainf}` as the directed colimit of the
cotangent complexes `L_{B i⁄A i}`, the transition maps of the system being those induced by
the squares of the system; that is, `colim L_{B i⁄A i} = L_{colim B i⁄colim A i}`. -/
@[stacks 08S9 "degreewise"]
theorem CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb
    (hA : IsDirectedColimitOfTypes (fun _ _ h a => (sq h).base a)
      (fun i a => (cocone i).base a))
    (hB : IsDirectedColimitOfTypes (fun _ _ h b => (sq h).map b)
      (fun i b => (cocone i).map b))
    (n : ℤ) :
    IsDirectedColimitOfTypes
      (fun _ _ h a => (CommAlgCat.cotangentComplexAbMap (sq h)).f n a)
      (fun i a => (CommAlgCat.cotangentComplexAbMap (cocone i)).f n a) :=
by
  classical
  by_cases hn : 0 < n
  · have hs (i : I) : Subsingleton ((CommAlgCat.cotangentComplexAb.{u, max w v} (A i) (B i)).X n) :=
      ModuleCat.subsingleton_of_isZero (CommAlgCat.cotangentComplex_isZero_pos _ _ n hn)
    have ht : Subsingleton ((CommAlgCat.cotangentComplexAb.{w, max u v} Ainf Binf).X n) :=
      ModuleCat.subsingleton_of_isZero (CommAlgCat.cotangentComplex_isZero_pos _ _ n hn)
    refine ⟨fun i _ => @Subsingleton.elim _ (hs i) _ _,
      fun _ _ k _ _ _ => @Subsingleton.elim _ (hs k) _ _,
      fun _ _ _ _ => @Subsingleton.elim _ ht _ _, ?_, ?_⟩
    · intro x
      exact ⟨Classical.choice ‹Nonempty I›, 0, @Subsingleton.elim _ ht _ _⟩
    · intro i x y h
      exact ⟨i, le_rfl, @Subsingleton.elim _ (hs i) _ _⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) :=
      ⟨(-n).toNat, by omega⟩
    have hX : IsDirectedColimitOfTypes
        (fun i j h => CommAlgCat.standardResolutionVariableMap (sq h) k)
        (fun i => CommAlgCat.standardResolutionVariableMap (cocone i) k) := by
      cases k with
      | zero => exact hB
      | succ k => exact CommAlgCat.standardResolutionSquareMap_isDirectedColimit sq cocone hA hB k
    have hF := IsDirectedColimitOfTypes.finsupp
      (fR := fun i j h => (sq h).map) (gR := fun i => (cocone i).map)
      (fX := fun i j h => CommAlgCat.standardResolutionVariableMap (sq h) k)
      (gX := fun i => CommAlgCat.standardResolutionVariableMap (cocone i) k) hB hX
    apply IsDirectedColimitOfTypes.of_equiv _ _ _ _
      (fun i => (CommAlgCat.cotangentComplexBasis.{u, max w v} (A i) (B i) k).repr.toEquiv)
      (CommAlgCat.cotangentComplexBasis.{w, max u v} Ainf Binf k).repr.toEquiv hF
    · intro i j h x
      exact CommAlgCat.cotangentComplexBasis_repr_map (sq h) k x
    · intro i x
      exact CommAlgCat.cotangentComplexBasis_repr_map (cocone i) k x

end System

/-- A cocone over a directed diagram of abelian groups whose legs exhibit its vertex as the
directed colimit of the underlying types is a colimit cocone. -/
noncomputable def AddCommGrpCat.isColimit_of_isDirectedColimitOfTypes
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ AddCommGrpCat.{v}) (c : Cocone F)
    (h : IsDirectedColimitOfTypes (F := fun i => F.obj i) (X := c.pt)
      (fun _ _ hij x => F.map (homOfLE hij) x)
      (fun i x => c.ι.app i x)) : IsColimit c := by
  classical
  let ht : IsColimit ((forget AddCommGrpCat).mapCocone c) :=
    Types.FilteredColimit.isColimitOf' _ _
      (fun x => by obtain ⟨i, y, hy⟩ := h.jointly_surjective x; exact ⟨i, y, hy.symm⟩)
      (fun i x y hxy => by
        obtain ⟨j, hij, he⟩ := h.exists_eq i x y hxy
        exact ⟨j, homOfLE hij, he⟩)
  let d (s : Cocone F) : c.pt → s.pt := ht.desc ((forget AddCommGrpCat).mapCocone s)
  have hd (s : Cocone F) (i : I) (x : F.obj i) : d s (c.ι.app i x) = s.ι.app i x :=
    ConcreteCategory.congr_hom (ht.fac ((forget AddCommGrpCat).mapCocone s) i) x
  let dm (s : Cocone F) : c.pt →+ s.pt := {
    toFun := d s
    map_zero' := by
      let i := Classical.choice ‹Nonempty I›
      have he := hd s i 0
      simpa only [map_zero] using he
    map_add' := by
      intro x y
      obtain ⟨i, a, rfl⟩ := h.jointly_surjective x
      obtain ⟨j, b, rfl⟩ := h.jointly_surjective y
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      rw [← h.comp i k hik a, ← h.comp j k hjk b, ← map_add, hd, hd, hd, map_add] }
  refine { desc := fun s => AddCommGrpCat.ofHom (dm s), fac := ?_, uniq := ?_ }
  · intro s i
    ext x
    exact hd s i x
  · intro s m hm
    ext x
    obtain ⟨i, a, rfl⟩ := h.jointly_surjective x
    exact (ConcreteCategory.congr_hom (hm i) a).trans (hd s i a).symm

/-! ### Equality of maps of complexes of abelian groups checked on elements -/

namespace CochainComplex

universe t

variable {K L M : CochainComplex AddCommGrpCat.{t} ℤ}

/-- A map of complexes of abelian groups which is the identity on elements in every degree is
the identity. -/
theorem hom_eq_id_of_apply (φ : K ⟶ K)
    (h : ∀ (n : ℤ) (x : K.X n), φ.f n x = x) : φ = 𝟙 K := by
  ext n x
  exact h n x

/-- A map of complexes of abelian groups which agrees elementwise in every degree with the
composite of two others is that composite. -/
theorem hom_eq_comp_of_apply (φ : K ⟶ L) (ψ : L ⟶ M) (χ : K ⟶ M)
    (h : ∀ (n : ℤ) (x : K.X n), χ.f n x = ψ.f n (φ.f n x)) : χ = φ ≫ ψ := by
  ext n x
  exact h n x

/-- The composite of two maps of complexes of abelian groups which agrees elementwise in every
degree with a third map is that map. -/
theorem comp_eq_hom_of_apply (φ : K ⟶ L) (ψ : L ⟶ M) (χ : K ⟶ M)
    (h : ∀ (n : ℤ) (x : K.X n), ψ.f n (φ.f n x) = χ.f n x) : φ ≫ ψ = χ := by
  ext n x
  exact h n x

end CochainComplex

/-! ### The system of cotangent complexes and its colimit

The system is formed for algebras in one module universe; the degreewise statement
`CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb` keeps the two base rings and the module
universe independent. -/

section Diagram

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {A : I → Type u} [∀ i, CommRing (A i)] {B : ∀ i, CommAlgCat.{u} (A i)}
  {Ainf : Type u} [CommRing Ainf] {Binf : CommAlgCat.{u} Ainf}
  (sq : ∀ ⦃i j : I⦄, i ≤ j → CommAlgCat.AlgebraSquare.{u, u, u} (A i) (A j) (B i) (B j))
  (cocone : ∀ i, CommAlgCat.AlgebraSquare.{u, u, u} (A i) Ainf (B i) Binf)
  (hA : IsDirectedColimitOfTypes (fun _ _ h a => (sq h).base a)
    (fun i a => (cocone i).base a))
  (hB : IsDirectedColimitOfTypes (fun _ _ h b => (sq h).map b)
    (fun i b => (cocone i).map b))

include sq cocone hA hB in
/-- The map induced by a square from a stage of the system to itself is the identity. -/
theorem CommAlgCat.cotangentComplexAbMap_eq_id (i : I) (h : i ≤ i) :
    CommAlgCat.cotangentComplexAbMap (sq h) =
      𝟙 (CommAlgCat.cotangentComplexAb.{u, u} (A i) (B i)) :=
  CochainComplex.hom_eq_id_of_apply _ (fun n x =>
    (CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb.{u, u, u, _} sq cocone hA hB
      n).map_id i x)

include sq cocone hA hB in
/-- The maps induced by the squares of the system compose. -/
theorem CommAlgCat.cotangentComplexAbMap_eq_comp (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
    (hik : i ≤ k) :
    CommAlgCat.cotangentComplexAbMap (sq hik) =
      CommAlgCat.cotangentComplexAbMap (sq hij) ≫ CommAlgCat.cotangentComplexAbMap (sq hjk) :=
  CochainComplex.hom_eq_comp_of_apply _ _ _ (fun n x =>
    ((CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb.{u, u, u, _} sq cocone hA hB
      n).map_comp
      i j k hij hjk x).symm)

include sq cocone hA hB in
/-- The maps induced by the comparison squares form a cocone over the system. -/
theorem CommAlgCat.cotangentComplexAbMap_comp_cocone (i j : I) (hij : i ≤ j) :
    CommAlgCat.cotangentComplexAbMap (sq hij) ≫ CommAlgCat.cotangentComplexAbMap (cocone j) =
      CommAlgCat.cotangentComplexAbMap (cocone i) :=
  CochainComplex.comp_eq_hom_of_apply _ _ _ (fun n x =>
    (CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb.{u, u, u, _} sq cocone hA hB
      n).comp i j hij x)

/-- The directed system of cotangent complexes of a system of squares of ring maps, read on
underlying abelian groups: the stage `i` is `L_{B i⁄A i}` and the transition map along `i ≤ j`
is the map induced by the square of the system. -/
noncomputable def CommAlgCat.cotangentComplexAbFunctor :
    I ⥤ CochainComplex AddCommGrpCat.{u} ℤ where
  obj i := CommAlgCat.cotangentComplexAb.{u, u} (A i) (B i)
  map h := CommAlgCat.cotangentComplexAbMap (sq (leOfHom h))
  map_id i := CommAlgCat.cotangentComplexAbMap_eq_id sq cocone hA hB i _
  map_comp f g :=
    CommAlgCat.cotangentComplexAbMap_eq_comp sq cocone hA hB _ _ _ (leOfHom f) (leOfHom g) _

/-- The system takes an index to the cotangent complex of that stage. -/
@[simp]
theorem CommAlgCat.cotangentComplexAbFunctor_obj (i : I) :
    (CommAlgCat.cotangentComplexAbFunctor sq cocone hA hB).obj i =
      CommAlgCat.cotangentComplexAb.{u, u} (A i) (B i) := rfl

/-- The system takes a morphism of the index preorder to the map induced by the corresponding
square. -/
@[simp]
theorem CommAlgCat.cotangentComplexAbFunctor_map {i j : I} (h : i ⟶ j) :
    (CommAlgCat.cotangentComplexAbFunctor sq cocone hA hB).map h =
      CommAlgCat.cotangentComplexAbMap (sq (leOfHom h)) := rfl

/-- The cocone on the system whose legs are the maps induced by the comparison squares, with
vertex the cotangent complex of the colimit. -/
noncomputable def CommAlgCat.cotangentComplexAbCocone :
    Cocone (CommAlgCat.cotangentComplexAbFunctor sq cocone hA hB) where
  pt := CommAlgCat.cotangentComplexAb.{u, u} Ainf Binf
  ι :=
    { app := fun i => CommAlgCat.cotangentComplexAbMap (cocone i)
      naturality := fun i j f =>
        (CommAlgCat.cotangentComplexAbMap_comp_cocone sq cocone hA hB i j (leOfHom f)).trans
          (Category.comp_id _).symm }

/-- The vertex of the cocone is the cotangent complex of the colimit. -/
@[simp]
theorem CommAlgCat.cotangentComplexAbCocone_pt :
    (CommAlgCat.cotangentComplexAbCocone sq cocone hA hB).pt =
      CommAlgCat.cotangentComplexAb.{u, u} Ainf Binf := rfl

/-- The leg of the cocone at an index is the map induced by the comparison square there. -/
@[simp]
theorem CommAlgCat.cotangentComplexAbCocone_ι_app (i : I) :
    (CommAlgCat.cotangentComplexAbCocone sq cocone hA hB).ι.app i =
      CommAlgCat.cotangentComplexAbMap (cocone i) := rfl

/-- Cotangent complexes commute with directed colimits of ring maps: the cocone of canonical
maps `L_{B i⁄A i} → L_{Binf⁄Ainf}` on the system of canonical maps `L_{B i⁄A i} → L_{B j⁄A j}`
is a colimit cocone. -/
@[stacks 08S9 "the colimit of complexes"]
noncomputable def CommAlgCat.isColimit_cotangentComplexAbCocone :
    IsColimit (CommAlgCat.cotangentComplexAbCocone sq cocone hA hB) := by
  refine HomologicalComplex.isColimitOfEval _ _ (fun n => ?_)
  apply AddCommGrpCat.isColimit_of_isDirectedColimitOfTypes
  exact CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb.{u, u, u, _} sq cocone hA hB n

end Diagram

end
