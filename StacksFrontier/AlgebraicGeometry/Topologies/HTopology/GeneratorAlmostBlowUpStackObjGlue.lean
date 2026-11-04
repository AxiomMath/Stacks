module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackMorSheaf

/-!
# Solutions of a descent problem over an object of the slice

Fix an object `U` of the big h category over `S`, a family `f i : V i ⟶ U` and a descent datum `D`
relative to it, in Mathlib's sense for the pullback pseudofunctor of a fibred category
`p : 𝒳 ⥤ (Sch/S)_h`.  A *solution of `D` over* a morphism `F : W ⟶ U` of the site is an object of
the fibre over `W` together with an identification of its chosen pullbacks with those of the
objects of `D`, over every object mapping compatibly into `W` and into some `V i`, compatible with
the gluing isomorphisms of `D` and with base change:
`AlgebraicGeometry.BigHOver.DescentSolution`.

This is the object-level analogue of `AlgebraicGeometry.BigHOver.MorAgree`, and it is the property
of an object `W ⟶ U` of the slice `(Sch/S)_h / U` that
`AlgebraicGeometry.BigHOver.of_localOnGenerators` is run on in order to prove condition (3) of
Stacks 026F — the second of the two auxiliary presheaves of the proof of Stacks 0EX9, the presheaf
of isomorphism classes of pairs `(y, ψ i)`.

Unlike `MorAgree`, a solution is *data*, so it is not subterminal on the nose; what replaces
subterminality is that two solutions pulled back to a common object are compared by a unique
morphism: `AlgebraicGeometry.BigHOver.DescentSolution.IsCmp` is the property of being such a
comparison, `AlgebraicGeometry.BigHOver.DescentSolution.IsCmp.eq` its uniqueness and
`AlgebraicGeometry.BigHOver.DescentSolution.exists_isCmp` its existence.  Both consume conditions
(1), (2) and (3) of Stacks 0EX9, and only through
`AlgebraicGeometry.BigHOver.eq_of_pullbackFiberHom_eq_of_covering` and
`AlgebraicGeometry.BigHOver.existsUnique_fiberHom_of_covering` — which is where descent of
morphisms, the companion half of the criterion, is consumed.

## Main definitions

* `AlgebraicGeometry.BigHOver.descentObj` and `AlgebraicGeometry.BigHOver.descentIso`: the objects
  and the gluing isomorphisms of a descent datum for the pullback pseudofunctor, read in the fibres
  of `p` and between the chosen pullbacks of `p`.
* `AlgebraicGeometry.BigHOver.DescentSolution`: a solution of `D` over `F : W ⟶ U`.
* `AlgebraicGeometry.BigHOver.DescentSolution.baseChange`: **base change of a solution.**  This is
  the transfer of effectivity along a morphism of the base, which is the monotonicity hypothesis of
  `AlgebraicGeometry.BigHOver.of_localOnGenerators` for the property that a solution exists.
* `AlgebraicGeometry.BigHOver.DescentSolution.IsCmp`: the property of a morphism between the chosen
  pullbacks of the objects of two solutions to a common object of being compatible with their
  identifications.

## Main results

* `AlgebraicGeometry.BigHOver.descentSolutionOfObj`: the objects of `D` are solutions of `D` over
  the members of the family, which is the hypothesis that a solution exists on one h covering
  family of `U`.
* `AlgebraicGeometry.BigHOver.DescentSolution.IsCmp.eq`: **a comparison of two solutions is
  unique.**  The canonical fibre products `V i ×_U T` form an h covering of `T` and the comparison
  is prescribed over each of them, so
  `AlgebraicGeometry.BigHOver.eq_of_pullbackFiberHom_eq_of_covering` identifies two of them.
* `AlgebraicGeometry.BigHOver.DescentSolution.exists_isCmp`: **a comparison of two solutions
  exists.**  Over each canonical fibre product the two identifications prescribe one; these are
  compatible because both solutions are compatible with the gluing isomorphisms of `D`, and
  `AlgebraicGeometry.BigHOver.existsUnique_fiberHom_of_covering` amalgamates them.
* `AlgebraicGeometry.BigHOver.DescentSolution.existsUnique_isCmp`: the two together.

## Implementation notes

**Why the identifications are indexed by arbitrary objects.**  A solution could be asked to carry
its identifications only over the canonical fibre products `V i ×_U W`; the identification over an
arbitrary `Z` mapping to `W` and to `V i` is then the base change along
`CategoryTheory.Limits.pullback.lift` of the one over `V i ×_U W`.  The two presentations carry the
same information, and that is exactly how
`AlgebraicGeometry.BigHOver.DescentSolution.exists_isCmp` works: the comparison is produced from
the canonical fibre products alone and then propagated to an arbitrary `Z` by that base change.
The arbitrary-`Z` presentation is the one stored, because the compatibility with the gluing
isomorphisms of `D` has to be stated over arbitrary objects in any case.

**Named composites.**  Every morphism to `U` that a composite is asked to equal is a named
argument, in the style of `CategoryTheory.Functor.baseChangeFiberMor` and
`AlgebraicGeometry.BigHOver.MorAgree`, so that no equality of morphisms of the site is ever
transported.  This is what makes `AlgebraicGeometry.BigHOver.DescentSolution.IsCmp` evaluate, at
the identity of the common object, to the comparison itself rather than to a conjugate of it by a
contraction isomorphism: `CategoryTheory.Functor.baseChangeFiberMor_id` applies on the nose.

**The two spellings of an object of the datum.**  For the pullback pseudofunctor the pullback
functors *are* the chosen-pullback functors, so an object of the datum is an object of a fibre of
`p` and `CategoryTheory.Pseudofunctor.DescentData.iso` already is an isomorphism of chosen
pullbacks.  The identification is by `rfl` but not by `rfl` at the transparency at which `rw`
checks that its motive is type-correct, so it is confined to
`AlgebraicGeometry.BigHOver.descentObj` and `AlgebraicGeometry.BigHOver.descentIso`, whose *types*
are the chosen-pullback ones; downstream no `rw` ever has to see the pseudofunctor spelling.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]

/-! ### Three bookkeeping facts about base change along a named composite -/

/-- Base change of an identity along a named composite is an identity. -/
public theorem baseChangeFiberMor_id_self {Ux Vx W : BigHOver B S hS} {x : p.Fiber Ux}
    {fx : Vx ⟶ Ux} (g : W ⟶ Vx) (mx : W ⟶ Ux) (hmx hmx' : g ≫ fx = mx) :
    Functor.baseChangeFiberMor (𝟙 (Functor.pullbackFiber p x fx)) g mx hmx mx hmx' = 𝟙 _ := by
  obtain rfl : hmx = hmx' := rfl
  rw [Functor.baseChangeFiberMor, Functor.pullbackFiberHom_id, Category.id_comp, Iso.inv_hom_id]

/-- Two morphisms between chosen pullbacks along *different* morphisms with equal base changes
along a named composite have equal base changes in the `pullbackFiberHom` sense.  This is
`CategoryTheory.Functor.pullbackFiberHom_eq_of_baseChangeFiberMor_eq` without the hypothesis that
the two chosen pullbacks are taken along one and the same morphism. -/
public theorem pullbackFiberHom_eq_of_baseChangeFiberMor_eq' {Ux Uy Vx W : BigHOver B S hS}
    {x : p.Fiber Ux} {y : p.Fiber Uy} {fx : Vx ⟶ Ux} {fy : Vx ⟶ Uy}
    (m m' : Functor.pullbackFiber p x fx ⟶ Functor.pullbackFiber p y fy) (g : W ⟶ Vx)
    {mx : W ⟶ Ux} (hmx : g ≫ fx = mx) {my : W ⟶ Uy} (hmy : g ≫ fy = my)
    (h : Functor.baseChangeFiberMor m g mx hmx my hmy =
      Functor.baseChangeFiberMor m' g mx hmx my hmy) :
    Functor.pullbackFiberHom m g = Functor.pullbackFiberHom m' g := by
  rw [Functor.baseChangeFiberMor, Functor.baseChangeFiberMor, cancel_epi, cancel_mono] at h
  exact h

/-- Base changing the inverse of a contraction of an iterated chosen pullback is again such an
inverse: the inverse form of
`CategoryTheory.Functor.baseChangeFiberMor_pullbackFiberCompIso'`. -/
public theorem baseChangeFiberMor_pullbackFiberCompIso'_inv {T Vx Z Z' : BigHOver B S hS}
    (z : p.Fiber T) (fa : Vx ⟶ T) (ε : Z ⟶ Vx) (n : Z ⟶ T) (hn : ε ≫ fa = n) (γ : Z' ⟶ Z)
    (mm : Z' ⟶ Vx) (hm : γ ≫ ε = mm) (c : Z' ⟶ T) (hc : mm ≫ fa = c) (hγn : γ ≫ n = c) :
    Functor.baseChangeFiberMor (Functor.pullbackFiberCompIso' z fa ε n hn).inv γ c hγn mm hm =
      (Functor.pullbackFiberCompIso' z fa mm c hc).inv := by
  rw [← Functor.baseChangeFiberIso_inv (Functor.pullbackFiberCompIso' z fa ε n hn) γ mm hm c hγn,
    Functor.baseChangeFiberIso_pullbackFiberCompIso' z fa ε n hn γ mm hm c hc hγn]

/-- **Base change of a morphism conjugated by two contractions of iterated chosen pullbacks.**  A
morphism between the chosen pullbacks of `x` and `y` along two named composites `Fx' = gx ≫ Fx` and
`Fy' = gy ≫ Fy` can be read, by conjugating with the contraction isomorphisms, as a morphism
between the chosen pullbacks along `gx` and `gy` of the chosen pullbacks along `Fx` and `Fy`.  Its
base change along a further morphism is the same reading of its base change.

This is `CategoryTheory.Functor.baseChangeFiberMor_conj` with the two chosen pullbacks allowed to
be taken along different morphisms of different objects, which is the generality the comparison of
two solutions over different objects of the slice needs. -/
public theorem baseChangeFiberMor_conj' {Ux Uy Vx Vy W Z : BigHOver B S hS} {x : p.Fiber Ux}
    {y : p.Fiber Uy} {Fx : Vx ⟶ Ux} {Fy : Vy ⟶ Uy} {gx : W ⟶ Vx} {gy : W ⟶ Vy} {Fx' : W ⟶ Ux}
    (hx : gx ≫ Fx = Fx') {Fy' : W ⟶ Uy} (hy : gy ≫ Fy = Fy')
    (m : Functor.pullbackFiber p x Fx' ⟶ Functor.pullbackFiber p y Fy') {ε : Z ⟶ W}
    {qx : Z ⟶ Vx} (hqx : ε ≫ gx = qx) {qy : Z ⟶ Vy} (hqy : ε ≫ gy = qy) {rx : Z ⟶ Ux}
    (hrx : qx ≫ Fx = rx) (hrx' : ε ≫ Fx' = rx) {ry : Z ⟶ Uy} (hry : qy ≫ Fy = ry)
    (hry' : ε ≫ Fy' = ry) :
    Functor.baseChangeFiberMor
        ((Functor.pullbackFiberCompIso' x Fx gx Fx' hx).hom ≫ m ≫
          (Functor.pullbackFiberCompIso' y Fy gy Fy' hy).inv) ε qx hqx qy hqy =
      (Functor.pullbackFiberCompIso' x Fx qx rx hrx).hom ≫
        Functor.baseChangeFiberMor m ε rx hrx' ry hry' ≫
          (Functor.pullbackFiberCompIso' y Fy qy ry hry).inv := by
  rw [Functor.baseChangeFiberMor_comp _ _ ε qx hqx rx hrx' qy hqy,
    Functor.baseChangeFiberMor_comp _ _ ε rx hrx' ry hry' qy hqy,
    Functor.baseChangeFiberMor_pullbackFiberCompIso' x Fx gx Fx' hx ε qx hqx rx hrx hrx',
    baseChangeFiberMor_pullbackFiberCompIso'_inv y Fy gy Fy' hy ε qy hqy ry hry hry']

/-! ### The objects and the gluing isomorphisms of a descent datum -/

variable {U : BigHOver B S hS} {I : Type (u + 1)} {V : I → BigHOver B S hS} {f : ∀ i, V i ⟶ U}

/-- **The object of a descent datum for the pullback pseudofunctor at a member of the family, read
as an object of the fibre.**  For the pullback pseudofunctor the value at an object of the site
*is* the fibre category, so this is the object itself; naming it confines the coincidence of the
two spellings to one declaration whose *type* is the fibre spelling. -/
public def descentObj (D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f) (i : I) :
    p.Fiber (V i) :=
  D.obj i

/-- **The gluing isomorphism of a descent datum for the pullback pseudofunctor, read between the
chosen pullbacks of `p`.**  For two members of the family and two morphisms into their sources
agreeing over a named morphism `q` to `U`, the canonical isomorphism between the chosen pullbacks
of the two attached objects.

The pullback functors of the pullback pseudofunctor *are* the chosen-pullback functors, so this is
`CategoryTheory.Pseudofunctor.DescentData.iso` with no translation. -/
public def descentIso (D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f) (i j : I)
    ⦃Z : BigHOver B S hS⦄ (ε : Z ⟶ V i) (ε' : Z ⟶ V j) (q : Z ⟶ U) (h : ε ≫ f i = q)
    (h' : ε' ≫ f j = q) :
    Functor.pullbackFiber p (descentObj D i) ε ≅ Functor.pullbackFiber p (descentObj D j) ε' :=
  D.iso q ε ε' h h'

variable {D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f}

/-- The gluing isomorphism of a member of the family with itself along one and the same morphism is
the identity: `CategoryTheory.Pseudofunctor.DescentData.hom_self`. -/
public theorem descentIso_self (i : I) ⦃Z : BigHOver B S hS⦄ (ε : Z ⟶ V i) (q : Z ⟶ U)
    (h : ε ≫ f i = q) : (descentIso D i i ε ε q h h).hom = 𝟙 _ :=
  D.hom_self q ε h

/-- The gluing isomorphisms of a descent datum compose: the cocycle condition
`CategoryTheory.Pseudofunctor.DescentData.hom_comp`. -/
public theorem descentIso_trans (i j k : I) ⦃Z : BigHOver B S hS⦄ (ε : Z ⟶ V i) (ε' : Z ⟶ V j)
    (ε'' : Z ⟶ V k) (q : Z ⟶ U) (h : ε ≫ f i = q) (h' : ε' ≫ f j = q) (h'' : ε'' ≫ f k = q) :
    (descentIso D i j ε ε' q h h').hom ≫ (descentIso D j k ε' ε'' q h' h'').hom =
      (descentIso D i k ε ε'' q h h'').hom :=
  D.hom_comp q ε ε' ε'' h h' h''

/-- The inverse of a gluing isomorphism is the gluing isomorphism of the two members in the other
order. -/
public theorem descentIso_symm (i j : I) ⦃Z : BigHOver B S hS⦄ (ε : Z ⟶ V i) (ε' : Z ⟶ V j)
    (q : Z ⟶ U) (h : ε ≫ f i = q) (h' : ε' ≫ f j = q) :
    (descentIso D i j ε ε' q h h').inv = (descentIso D j i ε' ε q h' h).hom := rfl

/-- **The gluing isomorphisms of a descent datum are compatible with base change**, which is
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` read through
`CategoryTheory.Functor.pullHom_eq`: Mathlib's pullback of a morphism between two chosen pullbacks
is base change along a named composite. -/
public theorem descentIso_baseChange (i j : I) ⦃Z Z' : BigHOver B S hS⦄ (ε : Z ⟶ V i)
    (ε' : Z ⟶ V j) (q : Z ⟶ U) (h : ε ≫ f i = q) (h' : ε' ≫ f j = q) (γ : Z' ⟶ Z)
    (ζ : Z' ⟶ V i) (hζ : γ ≫ ε = ζ) (ζ' : Z' ⟶ V j) (hζ' : γ ≫ ε' = ζ') (q' : Z' ⟶ U)
    (hq : ζ ≫ f i = q') (hq' : ζ' ≫ f j = q') :
    Functor.baseChangeFiberMor (descentIso D i j ε ε' q h h').hom γ ζ hζ ζ' hζ' =
      (descentIso D i j ζ ζ' q' hq hq').hom := by
  subst hζ
  subst hζ'
  obtain rfl : q' = γ ≫ q := by rw [← hq, ← h, Category.assoc]
  exact (Functor.pullHom_eq p (D.obj i) (D.obj j) ε ε' γ (D.hom q ε ε' h h')).symm.trans
    (D.pullHom_hom γ q (γ ≫ q) rfl ε ε' h h' (γ ≫ ε) (γ ≫ ε') rfl rfl)

/-! ### Solutions -/

/-- **A solution of the descent problem `D` over a morphism `F : W ⟶ U` of the site**: an object of
the fibre over `W`, together with an identification of its chosen pullback along any morphism to
`W` with the chosen pullback of the object of `D` at any member of the family along any morphism to
that member agreeing over `U`, compatibly with the gluing isomorphisms of `D` and with base
change.

This is the object-level analogue of `AlgebraicGeometry.BigHOver.MorAgree`; it is *data*, and what
replaces the subterminality of `MorAgree` is that two solutions are compared by a unique morphism,
`AlgebraicGeometry.BigHOver.DescentSolution.IsCmp`. -/
public structure DescentSolution
    (D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f)
    {W : BigHOver B S hS} (F : W ⟶ U) where
  /-- The object of the fibre over `W` the solution descends to. -/
  obj : p.Fiber W
  /-- The identification with the objects of `D`. -/
  iso : ∀ (i : I) ⦃Z : BigHOver B S hS⦄ (δ : Z ⟶ W) (ε : Z ⟶ V i) (q : Z ⟶ U)
    (_h : δ ≫ F = q) (_h' : ε ≫ f i = q),
    Functor.pullbackFiber p obj δ ≅ Functor.pullbackFiber p (descentObj D i) ε
  /-- Compatibility of the identifications with the gluing isomorphisms of `D`. -/
  compat : ∀ (i j : I) ⦃Z : BigHOver B S hS⦄ (δ : Z ⟶ W) (ε : Z ⟶ V i) (ε' : Z ⟶ V j)
    (q : Z ⟶ U) (h : δ ≫ F = q) (h' : ε ≫ f i = q) (h'' : ε' ≫ f j = q),
    (iso i δ ε q h h').hom ≫ (descentIso D i j ε ε' q h' h'').hom = (iso j δ ε' q h h'').hom
  /-- Compatibility of the identifications with base change. -/
  iso_baseChange : ∀ (i : I) ⦃Z Z' : BigHOver B S hS⦄ (δ : Z ⟶ W) (ε : Z ⟶ V i) (q : Z ⟶ U)
    (h : δ ≫ F = q) (h' : ε ≫ f i = q) (γ : Z' ⟶ Z) (δ' : Z' ⟶ W) (hδ' : γ ≫ δ = δ')
    (ε' : Z' ⟶ V i) (hε' : γ ≫ ε = ε') (q' : Z' ⟶ U) (hq : δ' ≫ F = q') (hq' : ε' ≫ f i = q'),
    Functor.baseChangeFiberMor (iso i δ ε q h h').hom γ δ' hδ' ε' hε' =
      (iso i δ' ε' q' hq hq').hom

namespace DescentSolution

/-- **The inverse identifications of a solution are compatible with base change.**  Base change
along a named composite is compatible with composition and takes identities to identities, so it
takes the inverse of an identification to the inverse of the base-changed identification. -/
public theorem iso_baseChange_inv {W : BigHOver B S hS} {F : W ⟶ U} (s : DescentSolution D F)
    (i : I) ⦃Z Z' : BigHOver B S hS⦄ (δ : Z ⟶ W) (ε : Z ⟶ V i) (q : Z ⟶ U)
    (h : δ ≫ F = q) (h' : ε ≫ f i = q) (γ : Z' ⟶ Z) (δ' : Z' ⟶ W) (hδ' : γ ≫ δ = δ')
    (ε' : Z' ⟶ V i) (hε' : γ ≫ ε = ε') (q' : Z' ⟶ U) (hq : δ' ≫ F = q') (hq' : ε' ≫ f i = q') :
    Functor.baseChangeFiberMor (s.iso i δ ε q h h').inv γ ε' hε' δ' hδ' =
      (s.iso i δ' ε' q' hq hq').inv := by
  have hfwd : Functor.baseChangeFiberMor (s.iso i δ ε q h h').hom γ δ' hδ' ε' hε' =
      (s.iso i δ' ε' q' hq hq').hom :=
    s.iso_baseChange i δ ε q h h' γ δ' hδ' ε' hε' q' hq hq'
  have hcomp : Functor.baseChangeFiberMor
        ((s.iso i δ ε q h h').hom ≫ (s.iso i δ ε q h h').inv) γ δ' hδ' δ' hδ' =
      Functor.baseChangeFiberMor (s.iso i δ ε q h h').hom γ δ' hδ' ε' hε' ≫
        Functor.baseChangeFiberMor (s.iso i δ ε q h h').inv γ ε' hε' δ' hδ' :=
    Functor.baseChangeFiberMor_comp _ _ γ δ' hδ' ε' hε' δ' hδ'
  have hid : Functor.baseChangeFiberMor
      ((s.iso i δ ε q h h').hom ≫ (s.iso i δ ε q h h').inv) γ δ' hδ' δ' hδ' = 𝟙 _ :=
    (congrArg (fun ξ ↦ Functor.baseChangeFiberMor ξ γ δ' hδ' δ' hδ')
      (s.iso i δ ε q h h').hom_inv_id).trans (baseChangeFiberMor_id_self γ δ' hδ' hδ')
  have hkey : (s.iso i δ' ε' q' hq hq').hom ≫
      Functor.baseChangeFiberMor (s.iso i δ ε q h h').inv γ ε' hε' δ' hδ' = 𝟙 _ :=
    (congrArg (fun ξ ↦ ξ ≫ Functor.baseChangeFiberMor (s.iso i δ ε q h h').inv γ ε' hε' δ' hδ')
      hfwd).symm.trans (hcomp.symm.trans hid)
  exact (cancel_epi (s.iso i δ' ε' q' hq hq').hom).mp
    (hkey.trans (s.iso i δ' ε' q' hq hq').hom_inv_id.symm)

/-- **Base change of a solution.**  A solution of `D` over `F : W ⟶ U` base changes, along a
morphism `γ : W' ⟶ W` and over a named composite, to a solution of `D` over `W' ⟶ U`.

Its object is the chosen pullback along `γ` of the object of the given solution, and its
identifications are those of the given solution preceded by the contraction
`CategoryTheory.Functor.pullbackFiberCompIso'` of the iterated chosen pullback.  This is the
transfer of effectivity along a morphism of the base. -/
public def baseChange {W W' : BigHOver B S hS} {F : W ⟶ U} (s : DescentSolution D F)
    (γ : W' ⟶ W) (F' : W' ⟶ U) (hF' : γ ≫ F = F') : DescentSolution D F' where
  obj := Functor.pullbackFiber p s.obj γ
  iso i _Z δ ε q h h' :=
    Functor.pullbackFiberCompIso' s.obj γ δ (δ ≫ γ) rfl ≪≫
      s.iso i (δ ≫ γ) ε q (by rw [Category.assoc, hF', h]) h'
  compat i j _Z δ ε ε' q h h' h'' := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [s.compat i j (δ ≫ γ) ε ε' q (by rw [Category.assoc, hF', h]) h' h'']
  iso_baseChange i _Z _Z' δ ε q h h' γ' δ' hδ' ε' hε' q' hq hq' := by
    have hmid : γ' ≫ δ ≫ γ = δ' ≫ γ := by rw [← hδ', Category.assoc]
    simp only [Iso.trans_hom]
    rw [Functor.baseChangeFiberMor_comp _ _ γ' δ' hδ' (δ' ≫ γ) hmid ε' hε',
      Functor.baseChangeFiberMor_pullbackFiberCompIso' s.obj γ δ (δ ≫ γ) rfl γ' δ' hδ'
        (δ' ≫ γ) rfl hmid,
      s.iso_baseChange i (δ ≫ γ) ε q (by rw [Category.assoc, hF', h]) h' γ' (δ' ≫ γ) hmid
        ε' hε' q' (by rw [Category.assoc, hF', hq]) hq']

/-- The object of a base-changed solution is the chosen pullback of the object along `γ`. -/
@[simp]
public theorem baseChange_obj {W W' : BigHOver B S hS} {F : W ⟶ U} (s : DescentSolution D F)
    (γ : W' ⟶ W) (F' : W' ⟶ U) (hF' : γ ≫ F = F') :
    (s.baseChange γ F' hF').obj = Functor.pullbackFiber p s.obj γ := rfl

/-- The identifications of a base-changed solution, with the iterated chosen pullback contracted
over a named composite. -/
public theorem baseChange_iso_hom {W W' : BigHOver B S hS} {F : W ⟶ U} (s : DescentSolution D F)
    (γ : W' ⟶ W) (F' : W' ⟶ U) (hF' : γ ≫ F = F') (i : I) ⦃Z : BigHOver B S hS⦄ (δ : Z ⟶ W')
    (ε : Z ⟶ V i) (q : Z ⟶ U) (h : δ ≫ F' = q) (h' : ε ≫ f i = q) (r : Z ⟶ W)
    (hr : δ ≫ γ = r) (hrq : r ≫ F = q) :
    ((s.baseChange γ F' hF').iso i δ ε q h h').hom =
      (Functor.pullbackFiberCompIso' s.obj γ δ r hr).hom ≫ (s.iso i r ε q hrq h').hom := by
  subst hr
  rfl

end DescentSolution

/-- **The objects of a descent datum are solutions over the members of the family.**  At the member
`i₀` the object attached to it is a solution over `f i₀`, its identifications being the gluing
isomorphisms of the datum themselves. -/
public def descentSolutionOfObj (D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f)
    (i₀ : I) : DescentSolution D (f i₀) where
  obj := descentObj D i₀
  iso i _Z δ ε q h h' := descentIso D i₀ i δ ε q h h'
  compat i j _Z δ ε ε' q h h' h'' := descentIso_trans i₀ i j δ ε ε' q h h' h''
  iso_baseChange i _Z _Z' δ ε q h h' γ δ' hδ' ε' hε' q' hq hq' :=
    descentIso_baseChange i₀ i δ ε q h h' γ δ' hδ' ε' hε' q' hq hq'

namespace DescentSolution

/-! ### Comparison of two solutions -/

/-- **The property of comparing two solutions.**  Let `s` and `s'` be solutions of `D` over
`F₀ : W₀ ⟶ U` and `F₁ : W₁ ⟶ U`, and let `γ₀ : T ⟶ W₀` and `γ₁ : T ⟶ W₁` be morphisms from a common
object.  A morphism `m` between the chosen pullbacks of the two objects *compares* the two
solutions when, over every object mapping to `T` and to some `V i` compatibly over `U`, the base
change of `m` carries the identification of `s'` to that of `s`.

At the identity of `T` the condition reads `m ≫ (s'.iso i γ₁ ε _).hom = (s.iso i γ₀ ε _).hom`,
because base change along an identity over the named composites `γ₀` and `γ₁` is the identity
operation, `CategoryTheory.Functor.baseChangeFiberMor_id`. -/
public def IsCmp {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    (s : DescentSolution D F₀) (γ₀ : T ⟶ W₀) (s' : DescentSolution D F₁) (γ₁ : T ⟶ W₁)
    (m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁) : Prop :=
  ∀ (i : I) ⦃Z : BigHOver B S hS⦄ (δ : Z ⟶ T) (ε : Z ⟶ V i) (q : Z ⟶ U)
    (δ₀ : Z ⟶ W₀) (hδ₀ : δ ≫ γ₀ = δ₀) (h₀ : δ₀ ≫ F₀ = q)
    (δ₁ : Z ⟶ W₁) (hδ₁ : δ ≫ γ₁ = δ₁) (h₁ : δ₁ ≫ F₁ = q) (h : ε ≫ f i = q),
    Functor.baseChangeFiberMor m δ δ₀ hδ₀ δ₁ hδ₁ ≫ (s'.iso i δ₁ ε q h₁ h).hom =
      (s.iso i δ₀ ε q h₀ h).hom

/-- A comparison, read at the identity of the common object. -/
public theorem IsCmp.fac {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    {s : DescentSolution D F₀} {γ₀ : T ⟶ W₀} {s' : DescentSolution D F₁} {γ₁ : T ⟶ W₁}
    {m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁}
    (hm : IsCmp s γ₀ s' γ₁ m) (i : I) (ε : T ⟶ V i) (q : T ⟶ U) (h₀ : γ₀ ≫ F₀ = q)
    (h₁ : γ₁ ≫ F₁ = q) (h : ε ≫ f i = q) :
    m ≫ (s'.iso i γ₁ ε q h₁ h).hom = (s.iso i γ₀ ε q h₀ h).hom := by
  have key := hm i (𝟙 T) ε q γ₀ (Category.id_comp γ₀) h₀ γ₁ (Category.id_comp γ₁) h₁ h
  rwa [Functor.baseChangeFiberMor_id] at key

/-- The identity compares a solution with itself. -/
public theorem isCmp_id {T W₀ : BigHOver B S hS} {F₀ : W₀ ⟶ U} (s : DescentSolution D F₀)
    (γ₀ : T ⟶ W₀) : IsCmp s γ₀ s γ₀ (𝟙 _) := by
  intro i Z δ ε q δ₀ hδ₀ h₀ δ₀' hδ₀' h₀' h
  obtain rfl : δ₀ = δ₀' := hδ₀.symm.trans hδ₀'
  rw [baseChangeFiberMor_id_self, Category.id_comp]

/-- A composite of comparisons is a comparison. -/
public theorem IsCmp.comp {T W₀ W₁ W₂ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    {F₂ : W₂ ⟶ U} {F' : T ⟶ U} {s : DescentSolution D F₀} {γ₀ : T ⟶ W₀}
    (hγ₀ : γ₀ ≫ F₀ = F') {s' : DescentSolution D F₁} {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F')
    {s'' : DescentSolution D F₂} {γ₂ : T ⟶ W₂}
    {m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁}
    {m' : Functor.pullbackFiber p s'.obj γ₁ ⟶ Functor.pullbackFiber p s''.obj γ₂}
    (hm : IsCmp s γ₀ s' γ₁ m) (hm' : IsCmp s' γ₁ s'' γ₂ m') : IsCmp s γ₀ s'' γ₂ (m ≫ m') := by
  intro i Z δ ε q δ₀ hδ₀ h₀ δ₂ hδ₂ h₂ h
  have hq : δ ≫ F' = q := by
    rw [← hγ₀, ← Category.assoc, hδ₀]; exact h₀
  have hmid : (δ ≫ γ₁) ≫ F₁ = q := by
    rw [Category.assoc, hγ₁]; exact hq
  rw [Functor.baseChangeFiberMor_comp m m' δ δ₀ hδ₀ (δ ≫ γ₁) rfl δ₂ hδ₂, Category.assoc,
    hm' i δ ε q (δ ≫ γ₁) rfl hmid δ₂ hδ₂ h₂ h, hm i δ ε q δ₀ hδ₀ h₀ (δ ≫ γ₁) rfl hmid h]

/-- A base change of a comparison is a comparison. -/
public theorem IsCmp.baseChange {T T' W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    {s : DescentSolution D F₀} {γ₀ : T ⟶ W₀} {s' : DescentSolution D F₁} {γ₁ : T ⟶ W₁}
    {m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁}
    (hm : IsCmp s γ₀ s' γ₁ m) (γ : T' ⟶ T) (δ₀ : T' ⟶ W₀) (hδ₀ : γ ≫ γ₀ = δ₀)
    (δ₁ : T' ⟶ W₁) (hδ₁ : γ ≫ γ₁ = δ₁) :
    IsCmp s δ₀ s' δ₁ (Functor.baseChangeFiberMor m γ δ₀ hδ₀ δ₁ hδ₁) := by
  intro i Z δ ε q d₀ hd₀ h₀ d₁ hd₁ h₁ h
  rw [Functor.baseChangeFiberMor_baseChangeFiberMor m γ δ₀ hδ₀ δ₁ hδ₁ δ d₀ hd₀ d₁ hd₁]
  exact hm i (δ ≫ γ) ε q d₀ (by rw [Category.assoc, hδ₀, hd₀]) h₀ d₁
    (by rw [Category.assoc, hδ₁, hd₁]) h₁ h

/-- A morphism from the canonical fibre product `X ×_Y T` to `T`, composed with a morphism
`γ : T ⟶ W` over `Y`, is a morphism to `W` over `Y` through the first projection. -/
private theorem pullback_snd_comp_comp_comp {X Y T W : BigHOver B S hS} (g : X ⟶ Y) (F' : T ⟶ Y)
    (γ : T ⟶ W) (F : W ⟶ Y) (hγ : γ ≫ F = F') :
    (Limits.pullback.snd g F' ≫ γ) ≫ F = Limits.pullback.fst g F' ≫ g := by
  rw [Category.assoc, hγ, ← Limits.pullback.condition]

/-- A morphism into the canonical fibre product `X ×_Y T` over `q : Z ⟶ T` has first projection
over `Y` equal to `q ≫ F'`. -/
private theorem pullback_fst_comp_comp {X Y T Z : BigHOver B S hS} (g : X ⟶ Y) (F' : T ⟶ Y)
    (ε : Z ⟶ Limits.pullback g F') (q : Z ⟶ T) (hq : ε ≫ Limits.pullback.snd g F' = q) :
    (ε ≫ Limits.pullback.fst g F') ≫ g = q ≫ F' := by
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hq]

/-- **A comparison of two solutions is unique.**  The canonical fibre products `V i ×_U T` form an
h covering of `T`, and over each of them a comparison is prescribed by the two identifications, so
`AlgebraicGeometry.BigHOver.eq_of_pullbackFiberHom_eq_of_covering` identifies two comparisons. -/
public theorem IsCmp.eq
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U} {F' : T ⟶ U}
    {s : DescentSolution D F₀} {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    {s' : DescentSolution D F₁} {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F')
    {m m' : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁}
    (hm : IsCmp s γ₀ s' γ₁ m) (hm' : IsCmp s γ₀ s' γ₁ m') : m = m' := by
  refine eq_of_pullbackFiberHom_eq_of_covering h1 h2 h3 h4 m m'
    (fun i ↦ Limits.pullback.snd (f i) F') (sieve_ofArrows_pullback_mem_topology hf F') fun i ↦ ?_
  have h₀ := pullback_snd_comp_comp_comp (f i) F' γ₀ F₀ hγ₀
  have h₁ := pullback_snd_comp_comp_comp (f i) F' γ₁ F₁ hγ₁
  refine pullbackFiberHom_eq_of_baseChangeFiberMor_eq' m m' (Limits.pullback.snd (f i) F')
    (mx := Limits.pullback.snd (f i) F' ≫ γ₀) rfl
    (my := Limits.pullback.snd (f i) F' ≫ γ₁) rfl ?_
  have e1 := hm i (Limits.pullback.snd (f i) F') (Limits.pullback.fst (f i) F')
    (Limits.pullback.fst (f i) F' ≫ f i) _ rfl h₀ _ rfl h₁ rfl
  have e2 := hm' i (Limits.pullback.snd (f i) F') (Limits.pullback.fst (f i) F')
    (Limits.pullback.fst (f i) F' ≫ f i) _ rfl h₀ _ rfl h₁ rfl
  exact ((Iso.eq_comp_inv _).mpr e1).trans ((Iso.eq_comp_inv _).mpr e2).symm

/-- **A comparison of two solutions exists.**  Over each canonical fibre product `V i ×_U T` the
two identifications prescribe a comparison; these are compatible over any further object because
both solutions are compatible with the gluing isomorphisms of `D`, so
`AlgebraicGeometry.BigHOver.existsUnique_fiberHom_of_covering` amalgamates them into a morphism
over `T`, which is a comparison over an arbitrary object because the two morphisms into `T` and
into `V i` factor through `V i ×_U T` by `CategoryTheory.Limits.pullback.lift` and both solutions
are compatible with base change. -/
public theorem exists_isCmp
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U} {F' : T ⟶ U}
    (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    (s' : DescentSolution D F₁) {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F') :
    ∃ m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁,
      IsCmp s γ₀ s' γ₁ m := by
  classical
  have h₀ := fun i ↦ pullback_snd_comp_comp_comp (f i) F' γ₀ F₀ hγ₀
  have h₁ := fun i ↦ pullback_snd_comp_comp_comp (f i) F' γ₁ F₁ hγ₁
  -- the local comparison over the canonical fibre product `V i ×_U T`
  let χ : ∀ i, Functor.pullbackFiber p s.obj (Limits.pullback.snd (f i) F' ≫ γ₀) ⟶
      Functor.pullbackFiber p s'.obj (Limits.pullback.snd (f i) F' ≫ γ₁) := fun i ↦
    (s.iso i _ (Limits.pullback.fst (f i) F') _ (h₀ i) rfl).hom ≫
      (s'.iso i _ (Limits.pullback.fst (f i) F') _ (h₁ i) rfl).inv
  -- the same, read between the iterated chosen pullbacks
  let ψ : ∀ i, Functor.pullbackFiber p (Functor.pullbackFiber p s.obj γ₀)
        (Limits.pullback.snd (f i) F') ⟶
      Functor.pullbackFiber p (Functor.pullbackFiber p s'.obj γ₁)
        (Limits.pullback.snd (f i) F') := fun i ↦
    (Functor.pullbackFiberCompIso' s.obj γ₀ (Limits.pullback.snd (f i) F') _ rfl).hom ≫
      χ i ≫ (Functor.pullbackFiberCompIso' s'.obj γ₁ (Limits.pullback.snd (f i) F') _ rfl).inv
  -- the base change of a local comparison to an arbitrary further object
  have key : ∀ (k : I) (Z : BigHOver B S hS) (ζ : Z ⟶ Limits.pullback (f k) F') (q : Z ⟶ T)
      (hζ : ζ ≫ Limits.pullback.snd (f k) F' = q)
      (hζk : (ζ ≫ Limits.pullback.fst (f k) F') ≫ f k = q ≫ F')
      (hq0 : (q ≫ γ₀) ≫ F₀ = q ≫ F') (hq1 : (q ≫ γ₁) ≫ F₁ = q ≫ F'),
      Functor.baseChangeFiberMor (ψ k) ζ q hζ q hζ =
        (Functor.pullbackFiberCompIso' s.obj γ₀ q (q ≫ γ₀) rfl).hom ≫
          ((s.iso k (q ≫ γ₀) (ζ ≫ Limits.pullback.fst (f k) F') (q ≫ F') hq0 hζk).hom ≫
            (s'.iso k (q ≫ γ₁) (ζ ≫ Limits.pullback.fst (f k) F') (q ≫ F') hq1 hζk).inv) ≫
          (Functor.pullbackFiberCompIso' s'.obj γ₁ q (q ≫ γ₁) rfl).inv := by
    intro k Z ζ q hζ hζk hq0 hq1
    have hmid₀ : ζ ≫ Limits.pullback.snd (f k) F' ≫ γ₀ = q ≫ γ₀ := by
      rw [← Category.assoc, hζ]
    have hmid₁ : ζ ≫ Limits.pullback.snd (f k) F' ≫ γ₁ = q ≫ γ₁ := by
      rw [← Category.assoc, hζ]
    rw [show ψ k = (Functor.pullbackFiberCompIso' s.obj γ₀ (Limits.pullback.snd (f k) F')
        _ rfl).hom ≫ χ k ≫
        (Functor.pullbackFiberCompIso' s'.obj γ₁ (Limits.pullback.snd (f k) F') _ rfl).inv from rfl,
      baseChangeFiberMor_conj' rfl rfl (χ k) hζ hζ rfl hmid₀ rfl hmid₁,
      show χ k = (s.iso k _ (Limits.pullback.fst (f k) F') _ (h₀ k) rfl).hom ≫
        (s'.iso k _ (Limits.pullback.fst (f k) F') _ (h₁ k) rfl).inv from rfl,
      Functor.baseChangeFiberMor_comp _ _ ζ (q ≫ γ₀) hmid₀
        (ζ ≫ Limits.pullback.fst (f k) F') rfl (q ≫ γ₁) hmid₁,
      s.iso_baseChange k _ (Limits.pullback.fst (f k) F') _ (h₀ k) rfl ζ (q ≫ γ₀) hmid₀
        (ζ ≫ Limits.pullback.fst (f k) F') rfl (q ≫ F') hq0 hζk,
      s'.iso_baseChange_inv k _ (Limits.pullback.fst (f k) F') _ (h₁ k) rfl ζ (q ≫ γ₁) hmid₁
        (ζ ≫ Limits.pullback.fst (f k) F') rfl (q ≫ F') hq1 hζk]
  -- the compatibility of the local comparisons, from the compatibility of both solutions with the
  -- gluing isomorphisms of `D`
  have hcompat : ∀ (i j : I) (Z : BigHOver B S hS) (ε : Z ⟶ Limits.pullback (f i) F')
      (ε' : Z ⟶ Limits.pullback (f j) F') (q : Z ⟶ T)
      (hq : ε ≫ Limits.pullback.snd (f i) F' = q)
      (hq' : ε' ≫ Limits.pullback.snd (f j) F' = q),
      Functor.baseChangeFiberMor (ψ i) ε q hq q hq =
        Functor.baseChangeFiberMor (ψ j) ε' q hq' q hq' := by
    intro i j Z ε ε' q hq hq'
    have hqi := pullback_fst_comp_comp (f i) F' ε q hq
    have hqj := pullback_fst_comp_comp (f j) F' ε' q hq'
    have hq0 : (q ≫ γ₀) ≫ F₀ = q ≫ F' := by rw [Category.assoc, hγ₀]
    have hq1 : (q ≫ γ₁) ≫ F₁ = q ≫ F' := by rw [Category.assoc, hγ₁]
    rw [key i Z ε q hq hqi hq0 hq1, key j Z ε' q hq' hqj hq0 hq1]
    congr 2
    have hs := s.compat i j (q ≫ γ₀) (ε ≫ Limits.pullback.fst (f i) F')
      (ε' ≫ Limits.pullback.fst (f j) F') (q ≫ F') hq0 hqi hqj
    have hs' := s'.compat i j (q ≫ γ₁) (ε ≫ Limits.pullback.fst (f i) F')
      (ε' ≫ Limits.pullback.fst (f j) F') (q ≫ F') hq1 hqi hqj
    have hinv := congrArg (fun e : Functor.pullbackFiber p s'.obj (q ≫ γ₁) ≅
        Functor.pullbackFiber p (descentObj D j) (ε' ≫ Limits.pullback.fst (f j) F') ↦ e.inv)
      (Iso.ext hs'.symm :
        s'.iso j (q ≫ γ₁) (ε' ≫ Limits.pullback.fst (f j) F') (q ≫ F') hq1 hqj =
          s'.iso i (q ≫ γ₁) (ε ≫ Limits.pullback.fst (f i) F') (q ≫ F') hq1 hqi ≪≫
            descentIso D i j (ε ≫ Limits.pullback.fst (f i) F')
              (ε' ≫ Limits.pullback.fst (f j) F') (q ≫ F') hqi hqj)
    rw [← hs, hinv, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]
  obtain ⟨m, hmψ, -⟩ := existsUnique_fiberHom_of_covering h1 h2 h3 h4
    (sieve_ofArrows_pullback_mem_topology hf F') (ψ := ψ)
    (fun i j Z ε ε' q hqi hqj ↦ hcompat i j Z ε ε' q hqi hqj)
  -- the comparison property at the canonical fibre products
  have hweak : ∀ i, Functor.baseChangeFiberMor m (Limits.pullback.snd (f i) F') _ rfl _ rfl =
      χ i := by
    intro i
    rw [Functor.baseChangeFiberMor, hmψ i,
      show ψ i = (Functor.pullbackFiberCompIso' s.obj γ₀ (Limits.pullback.snd (f i) F')
        _ rfl).hom ≫ χ i ≫
        (Functor.pullbackFiberCompIso' s'.obj γ₁ (Limits.pullback.snd (f i) F') _ rfl).inv from rfl,
      ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  refine ⟨m, fun i Z δ ε q δ₀ hδ₀ h₀' δ₁ hδ₁ h₁' h ↦ ?_⟩
  -- the pair `(ε, δ)` factors through the canonical fibre product `V i ×_U T`
  have hfac : ε ≫ f i = δ ≫ F' := by rw [h, ← h₀', ← hδ₀, Category.assoc, hγ₀]
  have httf : Limits.pullback.lift ε δ hfac ≫ Limits.pullback.fst (f i) F' = ε :=
    Limits.pullback.lift_fst _ _ _
  have htts : Limits.pullback.lift ε δ hfac ≫ Limits.pullback.snd (f i) F' = δ :=
    Limits.pullback.lift_snd _ _ _
  have hmid₀ : Limits.pullback.lift ε δ hfac ≫ Limits.pullback.snd (f i) F' ≫ γ₀ = δ₀ := by
    rw [← Category.assoc, htts, hδ₀]
  have hmid₁ : Limits.pullback.lift ε δ hfac ≫ Limits.pullback.snd (f i) F' ≫ γ₁ = δ₁ := by
    rw [← Category.assoc, htts, hδ₁]
  have hstep := congrArg
    (fun ξ ↦ Functor.baseChangeFiberMor ξ (Limits.pullback.lift ε δ hfac) δ₀ hmid₀ δ₁ hmid₁)
    (hweak i)
  rw [Functor.baseChangeFiberMor_baseChangeFiberMor m (Limits.pullback.snd (f i) F') _ rfl _ rfl
      (Limits.pullback.lift ε δ hfac) δ₀ hmid₀ δ₁ hmid₁,
    show χ i = (s.iso i _ (Limits.pullback.fst (f i) F') _ (h₀ i) rfl).hom ≫
      (s'.iso i _ (Limits.pullback.fst (f i) F') _ (h₁ i) rfl).inv from rfl,
    Functor.baseChangeFiberMor_comp _ _ (Limits.pullback.lift ε δ hfac) δ₀ hmid₀ ε httf δ₁ hmid₁,
    s.iso_baseChange i _ (Limits.pullback.fst (f i) F') _ (h₀ i) rfl
      (Limits.pullback.lift ε δ hfac) δ₀ hmid₀ ε httf q h₀' h,
    s'.iso_baseChange_inv i _ (Limits.pullback.fst (f i) F') _ (h₁ i) rfl
      (Limits.pullback.lift ε δ hfac) δ₁ hmid₁ ε httf q h₁' h] at hstep
  rw [Functor.baseChangeFiberMor_congr m htts.symm hδ₀ hmid₀ hδ₁ hmid₁, hstep, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- A comparison of two solutions exists and is unique. -/
public theorem existsUnique_isCmp
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U} {F' : T ⟶ U}
    (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    (s' : DescentSolution D F₁) {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F') :
    ∃! m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁,
      IsCmp s γ₀ s' γ₁ m := by
  obtain ⟨m, hm⟩ := exists_isCmp h1 h2 h3 h4 hf s hγ₀ s' hγ₁
  exact ⟨m, hm, fun m' hm' ↦ IsCmp.eq h1 h2 h3 h4 hf hγ₀ hγ₁ hm' hm⟩

end DescentSolution

end BigHOver

end AlgebraicGeometry

end
