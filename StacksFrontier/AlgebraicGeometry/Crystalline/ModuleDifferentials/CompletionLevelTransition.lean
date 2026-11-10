module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelSpan
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope
public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# The transition maps of the two shapes of the differentials of a completion, modulo `pᵏ`

Let `f : B ⟶ C` be a divided power morphism of divided power rings over `A`, with `p` nilpotent
modulo both divided power ideals, and write `B̂`, `Ĉ` for the `p`-adic completions.  Both shapes
of the differentials of the completion that
`Crystalline.completedDifferentialsLevelEquiv` of `ModuleDifferentials/CompletionLevel.lean`
compares — the universal `Ω_{B̂/A,γ̂}` and the completion `Ω̂_{B/A,δ}` — carry a transition map
along `f`, modulo `pᵏ` and semilinear over the completed ring map `B̂ → Ĉ`.  This file writes
those two maps down and computes them on the classes that
`Crystalline.span_completedDifferentialsModPow_mk_d_of` says span.

## Why no new mathematics is needed

Both maps are assembled from pieces that are already in the library, which is why they are
definitions here and not a development:

* the completed ring map `B̂ → Ĉ` is `Crystalline.adicCompletionRingMap` of
  `Cosimplicial/Envelope.lean`, and it is a divided power morphism of the completed divided
  powers by `Crystalline.adicCompletionRingMap_isDPMorphism` there;
* the universal differentials are functorial in a divided power morphism by
  `Crystalline.mapDifferentialsOfDPMorphismₛₗ` of `ModuleDifferentials/Functoriality.lean`;
* the completion of a module is functorial in a semilinear map by
  `Crystalline.adicCompletionMapₛₗ` of `Cosimplicial/CompletedForms.lean`, and the result is
  semilinear over the *completed* ring map by `Crystalline.adicCompletionMapₛₗ_smul`;
* and a semilinear map carrying one adic ideal into the other descends to the quotients by
  `Crystalline.adicQuotientMap`.

The only thing to do is to choose the spelling of the scalars once, in a definition, rather than
inside a proof: `Crystalline.completionDifferentialsMapₛₗ` is the retyping of
`Crystalline.adicCompletionMapₛₗ` from semilinearity over `B → C` to semilinearity over
`B̂ → Ĉ`, which is what the quotient by the ideal of `B̂` consumes.

## Main definitions

* `Crystalline.completedRingHom` and `Crystalline.completedAlgHom` — the `p`-adic completion of
  `f`, as a ring map `B̂ → Ĉ` and as an `A`-algebra map.
* `Crystalline.completedDifferentialsModPowMap` — the transition map
  `Ω_{B̂/A,γ̂} / pᵏ ⟶ Ω_{Ĉ/A,ε̂} / pᵏ`, semilinear over `B̂ → Ĉ`.
* `Crystalline.completionDifferentialsMapₛₗ` and
  `Crystalline.completionDifferentialsModPowMap` — the transition map
  `Ω̂_{B/A,δ} ⟶ Ω̂_{C/A,ε}` and its reduction `Ω̂_{B/A,δ} / pᵏ ⟶ Ω̂_{C/A,ε} / pᵏ`, both semilinear
  over `B̂ → Ĉ`.

## Main results

* `Crystalline.isDPMorphism_completedAlgHom` — the completion of a divided power morphism is a
  divided power morphism of the completed divided powers, read on
  `Crystalline.completedAlgHom`.
* `Crystalline.completedDifferentialsModPowMap_mk_d` and
  `Crystalline.completionDifferentialsModPowMap_mk_of_d` — the two transition maps on the classes
  of differentials.
* `Crystalline.completionDifferentialsModPowMap_completedDifferentialsLevelEquiv_mk_d` and
  `Crystalline.completedDifferentialsLevelEquiv_completedDifferentialsModPowMap_mk_d` — **the two
  routes round the naturality square of the level identification of [Stacks, Tag 07KK], computed
  on the spanning classes.**  Both are the class of the image of `d (f b)`, so the square
  commutes on generators; with
  `Crystalline.completedDifferentialsModPow_ext_addMonoidHom` of
  `ModuleDifferentials/CompletionLevelSpan.lean` that is the square itself, for any consumer
  whose two comparisons sit at a common level.

## What is and is not proved

**No tag attribute is placed, and [Stacks, Tag 07LF] is not proved here.**  What is removed is
the obstruction recorded in the "What `ε` owes" note of
`SmallSite/TensorRestrictionVanishing.lean`, which said that these two transition maps "are not
in the library at all, so the naturality square cannot be written down".  They are written down
here, and the two sides of the square are computed on the classes that span.

The square itself is not stated as a single equation of maps *here*, because the level
identification `Crystalline.completedDifferentialsLevelEquiv` is indexed by
`cmp.quotientSystem.cutoff + e` and two comparisons for two different rings carry two such
indices; an equation between the two composites is therefore, at this spelling, a statement
about types that are equal only propositionally.  The two generator computations below are
index-free in exactly that respect: they are two equations with the *same* right-hand side, so a
consumer at a common level gets the square from them without transporting anything.  That
consumer exists: `ModuleDifferentials/CompletionLevelReindex.lean` re-indexes the level
identification by a bare `k` carrying a proof — `Crystalline.completedDifferentialsLevelEquivAt`
— and `Crystalline.completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt`
there **is** the square as a single equation of additive maps, proved from the two computations
below.

Nothing is assumed beyond the divided power morphism `f` and the two nilpotence hypotheses; no
flatness, no finiteness, and no hypothesis relating the two
`Crystalline.DifferentialsCompletionComparison`s.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

universe u v w

namespace Crystalline

section Transition

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable (J : Ideal B) (delta : DividedPowers J) (L : Ideal C) (epsilon : DividedPowers L)
variable (p : ℕ)
variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))
variable (hq : IsNilpotent (Ideal.Quotient.mk L (p : C)))
variable (f : B →ₐ[A] C)

/-! ### The completion of the ring map -/

/-- **The `p`-adic completion of a ring map**, `B̂ → Ĉ`.  This is
`Crystalline.adicCompletionRingMap` fed with the fact that a ring map carries the `p`-adic ideal
into the `p`-adic ideal. -/
public noncomputable def completedRingHom :
    AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B →+*
      AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C :=
  adicCompletionRingMap f.toRingHom (map_pAdicIdeal_le p f.toRingHom)

/-- The completed ring map on the image of `B`. -/
@[simp]
public theorem completedRingHom_of (b : B) :
    completedRingHom p f (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b) =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) C (f b) :=
  adicCompletionRingMap_of _ _ b

/-- **The `p`-adic completion of an `A`-algebra map**, `B̂ → Ĉ`.  The completions are
`A`-algebras through `B` and `C`, so the commutation with the structure maps is
`Crystalline.completedRingHom_of` applied to `algebraMap A B a`. -/
public noncomputable def completedAlgHom :
    AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B →ₐ[A]
      AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C :=
  { completedRingHom p f with
    commutes' := fun a ↦ by
      rw [IsScalarTower.algebraMap_apply A B
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) a,
        IsScalarTower.algebraMap_apply A C
          (AdicCompletion (DividedPowers.pAdicIdeal (A := C) p) C) a]
      exact (completedRingHom_of p f (algebraMap A B a)).trans
        (congrArg (AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) C) (f.commutes a)) }

/-- **`Crystalline.completedRingHom` is `Crystalline.PAdicCompletion.mapRingHom`**: the `p`-adic
completion of a ring map, built here from `Crystalline.adicCompletionRingMap`, is the one built
in `StacksFrontier/RingTheory/AdicCompletion/AdditiveFunctoriality.lean` from the observation that
the level `(p)ⁿ` is cut out by the integer `pⁿ`.

Both are determined by their values at the levels on a representative, which is
`Crystalline.PAdicCompletion.mapAddHom_eq_of_val`, so this is an identification and not a second
construction.  It is what lets a restriction of scalars along `Crystalline.completedRingHom` be
fed the scalar compatibility `Crystalline.PAdicCompletion.mapAddHom_smul`, which is stated for
the other spelling. -/
public theorem completedRingHom_apply_eq_mapRingHom
    (x : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) :
    completedRingHom p f x = PAdicCompletion.mapRingHom p B C f.toRingHom x :=
  DFunLike.congr_fun
    (PAdicCompletion.mapAddHom_eq_of_val p B C f.toRingHom.toAddMonoidHom
      (completedRingHom p f).toAddMonoidHom
      fun n z y hz ↦ by
        change adicQuotientMap (ringHomₛₗ f.toRingHom) (map_pAdicIdeal_le p f.toRingHom) n
            (z.val n) = _
        rw [hz]
        rfl)
    x

/-- The completed algebra map on the image of `B`. -/
@[simp]
public theorem completedAlgHom_of (b : B) :
    completedAlgHom p f (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b) =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) C (f b) :=
  completedRingHom_of p f b

variable (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)

include hf

/-- **The completion of a divided power morphism is a divided power morphism** of the completed
divided powers.  This is `Crystalline.adicCompletionRingMap_isDPMorphism` read on
`Crystalline.completedAlgHom`. -/
public theorem isDPMorphism_completedAlgHom :
    DividedPowers.IsDPMorphism (DividedPowers.completedDividedPowers J delta p hp).1
      (DividedPowers.completedDividedPowers L epsilon p hq).1
      (completedAlgHom p f).toRingHom :=
  adicCompletionRingMap_isDPMorphism delta epsilon p hp hq (DividedPowers.DPMorphism.mk' hf)

/-! ### The transition map of the universal differentials of the completion -/

/-- **The transition map `Ω_{B̂/A,γ̂} / pᵏ ⟶ Ω_{Ĉ/A,ε̂} / pᵏ`**, semilinear over the completed
ring map `B̂ → Ĉ`.  It is the functoriality
`Crystalline.mapDifferentialsOfDPMorphismₛₗ` of the universal divided power differentials at the
divided power morphism `Crystalline.isDPMorphism_completedAlgHom`, descended to the quotients by
`Crystalline.adicQuotientMap`. -/
public noncomputable def completedDifferentialsModPowMap (k : ℕ) :
    completedDifferentialsModPow (A := A) J delta p hp k →ₛₗ[(completedAlgHom p f).toRingHom]
      completedDifferentialsModPow (A := A) L epsilon p hq k :=
  adicQuotientMap
    (mapDifferentialsOfDPMorphismₛₗ (A := A) _
      (DividedPowers.completedDividedPowers J delta p hp).1
      (DividedPowers.completedDividedPowers L epsilon p hq).1 (completedAlgHom p f)
      (isDPMorphism_completedAlgHom J delta L epsilon p hp hq f hf))
    (map_pAdicIdeal_le p (completedAlgHom p f).toRingHom) k

/-- **The transition map of the universal differentials of the completion carries `d x` to
`d (f x)`**, modulo `pᵏ`. -/
public theorem completedDifferentialsModPowMap_mk_d (k : ℕ)
    (x : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) :
    completedDifferentialsModPowMap J delta L epsilon p hp hq f hf k
        (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1 x)) =
      Submodule.Quotient.mk (dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers L epsilon p hq).1 (completedAlgHom p f x)) :=
  congrArg Submodule.Quotient.mk
    (mapDifferentialsOfDPMorphism_d (A := A) _
      (DividedPowers.completedDividedPowers J delta p hp).1
      (DividedPowers.completedDividedPowers L epsilon p hq).1 (completedAlgHom p f)
      (isDPMorphism_completedAlgHom J delta L epsilon p hp hq f hf) x)

/-! ### The transition map of the completion of the differentials -/

/-- **The transition map `Ω̂_{B/A,δ} ⟶ Ω̂_{C/A,ε}`, as a map semilinear over the completed ring
map `B̂ → Ĉ`.**  The underlying function is `Crystalline.adicCompletionMapₛₗ` of the
functoriality of the differentials, which is semilinear over the *uncompleted* `B → C`; the
semilinearity over `B̂ → Ĉ` is `Crystalline.adicCompletionMapₛₗ_smul`.  This retyping is a
definition rather than a step inside a proof because it is the spelling of the scalars that the
quotient by the `p`-adic ideal of `B̂` consumes. -/
public noncomputable def completionDifferentialsMapₛₗ :
    AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
        (dividedPowerDifferentials (A := A) delta) →ₛₗ[(completedAlgHom p f).toRingHom]
      AdicCompletion (DividedPowers.pAdicIdeal (A := C) p)
        (dividedPowerDifferentials (A := A) epsilon) where
  toFun := adicCompletionMapₛₗ
    (mapDifferentialsOfDPMorphismₛₗ (A := A) J delta epsilon f hf)
    (map_pAdicIdeal_le p f.toRingHom)
  map_add' := map_add _
  map_smul' r x := adicCompletionMapₛₗ_smul _ _ r x

/-- The transition map of the completion of the differentials on the image of `Ω_{B/A,δ}`. -/
@[simp]
public theorem completionDifferentialsMapₛₗ_of
    (omega : dividedPowerDifferentials (A := A) delta) :
    completionDifferentialsMapₛₗ J delta L epsilon p f hf
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) _ omega) =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) _
        (mapDifferentialsOfDPMorphismₛₗ (A := A) J delta epsilon f hf omega) :=
  adicCompletionMapₛₗ_of (mapDifferentialsOfDPMorphismₛₗ (A := A) J delta epsilon f hf)
    (map_pAdicIdeal_le p f.toRingHom) omega

/-- **The transition map `Ω̂_{B/A,δ} / pᵏ ⟶ Ω̂_{C/A,ε} / pᵏ`**, semilinear over the completed ring
map `B̂ → Ĉ`: `Crystalline.completionDifferentialsMapₛₗ` descended to the quotients by
`Crystalline.adicQuotientMap`. -/
public noncomputable def completionDifferentialsModPowMap (k : ℕ) :
    completionDifferentialsModPow (A := A) J delta p k →ₛₗ[(completedAlgHom p f).toRingHom]
      completionDifferentialsModPow (A := A) L epsilon p k :=
  adicQuotientMap (completionDifferentialsMapₛₗ J delta L epsilon p f hf)
    (map_pAdicIdeal_le p (completedAlgHom p f).toRingHom) k

/-- **The transition map of the completion of the differentials carries the class of `d b` to the
class of `d (f b)`**, modulo `pᵏ`, for `b` in the uncompleted `B`. -/
public theorem completionDifferentialsModPowMap_mk_of_d (k : ℕ) (b : B) :
    completionDifferentialsModPowMap J delta L epsilon p f hf k
        (Submodule.Quotient.mk (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) _
          (dividedPowerDifferential (A := A) delta b))) =
      Submodule.Quotient.mk (AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) _
        (dividedPowerDifferential (A := A) epsilon (f b))) :=
  congrArg Submodule.Quotient.mk
    ((completionDifferentialsMapₛₗ_of J delta L epsilon p f hf _).trans
      (congrArg (AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) _)
        (mapDifferentialsOfDPMorphism_d (A := A) J delta epsilon f hf b)))

/-! ### The two routes round the naturality square, on the spanning classes -/

/-- **One route round the naturality square of the level identification, on a spanning class**:
the level identification of [Stacks, Tag 07KK] for `B` followed by the transition map of the
completion of the differentials carries the class of `d (of b)` to the class of the image of
`d (f b)`. -/
public theorem completionDifferentialsModPowMap_completedDifferentialsLevelEquiv_mk_d
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ) (b : B) :
    completionDifferentialsModPowMap J delta L epsilon p f hf
        (cmp.quotientSystem.cutoff + e)
        (completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e
          (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1
            (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)))) =
      Submodule.Quotient.mk (AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) _
        (dividedPowerDifferential (A := A) epsilon (f b))) :=
  Eq.trans
    (congrArg (completionDifferentialsModPowMap J delta L epsilon p f hf
      (cmp.quotientSystem.cutoff + e))
      (completedDifferentialsLevelEquiv_d (A := A) J delta p hp cmp e b))
    (completionDifferentialsModPowMap_mk_of_d J delta L epsilon p f hf
      (cmp.quotientSystem.cutoff + e) b)

/-- **The other route round the naturality square of the level identification, on a spanning
class**: the transition map of the universal differentials of the completion followed by the
level identification of [Stacks, Tag 07KK] for `C` carries the class of `d (of b)` to the same
class of the image of `d (f b)`.

Together with
`Crystalline.completionDifferentialsModPowMap_completedDifferentialsLevelEquiv_mk_d` this is the
naturality square on the classes that
`Crystalline.span_completedDifferentialsModPow_mk_d_of` says span, so for a consumer whose two
comparisons sit at a common level
`Crystalline.completedDifferentialsModPow_ext_addMonoidHom` turns the pair into the square. -/
public theorem completedDifferentialsLevelEquiv_completedDifferentialsModPowMap_mk_d
    (cmp' : DifferentialsCompletionComparison (A := A) L epsilon p hq) (e' : ℕ) (b : B) :
    completedDifferentialsLevelEquiv (A := A) L epsilon p hq cmp' e'
        (completedDifferentialsModPowMap J delta L epsilon p hp hq f hf
          (cmp'.quotientSystem.cutoff + e')
          (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1
            (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)))) =
      Submodule.Quotient.mk (AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) _
        (dividedPowerDifferential (A := A) epsilon (f b))) := by
  refine Eq.trans (congrArg (completedDifferentialsLevelEquiv (A := A) L epsilon p hq cmp' e')
    (Eq.trans (completedDifferentialsModPowMap_mk_d J delta L epsilon p hp hq f hf
        (cmp'.quotientSystem.cutoff + e')
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b))
      (congrArg (fun y ↦ Submodule.Quotient.mk (dividedPowerDifferential (A := A)
          (DividedPowers.completedDividedPowers L epsilon p hq).1 y))
        (completedAlgHom_of p f b)))) ?_
  exact completedDifferentialsLevelEquiv_d (A := A) L epsilon p hq cmp' e' (f b)

end Transition

end Crystalline

end
