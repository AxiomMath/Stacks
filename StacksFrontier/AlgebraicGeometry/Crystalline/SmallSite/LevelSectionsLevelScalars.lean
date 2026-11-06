module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsCosimplicialModule

/-!
# The sections at a level are a module over every finite level of `D(n)` above `N + e`

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, and let
`(X, T(n)_e, δ(n))` be the cosimplicial system of thickenings of [Stacks, Tag 07JN].
`...SmallSite.levelSectionsScalars` of `SmallSite/LevelSectionsCosimplicialModule.lean` is the
ring map `D(n) → Γ(T(n)_e, 𝒪)` through which the sections of a sheaf of `𝒪_{X/S}`-modules over
the level `(n, e)` are a `D(n)`-module.  By construction it is the quotient map onto the finite
level `D(n)/(p)^{N + e}` followed by the inverse of
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv`, so it **factors through every finite level
`D(n)/(p)^k` with `N + e ≤ k`**, and the sections are a module over each of those.

This file records that factorisation and the module structures it gives.

## Why more than one level is needed

The two comparisons the isomorphism `ε` of [Stacks, Tag 07LF] has to compose ask for the module
structure at two *different* levels.

* `Crystalline.tensorFormsLevelEquiv` of `ModuleDifferentials/QuotientForms.lean` is read at
  `B = D(n)` and `k = N + e`, the level the section ring itself is.
* `Crystalline.tensorFormsCompletionLevelEquivAt` of
  `ModuleDifferentials/CompletionLevelFormsNaturality.lean` is read at a level tied to the cutoff
  of its own `Crystalline.DifferentialsCompletionComparison`.  That cutoff is a
  `Classical.choose` and is **not** comparable to `Crystalline.uniformLevel`, so no reindexing of
  the comparison can bring it down to `N + e`.  None is needed: the source and target of that
  equivalence do not depend on `k` — only its ring of scalars and the instance
  `[Module (B̂ ⧸ (p)^k) M]` do — so it suffices to read it at
  `k = cutoff + (N + e)`, where the proof `cmp.quotientSystem.cutoff + (N + e) = k` is `rfl` and
  `N + e ≤ k` is `Nat.le_add_left`.

Both shapes are therefore provided as instances: `levelSectionsModuleAtLevel` at `k = N + e`
exactly, and `levelSectionsModuleAtAdd` at `k = c + (N + e)` for an arbitrary `c`, which is the
shape the second comparison presents.  Typeclass synthesis cannot be asked to discharge a side
condition `N + e ≤ k` for an opaque `k`, which is why the general definitions carry it
explicitly and the instances are stated at the two shapes that actually occur.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsScalarsAt` — the ring map
  `D(n)/(p)^k → Γ(T(n)_e, 𝒪)` for `N + e ≤ k`, namely the surjection onto `D(n)/(p)^{N + e}`
  followed by the inverse of `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsModuleAt` — the resulting
  `D(n)/(p)^k`-module structure on the sections of a sheaf of `𝒪_{X/S}`-modules over the level
  `(n, e)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsModuleAtLevel` and
  `...SmallSite.levelSectionsModuleAtAdd` — that structure as instances at `k = N + e` and at
  `k = c + (N + e)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsScalarsAt_mk` — the
  factorisation: `levelSectionsScalarsAt` of the class of `r` is
  `...SmallSite.levelSectionsScalars` of `r`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsScalarsAt_comp_mk` — the same as
  an equality of ring maps.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsIsScalarTowerAtLevel` and
  `...SmallSite.levelSectionsIsScalarTowerAtAdd` — the scalar tower
  `D(n) → D(n)/(p)^k → Γ(T(n)_e, F)` at the two shapes, which is the third instance
  `Crystalline.tensorFormsLevelEquiv` and `Crystalline.tensorFormsCompletionLevelEquivAt` ask
  for.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsScalarsAt_restriction` — the
  scalars at a level are compatible with the cosimplicial direction, which is
  `...SmallSite.levelSectionsScalars_restriction` read one level up.

## What is and is not proved

**No tag attribute is placed in this file, and [Stacks, Tag 07LF] is not proved.**  What is
supplied is the typeclass prerequisite of the degreewise composite that the isomorphism `ε` of
that tag still owes: the module and scalar-tower instances over the finite levels of `D(n)`
without which neither `Crystalline.tensorFormsLevelEquiv` nor
`Crystalline.tensorFormsCompletionLevelEquivAt` can be applied to the sections `M(n)_e`.  The
composite itself is not formed here, and no isomorphism of cosimplicial abelian groups is
constructed.

The sheaf `F` is an arbitrary sheaf of `𝒪_{X/S}`-modules: neither hypothesis (1) nor hypothesis
(2) of [Stacks, Tag 07JN] is used or assumed, and no flatness or finiteness hypothesis appears.
The hypotheses carried are exactly those `...SmallSite.levelSectionsScalars` itself carries:
`hp`, `[IsAffine S.X]` and `[IsAffine S.S.scheme]`.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

/-! ### The scalars at a finite level above `N + e` -/

/-- **The ring map `D(n)/(p)^k → Γ(T(n)_e, 𝒪)` through which the level `(n, e)` of the system of
[Stacks, Tag 07JN] is an algebra over the finite level `D(n)/(p)^k`**, for any `k` at least the
uniform cutoff `N` plus the `p`-adic level `e`.

It is the surjection `D(n)/(p)^k ↠ D(n)/(p)^{N + e}` — available because `(p)^k ⊆ (p)^{N + e}` —
followed by the inverse of the identification
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` of that finite level with the section ring.  At
`k = N + e` the surjection is the identity and this is `...SmallSite.levelSectionsScalars`
factored through the quotient map. -/
def levelSectionsScalarsAt (n : SimplexCategory) (e k : ℕ)
    (hk : _root_.Crystalline.uniformLevel (affineSituation S hp) + e ≤ k) :
    (((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
            (affineSituation S hp).p ^ k) →+*
      ((structureSheaf S).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) : Type u) :=
  (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm.toRingHom.comp
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right hk))

/-- **`levelSectionsScalarsAt` factors `...SmallSite.levelSectionsScalars`**: its value on the
class of a scalar `r` of `D(n)` is `...SmallSite.levelSectionsScalars` of `r`.  This is what makes
the sections a module over `D(n)/(p)^k` *compatibly* with their `D(n)`-module structure. -/
theorem levelSectionsScalarsAt_mk (n : SimplexCategory) (e k : ℕ)
    (hk : _root_.Crystalline.uniformLevel (affineSituation S hp) + e ≤ k)
    (r : ((wholeSpaceEnvelopeRing hp).obj n : Type u)) :
    levelSectionsScalarsAt hp n e k hk (Ideal.Quotient.mk _ r) =
      levelSectionsScalars hp n e r := by
  show (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right hk) (Ideal.Quotient.mk _ r)) = _
  rw [Ideal.Quotient.factor_mk]
  rfl

/-- The factorisation of `...SmallSite.levelSectionsScalars` through the level, as an equality of
ring maps. -/
theorem levelSectionsScalarsAt_comp_mk (n : SimplexCategory) (e k : ℕ)
    (hk : _root_.Crystalline.uniformLevel (affineSituation S hp) + e ≤ k) :
    (levelSectionsScalarsAt hp n e k hk).comp
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
          (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
          (affineSituation S hp).p ^ k)) =
      levelSectionsScalars hp n e :=
  RingHom.ext fun r ↦ levelSectionsScalarsAt_mk hp n e k hk r

/-- **The scalars at a finite level are compatible with the cosimplicial direction.**  Restricting
`levelSectionsScalarsAt hp n e k hk s` along the transition map `T(m)_e ⟶ T(n)_e` of the system of
[Stacks, Tag 07JN] gives `levelSectionsScalarsAt hp m e k hk` of the image of `s` under the
descent `D(n)/(p)^k ⟶ D(m)/(p)^k` of the structure map of `...SmallSite.wholeSpaceEnvelopeRing`.

This is `...SmallSite.levelSectionsScalars_restriction` read one level up: both sides are
determined on the classes of scalars of `D(n)`, the quotient map being surjective, and there the
statement is that one. -/
theorem levelSectionsScalarsAt_restriction {n m : SimplexCategory} (φ : n ⟶ m) (e k : ℕ)
    (hk : _root_.Crystalline.uniformLevel (affineSituation S hp) + e ≤ k)
    (s : ((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
      DividedPowers.pAdicIdeal
          (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
          (affineSituation S hp).p ^ k) :
    ((structureSheaf S).obj.map (((wholeSpaceSystem S hp).map φ.op).app e).op).hom
        (levelSectionsScalarsAt hp n e k hk s) =
      levelSectionsScalarsAt hp m e k hk
        (Ideal.quotientMap _ ((wholeSpaceEnvelopeRing hp).map φ).hom
          (wholeSpaceEnvelopeRing_map_pAdicIdeal_pow_le hp φ k) s) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [levelSectionsScalarsAt_mk, Ideal.quotientMap_mk, levelSectionsScalarsAt_mk]
  exact levelSectionsScalars_restriction hp φ e r

/-! ### The module structures -/

variable (F : SheafOfModules.{u} (structureSheaf S))

/-- **The sections of a sheaf of `𝒪_{X/S}`-modules over the level `(n, e)` of the system of
[Stacks, Tag 07JN] are a module over the finite level `D(n)/(p)^k`**, for every `k` at least
`N + e`: restriction of scalars along `levelSectionsScalarsAt`.

This is a plain definition rather than an instance because typeclass synthesis cannot discharge
the side condition `N + e ≤ k` at an opaque `k`; the two shapes of `k` that occur are registered
as instances below. -/
@[instance_reducible]
def levelSectionsModuleAt (n : SimplexCategory) (e k : ℕ)
    (hk : _root_.Crystalline.uniformLevel (affineSituation S hp) + e ≤ k) :
    Module (((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
            (affineSituation S hp).p ^ k)
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :=
  Module.compHom _ (levelSectionsScalarsAt hp n e k hk)

/-- A scalar of `D(n)/(p)^k` acts on a section over the level `(n, e)` through
`levelSectionsScalarsAt`. -/
theorem levelSectionsModuleAt_smul (n : SimplexCategory) (e k : ℕ)
    (hk : _root_.Crystalline.uniformLevel (affineSituation S hp) + e ≤ k)
    (s : ((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
      DividedPowers.pAdicIdeal
          (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
          (affineSituation S hp).p ^ k)
    (x : F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :
    (levelSectionsModuleAt hp F n e k hk).toDistribMulAction.toMulAction.toSMul.smul s x =
      levelSectionsScalarsAt hp n e k hk s • x :=
  rfl

/-- **The sections over the level `(n, e)` are a module over `D(n)/(p)^{N + e}`**, the finite
level the section ring itself is.  This is the instance
`Crystalline.tensorFormsLevelEquiv` asks for. -/
instance levelSectionsModuleAtLevel (n : SimplexCategory) (e : ℕ) :
    Module (((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
            (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :=
  levelSectionsModuleAt hp F n e _ le_rfl

/-- **The sections over the level `(n, e)` are a module over `D(n)/(p)^{c + (N + e)}` for every
`c`.**  This is the shape `Crystalline.tensorFormsCompletionLevelEquivAt` presents: its level is
the cutoff of its own `Crystalline.DifferentialsCompletionComparison` added to `N + e`, and that
cutoff is a `Classical.choose` about which nothing is known. -/
instance levelSectionsModuleAtAdd (n : SimplexCategory) (e c : ℕ) :
    Module (((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
            (affineSituation S hp).p ^
          (c + (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)))
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :=
  levelSectionsModuleAt hp F n e _ (Nat.le_add_left _ c)

/-! ### The scalar towers -/

/-- **The scalar tower `D(n) → D(n)/(p)^k → Γ(T(n)_e, F)`**, for every `k` at least `N + e`:
acting by a scalar of `D(n)` is acting by its class in the level.  This is
`levelSectionsScalarsAt_mk` together with multiplicativity, the quotient map being surjective.

Stated as a plain theorem for the same reason as `levelSectionsModuleAt`; the two shapes that
occur are registered as instances below. -/
theorem levelSectionsIsScalarTowerAt (n : SimplexCategory) (e k : ℕ)
    (hk : _root_.Crystalline.uniformLevel (affineSituation S hp) + e ≤ k) :
    letI := levelSectionsModuleAt hp F n e k hk
    IsScalarTower ((wholeSpaceEnvelopeRing hp).obj n)
      (((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
            (affineSituation S hp).p ^ k)
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) := by
  let := levelSectionsModuleAt hp F n e k hk
  refine ⟨fun r s x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  show levelSectionsScalarsAt hp n e k hk (r • Ideal.Quotient.mk _ a) • x =
    levelSectionsScalars hp n e r • levelSectionsScalarsAt hp n e k hk
      (Ideal.Quotient.mk _ a) • x
  have hrs : r • Ideal.Quotient.mk (DividedPowers.pAdicIdeal
      (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
      (affineSituation S hp).p ^ k) a =
      Ideal.Quotient.mk _ r * Ideal.Quotient.mk _ a := by
    rw [← map_mul]
    rfl
  rw [hrs, map_mul, levelSectionsScalarsAt_mk, mul_smul]

/-- **The scalar tower at `k = N + e`**, the instance `Crystalline.tensorFormsLevelEquiv` asks
for. -/
instance levelSectionsIsScalarTowerAtLevel (n : SimplexCategory) (e : ℕ) :
    IsScalarTower ((wholeSpaceEnvelopeRing hp).obj n)
      (((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
            (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :=
  levelSectionsIsScalarTowerAt hp F n e _ le_rfl

/-! ### The two module structures agree along the level identification -/

/-- **At `k = N + e` the scalars are the inverse of the level identification itself**: the
surjection `D(n)/(p)^{N + e} ↠ D(n)/(p)^{N + e}` that `levelSectionsScalarsAt` composes with is
the identity, the quotient map being surjective and `Ideal.Quotient.factor_mk` being the
computation on a class. -/
theorem levelSectionsScalarsAt_level (n : SimplexCategory) (e : ℕ)
    (s : ((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
      DividedPowers.pAdicIdeal
          (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
          (affineSituation S hp).p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) :
    levelSectionsScalarsAt hp n e _ le_rfl s =
      (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm s := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [levelSectionsScalarsAt_mk]
  rfl

/-- **The native module structure on the sections and the one over the finite level `D(n)/(p)^{N +
e}` agree along the level identification.**

Acting by a section `b` of `𝒪_{X/S}` over the level `(n, e)` is acting by its image under
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` in the `D(n)/(p)^{N + e}`-module structure of
`levelSectionsModuleAtLevel`.

This is the hypothesis `hsm` of `Crystalline.tensorFormsEquivOfAlgEquiv` of
`ModuleDifferentials/FormsAlgEquivTensor.lean` read at the level objects, and so is what makes
that transport — the crossing of the ring identification in the degreewise composite of the
isomorphism `ε` of [Stacks, Tag 07LF] — applicable here.  It holds because the module structure
over the level is restriction of scalars along `levelSectionsScalarsAt`, which at this level is
the *inverse* of the identification by `levelSectionsScalarsAt_level`. -/
theorem levelSections_smul_eq (n : SimplexCategory) (e : ℕ)
    (b : ((structureSheaf S).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) : Type u))
    (x : F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :
    b • x = wholeSpaceEnvelopeRingLevelEquiv hp n.len e b • x := by
  show _ = levelSectionsScalarsAt hp n e _ le_rfl
    (wholeSpaceEnvelopeRingLevelEquiv hp n.len e b) • x
  rw [levelSectionsScalarsAt_level, RingEquiv.symm_apply_apply]

/-- **The scalar tower at `k = c + (N + e)`**, the instance
`Crystalline.tensorFormsCompletionLevelEquivAt` asks for. -/
instance levelSectionsIsScalarTowerAtAdd (n : SimplexCategory) (e c : ℕ) :
    IsScalarTower ((wholeSpaceEnvelopeRing hp).obj n)
      (((wholeSpaceEnvelopeRing hp).obj n : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
            (affineSituation S hp).p ^
          (c + (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)))
      (F.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :=
  levelSectionsIsScalarTowerAt hp F n e _ (Nat.le_add_left _ c)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
