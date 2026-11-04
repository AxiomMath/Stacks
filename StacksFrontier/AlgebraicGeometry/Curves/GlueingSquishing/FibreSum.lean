module

public import Mathlib.Data.ENat.BigOperators
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.StalkProduct
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsMeasure

/-!
# The fibre sum for a module with finite support of closed points

The measure of the induction of [Stacks, Tag 0C1L] is summed over the points of the base, so
comparing the measure of the *upper* half `X' ⟶ Spec_X(𝒜)` of an intermediate factorization with
that of `f : X' ⟶ X` means relating a sum over the points of `Spec_X(𝒜)` to a sum over the points
of `X`. This file supplies that comparison, for any morphism `g : W ⟶ X` which is universally
closed — in particular any finite one — and any `𝒪_W`-module `N` whose support is a finite set of
closed points, which is the shape the torsion quotients of the factorization have.

The input is `Stacks.Chow.pushforwardStalkLinearEquivPi`, the product decomposition
`(g_*N)_x ≅ ∏_{z ∈ Supp(N), g z = x} N_z` of [Stacks, Tag 02R6]. Its three hypotheses are all
free here: the support is closed because it is a finite union of closed points, the irreducible
components of a finite support are finitely many hence a locally finite family, and every point
of the support is the generic point of a component of it because it is closed and no other point
of the support can specialize to a closed point.

## Main results

* `Stacks.GlueSquishFactor.isClosed_supp_of_finite_of_forall_isClosed` — a finite support of
  closed points is closed.
* `Stacks.GlueSquishFactor.length_stalk_pushforward_eq_sum` — **the fibre sum**: the length of the
  stalk of `g_*N` at `x`, over the local ring of `X` at `x`, is the sum of the lengths over that
  same ring of the stalks of `N` along the fibre of the support.
* `Stacks.GlueSquishFactor.sum_length_stalk_le_length_stalk_pushforward` — the form the measure
  needs: the lengths of the stalks of `N` over the local rings of `W` sum to at most the length of
  the stalk of `g_*N` over the local ring of `X`.
* `Stacks.GlueSquishFactor.sum_sheafMultiplicity_le_sheafMultiplicity_pushforward` — the same
  inequality read through `Stacks.Chow.sheafMultiplicity`, i.e. in `ℤ`.

## Implementation notes

**Why an inequality and not an equality at the second step.** The length of `N_z` over the local
ring of `X` at `x` exceeds its length over the local ring of `W` at `z` by the factor
`[κ(z) : κ(x)]` (`IsLocalRing.length_restrictScalars`, and
`Stacks.Chow.length_stalk_restrictScalars_toNat` for the geometric reading). That factor is `1`
for a finite morphism of schemes of finite type over an algebraically closed field at a closed
point, but saying so needs the residue fields computed, and the induction of [Stacks, Tag 0C1L]
only ever needs the measure of the upper half to be *at most* the corresponding part of the
measure of `f`. So the degree is discarded against `1 ≤ ℓ(κ(x) → κ(z))`, which holds because a
residue field is not the zero ring, and no hypothesis on `k` is used anywhere in this file.

**`g` is only assumed universally closed.** Neither affineness, nor quasi-coherence of `N`, nor
coherence of `N` is used: `Stacks.Chow.pushforwardStalkLinearEquivPi` needs the morphism closed
and the support's components separated, and finiteness of the support gives the rest.

**What this does not give.** It does not identify `g_*` of the torsion quotient on `W` with the
torsion quotient on `X`; that is right exactness of `g_*` on quasi-coherent modules along an
affine morphism, which is a separate statement and *is* in the tree, as
`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero`. So no part of
[Stacks, Tag 0C1L] is asserted here and no attribute is attached.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.GlueSquishFactor

variable {W X : Scheme.{u}}

/-! ### A finite support of closed points -/

/-- **A finite support of closed points is closed**: it is the union of its own points, a finite
union of closed sets. -/
theorem isClosed_supp_of_finite_of_forall_isClosed (N : W.Modules)
    (hfin : (SheafOfModules.supp N : Set W).Finite)
    (hcl : ∀ z ∈ SheafOfModules.supp N, IsClosed ({z} : Set W)) :
    IsClosed (SheafOfModules.supp N : Set W) := by
  have he : (SheafOfModules.supp N : Set W) =
      ⋃ z ∈ (SheafOfModules.supp N : Set W), ({z} : Set W) := by
    simp
  rw [he]
  exact hfin.isClosed_biUnion hcl

/-- The irreducible components of a finite support are finitely many, hence a locally finite
family: this is the hypothesis `hloc` of `Stacks.Chow.pushforwardStalkLinearEquivPi`. -/
theorem locallyFinite_components_supp_of_finite (N : W.Modules)
    (hfin : (SheafOfModules.supp N : Set W).Finite) :
    LocallyFinite (fun C : irreducibleComponents (SheafOfModules.supp N : Set W) =>
      (Subtype.val '' C.1 : Set W)) := by
  have : Finite ↥(SheafOfModules.supp N : Set W) := hfin.to_subtype
  have : Finite ↥(irreducibleComponents (SheafOfModules.supp N : Set W)) := Subtype.finite
  exact locallyFinite_of_finite _

/-- **No point of the support specializes to another when they are all closed.** A point of the
support is closed, so the only point it specializes to is itself; this is the hypothesis `huniq`
of `Stacks.GlueSquishFactor.isGenericPoint_component_supp_of_isClosed_of_forall_specializes_eq`,
and it is free once every point of the support is closed. -/
theorem forall_specializes_eq_of_forall_isClosed (N : W.Modules)
    (hcl : ∀ z ∈ SheafOfModules.supp N, IsClosed ({z} : Set W)) {z : W} (η : W) (hη : η ⤳ z)
    (hηsupp : η ∈ SheafOfModules.supp N) : η = z := by
  have hx : z ∈ ({η} : Set W) := by
    rw [← (hcl η hηsupp).closure_eq]
    exact specializes_iff_mem_closure.mp hη
  exact hx.symm

/-- Every point of the support is the generic point of an irreducible component of it: this is the
hypothesis `hgen` of `Stacks.Chow.pushforwardStalkLinearEquivPi`. -/
theorem isGenericPoint_component_supp_of_finite_of_forall_isClosed (N : W.Modules)
    (hfin : (SheafOfModules.supp N : Set W).Finite)
    (hcl : ∀ z ∈ SheafOfModules.supp N, IsClosed ({z} : Set W)) {z : W}
    (hz : z ∈ SheafOfModules.supp N) :
    ∃ C : irreducibleComponents (SheafOfModules.supp N : Set W),
      IsGenericPoint z (Subtype.val '' C.1 : Set W) :=
  isGenericPoint_component_supp_of_isClosed_of_forall_specializes_eq N
    (isClosed_supp_of_finite_of_forall_isClosed N hfin hcl) hz (hcl z hz)
    (forall_specializes_eq_of_forall_isClosed N hcl)

/-! ### The fibre sum -/

/-- **The fibre sum.** Let `g : W ⟶ X` be a universally closed morphism of schemes and let `N` be
an `𝒪_W`-module whose support is a finite set of closed points. Then for every `x : X` the length
of the stalk of `g_*N` at `x` is the sum, over the points of the support lying above `x`, of the
lengths of the stalks of `N` there — all lengths taken over the local ring of `X` at `x`.

This is `Stacks.Chow.pushforwardStalkLinearEquivPi` with its three hypotheses discharged, read
through `Module.length_pi_of_fintype`. -/
theorem length_stalk_pushforward_eq_sum (g : W ⟶ X) [UniversallyClosed g] (N : W.Modules)
    (hfin : (SheafOfModules.supp N : Set W).Finite)
    (hcl : ∀ z ∈ SheafOfModules.supp N, IsClosed ({z} : Set W)) (x : X) :
    letI : ∀ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
        Module (X.presheaf.stalk x) (N.presheaf.stalk z.1) :=
      Stacks.Chow.supportFibreStalkModule g N x
    letI : Fintype ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} :=
      (hfin.subset fun _ hz => hz.2).fintype
    Module.length (X.presheaf.stalk x)
        (((Scheme.Modules.pushforward g).obj N).presheaf.stalk x) =
      ∑ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
        Module.length (X.presheaf.stalk x) (N.presheaf.stalk z.1) := by
  let : ∀ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
      Module (X.presheaf.stalk x) (N.presheaf.stalk z.1) :=
    Stacks.Chow.supportFibreStalkModule g N x
  let : Fintype ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} :=
    (hfin.subset fun _ hz => hz.2).fintype
  rw [(Stacks.Chow.pushforwardStalkLinearEquivPi g N
      (isClosed_supp_of_finite_of_forall_isClosed N hfin hcl) x
      (locallyFinite_components_supp_of_finite N hfin)
      fun z => isGenericPoint_component_supp_of_finite_of_forall_isClosed N hfin hcl
        z.2.2).length_eq,
    Module.length_pi_of_fintype]

/-! ### Discarding the residue degree -/

/-- **The length of a stalk over the base is at least its length upstairs.** For any morphism of
schemes `g : W ⟶ X` and any `𝒪_W`-module `N`, the length of `N_z` over the local ring of `X` at
`g z` is the length over the local ring of `W` at `z` times the length of the residue field
extension (`IsLocalRing.length_restrictScalars`), and the latter is at least `1` because a
residue field is not the zero ring. -/
theorem length_stalk_le_length_stalk_restrictScalars (g : W ⟶ X) (N : W.Modules) (z : W) :
    letI : Module (X.presheaf.stalk (g.base z)) (N.presheaf.stalk z) :=
      Module.compHom _ (g.stalkMap z).hom
    Module.length (W.presheaf.stalk z) (N.presheaf.stalk z) ≤
      Module.length (X.presheaf.stalk (g.base z)) (N.presheaf.stalk z) := by
  let : Algebra (X.presheaf.stalk (g.base z)) (W.presheaf.stalk z) :=
    (g.stalkMap z).hom.toAlgebra
  let : Module (X.presheaf.stalk (g.base z)) (N.presheaf.stalk z) :=
    Module.compHom _ (g.stalkMap z).hom
  let : IsScalarTower (X.presheaf.stalk (g.base z)) (W.presheaf.stalk z)
      (N.presheaf.stalk z) :=
    ⟨fun a b m => mul_smul ((g.stalkMap z).hom a) b m⟩
  let : IsLocalHom (algebraMap (X.presheaf.stalk (g.base z)) (W.presheaf.stalk z)) :=
    (inferInstance : IsLocalHom (g.stalkMap z).hom)
  rw [IsLocalRing.length_restrictScalars (X.presheaf.stalk (g.base z)) (W.presheaf.stalk z)
    (N.presheaf.stalk z)]
  refine le_mul_of_one_le_right zero_le (Order.one_le_iff_ne_zero.2 fun hzero => ?_)
  have := Module.length_eq_zero_iff.mp hzero
  exact (not_subsingleton _) this

/-- **The fibre sum, in the form the measure of [Stacks, Tag 0C1L] needs.** With the hypotheses of
`Stacks.GlueSquishFactor.length_stalk_pushforward_eq_sum`, the lengths of the stalks of `N` along
the fibre of the support, each over its own local ring on `W`, sum to at most the length of the
stalk of `g_*N` at `x` over the local ring of `X` at `x`.

The residue degrees of `g` at the fibre points are discarded here; see the implementation notes
of this file for why they are not needed. -/
theorem sum_length_stalk_le_length_stalk_pushforward (g : W ⟶ X) [UniversallyClosed g]
    (N : W.Modules) (hfin : (SheafOfModules.supp N : Set W).Finite)
    (hcl : ∀ z ∈ SheafOfModules.supp N, IsClosed ({z} : Set W)) (x : X) :
    letI : Fintype ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} :=
      (hfin.subset fun _ hz => hz.2).fintype
    ∑ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
        Module.length (W.presheaf.stalk z.1) (N.presheaf.stalk z.1) ≤
      Module.length (X.presheaf.stalk x)
        (((Scheme.Modules.pushforward g).obj N).presheaf.stalk x) := by
  rw [length_stalk_pushforward_eq_sum g N hfin hcl x]
  refine Finset.sum_le_sum fun z _ => ?_
  obtain ⟨z, hzx, hzsupp⟩ := z
  subst hzx
  exact length_stalk_le_length_stalk_restrictScalars g N z

/-- **The fibre sum through `Stacks.Chow.sheafMultiplicity`.** With the hypotheses of
`Stacks.GlueSquishFactor.sum_length_stalk_le_length_stalk_pushforward` and the length of the stalk
of `g_*N` at `x` finite, the multiplicities of `N` along the fibre of the support sum to at most
the multiplicity of `g_*N` at `x`.

Finiteness is what makes `Stacks.Chow.sheafMultiplicity`, which is read through `ENat.toNat`, see
the inequality: an infinite length is recorded as `0`. For the quotients of [Stacks, Tag 0C1L] it
is `Stacks.GlueSquishFactor.isFiniteLength_stalk_cokernel_structureUnitHom`. -/
theorem sum_sheafMultiplicity_le_sheafMultiplicity_pushforward (g : W ⟶ X)
    [UniversallyClosed g] (N : W.Modules) (hfin : (SheafOfModules.supp N : Set W).Finite)
    (hcl : ∀ z ∈ SheafOfModules.supp N, IsClosed ({z} : Set W)) (x : X)
    (hlen : IsFiniteLength (X.presheaf.stalk x)
      (((Scheme.Modules.pushforward g).obj N).presheaf.stalk x)) :
    letI : Fintype ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} :=
      (hfin.subset fun _ hz => hz.2).fintype
    ∑ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
        Stacks.Chow.sheafMultiplicity N z.1 ≤
      Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward g).obj N) x := by
  let : Fintype ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} :=
    (hfin.subset fun _ hz => hz.2).fintype
  have htot := Module.length_ne_top_iff.mpr hlen
  have hle := sum_length_stalk_le_length_stalk_pushforward g N hfin hcl x
  have hterm (z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N}) :
      Module.length (W.presheaf.stalk z.1) (N.presheaf.stalk z.1) ≠ ⊤ :=
    ne_top_of_le_ne_top htot
      (le_trans (Finset.single_le_sum
        (f := fun z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} =>
          Module.length (W.presheaf.stalk z.1) (N.presheaf.stalk z.1))
        (fun _ _ => zero_le) (Finset.mem_univ z)) hle)
  have hcast : ∑ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
      Stacks.Chow.sheafMultiplicity N z.1 =
      ((ENat.toNat (∑ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
        Module.length (W.presheaf.stalk z.1) (N.presheaf.stalk z.1)) : ℕ) : ℤ) := by
    rw [ENat.toNat_sum (fun z _ => hterm z), Nat.cast_sum]
    rfl
  rw [hcast]
  exact Int.ofNat_le.mpr (ENat.toNat_le_toNat hle htot)

end Stacks.GlueSquishFactor

end
