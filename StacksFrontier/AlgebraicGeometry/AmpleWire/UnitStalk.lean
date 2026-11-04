module

public import StacksFrontier.AlgebraicGeometry.AmplePowers.QuasiAffine

/-!
# The stalk of the structure sheaf as an abelian group, and the global basis `1`

`Stacks.ModuleStalk.maximalSmul` is the submodule `𝔪_x · M_x` of the stalk of an `𝒪_X`-module,
and `Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers` reduces Stacks Tag 01QE to a
`Stacks.Ample.NonvanishingBasis` in every tensor degree — a global section
vanishing nowhere whose multiples exhaust the global sections. That reduction was conditional
because `𝔪_x · M_x` is a submodule of the stalk of `M.presheaf`, which is a colimit in `Ab`,
while `𝔪_x` is an ideal of the stalk `𝒪_{X,x}`, which is a colimit in `CommRingCat`, and nothing
identified the two.

This file supplies the identification and the basis.

## Main definitions

* `Stacks.Ample.unitModule X`: `𝒪_X` regarded as a module over itself.
* `Stacks.Ample.unitStalkIso`: the stalk of `𝒪_X` taken in `Ab` is the stalk taken in
  `CommRingCat`, as an isomorphism of abelian groups.
* `Stacks.Ample.unitStalkEquiv`: the same comparison as an `𝒪_{X,x}`-linear equivalence onto
  `𝒪_{X,x}` viewed as a module over itself.
* `Stacks.Ample.unitBasis X`: the global section `1` of `𝒪_X`, with proofs that it vanishes
  nowhere and that its multiples are all of `Γ(X, 𝒪_X)`.

## Main results

* `Stacks.Ample.unitStalkFun_germ`: the comparison sends the `Ab`-germ of a section to its
  `CommRingCat`-germ. This is the only property of the comparison that is used.
* `Stacks.Ample.mem_maximalIdeal_of_mem_maximalSmul`: the comparison carries `𝔪_x · (𝒪_X)_x`
  into `𝔪_x`. Only this inclusion is needed, and it needs no surjectivity.
* `Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one`: **the germ of `1` avoids `𝔪_x · (𝒪_X)_x`**,
  i.e. `X_1 = X`.

## Implementation notes

The stalk of a presheaf `F` at `x` is `colimit ((OpenNhds.inclusion x).op ⋙ F)`, and the
underlying `Ab`-valued presheaf of `𝒪_X` regarded as a module over itself is, by `rfl`,
`X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab`. So the two stalks are
`colimit (D ⋙ G)` and `G.obj (colimit D)` for one diagram `D` and the forgetful composite `G`.
Mathlib's `CategoryTheory.Limits.preservesColimitIso` therefore gives the comparison outright:
`forget₂ CommRingCat RingCat` and `forget₂ RingCat Ab` each preserve filtered colimits, the
category of open neighbourhoods is filtered, and `CategoryTheory.Limits.ι_preservesColimitIso_inv`
is exactly the germ compatibility. Nothing had to be constructed by hand.

Scalar compatibility then reduces to germs: `Stacks.ModuleStalk.germ_smul` says the `Ab`-germ of
`a • t` is `germ a • germ t`, and on the structure sheaf `a • t` *is* `a * t`, so the comparison
turns the module action into ring multiplication by `map_mul` on the `CommRingCat`-germ.

The precedent in Mathlib is `smoothSheafCommRing.forgetStalk`, which compares the stalk of the
sheaf of smooth ring-valued functions with the stalk of the underlying sheaf of types in exactly
this way.

## Transparency gotchas

**1. `Γ(unitModule X, U)` and `Γ(X, U)` are the same type but not interchangeable for `rw`.**
They are definitionally equal — the carrier of
`(forget₂ RingCat Ab).obj ((forget₂ CommRingCat RingCat).obj (X.presheaf.obj (op U)))` is the
carrier of `X.presheaf.obj (op U)` — and no coercion function is inserted between them, so a
`rw` whose pattern fixes one spelling will not fire against the other. Every statement below
takes its section argument at the type it will be *applied* at, and uses `show T from t` rather
than a type ascription to move between the two. A type ascription is not enough, as can be
observed: writing `(ht : (t : Γ(X, ⊤)) = 1)` for `t : Γ(unitModule X, ⊤)` produces an equation at
`Γ(unitModule X, ⊤)`, not at `Γ(X, ⊤)`, and then the numeral fails to elaborate for want of an
`OfNat` instance — instance search does not unfold the forgetful composite to find the one on
`Γ(X, ⊤)`. That is also why `Γgerm_notMem_maximalSmul_of_eq_one` carries the hypothesis `1 = t`
instead of being stated about the numeral directly.

**2. The numerals and the ring structure are on the `Γ(X, U)` side only.** `Γ(unitModule X, U)`
is an abelian group as far as instance search is concerned; `mul_one` and `map_mul` are applied
at `Γ(X, U)` and transported by `exact`, which checks at default transparency and so succeeds.

## References

* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)

## What is not done

The comparison is built for the structure sheaf only. Nothing here identifies the stalk of a
general `𝒪_X`-module with anything, and in particular `𝔪_x · M_x` is still not computed for any
`M` other than `𝒪_X`. Openness of the nonvanishing locus (Stacks Tag 01CY) is not proved here,
and no local freeness or Nakayama argument appears; it is proved in
`../NonvanishingOpen/Basic.lean`, as `Stacks.NonvanishingOpen.isOpen_nonvanishingLocus`, over a
trivializing cover rather than by Nakayama. The comparison is not shown to be a ring
isomorphism — it is an isomorphism of abelian groups and an `𝒪_{X,x}`-linear equivalence, which
is all the ampleness argument asks of it, and the multiplicative statement proved is the single
equation `unitStalkFun (r • m) = r * unitStalkFun m`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open Stacks.ModuleStalk

universe u

namespace Stacks.Ample

/-- `𝒪_X` regarded as a module over itself: the monoidal unit of `X.Modules`, in Mathlib's
`SheafOfModules.unit` spelling. -/
noncomputable abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The forgetful functor from commutative rings to abelian groups, as the composite through
`RingCat` in which Mathlib states filtered-colimit preservation. -/
noncomputable abbrev forgetCommRingToAb : CommRingCat.{u} ⥤ Ab.{u} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} Ab.{u}

variable (X : Scheme.{u}) (x : X)

/-- **The stalk of `𝒪_X` as an abelian group is the stalk of `𝒪_X` as a ring.** The underlying
`Ab`-valued presheaf of `𝒪_X` regarded as a module over itself is `X.presheaf` followed by the
forgetful functor, so both stalks are colimits of one diagram, taken before and after that
functor; the functor preserves filtered colimits and the neighbourhoods of `x` are filtered. -/
noncomputable def unitStalkIso :
    TopCat.Presheaf.stalk (C := Ab.{u}) (unitModule X).presheaf x ≅
      forgetCommRingToAb.obj (X.presheaf.stalk x) :=
  (preservesColimitIso forgetCommRingToAb ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

/-- The comparison of `unitStalkIso` as a bare function to `𝒪_{X,x}`. -/
noncomputable def unitStalkFun :
    TopCat.Presheaf.stalk (C := Ab.{u}) (unitModule X).presheaf x → X.presheaf.stalk x :=
  fun m => (unitStalkIso X x).hom m

/-- **The germ compatibility.** The comparison sends the germ of a section of `𝒪_X`, taken in
`Ab`, to the germ of that same section taken in `CommRingCat`. -/
theorem unitStalkFun_germ (U : X.Opens) (hx : x ∈ U) (t : Γ(unitModule X, U)) :
    unitStalkFun X x (((unitModule X).presheaf.germ U x hx).hom t) =
      (X.presheaf.germ U x hx).hom (show Γ(X, U) from t) :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv (G := forgetCommRingToAb)
      (F := (OpenNhds.inclusion x).op ⋙ X.presheaf) (j := op ⟨U, hx⟩)) t

/-- `unitStalkFun_germ` for global sections. -/
theorem unitStalkFun_Γgerm (t : Γ(unitModule X, ⊤)) :
    unitStalkFun X x (((unitModule X).presheaf.Γgerm x).hom t) =
      (X.presheaf.Γgerm x).hom (show Γ(X, ⊤) from t) :=
  unitStalkFun_germ X x ⊤ True.intro t

/-- `unitStalkFun` is additive. -/
theorem unitStalkFun_add (m m' : TopCat.Presheaf.stalk (C := Ab.{u}) (unitModule X).presheaf x) :
    unitStalkFun X x (m + m') = unitStalkFun X x m + unitStalkFun X x m' := map_add _ m m'

/-- Scaling a section of `𝒪_X` by a section of `𝒪_X` is multiplying it. -/
theorem smul_eq_mul_unitModule (U : X.Opens) (a t : Γ(X, U)) :
    (a • (show Γ(unitModule X, U) from t) : Γ(unitModule X, U)) =
      show Γ(unitModule X, U) from a * t := rfl

/-- Restricting a section to a smaller neighbourhood of `y` does not change its germ. -/
private theorem germ_res_eq_of_germ_eq {C : Type*} [Category C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] {T : TopCat} (F : T.Presheaf C) {y : T} {V W : Opens T} (h : W ≤ V)
    (hyW : y ∈ W) {t : ToType (F.obj (op V))} {m : ToType (F.stalk y)}
    (ht : ConcreteCategory.hom (F.germ V y (h hyW)) t = m) :
    ConcreteCategory.hom (F.germ W y hyW) (ConcreteCategory.hom (F.map (homOfLE h).op) t) = m := by
  rw [TopCat.Presheaf.germ_res_apply, ht]

/-- **The comparison turns the `𝒪_{X,x}`-action into multiplication.** Both sides are reduced to
germs on a common neighbourhood, where the action is multiplication of sections. -/
theorem unitStalkFun_smul (r : X.presheaf.stalk x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (unitModule X).presheaf x) :
    unitStalkFun X x (r • m) = r * unitStalkFun X x m := by
  obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq (unitModule X).presheaf m
  obtain ⟨W, hxW, a, ha⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  have hxU : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have hm := germ_res_eq_of_germ_eq (unitModule X).presheaf (inf_le_left : V ⊓ W ≤ V) hxU ht
  have hr := germ_res_eq_of_germ_eq X.presheaf (inf_le_right : V ⊓ W ≤ W) hxU ha
  rw [← hm, ← hr, ← germ_smul, unitStalkFun_germ, unitStalkFun_germ]
  exact map_mul (X.presheaf.germ (V ⊓ W) x hxU).hom _ _

/-- `unitStalkFun` is surjective. -/
theorem unitStalkFun_surjective : Function.Surjective (unitStalkFun X x) :=
  fun y => ⟨(unitStalkIso X x).inv y, ConcreteCategory.congr_hom (unitStalkIso X x).inv_hom_id y⟩

/-- **The identification, in full.** The stalk at `x` of `𝒪_X` regarded as a module over itself
is `𝒪_{X,x}` regarded as a module over itself, `𝒪_{X,x}`-linearly. The left-hand side is the
object of which `Stacks.ModuleStalk.maximalSmul` is a submodule and the right-hand side is the
ring of which `IsLocalRing.maximalIdeal` is an ideal, so this is what relates the two. -/
noncomputable def unitStalkEquiv :
    TopCat.Presheaf.stalk (C := Ab.{u}) (unitModule X).presheaf x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x where
  toFun := unitStalkFun X x
  map_add' := unitStalkFun_add X x
  map_smul' r m := (unitStalkFun_smul X x r m).trans (smul_eq_mul r (unitStalkFun X x m)).symm
  invFun y := (unitStalkIso X x).inv y
  left_inv m := ConcreteCategory.congr_hom (unitStalkIso X x).hom_inv_id m
  right_inv y := ConcreteCategory.congr_hom (unitStalkIso X x).inv_hom_id y

/-- `unitStalkEquiv` is given by `unitStalkFun`. -/
@[simp] theorem unitStalkEquiv_apply
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (unitModule X).presheaf x) :
    unitStalkEquiv X x m = unitStalkFun X x m := rfl

/-- **The comparison carries `𝔪_x · (𝒪_X)_x` into `𝔪_x`.** Every element of the former is a sum
of products `r • m` with `r` in the maximal ideal, and the comparison turns those into multiples
of `r`. -/
theorem mem_maximalIdeal_of_mem_maximalSmul
    {m : TopCat.Presheaf.stalk (C := Ab.{u}) (unitModule X).presheaf x}
    (hm : m ∈ maximalSmul (unitModule X) x) :
    unitStalkFun X x m ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro s hs n _
    rw [unitStalkFun_smul]
    exact Ideal.mul_mem_right _ _ hs
  · intro y z hy hz
    rw [unitStalkFun_add]
    exact add_mem hy hz

/-- **The germ of `1` avoids `𝔪_x · (𝒪_X)_x`.** Equivalently `X_1 = X`: the unit section of the
structure sheaf vanishes nowhere. The comparison sends that germ to `1 ∈ 𝒪_{X,x}`, which is a
unit and so is outside the maximal ideal, while `𝔪_x · (𝒪_X)_x` lands inside it. -/
theorem Γgerm_notMem_maximalSmul_of_eq_one (t : Γ(unitModule X, ⊤))
    (ht : (1 : Γ(X, ⊤)) = show Γ(X, ⊤) from t) :
    ((unitModule X).presheaf.Γgerm x).hom t ∉ maximalSmul (unitModule X) x := by
  intro h
  have hmem := mem_maximalIdeal_of_mem_maximalSmul X x h
  rw [unitStalkFun_Γgerm, ← ht, map_one] at hmem
  exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one hmem

/-- Multiplying the unit section of `𝒪_X` by a global section `r` gives back `r`. -/
theorem smul_unitModule_one (r : Γ(X, ⊤)) :
    (r • (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤))) : Γ(unitModule X, ⊤)) =
      show Γ(unitModule X, ⊤) from r := mul_one r

/-- **The hypothesis of `Stacks.Ample.isQuasiAffine_iff_isAmpleForPowers`, discharged for the
structure sheaf.** The global section `1` of `𝒪_X` vanishes nowhere, and every global section of
`𝒪_X` is a multiple of it. -/
noncomputable def unitBasis : NonvanishingBasis (unitModule X) where
  gen := show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤))
  nonvanishing :=
    Set.eq_univ_of_forall fun y => Γgerm_notMem_maximalSmul_of_eq_one X y _ rfl
  surjective t := ⟨_, smul_unitModule_one X (show Γ(X, ⊤) from t)⟩

end Stacks.Ample

end
