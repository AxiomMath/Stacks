module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Situation
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle

/-!
# The situation preceding the key formula exists

Let `X` be an integral, locally Noetherian scheme, let `L` and `N` be invertible `𝒪_X`-modules and
let `s` and `t` be nonzero meromorphic sections of `L` and `N`, given by their values in the
generic stalks. This file builds a `Stacks.Chow.KeyFormulaSituation L N` whose two sections are
`s` and `t`, so that the key formula Stacks 0AYC applies to any such data.

Two things have to be produced: the family `{Z_i}` of prime divisors and the local generators.

The family is forced by the condition `isCoordinateAt_one_of_notMem`, which asks that `s`
generate `L` and `t` generate `N` at the generic point of every prime divisor outside the family;
the smallest family satisfying it is the set of prime divisors along which one of the two fails to
generate, and that is the family taken here. Its local finiteness is the geometric content: a
local trivialization of `L` at the generic point expresses `s` by a single rational function `f`,
which is a unit section on a nonempty open subset `U`, and at every point of `U` the section `s`
is the generic value of a generator of the stalk. So the members of the family all have their
generic points in the complement of a nonempty open subset, and only finitely many
codimension-one points lie outside such a subset near any given point of `X` — this is the
counting argument of Stacks 02RL, `Stacks.Chow.finite_notMem_coheight_eq_one`. Note that the
family cannot be read off the supports of `div_L(s)` and `div_N(t)`: on a non-normal scheme a
rational function may have order of vanishing zero along a prime divisor without being a unit of
the local ring there.

The generators exist because an invertible module is trivialized near every point, and are chosen
with `Classical.choice`.

## Main definitions

* `Stacks.Chow.keyFormulaSituationOf` — the situation attached to two nonzero meromorphic
  sections of two invertible modules.

## Main results

* `Stacks.Chow.exists_isCoordinateAt_one` — a nonzero meromorphic section generates its module at
  every point of a nonempty open subset.
* `Stacks.Chow.locallyFinite_support_nonGenerating` — the prime divisors along which one of the
  two sections fails to generate form a locally finite family.
* `Stacks.Chow.exists_keyFormulaSituation` — the situation of Stacks 0AYB exists for any two
  nonzero meromorphic sections of two invertible modules.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02RL](https://stacks.math.columbia.edu/tag/02RL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-! ### Where a meromorphic section generates its module -/

section Generates

variable {L : X.Modules}

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- A module trivialized near `x` has a basis of its stalk at `x`. -/
theorem exists_isStalkBasis {x : X} (hL : IsTrivializedNear L x) :
    ∃ m : L.presheaf.stalk x, IsStalkBasis L x m := by
  obtain ⟨W, hxW, e, he⟩ := hL
  exact ⟨L.presheaf.germ W x hxW e, he x hxW⟩

omit [IsLocallyNoetherian X] in
/-- A meromorphic section whose coordinate at `x` is the image of a unit of `𝒪_{X, x}` is the
generic value of a generator of `L_x`: rescaling the basis by that unit gives a basis in which
the coordinate is `1`. -/
theorem isCoordinateAt_one_of_isUnit {x : X} {s : L.presheaf.stalk (genericPoint X)}
    {u : X.presheaf.stalk x} (hu : IsUnit u)
    (ha : IsCoordinateAt L x s (algebraMap (X.presheaf.stalk x) X.functionField u)) :
    IsCoordinateAt L x s 1 := by
  obtain ⟨m, hm, hsa⟩ := ha
  refine ⟨u • m, hm.smul_of_isUnit hu, ?_⟩
  rw [toGenericStalk_smul, one_smul]
  exact hsa

omit [IsLocallyNoetherian X] in
/-- **A nonzero meromorphic section generates its module over a nonempty open subset.** A
trivialization of `L` at the generic point expresses `s` by a single rational function, which is
a unit section over a nonempty open subset; there `s` is the generic value of a generator of the
stalk. -/
theorem exists_isCoordinateAt_one (hL : IsTrivializedNear L (genericPoint X))
    {s : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ z ∈ U, IsCoordinateAt L z s 1 := by
  obtain ⟨W, hηW, e, he⟩ := hL
  obtain ⟨f, hf⟩ := (he _ hηW).surjective s
  replace hf : f • L.presheaf.germ W (genericPoint X) hηW e = s := hf
  have hf0 : f ≠ 0 := fun h => hs (by rw [← hf, h, zero_smul])
  obtain ⟨U, -, f', hUne, hgerm, hunit⟩ := exists_isUnit_germ_eq X f hf0
  have hηU : genericPoint X ∈ U := genericPoint_mem_of_mem hUne.some.2
  refine ⟨W ⊓ U, ⟨hηW, hηU⟩, fun z hz => ?_⟩
  refine isCoordinateAt_one_of_isUnit (u := X.presheaf.germ U z hz.2 f')
    (hunit.map (X.presheaf.germ U z hz.2).hom) ⟨L.presheaf.germ W z hz.1 e, he z hz.1, ?_⟩
  rw [X.algebraMap_germ_eq_germToFunctionField hz.2 f', hgerm,
    toGenericStalk_germ hz.1 hηW]
  exact hf.symm

end Generates

/-! ### Counting codimension-one points outside an open subset -/

/-- **Stacks 02RL, the counting step.** Every point of `X` has an open neighbourhood containing
only finitely many codimension-one points outside a given open subset `U` through the generic
point: on an affine neighbourhood this is
`Stacks.Chow.finite_notMem_coheight_eq_one`. -/
theorem exists_isOpen_finite_notMem (U : X.Opens) (hU : genericPoint X ∈ U) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ {z : X | z ∈ V ∧ z ∉ U ∧ coheight z = 1}.Finite := by
  obtain ⟨V, hV, hxV⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨W, hW, hxW⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨(V : Set X), V.isOpen, hxV, ?_⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace V.toScheme := noetherianSpace_of_isAffineOpen V hV
  have : Nonempty (V.ι ⁻¹ᵁ U) := ⟨⟨⟨genericPoint X, genericPoint_mem_of_mem hxV⟩, hU⟩⟩
  have hfin := finite_notMem_coheight_eq_one (X := V.toScheme) (V.ι ⁻¹ᵁ U)
  refine (hfin.image fun w => (V.ι.base w : X)).subset ?_
  rintro z ⟨hzV, hzU, hzc⟩
  obtain ⟨w, hw⟩ : ∃ w : ↥V.toScheme, V.ι.base w = z := ⟨⟨z, hzV⟩, rfl⟩
  have hco : coheight (V.ι.base w) = coheight w := coheight_eq_of_isOpenImmersion V.ι
  rw [hw] at hco
  exact ⟨w, ⟨fun h => hzU (by rw [← hw]; exact h), by rw [← hco]; exact hzc⟩, hw⟩

/-! ### The situation attached to two nonzero meromorphic sections -/

section Exists

variable (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (s : L.presheaf.stalk (genericPoint X)) (t : N.presheaf.stalk (genericPoint X))

/-- **The prime divisors along which `s` or `t` fails to generate form a locally finite family.**
Each of the two sections generates over a nonempty open subset, so the generic points of the
members of the family all lie outside a nonempty open subset, and near any point of `X` only
finitely many codimension-one points do. -/
theorem locallyFinite_support_nonGenerating (hs : s ≠ 0) (ht : t ≠ 0) :
    LocallyFinite fun Z : {Z : PrimeDivisor X //
        ¬(IsCoordinateAt L Z.genericPoint s 1 ∧ IsCoordinateAt N Z.genericPoint t 1)} =>
      (Z : PrimeDivisor X).support := by
  have := isInvertible_presheaf L
  have := isInvertible_presheaf N
  obtain ⟨U, hηU, hUs⟩ :=
    exists_isCoordinateAt_one (isTrivializedNear_of_isInvertible L (genericPoint X)) hs
  obtain ⟨U', hηU', hU't⟩ :=
    exists_isCoordinateAt_one (isTrivializedNear_of_isInvertible N (genericPoint X)) ht
  intro x
  obtain ⟨V, hVopen, hxV, hfin⟩ := exists_isOpen_finite_notMem (U ⊓ U') ⟨hηU, hηU'⟩ x
  refine ⟨V, hVopen.mem_nhds hxV, Set.Finite.of_finite_image (hfin.subset ?_)
    (PrimeDivisor.genericPoint_injective.comp Subtype.val_injective).injOn⟩
  rintro - ⟨⟨Z, hZ⟩, hmem, rfl⟩
  obtain ⟨p, hpZ, hpV⟩ := hmem
  replace hpZ : p ∈ closure ({Z.genericPoint} : Set X) := Z.support_eq_closure ▸ hpZ
  refine ⟨(specializes_iff_mem_closure.mpr hpZ).mem_open hVopen hpV, fun hmemU => ?_,
    Z.coheight_genericPoint⟩
  exact hZ ⟨hUs _ hmemU.1, hU't _ hmemU.2⟩

/-- **The situation preceding the key formula attached to two nonzero meromorphic sections,
Stacks 0AYB.** The family of prime divisors is the one along whose members `s` fails to generate
`L` or `t` fails to generate `N`, and the local generators are chosen with `Classical.choice`. -/
def keyFormulaSituationOf (hs : s ≠ 0) (ht : t ≠ 0) : KeyFormulaSituation L N :=
  have := isInvertible_presheaf L
  have := isInvertible_presheaf N
  { sectionL := s
    sectionL_ne_zero := hs
    sectionN := t
    sectionN_ne_zero := ht
    Index := {Z : PrimeDivisor X //
      ¬(IsCoordinateAt L Z.genericPoint s 1 ∧ IsCoordinateAt N Z.genericPoint t 1)}
    component := Subtype.val
    component_injective := Subtype.val_injective
    locallyFinite_component := locallyFinite_support_nonGenerating L N s t hs ht
    isCoordinateAt_one_of_notMem := fun Z hZ => by
      by_contra h
      exact hZ ⟨Z, h⟩ rfl
    localGeneratorL := fun i =>
      (exists_isStalkBasis
        (isTrivializedNear_of_isInvertible L (i : PrimeDivisor X).genericPoint)).choose
    localGeneratorN := fun i =>
      (exists_isStalkBasis
        (isTrivializedNear_of_isInvertible N (i : PrimeDivisor X).genericPoint)).choose
    isStalkBasis_localGeneratorL := fun i =>
      (exists_isStalkBasis
        (isTrivializedNear_of_isInvertible L (i : PrimeDivisor X).genericPoint)).choose_spec
    isStalkBasis_localGeneratorN := fun i =>
      (exists_isStalkBasis
        (isTrivializedNear_of_isInvertible N (i : PrimeDivisor X).genericPoint)).choose_spec }

/-- The section of `L` of `Stacks.Chow.keyFormulaSituationOf L N s t hs ht` is `s`. -/
@[simp]
theorem keyFormulaSituationOf_sectionL (hs : s ≠ 0) (ht : t ≠ 0) :
    (keyFormulaSituationOf L N s t hs ht).sectionL = s :=
  rfl

/-- The section of `N` of `Stacks.Chow.keyFormulaSituationOf L N s t hs ht` is `t`. -/
@[simp]
theorem keyFormulaSituationOf_sectionN (hs : s ≠ 0) (ht : t ≠ 0) :
    (keyFormulaSituationOf L N s t hs ht).sectionN = t :=
  rfl

/-- **The situation of Stacks 0AYB exists for any two nonzero meromorphic sections.** -/
theorem exists_keyFormulaSituation (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ ℱ : KeyFormulaSituation L N, ℱ.sectionL = s ∧ ℱ.sectionN = t :=
  ⟨keyFormulaSituationOf L N s t hs ht, rfl, rfl⟩

end Exists

end Stacks.Chow

end
