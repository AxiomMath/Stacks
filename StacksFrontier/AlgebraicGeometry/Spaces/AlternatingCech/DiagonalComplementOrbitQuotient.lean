module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.ULift
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionSpacesEtaleOrbitQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# The quotient of `W_p` by the symmetric group on the spaces-étale site

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S` and
let `W = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `n` factors be the complement of the diagonals
in the `n`-fold self-product, an object of the spaces-étale site of `X` carrying a free action
of the symmetric group on `n` letters by permuting the factors. With `n = p + 1` this is the
space `W_p` of Stacks 0726 with its action of `S_{p+1}`.

This file forms the quotient `U_p = W_p/S_{p+1}` and proves that the projection
`W_p ⟶ U_p` exhibits the final object of the spaces-étale site of `U_p` as that quotient, in
the sense of `CategoryTheory.IsOrbitQuotient`, so that `W_p` is an `S_{p+1}`-torsor over it.

Two things are needed beyond what the construction of `W_p` already provides. The first is the
action of the symmetric group on the *presheaf of points* of `W_p` together with its freeness
over the test objects of the big fppf site, `IsFreeOnNonemptyPoints`: Tag 071S, which makes
the quotient an algebraic space, reads freeness there, whereas
`AlgebraicGeometry.Space.SpacesEtale.eq_one_of_comp_diagonalComplementAut` states it for the
objects of the spaces-étale site of `X`, which are not the test objects. The second is the
refinement from the fppf topology to the étale one, which is
`AlgebraicGeometry.Space.translationSieve_mem_of_orbitSieve`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementMulAction` is the action of the
  symmetric group on the points of `W` over a test object, by permuting the factors of `U^n`.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotient` is the quotient
  `U_p = W/S_n` as an algebraic space over `S`, with
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementEtaleSource` the space `W` read as an
  object of the spaces-étale site of that quotient and
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientAut` the action of the
  symmetric group on it by automorphisms.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isNaturalAction_diagonalComplement`: the pointwise
  action is compatible with restriction.
* `AlgebraicGeometry.Space.SpacesEtale.eq_one_of_smul_eq_diagonalComplement` and
  `AlgebraicGeometry.Space.SpacesEtale.isFreeOnNonemptyPoints_diagonalComplement`: **the
  pointwise action of the symmetric group on `W` is free** over the test objects whose
  underlying scheme is nonempty. This is the re-derivation of Stacks 0726's freeness in
  presheaf language.
* `AlgebraicGeometry.Space.SpacesEtale.actsFreelyOnObject_diagonalComplement`: the action is
  free in the sense of `CategoryTheory.ActsFreelyOnObject`, over the objects of the
  spaces-étale site of the quotient.
* `AlgebraicGeometry.Space.SpacesEtale.isOrbitQuotient_diagonalComplement`: **the projection
  `W ⟶ W/S_n` exhibits the final object of the spaces-étale site of `W/S_n` as that
  quotient**, and `AlgebraicGeometry.Space.SpacesEtale.isTorsorObject_diagonalComplement`:
  **`W` is an `S_n`-torsor over it.**

## Implementation notes

The symmetric group is taken as `ULift.{u} (Equiv.Perm (Fin n))`, the group `S_n` lifted to
the universe of the schemes of the site. That is forced by Tag 071S, whose group must lie in
the universe of the site: the relation presenting the quotient is the disjoint union of one
piece for each group element, so the group indexes a coproduct *inside* the site. Lifting the
universe changes neither the group, `ULift.{u} (Equiv.Perm (Fin n))` being isomorphic to
`Equiv.Perm (Fin n)` by `MulEquiv.ulift`, nor the action, which is the one of
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementPerm` read through that isomorphism.

Freeness is proved from the geometry exactly as Stacks 0726 does, but with the test object in
place of an object of the site: a section of `W` over a test object fixed by a permutation `σ`
gives, at any point of the test object, a point of `W` at which the factors of index `i` and
`σ⁻¹ i` of `U^n` agree, whereas the points of `W` avoid all the diagonals. The two factors are
compared through the fibre square `U ×_X U`, whose sections are determined by their
projections (`AlgebraicGeometry.Space.SpacesEtale.prodTwo_section_ext`), and the passage from
a section to a point is `AlgebraicGeometry.Space.exists_fieldValuedPoint_schemePoint_eq`
together with `AlgebraicGeometry.Space.FieldValuedPoint.class_map_eq_of_app_eq`.

Surjectivity of `f`, which Stacks 0726 also assumes, is not used: it is what makes the Koszul
complex a resolution, not what makes the action free.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)

/-! ### The pointwise action of the symmetric group on `W` -/

/-- **The action of the symmetric group on `n` letters on the points of `W` over a test
object**, by permuting the factors of `U^n`. The group is lifted to the universe of the site,
as Tag 071S requires. -/
instance diagonalComplementMulAction (T : (BigFppfOver B S hS)ᵒᵖ) :
    MulAction (ULift.{u} (Equiv.Perm (Fin n)))
      ((underlying B S hS X (diagonalComplement B S hS X U n hsep)).1.obj T) where
  smul σ x := ((toSpaces B S hS X).map
    (diagonalComplementPerm B S hS X U n hsep σ.down)).hom.app T x
  one_smul x := by
    change ((toSpaces B S hS X).map
      (diagonalComplementPerm B S hS X U n hsep (1 : Equiv.Perm (Fin n)))).hom.app T x = x
    rw [diagonalComplementPerm_one, CategoryTheory.Functor.map_id]
    rfl
  mul_smul σ τ x := by
    change ((toSpaces B S hS X).map
        (diagonalComplementPerm B S hS X U n hsep (σ.down * τ.down))).hom.app T x = _
    rw [← diagonalComplementPerm_comp, hom_toSpaces_map_comp]
    rfl

/-- A permutation `σ` acts on a point of `W` over `T` by the component at `T` of the
automorphism `diagonalComplementPerm σ` of `W`. -/
@[simp]
theorem diagonalComplementMulAction_smul {T : (BigFppfOver B S hS)ᵒᵖ}
    (σ : ULift.{u} (Equiv.Perm (Fin n)))
    (x : (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1.obj T) :
    σ • x = ((toSpaces B S hS X).map
      (diagonalComplementPerm B S hS X U n hsep σ.down)).hom.app T x :=
  rfl

/-- **The pointwise action of the symmetric group on `W` is natural**: it commutes with the
restriction maps, being induced by a morphism of presheaves. -/
theorem isNaturalAction_diagonalComplement :
    IsNaturalAction B S hS (ULift.{u} (Equiv.Perm (Fin n)))
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 :=
  fun f σ x => (NatTrans.naturality_apply ((toSpaces B S hS X).map
    (diagonalComplementPerm B S hS X U n hsep σ.down)).hom f x).symm

/-! ### Freeness of the pointwise action -/

/-- The presheaf morphism of the diagonal `U ⟶ U ×_X U` followed by the first projection is
the identity. -/
theorem hom_toSpaces_map_diagTwo_comp_fst :
    ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom = 𝟙 _ := by
  rw [← hom_toSpaces_map_comp, diagTwo_comp_fst]
  simp

/-- The presheaf morphism of the diagonal `U ⟶ U ×_X U` followed by the second projection is
the identity. -/
theorem hom_toSpaces_map_diagTwo_comp_snd :
    ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom = 𝟙 _ := by
  rw [← hom_toSpaces_map_comp, diagTwo_comp_snd]
  simp

/-- The presheaf morphism of `projPair i j` followed by the first projection is the projection
onto the factor of index `i`. -/
theorem hom_toSpaces_map_projPair_comp_fst (i j : Fin n) :
    ((toSpaces B S hS X).map (projPair B S hS X U n i j)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom =
      ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i)).hom := by
  rw [← hom_toSpaces_map_comp, projPair_comp_fst]

/-- The presheaf morphism of `projPair i j` followed by the second projection is the
projection onto the factor of index `j`. -/
theorem hom_toSpaces_map_projPair_comp_snd (i j : Fin n) :
    ((toSpaces B S hS X).map (projPair B S hS X U n i j)).hom ≫
      ((toSpaces B S hS X).map
        (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom =
      ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) j)).hom := by
  rw [← hom_toSpaces_map_comp, projPair_comp_snd]

/-- **The sections of `W` avoid the diagonals**: over a test object with nonempty underlying
scheme, a section of `W` has distinct components of distinct indices `i` and `j` in `U`. A
point of the test object would otherwise give a point of `W` on the locus where those two
factors agree. -/
theorem comp_diagonalComplementι_π_ne {A : BigFppfOver B S hS}
    (hA : Nonempty ((BigFppfOver.toScheme B S hS).obj A))
    (y : yoneda.obj A ⟶ (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1)
    {i j : Fin n} (hij : i ≠ j) :
    (y ≫ ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom) ≫
        ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) j)).hom ≠
      (y ≫ ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom) ≫
        ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i)).hom := by
  intro hπ
  have hdfst := hom_toSpaces_map_diagTwo_comp_fst B S hS X U
  have hdsnd := hom_toSpaces_map_diagTwo_comp_snd B S hS X U
  have hpfst := hom_toSpaces_map_projPair_comp_fst B S hS X U n i j
  have hpsnd := hom_toSpaces_map_projPair_comp_snd B S hS X U n i j
  set iota := ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom
  set ppair := ((toSpaces B S hS X).map (projPair B S hS X U n i j)).hom
  set dg := ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom
  set pr₁ := ((toSpaces B S hS X).map
    (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom
  set pr₂ := ((toSpaces B S hS X).map
    (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom
  set πi := ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i)).hom
  set πj := ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) j)).hom
  set ξ := y ≫ iota with hξ
  have hfstEq : (ξ ≫ ppair) ≫ pr₁ = (ξ ≫ πi ≫ dg) ≫ pr₁ := by
    simp only [Category.assoc, hdfst, Category.comp_id, hpfst]
  have hsndEq : (ξ ≫ ppair) ≫ pr₂ = (ξ ≫ πi ≫ dg) ≫ pr₂ := by
    simp only [Category.assoc, hdsnd, Category.comp_id, hpsnd]
    simpa only [Category.assoc] using hπ
  obtain ⟨z⟩ := hA
  obtain ⟨p, -⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS A z
  have at_p : ∀ {k₁ k₂ : yoneda.obj A ⟶ (underlying B S hS X U).1}, k₁ = k₂ →
      ConcreteCategory.hom (NatTrans.app k₁
        (op (FieldValuedPoint.siteObject B S hS _ p))) p.value =
      ConcreteCategory.hom (NatTrans.app k₂
        (op (FieldValuedPoint.siteObject B S hS _ p))) p.value := fun h => by rw [h]
  have hsec := FieldValuedPoint.class_map_eq_of_app_eq B S hS (ξ ≫ ppair) (ξ ≫ πi ≫ dg) p
    (prodTwo_section_ext B S hS X U (at_p hfstEq) (at_p hsndEq))
  refine (mem_diagonalComplementPoints_iff B S hS X U n _).1
    (mem_diagonalComplementPoints_pointsMap_diagonalComplementι B S hS X U n hsep
      (pointsMap B S hS _ y (FieldValuedPoint.class B S hS _ p))) i j hij ?_
  refine ⟨pointsMap B S hS _ (ξ ≫ πi) (FieldValuedPoint.class B S hS _ p), ?_⟩
  calc pointsMap B S hS _ dg (pointsMap B S hS _ (ξ ≫ πi)
          (FieldValuedPoint.class B S hS _ p))
      = pointsMap B S hS _ ((ξ ≫ πi) ≫ dg) (FieldValuedPoint.class B S hS _ p) :=
        (congrFun (pointsMap_comp B S hS _ (ξ ≫ πi) dg)
          (FieldValuedPoint.class B S hS _ p)).symm
    _ = pointsMap B S hS _ (ξ ≫ πi ≫ dg) (FieldValuedPoint.class B S hS _ p) := by
        rw [Category.assoc]
    _ = pointsMap B S hS _ (ξ ≫ ppair) (FieldValuedPoint.class B S hS _ p) := hsec.symm
    _ = pointsMap B S hS _ ppair (pointsMap B S hS _ ξ
          (FieldValuedPoint.class B S hS _ p)) :=
        congrFun (pointsMap_comp B S hS _ ξ ppair) (FieldValuedPoint.class B S hS _ p)
    _ = pointsMap B S hS _ ppair (pointsMap B S hS _ iota
          (pointsMap B S hS _ y (FieldValuedPoint.class B S hS _ p))) := by
        rw [hξ, congrFun (pointsMap_comp B S hS _ y iota) (FieldValuedPoint.class B S hS _ p)]
        rfl

/-- **A section of `W` over a test object with nonempty underlying scheme fixed by a
permutation forces that permutation to be trivial.** This is Stacks 0726's freeness of the
action of `S_n` on `W_p`, re-derived for the test objects of the big fppf site rather than for
the objects of the spaces-étale site of `X`.

Pick a letter `i` moved by `σ`. The section, read as a morphism from the presheaf represented
by the test object, is fixed by the permutation, so its two components of index `i` and
`σ⁻¹ i` into `U` agree; hence its composite into the fibre square `U ×_X U` factors through
the diagonal. A point of the test object then gives a point of `W` lying on the locus where
those two factors agree, which the points of `W` avoid. -/
theorem eq_one_of_smul_eq_diagonalComplement {A : BigFppfOver B S hS}
    (hA : Nonempty ((BigFppfOver.toScheme B S hS).obj A))
    (x : (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1.obj (op A))
    (σ : ULift.{u} (Equiv.Perm (Fin n))) (h : σ • x = x) : σ = 1 := by
  by_contra hσ
  obtain ⟨i, hi⟩ : ∃ i : Fin n, σ.down⁻¹ i ≠ i := by
    by_contra hall
    exact hσ (ULift.ext
      (inv_eq_one.1 (Equiv.ext fun j => not_ne_iff.1 fun hne => hall ⟨j, hne⟩)))
  have hfix : yonedaEquiv.symm x ≫ ((toSpaces B S hS X).map
      (diagonalComplementPerm B S hS X U n hsep σ.down)).hom = yonedaEquiv.symm x :=
    yonedaEquiv.injective <| by
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact h
  have hιperm : ((toSpaces B S hS X).map
        (diagonalComplementPerm B S hS X U n hsep σ.down)).hom ≫
      ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom =
      ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom ≫
        ((toSpaces B S hS X).map (permProd U n σ.down)).hom := by
    rw [← hom_toSpaces_map_comp, ← hom_toSpaces_map_comp, diagonalComplementPerm_ι]
  have hπcomp : ((toSpaces B S hS X).map (permProd U n σ.down)).hom ≫
      ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i)).hom =
      ((toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) (σ.down⁻¹ i))).hom := by
    rw [← hom_toSpaces_map_comp, permProd_π]
  have hperm : (yonedaEquiv.symm x ≫
      ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom) ≫
        ((toSpaces B S hS X).map (permProd U n σ.down)).hom =
      yonedaEquiv.symm x ≫
        ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom := by
    rw [Category.assoc, ← hιperm, ← Category.assoc, hfix]
  exact comp_diagonalComplementι_π_ne B S hS X U n hsep hA (yonedaEquiv.symm x) (Ne.symm hi)
    (by rw [← hπcomp, ← Category.assoc, hperm])

/-- **The pointwise action of the symmetric group on `W` is free** over the test objects whose
underlying scheme is nonempty, which is the hypothesis of Tag 071S. -/
theorem isFreeOnNonemptyPoints_diagonalComplement :
    IsFreeOnNonemptyPoints B S hS (ULift.{u} (Equiv.Perm (Fin n)))
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 := by
  intro T hT
  refine { left_cancel' := fun a b c hbc => smul_left_cancel a hbc,
           right_cancel' := fun a b c hc => ?_ }
  exact (inv_mul_eq_one.1 (eq_one_of_smul_eq_diagonalComplement B S hS X U n hsep hT c
    (b⁻¹ * a) (by rw [mul_smul, hc, inv_smul_smul]))).symm

/-! ### The quotient `U_p` and the orbit quotient on its spaces-étale site -/

section Quotient

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The quotient `U_p = W/S_n`** of `W` by the symmetric group, as an algebraic space over
`S`: Tag 071S applies, the pointwise action of the symmetric group being free over the test
objects with nonempty underlying scheme. -/
def diagonalComplementQuotient : AlgebraicSpaces B S hS :=
  orbitQuotientSpace (isNaturalAction_diagonalComplement B S hS X U n hsep)
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)

/-- `W` as an object of the spaces-étale site of its own quotient `W/S_n`, the quotient
morphism being étale. -/
def diagonalComplementEtaleSource :
    SpacesEtale B S hS (diagonalComplementQuotient B S hS X U n hsep) :=
  orbitQuotientEtaleSource (isNaturalAction_diagonalComplement B S hS X U n hsep)
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)

/-- The action of the symmetric group on `W` by automorphisms, read in the spaces-étale site
of the quotient `W/S_n`. -/
def diagonalComplementQuotientAut :
    ULift.{u} (Equiv.Perm (Fin n)) →*
      Aut (diagonalComplementEtaleSource B S hS X U n hsep) :=
  orbitQuotientAut (isNaturalAction_diagonalComplement B S hS X U n hsep)
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)

/-- **The projection `W ⟶ W/S_n` exhibits the final object of the spaces-étale site of
`W/S_n` as the quotient of `W` by the symmetric group**, in the sense of
`CategoryTheory.IsOrbitQuotient`.

With `n = p + 1` this is the space `W_p` of Stacks 0726 with its action of `S_{p+1}`: the
étale-site projection `W_p ⟶ U_p = W_p/S_{p+1}` is the orbit quotient in the spaces-étale site
of the algebraic space `U_p`. -/
theorem isOrbitQuotient_diagonalComplement :
    IsOrbitQuotient (diagonalComplementQuotientAut B S hS X U n hsep)
      (topology B S hS (diagonalComplementQuotient B S hS X U n hsep))
      ((final_isTerminal B S hS (diagonalComplementQuotient B S hS X U n hsep)).from
        (diagonalComplementEtaleSource B S hS X U n hsep)) :=
  isOrbitQuotient_orbitQuotientAut (isNaturalAction_diagonalComplement B S hS X U n hsep)
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)

/-- **`W` is an `S_n`-torsor over the final object of the spaces-étale site of `W/S_n`.** This
is the instantiation of `CategoryTheory.IsOrbitQuotient.isTorsorObject` at the spaces-étale
site: the morphisms to `W` cover every object, any two of them are translates of each other
locally, and the translating permutation is unique away from the objects covered by the empty
sieve. -/
theorem isTorsorObject_diagonalComplement :
    IsTorsorObject (diagonalComplementQuotientAut B S hS X U n hsep)
      (topology B S hS (diagonalComplementQuotient B S hS X U n hsep)) :=
  isTorsorObject_orbitQuotientAut (isNaturalAction_diagonalComplement B S hS X U n hsep)
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)

/-- **The action of the symmetric group on `W` is free in the spaces-étale site of `W/S_n`.**
-/
theorem actsFreelyOnObject_diagonalComplement :
    ActsFreelyOnObject (diagonalComplementQuotientAut B S hS X U n hsep)
      (topology B S hS (diagonalComplementQuotient B S hS X U n hsep)) :=
  actsFreelyOnObject_orbitQuotientAut
    (isNaturalAction_diagonalComplement B S hS X U n hsep)
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)

end Quotient

end AlgebraicGeometry.Space.SpacesEtale

end
