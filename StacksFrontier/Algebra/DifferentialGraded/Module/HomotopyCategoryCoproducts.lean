module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory
public import StacksFrontier.Algebra.DGA.Cone

/-!
# The quotient functor to the homotopy category preserves direct sums

For a differential graded algebra `(A, d)` over a commutative ring `R`, the canonical functor
`Mod_{(A,d)} ⥤ K(A, d)` to the homotopy category carries a direct sum of differential graded
modules to a direct sum in the homotopy category. The point is the uniqueness half: two
morphisms out of a direct sum that agree on every summand agree, because a homotopy out of a
direct sum is the same thing as a family of homotopies out of the summands.

That statement is proved here without any reference to a model of the direct sum. The device is
an auxiliary differential graded module `nullHomotopyObj N`, the cone of the identity of the
shift `N[-1]`, whose maps *in* classify null-homotopies of maps *to* `N`: a homomorphism
`M ⟶ nullHomotopyObj N` is exactly a pair consisting of a degree `-1` map `h` and the
homomorphism `d ∘ h + h ∘ d` that `h` bounds. Since this object depends on the *target* and not
on the source, a family of null-homotopies of the restrictions of `u : S ⟶ N` to the summands
of `S` assembles, by the universal property of the direct sum alone, into a single map
`S ⟶ nullHomotopyObj N` over `u`, which is a null-homotopy of `u`.

## Main definitions

* `DifferentialGradedModule.nullHomotopyObj`: the cone of the identity of `N[-1]`.
* `DifferentialGradedModule.nullHomotopyProj`: its projection to `N`.

## Main results

* `DifferentialGradedModule.homotopic_zero_iff_exists_comp_nullHomotopyProj`: a homomorphism is
  null-homotopic exactly when it factors through `nullHomotopyProj`.
* `DifferentialGradedModule.jointlyEpi_toHomotopyCategory_of_isColimit_cofan`: the images of the
  coprojections of a direct sum are jointly epimorphic in the homotopy category.
* `DifferentialGradedModule.preservesCoproducts_toHomotopyCategory`: the quotient functor
  preserves colimits indexed by a discrete category on a type in the ambient universe, that is,
  it preserves direct sums.

## Implementation notes

Everything is single-universe: `DifferentialGradedModule A` lives in `Type u` for
`R : Type u`, so the index type of a direct sum is taken in the same universe `u`.

The degree-`n` part of `nullHomotopyObj N` is `N^{n-1} ⊕ N^n` and its differential is
`(z, y) ↦ (-d z + y, d y)`; both come from `coneObject` applied to the identity of
`shift N (-1)`, whose sign `(-1)^{-1} = -1` produces the displayed formula. Because the
underlying module of `shift N (-1)` is that of `N`, the coordinates of `nullHomotopyObj N` are
written with explicit type ascriptions to `N.M`.

## References

* [Stacks Project, Tag 09JR](https://stacks.math.columbia.edu/tag/09JR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

section NullHomotopy

variable {M N : DifferentialGradedModule A}

/-- A homomorphism of differential graded modules is homotopic to another exactly when their
difference is null-homotopic. -/
theorem homotopic_sub_zero_iff (f g : M ⟶ N) : Homotopic (f - g) 0 ↔ Homotopic f g := by
  have hsub (x : M.M) :
      (f - g).toFun x - (0 : M ⟶ N).toFun x = f.toFun x - g.toFun x := by
    rw [Hom.hom_sub_toFun, Hom.hom_zero_toFun, LinearMap.sub_apply,
      LinearMap.zero_apply, sub_zero]
  constructor
  · rintro ⟨h⟩
    exact ⟨h.toLinearMap, h.map_grading, fun x => (hsub x).symm.trans (h.homotopy_eq x)⟩
  · rintro ⟨h⟩
    exact ⟨h.toLinearMap, h.map_grading, fun x => (hsub x).trans (h.homotopy_eq x)⟩

/-- The differential graded module classifying null-homotopies of maps into `N`: the cone of the
identity of the shift `N[-1]`. Its underlying right module is `N ⊕ N`, its degree-`n` part is
`N^{n-1} ⊕ N^n`, and its differential is `(z, y) ↦ (-d z + y, d y)`. -/
noncomputable abbrev nullHomotopyObj (N : DifferentialGradedModule A) :
    DifferentialGradedModule A :=
  coneObject (𝟙 (shift N (-1)))

/-- The degree-`n` part of `nullHomotopyObj N` is `N^{n-1} ⊕ N^n`. -/
theorem mem_nullHomotopyObj_grading (n : ℤ) (x : (nullHomotopyObj N).M) :
    x ∈ (nullHomotopyObj N).grading n ↔
      (x.1 : N.M) ∈ N.grading (n - 1) ∧ (x.2 : N.M) ∈ N.grading n := by
  have h1 : n + (-1 : ℤ) = n - 1 := by omega
  have h2 : n + 1 + (-1 : ℤ) = n := by omega
  have key := coneGrading_mem (K := shift N (-1)) (L := shift N (-1)) n x
  simp only [shift_grading, h1, h2] at key
  exact key

/-- The differential of the shift `N[-1]` is the negative of that of `N`. -/
private theorem shift_neg_one_d_apply (z : (shift N (-1)).M) :
    (shift N (-1)).d z = -N.d (show N.M from z) := by
  rw [shift_d]
  simp only [Units.smul_def, Int.negOnePow_neg, Int.negOnePow_one,
    Units.val_neg, Units.val_one, neg_smul, one_smul, LinearMap.neg_apply]

/-- The first coordinate of the differential of `nullHomotopyObj N`. -/
theorem nullHomotopyObj_d_fst (x : (nullHomotopyObj N).M) :
    ((((nullHomotopyObj N).d x).1 : N.M)) =
      -N.d (show N.M from x.1) + (show N.M from x.2) := by
  rw [show (nullHomotopyObj N).d x = coneD (𝟙 (shift N (-1))) x from rfl, coneD_apply]
  exact congrArg (· + (x.2 : N.M)) (shift_neg_one_d_apply _)

/-- The second coordinate of the differential of `nullHomotopyObj N`. -/
theorem nullHomotopyObj_d_snd (x : (nullHomotopyObj N).M) :
    ((((nullHomotopyObj N).d x).2 : N.M)) = N.d (x.2 : N.M) := by
  rw [show (nullHomotopyObj N).d x = coneD (𝟙 (shift N (-1))) x from rfl, coneD_apply]
  exact (congrArg Neg.neg (shift_neg_one_d_apply _)).trans (neg_neg _)

/-- The projection of `nullHomotopyObj N` onto `N`: the second coordinate. Composing a
homomorphism into `nullHomotopyObj N` with this projection gives the homomorphism bounded by
the homotopy recorded in its first coordinate. -/
noncomputable def nullHomotopyProj (N : DifferentialGradedModule A) :
    nullHomotopyObj N ⟶ N where
  toFun := LinearMap.snd R N.M N.M
  map_smul _ _ := rfl
  map_grading n x hx := ((mem_nullHomotopyObj_grading n x).1 hx).2
  map_d := by
    apply LinearMap.ext
    intro x
    exact nullHomotopyObj_d_snd x

/-- The projection `nullHomotopyProj N` sends an element of `nullHomotopyObj N` to its second
coordinate. -/
@[simp] theorem nullHomotopyProj_toFun_apply (x : (nullHomotopyObj N).M) :
    (nullHomotopyProj N).toFun x = (x.2 : N.M) := rfl

/-- A null-homotopic homomorphism factors through `nullHomotopyProj`. -/
private theorem exists_comp_nullHomotopyProj_of_homotopic_zero {u : M ⟶ N}
    (hu₀ : Homotopic u 0) : ∃ v : M ⟶ nullHomotopyObj N, v ≫ nullHomotopyProj N = u := by
  obtain ⟨h⟩ := hu₀
  have hu (x : M.M) : u.toFun (M.d x) = N.d (u.toFun x) := by
    simpa using LinearMap.congr_fun u.map_d x
  have hh (x : M.M) :
      h.toLinearMap (M.d x) = -N.d (h.toLinearMap x) + u.toFun x := by
    have hx := h.homotopy_eq x
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero] at hx
    rw [hx]
    abel
  refine ⟨{ toFun := (LinearMap.restrictScalars R h.toLinearMap).prod u.toFun
            map_smul := ?_, map_grading := ?_, map_d := ?_ }, ?_⟩
  · intro x a
    exact Prod.ext (map_smul h.toLinearMap (MulOpposite.op a) x) (u.map_smul x a)
  · intro n x hx
    exact (mem_nullHomotopyObj_grading n _).2
      ⟨h.map_grading n x hx, u.map_grading n x hx⟩
  · exact LinearMap.ext fun x => Prod.ext
      ((hh x).trans (nullHomotopyObj_d_fst (N := N)
        ((LinearMap.restrictScalars R h.toLinearMap).prod u.toFun x)).symm)
      ((hu x).trans (nullHomotopyObj_d_snd (N := N)
        ((LinearMap.restrictScalars R h.toLinearMap).prod u.toFun x)).symm)
  · exact Hom.ext (LinearMap.ext fun _ => rfl)

/-- A homomorphism factoring through `nullHomotopyProj` is null-homotopic. -/
private theorem homotopic_zero_of_comp_nullHomotopyProj {u : M ⟶ N} (v : M ⟶ nullHomotopyObj N)
    (hv : v ≫ nullHomotopyProj N = u) : Homotopic u 0 := by
  have hvx (x : M.M) : ((v.toFun x).2 : N.M) = u.toFun x := by
    rw [← hv]
    rfl
  have hvd (x : M.M) : v.toFun (M.d x) = (nullHomotopyObj N).d (v.toFun x) := by
    simpa using LinearMap.congr_fun v.map_d x
  refine ⟨{ toLinearMap :=
              { toFun := fun x => ((v.toFun x).1 : N.M)
                map_add' := fun x y => by rw [map_add]; rfl
                map_smul' := ?_ }
            map_grading := ?_, homotopy_eq := ?_ }⟩
  · intro a x
    have h := v.map_smul x a.unop
    rw [MulOpposite.op_unop] at h
    exact congrArg Prod.fst h
  · intro n x hx
    exact ((mem_nullHomotopyObj_grading n _).1 (v.map_grading n x hx)).1
  · intro x
    have h1 : ((v.toFun (M.d x)).1 : N.M)
        = -N.d (show N.M from (v.toFun x).1) + (show N.M from (v.toFun x).2) := by
      rw [hvd x]
      exact nullHomotopyObj_d_fst (N := N) (v.toFun x)
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero]
    change u.toFun x =
      N.d (show N.M from (v.toFun x).1) + (show N.M from (v.toFun (M.d x)).1)
    rw [h1, hvx x]
    exact (add_neg_cancel_left _ _).symm

/-- A homomorphism of differential graded modules is null-homotopic exactly when it factors
through the projection from the module classifying null-homotopies of maps into its target. -/
theorem homotopic_zero_iff_exists_comp_nullHomotopyProj (u : M ⟶ N) :
    Homotopic u 0 ↔ ∃ v : M ⟶ nullHomotopyObj N, v ≫ nullHomotopyProj N = u :=
  ⟨exists_comp_nullHomotopyProj_of_homotopic_zero, fun ⟨v, hv⟩ =>
    homotopic_zero_of_comp_nullHomotopyProj v hv⟩

end NullHomotopy

section Coproducts

variable {ι : Type u}

/-- The images of the components of a colimit cocone over a discrete diagram of differential
graded modules form a jointly epimorphic family in the homotopy category. -/
theorem jointlyEpi_map_toHomotopyCategory_of_isColimit
    {F : Discrete ι ⥤ DifferentialGradedModule A} {c : Cocone F} (hc : IsColimit c)
    {Y : HomotopyCategory A} (f g : (toHomotopyCategory A).obj c.pt ⟶ Y)
    (h : ∀ j, (toHomotopyCategory A).map (c.ι.app j) ≫ f =
      (toHomotopyCategory A).map (c.ι.app j) ≫ g) :
    f = g := by
  have hf : (toHomotopyCategory A).map ((toHomotopyCategory A).preimage f) = f :=
    (toHomotopyCategory A).map_preimage f
  have hg : (toHomotopyCategory A).map ((toHomotopyCategory A).preimage g) = g :=
    (toHomotopyCategory A).map_preimage g
  set f' := (toHomotopyCategory A).preimage f
  set g' := (toHomotopyCategory A).preimage g
  have hzero : ∀ j, Homotopic (c.ι.app j ≫ (f' - g')) 0 := by
    intro j
    have hj : (toHomotopyCategory A).map (c.ι.app j ≫ f')
        = (toHomotopyCategory A).map (c.ι.app j ≫ g') := by
      rw [Functor.map_comp, Functor.map_comp, hf, hg]
      exact h j
    rw [Preadditive.comp_sub]
    exact (homotopic_sub_zero_iff _ _).2
      ((CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ _).1 hj)
  choose v hv using fun j =>
    (homotopic_zero_iff_exists_comp_nullHomotopyProj _).1 (hzero j)
  let s : Cocone F := { pt := nullHomotopyObj Y.as, ι := Discrete.natTrans v }
  have key : hc.desc s ≫ nullHomotopyProj Y.as = f' - g' := by
    refine hc.hom_ext fun j => ?_
    rw [← Category.assoc, hc.fac s j]
    exact hv j
  have hfg : Homotopic f' g' := (homotopic_sub_zero_iff f' g').1
    ((homotopic_zero_iff_exists_comp_nullHomotopyProj _).2 ⟨hc.desc s, key⟩)
  rw [← hf, ← hg]
  exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) f' g').2 hfg

/-- A family of differential graded modules whose direct sum is `S` has jointly epimorphic
coprojections in the homotopy category. -/
theorem jointlyEpi_toHomotopyCategory_of_isColimit_cofan
    {X : ι → DifferentialGradedModule A} {S : DifferentialGradedModule A}
    (p : ∀ i, X i ⟶ S) (hS : IsColimit (Cofan.mk S p))
    {Y : HomotopyCategory A}
    (f g : (toHomotopyCategory A).obj S ⟶ Y)
    (h : ∀ i, (toHomotopyCategory A).map (p i) ≫ f =
      (toHomotopyCategory A).map (p i) ≫ g) :
    f = g :=
  jointlyEpi_map_toHomotopyCategory_of_isColimit hS f g fun j => h j.as

/-- A cocone in the homotopy category over a discrete diagram of differential graded modules,
lifted to a cocone of differential graded modules through the fullness of the quotient
functor. -/
noncomputable def liftCoconeOfHomotopyCategory (F : Discrete ι ⥤ DifferentialGradedModule A)
    (s : Cocone (F ⋙ toHomotopyCategory A)) : Cocone F where
  pt := s.pt.as
  ι := Discrete.natTrans fun j => (toHomotopyCategory A).preimage (s.ι.app j)

/-- The lifted cocone maps back to the given one. -/
theorem map_liftCoconeOfHomotopyCategory_ι_app
    (F : Discrete ι ⥤ DifferentialGradedModule A)
    (s : Cocone (F ⋙ toHomotopyCategory A)) (j : Discrete ι) :
    (toHomotopyCategory A).map ((liftCoconeOfHomotopyCategory F s).ι.app j) = s.ι.app j :=
  (toHomotopyCategory A).map_preimage (s.ι.app j)

/-- The image of a colimit cocone over a discrete diagram of differential graded modules is a
colimit cocone in the homotopy category. -/
noncomputable def isColimitMapCoconeOfDiscrete
    {F : Discrete ι ⥤ DifferentialGradedModule A} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((toHomotopyCategory A).mapCocone c) where
  desc s := (toHomotopyCategory A).map (hc.desc (liftCoconeOfHomotopyCategory F s))
  -- The two obligations are chained as terms rather than with `calc`: the cocone point of the
  -- lifted cocone and `s.pt` agree only definitionally, and `calc` asks instance search for the
  -- `Trans` step, which does not unfold either of them.
  fac s j :=
    (((toHomotopyCategory A).map_comp (c.ι.app j)
          (hc.desc (liftCoconeOfHomotopyCategory F s))).symm.trans
        (congrArg (toHomotopyCategory A).map
          (hc.fac (liftCoconeOfHomotopyCategory F s) j))).trans
      (map_liftCoconeOfHomotopyCategory_ι_app F s j)
  uniq s m hm := by
    refine jointlyEpi_map_toHomotopyCategory_of_isColimit hc m _ fun j => ?_
    exact (hm j).trans ((map_liftCoconeOfHomotopyCategory_ι_app F s j).symm.trans
      ((congrArg (toHomotopyCategory A).map
          (hc.fac (liftCoconeOfHomotopyCategory F s) j)).symm.trans
        ((toHomotopyCategory A).map_comp _ _)))

/-- The quotient functor preserves direct sums indexed by a type in the ambient universe. -/
@[stacks 09JR "homotopy_direct_sums_preserved"]
instance preservesCoproducts_toHomotopyCategory (A : DifferentialGradedAlgebra R)
    (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (toHomotopyCategory A) where
  preservesColimit := ⟨fun hc => ⟨isColimitMapCoconeOfDiscrete hc⟩⟩

end Coproducts

end DifferentialGradedModule
