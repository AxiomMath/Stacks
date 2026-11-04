module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjectiveHomSequence

/-!
# Action-linear cochains and null homotopies

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. A
homotopy from a morphism of right differential graded `A`-modules to zero is the same datum as
an action-linear cochain of degree `-1` whose commutator with the differentials is the
morphism. This file sets up that dictionary, together with the two constructions of
action-linear cochains that the transfinite argument for Tag 0FSY needs: a closed action-linear
cochain of degree zero is a morphism, and compatible action-linear cochains out of a diagram
assemble into one out of its colimit.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopic_zero_iff_exists_actionLinear`: a morphism
  is homotopic to zero exactly when it is the commutator of the differentials with an
  action-linear cochain of degree `-1`.
* `SheafOfModules.DifferentialGradedModule.homOfClosed` and
  `SheafOfModules.DifferentialGradedModule.ofHom_homOfClosed`: a closed action-linear cochain
  of degree zero is the cochain of a morphism of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.exists_actionLinear_colimit`: a family of
  action-linear cochains out of the objects of a diagram, compatible with its maps, comes from
  a unique action-linear cochain out of the colimit.

## Implementation notes

An action-linear cochain of degree `k` out of `M` is the same thing as a morphism of graded
modules from `M` into the degree shift by `k` of the target, which is how the colimit statement
is proved: forgetting the differential is a left adjoint, so it carries the colimit cocone to a
colimit cocone of graded modules, and the assembled graded morphism is read back as a cochain.
The degree shift used is `SheafOfModules.GradedModule.shift`, whose degree-`n` piece is the
degree-`n + k` piece of the original.

The components of a cochain of degree `k` out of degree `p` land in degree `p + k`, while the
action of a homogeneous section of degree `m` moves `p + k` to `(p + k) + m` and `p + m` to
`(p + m) + k`; these two degrees are equal but not definitionally so, which is why
action-linearity is stated with `HEq` and why the transport lemmas `cochain_v_heq_of_eq` and
`cochain_v_comp_eqToHom` are needed throughout.

## References

* [Stacks Project, Tag 0FS4](https://stacks.math.columbia.edu/tag/0FS4)
* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-! ### Transport of the components of a cochain -/

/-- Two components of a cochain with the same source and propositionally equal targets agree
on sections. -/
theorem cochain_v_heq_of_eq {M N : DifferentialGradedModule.{u, v, w} A} {k p q q' : ℤ}
    (z : Cochain M.complex N.complex k) (h : q = q')
    (hp : p + k = q) (hp' : p + k = q') (U : X.Cᵒᵖ)
    (x : (M.complex.X p).val.obj U) :
    HEq ((z.v p q hp).val.app U x) ((z.v p q' hp').val.app U x) := by
  subst h
  rfl

/-- Two components of a cochain with the same source and propositionally equal targets agree
up to the transport identifying the targets. -/
theorem cochain_v_comp_eqToHom {M N : DifferentialGradedModule.{u, v, w} A} {k p q q' : ℤ}
    (z : Cochain M.complex N.complex k) (h : q = q')
    (hp : p + k = q) (hp' : p + k = q') :
    z.v p q hp ≫ eqToHom (congrArg N.complex.X h) = z.v p q' hp' := by
  subst h
  simp

/-! ### Null homotopies as action-linear cochains -/

/-- An action-linear cochain of degree `-1` whose commutator with the differentials is a
morphism is a homotopy from that morphism to zero. -/
theorem homotopic_zero_of_actionLinear_delta {M N : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) (z : Cochain M.complex N.complex (-1)) (hz : IsActionLinear A z)
    (hd : δ (-1) 0 z = Cochain.ofHom f.toHomologicalComplex) : Homotopic f 0 := by
  refine ⟨{ app := fun n => z.v n (n - 1) (by omega)
            map_mul := ?_
            comm := ?_ }⟩
  · intro n m U x a
    exact (cochain_v_heq_of_eq A z (show n + m - 1 = (n - 1) + m by omega)
      (by omega) (by omega) U _).trans (hz n (n - 1) m (by omega) U x a)
  · intro n
    have h := Cochain.congr_v hd n n (add_zero n)
    simp only [Cochain.ofHom_v] at h
    rw [δ_v (-1) 0 (by omega) z n n (add_zero n) (n - 1) (n + 1) rfl rfl] at h
    show f.toHomologicalComplex.f n - 0 = _
    rw [sub_zero, ← h]
    simp only [Int.negOnePow_zero, one_smul]
    rw [Category.assoc, cochain_v_comp_eqToHom A]
    omega

/-- A morphism homotopic to zero is the commutator of the differentials with an action-linear
cochain of degree `-1`. -/
theorem exists_actionLinear_delta_of_homotopic_zero
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) (hf : Homotopic f 0) :
    ∃ z : Cochain M.complex N.complex (-1),
      IsActionLinear A z ∧ δ (-1) 0 z = Cochain.ofHom f.toHomologicalComplex := by
  obtain ⟨H⟩ := hf
  let z : Cochain M.complex N.complex (-1) := Cochain.mk fun p q hpq =>
    H.app p ≫ eqToHom (congrArg N.complex.X (show p - 1 = q by omega))
  have hzv (p : ℤ) : z.v p (p - 1) (by omega) = H.app p := by
    simp [z]
  refine ⟨z, ?_, ?_⟩
  · intro p q m hpq U x a
    obtain rfl : q = p - 1 := by omega
    have hv := cochain_v_heq_of_eq A z (show p - 1 + m = p + m - 1 by omega)
      (by omega) (by omega) U ((M.mul p m).app U x a)
    rw [hzv] at hv ⊢
    exact hv.trans (H.map_mul p m U x a)
  · apply Cochain.ext
    intro n q hnq
    obtain rfl : n = q := by omega
    rw [δ_v (-1) 0 (by omega) z n n (add_zero n) (n - 1) (n + 1) rfl rfl]
    have h := H.comm n
    change f.toHomologicalComplex.f n - 0 = _ at h
    simpa [z, Cochain.mk_v] using h.symm

/-- **Null homotopies are action-linear cochains.** A morphism of right differential graded
modules is homotopic to zero exactly when it is the commutator of the differentials with an
action-linear cochain of degree `-1`. -/
theorem homotopic_zero_iff_exists_actionLinear
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    Homotopic f 0 ↔ ∃ z : Cochain M.complex N.complex (-1),
      IsActionLinear A z ∧ δ (-1) 0 z = Cochain.ofHom f.toHomologicalComplex :=
  ⟨exists_actionLinear_delta_of_homotopic_zero A f,
    fun ⟨z, hz, hd⟩ => homotopic_zero_of_actionLinear_delta A f z hz hd⟩

/-! ### Closed action-linear cochains of degree zero -/

/-- The morphism of right differential graded modules attached to a closed action-linear
cochain of degree zero. -/
noncomputable def homOfClosed {M N : DifferentialGradedModule.{u, v, w} A}
    (z : Cochain M.complex N.complex 0) (hz : IsActionLinear A z) (hd : δ 0 1 z = 0) : M ⟶ N where
  toHomologicalComplex := Cocycle.homOf (Cocycle.mk z 1 rfl hd)
  map_mul n m U x a := eq_of_heq (hz n n m (add_zero n) U x a)

/-- The cochain of the morphism attached to a closed action-linear cochain of degree zero is
that cochain. -/
theorem ofHom_homOfClosed {M N : DifferentialGradedModule.{u, v, w} A}
    (z : Cochain M.complex N.complex 0) (hz : IsActionLinear A z) (hd : δ 0 1 z = 0) :
    Cochain.ofHom (homOfClosed A z hz hd).toHomologicalComplex = z :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

/-! ### Action-linear cochains as graded morphisms into a shift -/

/-- Transporting the degree of a homogeneous section does not change it. -/
theorem castHom_heq (F : ℤ → SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {i j : ℤ} (h : i = j) (U : X.Cᵒᵖ) (x : (F i).val.obj U) : HEq (castHom F h U x) x := by
  subst h
  rfl

/-- The morphism of graded modules into the degree shift attached to an action-linear
cochain. -/
noncomputable def gradedHomOfCochain {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (z : Cochain M.complex N.complex k) (hz : IsActionLinear A z) :
    (forgetToGradedModule A).obj M ⟶ (((forgetToGradedModule A).obj N).shift k) where
  app p := z.v p (p + k) rfl
  map_smul p m U x a := by
    rw [GradedModule.shift_smul]
    apply eq_of_heq
    refine (cochain_v_heq_of_eq A z (show (p + m) + k = (p + k) + m by omega)
      rfl (by omega) U _).trans ((hz p (p + k) m rfl U x a).trans ?_)
    exact (castHom_heq ((forgetToGradedModule A).obj N).piece
      (show (p + k) + m = (p + m) + k by omega) U _).symm

/-- The component in degree `p` of the graded morphism attached to an action-linear cochain `z`
is the component `z.v p (p + k)`. -/
@[simp] theorem gradedHomOfCochain_app {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (z : Cochain M.complex N.complex k) (hz : IsActionLinear A z) (p : ℤ) :
    (gradedHomOfCochain A z hz).app p = z.v p (p + k) rfl := rfl

/-- The cochain attached to a morphism of graded modules into a degree shift. -/
noncomputable def cochainOfGradedHom {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (g : (forgetToGradedModule A).obj M ⟶ (((forgetToGradedModule A).obj N).shift k)) :
    Cochain M.complex N.complex k :=
  Cochain.mk fun p _q h => g.app p ≫ eqToHom (congrArg N.complex.X h)

/-- The component `(p, p + k)` of the cochain attached to a graded morphism `g` into a degree
shift is the component of `g` in degree `p`. -/
@[simp] theorem cochainOfGradedHom_v {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (g : (forgetToGradedModule A).obj M ⟶ (((forgetToGradedModule A).obj N).shift k)) (p : ℤ) :
    (cochainOfGradedHom A g).v p (p + k) rfl = g.app p := by
  simp only [cochainOfGradedHom, Cochain.mk_v]
  exact Category.comp_id _

/-- The cochain attached to a morphism of graded modules into a degree shift is action-linear. -/
theorem actionLinear_cochainOfGradedHom {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (g : (forgetToGradedModule A).obj M ⟶ (((forgetToGradedModule A).obj N).shift k)) :
    IsActionLinear A (cochainOfGradedHom A g) := by
  rintro p q m rfl U x a
  have h := g.map_smul p m U x a
  rw [GradedModule.shift_smul] at h
  have hv := cochain_v_heq_of_eq A (cochainOfGradedHom A g)
    (show (p + m) + k = (p + k) + m by omega) rfl (by omega) U
    ((M.mul p m).app U x a)
  rw [cochainOfGradedHom_v] at hv ⊢
  refine hv.symm.trans ((heq_of_eq h).trans ?_)
  exact castHom_heq ((forgetToGradedModule A).obj N).piece
    (show (p + k) + m = (p + m) + k by omega) U _

/-- The cochain attached to the graded morphism of an action-linear cochain `z` is `z`. -/
theorem cochainOfGradedHom_gradedHomOfCochain {M N : DifferentialGradedModule.{u, v, w} A}
    {k : ℤ} (z : Cochain M.complex N.complex k) (hz : IsActionLinear A z) :
    cochainOfGradedHom A (gradedHomOfCochain A z hz) = z := by
  apply Cochain.ext
  rintro p q rfl
  rw [cochainOfGradedHom_v]
  rfl

/-- The cochain attached to the composite of a morphism `f` of right differential graded modules
with a graded morphism `g` into a degree shift is the composite of the cochain of `f` with the
cochain attached to `g`. -/
theorem cochainOfGradedHom_precomp {L M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (f : L ⟶ M)
    (g : (forgetToGradedModule A).obj M ⟶ (((forgetToGradedModule A).obj N).shift k)) :
    cochainOfGradedHom A ((forgetToGradedModule A).map f ≫ g) =
      (Cochain.ofHom f.toHomologicalComplex).comp (cochainOfGradedHom A g) (zero_add k) := by
  apply Cochain.ext
  rintro p q rfl
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, cochainOfGradedHom_v]
  rfl

/-! ### Action-linear cochains out of a colimit -/

/-- **Compatible action-linear cochains assemble over a colimit.** A family of action-linear
cochains of degree `k` out of the objects of a diagram of right differential graded modules,
compatible with the maps of the diagram, is the restriction of an action-linear cochain out of
the colimit. -/
theorem exists_actionLinear_colimit {K : Type max u v w} [Category.{max u v w} K]
    (F : K ⥤ DifferentialGradedModule.{u, v, max u v w} A)
    (c : Cocone F) (hc : IsColimit c)
    (N : DifferentialGradedModule.{u, v, max u v w} A) (k : ℤ)
    (z : ∀ j, Cochain (F.obj j).complex N.complex k)
    (hz : ∀ j, IsActionLinear A (z j))
    (hcompat : ∀ ⦃i j⦄ (f : i ⟶ j),
      (Cochain.ofHom (F.map f).toHomologicalComplex).comp (z j) (zero_add k) = z i) :
    ∃ z' : Cochain c.pt.complex N.complex k, IsActionLinear A z' ∧
      ∀ j, (Cochain.ofHom (c.ι.app j).toHomologicalComplex).comp z' (zero_add k) = z j := by
  have hG : PreservesColimitsOfShape K (forgetToGradedModule.{u, v, max u v w} A) :=
    (forgetToGradedModule_preservesColimitsOfSize.{u, v, max u v w, u, u,
      max u v w, max u v w} A).preservesColimitsOfShape
  let G := forgetToGradedModule.{u, v, max u v w} A
  let d : Cocone (F ⋙ G) :=
    { pt := (G.obj N).shift k
      ι :=
        { app := fun j => gradedHomOfCochain A (z j) (hz j)
          naturality := by
            intro i j f
            apply GradedModule.Hom.ext
            intro p
            have h := Cochain.congr_v (hcompat f) p (p + k) rfl
            simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h
            simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map,
              GradedModule.Hom.comp_app', Category.comp_id, gradedHomOfCochain_app]
            exact h } }
  let hcG := isColimitOfPreserves G hc
  let g := hcG.desc d
  refine ⟨cochainOfGradedHom A g, actionLinear_cochainOfGradedHom A g, fun j => ?_⟩
  rw [← cochainOfGradedHom_precomp]
  have h := hcG.fac d j
  change G.map (c.ι.app j) ≫ g = gradedHomOfCochain A (z j) (hz j) at h
  rw [h, cochainOfGradedHom_gradedHomOfCochain]

end SheafOfModules.DifferentialGradedModule

end
