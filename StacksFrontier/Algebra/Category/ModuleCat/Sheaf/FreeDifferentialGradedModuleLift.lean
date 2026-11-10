module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule

/-!
# Homomorphisms of differential graded modules out of a free graded module

Let `R` be a sheaf of rings on a site, let `D` be a sheaf of differential graded `R`-algebras and
let `S` be a sheaf of graded sets. The canonical generators of the free differential graded
`D`-module `D[S]` are closed, so a family of homogeneous local sections of a right differential
graded `D`-module `M` indexed by `S`, all of them killed by the differential of `M`, extends to a
homomorphism of *differential* graded modules `D[S] ⟶ M` — not merely to the homomorphism of
graded modules that the universal property of `D[S]` supplies.

## Main definitions

* `SheafOfModules.dgLiftHom` is the homomorphism of right differential graded modules
  `D[S] ⟶ M` determined by a family of generators all of whose sections are closed.

## Main results

* `SheafOfModules.liftAdd_dPres`: on the presentation of `D[S]`, the lift of a closed family
  intertwines the differential of the presentation with the differential of `M`.
* `SheafOfModules.liftVal_comp_d`: the same identity after sheafification, degree by degree.
* `SheafOfModules.dgLiftHom_generator`: the homomorphism sends each canonical generator to the
  prescribed section.

## Implementation notes

Both sides of `d_M ∘ lift = lift ∘ d_{D[S]}` are morphisms out of the sheafification of the
presentation of `D[S]`, so `SheafOfModules.freePiece_hom_ext` reduces the identity to the
presentation. There `SheafOfModules.dPres` and `SheafOfModules.liftAdd` are computed on the
summand of a generator `s` of degree `j` by `dPres_freeOf` and `liftAdd_freeOf`, and the identity
becomes the signed Leibniz rule of `M` with its first term killed by the closedness hypothesis:
the sign `(-1)^{deg s}` carried by `dPres` is exactly the sign the Leibniz rule puts on the
surviving term.

The two sides of that Leibniz rule live in the propositionally but not definitionally equal
degrees `(j + (n - j)) + 1` and `j + ((n - j) + 1)`, so the comparison runs through
`SheafOfModules.castHom`, as it does throughout
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean`. Two transports are isolated
for it: `SheafOfModules.dgD_castHom`, the module counterpart of `SheafOfModules.algD_castHom`,
and `SheafOfModules.leibniz_ofDifferentialGraded`, the Leibniz rule of `M` restated for the
underlying graded module with its transports written through `castHom`.

Two spellings of one type recur and must be kept apart in statements, as they are in
`FreeGradedModule.lean`: the degree-`n` sections of `M` are `(M.complex.X n).val.obj U` when they
come from the complex and `((GradedModule.ofDifferentialGraded M).piece n).val.obj U` when they
come from the graded module. They are definitionally equal, so term-mode steps never notice, but
`rw` does. Hence `SheafOfModules.smul_zero_left_ofDifferentialGraded`, which is
`GradedModule.smul_zero_left` with its zero written in the first spelling, and the four places
below where a rewrite is replaced by a term-mode step.

## References

* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum

universe w t a m v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Transports -/

/-- The action of a graded module vanishes on the zero module section. -/
theorem GradedModule.smul_zero_left {A : GradedAlgebra.{t, a} R} (N : GradedModule.{t, a, m} A)
    (n i : ℤ) (U : Cᵒᵖ) (y : (A.piece i).val.obj U) : N.smul n i U 0 y = 0 := by
  rw [map_zero (N.smul n i U)]
  rfl

/-- The action of the graded module underlying a right differential graded module vanishes on the
zero section, with the zero written in the degree family of the complex. -/
theorem smul_zero_left_ofDifferentialGraded {D : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} D) (n i : ℤ) (U : Cᵒᵖ)
    (y : (D.toGradedAlgebra.piece i).val.obj U) :
    (GradedModule.ofDifferentialGraded M).smul n i U (0 : (M.complex.X n).val.obj U) y = 0 :=
  (GradedModule.ofDifferentialGraded M).smul_zero_left n i U y

/-- The differential of a right differential graded module commutes with transport along an
equality of degrees, stated for the degree family of the underlying graded module. -/
theorem dgD_castHom {D : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} D) {k k' : ℤ} (h : k = k') (h' : k + 1 = k' + 1)
    (U : Cᵒᵖ) (z : ((GradedModule.ofDifferentialGraded M).piece k).val.obj U) :
    homSections (M.complex.d k' (k' + 1)) U
        (castHom (GradedModule.ofDifferentialGraded M).piece h U z) =
      castHom (GradedModule.ofDifferentialGraded M).piece h' U
        (homSections (M.complex.d k (k + 1)) U z) := by
  subst h
  exact (eq_of_heq
    (heq_castHom (GradedModule.ofDifferentialGraded M).piece h' U _)).symm

/-- The signed Leibniz rule of a right differential graded module, with its two transports written
through `SheafOfModules.castHom` and its action spelled as the action of the underlying graded
module. This is the form the free module consumes. -/
theorem leibniz_ofDifferentialGraded {D : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} D) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((GradedModule.ofDifferentialGraded M).piece n).val.obj U)
    (y : (D.toGradedAlgebra.piece i).val.obj U) :
    homSections (M.complex.d (n + i) (n + i + 1)) U
        ((GradedModule.ofDifferentialGraded M).smul n i U x y) =
      castHom (GradedModule.ofDifferentialGraded M).piece (add_right_comm n 1 i) U
          ((GradedModule.ofDifferentialGraded M).smul (n + 1) i U
            (homSections (M.complex.d n (n + 1)) U x) y)
        + (Int.negOnePow n : ℤ) •
            castHom (GradedModule.ofDifferentialGraded M).piece (add_assoc n i 1).symm U
              ((GradedModule.ofDifferentialGraded M).smul n (i + 1) U x
                (homSections (D.complex.d i (i + 1)) U y)) := by
  simp only [castHom_apply]
  exact M.leibniz n i U x y

/-! ### The lift of a closed family of generators -/

section Lift

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  (S : SheafOfGradedSets.{w} J) (D : DifferentialGradedAlgebra.{t, a} R)
  (M : DifferentialGradedModule.{t, a, max w a} D)
  (g : GradedGeneratorFamily S (GradedModule.ofDifferentialGraded M))

/-- **Two homomorphisms of right differential graded modules out of `D[S]` agreeing on the
canonical generators are equal.** This is `SheafOfModules.freeGradedModule_hom_ext` for the
underlying homomorphisms of graded modules, whose degree-`n` components are the degree-`n`
components of the given homomorphisms. -/
theorem dgHom_ext_generator {u v : freeDGModule S D ⟶ M}
    (h : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
      (u.toHomologicalComplex.f n).val.app U (freeGeneratorSection D.toGradedAlgebra S n U s hs) =
        (v.toHomologicalComplex.f n).val.app U
          (freeGeneratorSection D.toGradedAlgebra S n U s hs)) :
    u = v :=
  DifferentialGradedModule.Hom.ext fun n =>
    congrArg (fun φ : GradedModule.Hom (GradedModule.ofDifferentialGraded (freeDGModule S D))
        (GradedModule.ofDifferentialGraded M) => φ.app n)
      (freeGradedModule_hom_ext D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M)
        (f₁ := GradedModule.ofDifferentialGradedMap u)
        (f₂ := GradedModule.ofDifferentialGradedMap v) h)

variable (hg : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
  homSections (M.complex.d n (n + 1)) U (g.app n U s hs) = 0)
include hg

omit [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}] in
/-- **On the presentation of `D[S]`, the lift of a closed family of generators commutes with the
differentials.** On the summand of a generator of degree `j` this is the Leibniz rule of `M`,
whose first term vanishes because that generator goes to a closed section. -/
theorem liftAdd_dPres (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections D.toGradedAlgebra S n U) :
    liftAdd D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g (n + 1) U
        (dPres S D n U ζ) =
      homSections (M.complex.d n (n + 1)) U
        (liftAdd D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g n U ζ) := by
  induction ζ using _root_.DirectSum.induction_on with
  | zero =>
    simp only [map_zero]
    exact (map_zero (homSections (M.complex.d n (n + 1)) U)).symm
  | of p x =>
    obtain ⟨j, s, hs⟩ := p
    change liftAdd D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g (n + 1) U
        (dPres S D n U (freeOf D.toGradedAlgebra S n U j s hs x)) = _
    rw [dPres_freeOf, AddMonoidHom.map_zsmul, liftAdd_freeOf, liftAdd_freeOf,
      Cofree.smul_castHom_right, Cofree.castHom_castHom,
      dgD_castHom M (freeDegAdd n j) (by omega), leibniz_ofDifferentialGraded,
      hg j U s hs, smul_zero_left_ofDifferentialGraded, Cofree.castHom_zero, zero_add,
      AddMonoidHom.map_zsmul, Cofree.castHom_castHom]
  | add ζ ζ' hζ hζ' =>
    simp only [map_add, hζ, hζ']
    exact (map_add (homSections (M.complex.d n (n + 1)) U) _ _).symm

/-- **The lift of a closed family of generators commutes with the differentials.** This is
`SheafOfModules.liftAdd_dPres` transported to the sheafification, where both sides are determined
by their restrictions to the presentation. -/
theorem liftVal_comp_d (n : ℤ) :
    liftVal D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g n ≫
        M.complex.d n (n + 1) =
      freeD S D n ≫
        liftVal D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g (n + 1) := by
  refine freePiece_hom_ext D.toGradedAlgebra S fun U ζ => ?_
  change (M.complex.d n (n + 1)).val.app U
      ((liftVal D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g n).val.app U
        ((freeUnit D.toGradedAlgebra S n).app U ζ)) =
    (liftVal D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g (n + 1)).val.app U
      ((freeD S D n).val.app U ((freeUnit D.toGradedAlgebra S n).app U ζ))
  rw [liftVal_unit, freeD_unit]
  refine Eq.trans ?_ (liftVal_unit D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g
    (n + 1) U (dPres S D n U ζ)).symm
  exact (liftAdd_dPres S D M g hg n U ζ).symm

/-- **The homomorphism of right differential graded modules `D[S] ⟶ M` determined by a closed
family of homogeneous generators.** Its underlying homomorphism of graded modules is the one of
Tag 0FSF; what the closedness of the family buys is that it commutes with the differentials. -/
noncomputable def dgLiftHom : freeDGModule S D ⟶ M where
  toHomologicalComplex :=
    { f := fun n =>
        (liftHom D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g).app n
      comm' := by
        intro i j hij
        obtain rfl : i + 1 = j := hij
        change liftVal D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g i ≫
            M.complex.d i (i + 1) =
          (freeComplex S D).d i (i + 1) ≫
            liftVal D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g (i + 1)
        rw [show (freeComplex S D).d i (i + 1) = freeD S D i from
          CochainComplex.of_d _ _ i]
        exact liftVal_comp_d S D M g hg i }
  map_mul n i U x y :=
    (liftHom D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g).map_smul n i U x y

/-- In each degree, `SheafOfModules.dgLiftHom` is the component of the underlying homomorphism of
graded modules. -/
@[simp]
theorem dgLiftHom_f (n : ℤ) :
    (dgLiftHom S D M g hg).toHomologicalComplex.f n =
      (liftHom D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g).app n :=
  rfl

/-- **The lift sends each canonical generator of `D[S]` to the prescribed section.** -/
theorem dgLiftHom_generator (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) :
    ((dgLiftHom S D M g hg).toHomologicalComplex.f n).val.app U
        (freeGeneratorSection D.toGradedAlgebra S n U s hs) = g.app n U s hs :=
  liftHom_generator D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g n U s hs

end Lift

end SheafOfModules

end
