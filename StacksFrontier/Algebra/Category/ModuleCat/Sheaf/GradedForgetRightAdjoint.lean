module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The differential graded hull of a graded module

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. Forgetting the differential of a right differential graded `A`-module gives a
right graded module over `A.toGradedAlgebra`; this is
`SheafOfModules.forgetToGradedModule A`, which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits` exhibits as a **left**
adjoint, with the cofree differential graded module as its right adjoint.

This file shows that the same functor is also a **right** adjoint: its left adjoint sends a
graded module `N` to the *differential graded hull* of `N`, which is `Nⁿ ⊕ Nⁿ⁻¹` in degree `n`
with differential `(x, y) ↦ (0, x)`. The hull is also shown to be acyclic, and the unit of the
adjunction to be injective.

## Main definitions

* `SheafOfModules.GradedModule.shift N k` is the shift `N[k]` of a right graded module: its
  degree-`n` piece is `N`'s degree-`n + k` piece, with the same action.
* `SheafOfModules.Hull.obj N` is the differential graded hull of a right graded module.
* `SheafOfModules.Hull.descHom`, `SheafOfModules.Hull.descDgHom` are the morphism out of the
  hull attached to a graded morphism `N ⟶ forget M`, and `SheafOfModules.Hull.unitHom`,
  `SheafOfModules.Hull.lowerHom` the inverse construction; `SheafOfModules.Hull.homEquiv` is
  the resulting hom-bijection.
* `SheafOfModules.dgHullFunctor` is the hull as a functor and
  `SheafOfModules.dgHullAdjunction` the adjunction.
* `SheafOfModules.degCastHom` is the transport of a sheaf of modules along an equality of
  degrees, as a morphism; `SheafOfModules.Hull.appC` and `SheafOfModules.Hull.fC` read the
  components of a graded, resp. differential graded, morphism as morphisms of the relevant
  sheaves of modules.
* `SheafOfModules.toCochainComplex` forgets the action of a right differential graded module.

## Main results

* `SheafOfModules.forgetToGradedModule_isRightAdjoint` is Tag 0FSK: forgetting the
  differential has a left adjoint.
* `SheafOfModules.dgHull_unit_mono` is Tag 0FSL part (1): the unit of that adjunction is a
  monomorphism.
* `SheafOfModules.dgHull_acyclic` is Tag 0FSL part (3): the hull is acyclic.
* `SheafOfModules.DifferentialGradedModule.leibniz'` restates the Leibniz rule of a
  differential graded module in terms of `SheafOfModules.homSections` and
  `SheafOfModules.castHom`.

## Implementation notes

The hull is **not** built from scratch. In degree `n` it is `Nⁿ ⊕ Nⁿ⁻¹` with differential
`(x, y) ↦ (0, x)` and action `(x, y) · a = (x a + (-1)ⁿ y (d a), y a)`, and interchanging the
two coordinates identifies this with the *cofree* differential graded module on the shift
`N[-1]`: the cofree module on `P` is `Pⁿ ⊕ Pⁿ⁺¹` with differential `(x, y) ↦ (y, 0)` and
action `(x, y) · a = (x a, y a + (-1)ⁿ x (d a))`, and the signs match on the nose because the
sign depends only on the total degree. So `Hull.obj N := Cofree.cofree (N.shift (-1))`, and
all of the structure laws — associativity of the action, its Leibniz rule, the unit law,
bilinearity and compatibility with restriction — are inherited from `GradedForgetColimits`
rather than reproved. What is new here is the shift, the hom-bijection in the other variable,
and the acyclicity.

Consequently the hull's degree-`n` piece is presented as `Nⁿ⁻¹ ⊕ Nⁿ`, i.e. with the copy of
`Nⁿ` in the *second* coordinate; `Hull.unitHom` is `biprod.inr` precomposed with the transport
`degCastHom N.piece` across `n = n + 1 + -1`, and `Hull.descHom` is `biprod.desc` of the two
components `d ∘ α` and `α`.

Degrees are written `n + -1` rather than `n - 1` so that every index equality is closed by
`omega` and every transport is a `SheafOfModules.castHom` or `SheafOfModules.degCastHom`,
which commute with everything in sight by `subst`. `GradedModule.shift` is marked
`@[implicit_reducible]`: without it `(N.shift k).piece n` does not reduce to `N.piece (n + k)`
at the transparency `rw` uses to check type correctness, and the rewrites in `descHom_comm`
fail even though the statements elaborate. For the same reason `Hull.appC` and `Hull.fC` are
plain `def`s and not `abbrev`s, and are used in place of `α.app` and
`ψ.toHomologicalComplex.f`: the targets `((forgetToGradedModule A).obj M).piece n` and
`(Hull.obj N).complex.X n` only agree with `M.complex.X n` and `Cofree.piece (N.shift (-1)) n`
after unfolding semireducible definitions.

Acyclicity is proved degreewise and without sheafification. `SheafOfModules.{m} R` has no
cokernels in general, so there is no `CategoryWithHomology` structure to appeal to and the
`ShortComplex.HomologyData` has to be produced by hand; it is obtained by comparing the short
complex `Hull.hullSc` of two consecutive differentials with the split short exact sequence
`Hull.splitSc` of a binary biproduct, through the intermediate `Hull.midSc`, using
`CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono` twice. The zero object needed
for `CategoryTheory.ShortComplex.Splitting.exact` comes from the unconditional finite limits
of `SheafOfModules.{m} R`. Exactness is proved at every degree of the form `k + 1`, which is
every degree, so that both differentials appearing are in the canonical form `d k (k + 1)`
that `CochainComplex.of_d` computes.

No universe is specialized: the site, the sheaf of rings, the algebra components and the
module components keep the four independent universes of `GradedForgetColimits`; a ringed
site `RingedSite.{u, u, u}` is the special case `t = a = m = u`.

## References

* [Stacks Project, Tag 0FSK](https://stacks.math.columbia.edu/tag/0FSK)
* [Stacks Project, Tag 0FSL](https://stacks.math.columbia.edu/tag/0FSL)
* [Stacks Project, Tag 0FQ1](https://stacks.math.columbia.edu/tag/0FQ1)
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe t a m v u
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transport of a sheaf of modules along an equality of degrees. -/
def degCastHom (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) : X i ⟶ X j := by
  subst h
  exact 𝟙 _

/-- Transport along a reflexive equality of degrees is the identity. -/
@[simp] theorem degCastHom_rfl (X : ℤ → SheafOfModules.{m} R) (i : ℤ) :
    degCastHom X (rfl : i = i) = 𝟙 _ := rfl

/-- Transport along an equality of degrees is an isomorphism. -/
instance isIso_degCastHom (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) :
    IsIso (degCastHom X h) := by
  subst h
  rw [degCastHom_rfl]
  infer_instance

/-- On sections, `degCastHom X h` is the transport `castHom X h`. -/
theorem homSections_degCastHom (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (X i).val.obj U) : homSections (degCastHom X h) U x = castHom X h U x := by
  subst h
  rfl

/-- The differential of a complex, in canonical degrees, applied to a transported section. -/
theorem homSections_d_succ_castHom (K : CochainComplex (SheafOfModules.{m} R) ℤ) {i i' : ℤ}
    (h : i = i') (U : Cᵒᵖ) (x : (K.X i).val.obj U) :
    homSections (K.d i' (i' + 1)) U (castHom K.X h U x)
      = castHom K.X (by rw [h] : i + 1 = i' + 1) U (homSections (K.d i (i + 1)) U x) := by
  subst h
  rfl

/-- Transporting the source degree and then applying a differential is the differential out of
the original degree. -/
theorem degCastHom_comp_d (K : CochainComplex (SheafOfModules.{m} R) ℤ) {i i' : ℤ} (h : i = i')
    (j : ℤ) : degCastHom K.X h ≫ K.d i' j = K.d i j := by
  subst h
  rw [degCastHom_rfl, Category.id_comp]

/-- A differential followed by transport of the target degree is the differential into the new
degree. -/
theorem d_comp_degCastHom (K : CochainComplex (SheafOfModules.{m} R) ℤ) (i : ℤ) {j j' : ℤ}
    (h : j = j') : K.d i j ≫ degCastHom K.X h = K.d i j' := by
  subst h
  rw [degCastHom_rfl, Category.comp_id]

/-- The composite of two transports of degree is the transport along the composite equality. -/
@[reassoc]
theorem degCastHom_comp_degCastHom (X : ℤ → SheafOfModules.{m} R) {i j k : ℤ} (h : i = j)
    (h' : j = k) : degCastHom X h ≫ degCastHom X h' = degCastHom X (h.trans h') := by
  subst h h'
  rw [degCastHom_rfl, Category.id_comp]

/-- On sections, `biprod.desc f g` sends `ξ` to `f` of its first component plus `g` of its
second component. -/
theorem homSections_desc {M N Z : SheafOfModules.{m} R} (f : M ⟶ Z) (g : N ⟶ Z) (U : Cᵒᵖ)
    (ξ : (M ⊞ N).val.obj U) :
    homSections (biprod.desc f g) U ξ
      = homSections f U (biprodFst M N U ξ) + homSections g U (biprodSnd M N U ξ) := by
  conv_lhs => rw [← biprodSections_total M N U ξ]
  rw [map_add]
  exact congrArg₂ (· + ·)
    ((homSections_comp _ _ U _).symm.trans (homSections_congr (biprod.inl_desc f g) U _))
    ((homSections_comp _ _ U _).symm.trans (homSections_congr (biprod.inr_desc f g) U _))

namespace GradedModule

variable {A' : GradedAlgebra.{t, a} R}

/-- The shift of a right graded module: the degree-`n` piece of `N.shift k` is the degree
`n + k` piece of `N`, with the same action. -/
@[implicit_reducible]
def shift (N : GradedModule.{t, a, m} A') (k : ℤ) : GradedModule.{t, a, m} A' where
  piece n := N.piece (n + k)
  smul n i U :=
    AddMonoidHom.mk'
      (fun x ↦ (castHom N.piece (by omega : n + k + i = n + i + k) U).comp
        (N.smul (n + k) i U x))
      (fun x y ↦ AddMonoidHom.ext fun z ↦ by
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add])
  smul_smul_left n i U r x y := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply, N.smul_smul_left, castHom_smul]
  smul_smul_right n i U r x y := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply, N.smul_smul_right, castHom_smul]
  smul_naturality n i {U V} f x y := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply, castHom_naturality,
      N.smul_naturality]
    rfl
  smul_mul n i j U x y z := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply, Cofree.smul_castHom_left,
      Cofree.castHom_castHom]
    refine ((heq_castHom _ _ _ _).trans ?_).trans (heq_castHom _ _ _ _).symm
    exact N.smul_mul (n + k) i j U x y z
  smul_one n U x := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply]
    exact (heq_castHom _ _ _ _).trans (N.smul_one (n + k) U x)

/-- The degree-`n` piece of `N.shift k` is the degree-`n + k` piece of `N`. -/
@[simp] theorem shift_piece (N : GradedModule.{t, a, m} A') (k n : ℤ) :
    (N.shift k).piece n = N.piece (n + k) := rfl

/-- Transport of degree in `N.shift k` along `i = j` is transport of degree in `N` along
`i + k = j + k`. -/
theorem castHom_shift_piece (N : GradedModule.{t, a, m} A') (k : ℤ) {i j : ℤ} (h : i = j)
    (U : Cᵒᵖ) (x : (N.piece (i + k)).val.obj U) :
    castHom (N.shift k).piece h U x
      = castHom N.piece (by rw [h] : i + k = j + k) U x := by
  subst h
  rfl

/-- The action on `N.shift k` is the action on `N`, transported to the shifted degree. -/
theorem shift_smul (N : GradedModule.{t, a, m} A') (k n i : ℤ) (U : Cᵒᵖ)
    (x : (N.piece (n + k)).val.obj U) (y : (A'.piece i).val.obj U) :
    (N.shift k).smul n i U x y
      = castHom N.piece (by omega : n + k + i = n + i + k) U (N.smul (n + k) i U x y) := rfl

/-- A homomorphism of graded modules with monomorphic homogeneous components is a
monomorphism. -/
theorem mono_of_mono_app {N N' : GradedModule.{t, a, m} A'} (f : N ⟶ N')
    (h : ∀ n, Mono (f.app n)) : Mono f :=
  ⟨fun _ _ hgg' => Hom.ext fun n =>
    (cancel_mono (f.app n)).1 (congrArg (fun φ : _ ⟶ N' => φ.app n) hgg')⟩

end GradedModule

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The action of a differential graded module commutes with transport of the module degree. -/
theorem mul_castHom_left (M : DifferentialGradedModule.{t, a, m} A) {n n' i : ℤ} (h : n = n')
    (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    (M.mul n' i).app U (castHom M.complex.X h U x) y
      = castHom M.complex.X (by rw [h]) U ((M.mul n i).app U x y) := by
  subst h
  rfl

/-- The Leibniz rule of a differential graded module, stated with `homSections` and `castHom`
instead of `.val.app` and `gradedCast`. -/
theorem leibniz' (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    homSections (M.complex.d (n + i) (n + i + 1)) U ((M.mul n i).app U x y)
      = castHom M.complex.X (add_right_comm n 1 i) U
          ((M.mul (n + 1) i).app U (homSections (M.complex.d n (n + 1)) U x) y)
        + (Int.negOnePow n : ℤ) • castHom M.complex.X (add_assoc n i 1).symm U
            ((M.mul n (i + 1)).app U x (homSections (A.complex.d i (i + 1)) U y)) := by
  rw [castHom_apply, castHom_apply]
  exact M.leibniz n i U x y

end DifferentialGradedModule

/-- As an integer, the sign `Int.negOnePow (n + -1)` is the negative of `Int.negOnePow n`. -/
theorem negOnePow_pred (n : ℤ) :
    ((Int.negOnePow (n + -1) : ℤ)) = -(Int.negOnePow n : ℤ) := by
  have h : Int.negOnePow n = -Int.negOnePow (n + -1) := by
    conv_lhs => rw [show n = n + -1 + 1 by omega]
    rw [Int.negOnePow_succ]
  rw [h, Units.val_neg, neg_neg]

namespace Cofree

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The inclusion of the first coordinate of the cofree module commutes with transport of
degree. -/
theorem castHom_coordInl (N : GradedModule.{t, a, m} A.toGradedAlgebra) {k k' : ℤ} (h : k = k')
    (U : Cᵒᵖ) (z : (N.piece k).val.obj U) :
    castHom (piece N) h U (coordInl N k U z) = coordInl N k' U (castHom N.piece h U z) := by
  subst h
  rfl

/-- The differential of the cofree module on a section of the second coordinate. -/
theorem homSections_d_coordInr (N : GradedModule.{t, a, m} A.toGradedAlgebra) (k : ℤ) (U : Cᵒᵖ)
    (z : (N.piece (k + 1)).val.obj U) :
    homSections (d N k) U (coordInr N k U z) = coordInl N (k + 1) U z := by
  refine sections_ext N U ?_ ?_
  · rw [coordFst_d, biprodSnd_inr, biprodFst_inl]
  · rw [coordSnd_d, biprodSnd_inl]

end Cofree

namespace Hull

variable {A : DifferentialGradedAlgebra.{t, a} R} (N : GradedModule.{t, a, m} A.toGradedAlgebra)

/-- The differential graded hull of a right graded module: degreewise `Nⁿ ⊕ Nⁿ⁻¹`, with
differential `(x, y) ↦ (0, x)`. It is realized as the cofree differential graded module on
the shift `N[-1]`, whose two coordinates are the same two sheaves in the other order. -/
noncomputable def obj : DifferentialGradedModule.{t, a, m} A :=
  Cofree.cofree (N.shift (-1))

variable {M : DifferentialGradedModule.{t, a, m} A}

/-- The homogeneous components of a graded morphism `N ⟶ forget M`, read as morphisms into
the underlying complex of `M`. The two targets are the same sheaf of modules; the abbreviation
keeps every expression below stated for one of them. -/
def appC (α : N ⟶ (forgetToGradedModule A).obj M) (k : ℤ) : N.piece k ⟶ M.complex.X k :=
  α.app k

/-- The components `appC N α` carry the action on `N` to the action on `M`. -/
theorem homSections_appC_smul (α : N ⟶ (forgetToGradedModule A).obj M) (n i : ℤ) (U : Cᵒᵖ)
    (x : (N.piece n).val.obj U) (y : (A.complex.X i).val.obj U) :
    homSections (appC N α (n + i)) U (N.smul n i U x y)
      = (M.mul n i).app U (homSections (appC N α n) U x) y := α.map_smul n i U x y

/-- The components `appC N α` commute with transport of degree. -/
theorem homSections_appC_castHom (α : N ⟶ (forgetToGradedModule A).obj M) {k k' : ℤ}
    (h : k = k') (U : Cᵒᵖ) (x : (N.piece k).val.obj U) :
    homSections (appC N α k') U (castHom N.piece h U x)
      = castHom M.complex.X h U (homSections (appC N α k) U x) := by
  subst h
  rfl

/-- The degree-`n` component of the morphism `obj N ⟶ M` attached to a graded morphism
`N ⟶ forget M`: it sends `(x, y)` to `d (α x) + α y`. -/
noncomputable def descHom (α : N ⟶ (forgetToGradedModule A).obj M) (n : ℤ) :
    Cofree.piece (N.shift (-1)) n ⟶ M.complex.X n :=
  biprod.desc
    (appC N α (n + -1) ≫ M.complex.d (n + -1) (n + -1 + 1)
      ≫ degCastHom M.complex.X (by omega : n + -1 + 1 = n))
    (degCastHom N.piece (by omega : n + 1 + -1 = n) ≫ appC N α n)

/-- On sections, `descHom N α n` sends `(x, y)` to `d (α x) + α y`, up to transport of
degree. -/
theorem homSections_descHom (α : N ⟶ (forgetToGradedModule A).obj M) (n : ℤ) (U : Cᵒᵖ)
    (ξ : (Cofree.piece (N.shift (-1)) n).val.obj U) :
    homSections (descHom N α n) U ξ
      = castHom M.complex.X (by omega : n + -1 + 1 = n) U
          (homSections (M.complex.d (n + -1) (n + -1 + 1)) U
            (homSections (appC N α (n + -1)) U (Cofree.coordFst (N.shift (-1)) n U ξ)))
        + homSections (appC N α n) U (castHom N.piece (by omega : n + 1 + -1 = n) U
            (Cofree.coordSnd (N.shift (-1)) n U ξ)) := by
  refine (homSections_desc _ _ U ξ).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [homSections_comp, homSections_comp, homSections_degCastHom]
  · rw [homSections_comp, homSections_degCastHom]

/-- Transporting the degree, then applying `appC N α` and a differential, is `appC N α`
followed by the differential out of the original degree. -/
theorem degCastHom_comp_appC (α : N ⟶ (forgetToGradedModule A).obj M) {k k' : ℤ} (h : k = k')
    (j : ℤ) :
    degCastHom N.piece h ≫ appC N α k' ≫ M.complex.d k' j = appC N α k ≫ M.complex.d k j := by
  subst h
  rw [degCastHom_rfl, Category.id_comp]

/-- On the first coordinate, `descHom N α n` is `d ∘ α`, up to transport of degree. -/
@[reassoc]
theorem inl_descHom (α : N ⟶ (forgetToGradedModule A).obj M) (n : ℤ) :
    biprod.inl ≫ descHom N α n
      = appC N α (n + -1) ≫ M.complex.d (n + -1) (n + -1 + 1)
          ≫ degCastHom M.complex.X (by omega : n + -1 + 1 = n) :=
  biprod.inl_desc _ _

/-- On the second coordinate, `descHom N α n` is `α`, up to transport of degree. -/
@[reassoc]
theorem inr_descHom (α : N ⟶ (forgetToGradedModule A).obj M) (n : ℤ) :
    biprod.inr ≫ descHom N α n
      = degCastHom N.piece (by omega : n + 1 + -1 = n) ≫ appC N α n :=
  biprod.inr_desc _ _

/-- The components of `descHom` commute with the differentials. -/
theorem descHom_comm (α : N ⟶ (forgetToGradedModule A).obj M) (i : ℤ) :
    descHom N α i ≫ M.complex.d i (i + 1)
      = Cofree.d (N.shift (-1)) i ≫ descHom N α (i + 1) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [Cofree.d, Category.assoc, biprod.inl_snd_assoc, inl_descHom_assoc, degCastHom_comp_d,
      HomologicalComplex.d_comp_d, comp_zero, zero_comp]
  · rw [Cofree.d, Category.assoc, biprod.inr_snd_assoc, inr_descHom_assoc, inl_descHom,
      d_comp_degCastHom]
    exact degCastHom_comp_appC N α _ (i + 1)

/-- The components `descHom N α` carry the action on the hull to the action on `M`. -/
theorem homSections_descHom_mulHom (α : N ⟶ (forgetToGradedModule A).obj M) (n i : ℤ) (U : Cᵒᵖ)
    (ξ : (Cofree.piece (N.shift (-1)) n).val.obj U) (a : (A.complex.X i).val.obj U) :
    homSections (descHom N α (n + i)) U (Cofree.mulHom (N.shift (-1)) n i U a ξ)
      = (M.mul n i).app U (homSections (descHom N α n) U ξ) a := by
  rw [homSections_descHom, homSections_descHom]
  simp only [Cofree.coordFst_mulHom, Cofree.coordSnd_mulHom, GradedModule.shift_smul,
    GradedModule.castHom_shift_piece, Cofree.castHom_castHom, map_add,
    AddMonoidHom.map_zsmul, homSections_appC_castHom, homSections_appC_smul,
    homSections_d_succ_castHom, DifferentialGradedModule.mul_castHom_left,
    AddMonoidHom.add_apply, DifferentialGradedModule.leibniz', negOnePow_pred, neg_zsmul,
    map_neg, Cofree.algD]
  abel

/-- The differential of the hull out of degree `k` is the differential of the cofree module. -/
private theorem complex_d_eq_cofree_d (k : ℤ) :
    (obj N).complex.d k (k + 1) = Cofree.d (N.shift (-1)) k :=
  CochainComplex.of_d _ _ k

/-- The underlying morphism of cochain complexes of the morphism attached to a graded
morphism out of the hull. -/
noncomputable def descComplexHom (α : N ⟶ (forgetToGradedModule A).obj M) :
    (obj N).complex ⟶ M.complex where
  f := descHom N α
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [show (obj N).complex.d i (i + 1) = Cofree.d (N.shift (-1)) i from
      CochainComplex.of_d _ _ i]
    exact descHom_comm N α i

/-- The morphism of differential graded modules attached to a graded morphism `N ⟶ forget M`. -/
noncomputable def descDgHom (α : N ⟶ (forgetToGradedModule A).obj M) : obj N ⟶ M where
  toHomologicalComplex := descComplexHom N α
  map_mul n i U x y := homSections_descHom_mulHom N α n i U x y

/-- The inclusion of `N` into the top coordinate of the degree-`n` piece of the hull. -/
noncomputable def unitHom (n : ℤ) : N.piece n ⟶ Cofree.piece (N.shift (-1)) n :=
  degCastHom N.piece (by omega : n = n + 1 + -1) ≫ biprod.inr

/-- On sections, `unitHom N n` sends `x` to `(0, x)`, up to transport of degree. -/
theorem homSections_unitHom (n : ℤ) (U : Cᵒᵖ) (x : (N.piece n).val.obj U) :
    homSections (unitHom N n) U x
      = Cofree.coordInr (N.shift (-1)) n U
          (castHom N.piece (by omega : n = n + 1 + -1) U x) := by
  rw [unitHom, homSections_comp, homSections_degCastHom]
  rfl

/-- The inclusion of `N` into the hull is compatible with the two actions. -/
theorem mulHom_homSections_unitHom (n i : ℤ) (U : Cᵒᵖ) (x : (N.piece n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    Cofree.mulHom (N.shift (-1)) n i U y (homSections (unitHom N n) U x)
      = homSections (unitHom N (n + i)) U (N.smul n i U x y) := by
  rw [homSections_unitHom, homSections_unitHom]
  refine Cofree.sections_ext _ U ?_ ?_
  · rw [Cofree.coordFst_mulHom, biprodFst_inr, biprodFst_inr, map_zero,
      AddMonoidHom.zero_apply]
  · rw [Cofree.coordSnd_mulHom, biprodSnd_inr, biprodSnd_inr, biprodFst_inr,
      map_zero, AddMonoidHom.zero_apply, map_zero, smul_zero, add_zero,
      GradedModule.castHom_shift_piece, GradedModule.shift_smul,
      Cofree.smul_castHom_left, Cofree.castHom_castHom, Cofree.castHom_castHom]

/-- The homogeneous components of a morphism of differential graded modules out of the hull,
read as morphisms out of the biproduct pieces. -/
def fC (ψ : obj N ⟶ M) (k : ℤ) : Cofree.piece (N.shift (-1)) k ⟶ M.complex.X k :=
  ψ.toHomologicalComplex.f k

/-- The components `fC N ψ` commute with the differentials of the hull and of `M`. -/
theorem fC_comm (ψ : obj N ⟶ M) (k : ℤ) :
    fC N ψ k ≫ M.complex.d k (k + 1) = Cofree.d (N.shift (-1)) k ≫ fC N ψ (k + 1) := by
  refine (ψ.toHomologicalComplex.comm k (k + 1)).trans ?_
  rw [complex_d_eq_cofree_d]
  rfl

/-- The components `fC N ψ` carry the action on the hull to the action on `M`. -/
theorem homSections_fC_mul (ψ : obj N ⟶ M) (n i : ℤ) (U : Cᵒᵖ)
    (ξ : (Cofree.piece (N.shift (-1)) n).val.obj U) (y : (A.complex.X i).val.obj U) :
    homSections (fC N ψ (n + i)) U (Cofree.mulHom (N.shift (-1)) n i U y ξ)
      = (M.mul n i).app U (homSections (fC N ψ n) U ξ) y := ψ.map_mul n i U ξ y

/-- The components `fC N ψ` commute with transport of degree. -/
theorem homSections_fC_castHom (ψ : obj N ⟶ M) {k k' : ℤ} (h : k = k') (U : Cᵒᵖ)
    (z : (Cofree.piece (N.shift (-1)) k).val.obj U) :
    homSections (fC N ψ k') U (castHom (Cofree.piece (N.shift (-1))) h U z)
      = castHom M.complex.X h U (homSections (fC N ψ k) U z) := by
  subst h
  rfl

/-- The graded morphism `N ⟶ forget M` attached to a morphism of differential graded modules
out of the hull, by restricting along the inclusion of the top coordinate. -/
noncomputable def lowerHom (ψ : obj N ⟶ M) : N ⟶ (forgetToGradedModule A).obj M where
  app n := unitHom N n ≫ fC N ψ n
  map_smul n i U x y :=
    (congrArg (homSections (fC N ψ (n + i)) U)
        (mulHom_homSections_unitHom N n i U x y).symm).trans
      (homSections_fC_mul N ψ n i U (homSections (unitHom N n) U x) y)

/-- The degree-`k` component of `lowerHom N ψ` is `unitHom N k ≫ fC N ψ k`. -/
theorem appC_lowerHom (ψ : obj N ⟶ M) (k : ℤ) :
    appC N (lowerHom N ψ) k = unitHom N k ≫ fC N ψ k := rfl

/-- Restricting `descHom N α n` along `unitHom N n` gives `appC N α n`. -/
theorem unitHom_comp_descHom (α : N ⟶ (forgetToGradedModule A).obj M) (n : ℤ) :
    unitHom N n ≫ descHom N α n = appC N α n := by
  rw [unitHom, Category.assoc, inr_descHom, degCastHom_comp_degCastHom_assoc]
  exact Category.id_comp _

/-- Restricting along the inclusion of the top coordinate is inverse to the descent. -/
theorem lowerHom_descDgHom (α : N ⟶ (forgetToGradedModule A).obj M) :
    lowerHom N (descDgHom N α) = α :=
  GradedModule.Hom.ext fun n => unitHom_comp_descHom N α n

/-- On sections, the degree-`n` component of the descent of `lowerHom N ψ` agrees with that of
`ψ`. -/
theorem homSections_descHom_lowerHom (ψ : obj N ⟶ M) (n : ℤ) (U : Cᵒᵖ)
    (ζ : (Cofree.piece (N.shift (-1)) n).val.obj U) :
    homSections (descHom N (lowerHom N ψ) n) U ζ = homSections (fC N ψ n) U ζ := by
  have hsplit : homSections (fC N ψ n) U ζ
      = homSections (fC N ψ n) U
            (Cofree.coordInl (N.shift (-1)) n U (Cofree.coordFst (N.shift (-1)) n U ζ))
          + homSections (fC N ψ n) U
            (Cofree.coordInr (N.shift (-1)) n U (Cofree.coordSnd (N.shift (-1)) n U ζ)) :=
    (congrArg (homSections (fC N ψ n) U) (biprodSections_total _ _ U ζ).symm).trans
      (map_add (homSections (fC N ψ n) U) _ _)
  rw [homSections_descHom, hsplit]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [appC_lowerHom, homSections_comp, homSections_unitHom,
      ← homSections_comp (fC N ψ (n + -1)) (M.complex.d (n + -1) (n + -1 + 1)),
      homSections_congr (fC_comm N ψ (n + -1)) U, homSections_comp,
      Cofree.homSections_d_coordInr, ← homSections_fC_castHom, Cofree.castHom_coordInl,
      GradedModule.castHom_shift_piece, Cofree.castHom_castHom]
    exact congrArg _ (congrArg _ (eq_of_heq (heq_castHom _ _ _ _)))
  · rw [appC_lowerHom, homSections_comp, homSections_unitHom, Cofree.castHom_castHom]
    exact congrArg _ (congrArg _ (eq_of_heq (heq_castHom _ _ _ _)))

/-- The descent is inverse to restricting along the inclusion of the top coordinate. -/
theorem descDgHom_lowerHom (ψ : obj N ⟶ M) : descDgHom N (lowerHom N ψ) = ψ := by
  refine DifferentialGradedModule.Hom.ext fun n =>
    SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U => ?_
  ext z
  exact homSections_descHom_lowerHom N ψ n U z

/-- The inclusion `unitHom N n` is a monomorphism. -/
instance mono_unitHom (n : ℤ) : Mono (unitHom N n) := by
  have : Mono (biprod.inr : (N.shift (-1)).piece (n + 1) ⟶ Cofree.piece (N.shift (-1)) n) :=
    mono_of_mono_fac (biprod.inr_snd (X := (N.shift (-1)).piece n))
  rw [unitHom]
  exact mono_comp _ _

/-- The differential of the hull out of degree `k` is `biprod.snd ≫ biprod.inl`. -/
theorem complex_d (k : ℤ) :
    (obj N).complex.d k (k + 1)
      = (biprod.snd : Cofree.piece (N.shift (-1)) k ⟶ (N.shift (-1)).piece (k + 1))
          ≫ biprod.inl :=
  complex_d_eq_cofree_d N k

/-- Two consecutive differentials of the hull, in biproduct coordinates. -/
noncomputable def hullSc (k : ℤ) : ShortComplex (SheafOfModules.{m} R) :=
  ShortComplex.mk
    ((biprod.snd : Cofree.piece (N.shift (-1)) k ⟶ (N.shift (-1)).piece (k + 1))
      ≫ (biprod.inl : (N.shift (-1)).piece (k + 1) ⟶ Cofree.piece (N.shift (-1)) (k + 1)))
    ((biprod.snd : Cofree.piece (N.shift (-1)) (k + 1) ⟶ (N.shift (-1)).piece (k + 1 + 1))
      ≫ (biprod.inl : (N.shift (-1)).piece (k + 1 + 1)
          ⟶ Cofree.piece (N.shift (-1)) (k + 1 + 1)))
    (by simp)

/-- The split short exact sequence `Nᵏ⁺¹ ⟶ Nᵏ⁺¹ ⊞ Nᵏ⁺² ⟶ Nᵏ⁺²` of a biproduct piece. -/
noncomputable def splitSc (k : ℤ) : ShortComplex (SheafOfModules.{m} R) :=
  ShortComplex.mk
    (biprod.inl : (N.shift (-1)).piece (k + 1) ⟶ Cofree.piece (N.shift (-1)) (k + 1))
    (biprod.snd : Cofree.piece (N.shift (-1)) (k + 1) ⟶ (N.shift (-1)).piece (k + 1 + 1))
    (by simp)

/-- The short complex interpolating between `Hull.hullSc` and `Hull.splitSc`: it has the
hull's differential on the left and the bare biproduct projection on the right. -/
noncomputable def midSc (k : ℤ) : ShortComplex (SheafOfModules.{m} R) :=
  ShortComplex.mk
    ((biprod.snd : Cofree.piece (N.shift (-1)) k ⟶ (N.shift (-1)).piece (k + 1))
      ≫ (biprod.inl : (N.shift (-1)).piece (k + 1) ⟶ Cofree.piece (N.shift (-1)) (k + 1)))
    (biprod.snd : Cofree.piece (N.shift (-1)) (k + 1) ⟶ (N.shift (-1)).piece (k + 1 + 1))
    (by simp)

/-- The short complex `Hull.splitSc N k` is exact. -/
theorem splitSc_exact (k : ℤ) [HasZeroObject (SheafOfModules.{m} R)] :
    (splitSc N k).Exact :=
  ShortComplex.Splitting.exact
    { r := biprod.fst
      s := biprod.inr
      f_r := biprod.inl_fst
      s_g := biprod.inr_snd
      id := biprod.total }

/-- Shrinking the right-hand term of `Hull.midSc` to the biproduct projection. -/
noncomputable def midScToSplitSc (k : ℤ) : midSc N k ⟶ splitSc N k where
  τ₁ := biprod.snd
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _

/-- Enlarging the right-hand term of `Hull.midSc` to the full biproduct piece. -/
noncomputable def midScToHullSc (k : ℤ) : midSc N k ⟶ hullSc N k where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := biprod.inl

/-- The left component of `midScToSplitSc N k` is an epimorphism. -/
instance epi_midScToSplitSc_τ₁ (k : ℤ) : Epi (midScToSplitSc N k).τ₁ :=
  (inferInstance :
    Epi (biprod.snd : Cofree.piece (N.shift (-1)) k ⟶ (N.shift (-1)).piece (k + 1)))

/-- The middle component of `midScToSplitSc N k` is an isomorphism. -/
instance isIso_midScToSplitSc_τ₂ (k : ℤ) : IsIso (midScToSplitSc N k).τ₂ :=
  (inferInstance : IsIso (𝟙 (Cofree.piece (N.shift (-1)) (k + 1))))

/-- The right component of `midScToSplitSc N k` is a monomorphism. -/
instance mono_midScToSplitSc_τ₃ (k : ℤ) : Mono (midScToSplitSc N k).τ₃ :=
  (inferInstance : Mono (𝟙 ((N.shift (-1)).piece (k + 1 + 1))))

/-- The left component of `midScToHullSc N k` is an epimorphism. -/
instance epi_midScToHullSc_τ₁ (k : ℤ) : Epi (midScToHullSc N k).τ₁ :=
  (inferInstance : Epi (𝟙 (Cofree.piece (N.shift (-1)) k)))

/-- The middle component of `midScToHullSc N k` is an isomorphism. -/
instance isIso_midScToHullSc_τ₂ (k : ℤ) : IsIso (midScToHullSc N k).τ₂ :=
  (inferInstance : IsIso (𝟙 (Cofree.piece (N.shift (-1)) (k + 1))))

/-- The right component of `midScToHullSc N k` is a monomorphism. -/
instance mono_midScToHullSc_τ₃ (k : ℤ) : Mono (midScToHullSc N k).τ₃ :=
  (inferInstance :
    Mono (biprod.inl : (N.shift (-1)).piece (k + 1 + 1)
      ⟶ Cofree.piece (N.shift (-1)) (k + 1 + 1)))

/-- The short complex `Hull.hullSc N k` of two consecutive differentials of the hull is
exact. -/
theorem hullSc_exact (k : ℤ) [HasZeroObject (SheafOfModules.{m} R)] :
    (hullSc N k).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (midScToHullSc N k)).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono (midScToSplitSc N k)).2
      (splitSc_exact N k))

/-- The complex underlying the differential graded hull is acyclic: in each degree the kernel
of the differential is the first summand, which is also its image. -/
theorem acyclic : ((obj N).complex).Acyclic := by
  have hzero : HasZeroObject (SheafOfModules.{m} R) := hasZeroObject_of_hasTerminal_object
  have key : ∀ k : ℤ, ((obj N).complex).ExactAt (k + 1) := by
    intro k
    rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 1 + 1)
      (by rw [CochainComplex.prev]; omega) (by rw [CochainComplex.next])]
    refine ShortComplex.exact_of_iso (S₁ := hullSc N k) ?_ (hullSc_exact N k)
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · exact (Category.id_comp _).trans
        ((complex_d N k).trans (Category.comp_id (hullSc N k).f).symm)
    · exact (Category.id_comp _).trans
        ((complex_d N (k + 1)).trans (Category.comp_id (hullSc N k).g).symm)
  intro j
  have h := key (j - 1)
  rwa [sub_add_cancel] at h

/-- The hom-bijection exhibiting the differential graded hull as left adjoint to forgetting
the differential. -/
noncomputable def homEquiv (M : DifferentialGradedModule.{t, a, m} A) :
    (obj N ⟶ M) ≃ (N ⟶ (forgetToGradedModule A).obj M) where
  toFun := lowerHom N
  invFun := descDgHom N
  left_inv := descDgHom_lowerHom N
  right_inv := lowerHom_descDgHom N

/-- The hom-bijection is natural in the differential graded module. -/
theorem homEquiv_naturality (M M' : DifferentialGradedModule.{t, a, m} A) (g : M ⟶ M')
    (ψ : obj N ⟶ M) :
    homEquiv N M' (ψ ≫ g) = homEquiv N M ψ ≫ (forgetToGradedModule A).map g :=
  GradedModule.Hom.ext fun _ => (Category.assoc _ _ _).symm

end Hull

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The differential graded hull functor: the left adjoint to forgetting the differential of a
right differential graded module. -/
noncomputable def dgHullFunctor (A : DifferentialGradedAlgebra.{t, a} R) :
    GradedModule.{t, a, m} A.toGradedAlgebra ⥤ DifferentialGradedModule.{t, a, m} A :=
  Adjunction.leftAdjointOfEquiv (G := forgetToGradedModule.{t, a, m} A)
    (F_obj := Hull.obj) Hull.homEquiv Hull.homEquiv_naturality

/-- The differential graded hull is left adjoint to forgetting the differential. -/
noncomputable def dgHullAdjunction (A : DifferentialGradedAlgebra.{t, a} R) :
    dgHullFunctor.{t, a, m} A ⊣ forgetToGradedModule.{t, a, m} A :=
  Adjunction.adjunctionOfEquivLeft Hull.homEquiv Hull.homEquiv_naturality

/-- For a sheaf of differential graded algebras, the functor from right differential graded
modules to right graded modules that forgets the differential has a left adjoint. -/
@[stacks 0FSK]
instance forgetToGradedModule_isRightAdjoint (A : DifferentialGradedAlgebra.{t, a} R) :
    (forgetToGradedModule.{t, a, m} A).IsRightAdjoint :=
  ⟨⟨dgHullFunctor A, ⟨dgHullAdjunction A⟩⟩⟩

namespace Hull

variable (N : GradedModule.{t, a, m} A.toGradedAlgebra)

/-- The unit of `dgHullAdjunction A` at `N` is `lowerHom N (𝟙 (obj N))`. -/
theorem unit_dgHullAdjunction_app :
    (dgHullAdjunction A).unit.app N = lowerHom N (𝟙 (obj N)) := by
  rw [← Adjunction.homEquiv_id]
  rfl

/-- The unit of `dgHullAdjunction A` at `N` is a monomorphism. -/
theorem mono_unit_dgHullAdjunction : Mono ((dgHullAdjunction A).unit.app N) := by
  rw [unit_dgHullAdjunction_app]
  refine GradedModule.mono_of_mono_app _ fun n => ?_
  change Mono (unitHom N n ≫ 𝟙 _)
  rw [Category.comp_id]
  infer_instance

end Hull

/-- Forgetting the action of a right differential graded module, keeping its complex. -/
def toCochainComplex (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedModule.{t, a, m} A ⥤ CochainComplex (SheafOfModules.{m} R) ℤ where
  obj M := M.complex
  map f := f.toHomologicalComplex
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The differential graded hull of a right graded module is acyclic. -/
@[stacks 0FSL "part (3)"]
theorem dgHull_acyclic (A : DifferentialGradedAlgebra.{t, a} R)
    (N : GradedModule.{t, a, m} A.toGradedAlgebra) :
    (((forgetToGradedModule.{t, a, m} A).leftAdjoint.obj N).complex).Acyclic := by
  have e : Hull.obj N ≅ (forgetToGradedModule.{t, a, m} A).leftAdjoint.obj N :=
    (Adjunction.leftAdjointUniq (dgHullAdjunction A)
      (Adjunction.ofIsRightAdjoint (forgetToGradedModule.{t, a, m} A))).app N
  intro j
  exact (Hull.acyclic N j).of_iso ((toCochainComplex A).mapIso e)

/-- The unit of the adjunction embeds a right graded module into its differential graded
hull. -/
@[stacks 0FSL "part (1)"]
theorem dgHull_unit_mono (A : DifferentialGradedAlgebra.{t, a} R)
    (N : GradedModule.{t, a, m} A.toGradedAlgebra) :
    Mono ((Adjunction.ofIsRightAdjoint (forgetToGradedModule.{t, a, m} A)).unit.app N) := by
  have := Hull.mono_unit_dgHullAdjunction N
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (dgHullAdjunction A)
    (Adjunction.ofIsRightAdjoint (forgetToGradedModule.{t, a, m} A)) N]
  exact mono_comp _ _

end SheafOfModules
