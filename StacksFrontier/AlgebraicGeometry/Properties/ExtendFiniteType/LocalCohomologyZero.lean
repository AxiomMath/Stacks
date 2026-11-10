module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.RingTheory.Finiteness.Ideal
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn

/-!
# Local cohomology in degree zero

Let `A` be a commutative ring and `I ⊆ A` a finitely generated ideal. Two constructions of the
degree-zero local cohomology of an `A`-module `M` with support in `Z = V(I)` are available, and
this module identifies both of them with the `I`-power-torsion submodule of `M`.

## Main results

* `Module.sectionsWithSupportIn_zeroLocus`: sections with support in the closed set `V(I)` are
  exactly the `I`-power-torsion submodule.
* `Stacks.LocalCohomologyZero.extZeroNatIso`: degree-zero `Ext` into a fixed module is the
  module of homomorphisms into it.
* `Stacks.LocalCohomologyZero.localCohomologyZeroIso`: the degree-zero local cohomology of a
  module with support in `V(I)` is the `I`-power-torsion submodule.
* `Stacks.LocalCohomologyZero.localCohomologyZeroIsoSectionsWithSupportIn`: for a finitely
  generated ideal, that degree-zero local cohomology agrees with the degree-zero sections with
  support in the closed set `V(I)`.

## Implementation notes

`Stacks.LocalCohomology.sectionsWithSupportIn A T M` is a supremum over all ideals whose zero
locus is contained in `T`; when `T` is itself the zero locus of a finitely generated ideal `I`,
that supremum collapses onto the powers of `I`, because an inclusion of zero loci is an
inclusion of radicals and a finitely generated ideal inside a radical has a power inside the
ideal.

`localCohomology I 0` is a colimit of `Ext⁰(A / Iⁿ, -)` taken in the category of endofunctors of
`ModuleCat A`. Evaluating it at `M` commutes with the colimit
(`colimitObjIsoColimitCompEvaluation`), so the computation reduces to exhibiting the
`I`-power-torsion submodule as the colimit of the modules `Hom(A / Iⁿ, M)`. The required
degree-zero identification of `Ext` is `Functor.leftDerivedZeroIsoSelf` applied to
`((linearYoneda A (ModuleCat A)).obj M).rightOp`; the two preservation instances it needs are
supplied here, since `Hom(-, M)` preserves finite limits for the reason that it does so after
composing with the forgetful functor to types.

The colimit cocone sends a homomorphism `A / Iⁿ ⟶ M` to its value on the class of `1`, which is
killed by `Iⁿ`. The induced map out of the colimit is shown to be bijective rather than to be a
colimit comparison in the abstract: every element of the colimit is represented in a single term
of the system (`Concrete.colimit_exists_rep`, available because the index category is filtered
and the forgetful functor preserves filtered colimits), evaluation at the class of `1` is
injective on each term because a homomorphism out of a cyclic module is determined by that
value, and it is surjective onto the torsion submodule because an element killed by `Iⁿ` spans
such a homomorphism.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite localCohomology

universe u v

namespace Module

open Stacks.LocalCohomology (sectionsWithSupportIn mem_sectionsWithSupportIn_iff)

/-- Sections with support in the zero locus of a finitely generated ideal `I` are the
`I`-power-torsion submodule. -/
theorem sectionsWithSupportIn_zeroLocus (A : Type u) [CommRing A] {I : Ideal A} (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module A M] :
    sectionsWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A)) M = I.primaryComponent M := by
  ext m
  rw [mem_sectionsWithSupportIn_iff, Ideal.primaryComponent_mem,
    PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h hI
    exact ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr fun a ↦
      (Ideal.mem_torsionOf_iff m (a : A)).mp (hn a.property)⟩
  · rintro ⟨n, hn⟩ a ha
    exact ⟨n, (Ideal.mem_torsionOf_iff m (a ^ n)).mpr
      ((Submodule.mem_torsionBySet_iff _ _).mp hn ⟨a ^ n, Ideal.pow_mem_pow ha n⟩)⟩

end Module

namespace Stacks.LocalCohomologyZero

variable {A : Type u} [CommRing A]

/-- Taking `unop` componentwise turns an isomorphism of functors into `Dᵒᵖ` into an isomorphism
of the associated functors out of `Cᵒᵖ`. -/
def natIsoLeftOp {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ Dᵒᵖ} (α : F ≅ G) :
    G.leftOp ≅ F.leftOp where
  hom := NatTrans.leftOp α.hom
  inv := NatTrans.leftOp α.inv
  hom_inv_id := by rw [← NatTrans.leftOp_comp, α.inv_hom_id, NatTrans.leftOp_id]
  inv_hom_id := by rw [← NatTrans.leftOp_comp, α.hom_inv_id, NatTrans.leftOp_id]

/-- The functor of homomorphisms into a fixed module, `Hom(-, M)`, preserves finite limits. -/
instance linearYonedaObj_preservesFiniteLimits (M : ModuleCat.{u} A) :
    PreservesFiniteLimits ((linearYoneda A (ModuleCat.{u} A)).obj M) := by
  constructor
  intro J _ _
  constructor
  intro K
  have : PreservesLimit K
      ((linearYoneda A (ModuleCat.{u} A)).obj M ⋙ forget (ModuleCat.{u} A)) := by
    change PreservesLimit K (yoneda.obj M)
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (forget (ModuleCat.{u} A))

/-- The opposite of the functor `Hom(-, M)`, as a functor into the opposite category, preserves
finite colimits. -/
instance linearYonedaObjRightOp_preservesFiniteColimits (M : ModuleCat.{u} A) :
    PreservesFiniteColimits ((linearYoneda A (ModuleCat.{u} A)).obj M).rightOp :=
  preservesFiniteColimits_rightOp _

/-- Degree-zero `Ext` into a fixed module is the module of homomorphisms into it. -/
noncomputable def extZeroNatIso (M : ModuleCat.{u} A) :
    Ext A (ModuleCat.{u} A) 0 ⋙ (evaluation (ModuleCat.{u} A) (ModuleCat.{u} A)).obj M ≅
      (linearYoneda A (ModuleCat.{u} A)).obj M :=
  (natIsoLeftOp ((linearYoneda A (ModuleCat.{u} A)).obj M).rightOp.leftDerivedZeroIsoSelf).symm

/-- The system of modules of homomorphisms out of the quotients by the powers of `I`, whose
colimit is the degree-zero local cohomology with support in `V(I)`. -/
noncomputable abbrev homPowersDiagram (I : Ideal A) (M : ModuleCat.{u} A) :
    (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} A :=
  (ringModIdeals (idealPowersDiagram I)).op ⋙ (linearYoneda A (ModuleCat.{u} A)).obj M

/-- Degree-zero local cohomology, evaluated at a module, is the colimit of the system of
homomorphism modules out of the quotients by the powers of the ideal. -/
noncomputable def localCohomologyZeroObjIso (I : Ideal A) (M : ModuleCat.{u} A) :
    (localCohomology I 0).obj M ≅ colimit (homPowersDiagram I M) :=
  colimitObjIsoColimitCompEvaluation _ _ ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft _ (extZeroNatIso M))

/-- Scalar multiplication of the class of `1` in `A / J` by `a` gives the class of `a`. -/
private theorem smul_mk_one (J : Ideal A) (a : A) :
    a • (Submodule.Quotient.mk 1 : A ⧸ J) = Submodule.Quotient.mk a := by
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

/-- The value at the class of `1` of a homomorphism out of `A / Iⁿ` is `I`-power torsion. -/
theorem evalOne_mem (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ)
    (f : (ModuleCat.of A (A ⧸ I ^ n) : ModuleCat.{u} A) ⟶ M) :
    f.hom (Submodule.Quotient.mk 1) ∈ I.primaryComponent M := by
  refine (Ideal.primaryComponent_mem _ I _).mpr
    ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr fun a ↦ ?_⟩
  rw [← map_smul, smul_mk_one, (Submodule.Quotient.mk_eq_zero _).mpr a.2, map_zero]

/-- Evaluation at the class of `1`, as a map into the `I`-power-torsion submodule. -/
noncomputable def evalOne (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    ((ModuleCat.of A (A ⧸ I ^ n) : ModuleCat.{u} A) ⟶ M) →ₗ[A] I.primaryComponent M where
  toFun f := ⟨f.hom (Submodule.Quotient.mk 1), evalOne_mem I M n f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cocone on the system of homomorphism modules with vertex the `I`-power-torsion
submodule, given by evaluation at the class of `1`. -/
noncomputable def evalOneCocone (I : Ideal A) (M : ModuleCat.{u} A) :
    Cocone (homPowersDiagram I M) where
  pt := ModuleCat.of A (I.primaryComponent M)
  ι :=
    { app := fun j ↦ ModuleCat.ofHom (evalOne I M j.unop.unop)
      naturality := fun _ _ _ ↦ rfl }

/-- The homomorphism out of `A / Iⁿ` determined by an element killed by `Iⁿ`. -/
noncomputable def ofTorsion (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ)
    (x : M) (hx : x ∈ Submodule.torsionBySet A M ((I ^ n : Ideal A) : Set A)) :
    (ModuleCat.of A (A ⧸ I ^ n) : ModuleCat.{u} A) ⟶ M :=
  ModuleCat.ofHom <| Submodule.liftQ _ (LinearMap.toSpanSingleton A M x) <| fun a ha ↦ by
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨a, ha⟩

/-- Evaluating `ofTorsion` at the class of `1` returns the element it was built from. -/
theorem evalOne_ofTorsion (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ)
    (x : M) (hx : x ∈ Submodule.torsionBySet A M ((I ^ n : Ideal A) : Set A)) :
    (ofTorsion I M n x hx).hom (Submodule.Quotient.mk 1) = x := by
  change (LinearMap.toSpanSingleton A (M : Type u) x) 1 = x
  exact one_smul A x

/-- A homomorphism out of `A / Iⁿ` vanishing on the class of `1` is zero. -/
theorem eq_zero_of_evalOne_eq_zero (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ)
    (f : (ModuleCat.of A (A ⧸ I ^ n) : ModuleCat.{u} A) ⟶ M)
    (hf : f.hom (Submodule.Quotient.mk 1) = 0) : f = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← smul_mk_one, map_smul, hf, smul_zero]
  rfl

/-- The forgetful functor preserves the colimit of the homomorphism system, which is filtered. -/
instance forget_preservesColimit_homPowersDiagram (I : Ideal A) (M : ModuleCat.{u} A) :
    PreservesColimit (homPowersDiagram I M) (forget (ModuleCat.{u} A)) := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  infer_instance

/-- The map induced on the colimit by the evaluation cocone, read on a single term. -/
theorem desc_evalOneCocone_ι (I : Ideal A) (M : ModuleCat.{u} A) (j : (ℕᵒᵖ)ᵒᵖ)
    (y : ToType ((homPowersDiagram I M).obj j)) :
    (ConcreteCategory.hom (colimit.desc (homPowersDiagram I M) (evalOneCocone I M)))
        ((ConcreteCategory.hom (colimit.ι (homPowersDiagram I M) j)) y) =
      evalOne I M j.unop.unop y := by
  rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
  rfl

/-- Only the zero element of the colimit is sent to zero by evaluation at the class of `1`. -/
theorem eq_zero_of_desc_evalOneCocone_eq_zero (I : Ideal A) (M : ModuleCat.{u} A)
    (z : ToType (colimit (homPowersDiagram I M)))
    (hz : (ConcreteCategory.hom
      (colimit.desc (homPowersDiagram I M) (evalOneCocone I M))) z = 0) : z = 0 := by
  obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep (homPowersDiagram I M) z
  rw [desc_evalOneCocone_ι] at hz
  have hy : y = 0 :=
    eq_zero_of_evalOne_eq_zero I M j.unop.unop y (congrArg Subtype.val hz)
  rw [hy]
  simp

/-- The colimit of the system of homomorphism modules out of the quotients by the powers of `I`
is the `I`-power-torsion submodule, via evaluation at the class of `1`. -/
noncomputable def homPowersColimitIso (I : Ideal A) (M : ModuleCat.{u} A) :
    colimit (homPowersDiagram I M) ≅ ModuleCat.of A (I.primaryComponent M) := by
  have hiso : IsIso (colimit.desc (homPowersDiagram I M) (evalOneCocone I M)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun z w h ↦ ?_, ?_⟩
    · exact sub_eq_zero.mp (eq_zero_of_desc_evalOneCocone_eq_zero I M (z - w)
        (by rw [map_sub, h, sub_self]))
    · rintro ⟨xv, hxv⟩
      obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (M : Type u) I xv).mp hxv
      exact ⟨(ConcreteCategory.hom (colimit.ι (homPowersDiagram I M) (op (op n))))
          (ofTorsion I M n xv hn),
        (desc_evalOneCocone_ι I M (op (op n)) (ofTorsion I M n xv hn)).trans
          (Subtype.ext (evalOne_ofTorsion I M n xv hn))⟩
  exact @asIso _ _ _ _ (colimit.desc (homPowersDiagram I M) (evalOneCocone I M)) hiso

/-- **The degree-zero local cohomology of a module with support in `V(I)`.** It is the
`I`-power-torsion submodule. -/
noncomputable def localCohomologyZeroIso (I : Ideal A) (M : ModuleCat.{u} A) :
    (localCohomology I 0).obj M ≅ ModuleCat.of A (I.primaryComponent M) :=
  localCohomologyZeroObjIso I M ≪≫ homPowersColimitIso I M

/-- Degree-zero local cohomology agrees with degree-zero sections with support in the closed
set `V(I)`, for a finitely generated ideal `I`. -/
noncomputable def localCohomologyZeroIsoSectionsWithSupportIn {I : Ideal A} (hI : I.FG)
    (M : ModuleCat.{u} A) :
    (localCohomology I 0).obj M ≅
      ModuleCat.of A
        (Stacks.LocalCohomology.sectionsWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A)) M) :=
  localCohomologyZeroIso I M ≪≫
    eqToIso (congrArg (fun S : Submodule A M ↦ ModuleCat.of A S)
      (Module.sectionsWithSupportIn_zeroLocus A hI M).symm)

end Stacks.LocalCohomologyZero

end
