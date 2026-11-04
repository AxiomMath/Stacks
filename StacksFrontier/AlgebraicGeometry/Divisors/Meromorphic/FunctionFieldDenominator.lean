module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FunctionFieldSection

/-!
# The ideal of denominators of a rational function

Let `X` be an integral scheme and `g` a nonzero rational function on `X`, read as a regular
meromorphic section of `𝒪_X` by `AlgebraicGeometry.meromorphicSectionOfFunctionField`. The ideal
of denominators `I` of that section carries two maps to `𝒪_X`: the inclusion
`AlgebraicGeometry.denominatorIdealι` and multiplication by `g`,
`AlgebraicGeometry.denominatorIdealMul`. This file identifies the two on germs at the generic
point — multiplication by `g` really is multiplication by `g` — and then on stalks at an
arbitrary point, where the two composites with the comparison of the stalk of `𝒪_X` with the
local ring are the two linear maps `i, j : I_x →ₗ[𝒪_{X,x}] 𝒪_{X,x}` with `g · i = j` whose
quotient lengths differ by `ord_x(g)`.

The last statement is the hypothesis of the ring-level computation in the proof of
Stacks 0FDS, and together with the nondegeneracy statement
`AlgebraicGeometry.exists_unitStalkLinearMap_denominatorIdealι_ne_zero` it is everything that
computation needs at a point.

## Main results

* `AlgebraicGeometry.meromorphicSectionMul_comp_meromorphicUnitToUnit` — multiplication by the
  section attached to `g`, followed by the identification `K_X(𝒪_X) ≅ K_X`, is the canonical map
  `𝒪_X ⟶ K_X` followed by multiplication by `g`.
* `AlgebraicGeometry.germToFunctionField_denominatorIdealMul` — on a section of the ideal of
  denominators over an open set, the germ at the generic point of its image under multiplication
  by `g` is `g` times the germ of its image under the inclusion.
* `AlgebraicGeometry.exists_denominatorIdealι_app_eq_of_germ_mul` — conversely, a section `b` of
  `𝒪_X` whose product with `g` is the germ of a section of `𝒪_X` is a denominator.
* `AlgebraicGeometry.mul_algebraMap_unitStalkLinearMap_denominatorIdealι` — **the stalk
  identity** `g · i(m) = j(m)` in the function field.
* `AlgebraicGeometry.exists_unitStalkLinearMap_denominatorIdealι_ne_zero` — the stalk of the
  inclusion is not identically zero.

## Implementation notes

The whole file is a chain of two identities read at an open set, and both are proved in term
mode. `rw` and `simp` cannot be used on any of these goals: the structure sheaf of a scheme is
spelled both `TopCat.Sheaf CommRingCat X` and `CategoryTheory.Sheaf (Opens.grothendieckTopology X)
CommRingCat`, and those are not identified at the `implicit` transparency level a motive check
uses, so a rewrite reports the target as not type-correct. Each step is therefore an explicit
`Eq.trans` of `congrArg`s, and the implicit module arguments of
`CategoryTheory.SheafOfModules.unitHomEquiv_symm_comp` are supplied by name — left to
unification they are solved with the module over the sheaf of meromorphic functions instead of
its restriction of scalars, and the statement then does not typecheck.

The first identity is the transpose, across the change-of-rings adjunction along `𝒪_X ⟶ K_X`, of
the fact that the section attached to `g` corresponds to multiplication by `g` on `K_X`; the
second, for the canonical map `𝒪_X ⟶ K_X(𝒪_X)`, is
`AlgebraicGeometry.unit_comp_meromorphicUnitToUnit`. Composing the commuting square of the fibre
product defining the ideal of denominators with the identification `K_X(𝒪_X) ≅ K_X` and using
both turns that square into an identity between sections of `K_X`, which the injectivity of
`AlgebraicGeometry.functionFieldToTotalQuotientSheaf` on a nonempty open set transports to the
function field.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample (unitModule)

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] (g : X.functionFieldˣ)

/-! ### The canonical map `𝒪_X ⟶ K_X` on sections -/

/-- A nonempty open set of an integral scheme contains the generic point. -/
private theorem genericPoint_mem_of_nonempty (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- Equal morphisms of sheaves of modules agree on sections over an open set. -/
private theorem val_app_apply_eq_of_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} {f f' : M ⟶ N} (h : f = f') (U : Cᵒᵖ)
    (z : M.val.obj U) : f.val.app U z = f'.val.app U z :=
  ConcreteCategory.congr_hom (congrArg (fun q => q.val.app U) h) z

omit [IsIntegral X] in
/-- The canonical `𝒪_X`-linear map `𝒪_X ⟶ K_X` is, on the sections over an open set, the
canonical ring map to the sheaf of meromorphic functions: it is multiplication by the section
`1`. -/
theorem toKUnit_val_app_apply (U : (Opens X)ᵒᵖ)
    (b : (SheafOfModules.unit X.ringCatSheaf).val.obj U) :
    (toKUnit X).val.app U b = (toTotalQuotientRingSheaf X).hom.app U b :=
  mul_one ((toTotalQuotientRingSheaf X).hom.app U b)

/-! ### Multiplication by the section attached to `g` -/

/-- The global section of `K_X` underlying the section of `K_X(𝒪_X)` attached to `g` is `g`
itself: both are the image of multiplication by `g` under the bijection between morphisms out of
`K_X` and global sections. -/
theorem sectionsMap_meromorphicSectionOfFunctionField :
    SheafOfModules.sectionsMap (meromorphicUnitToUnit X)
        (meromorphicSectionOfFunctionField X g) =
      SheafOfModules.sectionsMap (unitIsoOfFunctionFieldUnit X g).hom (kOne X) :=
  ((SheafOfModules.unitHomEquiv_comp_apply
      ((unitIsoOfFunctionFieldUnit X g).hom ≫ (unitIsoMeromorphicSectionSheafUnit X).hom)
      (meromorphicUnitToUnit X)).symm.trans
    (congrArg
      (fun t => (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)).unitHomEquiv t)
      (((Category.assoc _ _ _).trans
        (congrArg (fun t => (unitIsoOfFunctionFieldUnit X g).hom ≫ t)
          (unitIsoMeromorphicSectionSheafUnit X).hom_inv_id)).trans
        (Category.comp_id _)))).trans
    ((congrArg
        (fun t => (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)).unitHomEquiv t)
        (Category.id_comp (unitIsoOfFunctionFieldUnit X g).hom)).symm.trans
      (SheafOfModules.unitHomEquiv_comp_apply (𝟙 _) (unitIsoOfFunctionFieldUnit X g).hom))

/-- **Multiplication by the meromorphic section attached to `g` is multiplication by `g`.**
Followed by the identification `K_X(𝒪_X) ≅ K_X` it is the canonical map `𝒪_X ⟶ K_X` followed by
the automorphism of `K_X` given by `g`. -/
theorem meromorphicSectionMul_comp_meromorphicUnitToUnit :
    meromorphicSectionMul X (SheafOfModules.unit X.ringCatSheaf)
          (meromorphicSectionOfFunctionField X g) ≫
        (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
          (meromorphicUnitToUnit X) =
      toKUnit X ≫ (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitIsoOfFunctionFieldUnit X g).hom :=
  (SheafOfModules.unitHomEquiv_symm_comp
      (M := meromorphicSectionSheafAsModule X (SheafOfModules.unit X.ringCatSheaf))
      (N := (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
        (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)))
      (meromorphicSectionOfFunctionField X g)
      ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (meromorphicUnitToUnit X))).trans
    ((congrArg (fun t => ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
        (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X))).unitHomEquiv.symm t)
      (sectionsMap_meromorphicSectionOfFunctionField X g)).trans
      (SheafOfModules.unitHomEquiv_symm_comp
        (M := (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
          (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)))
        (N := (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
          (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)))
        (kOne X)
        ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
          (unitIsoOfFunctionFieldUnit X g).hom)).symm)

/-- The right-hand side of `meromorphicSectionMul_comp_meromorphicUnitToUnit`, read on the
sections over an open set: the canonical ring map to `K_X`, times `g`. -/
theorem unitIsoOfFunctionFieldUnit_hom_toKUnit_app (U : (Opens X)ᵒᵖ)
    (b : (SheafOfModules.unit X.ringCatSheaf).val.obj U) :
    (show (totalQuotientSheaf X.sheaf).obj.obj U from
      ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitIsoOfFunctionFieldUnit X g).hom).val.app U ((toKUnit X).val.app U b)) =
      (toTotalQuotientSheaf X.sheaf).hom.app U b *
        (functionFieldToTotalQuotientSheaf X).app U (g : X.functionField) :=
  congrArg (fun t => t * (functionFieldToTotalQuotientSheaf X).app U (g : X.functionField))
    (mul_one ((toTotalQuotientRingSheaf X).hom.app U b))

/-! ### The commuting square of the ideal of denominators -/

/-- **The commuting square of the fibre product, transported to `K_X`.** The inclusion of the
ideal of denominators followed by the canonical map to `K_X` and multiplication by `g` is
multiplication by `g` on the ideal followed by the canonical map to `K_X`. -/
theorem denominatorIdealι_comp_toKUnit :
    denominatorIdealι X (unitModule X) (meromorphicSectionOfFunctionField X g) ≫
        toKUnit X ≫ (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
          (unitIsoOfFunctionFieldUnit X g).hom =
      denominatorIdealMul X (unitModule X) (meromorphicSectionOfFunctionField X g) ≫
        toKUnit X :=
  (congrArg
      (fun q => denominatorIdealι X (unitModule X)
        (meromorphicSectionOfFunctionField X g) ≫ q)
      (meromorphicSectionMul_comp_meromorphicUnitToUnit X g).symm).trans
    (((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ (SheafOfModules.restrictScalars
          (toTotalQuotientRingSheaf X)).map (meromorphicUnitToUnit X))
        (pullback.condition
          (f := meromorphicSectionMul X (unitModule X)
            (meromorphicSectionOfFunctionField X g))
          (g := toMeromorphicSectionSheafAsModule X (unitModule X)))).trans
        (Category.assoc _ _ _))).trans
      (congrArg
        (fun q => denominatorIdealMul X (unitModule X)
          (meromorphicSectionOfFunctionField X g) ≫ q)
        (unit_comp_meromorphicUnitToUnit X)))

/-- The commuting square read on a section of the ideal of denominators, as an identity between
sections of `K_X`. -/
theorem denominatorIdealι_comp_toKUnit_app (U : (Opens X)ᵒᵖ)
    (d : (denominatorIdeal X (unitModule X)
      (meromorphicSectionOfFunctionField X g)).val.obj U) :
    (toTotalQuotientSheaf X.sheaf).hom.app U
        ((denominatorIdealι X (unitModule X)
          (meromorphicSectionOfFunctionField X g)).val.app U d) *
        (functionFieldToTotalQuotientSheaf X).app U (g : X.functionField) =
      (toTotalQuotientSheaf X.sheaf).hom.app U
        ((denominatorIdealMul X (unitModule X)
          (meromorphicSectionOfFunctionField X g)).val.app U d) :=
  (unitIsoOfFunctionFieldUnit_hom_toKUnit_app X g U _).symm.trans
    ((val_app_apply_eq_of_eq (denominatorIdealι_comp_toKUnit X g) U d).trans
      (toKUnit_val_app_apply X U _))

/-! ### The two maps on germs at the generic point -/

/-- **Multiplication by `g` on the ideal of denominators is multiplication by `g`.** On a section
of the ideal over an open set, the germ at the generic point of its image under multiplication by
`g` is the germ of its image under the inclusion, times `g`. -/
theorem germToFunctionField_denominatorIdealMul (U : X.Opens) [Nonempty U]
    (d : (denominatorIdeal X (unitModule X)
      (meromorphicSectionOfFunctionField X g)).val.obj (op U)) :
    X.germToFunctionField U
          ((denominatorIdealι X (unitModule X)
            (meromorphicSectionOfFunctionField X g)).val.app (op U) d) *
        (g : X.functionField) =
      X.germToFunctionField U
        ((denominatorIdealMul X (unitModule X)
          (meromorphicSectionOfFunctionField X g)).val.app (op U) d) := by
  have hU := genericPoint_mem_of_nonempty X U
  refine functionFieldToTotalQuotientSheaf_app_injective X U ⟨genericPoint X, hU⟩ ?_
  exact (map_mul _ _ _).trans
    ((congrArg
        (fun t => t * (functionFieldToTotalQuotientSheaf X).app (op U) (g : X.functionField))
        (functionFieldToTotalQuotientSheaf_germ X U _ hU)).trans
      ((denominatorIdealι_comp_toKUnit_app X g (op U) d).trans
        (functionFieldToTotalQuotientSheaf_germ X U _ hU).symm))

/-- **The denominator rule for a rational function.** A section `b` of `𝒪_X` over an open set
whose product with `g` is the germ at the generic point of a section `a` of `𝒪_X` there is a
denominator of `g`. -/
theorem exists_denominatorIdealι_app_eq_of_germ_mul (U : X.Opens) [Nonempty U] (a b : Γ(X, U))
    (hab : X.germToFunctionField U b * (g : X.functionField) = X.germToFunctionField U a) :
    ∃ d : (denominatorIdeal X (unitModule X)
      (meromorphicSectionOfFunctionField X g)).val.obj (op U),
      (denominatorIdealι X (unitModule X)
        (meromorphicSectionOfFunctionField X g)).val.app (op U) d = b := by
  have hU := genericPoint_mem_of_nonempty X U
  refine (exists_denominatorIdeal_inclusion_app_eq_iff X (unitModule X)
    (meromorphicSectionOfFunctionField X g) U b).mpr ⟨a, ?_⟩
  have hinj : Function.Injective
      (((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (meromorphicUnitToUnit X)).val.app (op U)) := by
    intro v w hvw
    have hid (z) :=
      val_app_apply_eq_of_eq (unitIsoMeromorphicSectionSheafUnit X).inv_hom_id (op U) z
    exact (hid v).symm.trans
      ((congrArg (fun z => (unitIsoMeromorphicSectionSheafUnit X).hom.val.app (op U) z)
        hvw).trans (hid w))
  refine hinj ?_
  let a' : (SheafOfModules.unit X.ringCatSheaf).val.obj (op U) := a
  let b' : (SheafOfModules.unit X.ringCatSheaf).val.obj (op U) := b
  have h₁ := (val_app_apply_eq_of_eq
      (meromorphicSectionMul_comp_meromorphicUnitToUnit X g) (op U) b').trans
    (unitIsoOfFunctionFieldUnit_hom_toKUnit_app X g (op U) b')
  have h₂ := (val_app_apply_eq_of_eq (unit_comp_meromorphicUnitToUnit X) (op U) a').trans
    (toKUnit_val_app_apply X (op U) a')
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  exact (congrArg
      (fun t => t * (functionFieldToTotalQuotientSheaf X).app (op U) (g : X.functionField))
      (functionFieldToTotalQuotientSheaf_germ X U b hU).symm).trans
    (((map_mul _ _ _).symm.trans
      (congrArg (fun t => (functionFieldToTotalQuotientSheaf X).app (op U) t) hab)).trans
      (functionFieldToTotalQuotientSheaf_germ X U a hU))

/-! ### The two maps on a stalk -/

/-- **The stalk identity.** At any point, the stalk of multiplication by `g` on the ideal of
denominators is `g` times the stalk of the inclusion, read in the function field. This is the
hypothesis `g · i(m) = j(m)` of the length computation in the proof of Stacks 0FDS. -/
theorem mul_algebraMap_unitStalkLinearMap_denominatorIdealι (x : X)
    (m : (Scheme.Modules.presheaf (denominatorIdeal X (unitModule X)
      (meromorphicSectionOfFunctionField X g))).stalk x) :
    (g : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField
        (Scheme.Modules.unitStalkLinearMap x
          (denominatorIdealι X (unitModule X) (meromorphicSectionOfFunctionField X g)) m) =
      algebraMap (X.presheaf.stalk x) X.functionField
        (Scheme.Modules.unitStalkLinearMap x
          (denominatorIdealMul X (unitModule X) (meromorphicSectionOfFunctionField X g)) m) := by
  obtain ⟨U, hx, d, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (Scheme.Modules.presheaf (denominatorIdeal X (unitModule X)
      (meromorphicSectionOfFunctionField X g))) m
  have hne : Nonempty U := ⟨⟨x, hx⟩⟩
  exact (congrArg
      (fun t => (g : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField t)
      (Scheme.Modules.unitStalkLinearMap_germ x _ U hx d)).trans
    (((congrArg (fun t => (g : X.functionField) * t)
        (X.algebraMap_germ_eq_germToFunctionField hx _)).trans
      ((mul_comm _ _).trans (germToFunctionField_denominatorIdealMul X g U d))).trans
      ((X.algebraMap_germ_eq_germToFunctionField hx _).symm.trans
        (congrArg (fun t => algebraMap (X.presheaf.stalk x) X.functionField t)
          (Scheme.Modules.unitStalkLinearMap_germ x _ U hx d).symm)))

/-- **The stalk of the inclusion is not identically zero.** A denominator of `g` at `x` is
provided by the denominator of a presentation of `g` as a fraction over the local ring, which is
a nonzerodivisor there and so has nonzero germ. -/
theorem exists_unitStalkLinearMap_denominatorIdealι_ne_zero (x : X) :
    ∃ m, Scheme.Modules.unitStalkLinearMap x
      (denominatorIdealι X (unitModule X) (meromorphicSectionOfFunctionField X g)) m ≠ 0 := by
  obtain ⟨U, hxU, a, ha⟩ := X.presheaf.exists_germ_eq
    (IsLocalization.sec (nonZeroDivisors (X.presheaf.stalk x)) (g : X.functionField)).1
  obtain ⟨V, hxV, b, hb⟩ := X.presheaf.exists_germ_eq
    ((IsLocalization.sec (nonZeroDivisors (X.presheaf.stalk x))
      (g : X.functionField)).2 : X.presheaf.stalk x)
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  have hne : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hxW⟩⟩
  have ha' : X.presheaf.germ (U ⊓ V) x hxW
      (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) =
      (IsLocalization.sec (nonZeroDivisors (X.presheaf.stalk x)) (g : X.functionField)).1 :=
    (TopCat.Presheaf.germ_res_apply X.presheaf _ x hxW a).trans ha
  have hb' : X.presheaf.germ (U ⊓ V) x hxW
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b) =
      ((IsLocalization.sec (nonZeroDivisors (X.presheaf.stalk x))
        (g : X.functionField)).2 : X.presheaf.stalk x) :=
    (TopCat.Presheaf.germ_res_apply X.presheaf _ x hxW b).trans hb
  have hab : X.germToFunctionField (U ⊓ V)
        (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b) *
        (g : X.functionField) =
      X.germToFunctionField (U ⊓ V)
        (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) := by
    have key : (g : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField
          (X.presheaf.germ (U ⊓ V) x hxW
            (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b)) =
        algebraMap (X.presheaf.stalk x) X.functionField
          (X.presheaf.germ (U ⊓ V) x hxW
            (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a)) := by
      rw [ha', hb']
      exact IsLocalization.sec_spec _ _
    exact (congrArg (fun t => t * (g : X.functionField))
        (X.algebraMap_germ_eq_germToFunctionField hxW _).symm).trans
      ((mul_comm _ _).trans (key.trans (X.algebraMap_germ_eq_germToFunctionField hxW _)))
  obtain ⟨d, hd⟩ := exists_denominatorIdealι_app_eq_of_germ_mul X g (U ⊓ V) _ _ hab
  refine ⟨(Scheme.Modules.presheaf (denominatorIdeal X (unitModule X)
    (meromorphicSectionOfFunctionField X g))).germ (U ⊓ V) x hxW d, ?_⟩
  refine (((Scheme.Modules.unitStalkLinearMap_germ x _ (U ⊓ V) hxW d).trans
    (congrArg (X.presheaf.germ (U ⊓ V) x hxW) hd)).trans hb') ▸ ?_
  exact mem_nonZeroDivisors_iff_ne_zero.mp
    (IsLocalization.sec (nonZeroDivisors (X.presheaf.stalk x)) (g : X.functionField)).2.property

end AlgebraicGeometry
