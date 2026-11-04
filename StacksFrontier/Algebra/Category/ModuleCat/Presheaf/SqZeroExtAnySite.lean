module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt

/-!
# Square-zero extensions over a site with independent universes

Let `C : Type u₁` be a category with `Category.{v₁} C`, let `R : Cᵒᵖ ⥤ CommRingCat.{u}` be a
presheaf of commutative rings on it, the three universes being unrelated, and let `M` be a presheaf
of modules over `R`. This file constructs the square-zero extension `R ⊕ M` of `R` by `M` as a
presheaf of commutative rings, whose sections over `U` are `TrivSqZeroExt (R.obj U) (M.obj U)`.
When all three universes agree, `sqZeroExtObjAnySite` and `PresheafOfModules.sqZeroExtObj` are the
same object.

## Main definitions

* `PresheafOfModules.sqZeroExtObjAnySite` and `PresheafOfModules.sqZeroExtMapAnySite`: the sections
  and the restriction maps of the square-zero extension of `R` by `M`.
* `PresheafOfModules.sqZeroExtPresheafAnySite`: the square-zero extension of `R` by `M`, as a
  presheaf of commutative rings on a site with three independent universes.
* `PresheafOfModules.sqZeroExtInlAnySite`: the inclusion of `R` into its square-zero extension.
* `PresheafOfModules.sqZeroExtMkAnySite`, `PresheafOfModules.sqZeroExtFstAnySite` and
  `PresheafOfModules.sqZeroExtSndAnySite`: the accessors for the two components of a section.

## References

* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v₁ u₁

namespace PresheafOfModules

attribute [local instance] moduleMulOpposite isCentralScalar_of_commRing

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- The sections on `U` of the square-zero extension of `R` by `M`, over a site whose universe of
objects and universe of morphisms are independent of the universe of the sections. -/
noncomputable def sqZeroExtObjAnySite (U : Cᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of (TrivSqZeroExt (R.obj U) (M.obj U))

/-- The restriction map of the square-zero extension of `R` by `M`, acting on the ring component
and on the module component separately. -/
noncomputable def sqZeroExtMapAnySite {U V : Cᵒᵖ} (i : U ⟶ V) :
    sqZeroExtObjAnySite M U ⟶ sqZeroExtObjAnySite M V :=
  CommRingCat.ofHom
    ({ toFun := fun x => (((R.map i).hom x.fst, M.map i x.snd) : TrivSqZeroExt _ _)
       map_one' := TrivSqZeroExt.ext (map_one _) (map_zero _)
       map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero _)
       map_add' := fun x y => TrivSqZeroExt.ext (map_add _ _ _) (map_add _ _ _)
       map_mul' := fun x y => TrivSqZeroExt.ext (map_mul _ _ _) (by
         change M.map i (x.fst • y.snd + y.fst • x.snd) =
           (R.map i).hom x.fst • M.map i y.snd + (R.map i).hom y.fst • M.map i x.snd
         rw [map_add]
         exact congrArg₂ (· + ·) (M.map_smul i x.fst y.snd) (M.map_smul i y.fst x.snd)) } :
      TrivSqZeroExt (R.obj U) (M.obj U) →+* TrivSqZeroExt (R.obj V) (M.obj V))

variable {M}

/-- The section of the square-zero extension with the given ring and module components. -/
noncomputable def sqZeroExtMkAnySite {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    sqZeroExtObjAnySite M U := (r, m)

/-- The ring component of a section of the square-zero extension. -/
noncomputable def sqZeroExtFstAnySite {U : Cᵒᵖ} (x : sqZeroExtObjAnySite M U) : R.obj U := x.1

/-- The module component of a section of the square-zero extension. -/
noncomputable def sqZeroExtSndAnySite {U : Cᵒᵖ} (x : sqZeroExtObjAnySite M U) : M.obj U := x.2

/-- Two sections of the square-zero extension with the same components are equal. -/
theorem sqZeroExt_ext_anySite {U : Cᵒᵖ} {x y : sqZeroExtObjAnySite M U}
    (h1 : sqZeroExtFstAnySite x = sqZeroExtFstAnySite y)
    (h2 : sqZeroExtSndAnySite x = sqZeroExtSndAnySite y) : x = y :=
  TrivSqZeroExt.ext h1 h2

variable (M)

/-- The square-zero extension of `R` by `M`, as a presheaf of commutative rings on a site whose
universe of objects and universe of morphisms are independent of the universe of the sections. -/
noncomputable def sqZeroExtPresheafAnySite : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := sqZeroExtObjAnySite M U
  map i := sqZeroExtMapAnySite M i
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => sqZeroExt_ext_anySite ?_ ?_)
    · change (R.map (𝟙 U)).hom (sqZeroExtFstAnySite x) = sqZeroExtFstAnySite x
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (sqZeroExtFstAnySite x)) (R.map_id U)
    · change M.map (𝟙 U) (sqZeroExtSndAnySite x) = sqZeroExtSndAnySite x
      rw [← presheaf_map_apply_coe, M.presheaf.map_id]
      rfl
  map_comp {U V W} i j := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => sqZeroExt_ext_anySite ?_ ?_)
    · change (R.map (i ≫ j)).hom (sqZeroExtFstAnySite x) = _
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (sqZeroExtFstAnySite x)) (R.map_comp i j)
    · change M.map (i ≫ j) (sqZeroExtSndAnySite x) = _
      exact map_comp_apply M i j (sqZeroExtSndAnySite x)

/-- The inclusion of the presheaf of commutative rings into its square-zero extension,
`r ↦ (r, 0)`. -/
noncomputable def sqZeroExtInlAnySite : R ⟶ sqZeroExtPresheafAnySite M where
  app U := CommRingCat.ofHom
    ({ toFun := TrivSqZeroExt.inl
       map_one' := rfl
       map_mul' r r' := TrivSqZeroExt.ext rfl (by simp)
       map_zero' := rfl
       map_add' r r' := TrivSqZeroExt.ext rfl (by simp) } :
      R.obj U →+* TrivSqZeroExt (R.obj U) (M.obj U))
  naturality U V i :=
    CommRingCat.hom_ext (RingHom.ext fun r => TrivSqZeroExt.ext rfl (map_zero _).symm)

end PresheafOfModules

end
