module

public import Mathlib.CategoryTheory.Subfunctor.Subobject
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.WellPowered
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# Subobjects of a sheaf of modules are its submodules

Let `M` be a sheaf of modules. Mathlib has two notions of "subobject of `M`": the categorical
`CategoryTheory.Subobject M`, an isomorphism class of monomorphisms into `M`, and
`SheafOfModules.Submodule M`, a family of submodules of the modules of sections which is stable
under restriction and whose membership condition is local. This file identifies the two, and
specialises the identification to a sheaf of modules on a scheme and to the restriction of such
a sheaf to an open subscheme.

## Main definitions

* `SheafOfModules.Submodule.range`: the sectionwise range of a monomorphism of sheaves of
  modules, as a submodule of the target.
* `SheafOfModules.Submodule.ofSubobject` and `SheafOfModules.Submodule.toSubobject`: the two
  directions of the comparison, and `SheafOfModules.Submodule.orderIsoSubobject`, the order
  isomorphism they form.
* `AlgebraicGeometry.Scheme.Modules.rangeSubmodule`,
  `AlgebraicGeometry.Scheme.Modules.subobjectSubmodule` and
  `AlgebraicGeometry.Scheme.Modules.submoduleOrderIsoSubobject`: the same for `𝒪ₓ`-modules.
* `AlgebraicGeometry.Scheme.Modules.restrictSubobjectSubmodule`: the restricted form, turning a
  subobject of `F|_U` into a subsheaf of `F|_U` for `U` an open of `X`.

## Main results

* `SheafOfModules.Submodule.rangeIso` and `AlgebraicGeometry.Scheme.Modules.rangeSubmoduleIso`:
  a monomorphism presents its source as its image subsheaf, compatibly with the two inclusions
  into the ambient sheaf.
* `SheafOfModules.Submodule.range_ι`, `SheafOfModules.Submodule.toSubobject_ofSubobject` and
  `SheafOfModules.Submodule.ofSubobject_toSubobject`: the two round trips are the identity.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_rangeSubmodule`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_rangeSubmodule` and their converses: the
  correspondence preserves quasi-coherence and finite type, in both directions.
* `AlgebraicGeometry.Scheme.Modules.exists_submodule_of_mono` and
  `AlgebraicGeometry.Scheme.Modules.exists_submodule_isIso_restrict_of_mono`: a monomorphism
  into `F` is, up to isomorphism, the inclusion of a subsheaf of `F`, with finite type,
  quasi-coherence and being an isomorphism over an open carried along.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a non-reducible `def` wrapping `SheafOfModules`, and
instance search runs at reducible transparency only, so it does not cross it: `Mono`, and every
instance whose implicit sheaf of modules has to be unified with an `X.Modules`, has to be
re-stated for the `SheafOfModules` reading. `AlgebraicGeometry.Scheme.Modules.mono_sheafOfModules`
and `AlgebraicGeometry.Scheme.Modules.mono_of_mono_sheafOfModules` exchange the two readings of
`Mono`, `SheafOfModules.Submodule.mono_ι` restates Mathlib's instance as a lemma, and the whole
subobject correspondence is proved for `SheafOfModules` and then *applied* to `X.Modules`:
terms unify at default transparency even though instance search and `rw` do not.

For the same reason `AlgebraicGeometry.Scheme.Modules.isIso_map_of_inv_comp` is stated over
abstract variables; rewriting the composite `e.inv ≫ j` underneath
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` does not fire.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace PresheafOfModules.Submodule

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {P Q : PresheafOfModules.{u} R}

/-- Membership in the sectionwise range of a morphism of presheaves of modules, unfolded. -/
lemma mem_range_iff (f : P ⟶ Q) (U : Cᵒᵖ) (y : Q.obj U) :
    y ∈ (range f).obj U ↔ ∃ x, f.app U x = y :=
  Iff.rfl

end PresheafOfModules.Submodule

namespace SheafOfModules.Submodule

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M K K' : SheafOfModules.{u} R}

/-- The underlying morphism of type-valued presheaves of a morphism of presheaves of
modules. -/
noncomputable abbrev typeMap {P Q : PresheafOfModules.{u} R.obj} (f : P ⟶ Q) :
    P.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u} ⟶
      Q.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u} :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf R.obj).map f)
    (CategoryTheory.forget AddCommGrpCat.{u})

/-- The underlying morphism of type-valued presheaves of a monomorphism is a monomorphism. -/
lemma mono_typeMap {P Q : PresheafOfModules.{u} R.obj} (f : P ⟶ Q) [Mono f] :
    Mono (typeMap f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  exact PresheafOfModules.injective_of_mono f U

/-- The underlying type-valued presheaf of a sheaf of modules is a sheaf of types. -/
lemma isSheaf_typePresheaf (N : SheafOfModules.{u} R) :
    Presieve.IsSheaf J (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  (isSheaf_iff_isSheaf_of_type J _).mp
    (GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf)

/-- The sectionwise range of a monomorphism of sheaves of modules, as a submodule of the
target. -/
noncomputable def range (j : K ⟶ M) [Mono j] : M.Submodule where
  toSubmodule := PresheafOfModules.Submodule.range j.val
  isSheaf := by
    have hmono : Mono j.val := inferInstanceAs (Mono ((SheafOfModules.forget R).map j))
    have htype : Mono (typeMap j.val) := mono_typeMap j.val
    have hiso : IsIso (Subfunctor.toRange (typeMap j.val)) := by
      have := htype
      infer_instance
    refine ((PresheafOfModules.Submodule.range j.val).toSubfunctor.isSheaf_iff
      (isSheaf_typePresheaf M)).mp ?_
    exact Presieve.isSheaf_iso J (@asIso _ _ _ _ _ hiso) (isSheaf_typePresheaf K)

/-- The underlying presheaf submodule of `range j` is the sectionwise range of `j`. -/
@[simp]
lemma range_toSubmodule (j : K ⟶ M) [Mono j] :
    (range j).toSubmodule = PresheafOfModules.Submodule.range j.val :=
  rfl

/-- The sections of `range j` over `U` are the range of `j` on sections over `U`. -/
@[simp]
lemma range_obj (j : K ⟶ M) [Mono j] (U : Cᵒᵖ) :
    (range j).obj U = LinearMap.range (j.val.app U).hom :=
  rfl

/-- Membership in the sectionwise range of a monomorphism of sheaves of modules, unfolded. -/
lemma mem_range_iff (j : K ⟶ M) [Mono j] (U : Cᵒᵖ) (y : M.val.obj U) :
    y ∈ (range j).obj U ↔ ∃ x, j.val.app U x = y :=
  Iff.rfl

/-- The range of the inclusion of a submodule is that submodule. -/
@[simp]
lemma range_ι (N : M.Submodule) : range N.ι = N :=
  SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.range_ι N.toSubmodule)

/-- The corestriction of a monomorphism of sheaves of modules to its range. -/
noncomputable def toRange (j : K ⟶ M) [Mono j] : K ⟶ (range j).toSheafOfModules :=
  ⟨{ app U := ModuleCat.ofHom
        { toFun x := ⟨j.val.app U x, ⟨x, rfl⟩⟩
          map_add' x y := Subtype.ext (map_add _ _ _)
          map_smul' r x := Subtype.ext (map_smul _ _ _) }
     naturality := by
       intro U V g
       apply ModuleCat.Hom.ext
       ext x
       exact Subtype.ext (PresheafOfModules.naturality_apply j.val g x) }⟩

/-- The corestriction of `j` to its range, followed by the inclusion of the range, is `j`. -/
@[reassoc (attr := simp)]
lemma toRange_ι (j : K ⟶ M) [Mono j] : toRange j ≫ (range j).ι = j := rfl

/-- The corestriction of a monomorphism to its range is an isomorphism. -/
instance isIso_toRange (j : K ⟶ M) [Mono j] : IsIso (toRange j) := by
  have hmono : Mono j.val := inferInstanceAs (Mono ((SheafOfModules.forget R).map j))
  have happ : ∀ U, IsIso (((SheafOfModules.forget R ⋙
      PresheafOfModules.toPresheaf R.obj).map (toRange j)).app U) := by
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · exact PresheafOfModules.injective_of_mono j.val U (Subtype.ext_iff.mp hxy)
    · obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩
  have : IsIso ((SheafOfModules.forget R ⋙
      PresheafOfModules.toPresheaf R.obj).map (toRange j)) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)

/-- A monomorphism of sheaves of modules presents its source as its range subsheaf. -/
noncomputable def rangeIso (j : K ⟶ M) [Mono j] : K ≅ (range j).toSheafOfModules :=
  asIso (toRange j)

/-- The forward map of `rangeIso j` is the corestriction of `j` to its range. -/
@[simp]
lemma rangeIso_hom (j : K ⟶ M) [Mono j] : (rangeIso j).hom = toRange j := rfl

/-- The isomorphism `rangeIso j` is compatible with the inclusions into `M`. -/
lemma rangeIso_hom_ι (j : K ⟶ M) [Mono j] : (rangeIso j).hom ≫ (range j).ι = j :=
  toRange_ι j

/-- The inverse of `rangeIso j`, followed by `j`, is the inclusion of the range. -/
@[reassoc]
lemma rangeIso_inv_comp (j : K ⟶ M) [Mono j] : (rangeIso j).inv ≫ j = (range j).ι :=
  (Iso.inv_comp_eq _).mpr (rangeIso_hom_ι j).symm

/-- The inclusion of a submodule into the ambient sheaf of modules is a monomorphism. -/
lemma mono_ι (N : M.Submodule) : Mono N.ι := inferInstance

/-- Two comparable monomorphisms into `M` have comparable ranges. -/
lemma range_le_range_of_comm {j : K ⟶ M} {j' : K' ⟶ M} [Mono j] [Mono j'] (f : K ⟶ K')
    (h : f ≫ j' = j) : range j ≤ range j' := by
  intro U y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨f.val.app U x, congrArg (fun k : K ⟶ M => (k.val.app U).hom x) h⟩

/-- Two monomorphisms into `M` which differ by an isomorphism of their sources have the same
range. -/
lemma range_eq_range_of_comm {j : K ⟶ M} {j' : K' ⟶ M} [Mono j] [Mono j'] (e : K ≅ K')
    (h : e.hom ≫ j' = j) : range j = range j' :=
  le_antisymm (range_le_range_of_comm e.hom h)
    (range_le_range_of_comm e.inv (by rw [← h, Iso.inv_hom_id_assoc]))

/-! ### The correspondence with categorical subobjects -/

/-- A subobject of a sheaf of modules, as a submodule: the sectionwise range of its arrow. -/
noncomputable def ofSubobject (S : Subobject M) : M.Submodule := range S.arrow

/-- The sections of `ofSubobject S` over `U` are the range of the arrow of `S` on sections. -/
@[simp]
lemma ofSubobject_obj (S : Subobject M) (U : Cᵒᵖ) :
    (ofSubobject S).obj U = LinearMap.range (S.arrow.val.app U).hom :=
  rfl

/-- A submodule of a sheaf of modules, as a subobject: the subobject presented by its
inclusion. -/
noncomputable def toSubobject (N : M.Submodule) : Subobject M := Subobject.mk N.ι

/-- A subobject is isomorphic to the submodule it corresponds to. -/
noncomputable def ofSubobjectIso (S : Subobject M) :
    (S : SheafOfModules.{u} R) ≅ (ofSubobject S).toSheafOfModules :=
  rangeIso S.arrow

/-- The isomorphism `ofSubobjectIso S` is compatible with the inclusions into `M`. -/
lemma ofSubobjectIso_hom_ι (S : Subobject M) :
    (ofSubobjectIso S).hom ≫ (ofSubobject S).ι = S.arrow :=
  rangeIso_hom_ι S.arrow

/-- The inverse of `ofSubobjectIso S`, followed by the arrow of `S`, is the inclusion of
`ofSubobject S`. -/
lemma ofSubobjectIso_inv_arrow (S : Subobject M) :
    (ofSubobjectIso S).inv ≫ S.arrow = (ofSubobject S).ι :=
  rangeIso_inv_comp S.arrow

/-- The subobject of the submodule of a subobject `S` is `S`. -/
@[simp]
lemma toSubobject_ofSubobject (S : Subobject M) : toSubobject (ofSubobject S) = S :=
  Eq.trans
    (Subobject.mk_eq_mk_of_comm _ _ (ofSubobjectIso S).symm (ofSubobjectIso_inv_arrow S))
    (Subobject.mk_arrow S)

/-- The submodule of the subobject of a submodule `N` is `N`. -/
@[simp]
lemma ofSubobject_toSubobject (N : M.Submodule) : ofSubobject (toSubobject N) = N :=
  (range_eq_range_of_comm (Subobject.underlyingIso N.ι)
    (Subobject.underlyingIso_hom_comp_eq_mk N.ι)).trans (range_ι N)

/-- Passing from subobjects to submodules is monotone. -/
lemma ofSubobject_monotone : Monotone (ofSubobject (M := M)) := fun _ _ h =>
  range_le_range_of_comm (Subobject.ofLE _ _ h) (Subobject.ofLE_arrow h)

/-- Passing from submodules to subobjects is monotone. -/
lemma toSubobject_monotone : Monotone (toSubobject (M := M)) := fun _ _ h =>
  Subobject.mk_le_mk_of_comm (homOfLE h) (homOfLE_ι h)

/-- The order isomorphism between the submodules and the subobjects of a sheaf of modules,
sending a submodule to the subobject presented by its inclusion and a subobject to the
sectionwise range of its arrow. -/
noncomputable def orderIsoSubobject (M : SheafOfModules.{u} R) : M.Submodule ≃o Subobject M where
  toFun := toSubobject
  invFun := ofSubobject
  left_inv := ofSubobject_toSubobject
  right_inv := toSubobject_ofSubobject
  map_rel_iff' {N N'} := by
    refine ⟨fun h => ?_, fun h => toSubobject_monotone h⟩
    simpa using ofSubobject_monotone h

/-- `orderIsoSubobject M` sends a submodule to its subobject. -/
@[simp]
lemma orderIsoSubobject_apply (N : M.Submodule) : orderIsoSubobject M N = toSubobject N := rfl

/-- The inverse of `orderIsoSubobject M` sends a subobject to its submodule. -/
@[simp]
lemma orderIsoSubobject_symm_apply (S : Subobject M) :
    (orderIsoSubobject M).symm S = ofSubobject S := rfl

end SheafOfModules.Submodule

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F K K' : X.Modules}

/-- A monomorphism of `𝒪ₓ`-modules is a monomorphism in the category of sheaves of modules
over the structure sheaf. -/
lemma mono_sheafOfModules (j : K ⟶ F) [Mono j] :
    @Mono (SheafOfModules.{u} X.ringCatSheaf) inferInstance K F j :=
  ⟨fun g h hcomp => (‹Mono j›).right_cancellation g h hcomp⟩

/-- A monomorphism of sheaves of modules over the structure sheaf of `X` is a monomorphism of
`𝒪ₓ`-modules. -/
lemma mono_of_mono_sheafOfModules (j : K ⟶ F)
    (h : @Mono (SheafOfModules.{u} X.ringCatSheaf) inferInstance K F j) :
    @Mono X.Modules inferInstance K F j :=
  ⟨fun g k hcomp => h.right_cancellation g k hcomp⟩

/-- The inclusion of a subsheaf of `F` is a monomorphism of `𝒪ₓ`-modules. -/
instance mono_submodule_ι (N : F.Submodule) :
    @Mono X.Modules inferInstance N.toSheafOfModules F N.ι :=
  mono_of_mono_sheafOfModules N.ι (SheafOfModules.Submodule.mono_ι N)

/-- The inclusion of a subsheaf of `F` is a monomorphism in the category of sheaves of modules
over the structure sheaf. -/
instance mono_submodule_ι' (N : F.Submodule) :
    @Mono (SheafOfModules.{u} X.ringCatSheaf) inferInstance N.toSheafOfModules F N.ι :=
  SheafOfModules.Submodule.mono_ι N

/-- The image subsheaf of a monomorphism of `𝒪ₓ`-modules: its sectionwise range. -/
noncomputable def rangeSubmodule (j : K ⟶ F) [Mono j] : F.Submodule :=
  @SheafOfModules.Submodule.range _ _ _ _ F K j (mono_sheafOfModules j)

/-- The sections of `rangeSubmodule j` over `U` are the range of `j` on sections over `U`. -/
@[simp]
lemma rangeSubmodule_obj (j : K ⟶ F) [Mono j] (U : (Opens X)ᵒᵖ) :
    (rangeSubmodule j).obj U = LinearMap.range (j.val.app U).hom :=
  rfl

/-- Membership in the image subsheaf of a monomorphism of `𝒪ₓ`-modules, unfolded. -/
lemma mem_rangeSubmodule_iff (j : K ⟶ F) [Mono j] (U : (Opens X)ᵒᵖ) (y : F.val.obj U) :
    y ∈ (rangeSubmodule j).obj U ↔ ∃ x, j.val.app U x = y :=
  Iff.rfl

/-- The image subsheaf of the inclusion of a subsheaf is that subsheaf. -/
@[simp]
lemma rangeSubmodule_ι (N : F.Submodule) : rangeSubmodule N.ι = N :=
  @SheafOfModules.Submodule.range_ι _ _ _ _ F N

/-- A monomorphism of `𝒪ₓ`-modules presents its source as its image subsheaf. -/
noncomputable def rangeSubmoduleIso (j : K ⟶ F) [Mono j] :
    K ≅ (rangeSubmodule j).toSheafOfModules :=
  @SheafOfModules.Submodule.rangeIso _ _ _ _ F K j (mono_sheafOfModules j)

/-- The isomorphism `rangeSubmoduleIso j` is compatible with the inclusions into `F`. -/
@[reassoc]
lemma rangeSubmoduleIso_hom_ι (j : K ⟶ F) [Mono j] :
    (rangeSubmoduleIso j).hom ≫ (rangeSubmodule j).ι = j :=
  @SheafOfModules.Submodule.rangeIso_hom_ι _ _ _ _ F K j (mono_sheafOfModules j)

/-- The inverse of `rangeSubmoduleIso j`, followed by `j`, is the inclusion of the image
subsheaf. -/
@[reassoc]
lemma rangeSubmoduleIso_inv_comp (j : K ⟶ F) [Mono j] :
    (rangeSubmoduleIso j).inv ≫ j = (rangeSubmodule j).ι :=
  @SheafOfModules.Submodule.rangeIso_inv_comp _ _ _ _ F K j (mono_sheafOfModules j)

/-- Two comparable monomorphisms into `F` have comparable image subsheaves. -/
lemma rangeSubmodule_le_rangeSubmodule_of_comm {j : K ⟶ F} {j' : K' ⟶ F} [Mono j] [Mono j']
    (f : K ⟶ K') (h : f ≫ j' = j) : rangeSubmodule j ≤ rangeSubmodule j' :=
  @SheafOfModules.Submodule.range_le_range_of_comm _ _ _ _ F K K' j j'
    (mono_sheafOfModules j) (mono_sheafOfModules j') f h

/-- Two monomorphisms into `F` which differ by an isomorphism of their sources have the same
image subsheaf. -/
lemma rangeSubmodule_eq_rangeSubmodule_of_comm {j : K ⟶ F} {j' : K' ⟶ F} [Mono j] [Mono j']
    (e : K ≅ K') (h : e.hom ≫ j' = j) : rangeSubmodule j = rangeSubmodule j' :=
  @SheafOfModules.Submodule.range_eq_range_of_comm _ _ _ _ F K K' j j'
    (mono_sheafOfModules j) (mono_sheafOfModules j') e h

/-- Being quasi-coherent transfers from the source of a monomorphism to its image subsheaf. -/
lemma isQuasicoherent_rangeSubmodule (j : K ⟶ F) [Mono j] [K.IsQuasicoherent] :
    (rangeSubmodule j).toSheafOfModules.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (rangeSubmoduleIso j) inferInstance

/-- Being quasi-coherent transfers from the image subsheaf of a monomorphism to its source. -/
lemma isQuasicoherent_of_isQuasicoherent_rangeSubmodule (j : K ⟶ F) [Mono j]
    [(rangeSubmodule j).toSheafOfModules.IsQuasicoherent] : K.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (rangeSubmoduleIso j).symm inferInstance

/-- Being of finite type transfers from the source of a monomorphism to its image subsheaf. -/
lemma isFiniteType_rangeSubmodule (j : K ⟶ F) [Mono j] [K.IsFiniteType] :
    (rangeSubmodule j).toSheafOfModules.IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} (rangeSubmoduleIso j)

/-- Being of finite type transfers from the image subsheaf of a monomorphism to its source. -/
lemma isFiniteType_of_isFiniteType_rangeSubmodule (j : K ⟶ F) [Mono j]
    [(rangeSubmodule j).toSheafOfModules.IsFiniteType] : K.IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} (rangeSubmoduleIso j).symm

/-- If `e.inv ≫ g = h` and the image of `g` under a functor is an isomorphism, so is the image
of `h`. -/
lemma isIso_map_of_inv_comp {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B E : C} (e : A ≅ B) {g : A ⟶ E} {h : B ⟶ E} (hc : e.inv ≫ g = h)
    (hg : IsIso (G.map g)) : IsIso (G.map h) := by
  subst hc
  rw [G.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hg

/-- If a monomorphism becomes an isomorphism after restriction to an open, so does the
inclusion of its image subsheaf. -/
lemma isIso_restrictFunctor_map_rangeSubmodule_ι (j : K ⟶ F) [Mono j] (W : X.Opens)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor W.ι).map j)) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (rangeSubmodule j).ι) :=
  isIso_map_of_inv_comp (Scheme.Modules.restrictFunctor W.ι) (rangeSubmoduleIso j)
    (rangeSubmoduleIso_inv_comp j) hiso

/-! ### The correspondence with categorical subobjects -/

/-- A subobject of a sheaf of modules on a scheme, as a subsheaf: the sectionwise range of its
arrow. -/
noncomputable def subobjectSubmodule (S : Subobject F) : F.Submodule :=
  @SheafOfModules.Submodule.ofSubobject _ _ _ _ F S

/-- The sections of `subobjectSubmodule S` over `U` are the range of the arrow of `S` on
sections. -/
@[simp]
lemma subobjectSubmodule_obj (S : Subobject F) (U : (Opens X)ᵒᵖ) :
    (subobjectSubmodule S).obj U = LinearMap.range (S.arrow.val.app U).hom :=
  rfl

/-- A subsheaf of a sheaf of modules on a scheme, as a subobject: the subobject presented by
its inclusion. -/
noncomputable def submoduleSubobject (N : F.Submodule) : Subobject F :=
  @SheafOfModules.Submodule.toSubobject _ _ _ _ F N

/-- A subobject is isomorphic to the subsheaf it corresponds to. -/
noncomputable def subobjectSubmoduleIso (S : Subobject F) :
    (S : X.Modules) ≅ (subobjectSubmodule S).toSheafOfModules :=
  @SheafOfModules.Submodule.ofSubobjectIso _ _ _ _ F S

/-- The isomorphism `subobjectSubmoduleIso S` is compatible with the inclusions into `F`. -/
lemma subobjectSubmoduleIso_hom_ι (S : Subobject F) :
    (subobjectSubmoduleIso S).hom ≫ (subobjectSubmodule S).ι = S.arrow :=
  @SheafOfModules.Submodule.ofSubobjectIso_hom_ι _ _ _ _ F S

/-- The inverse of `subobjectSubmoduleIso S`, followed by the arrow of `S`, is the inclusion
of `subobjectSubmodule S`. -/
lemma subobjectSubmoduleIso_inv_arrow (S : Subobject F) :
    (subobjectSubmoduleIso S).inv ≫ S.arrow = (subobjectSubmodule S).ι :=
  @SheafOfModules.Submodule.ofSubobjectIso_inv_arrow _ _ _ _ F S

/-- The subobject of the subsheaf of a subobject `S` is `S`. -/
@[simp]
lemma submoduleSubobject_subobjectSubmodule (S : Subobject F) :
    submoduleSubobject (subobjectSubmodule S) = S :=
  @SheafOfModules.Submodule.toSubobject_ofSubobject _ _ _ _ F S

/-- The subsheaf of the subobject of a subsheaf `N` is `N`. -/
@[simp]
lemma subobjectSubmodule_submoduleSubobject (N : F.Submodule) :
    subobjectSubmodule (submoduleSubobject N) = N :=
  @SheafOfModules.Submodule.ofSubobject_toSubobject _ _ _ _ F N

/-- The order isomorphism between the subsheaves and the subobjects of a sheaf of modules on a
scheme. -/
noncomputable def submoduleOrderIsoSubobject (F : X.Modules) : F.Submodule ≃o Subobject F :=
  @SheafOfModules.Submodule.orderIsoSubobject _ _ _ _ F

/-! ### Transport of the finiteness properties -/

/-- Being quasi-coherent transfers from a subobject to the subsheaf it corresponds to. -/
lemma isQuasicoherent_subobjectSubmodule (S : Subobject F) [(S : X.Modules).IsQuasicoherent] :
    (subobjectSubmodule S).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_rangeSubmodule S.arrow

/-- Being quasi-coherent transfers from a subsheaf to the subobject it corresponds to. -/
lemma isQuasicoherent_of_isQuasicoherent_subobjectSubmodule (S : Subobject F)
    [(subobjectSubmodule S).toSheafOfModules.IsQuasicoherent] :
    (S : X.Modules).IsQuasicoherent :=
  @isQuasicoherent_of_isQuasicoherent_rangeSubmodule _ _ _ S.arrow _ ‹_›

/-- Being of finite type transfers from a subobject to the subsheaf it corresponds to. -/
lemma isFiniteType_subobjectSubmodule (S : Subobject F) [(S : X.Modules).IsFiniteType] :
    (subobjectSubmodule S).toSheafOfModules.IsFiniteType :=
  isFiniteType_rangeSubmodule S.arrow

/-- Being of finite type transfers from a subsheaf to the subobject it corresponds to. -/
lemma isFiniteType_of_isFiniteType_subobjectSubmodule (S : Subobject F)
    [(subobjectSubmodule S).toSheafOfModules.IsFiniteType] :
    (S : X.Modules).IsFiniteType :=
  @isFiniteType_of_isFiniteType_rangeSubmodule _ _ _ S.arrow _ ‹_›

/-! ### The restricted form -/

/-- A subobject of the restriction of `F` to an open `U`, as a subsheaf of that
restriction. -/
noncomputable def restrictSubobjectSubmodule (F : X.Modules) (U : X.Opens)
    (G : Subobject (F.restrict U.ι)) : (F.restrict U.ι).Submodule :=
  subobjectSubmodule G

/-- The sections of `restrictSubobjectSubmodule F U G` over `W` are the range of the arrow of
`G` on sections over `W`. -/
@[simp]
lemma restrictSubobjectSubmodule_obj (F : X.Modules) (U : X.Opens)
    (G : Subobject (F.restrict U.ι)) (W : (Opens U.toScheme)ᵒᵖ) :
    (restrictSubobjectSubmodule F U G).obj W = LinearMap.range (G.arrow.val.app W).hom :=
  rfl

/-- The subobject `G` of `F|_U` is isomorphic to the subsheaf of `F|_U` it corresponds to. -/
noncomputable def restrictSubobjectSubmoduleIso (F : X.Modules) (U : X.Opens)
    (G : Subobject (F.restrict U.ι)) :
    (G : U.toScheme.Modules) ≅ (restrictSubobjectSubmodule F U G).toSheafOfModules :=
  subobjectSubmoduleIso G

/-- The isomorphism `restrictSubobjectSubmoduleIso F U G` is compatible with the inclusions
into `F|_U`. -/
lemma restrictSubobjectSubmoduleIso_hom_ι (F : X.Modules) (U : X.Opens)
    (G : Subobject (F.restrict U.ι)) :
    (restrictSubobjectSubmoduleIso F U G).hom ≫ (restrictSubobjectSubmodule F U G).ι =
      G.arrow :=
  subobjectSubmoduleIso_hom_ι G

/-- The subobject of the subsheaf of a subobject `G` of `F|_U` is `G`. -/
@[simp]
lemma submoduleSubobject_restrictSubobjectSubmodule (F : X.Modules) (U : X.Opens)
    (G : Subobject (F.restrict U.ι)) :
    submoduleSubobject (restrictSubobjectSubmodule F U G) = G :=
  submoduleSubobject_subobjectSubmodule G

/-- The order isomorphism between the subsheaves and the subobjects of `F|_U`. -/
noncomputable def restrictSubmoduleOrderIsoSubobject (F : X.Modules) (U : X.Opens) :
    (F.restrict U.ι).Submodule ≃o Subobject (F.restrict U.ι) :=
  submoduleOrderIsoSubobject _

/-! ### Monomorphisms as inclusions of subsheaves -/

/-- A monomorphism into `F` is, up to isomorphism, the inclusion of a subsheaf of `F`. -/
theorem exists_submodule_of_mono (j : K ⟶ F) [Mono j] :
    ∃ (N : F.Submodule) (e : K ≅ N.toSheafOfModules), e.hom ≫ N.ι = j :=
  ⟨rangeSubmodule j, rangeSubmoduleIso j, rangeSubmoduleIso_hom_ι j⟩

/-- A monomorphism into `F` whose source is of finite type and quasi-coherent, and which is
an isomorphism over an open `W`, is, up to isomorphism, the inclusion of a subsheaf of `F` with
the same three properties. -/
theorem exists_submodule_isIso_restrict_of_mono
    (j : K ⟶ F) [Mono j] [K.IsFiniteType] [K.IsQuasicoherent] (W : X.Opens)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor W.ι).map j)) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsFiniteType ∧
      N.toSheafOfModules.IsQuasicoherent ∧
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map N.ι) ∧
      ∃ e : K ≅ N.toSheafOfModules, e.hom ≫ N.ι = j :=
  ⟨rangeSubmodule j, isFiniteType_rangeSubmodule j, isQuasicoherent_rangeSubmodule j,
    isIso_restrictFunctor_map_rangeSubmodule_ι j W hiso,
    rangeSubmoduleIso j, rangeSubmoduleIso_hom_ι j⟩

end AlgebraicGeometry.Scheme.Modules
