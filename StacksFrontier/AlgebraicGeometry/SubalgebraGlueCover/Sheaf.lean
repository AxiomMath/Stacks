module

public import StacksFrontier.AlgebraicGeometry.SubalgebraGlueCover.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebra.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# A concrete subalgebra is an algebra sheaf, and a subobject of the ambient one

A concrete subalgebra `C : Subalg A` of an algebra sheaf `A` on a scheme `X` is a subring of
`A(U)` for every open `U`, containing the image of `Γ(X, U)`, stable under restriction, and
local. This file realizes it as an object of `Stacks.RelativeSpec.AlgebraSheaf X` together with
a monomorphism into `A`, so that the predicates
`Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent` and
`Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType` can be asserted of it.

## Main definitions

* `Subalg.presheaf`, `Subalg.toSheafOfRings`: the sheaf of commutative rings of sections of
  `C`.
* `Subalg.toAlgebraSheaf`: that sheaf with the corestriction of the structure morphism of `A`,
  as an object of `Stacks.RelativeSpec.AlgebraSheaf X`.
* `Subalg.incl`: the inclusion `C.toAlgebraSheaf ⟶ A`.
* `Subalg.toSubobject`: `C` as a subobject of `A` in the sense of `CategoryTheory.Subobject`.

## Main results

* `Subalg.presheaf_isSheaf`: the sections of `C` form a sheaf.
* `Subalg.mono_incl`: the inclusion is a monomorphism.
* `Subalg.finiteType_app_of_obj_eq`: if two concrete subalgebras have the same subring of
  sections over an open, then the structure map of one over that open is of finite type as soon
  as that of the other is.
* `finiteType_app_glue_of_le`: over an open inside `W j`, the structure map of the glue is of
  finite type as soon as that of `C j` is.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}} {A : AlgebraSheaf X}

/-- The unique-gluing form of the sheaf condition for the underlying sheaf of rings of an
algebra sheaf. -/
theorem isSheafUniqueGluing_right (A : AlgebraSheaf X) :
    TopCat.Presheaf.IsSheafUniqueGluing A.right.obj := by
  rw [← TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  exact A.right.property

namespace Subalg

variable (C : Subalg A)

/-! ### The sheaf of commutative rings of sections -/

/-- The presheaf of commutative rings of sections of a concrete subalgebra. -/
def presheaf : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (C.obj U.unop)
  map {_ _} i := CommRingCat.ofHom
    { toFun x := ⟨(A.right.obj.map i).hom x.1, C.map_mem i.unop.le x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' _ _ := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' _ _ := Subtype.ext (map_add _ _ _) }
  map_id U := by
    ext x
    exact congr($(A.right.obj.map_id U).hom x.1)
  map_comp f g := by
    ext x
    exact congr($(A.right.obj.map_comp f g).hom x.1)

/-- The sections of `presheaf C` over `U` are the subring `C.obj U.unop`. -/
@[simp] theorem presheaf_obj (U : X.Opensᵒᵖ) :
    (presheaf C).obj U = CommRingCat.of (C.obj U.unop) := rfl

/-- The restriction maps of `presheaf C` are those of `A` on the underlying sections. -/
@[simp] theorem presheaf_map_coe {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (x : (presheaf C).obj U) :
    (((presheaf C).map i).hom x).1 = (A.right.obj.map i).hom x.1 := rfl

/-- The sections of a concrete subalgebra form a sheaf. -/
theorem presheaf_isSheaf : (presheaf C).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  obtain ⟨s, hs, huniq⟩ := isSheafUniqueGluing_right A U (fun i ↦ (sf i).1)
    fun i j ↦ congr_arg Subtype.val (hcompat i j)
  have hmem : s ∈ C.obj (iSup U) := by
    refine C.isSheaf s fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨U i, le_iSup U i, hi, ?_⟩
    change (A.right.obj.map (Opens.leSupr U i).op) s ∈ C.obj (U i)
    rw [hs i]
    exact (sf i).2
  exact ⟨⟨s, hmem⟩, fun i ↦ Subtype.ext (hs i),
    fun t ht ↦ Subtype.ext (huniq t.1 fun i ↦ congr_arg Subtype.val (ht i))⟩

/-- The sheaf of commutative rings of sections of a concrete subalgebra. -/
def toSheafOfRings : TopCat.Sheaf CommRingCat.{u} X := ⟨presheaf C, presheaf_isSheaf C⟩

/-! ### The structure morphism and the inclusion -/

/-- The structure morphism of a concrete subalgebra, as a natural transformation of presheaves
of commutative rings: the corestriction of the structure morphism of `A`, which lands in `C` by
the `algebraMap_mem` field. -/
def structNatTrans : X.sheaf.obj ⟶ presheaf C where
  app U := CommRingCat.ofHom
    { toFun a := ⟨(A.hom.hom.app U).hom a, C.algebraMap_mem U.unop a⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' _ _ := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' _ _ := Subtype.ext (map_add _ _ _) }
  naturality _ _ i := by
    ext a
    exact Subtype.ext congr($(A.hom.hom.naturality i).hom a)

/-- The inclusion of a concrete subalgebra into the ambient sheaf of rings. -/
def inclNatTrans : presheaf C ⟶ A.right.obj where
  app U := CommRingCat.ofHom (SubringClass.subtype (C.obj U.unop))
  naturality _ _ _ := by ext x; rfl

/-- The algebra sheaf of a concrete subalgebra. -/
def toAlgebraSheaf : AlgebraSheaf X :=
  Under.mk (ObjectProperty.homMk (structNatTrans C) : X.sheaf ⟶ toSheafOfRings C)

/-- The sections of `toAlgebraSheaf C` over `U` are the subring `C.obj U`. -/
@[simp] theorem sections_toAlgebraSheaf (U : X.Opens) :
    sections (toAlgebraSheaf C) U = CommRingCat.of (C.obj U) := rfl

/-- The structure morphism of `toAlgebraSheaf C` is that of `A` on the underlying sections. -/
@[simp] theorem app_toAlgebraSheaf_coe (U : X.Opens) (a : Γ(X, U)) :
    (((toAlgebraSheaf C).hom.hom.app (op U)).hom a).1 = (A.hom.hom.app (op U)).hom a := rfl

/-- The inclusion of a concrete subalgebra into the ambient algebra sheaf. -/
def incl : toAlgebraSheaf C ⟶ A :=
  Under.homMk (ObjectProperty.homMk (inclNatTrans C)) (by
    apply Sheaf.hom_ext
    ext U a
    rfl)

/-- The inclusion of a concrete subalgebra into the ambient algebra sheaf is a monomorphism. -/
instance mono_incl : Mono (incl C) := by
  have happ : ∀ U, Mono ((inclNatTrans C).app U) := fun _ ↦
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have h₁ : Mono (inclNatTrans C) := NatTrans.mono_of_mono_app _
  have h₂ : Mono (ObjectProperty.homMk (inclNatTrans C) :
      toSheafOfRings C ⟶ A.right) :=
    (sheafToPresheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}).mono_of_mono_map h₁
  exact (Under.forget X.sheaf).mono_of_mono_map h₂

/-- A concrete subalgebra as a subobject of the ambient algebra sheaf. -/
def toSubobject : Subobject A := Subobject.mk (incl C)

/-! ### Transport of finite type along an equality of subrings of sections -/

/-- If two concrete subalgebras have the same sections over an open `U` and the structure map of
one over `U` is of finite type, so is that of the other. -/
theorem finiteType_app_of_obj_eq {C D : Subalg A} {U : X.Opens} (h : C.obj U = D.obj U)
    (hft : RingHom.FiniteType ((toAlgebraSheaf D).hom.hom.app (op U)).hom) :
    RingHom.FiniteType ((toAlgebraSheaf C).hom.hom.app (op U)).hom := by
  exact hft.comp_surjective (g := (RingEquiv.subringCongr h).symm.toRingHom)
    (RingEquiv.subringCongr h).symm.surjective

end Subalg

/-! ### The glueing identity at the level of finite type -/

section Glue

variable {ι : Type*} (W : ι → X.Opens) (C : ι → Subalg A)

/-- Over an open contained in `W j`, the structure map of the glued subalgebra is of finite type as
soon as that of `C j` is. -/
theorem finiteType_app_glue_of_le (hagree : Agree W C) {j : ι} {U : X.Opens} (hUW : U ≤ W j)
    (hft : RingHom.FiniteType ((Subalg.toAlgebraSheaf (C j)).hom.hom.app (op U)).hom) :
    RingHom.FiniteType ((Subalg.toAlgebraSheaf (glue W C)).hom.hom.app (op U)).hom :=
  Subalg.finiteType_app_of_obj_eq (glue_obj_of_le W C hagree hUW) hft

end Glue

end Stacks.RelativeSpec.AlgebraSheaf

end
