module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Regular sections of a sheaf of modules

A global section `s` of a sheaf of modules `L` over a sheaf of rings `O` is *regular* when
multiplication by `s`, viewed as a morphism `O ⟶ L`, is a monomorphism. For the structure
sheaf of a locally ringed space this is a pointwise condition: a section is regular exactly
when its germ at every point is a nonzerodivisor. On a scheme it can equivalently be tested
on all affine opens, or on the members of a single affine open covering.

## Main definitions

* `AlgebraicGeometry.IsRegularSection`: the morphism from the structure sheaf associated to a
  global section of a sheaf of modules is a monomorphism.
* `AlgebraicGeometry.globalFunctionSections`: a global function on a scheme, read as a global
  section of the structure sheaf regarded as a sheaf of modules over itself.
* `AlgebraicGeometry.structureSectionValue` and `AlgebraicGeometry.unitGroupSectionEquiv` name
  the two retypings of a ring of sections of a ringed site which the sectionwise criterion on
  an arbitrary site needs.

## Main results

* `AlgebraicGeometry.isRegularSection_iff_forall_isSMulRegular_obj`: on an arbitrary site,
  regularity of a section of the structure sheaf is sectionwise regularity over every object.
* `AlgebraicGeometry.isRegularSection_iff_forall_isSMulRegular`: on a sheafed space,
  regularity of a section of the structure sheaf is sectionwise regularity on every open.
* `AlgebraicGeometry.isRegularSection_iff_stalk`: regularity is detected on all stalks.
* `AlgebraicGeometry.isRegularSection_iff_affineOpen`: on a scheme, regularity can be checked
  on every affine open.
* `AlgebraicGeometry.isRegularSection_iff_exists_affineOpenCover`: on a scheme, it is enough
  to check regularity on one affine open covering.
* `RingEquiv.isSMulRegular_congr` and `Module.FaithfullyFlat.isSMulRegular_algebraMap_iff`:
  being a nonzerodivisor transports along a ring isomorphism, and along a faithfully flat
  algebra map in both directions.
* `AlgebraicGeometry.isSMulRegular_of_forall_isSMulRegular_germ`: a global function on a
  scheme is a nonzerodivisor as soon as all its germs are.

## Implementation notes

The equivalence `SheafOfModules.unitHomEquiv` identifies a global section `s` with the
module-sheaf morphism `f ↦ f • s` from the structure sheaf, so categorical monicity expresses
exactly injectivity in the source. The predicate is defined for every module sheaf; the
source's assumption that the sheaf is invertible is imposed by applications of the definition.

The structure sheaf is regarded as a sheaf of modules via `SheafOfModules.unit`. A global
section in that sense is a compatible family of sections, whose component on an open `U` is
`f.val (.op U)`; so the stalkwise criterion applies the germ map to the component on the whole
space, while the affine criteria use the components on affine opens.

## References

* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 01WZ](https://stacks.math.columbia.edu/tag/01WZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v u w

/-! ### Nonzerodivisors and ring maps -/

/-- Being a nonzerodivisor transports along a ring isomorphism. -/
theorem RingEquiv.isSMulRegular_congr {A C : Type*} [CommRing A] [CommRing C] (e : A ≃+* C)
    (a : A) : IsSMulRegular A a ↔ IsSMulRegular C (e a) :=
  Equiv.isSMulRegular_congr (e := e.toEquiv) (r := a) (s := e a) fun x ↦ e.map_mul a x

/-- A ring element is a nonzerodivisor as soon as its image under an injective algebra map
is one. -/
theorem isSMulRegular_of_isSMulRegular_algebraMap {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] (hinj : Function.Injective (algebraMap A C)) {a : A}
    (h : IsSMulRegular C (algebraMap A C a)) : IsSMulRegular A a := by
  intro x y hxy
  refine hinj (h ?_)
  simpa only [smul_eq_mul, ← map_mul] using congrArg (algebraMap A C) hxy

/-- Over a faithfully flat algebra a ring element is a nonzerodivisor exactly when its image
is one: flatness gives one direction, and injectivity of the algebra map the other. -/
@[sga "1 IV 1.3" "(i), special case"]
theorem Module.FaithfullyFlat.isSMulRegular_algebraMap_iff {A C : Type*} [CommRing A]
    [CommRing C] [Algebra A C] [Module.FaithfullyFlat A C] (a : A) :
    IsSMulRegular A a ↔ IsSMulRegular C (algebraMap A C a) :=
  ⟨IsSMulRegular.of_flat,
    isSMulRegular_of_isSMulRegular_algebraMap (FaithfulSMul.algebraMap_injective A C)⟩

namespace AlgebraicGeometry

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- A global section is regular when multiplication by it gives a monomorphism
from the structure sheaf to its module sheaf. -/
@[stacks 01WY]
noncomputable abbrev IsRegularSection
    {L : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (s : L.sections) : Prop :=
  Mono (L.unitHomEquiv.symm s)

section SheafedSpace

/-- The component over an object of the site of a global section of the structure sheaf of a
ringed site, as an element of the ring of sections there.  The two types have the same
carrier and differ only in how they are indexed. -/
def structureSectionValue
    (f : (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).sections) (U : Cᵒᵖ) :
    O.obj U := f.val U

/-- An element of the ring of sections over an object of the site, read as a section of the
abelian-group sheaf underlying the structure sheaf regarded as a sheaf of modules over
itself.  The two types have the same carrier, and naming the identification once keeps the
development from depending on how transparently the indices unfold. -/
noncomputable def unitGroupSectionEquiv (U : Cᵒᵖ) :
    O.obj U ≃
      ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).obj
          (SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).obj.obj U where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Multiplication by a global section of the structure sheaf, read on the sections over an
object of the site: the morphism of module sheaves attached to the section acts as
multiplication by its component there. -/
theorem unitGroupSectionEquiv_toSheaf_map_apply
    (f : (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).sections) (U : Cᵒᵖ)
    (z : O.obj U) :
    ((SheafOfModules.toSheaf _).map
        ((SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).unitHomEquiv.symm
            f)).hom.app U (unitGroupSectionEquiv O hO U z) =
      unitGroupSectionEquiv O hO U (z * structureSectionValue O hO f U) := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A section of the structure sheaf of a site is regular if and only if multiplication by its
component over every object of the site is a regular element of the ring of sections there. -/
theorem isRegularSection_iff_forall_isSMulRegular_obj
    (f : (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).sections) :
    IsRegularSection O hO f ↔
      ∀ U : Cᵒᵖ, IsSMulRegular (O.obj U) (structureSectionValue O hO f U) := by
  let p := (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).unitHomEquiv.symm f
  have key (U : Cᵒᵖ) :
      Function.Injective (((SheafOfModules.toSheaf _).map p).hom.app U) ↔
        IsSMulRegular (O.obj U) (structureSectionValue O hO f U) := by
    have hcomp : (unitGroupSectionEquiv O hO U).symm ∘
        (((SheafOfModules.toSheaf _).map p).hom.app U) ∘ (unitGroupSectionEquiv O hO U) =
          fun z : O.obj U ↦ structureSectionValue O hO f U • z := by
      funext z
      show (unitGroupSectionEquiv O hO U).symm
        (((SheafOfModules.toSheaf _).map p).hom.app U (unitGroupSectionEquiv O hO U z)) = _
      rw [unitGroupSectionEquiv_toSheaf_map_apply, Equiv.symm_apply_apply, smul_eq_mul]
      exact mul_comm z (structureSectionValue O hO f U)
    have hiff := (Equiv.comp_injective
        ((((SheafOfModules.toSheaf _).map p).hom.app U) ∘ (unitGroupSectionEquiv O hO U))
        (unitGroupSectionEquiv O hO U).symm).trans
      (Equiv.injective_comp (unitGroupSectionEquiv O hO U)
        (((SheafOfModules.toSheaf _).map p).hom.app U))
    rw [hcomp] at hiff
    exact hiff.symm
  show Mono p ↔ _
  rw [← (SheafOfModules.toSheaf _).mono_map_iff_mono,
    ← (sheafToPresheaf J AddCommGrpCat.{w}).mono_map_iff_mono,
    CategoryTheory.NatTrans.mono_iff_mono_app]
  exact forall_congr' fun U ↦
    ((ConcreteCategory.mono_iff_injective_of_preservesPullback _).trans (key U))

/-- A section of the structure sheaf of a sheafed space is regular if and only if
multiplication by its component on every open is a regular element there. -/
theorem isRegularSection_iff_forall_isSMulRegular
    (X : SheafedSpace CommRingCat.{u})
    (f : (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)).sections) :
    IsRegularSection X.presheaf
        ((Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat.{u} RingCat.{u})).mp X.IsSheaf) f ↔
      ∀ U : Opens X, IsSMulRegular (X.presheaf.obj (.op U))
        (show X.presheaf.obj (.op U) from f.val (.op U)) := by
  let p := (SheafOfModules.unit _).unitHomEquiv.symm f
  have hp (U) (z : X.presheaf.obj U) :
      ((SheafOfModules.toSheaf _).map p).hom.app U z =
        (show X.presheaf.obj U from f.val U) • z := by
    show z * (show X.presheaf.obj U from f.val U) = _ * z
    exact mul_comm _ _
  show Mono p ↔ _
  rw [← (SheafOfModules.toSheaf _).mono_map_iff_mono,
    Sheaf.Hom.mono_iff_presheaf_mono, CategoryTheory.NatTrans.mono_iff_mono_app]
  refine ⟨fun h U a b hab ↦
      (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp (h (.op U)) ?_,
    fun h U ↦ ConcreteCategory.mono_of_injective _ fun a b hab ↦ h U.unop ?_⟩
  · rwa [hp (.op U) a, hp (.op U) b]
  · rwa [hp U a, hp U b] at hab

/-- The components of a global section of the structure sheaf are compatible with
restriction. -/
theorem SheafedSpace.structureSection_map
    (X : SheafedSpace CommRingCat.{u})
    (f : (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)).sections)
    {U V : Opens X} (i : U ⟶ V) :
    X.presheaf.map i.op (f.val (.op V)) = f.val (.op U) := f.property i.op

/-- Every germ of a global section of the structure sheaf is the germ of its component on the
whole space. -/
theorem SheafedSpace.germ_structureSection
    (X : SheafedSpace CommRingCat.{u})
    (f : (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)).sections)
    (U : Opens X) (x : X) (hx : x ∈ U) :
    X.presheaf.germ U x hx (f.val (.op U)) =
      X.presheaf.germ ⊤ x trivial (f.val (.op ⊤)) := by
  rw [← SheafedSpace.structureSection_map X f (homOfLE le_top)]
  exact X.presheaf.germ_res_apply _ _ _ _

end SheafedSpace

/-- A section over an open of a sheafed space is a nonzerodivisor as soon as its germ at every
point of the open is one. -/
private theorem isSMulRegular_of_forall_isSMulRegular_germ_of_mem
    (X : SheafedSpace CommRingCat.{u}) (U : Opens X) (s : X.presheaf.obj (.op U))
    (h : ∀ (x : X) (hx : x ∈ U), IsSMulRegular (X.presheaf.stalk x) (X.presheaf.germ U x hx s)) :
    IsSMulRegular (X.presheaf.obj (.op U)) s := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro b hb
  apply TopCat.Presheaf.section_ext
    (⟨X.presheaf, X.IsSheaf⟩ : TopCat.Sheaf CommRingCat.{u} X.carrier) U b 0
  intro x hx
  rw [map_zero]
  refine (h x hx).right_eq_zero_of_smul ?_
  simpa only [smul_eq_mul, map_mul, map_zero] using congrArg (X.presheaf.germ U x hx) hb

/-- A section of the structure sheaf is regular if and only if its germ at every point is a
nonzerodivisor. -/
@[stacks 01WZ "conditions (1) and (2)"]
theorem isRegularSection_iff_stalk
    (X : LocallyRingedSpace.{u})
    (f : (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)).sections) :
    IsRegularSection X.presheaf
        ((Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat.{u} RingCat.{u})).mp X.IsSheaf) f ↔
      ∀ x : X, IsSMulRegular (X.presheaf.stalk x)
        (X.presheaf.germ ⊤ x trivial (f.val (.op ⊤))) := by
  refine (isRegularSection_iff_forall_isSMulRegular X.toSheafedSpace f).trans ?_
  constructor
  · intro h x
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
    have he : X.presheaf.germ U x hx ((show X.presheaf.obj (.op U) from
        f.val (.op U)) * s) = X.presheaf.germ U x hx 0 := by
      rwa [map_mul, map_zero, SheafedSpace.germ_structureSection X.toSheafedSpace f]
    obtain ⟨W, hxW, i, j, hij⟩ := X.presheaf.germ_eq x hx hx _ _ he
    have hz : X.presheaf.map i.op s = 0 := by
      refine (h W).right_eq_zero_of_smul ?_
      have hij' : X.presheaf.map i.op
          ((show X.presheaf.obj (.op U) from f.val (.op U)) * s) = 0 := by
        simpa only [map_zero] using hij
      rwa [map_mul, SheafedSpace.structureSection_map X.toSheafedSpace f i] at hij'
    rw [← X.presheaf.germ_res_apply i x hxW s, hz, map_zero]
  · intro h U
    refine isSMulRegular_of_forall_isSMulRegular_germ_of_mem X.toSheafedSpace U _ fun x hx ↦ ?_
    rw [SheafedSpace.germ_structureSection X.toSheafedSpace f U x hx]
    exact h x

/-- A regular element of the ring of sections on an affine open has regular germs. -/
theorem isSMulRegular_germ_of_isAffineOpen
    (X : Scheme.{u}) {U : X.Opens} (hU : IsAffineOpen U)
    {s : Γ(X, U)} (hs : IsSMulRegular Γ(X, U) s) (x : U) :
    IsSMulRegular (X.presheaf.stalk x) (X.presheaf.germ U x x.property s) := by
  have := hU.isLocalization_stalk x
  exact hs.of_isLocalization (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal.primeCompl

/-- On a scheme, a section of the structure sheaf is regular if and only if its restriction
to every affine open is a nonzerodivisor. -/
@[stacks 01WZ "conditions (1) and (3)"]
theorem isRegularSection_iff_affineOpen
    (X : Scheme.{u})
    (f : (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)).sections) :
    IsRegularSection X.presheaf
        ((Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat.{u} RingCat.{u})).mp X.IsSheaf) f ↔
      ∀ U : X.Opens, IsAffineOpen U →
        IsSMulRegular Γ(X, U) (show Γ(X, U) from f.val (.op U)) := by
  refine ⟨fun h U _ ↦ (isRegularSection_iff_forall_isSMulRegular X.toSheafedSpace f).mp h U,
    fun h ↦ (isRegularSection_iff_stalk X.toLocallyRingedSpace f).mpr fun x ↦ ?_⟩
  obtain ⟨U, hx⟩ := X.isBasis_affineOpens.isOpenCover.exists_mem x
  simpa only [SheafedSpace.germ_structureSection X.toSheafedSpace f U.val x hx] using
    isSMulRegular_germ_of_isAffineOpen X U.property (h U U.property) ⟨x, hx⟩

/-- On a scheme, a section of the structure sheaf is regular if and only if its restrictions
are nonzerodivisors on the members of some affine open covering. -/
@[stacks 01WZ "conditions (1) and (4)"]
theorem isRegularSection_iff_exists_affineOpenCover
    (X : Scheme.{u})
    (f : (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)).sections) :
    IsRegularSection X.presheaf
        ((Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat.{u} RingCat.{u})).mp X.IsSheaf) f ↔
      ∃ (I : Type u) (U : I → X.Opens), IsOpenCover U ∧
        (∀ i, IsAffineOpen (U i) ∧
          IsSMulRegular Γ(X, U i) (show Γ(X, U i) from f.val (.op (U i)))) := by
  refine ⟨fun h ↦ ⟨X.affineOpens, fun U ↦ U.val, X.isBasis_affineOpens.isOpenCover,
    fun U ↦ ⟨U.property, (isRegularSection_iff_affineOpen X f).mp h U U.property⟩⟩, ?_⟩
  rintro ⟨I, U, hU, h⟩
  refine (isRegularSection_iff_stalk X.toLocallyRingedSpace f).mpr fun x ↦ ?_
  obtain ⟨i, hx⟩ := hU.exists_mem x
  simpa only [SheafedSpace.germ_structureSection X.toSheafedSpace f (U i) x hx] using
    isSMulRegular_germ_of_isAffineOpen X (h i).1 (h i).2 ⟨x, hx⟩

/-! ### Global functions on a scheme -/

/-- A global function on a scheme, read as a global section of the structure sheaf regarded
as a sheaf of modules over itself: its component on an open is the restriction of the
function to that open. -/
noncomputable def globalFunctionSections (T : Scheme.{u}) (a : Γ(T, ⊤)) :
    (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology T)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj T.sheaf)).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ show T.presheaf.obj V from
      T.presheaf.map (homOfLE (le_top (a := V.unop))).op a)
    (fun {_ _} i ↦ by
      change T.presheaf.map i (T.presheaf.map _ _) = T.presheaf.map _ _
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl)

/-- The component of `AlgebraicGeometry.globalFunctionSections` on the whole scheme is the
given function. -/
@[simp]
theorem globalFunctionSections_val_top (T : Scheme.{u}) (a : Γ(T, ⊤)) :
    (globalFunctionSections T a).val (.op ⊤) = a := by
  show T.presheaf.map (𝟙 (Opposite.op (⊤ : T.Opens))) a = a
  rw [T.presheaf.map_id]
  exact CommRingCat.id_apply (T.presheaf.obj (.op ⊤)) a

/-- A global function on a scheme is a nonzerodivisor as soon as its germ at every point
is one. -/
theorem isSMulRegular_of_forall_isSMulRegular_germ (T : Scheme.{u}) (a : Γ(T, ⊤))
    (h : ∀ z : T, IsSMulRegular (T.presheaf.stalk z)
      (T.presheaf.germ ⊤ z trivial a)) :
    IsSMulRegular Γ(T, ⊤) a := by
  exact isSMulRegular_of_forall_isSMulRegular_germ_of_mem T.toSheafedSpace ⊤ a fun z _ ↦ h z

end AlgebraicGeometry
