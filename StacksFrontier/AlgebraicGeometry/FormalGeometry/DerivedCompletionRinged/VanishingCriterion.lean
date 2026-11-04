module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationAtGlobalSection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.FirstVariable
public import StacksFrontier.Homology.Injectives.DerivedCategory.KInjectiveProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom from a principal localization

Let `(𝒞, 𝒪)` be a ringed site, let `f` be a global section of `𝒪`, and let `K ∈ D(𝒪)`. By
[Stacks, Tag 0997] the conditions `R𝑆heafHom_𝒪(𝒪_f, K) = 0`, `R𝑆heafHom_𝒪(L, K) = 0` for every
`L ∈ D(𝒪_f)`, and `T(K, f) = 0` are equivalent. This file gives `𝒪_f` as a sheaf of `𝒪`-modules,
the implication from the second condition to the first, and the identification of derived
internal Hom out of a free sheaf of modules with a product.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayRingedSite`: the ringed site `(𝒞, 𝒪_f)`.
* `AlgebraicGeometry.RingedSite.awayRestrictScalars`: restriction of scalars along `𝒪 ⟶ 𝒪_f`.
* `AlgebraicGeometry.RingedSite.awayModule`: the sheaf `𝒪_f` as a sheaf of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.derivedAwayModule`: `𝒪_f` in degree zero in `D(𝒪)`.
* `AlgebraicGeometry.RingedSite.freeComplex`: the free sheaf of `𝒪`-modules on a type, placed
  in degree zero.
* `AlgebraicGeometry.RingedSite.derivedSheafHomFreeIsoPi`: the isomorphism
  `R𝑆heafHom_𝒪(𝒪^{⊕ ι}, K) ≅ ∏_{i ∈ ι} K`, for an index type whose products exist in `D(𝒪)`.

## Main results

* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_derivedAwayModule_of_forall`: right
  orthogonality of `K` to `D(𝒪_f)` implies the vanishing of `R𝑆heafHom_𝒪(𝒪_f, K)`.
* `AlgebraicGeometry.RingedSite.isLimitFanInternalHomFree`: internal Hom out of a free sheaf of
  modules is the product of copies of internal Hom out of `𝒪`.
* `AlgebraicGeometry.RingedSite.isLimitFanHomFree`: the same for the internal Hom complex out of
  a free sheaf of modules in degree zero.
* `AlgebraicGeometry.RingedSite.isLimitFanDerivedSheafHomFree`: `R𝑆heafHom_𝒪(𝒪^{⊕ ι}, K)` is
  the product of `ι` copies of `K`, with the projections induced by the inclusions of the
  summands.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The ringed site with the same underlying site and with structure sheaf `𝒪_f`. -/
abbrev awayRingedSite : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := awaySheaf h }

/-- Restriction of scalars along the canonical map `𝒪 ⟶ 𝒪_f`. -/
abbrev awayRestrictScalars :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map (toAwaySheaf h))

/-- The sheaf `𝒪_f` obtained by inverting a global section, as a sheaf of `𝒪`-modules. -/
abbrev awayModule : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (awayRestrictScalars X h).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O))

/-- Restriction of scalars along `𝒪 ⟶ 𝒪_f` preserves finite limits. -/
instance preservesFiniteLimits_awayRestrictScalars :
    PreservesFiniteLimits (awayRestrictScalars X h) := by
  have : PreservesFiniteLimits
      (awayRestrictScalars X h ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := by
    change PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Restriction of scalars along `𝒪 ⟶ 𝒪_f` preserves finite colimits. -/
instance preservesFiniteColimits_awayRestrictScalars :
    PreservesFiniteColimits (awayRestrictScalars X h) := by
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.toSheaf.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)) :=
    preservesColimitsOfSize_shrink _
  have : PreservesFiniteColimits
      (awayRestrictScalars X h ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := by
    change PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O))
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The sheaf `𝒪_f`, placed in degree zero in the derived category of sheaves of
`𝒪`-modules. -/
abbrev derivedAwayModule :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj (awayModule X h)

/-- The functor `D(𝒪_f) ⥤ D(𝒪)` induced by restriction of scalars along `𝒪 ⟶ 𝒪_f`. -/
abbrev awayRestrictScalarsDerived :
    DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  letI : (awayRestrictScalars X h).Additive := SheafOfModules.instAdditiveRestrictScalars _
  (awayRestrictScalars X h).mapDerivedCategory

/-- Derived restriction of scalars carries the unit sheaf of `𝒪_f`, in degree zero, to
`𝒪_f` in degree zero. -/
def awayRestrictScalarsDerivedUnitIso :
    (awayRestrictScalarsDerived X h).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)) 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O))) ≅
      derivedAwayModule X h :=
  letI : (awayRestrictScalars X h).Additive := SheafOfModules.instAdditiveRestrictScalars _
  ((awayRestrictScalars X h).mapDerivedCategorySingleFunctor 0).app
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O))

/-- If `R𝑆heafHom_𝒪(L, K)` vanishes for every object `L` of `D(𝒪_f)`, viewed as an object of
`D(𝒪)` by restriction of scalars, then `R𝑆heafHom_𝒪(𝒪_f, K)` vanishes. -/
@[stacks 0997 "(2) ⇒ (1)"]
theorem isZero_derivedSheafHom_derivedAwayModule_of_forall
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (H : ∀ L : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)),
      IsZero (((derivedSheafHomBifunctor X).obj
        (op ((awayRestrictScalarsDerived X h).obj L))).obj K)) :
    IsZero (((derivedSheafHomBifunctor X).obj (op (derivedAwayModule X h))).obj K) :=
  IsZero.of_iso (H _)
    (((derivedSheafHomBifunctor X).mapIso (awayRestrictScalarsDerivedUnitIso X h).op).app K)

end Derived

section FreeSource

omit [HasWeakSheafify X.J CommRingCat.{u}]

open Stacks.SheafOfModules.InternalHom

/-- In a limit fan all but one of whose objects is zero, the remaining projection is an
isomorphism. -/
theorem isIso_fan_proj_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {α : Type*} {A : α → C} {t : Fan A} (ht : IsLimit t) (a₀ : α)
    (hA : ∀ a, a ≠ a₀ → IsZero (A a)) : IsIso (t.proj a₀) := by
  classical
  refine ⟨Fan.IsLimit.lift ht (fun a => if h : a = a₀ then eqToHom (by rw [h]) else 0),
    Fan.IsLimit.hom_ext ht _ _ fun a => ?_, ?_⟩
  · rw [Category.assoc, Fan.IsLimit.fac, Category.id_comp]
    by_cases ha : a = a₀
    · subst ha
      simp
    · rw [dite_eq_right_of_eq_false (eq_false ha), comp_zero]
      exact ((hA a ha).eq_of_tgt _ _).symm
  · rw [Fan.IsLimit.fac]
    simp

/-- Postcomposing the projections of a limit fan with isomorphisms gives a limit fan. -/
def isLimitFanCompIso {C : Type*} [Category C] {α : Type*} {A B : α → C} {P : C}
    {q : ∀ a, P ⟶ A a} (hq : IsLimit (Fan.mk P q)) (e : ∀ a, A a ≅ B a) :
    IsLimit (Fan.mk P fun a => q a ≫ (e a).hom) := by
  refine Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift hq fun a => s.proj a ≫ (e a).inv)
    (fun s a => ?_) (fun s m hm => ?_)
  · have h : (Fan.IsLimit.lift hq fun b => s.proj b ≫ (e b).inv) ≫ q a =
      s.proj a ≫ (e a).inv := Fan.IsLimit.fac hq _ a
    change (Fan.IsLimit.lift hq fun b => s.proj b ≫ (e b).inv) ≫ q a ≫ (e a).hom = s.proj a
    rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine Fan.IsLimit.hom_ext hq _ _ fun a => ?_
    have ha : m ≫ q a ≫ (e a).hom = s.proj a := hm a
    have h : (Fan.IsLimit.lift hq fun b => s.proj b ≫ (e b).inv) ≫ q a =
      s.proj a ≫ (e a).inv := Fan.IsLimit.fac hq _ a
    change m ≫ q a = (Fan.IsLimit.lift hq fun b => s.proj b ≫ (e b).inv) ≫ q a
    rw [h, ← ha]
    simp

/-- Precomposing the projections of a limit fan with an isomorphism onto its point gives a
limit fan. -/
def isLimitFanIsoComp {C : Type*} [Category C] {α : Type*} {A : α → C} {P P' : C}
    {q : ∀ a, P ⟶ A a} (hq : IsLimit (Fan.mk P q)) (e : P' ≅ P) :
    IsLimit (Fan.mk P' fun a => e.hom ≫ q a) := by
  have h : ∀ s : Fan A, ∀ a, (Fan.IsLimit.lift hq fun b => s.proj b) ≫ q a = s.proj a :=
    fun s a => Fan.IsLimit.fac hq _ a
  refine Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift hq (fun a => s.proj a) ≫ e.inv)
    (fun s a => ?_) (fun s m hm => ?_)
  · change (Fan.IsLimit.lift hq (fun b => s.proj b) ≫ e.inv) ≫ e.hom ≫ q a = s.proj a
    rw [Category.assoc, ← Category.assoc e.inv, Iso.inv_hom_id, Category.id_comp, h s a]
  · rw [Iso.eq_comp_inv]
    refine Fan.IsLimit.hom_ext hq _ _ fun a => ?_
    have ha : m ≫ e.hom ≫ q a = s.proj a := hm a
    change (m ≫ e.hom) ≫ q a = (Fan.IsLimit.lift hq fun b => s.proj b) ≫ q a
    rw [h s a, Category.assoc, ha]

/-- A fan whose projections are the components at an object of natural transformations out of
an endofunctor is a limit fan at that object as soon as it is one at an isomorphic object. -/
def isLimitFanAppOfIso {D : Type*} [Category D] {α : Type*} (Φ : D ⥤ D)
    (τ : α → (Φ ⟶ 𝟭 D)) {Z W : D} (e : Z ≅ W)
    (hZ : IsLimit (Fan.mk (Φ.obj Z) fun a => (τ a).app Z)) :
    IsLimit (Fan.mk (Φ.obj W) fun a => (τ a).app W) := by
  refine IsLimit.ofIsoLimit (isLimitFanIsoComp (isLimitFanCompIso hZ fun _ : α => e)
    (Φ.mapIso e.symm)) (Cone.ext (Iso.refl _) fun j => ?_)
  obtain ⟨a⟩ := j
  have hnat : Φ.map e.hom ≫ (τ a).app W = (τ a).app Z ≫ e.hom := (τ a).naturality e.hom
  simp only [Fan.mk_π_app, Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.symm_hom]
  rw [← hnat, ← Category.assoc, ← Φ.map_comp, e.inv_hom_id, Φ.map_id, Category.id_comp]

/-- A cofan in the opposite category is a colimit exactly when the corresponding fan is a
limit; this is the direction that produces the limit. -/
def isLimitFanOfIsColimitCofanOp {C : Type*} [Category C] {α : Type*} {W : α → C}
    {P : C} (p : ∀ a, P ⟶ W a)
    (hc : IsColimit (Cofan.mk (op P) fun a => (p a).op)) :
    IsLimit (Fan.mk P p) := by
  refine Fan.IsLimit.mk _
    (fun s => (Cofan.IsColimit.desc hc fun a => (s.proj a).op).unop)
    (fun s a => ?_) (fun s m hm => ?_)
  · exact Quiver.Hom.op_inj (by simpa using Cofan.IsColimit.fac hc _ a)
  · refine Quiver.Hom.op_inj (Cofan.IsColimit.hom_ext hc m.op _ fun a => ?_)
    have ha : m ≫ p a = s.proj a := hm a
    simp only [Quiver.Hom.op_unop]
    rw [Cofan.IsColimit.fac hc]
    simp [← op_comp, ha]

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The internal Hom sheaf `SheafHom(𝒪^{⊕ ι}, G)` is the product of `ι` copies of
`SheafHom(𝒪, G)`, with the projections induced by the inclusions of the summands. -/
def isLimitFanInternalHomFree (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ι : Type u) :
    IsLimit (Fan.mk (internalHomSheaf X (SheafOfModules.free ι) G)
      fun i : ι => internalHomPre X (C := G)
        (SheafOfModules.ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i)) :=
  isLimitFanOfIsColimitCofanOp _
    ((Cofan.isColimitMapCoconeEquiv (internalHomFirstFunctor X G) _
        (SheafOfModules.freeCofan (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι))
      (isColimitOfPreserves (internalHomFirstFunctor X G)
        (SheafOfModules.isColimitFreeCofan (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι)))

/-- Precomposition on internal Hom sheaves carries an isomorphism of sources to an isomorphism
of internal Hom sheaves. -/
def internalHomPreIso {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : A ≅ B) :
    internalHomSheaf X B C ≅ internalHomSheaf X A C where
  hom := internalHomPre X e.hom
  inv := internalHomPre X e.inv
  hom_inv_id := by rw [internalHomPre_comp, e.inv_hom_id, internalHomPre_id]
  inv_hom_id := by rw [internalHomPre_comp, e.hom_inv_id, internalHomPre_id]

/-- The free sheaf of `𝒪`-modules on `ι`, placed in degree zero. -/
abbrev freeComplex (ι : Type u) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0).obj (SheafOfModules.free ι)

/-- The inclusion in degree zero of the `i`-th copy of the structure sheaf into `𝒪^{⊕ ι}`. -/
abbrev freeComplexι (ι : Type u) (i : ι) : structureSheafComplex X ⟶ freeComplex X ι :=
  (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0).map (SheafOfModules.ιFree i)

/-- The degree-`n` term of `SheafHom(𝒪^{⊕ ι}[0], F)` is the product of `ι` copies of the
degree-`n` term of `SheafHom(𝒪[0], F)`, the projections being induced by the inclusions of the
summands. -/
def isLimitFanHomFreeDegree (ι : Type u)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    IsLimit (Fan.mk ((sheafHomComplex X (freeComplex X ι) F).obj.X n)
      fun i : ι => (homMap X (freeComplexι X ι i) (𝟙 F)).f n) := by
  have hE : IsIso (homDegreeProjection X (freeComplex X ι) F n 0) :=
    isIso_fan_proj_of_isZero (homDegreeIsLimit X (freeComplex X ι) F n) 0 fun q hq =>
      internalHomSheaf_isZero_of_isZero X
        (HomologicalComplex.isZero_single_obj_X _ 0 _ _ (neg_ne_zero.2 hq))
  have hS : IsIso (homDegreeProjection X (structureSheafComplex X) F n 0) :=
    isIso_fan_proj_of_isZero (homDegreeIsLimit X (structureSheafComplex X) F n) 0 fun q hq =>
      internalHomSheaf_isZero_of_isZero X
        (HomologicalComplex.isZero_single_obj_X _ 0 _ _ (neg_ne_zero.2 hq))
  set σS := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) with hσS
  set σE := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι) with hσE
  refine IsLimit.ofIsoLimit
    (isLimitFanCompIso
      (isLimitFanIsoComp
        (isLimitFanIsoComp
          (isLimitFanCompIso (isLimitFanInternalHomFree X (F.X (n - 0)) ι)
            fun _ : ι => internalHomPreIso X (C := F.X (n - 0)) σS)
          (internalHomPreIso X (C := F.X (n - 0)) σE.symm))
        (asIso (homDegreeProjection X (freeComplex X ι) F n 0)))
      fun _ : ι => (asIso (homDegreeProjection X (structureSheafComplex X) F n 0)).symm)
    (Cone.ext (Iso.refl _) fun j => ?_)
  obtain ⟨i⟩ := j
  have hf : (freeComplexι X ι i).f (-0) = σS.hom ≫ SheafOfModules.ιFree i ≫ σE.inv :=
    HomologicalComplex.single_map_f_self _ _ _
  change _ ≫ (asIso (homDegreeProjection X (structureSheafComplex X) F n 0)).symm.hom =
    (Iso.refl _).hom ≫ (homMap X (freeComplexι X ι i) (𝟙 F)).f n
  rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq,
    homDegreeProjection_homMap, hf]
  dsimp only [internalHomPreIso, asIso_hom, Iso.symm_hom]
  rw [internalHomPre_comp, internalHomPre_comp, Category.assoc]

/-- The internal Hom complex `SheafHom(𝒪^{⊕ ι}[0], F)` is the product of `ι` copies of
`SheafHom(𝒪[0], F)`, the projections being induced by the inclusions of the summands. -/
def isLimitFanHomFree (ι : Type u)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsLimit (Fan.mk (sheafHomComplex X (freeComplex X ι) F).obj
      fun i : ι => homMap X (freeComplexι X ι i) (𝟙 F)) :=
  HomologicalComplex.isLimitOfEval _ _ fun n =>
    (Fan.isLimitMapConeEquiv (HomologicalComplex.eval _ _ n) _ _).symm
      (isLimitFanHomFreeDegree X ι F n)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- For a K-injective complex `I`, `R𝑆heafHom_𝒪(𝒪^{⊕ ι}, I)` is the product of `ι` copies of
`I`, the projections being induced by the inclusions of the summands followed by the
identification of `R𝑆heafHom_𝒪(𝒪, I)` with `I`. -/
def isLimitFanDerivedSheafHomFreeModel (ι : Type u)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    IsLimit (Fan.mk (((derivedSheafHomBifunctor X).obj
        (op (DerivedCategory.Q.obj (freeComplex X ι)))).obj (DerivedCategory.Q.obj I))
      fun i : ι => ((derivedSheafHomBifunctor X).map
          (DerivedCategory.Q.map (freeComplexι X ι i)).op).app (DerivedCategory.Q.obj I) ≫
        (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom) := by
  have hchain : IsLimit (Fan.mk (sheafHomComplex X (freeComplex X ι) I).obj
      fun i : ι => homMap X (freeComplexι X ι i) (𝟙 I) ≫ (structureSheafHomIso X I).hom) :=
    isLimitFanCompIso (isLimitFanHomFree X ι I) fun _ : ι => structureSheafHomIso X I
  have hpi : ∀ i : ι,
      (IsLimit.conePointUniqueUpToIso hchain (productIsProduct fun _ : ι => I)).hom ≫
          Pi.π (fun _ : ι => I) i =
        homMap X (freeComplexι X ι i) (𝟙 I) ≫ (structureSheafHomIso X I).hom :=
    fun i => IsLimit.conePointUniqueUpToIso_hom_comp hchain _ ⟨i⟩
  refine IsLimit.ofIsoLimit
    (isLimitFanIsoComp
      (isLimitFanIsoComp
        (Classical.choice (Stacks.Injectives.isLimit_productFanInDerivedCategory
          (fun _ : ι => I) fun _ => inferInstance))
        (DerivedCategory.Q.mapIso
          (IsLimit.conePointUniqueUpToIso hchain (productIsProduct fun _ : ι => I))))
      (derivedSheafHomComparison X (freeComplex X ι) I))
    (Cone.ext (Iso.refl _) fun j => ?_)
  obtain ⟨i⟩ := j
  have key : ((derivedSheafHomBifunctor X).map
        (DerivedCategory.Q.map (freeComplexι X ι i)).op).app (DerivedCategory.Q.obj I) ≫
      (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom =
    (derivedSheafHomComparison X (freeComplex X ι) I).hom ≫
      DerivedCategory.Q.map (homMap X (freeComplexι X ι i) (𝟙 I)) ≫
        DerivedCategory.Q.map (structureSheafHomIso X I).hom := by
    rw [derivedStructureSheafHomIso_model, ← Category.assoc,
      derivedSheafHomComparison_naturality_id, Category.assoc,
      Stacks.Cohomology.InternalHom.homMap_eq_sheafHomComplexMap]
    rfl
  simp only [Fan.mk_π_app, Iso.refl_hom, Category.id_comp, Functor.mapIso_hom]
  rw [key, ← Functor.map_comp, hpi i, Functor.map_comp]

/-- For every object `K` of `D(𝒪)`, the object `R𝑆heafHom_𝒪(𝒪^{⊕ ι}, K)` is the product of `ι`
copies of `K`, the projections being the maps induced by the inclusions of the summands followed
by the identification of `R𝑆heafHom_𝒪(𝒪, K)` with `K`. -/
def isLimitFanDerivedSheafHomFree (ι : Type u)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsLimit (Fan.mk (((derivedSheafHomBifunctor X).obj
        (op (DerivedCategory.Q.obj (freeComplex X ι)))).obj K)
      fun i : ι => ((derivedSheafHomBifunctor X).map
          (DerivedCategory.Q.map (freeComplexι X ι i)).op).app K ≫
        (derivedStructureSheafHomIso X K).hom) :=
  isLimitFanAppOfIso _
    (fun i : ι => (derivedSheafHomBifunctor X).map
      (DerivedCategory.Q.map (freeComplexι X ι i)).op ≫ (derivedStructureSheafHomNatIso X).hom)
    (kInjectiveModelIso X K)
    (isLimitFanDerivedSheafHomFreeModel X ι (kInjectiveModel X K))

/-- `R𝑆heafHom_𝒪(𝒪^{⊕ ι}, K) ≅ ∏_{i ∈ ι} K`, for an index type whose products exist in `D(𝒪)`.
-/
def derivedSheafHomFreeIsoPi (ι : Type u)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun _ : ι => K] :
    ((derivedSheafHomBifunctor X).obj
        (op (DerivedCategory.Q.obj (freeComplex X ι)))).obj K ≅ ∏ᶜ fun _ : ι => K :=
  IsLimit.conePointUniqueUpToIso (isLimitFanDerivedSheafHomFree X ι K)
    (productIsProduct fun _ : ι => K)

/-- The `i`-th projection of `derivedSheafHomFreeIsoPi` is induced by the inclusion of the
`i`-th summand. -/
@[reassoc]
lemma derivedSheafHomFreeIsoPi_hom_π (ι : Type u)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun _ : ι => K] (i : ι) :
    (derivedSheafHomFreeIsoPi X ι K).hom ≫ Pi.π (fun _ : ι => K) i =
      ((derivedSheafHomBifunctor X).map
          (DerivedCategory.Q.map (freeComplexι X ι i)).op).app K ≫
        (derivedStructureSheafHomIso X K).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitFanDerivedSheafHomFree X ι K)
    (productIsProduct fun _ : ι => K) ⟨i⟩

end Derived

end FreeSource

end AlgebraicGeometry.RingedSite

end
