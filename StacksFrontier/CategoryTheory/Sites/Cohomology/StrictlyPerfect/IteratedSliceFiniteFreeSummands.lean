module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatFinitelyPresentedSummands

/-!
# Iterated slices of a site, and direct summands of finite free modules

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `V` be an object of the
localized site `C/U`. This file supplies the sheafification data of the *iterated* slice
`(C/U)/V`, and transports the condition of being a direct summand of a finite free module along
an equivalence of categories of sheaves of modules.

Both are prerequisites for reading Stacks 08FD — a flat module of finite presentation is locally
a direct summand of a finite free module — for a module living on a localized site `C/U` rather
than on `C`. Stacks 08FD quantifies over the slices of the site it is applied to, so applying it
on `C/U` asks for the sheafification data of the iterated slices `(C/U)/V`; and its conclusion is
phrased on those iterated slices, whereas the strictly perfect complexes of Stacks 08FL and
their consumers are written with restriction along a single arrow of `C`
(`SheafOfModules.overMap`).

## Main results

* `Stacks.SheafOfModules.iteratedSliceEssSurj`: the pushforward of sheaves along the
  iterated-slice equivalence is essentially surjective.
* `Stacks.SheafOfModules.iteratedSliceHasSheafify`,
  `Stacks.SheafOfModules.iteratedSliceHasSheafCompose` and
  `Stacks.SheafOfModules.iteratedSliceWEqualsLocallyBijective`: the sheafification data of
  `(C/U)/V`, transported from the slice `C/V.left`.
* `CategoryTheory.Over.iteratedSliceForwardCompMap` and
  `Stacks.SheafOfModules.sliceEquivOverMapFunctorIso`: restriction along the structure arrow of
  `V` is, under the iterated-slice equivalence, restriction to the iterated slice over `V`.
* `Stacks.SheafOfModules.inverseFreeIso`: an equivalence of categories of sheaves of modules
  matching up the two structure sheaves carries a finite free module to a finite free module.
* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_equivalence`: being a direct summand of
  a finite free module transports along such an equivalence.
* `Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_overMap`: Stacks 08FD
  applied on a localized site `C/U` and read back through `SheafOfModules.overMap`, which is
  what the first two items are for.

## Implementation notes

The data of an iterated slice is supplied rather than assumed. The hypotheses that the
ringed-site development carries are sheafification on `C` and on each slice `C/T`, and those do
not give the data for `(C/U)/V`: an instance proved for `C/T` does not fire at `(C/U)/V`, which
is a slice of a slice. What makes the transport possible is that Mathlib's
`CategoryTheory.Over.iteratedSliceEquiv` is an equivalence of *sites* `(C/U)/V ≌ C/V.left` —
`CategoryTheory.Functor.IsDenseSubsite` holds for its inverse — and `HasSheafify`,
`HasSheafCompose` and `WEqualsLocallyBijective` each transport along an equivalence of sites.

The transport of `WEqualsLocallyBijective` additionally asks for the pushforward on sheaves to
be essentially surjective. That is `iteratedSliceEssSurj`, proved from the composition law
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` for pushforwards along continuous
functors: the pushforward along the inverse equivalence is a quasi-inverse, so every sheaf is in
the essential image.

A finite free module is a coproduct of copies of the structure sheaf
(`SheafOfModules.free` is `∐ fun _ => SheafOfModules.unit _`), so `inverseFreeIso` is the
preservation of that coproduct by an equivalence, followed by the comparison of the two
structure sheaves in each summand. `IsDirectSummandOfFiniteFree` is then transported by carrying
the retraction across; the universe lift it is stated through plays no role, the transport being
read at equal module and ring universes through
`Stacks.SheafOfModules.isDirectSummandOfFiniteFree_iff_free`.

## References

* [Stacks Project, Tag 08FD](https://stacks.math.columbia.edu/tag/08FD)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Over

/-- **Going to the iterated slice over `V` and then pushing forward along `V.hom` is the
forgetful functor of the slice over `V`.** Both functors carry an object `W` of `(C/U)/V` to the
object `W.left` of `C/U`; the two readings `W.hom.left ≫ V.hom` and `W.left.hom` of its
structure arrow agree by `CategoryTheory.Over.w`, which is a proof and not a definitional
equality, so the comparison is an isomorphism rather than an identity. -/
def iteratedSliceForwardCompMap {C : Type u} [Category.{v} C] {U : C} (V : Over U) :
    V.iteratedSliceForward ⋙ Over.map V.hom ≅ Over.forget V :=
  NatIso.ofComponents
    (fun W => Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Over.w W.hom).symm))
    (fun f => Over.OverMorphism.ext
      ((Category.comp_id (Over.Hom.left (Over.Hom.left f))).trans (Category.id_comp _).symm))

/-- The underlying arrow of the component at `W` of `iteratedSliceForwardCompMap V` is the
identity of `W.left.left`. -/
@[simp]
theorem iteratedSliceForwardCompMap_hom_app_left {C : Type u} [Category.{v} C] {U : C}
    (V : Over U) (W : Over V) :
    ((iteratedSliceForwardCompMap V).hom.app W).left = 𝟙 W.left.left := rfl

/-- The underlying arrow of the component at `W` of the inverse of
`iteratedSliceForwardCompMap V` is the identity of `W.left.left`. -/
@[simp]
theorem iteratedSliceForwardCompMap_inv_app_left {C : Type u} [Category.{v} C] {U : C}
    (V : Over U) (W : Over V) :
    ((iteratedSliceForwardCompMap V).inv.app W).left = 𝟙 W.left.left := rfl

end CategoryTheory.Over

namespace Stacks.SheafOfModules

/-! ### Sheafification data on an iterated slice -/

section IteratedSlice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **The pushforward of sheaves along the iterated-slice equivalence is essentially
surjective.** The pushforward along the inverse equivalence is a quasi-inverse to it, by the
composition law for pushforwards along continuous functors, so every sheaf on `C/V.left` is the
image of one on `(C/U)/V`. -/
theorem iteratedSliceEssSurj (A : Type*) [Category* A] {U : C} (V : Over U) :
    (V.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A
      (J.over V.left) ((J.over U).over V)).EssSurj := by
  have iso : V.iteratedSliceEquiv.functor.sheafPushforwardContinuous A
        ((J.over U).over V) (J.over V.left) ⋙
      V.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A
        (J.over V.left) ((J.over U).over V) ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousComp' V.iteratedSliceEquiv.counitIso A _ _ _
  exact ⟨fun Y => ⟨_, ⟨iso.app Y⟩⟩⟩

/-- **Sheafification on an iterated slice.** The iterated slice `(C/U)/V` is equivalent, as a
site, to the slice `C/V.left`, so `HasSheafify` transports to it. -/
theorem iteratedSliceHasSheafify (A : Type*) [Category* A] {U : C} (V : Over U)
    [HasSheafify (J.over V.left) A] : HasSheafify ((J.over U).over V) A :=
  V.iteratedSliceEquiv.hasSheafify ((J.over U).over V) (J.over V.left) A

/-- **Composition with a functor preserves sheaves on an iterated slice**, transported from the
slice `C/V.left` along the iterated-slice equivalence of sites. -/
theorem iteratedSliceHasSheafCompose {A : Type*} [Category* A] {B : Type*} [Category* B]
    (F : A ⥤ B) {U : C} (V : Over U) [(J.over V.left).HasSheafCompose F] :
    ((J.over U).over V).HasSheafCompose F :=
  V.iteratedSliceEquiv.hasSheafCompose ((J.over U).over V) (J.over V.left) F

/-- **The weak equivalences of an iterated slice are exactly the locally bijective maps**,
transported from the slice `C/V.left` along the iterated-slice equivalence of sites; the
essential surjectivity the transport asks for is `iteratedSliceEssSurj`. -/
theorem iteratedSliceWEqualsLocallyBijective (A : Type*) [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] {U : C} (V : Over U)
    [(J.over V.left).WEqualsLocallyBijective A] :
    ((J.over U).over V).WEqualsLocallyBijective A :=
  have := iteratedSliceEssSurj (J := J) A V
  GrothendieckTopology.WEqualsLocallyBijective.transport ((J.over U).over V) (J.over V.left)
    V.iteratedSliceEquiv.inverse
    (Functor.IsDenseSubsite.coverPreserving (J.over V.left) ((J.over U).over V) _)

end IteratedSlice

/-! ### Restriction along an arrow read on the iterated slice -/

section OverMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Restriction along `V.hom` read on the iterated slice over `V`.** Under the equivalence
`Stacks.SheafOfModules.sliceEquiv` of sheaves of modules on `C/V.left` with sheaves of modules
on the iterated slice `(C/U)/V`, the restriction `SheafOfModules.overMap R V.hom` along the
structure arrow of `V` corresponds to the restriction `SheafOfModules.overFunctor (R.over U) V`
to the iterated slice.

Unlike `Stacks.SheafOfModules.sliceEquivObjIso` this is not the identity on sections: the two
sides are pushforwards along `Over.iteratedSliceForward V ⋙ Over.map V.hom` and along
`Over.forget V`, functors which agree on underlying objects but not on structure arrows, and
`SheafOfModules.overMap` moreover carries the comparison `Sheaf.pushforwardOverMapIso` of the
two sheaves of rings in its restriction-of-scalars datum where
`SheafOfModules.overFunctor` carries the identity. Both discrepancies are discharged by
`SheafOfModules.pushforwardCongr₂` applied to `CategoryTheory.Over.iteratedSliceForwardCompMap`:
the two structure maps have the same components, namely the identity. -/
def sliceEquivOverMapFunctorIso (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    SheafOfModules.overMap.{w} R V.hom ⋙ (sliceEquiv R U V).functor ≅
      SheafOfModules.overFunctor.{w} (R.over U) V := by
  have : Functor.IsContinuous (V.iteratedSliceForward ⋙ Over.map V.hom)
      ((J.over U).over V) (J.over U) :=
    Functor.isContinuous_comp _ _ ((J.over U).over V) (J.over V.left) (J.over U)
  refine SheafOfModules.pushforwardComp (𝟙 _) (Sheaf.pushforwardOverMapIso R V.hom).inv ≪≫
    (SheafOfModules.pushforwardCongr₂ (𝟙 _) (Over.iteratedSliceForwardCompMap V) ?_).symm
  ext W : 3
  exact (R.obj.map_id _).trans (Category.id_comp _).symm

/-- **Restriction of a single sheaf of modules along `V.hom`, read on the iterated slice over
`V`.** This is `Stacks.SheafOfModules.sliceEquivOverMapFunctorIso` at `F`; it is the
identification which lets Stacks 08FD, whose conclusion is phrased on the iterated slices of
`C/U`, be read through `SheafOfModules.overMap`, as the strictly perfect complexes of Stacks
08FL are. -/
def sliceEquivOverMapIso {R : Sheaf J RingCat.{w}} {U : C} (V : Over U)
    (F : SheafOfModules.{w} (R.over U)) :
    (sliceEquiv R U V).functor.obj ((SheafOfModules.overMap.{w} R V.hom).obj F) ≅ F.over V :=
  (sliceEquivOverMapFunctorIso R U V).app F

end OverMap

/-! ### Transporting the finite-free-summand condition -/

section Transport

variable {C₁ : Type*} [Category* C₁] {J₁ : GrothendieckTopology C₁} {R₁ : Sheaf J₁ RingCat.{w}}
  {C₂ : Type*} [Category* C₂] {J₂ : GrothendieckTopology C₂} {R₂ : Sheaf J₂ RingCat.{w}}
  [HasWeakSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **An equivalence matching up the two structure sheaves carries a finite free module to a
finite free module.** A free module on an index type is the coproduct of copies of the structure
sheaf indexed by it, an equivalence preserves that coproduct, and the comparison of the two
structure sheaves identifies the summands. -/
def inverseFreeIso (e : SheafOfModules.{w} R₁ ≌ SheafOfModules.{w} R₂)
    (η : e.inverse.obj (SheafOfModules.unit R₂) ≅ SheafOfModules.unit R₁) (I : Type w) :
    e.inverse.obj (SheafOfModules.free (R := R₂) I) ≅ SheafOfModules.free (R := R₁) I :=
  haveI : HasCoproducts.{w} (SheafOfModules.{w} R₁) := fun K =>
    @SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _ _ R₁ _ _ (Discrete K) _
      (@PresheafOfModules.hasColimitsOfShape _ _ R₁.obj (Discrete K) _
        AddCommGrpCat.hasColimitsOfShape)
  haveI : HasCoproducts.{w} (SheafOfModules.{w} R₂) := fun K =>
    @SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _ _ R₂ _ _ (Discrete K) _
      (@PresheafOfModules.hasColimitsOfShape _ _ R₂.obj (Discrete K) _
        AddCommGrpCat.hasColimitsOfShape)
  haveI : PreservesColimitsOfShape (Discrete I) e.inverse :=
    (e.symm.toAdjunction.leftAdjoint_preservesColimits.{w, w}).preservesColimitsOfShape
  (isColimitOfPreserves e.inverse
    (SheafOfModules.isColimitFreeCofan (R := R₂) I)).coconePointsIsoOfNatIso
    (SheafOfModules.isColimitFreeCofan (R := R₁) I) (Discrete.natIso fun _ => η)

/-- **Being a direct summand of a finite free module transports along an equivalence.** Let `e`
identify the two categories of sheaves of modules and match up the two structure sheaves. If
`e.inverse` carries `N` to `M`, then `M` is a direct summand of a finite free module as soon as
`N` is: the retraction of `N` off a finite free module is carried across by `e.inverse`, and its
target is again finite free by `inverseFreeIso`. -/
theorem isDirectSummandOfFiniteFree_of_equivalence
    [J₁.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [J₂.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    (e : SheafOfModules.{w} R₁ ≌ SheafOfModules.{w} R₂)
    (η : e.inverse.obj (SheafOfModules.unit R₂) ≅ SheafOfModules.unit R₁)
    {M : SheafOfModules.{w} R₁} {N : SheafOfModules.{w} R₂}
    (ρ : e.inverse.obj N ≅ M) (h : IsDirectSummandOfFiniteFree R₂ N) :
    IsDirectSummandOfFiniteFree R₁ M := by
  rw [isDirectSummandOfFiniteFree_iff_free] at h ⊢
  obtain ⟨n, i, r, hir⟩ := h
  refine ⟨n, ρ.inv ≫ e.inverse.map i ≫ (inverseFreeIso e η _).hom,
    (inverseFreeIso e η _).inv ≫ e.inverse.map r ≫ ρ.hom, ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← e.inverse.map_comp_assoc, hir,
    e.inverse.map_id, Category.id_comp, Iso.inv_hom_id]

end Transport

/-! ### Stacks 08FD on a slice, read through restriction along an arrow of the base -/

section Slice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [∀ T : C, HasSheafify (J.over T) AddCommGrpCat.{max u v}]
  [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ T : C, (J.over T).HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [∀ T : C, (J.over T).HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
  (U : C)
  [∀ T : Over U, HasWeakSheafify ((J.over U).over T) AddCommGrpCat.{max u v}]
  [∀ T : Over U, ((J.over U).over T).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ T : Over U, ((J.over U).over T).HasSheafCompose
    (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

/-- **Stacks 08FD on a slice, read through `SheafOfModules.overMap`.** Let `F` be a flat sheaf
of modules of finite presentation on the localized ringed site `(C/U, O|_U)` and let `W₀` be an
object of `C/U`. Then `W₀` admits a covering sieve over each member `W` of which the restriction
of `F` along the structure arrow `W.hom : W.left ⟶ U` is a direct summand of a finite free
`O|_{W.left}`-module.

Stacks 08FD itself produces that conclusion over the *iterated* slices `(C/U)/W`, where the
strictly perfect complexes of Stacks 08FL cannot read it: those are written with restriction
along a single arrow of the base site. The translation is
`Stacks.SheafOfModules.sliceEquivOverMapIso` together with
`Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_equivalence`. The sheafification data of
the iterated slices is assumed rather than derived: it is supplied by
`Stacks.SheafOfModules.iteratedSliceHasSheafify`,
`Stacks.SheafOfModules.iteratedSliceWEqualsLocallyBijective` and
`Stacks.SheafOfModules.iteratedSliceHasSheafCompose`, which are stated at an unconstrained
universe for the target category and therefore cannot be registered as instances at the
universe `max u v` of the sections. -/
theorem exists_coveringSieve_isDirectSummandOfFiniteFree_overMap
    (O : Sheaf J CommRingCat.{max u v})
    (F : SheafOfModules.{max u v} (commRingSheafToRingSheaf (O.over U)))
    [F.IsFinitePresentation] (hF : IsFlat F) (W₀ : Over U) :
    ∃ S : Sieve W₀, S ∈ (J.over U) W₀ ∧ ∀ {W : Over U} (g : W ⟶ W₀), S g →
      IsDirectSummandOfFiniteFree ((commRingSheafToRingSheaf O).over W.left)
        ((SheafOfModules.overMap.{max u v} (commRingSheafToRingSheaf O) W.hom).obj F) := by
  obtain ⟨S, hS, h⟩ :=
    exists_coveringSieve_isDirectSummandOfFiniteFree (O.over U) F hF W₀
  refine ⟨S, hS, fun {W} g hg => ?_⟩
  let e := sliceEquiv (commRingSheafToRingSheaf O) U W
  refine isDirectSummandOfFiniteFree_of_equivalence e
    (e.inverse.mapIso (sliceEquivUnitIso (commRingSheafToRingSheaf O) U W).symm ≪≫
      (e.unitIso.app (SheafOfModules.unit ((commRingSheafToRingSheaf O).over W.left))).symm)
    (e.inverse.mapIso
        (sliceEquivOverMapIso (R := commRingSheafToRingSheaf O) (U := U) W F).symm ≪≫
      (e.unitIso.app ((SheafOfModules.overMap.{max u v}
        (commRingSheafToRingSheaf O) W.hom).obj F)).symm)
    (h g hg)

end Slice

end Stacks.SheafOfModules

end
