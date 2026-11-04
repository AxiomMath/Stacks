module

public import Mathlib.CategoryTheory.Core
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleFibration
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatGroupoid

/-!
# The category fibred in groupoids of Frobenius-colimit vector bundles

`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleFibration` builds the category
over the big h site whose fibre over `U` is the *category* of finite locally free
`colim_F 𝒪_U`-modules, which is the fibre Stacks Tag 0EXE names and the one for which the tag's
closing identification with `colim_F Vect(U)` is literally true. That category is fibred, but not
fibred in groupoids: a category of modules has non-invertible endomorphisms.

Stacks Tag 0EXE calls its `𝒮` a category fibred *in groupoids*, and the criterion it invokes,
Stacks Tag 0EX9, is about categories fibred in groupoids. This file therefore builds the
**maximal subgroupoid** version: the same objects over each `U`, with only the isomorphisms as
morphisms. It is this one that can carry the tag's stackness assertion.

The construction cores the pseudofunctor of *all* Frobenius-colimit modules and only then cuts
out the finite locally free objects, which is what makes it cheap: `Mathlib`'s
`CategoryTheory.Functor.coreId` and `CategoryTheory.Functor.coreComp` are `Iso.refl`, so
`(F ⋙ G).core` is *definitionally* `F.core ⋙ G.core` and the three coherences of the cored
pseudofunctor are the `CategoryTheory.Iso.core` images of the three coherences already proved;
and `CategoryTheory.Pseudofunctor.ObjectProperty.fullsubcategory` then asks for no coherence of
its own.

## Main definitions

* `CategoryTheory.Functor.core_isoWhiskerLeft`, `core_isoWhiskerRight`, `core_associator` and
  `CategoryTheory.Iso.core_symm`, `Iso.core_eqToIso`: `CategoryTheory.Iso.core` of the structural
  isomorphisms, in the form the coherences need.
* `AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor`: the maximal-subgroupoid
  pseudofunctor of all Frobenius-colimit modules.
* `AlgebraicGeometry.frobeniusVectorBundleGroupoidPseudofunctor`: **the pseudofunctor in
  groupoids of Stacks Tag 0EXE**, sending `U` to the groupoid of finite locally free
  `colim_F 𝒪_U`-modules and their isomorphisms.
* `AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration`: **the structure functor
  `p : 𝒮 ⟶ (Sch/S)_h` of Stacks Tag 0EXE**, in the form Stacks Tag 0EX9 is about.

## Main results

* `AlgebraicGeometry.bigHFrobeniusColimitPullbackComp_assoc`,
  `bigHFrobeniusColimitPullbackId_comp` and `bigHFrobeniusColimitPullbackComp_id`: the three
  coherences of the transition functors over the big h site, named so that they can be cored.
* `AlgebraicGeometry.frobeniusVectorBundleGroupoidFiberEquiv`: the fibre over `U` is the
  groupoid of finite locally free `colim_F 𝒪_U`-modules and their isomorphisms.
* `AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration_isFiberedInGroupoids`: **the
  structure functor is a category fibred in groupoids** — it is fibred, by the Grothendieck
  construction, and every fibre is a groupoid, being a full subcategory of a core.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

/-- **The core of a composite is the composite of the cores**, as an equality of functors and
not merely an isomorphism: Mathlib's `CategoryTheory.Functor.coreComp` is `Iso.refl`, so the two
functors are definitionally equal. Stated because `simp` matches syntactically, and the
structural isomorphisms of the coherences below are spelled on one side of this equation and on
the other. -/
lemma Functor.comp_core (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).core = F.core ⋙ G.core := rfl

/-- **The core of the identity functor is the identity functor of the core**, as an equality. -/
lemma Functor.id_core : (𝟭 C).core = 𝟭 (Core C) := rfl

/-- Taking cores turns the whiskering of a natural isomorphism on the left into the whiskering
of its core. The composition comparison `CategoryTheory.Functor.coreComp` is the identity, so
Mathlib's `CategoryTheory.Iso.coreWhiskerLeft` says exactly this. -/
lemma Functor.core_isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (η : G ≅ H) :
    (Functor.isoWhiskerLeft F η).core = Functor.isoWhiskerLeft F.core η.core := by
  simp [Iso.coreWhiskerLeft, Functor.coreComp, Functor.comp_core]

/-- Taking cores turns the whiskering of a natural isomorphism on the right into the whiskering
of its core. -/
lemma Functor.core_isoWhiskerRight {F G : C ⥤ D} (η : F ≅ G) (H : D ⥤ E) :
    (Functor.isoWhiskerRight η H).core = Functor.isoWhiskerRight η.core H.core := by
  simp [Iso.coreWhiskerRight, Functor.coreComp, Functor.comp_core]

/-- Taking cores turns the associator into the associator of the cores. -/
lemma Functor.core_associator (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (Functor.associator F G H).core = Functor.associator F.core G.core H.core := by
  simp [Iso.coreAssociator, Functor.coreComp, Functor.comp_core]

/-- The core of the inverse of a natural isomorphism is the inverse of its core. -/
lemma Iso.core_symm {F G : C ⥤ D} (η : F ≅ G) : η.symm.core = η.core.symm := by
  ext X
  rfl

/-- The core of a transport along an equality of functors is the transport along the induced
equality of cores. -/
lemma Iso.core_eqToIso {F G : C ⥤ D} (h : F = G) :
    (eqToIso h).core = eqToIso (congrArg Functor.core h) := by
  subst h
  rfl

/-- **The associativity pentagon survives taking cores.** -/
lemma Functor.corePentagon (mF : C ⥤ D) (mG : D ⥤ E) (mH : E ⥤ E')
    (mFG : C ⥤ E) (mGH : D ⥤ E') (mFGH : C ⥤ E')
    (cFG : mF ⋙ mG ≅ mFG) (cGH : mG ⋙ mH ≅ mGH)
    (c₁ : mF ⋙ mGH ≅ mFGH) (c₂ : mFG ⋙ mH ≅ mFGH)
    (pent : Functor.isoWhiskerLeft mF cGH ≪≫ c₁ =
      (Functor.associator mF mG mH).symm ≪≫ Functor.isoWhiskerRight cFG mH ≪≫ c₂) :
    Functor.isoWhiskerLeft mF.core cGH.core ≪≫ c₁.core =
      (Functor.associator mF.core mG.core mH.core).symm ≪≫
        Functor.isoWhiskerRight cFG.core mH.core ≪≫ c₂.core := by
  have h := congrArg Iso.core pent
  rw [Iso.coreComp, Iso.coreComp, Iso.coreComp, Functor.core_isoWhiskerLeft,
    Functor.core_isoWhiskerRight, Iso.core_symm, Functor.core_associator] at h
  exact h

/-- **The left unit coherence survives taking cores.** -/
lemma Functor.coreLeftUnit (mE : C ⥤ C) (mF mFE : C ⥤ D)
    (cE : mE ≅ 𝟭 C) (cC : mE ⋙ mF ≅ mFE) (hFE : mFE = mF)
    (hu : cC ≪≫ eqToIso hFE = Functor.isoWhiskerRight cE mF ≪≫ Functor.leftUnitor mF) :
    cC.core ≪≫ eqToIso (congrArg Functor.core hFE) =
      Functor.isoWhiskerRight cE.core mF.core ≪≫ Functor.leftUnitor mF.core := by
  simpa [Iso.coreComp, Iso.core_eqToIso, Functor.core_isoWhiskerRight, Iso.coreLeftUnitor,
    Functor.coreComp, Functor.coreId, Functor.comp_core, Functor.id_core] using congrArg Iso.core hu

/-- **The right unit coherence survives taking cores.** -/
lemma Functor.coreRightUnit (mF mFE : C ⥤ D) (mE : D ⥤ D)
    (cE : mE ≅ 𝟭 D) (cC : mF ⋙ mE ≅ mFE) (hFE : mFE = mF)
    (hu : cC ≪≫ eqToIso hFE = Functor.isoWhiskerLeft mF cE ≪≫ Functor.rightUnitor mF) :
    cC.core ≪≫ eqToIso (congrArg Functor.core hFE) =
      Functor.isoWhiskerLeft mF.core cE.core ≪≫ Functor.rightUnitor mF.core := by
  simpa [Iso.coreComp, Iso.core_eqToIso, Functor.core_isoWhiskerLeft, Iso.coreRightUnitor,
    Functor.coreComp, Functor.coreId, Functor.comp_core, Functor.id_core] using congrArg Iso.core hu

end CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- **The maximal-subgroupoid pseudofunctor of all Frobenius-colimit modules.** It sends an
object `U` of the big h category over `S` to the groupoid of sheaves of `colim_F 𝒪_U`-modules and
their isomorphisms, and an arrow to the core of the transition functor.

Its three coherences are the `CategoryTheory.Iso.core` images of the three coherences of the
transition functors, by `CategoryTheory.Functor.corePentagon`,
`CategoryTheory.Functor.coreLeftUnit` and `CategoryTheory.Functor.coreRightUnit`. -/
def frobeniusColimitModuleCorePseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{u, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun U => Cat.of (Core (_root_.SheafOfModules.{u}
      (bigHFrobeniusColimitRingSheaf B S hS p hpS U.unop))))
    (fun {_ _} f => Functor.toCatHom (bigHFrobeniusColimitPullback B S hS p hpS f).core)
    (fun U => Cat.Hom.isoMk (bigHFrobeniusColimitPullbackId B S hS p hpS U).core)
    (fun {_ _ _} f g =>
      Cat.Hom.isoMk (bigHFrobeniusColimitPullbackComp B S hS p hpS f g).core.symm)
    (fun {_ _ _ _} f g h =>
      Cat.map₂_associator_of_pentagon
        (bigHFrobeniusColimitPullback B S hS p hpS f).core
        (bigHFrobeniusColimitPullback B S hS p hpS g).core
        (bigHFrobeniusColimitPullback B S hS p hpS h).core
        (bigHFrobeniusColimitPullback B S hS p hpS (f ≫ g)).core
        (bigHFrobeniusColimitPullback B S hS p hpS (g ≫ h)).core
        (bigHFrobeniusColimitPullback B S hS p hpS (f ≫ g ≫ h)).core
        (bigHFrobeniusColimitPullbackComp B S hS p hpS f g).core
        (bigHFrobeniusColimitPullbackComp B S hS p hpS g h).core
        (bigHFrobeniusColimitPullbackComp B S hS p hpS f (g ≫ h)).core
        (bigHFrobeniusColimitPullbackComp B S hS p hpS (f ≫ g) h).core
        (Functor.corePentagon _ _ _ _ _ _ _ _ _ _
          (bigHFrobeniusColimitPullbackComp_assoc B S hS p hpS f g h)))
    (fun {b₀ b₁} f =>
      Cat.map₂_left_unitor_of_unit
        (bigHFrobeniusColimitPullback B S hS p hpS (𝟙 b₀)).core
        (bigHFrobeniusColimitPullback B S hS p hpS f).core
        (bigHFrobeniusColimitPullback B S hS p hpS (𝟙 b₀ ≫ f)).core
        (bigHFrobeniusColimitPullbackId B S hS p hpS b₀).core
        (bigHFrobeniusColimitPullbackComp B S hS p hpS (𝟙 b₀) f).core
        (congrArg Functor.core
          (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
            (Category.id_comp f)))
        (Functor.coreLeftUnit _ _ _ _ _ _
          (bigHFrobeniusColimitPullbackId_comp B S hS p hpS f)))
    (fun {b₀ b₁} f =>
      Cat.map₂_right_unitor_of_unit
        (bigHFrobeniusColimitPullback B S hS p hpS f).core
        (bigHFrobeniusColimitPullback B S hS p hpS (f ≫ 𝟙 b₁)).core
        (bigHFrobeniusColimitPullback B S hS p hpS (𝟙 b₁)).core
        (bigHFrobeniusColimitPullbackId B S hS p hpS b₁).core
        (bigHFrobeniusColimitPullbackComp B S hS p hpS f (𝟙 b₁)).core
        (congrArg Functor.core
          (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
            (Category.comp_id f)))
        (Functor.coreRightUnit _ _ _ _ _ _
          (bigHFrobeniusColimitPullbackComp_id B S hS p hpS f)))

/-- **Being finite locally free**, as a property of the objects of the groupoids of
`AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor`. The objects are those of the
underlying categories, so this is the same property as before. -/
def frobeniusColimitCoreFiniteLocallyFree :
    (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).ObjectProperty where
  prop _ := fun M => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M.of

/-- The finite locally free property is preserved by the cores of the transition functors,
because it is preserved by the transition functors themselves. -/
instance : (frobeniusColimitCoreFiniteLocallyFree B S hS p hpS).IsClosedUnderMapObj where
  map_obj {_ _} {M} hM f :=
    isFiniteLocallyFree_frobeniusColimitPullback p
      ((BigHOver.toScheme B S hS).map f.as.unop) _ _ M.of hM

/-- **The pseudofunctor in groupoids of Stacks Tag 0EXE.** It sends an object `U` of the big h
category over `S` to the groupoid of finite locally free `colim_F 𝒪_U`-modules and their
isomorphisms. -/
def frobeniusVectorBundleGroupoidPseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{u, u + 1} :=
  (frobeniusColimitCoreFiniteLocallyFree B S hS p hpS).fullsubcategory

/-- **The category `𝒮` of Stacks Tag 0EXE, in groupoids**: the Grothendieck construction of the
pseudofunctor in groupoids of finite locally free Frobenius-colimit modules. -/
abbrev FrobeniusVectorBundleGroupoidTotal : Type (u + 1) :=
  Pseudofunctor.CoGrothendieck (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS)

/-- **The structure functor `p : 𝒮 ⟶ (Sch/S)_h` of Stacks Tag 0EXE**, in the form Stacks Tag
0EX9 is about. -/
abbrev frobeniusVectorBundleGroupoidFibration :
    FrobeniusVectorBundleGroupoidTotal B S hS p hpS ⥤ BigHOver B S hS :=
  Pseudofunctor.CoGrothendieck.forget (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS)

/-- The category the maximal-subgroupoid pseudofunctor assigns to an object is a groupoid: it is
a core. Stated as an instance because instance synthesis does not see through the pseudofunctor's
object map. -/
instance isGroupoid_frobeniusColimitModuleCoreObj (U : (BigHOver B S hS)ᵒᵖ) :
    IsGroupoid ((frobeniusColimitModuleCorePseudofunctor B S hS p hpS).obj ⟨U⟩) :=
  inferInstanceAs (IsGroupoid (Core (_root_.SheafOfModules.{u}
    (bigHFrobeniusColimitRingSheaf B S hS p hpS U.unop))))

/-- **The finite locally free objects of a core form a groupoid**: a full subcategory of a
groupoid is a groupoid, the inclusion of a full subcategory being fully faithful. -/
instance isGroupoid_frobeniusColimitCoreFiniteLocallyFreeObj (U : (BigHOver B S hS)ᵒᵖ) :
    IsGroupoid ((frobeniusColimitCoreFiniteLocallyFree B S hS p hpS).Obj ⟨U⟩) :=
  isGroupoid_of_fullyFaithful
    (ObjectProperty.ι ((frobeniusColimitCoreFiniteLocallyFree B S hS p hpS).prop ⟨U⟩))

/-- **Each category of the pseudofunctor in groupoids of Stacks Tag 0EXE really is a groupoid.**
Stated as an instance because instance synthesis does not see through the pseudofunctor's object
map. -/
instance isGroupoid_frobeniusVectorBundleGroupoidObj (U : (BigHOver B S hS)ᵒᵖ) :
    IsGroupoid ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj ⟨U⟩) :=
  inferInstanceAs
    (IsGroupoid ((frobeniusColimitCoreFiniteLocallyFree B S hS p hpS).Obj ⟨U⟩))

/-- **The fibre of Stacks Tag 0EXE in groupoids over `U` is the groupoid of finite locally free
`colim_F 𝒪_U`-modules and their isomorphisms** — the objects are those of the fibre of
`AlgebraicGeometry.frobeniusVectorBundleFibration` and the morphisms are its isomorphisms, since
`AlgebraicGeometry.frobeniusColimitCoreFiniteLocallyFree` cuts the finite locally free objects out
of the core. This is the fibre category Stacks Tag 0EX9's conditions are quantified over. -/
def frobeniusVectorBundleGroupoidFiberEquiv (U : BigHOver B S hS) :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).Fiber U ≌
      (frobeniusColimitCoreFiniteLocallyFree B S hS p hpS).Obj ⟨op U⟩ :=
  (Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) U)).asEquivalence.symm

/-- **The structure functor of Stacks Tag 0EXE is a category fibred in groupoids.** It is a
fibred category, by the Grothendieck construction, and each of its fibres is equivalent to the
groupoid the pseudofunctor assigns, so Stacks Tag 003V applies. -/
theorem frobeniusVectorBundleGroupoidFibration_isFiberedInGroupoids :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.mk' fun U =>
    isGroupoid_of_equivalence
      (Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const
        (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) U)).asEquivalence

end AlgebraicGeometry

end
