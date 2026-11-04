module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist

/-!
# The category over the big h site of Frobenius-colimit vector bundles

Let `p` be a prime and let `S` be a scheme in characteristic `p`. Stacks Tag 0EXE is about the
category fibred in groupoids over the big h site `(Sch/S)_h` of Stacks Tag 0EU1 whose fibre over
an object `U` is the category of finite locally free `colim_F 𝒪_U`-modules, and asserts that it is
a stack in groupoids; its "moreover" clause says that for quasi-compact quasi-separated `U` that
fibre is `colim_F Vect(U)`.

This file **constructs that category over the site** and **proves the "moreover" clause**. The
construction is the Grothendieck construction of a pseudofunctor assembled from the canonical
morphism of Frobenius-colimit structure sheaves of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial`: its transition functors are
extension of scalars along that morphism, its identity and composition comparisons are the
comparisons of extension of scalars, and its three coherences are the three coherences proved
there.

## Main definitions

* `CategoryTheory.Cat.map₂_associator_of_pentagon`,
  `CategoryTheory.Cat.map₂_left_unitor_of_unit` and
  `CategoryTheory.Cat.map₂_right_unitor_of_unit`: the three conditions of
  `CategoryTheory.LocallyDiscrete.mkPseudofunctor` from the corresponding coherences of
  comparison isomorphisms of functors.
* `AlgebraicGeometry.frobeniusColimitModulePseudofunctor`: the pseudofunctor sending an object `U`
  of the big h category over `S` to **all** sheaves of `colim_F 𝒪_U`-modules.
* `AlgebraicGeometry.frobeniusColimitFiniteLocallyFree`: the property, on the categories of that
  pseudofunctor, of being finite locally free.
* `AlgebraicGeometry.frobeniusVectorBundlePseudofunctor`: **the pseudofunctor of Stacks Tag
  0EXE**, the sub-pseudofunctor that property cuts out, sending `U` to the finite locally free
  `colim_F 𝒪_U`-modules.
* `AlgebraicGeometry.frobeniusVectorBundleFibration`: **the structure functor
  `𝒮 ⟶ (Sch/S)_h` of Stacks Tag 0EXE**, the Grothendieck construction of that pseudofunctor
  followed by its forgetful functor. It is a fibred category, with the cartesian lifts of the
  Grothendieck construction, by Mathlib's instance for
  `CategoryTheory.Pseudofunctor.CoGrothendieck.forget`.

## Main results

* `AlgebraicGeometry.isInCharacteristic_bigHOver`: every object of the big h category over `S` is
  in characteristic `p`, because it comes with a morphism to `S`.
* `AlgebraicGeometry.frobeniusVectorBundleFiberEquiv`: **the fibre over `U` is the category of
  finite locally free `colim_F 𝒪_U`-modules**, which is the fibre category Stacks Tag 0EXE names.
* `AlgebraicGeometry.frobeniusVectorBundleFiberEquivColimitVect`: **for `U` quasi-compact and
  quasi-separated the fibre is `colim_F Vect(U)`** — the "moreover" clause of Stacks Tag 0EXE.
  This is Stacks Tag 0EXB, `AlgebraicGeometry.frobeniusColimitVectEquivalence`,
  transported along the previous item; nothing of 0EXB is restated here.

## Implementation notes

**Why two pseudofunctors.** Mathlib's
`CategoryTheory.Pseudofunctor.ObjectProperty.fullsubcategory` builds a sub-pseudofunctor out of a
pseudofunctor and a property of objects closed under the transition functors, and asks for no
coherence of its own. The three coherences are therefore proved once, for all sheaves of modules,
and the finite locally free ones are cut out afterwards.

**The direction of the comparisons.** `CategoryTheory.LocallyDiscrete.mkPseudofunctor` asks for
`mapComp f g : map (f ≫ g) ≅ map f ≫ map g`, while
`AlgebraicGeometry.frobeniusColimitPullbackCompOfEq` is the comparison in the other direction, so
the field is its `Iso.symm`; the base category is `(Sch/S)_h` opposite, so an arrow `f` of the
base is used through `f.unop`, and `(f ≫ g).unop` is `g.unop ≫ f.unop`.

**Why the three conditions are discharged through parameters and not by unfolding.** Each
condition of `CategoryTheory.LocallyDiscrete.mkPseudofunctor` compares a composite of comparisons
with `eqToHom` of an associativity or unit equation of the base. Those equations do hold
definitionally here — composition in the big h category over `S` is composition of morphisms of
schemes — but the *transition functor* attached to an arrow is extension of scalars along a
morphism out of a sequential colimit, and asking the elaborator to see
`map (𝟙 U ≫ f)` and `map f` as the same functor makes it unfold that colimit. So the functor
attached to the composite and the identification of the two are parameters of the bridge lemmas,
and at the point of use the identification is supplied by `congrArg` from `Category.id_comp`,
respectively `Category.comp_id`, of the base. The associativity condition needs no such
parameter: there the two sides of the `eqToHom` are the same arrow of the base.

**Universes.** The fibre categories have objects in `Type (u + 1)` and morphisms in `Type u`, so
the pseudofunctor lands in `Cat.{u, u + 1}` and no transport of morphism universes is needed.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

namespace CategoryTheory.Cat

universe v₁ u₁

variable {A₀ : Type u₁} {A₁ : Type u₁} {A₂ : Type u₁} {A₃ : Type u₁}
  [Category.{v₁} A₀] [Category.{v₁} A₁] [Category.{v₁} A₂] [Category.{v₁} A₃]

/-- **The associativity condition of `CategoryTheory.LocallyDiscrete.mkPseudofunctor` from the
pentagon of the comparison isomorphisms.** For six functors and four comparison isomorphisms
between their composites satisfying the pentagon, the composite of `2`-morphisms of `Cat` that
`CategoryTheory.LocallyDiscrete.mkPseudofunctor` asks to be an identity is one. -/
lemma map₂_associator_of_pentagon
    (mF : A₀ ⥤ A₁) (mG : A₁ ⥤ A₂) (mH : A₂ ⥤ A₃)
    (mFG : A₀ ⥤ A₂) (mGH : A₁ ⥤ A₃) (mFGH : A₀ ⥤ A₃)
    (cFG : mF ⋙ mG ≅ mFG) (cGH : mG ⋙ mH ≅ mGH)
    (c₁ : mF ⋙ mGH ≅ mFGH) (c₂ : mFG ⋙ mH ≅ mFGH)
    (pent : Functor.isoWhiskerLeft mF cGH ≪≫ c₁ =
      (Functor.associator mF mG mH).symm ≪≫ Functor.isoWhiskerRight cFG mH ≪≫ c₂) :
    (Cat.Hom.isoMk c₂.symm).hom ≫
        Bicategory.whiskerRight (Cat.Hom.isoMk cFG.symm).hom (Functor.toCatHom mH) ≫
          (Bicategory.associator (Functor.toCatHom mF) (Functor.toCatHom mG)
            (Functor.toCatHom mH)).hom ≫
            Bicategory.whiskerLeft (Functor.toCatHom mF) (Cat.Hom.isoMk cGH.symm).inv ≫
              (Cat.Hom.isoMk c₁.symm).inv = 𝟙 (Functor.toCatHom mFGH) := by
  apply Cat.Hom₂.ext
  have h := congrArg Iso.hom pent
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] at h
  simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv, Iso.symm_hom, Iso.symm_inv,
    Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans, Cat.Hom.toNatTrans_comp,
    NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_id, Functor.toCatHom_toFunctor]
  have hassoc : (Bicategory.associator (Functor.toCatHom mF) (Functor.toCatHom mG)
      (Functor.toCatHom mH)).hom.toNatTrans = (Functor.associator mF mG mH).hom := rfl
  rw [hassoc, h, Iso.hom_inv_id_assoc, ← Functor.isoWhiskerRight_inv,
    ← Functor.isoWhiskerRight_hom, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- The `2`-morphism of `Cat` induced by a comparison `cC` that becomes `w` after composing with
`eqToIso hFE` is, once inverted, a retraction of `w` up to `eqToHom`. -/
private lemma isoMk_symm_hom_comp_isoMk_hom {mE mFE mF : A₀ ⥤ A₁} (cC : mE ≅ mFE)
    (hFE : mFE = mF) (w : mE ≅ mF) (hu : cC ≪≫ eqToIso hFE = w) :
    (Cat.Hom.isoMk cC.symm).hom ≫ (Cat.Hom.isoMk w).hom =
      eqToHom (congrArg Functor.toCatHom hFE) := by
  subst hFE hu
  rw [eqToIso_refl, Iso.trans_refl, eqToHom_refl]
  exact (Cat.Hom.isoMk cC).inv_hom_id

/-- **The left unit condition of `CategoryTheory.LocallyDiscrete.mkPseudofunctor` from the unit
coherence of the comparison isomorphisms.**

The functor `mFE` attached to the composite and the equation `hFE` identifying it with `mF` are
parameters, so that the condition is discharged without the elaborator ever having to see the two
as the same functor. -/
lemma map₂_left_unitor_of_unit (mE : A₀ ⥤ A₀) (mF mFE : A₀ ⥤ A₁)
    (cE : mE ≅ 𝟭 A₀) (cC : mE ⋙ mF ≅ mFE) (hFE : mFE = mF)
    (hu : cC ≪≫ eqToIso hFE = Functor.isoWhiskerRight cE mF ≪≫ Functor.leftUnitor mF) :
    (Cat.Hom.isoMk cC.symm).hom ≫
        Bicategory.whiskerRight (Cat.Hom.isoMk cE).hom (Functor.toCatHom mF) ≫
          (Bicategory.leftUnitor (Functor.toCatHom mF)).hom =
      eqToHom (congrArg Functor.toCatHom hFE) := by
  exact isoMk_symm_hom_comp_isoMk_hom cC hFE _ hu

/-- **The right unit condition of `CategoryTheory.LocallyDiscrete.mkPseudofunctor` from the unit
coherence of the comparison isomorphisms.**

The functor `mFE` attached to the composite and the equation `hFE` identifying it with `mF` are
parameters, for the reason recorded at
`CategoryTheory.Cat.map₂_left_unitor_of_unit`. -/
lemma map₂_right_unitor_of_unit (mF mFE : A₀ ⥤ A₁) (mE : A₁ ⥤ A₁)
    (cE : mE ≅ 𝟭 A₁) (cC : mF ⋙ mE ≅ mFE) (hFE : mFE = mF)
    (hu : cC ≪≫ eqToIso hFE = Functor.isoWhiskerLeft mF cE ≪≫ Functor.rightUnitor mF) :
    (Cat.Hom.isoMk cC.symm).hom ≫
        Bicategory.whiskerLeft (Functor.toCatHom mF) (Cat.Hom.isoMk cE).hom ≫
          (Bicategory.rightUnitor (Functor.toCatHom mF)).hom =
      eqToHom (congrArg Functor.toCatHom hFE) := by
  exact isoMk_symm_hom_comp_isoMk_hom cC hFE _ hu

end CategoryTheory.Cat

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

omit [Fact p.Prime] in
/-- **Every object of the big h category over `S` is in characteristic `p`** when `S` is: it
comes with a morphism to `S`, and a scheme over a scheme in characteristic `p` is in
characteristic `p`. -/
lemma isInCharacteristic_bigHOver (U : BigHOver B S hS) :
    IsInCharacteristic ((BigHOver.toScheme B S hS).obj U) p :=
  isInCharacteristic_of_hom (B.inclusion.map U.hom) p hpS

/-- The sheaf of rings `colim_F 𝒪_U` attached to an object of the big h category over `S`. -/
abbrev bigHFrobeniusColimitRingSheaf (U : BigHOver B S hS) :
    Sheaf (Opens.grothendieckTopology (((BigHOver.toScheme B S hS).obj U) : TopCat))
      RingCat.{u} :=
  frobeniusColimitRingSheaf ((BigHOver.toScheme B S hS).obj U) p
    (isInCharacteristic_bigHOver B S hS p hpS U)

/-- The canonical morphism `colim_F 𝒪_V ⟶ (f.unop)_*(colim_F 𝒪_U)` attached to an arrow
`f : V ⟶ U` of the *opposite* of the big h category over `S`. -/
abbrev bigHFrobeniusColimitHom {V U : (BigHOver B S hS)ᵒᵖ} (f : V ⟶ U) :
    bigHFrobeniusColimitRingSheaf B S hS p hpS V.unop ⟶
      (((BigHOver.toScheme B S hS).map f.unop).ringSheafPushforward).obj
        (bigHFrobeniusColimitRingSheaf B S hS p hpS U.unop) :=
  frobeniusColimitStructureSheafHom p ((BigHOver.toScheme B S hS).map f.unop)
    (isInCharacteristic_bigHOver B S hS p hpS U.unop)
    (isInCharacteristic_bigHOver B S hS p hpS V.unop)

/-- The transition functor attached to an arrow of the opposite of the big h category over `S`:
extension of scalars along `AlgebraicGeometry.bigHFrobeniusColimitHom`. -/
abbrev bigHFrobeniusColimitPullback {V U : (BigHOver B S hS)ᵒᵖ} (f : V ⟶ U) :
    _root_.SheafOfModules.{u} (bigHFrobeniusColimitRingSheaf B S hS p hpS V.unop) ⥤
      _root_.SheafOfModules.{u} (bigHFrobeniusColimitRingSheaf B S hS p hpS U.unop) :=
  _root_.SheafOfModules.pullback.{u} (bigHFrobeniusColimitHom B S hS p hpS f)

/-- The composition comparison of the transition functors, with the morphism attached to the
composite arrow spelled out, so that it is the one `map (f ≫ g)` of the pseudofunctor uses. -/
abbrev bigHFrobeniusColimitPullbackComp {W V U : (BigHOver B S hS)ᵒᵖ} (f : W ⟶ V) (g : V ⟶ U) :
    bigHFrobeniusColimitPullback B S hS p hpS f ⋙
        bigHFrobeniusColimitPullback B S hS p hpS g ≅
      bigHFrobeniusColimitPullback B S hS p hpS (f ≫ g) :=
  frobeniusColimitPullbackCompOfEq p ((BigHOver.toScheme B S hS).map g.unop)
    ((BigHOver.toScheme B S hS).map f.unop)
    (isInCharacteristic_bigHOver B S hS p hpS U.unop)
    (isInCharacteristic_bigHOver B S hS p hpS V.unop)
    (isInCharacteristic_bigHOver B S hS p hpS W.unop)
    (bigHFrobeniusColimitHom B S hS p hpS f) (bigHFrobeniusColimitHom B S hS p hpS g)
    (bigHFrobeniusColimitHom B S hS p hpS (f ≫ g))
    (frobeniusColimitStructureSheafHom_comp p ((BigHOver.toScheme B S hS).map g.unop)
      ((BigHOver.toScheme B S hS).map f.unop)
      (isInCharacteristic_bigHOver B S hS p hpS U.unop)
      (isInCharacteristic_bigHOver B S hS p hpS V.unop)
      (isInCharacteristic_bigHOver B S hS p hpS W.unop))

/-- The identity comparison of the transition functors. -/
abbrev bigHFrobeniusColimitPullbackId (U : (BigHOver B S hS)ᵒᵖ) :
    bigHFrobeniusColimitPullback B S hS p hpS (𝟙 U) ≅ 𝟭 _ :=
  frobeniusColimitPullbackIdOfEq ((BigHOver.toScheme B S hS).obj U.unop) p
    (isInCharacteristic_bigHOver B S hS p hpS U.unop)
    (bigHFrobeniusColimitHom B S hS p hpS (𝟙 U))
    (frobeniusColimitStructureSheafHom_id ((BigHOver.toScheme B S hS).obj U.unop) p
      (isInCharacteristic_bigHOver B S hS p hpS U.unop))

/-! ### The three coherences of the transition functors over the big h site -/

/-- **The associativity pentagon of the transition functors over the big h site.** The two routes
from the triple composite of transition functors to the transition functor of the triple
composite arrow agree. This is
`AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_assoc` read at the canonical morphisms. -/
lemma bigHFrobeniusColimitPullbackComp_assoc {b₀ b₁ b₂ b₃ : (BigHOver B S hS)ᵒᵖ}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    Functor.isoWhiskerLeft (bigHFrobeniusColimitPullback B S hS p hpS f)
          (bigHFrobeniusColimitPullbackComp B S hS p hpS g h) ≪≫
        bigHFrobeniusColimitPullbackComp B S hS p hpS f (g ≫ h) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (bigHFrobeniusColimitPullbackComp B S hS p hpS f g)
            (bigHFrobeniusColimitPullback B S hS p hpS h) ≪≫
          bigHFrobeniusColimitPullbackComp B S hS p hpS (f ≫ g) h :=
  frobeniusColimitPullbackCompOfEq_assoc p
    ((BigHOver.toScheme B S hS).map h.unop) ((BigHOver.toScheme B S hS).map g.unop)
    ((BigHOver.toScheme B S hS).map f.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₃.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₂.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₁.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₀.unop)
    (bigHFrobeniusColimitHom B S hS p hpS f) (bigHFrobeniusColimitHom B S hS p hpS g)
    (bigHFrobeniusColimitHom B S hS p hpS h)
    (bigHFrobeniusColimitHom B S hS p hpS (f ≫ g))
    (frobeniusColimitStructureSheafHom_comp p
      ((BigHOver.toScheme B S hS).map g.unop) ((BigHOver.toScheme B S hS).map f.unop) _ _ _)
    (bigHFrobeniusColimitHom B S hS p hpS (g ≫ h))
    (frobeniusColimitStructureSheafHom_comp p
      ((BigHOver.toScheme B S hS).map h.unop) ((BigHOver.toScheme B S hS).map g.unop) _ _ _)
    (bigHFrobeniusColimitHom B S hS p hpS (f ≫ g ≫ h))
    (frobeniusColimitStructureSheafHom_comp p
      ((BigHOver.toScheme B S hS).map (g ≫ h).unop)
      ((BigHOver.toScheme B S hS).map f.unop) _ _ _)
    (frobeniusColimitStructureSheafHom_comp p
      ((BigHOver.toScheme B S hS).map h.unop)
      ((BigHOver.toScheme B S hS).map (f ≫ g).unop) _ _ _)

/-- **The left unit coherence of the transition functors over the big h site.** -/
lemma bigHFrobeniusColimitPullbackId_comp {b₀ b₁ : (BigHOver B S hS)ᵒᵖ} (f : b₀ ⟶ b₁) :
    bigHFrobeniusColimitPullbackComp B S hS p hpS (𝟙 b₀) f ≪≫
        eqToIso (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
          (Category.id_comp f)) =
      Functor.isoWhiskerRight (bigHFrobeniusColimitPullbackId B S hS p hpS b₀)
          (bigHFrobeniusColimitPullback B S hS p hpS f) ≪≫
        Functor.leftUnitor _ :=
  frobeniusColimitPullbackIdOfEq_comp p ((BigHOver.toScheme B S hS).map f.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₁.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₀.unop)
    (bigHFrobeniusColimitHom B S hS p hpS (𝟙 b₀))
    (frobeniusColimitStructureSheafHom_id ((BigHOver.toScheme B S hS).obj b₀.unop) p _)
    (bigHFrobeniusColimitHom B S hS p hpS f)
    (bigHFrobeniusColimitHom B S hS p hpS (𝟙 b₀ ≫ f))
    (frobeniusColimitStructureSheafHom_comp p
      ((BigHOver.toScheme B S hS).map f.unop)
      ((BigHOver.toScheme B S hS).map (𝟙 b₀).unop) _ _ _)
    (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
      (Category.id_comp f))

/-- **The right unit coherence of the transition functors over the big h site.** -/
lemma bigHFrobeniusColimitPullbackComp_id {b₀ b₁ : (BigHOver B S hS)ᵒᵖ} (f : b₀ ⟶ b₁) :
    bigHFrobeniusColimitPullbackComp B S hS p hpS f (𝟙 b₁) ≪≫
        eqToIso (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
          (Category.comp_id f)) =
      Functor.isoWhiskerLeft (bigHFrobeniusColimitPullback B S hS p hpS f)
          (bigHFrobeniusColimitPullbackId B S hS p hpS b₁) ≪≫
        Functor.rightUnitor _ :=
  frobeniusColimitPullbackCompOfEq_id p ((BigHOver.toScheme B S hS).map f.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₁.unop)
    (isInCharacteristic_bigHOver B S hS p hpS b₀.unop)
    (bigHFrobeniusColimitHom B S hS p hpS (𝟙 b₁))
    (frobeniusColimitStructureSheafHom_id ((BigHOver.toScheme B S hS).obj b₁.unop) p _)
    (bigHFrobeniusColimitHom B S hS p hpS f)
    (bigHFrobeniusColimitHom B S hS p hpS (f ≫ 𝟙 b₁))
    (frobeniusColimitStructureSheafHom_comp p
      ((BigHOver.toScheme B S hS).map (𝟙 b₁).unop)
      ((BigHOver.toScheme B S hS).map f.unop) _ _ _)
    (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
      (Category.comp_id f))

/-- **The pseudofunctor of all Frobenius-colimit modules.** It sends an object `U` of the big h
category over `S` to the category of sheaves of `colim_F 𝒪_U`-modules and an arrow to extension
of scalars along the canonical morphism of Frobenius-colimit sheaves. -/
def frobeniusColimitModulePseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{u, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun U => Cat.of (_root_.SheafOfModules.{u}
      (bigHFrobeniusColimitRingSheaf B S hS p hpS U.unop)))
    (fun {_ _} f => Functor.toCatHom (bigHFrobeniusColimitPullback B S hS p hpS f))
    (fun U => Cat.Hom.isoMk (bigHFrobeniusColimitPullbackId B S hS p hpS U))
    (fun {_ _ _} f g => Cat.Hom.isoMk (bigHFrobeniusColimitPullbackComp B S hS p hpS f g).symm)
    (fun {_ _ _ _} f g h =>
      Cat.map₂_associator_of_pentagon _ _ _ _ _ _ _ _ _ _
        (bigHFrobeniusColimitPullbackComp_assoc B S hS p hpS f g h))
    (fun {b₀ b₁} f =>
      Cat.map₂_left_unitor_of_unit
        (bigHFrobeniusColimitPullback B S hS p hpS (𝟙 b₀))
        (bigHFrobeniusColimitPullback B S hS p hpS f)
        (bigHFrobeniusColimitPullback B S hS p hpS (𝟙 b₀ ≫ f))
        (bigHFrobeniusColimitPullbackId B S hS p hpS b₀)
        (bigHFrobeniusColimitPullbackComp B S hS p hpS (𝟙 b₀) f)
        (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
          (Category.id_comp f))
        (bigHFrobeniusColimitPullbackId_comp B S hS p hpS f))
    (fun {b₀ b₁} f =>
      Cat.map₂_right_unitor_of_unit
        (bigHFrobeniusColimitPullback B S hS p hpS f)
        (bigHFrobeniusColimitPullback B S hS p hpS (f ≫ 𝟙 b₁))
        (bigHFrobeniusColimitPullback B S hS p hpS (𝟙 b₁))
        (bigHFrobeniusColimitPullbackId B S hS p hpS b₁)
        (bigHFrobeniusColimitPullbackComp B S hS p hpS f (𝟙 b₁))
        (congrArg (fun x : b₀ ⟶ b₁ => bigHFrobeniusColimitPullback B S hS p hpS x)
          (Category.comp_id f))
        (bigHFrobeniusColimitPullbackComp_id B S hS p hpS f))

/-! ### The finite locally free sub-pseudofunctor and its Grothendieck construction -/

/-- **Being finite locally free**, as a property of the objects of the categories of
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor`. -/
def frobeniusColimitFiniteLocallyFree :
    (frobeniusColimitModulePseudofunctor B S hS p hpS).ObjectProperty where
  prop _ := fun M => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M

/-- The finite locally free property is preserved by the transition functors, which is
`AlgebraicGeometry.isFiniteLocallyFree_frobeniusColimitPullback`. -/
instance : (frobeniusColimitFiniteLocallyFree B S hS p hpS).IsClosedUnderMapObj where
  map_obj {_ _} {M} hM f :=
    isFiniteLocallyFree_frobeniusColimitPullback p
      ((BigHOver.toScheme B S hS).map f.as.unop) _ _ M hM

/-- **The pseudofunctor of Stacks Tag 0EXE.** It sends an object `U` of the big h category over
`S` to the category of finite locally free `colim_F 𝒪_U`-modules and an arrow to extension of
scalars along the canonical morphism of Frobenius-colimit sheaves. -/
def frobeniusVectorBundlePseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{u, u + 1} :=
  (frobeniusColimitFiniteLocallyFree B S hS p hpS).fullsubcategory

/-- **The category `𝒮` of Stacks Tag 0EXE**: the Grothendieck construction of the pseudofunctor
of finite locally free Frobenius-colimit modules. -/
abbrev FrobeniusVectorBundleTotal : Type (u + 1) :=
  Pseudofunctor.CoGrothendieck (frobeniusVectorBundlePseudofunctor B S hS p hpS)

/-- **The structure functor `p : 𝒮 ⟶ (Sch/S)_h` of Stacks Tag 0EXE.** -/
abbrev frobeniusVectorBundleFibration :
    FrobeniusVectorBundleTotal B S hS p hpS ⥤ BigHOver B S hS :=
  Pseudofunctor.CoGrothendieck.forget (frobeniusVectorBundlePseudofunctor B S hS p hpS)

/-- **The fibre of Stacks Tag 0EXE over `U` is the category of finite locally free
`colim_F 𝒪_U`-modules.** This is the fibre category the tag names; the equivalence is the
canonical one of the Grothendieck construction. -/
def frobeniusVectorBundleFiberEquiv (U : BigHOver B S hS) :
    (frobeniusVectorBundleFibration B S hS p hpS).Fiber U ≌
      frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj U) p
        (isInCharacteristic_bigHOver B S hS p hpS U) :=
  (Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const
    (frobeniusVectorBundlePseudofunctor B S hS p hpS) U)).asEquivalence.symm

/-- **Stacks Tag 0EXE, the "moreover" clause.** For a quasi-compact and quasi-separated object
`U` of the big h category over `S`, the fibre of Stacks Tag 0EXE over `U` is `colim_F Vect(U)`.

This is Stacks Tag 0EXB, `AlgebraicGeometry.frobeniusColimitVectEquivalence`,
transported along `AlgebraicGeometry.frobeniusVectorBundleFiberEquiv`; the content of 0EXB is
not restated. -/
def frobeniusVectorBundleFiberEquivColimitVect (U : BigHOver B S hS)
    [CompactSpace ((BigHOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj U)] :
    (frobeniusVectorBundleFibration B S hS p hpS).Fiber U ≌
      frobeniusColimitVectModel ((BigHOver.toScheme B S hS).obj U) p
        (isInCharacteristic_bigHOver B S hS p hpS U) :=
  (frobeniusVectorBundleFiberEquiv B S hS p hpS U).trans
    (frobeniusColimitVectEquivalence ((BigHOver.toScheme B S hS).obj U) p
      (isInCharacteristic_bigHOver B S hS p hpS U)).symm

end AlgebraicGeometry

end
