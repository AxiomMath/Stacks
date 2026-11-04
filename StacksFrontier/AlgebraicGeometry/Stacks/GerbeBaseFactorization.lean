module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeIsoClasses
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoClassSection

/-!
# A gerbe over an algebraic space is universal for 1-morphisms to algebraic spaces

Let `g : 𝒲 ⟶ V` make an algebraic stack `𝒲` a gerbe over an algebraic space `V`. Every
1-morphism `h : 𝒲 ⟶ Y` to an algebraic space factors, up to 2-isomorphism, as `g` followed by a
morphism of algebraic spaces `V ⟶ Y`. This is the factorization `𝒱 ⟶ V ⟶ Y` used in the proof of
Chow's lemma for algebraic stacks (Stacks 0CQ8), which the source reads off the construction of
Stacks 06QD: `V` is the sheafification of the presheaf of isomorphism classes of `𝒲`.

## Main results

In the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`:

* `exists_isGerbeOver_algebraicSpaceStack`: a gerbe is a gerbe over the algebraic stack of an
  algebraic space.
* `exists_twoIso_comp_algebraicSpaceStackMap_of_isGerbeOver`: the factorization of a
  1-morphism to an algebraic space through a gerbe over an algebraic space.

## Implementation notes

The map on isomorphism classes induced by a gerbe is locally bijective
(`CategoryTheory.IsGerbeOver.isLocallyInjective_isoClassMap`,
`CategoryTheory.IsGerbeOver.isLocallySurjective_isoClassMap`), so a map from the isomorphism
classes of `𝒲` to the sheaf `Y` factors through the sheaf `V`. The factorization is a morphism of
presheaves `V ⟶ Y` because the isomorphism classes of the algebraic stack of an algebraic space are
its sections (`CategoryTheory.PresheafOfCategories.isoClassPresheafIsoOfEquivalenceOver`), and the
2-isomorphism is Stacks 04SC (1) for the target, which is fibred in setoids.

## References

* [Stacks Project, Tag 06QD](https://stacks.math.columbia.edu/tag/06QD)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A gerbe is a gerbe over the algebraic stack of an algebraic space.** If an algebraic stack
`𝒲` is a gerbe (Stacks 06QC), there are an algebraic space `V` and a 1-morphism
`𝒲 ⟶ V` making `𝒲` a gerbe over `V`: compose the given gerbe `𝒲 ⟶ 𝒴` with the equivalence of
`𝒴` with the category of elements of the algebraic space representing it, which is a gerbe by
Stacks 06P0. -/
theorem exists_isGerbeOver_algebraicSpaceStack {𝒲 : AlgebraicStacks.{u, w} B S hS}
    (h𝒲 : IsGerbe B S hS 𝒲) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
      (g : 𝒲 ⟶ algebraicSpaceStack.{u, w} B S hS V hV), IsGerbeOver B S hS g := by
  obtain ⟨𝒴, ⟨V, hV, ⟨E⟩⟩, g, hg⟩ := h𝒲
  let F : 𝒲.val.val ⥤ᵇ (algebraicSpaceStack.{u, w} B S hS V hV).val.val :=
    BasedFunctor.comp g.hom.hom ⟨E.hom.functor, E.hom.w⟩
  refine ⟨V, hV, Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom F), ?_⟩
  show CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS)
    (algebraicSpaceStack.{u, w} B S hS V hV).val.val.p
    (CatFiberedInGroupoids.homFunctor g.hom ⋙ E.hom.functor)
  refine CategoryTheory.IsGerbeOver.comp ?_
    (CategoryTheory.IsGerbeOver.of_equivalenceOver
      (algebraicSpaceStack.{u, w} B S hS V hV).val.isFiberedInGroupoids E)
  exact (congrArg (fun q => CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) q
    (CatFiberedInGroupoids.homFunctor g.hom)) E.hom.w).mpr hg

/-- The section named by the image of an object under the 1-morphism of algebraic stacks induced
by `φ : V ⟶ Y` is the image under `φ` of the section the object names. -/
theorem sectionOfObj_algebraicSpaceStackMap {V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hY : IsAlgebraicSpace B S hS Y) (φ : V ⟶ Y)
    (z : (algebraicSpaceStack.{u, w} B S hS V hV).val.val.obj) {W : BigFppfOver B S hS}
    (hz : (algebraicSpaceStack.{u, w} B S hS V hV).val.val.p.obj z = W) :
    PresheafOfCategories.sectionOfObj (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS Y hY).val.val.p)
        ((CatFiberedInGroupoids.homFunctor
          (algebraicSpaceStackMap.{u, w} B S hS hV hY φ).hom).obj z) hz =
      φ.app (op W) (PresheafOfCategories.sectionOfObj (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS V hV).val.val.p) z hz) := by
  subst hz
  rfl

/-- **Stacks 04SC (1) for an algebraic space.** Two 1-morphisms to an algebraic space are
2-isomorphic as soon as they name the same section at every object. -/
theorem nonempty_iso_of_forall_sectionOfObj_eq {𝒲 : AlgebraicStacks.{u, w} B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (k h : 𝒲 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hkh : ∀ x : 𝒲.val.val.obj,
      PresheafOfCategories.sectionOfObj (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS Y hY).val.val.p)
          ((CatFiberedInGroupoids.homFunctor k.hom).obj x)
          (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p k.hom) x) =
        PresheafOfCategories.sectionOfObj (StacksRepresentableCFG.EquivalenceOver.refl
          (algebraicSpaceStack.{u, w} B S hS Y hY).val.val.p)
          ((CatFiberedInGroupoids.homFunctor h.hom).obj x)
          (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p h.hom) x)) :
    Nonempty (k ≅ h) := by
  let p := 𝒲.val.val.p
  let qY := (algebraicSpaceStack.{u, w} B S hS Y hY).val.val.p
  have hqY : qY.IsFiberedInGroupoids := (algebraicSpaceStack.{u, w} B S hS Y hY).val.property
  let : qY.IsFibered := hqY.isFibered
  let eY : qY.isoClassPresheaf ≅ Y ⋙ uliftFunctor.{u + 1} :=
    PresheafOfCategories.isoClassPresheafIsoOfEquivalenceOver.{u, u + 1, u, u + 1} (F := Y)
      (StacksRepresentableCFG.EquivalenceOver.refl qY)
  have hvert : ∀ x : 𝒲.val.val.obj, ∃ θ : (CatFiberedInGroupoids.homFunctor k.hom).obj x ⟶
      (CatFiberedInGroupoids.homFunctor h.hom).obj x, qY.IsHomLift (𝟙 (p.obj x)) θ := by
    intro x
    have hk : qY.obj ((CatFiberedInGroupoids.homFunctor k.hom).obj x) = p.obj x :=
      Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p k.hom) x
    have hh : qY.obj ((CatFiberedInGroupoids.homFunctor h.hom).obj x) = p.obj x :=
      Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p h.hom) x
    have hcl : Functor.isoClassMk qY (Functor.Fiber.mk hk) =
        Functor.isoClassMk qY (Functor.Fiber.mk hh) := by
      apply (eY.app (op (p.obj x))).toEquiv.injective
      show ULift.up (PresheafOfCategories.sectionOfObj
          (StacksRepresentableCFG.EquivalenceOver.refl qY) _ hk) =
        ULift.up (PresheafOfCategories.sectionOfObj
          (StacksRepresentableCFG.EquivalenceOver.refl qY) _ hh)
      exact congrArg ULift.up (hkh x)
    obtain ⟨i⟩ := Functor.exists_iso_of_isoClassMk_eq hcl
    exact ⟨i.hom.1, i.hom.2⟩
  have : qY.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver
      (StacksRepresentableCFG.EquivalenceOver.refl qY)
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection Y)
  obtain ⟨e, he, -⟩ := Functor.existsUnique_twoIso_of_forall_exists_vertical_hom
    (q := qY) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p h.hom) hvert
  exact ⟨Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso e he))⟩

/-- The universe lift of an algebraic space is a sheaf for the big fppf topology. -/
private theorem isSheaf_uliftFunctor_of_isAlgebraicSpace {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (V ⋙ uliftFunctor.{u + 1}) :=
  (isSheaf_iff_isSheaf_of_type _ _).2 (Presieve.isSheaf_comp_uliftFunctor _
    ((isSheaf_iff_isSheaf_of_type _ V).1 hV.isSheaf))

/-- **A 1-morphism from a gerbe over an algebraic space to an algebraic space factors through the
gerbe.** Let `g : 𝒲 ⟶ V` make the algebraic stack `𝒲` a gerbe over the algebraic space `V` and let
`h : 𝒲 ⟶ Y` be a 1-morphism to an algebraic space. Then there is a morphism of algebraic spaces
`φ : V ⟶ Y` with `g ≫ φ` 2-isomorphic to `h`.

The map `[h]` from the isomorphism classes of `𝒲` to `Y` factors through the map `[g]` to `V`,
which is locally bijective (`g` is a gerbe), since `V` and `Y` are sheaves; the factorization is
`φ`. Then `g ≫ φ` and `h` induce the same map on isomorphism classes, so they are 2-isomorphic by
Stacks 04SC (1), the target being fibred in setoids. -/
theorem exists_twoIso_comp_algebraicSpaceStackMap_of_isGerbeOver
    {𝒲 : AlgebraicStacks.{u, w} B S hS} {V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hY : IsAlgebraicSpace B S hS Y)
    (g : 𝒲 ⟶ algebraicSpaceStack.{u, w} B S hS V hV) (hg : IsGerbeOver B S hS g)
    (h : 𝒲 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) :
    ∃ φ : V ⟶ Y, Nonempty (g ≫ algebraicSpaceStackMap.{u, w} B S hS hV hY φ ≅ h) := by
  classical
  let J := BigFppfOver.topology B S hS
  let p := 𝒲.val.val.p
  let qV := (algebraicSpaceStack.{u, w} B S hS V hV).val.val.p
  let qY := (algebraicSpaceStack.{u, w} B S hS Y hY).val.val.p
  have hqV : qV.IsFiberedInGroupoids := (algebraicSpaceStack.{u, w} B S hS V hV).val.property
  have hqY : qY.IsFiberedInGroupoids := (algebraicSpaceStack.{u, w} B S hS Y hY).val.property
  let : p.IsFibered := (CatFiberedInGroupoids.isFiberedInGroupoids 𝒲.val).isFibered
  let : qV.IsFibered := hqV.isFibered
  let : qY.IsFibered := hqY.isFibered
  let eV : qV.isoClassPresheaf ≅ V ⋙ uliftFunctor.{u + 1} :=
    PresheafOfCategories.isoClassPresheafIsoOfEquivalenceOver.{u, u + 1, u, u + 1} (F := V)
      (StacksRepresentableCFG.EquivalenceOver.refl qV)
  let eY : qY.isoClassPresheaf ≅ Y ⋙ uliftFunctor.{u + 1} :=
    PresheafOfCategories.isoClassPresheafIsoOfEquivalenceOver.{u, u + 1, u, u + 1} (F := Y)
      (StacksRepresentableCFG.EquivalenceOver.refl qY)
  let hmG := Functor.isFibredOneMorphism_of_isFiberedInGroupoids hqV
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
  let hmH := Functor.isFibredOneMorphism_of_isFiberedInGroupoids hqY
    (CatFiberedInGroupoids.homFunctor_comp_p h.hom)
  let a : p.isoClassPresheaf ⟶ V ⋙ uliftFunctor.{u + 1} := Functor.isoClassMap hmG ≫ eV.hom
  let b : p.isoClassPresheaf ⟶ Y ⋙ uliftFunctor.{u + 1} := Functor.isoClassMap hmH ≫ eY.hom
  have hlocI : Presheaf.IsLocallyInjective J a := by
    let : Presheaf.IsLocallyInjective J (Functor.isoClassMap hmG) :=
      IsGerbeOver.isLocallyInjective_isoClassMap hg hmG
    infer_instance
  have hlocS : Presheaf.IsLocallySurjective J a := by
    let : Presheaf.IsLocallySurjective J (Functor.isoClassMap hmG) :=
      IsGerbeOver.isLocallySurjective_isoClassMap hg hmG
    infer_instance
  have hVsh := isSheaf_uliftFunctor_of_isAlgebraicSpace B S hS hV
  have hYsh := isSheaf_uliftFunctor_of_isAlgebraicSpace B S hS hY
  -- the factorization of `b` through the locally bijective `a`
  let liftA := J.sheafifyLift a hVsh
  have hfacA : J.toSheafify p.isoClassPresheaf ≫ liftA = a := J.toSheafify_sheafifyLift a hVsh
  have hliftIso : IsIso liftA := by
    have hI : Presheaf.IsLocallyInjective J liftA :=
      Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J a hfacA
    have hS' : Presheaf.IsLocallySurjective J liftA :=
      Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfacA
    let Psh : Sheaf J (Type (u + 1)) :=
      ⟨J.sheafify p.isoClassPresheaf, J.sheafify_isSheaf p.isoClassPresheaf⟩
    let Qsh : Sheaf J (Type (u + 1)) := ⟨V ⋙ uliftFunctor.{u + 1}, hVsh⟩
    let liftSh : Psh ⟶ Qsh := ObjectProperty.homMk liftA
    have hIsoSh : IsIso liftSh := (Sheaf.isLocallyBijective_iff_isIso liftSh).mp ⟨hI, hS'⟩
    have hMapIso : IsIso ((sheafToPresheaf J (Type (u + 1))).map liftSh) := by
      let : IsIso liftSh := hIsoSh
      infer_instance
    exact hMapIso
  let c : V ⋙ uliftFunctor.{u + 1} ⟶ Y ⋙ uliftFunctor.{u + 1} := inv liftA ≫ J.sheafifyLift b hYsh
  have hc : a ≫ c = b := by
    simp only [c, ← hfacA, Category.assoc, IsIso.hom_inv_id_assoc, J.toSheafify_sheafifyLift]
  -- the morphism of algebraic spaces
  let φ : V ⟶ Y :=
    { app U := TypeCat.ofHom fun x => (c.app U (ULift.up x)).down
      naturality U U' k := by
        ext x
        have hn := NatTrans.naturality_apply (G := Y ⋙ uliftFunctor.{u + 1}) c k
          (show (V ⋙ uliftFunctor.{u + 1}).obj U from ULift.up x)
        exact congrArg ULift.down hn }
  -- `g ≫ φ` and `h` name the same sections
  refine ⟨φ, nonempty_iso_of_forall_sectionOfObj_eq B S hS hY _ h fun x => ?_⟩
  let cls := Functor.isoClassMk p (Functor.Fiber.mk (rfl : p.obj x = p.obj x))
  have hb : c.app (op (p.obj x)) (a.app (op (p.obj x)) cls) = b.app (op (p.obj x)) cls := by
    rw [← hc]
    rfl
  exact (sectionOfObj_algebraicSpaceStackMap.{u, w} B S hS hV hY φ _
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p g.hom) x)).trans
      (congrArg ULift.down hb)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
