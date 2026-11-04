module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackOpenCoverRestriction
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverMapCorners

/-!
# The restriction of `Complexes_{X/S}` to a scheme over `S`

Let `f : X ⟶ Y` be a situation of Stacks 0DLE over a scheme `S` whose base `Y` is the final
algebraic space, so that `Complexes_{X/Y}` is a category fibred in groupoids over the big fppf
site of `S` itself. The paragraph of the proof of Stacks 0DLN which chooses an affine open
covering `S = ⋃ U_i` uses that the restriction `Complexes_{X/Y} ×_{(Sch/S)_fppf} (Sch/U_i)_fppf`
of Section 04X4 is `Complexes` of the base change `X_{U_i} ⟶ U_i`. This file proves that
identification, in the direction the proof uses it: if `Complexes` of the base change is an
algebraic stack, so is the restriction.

The argument is 2-categorical. By Remark 0DLI
(`AlgebraicGeometry.Space.ComplexesSituation.baseChangeSquare_isTwoFibreProduct`),
`Complexes` of the base change along `g : U ⟶ Y` is the 2-fibre product
`Complexes_{X/Y} ×_{𝒮_Y} 𝒮_U`. The restriction is the 2-fibre product
`Complexes_{X/Y} ×_{(Sch/S)} (Sch/U)`, formed at a small model of `Complexes_{X/Y}`. The two
cospans are equivalent corner by corner: the small model is equivalent to `Complexes_{X/Y}`,
`𝒮_U` is the slice of the site over `U` (Yoneda), and `𝒮_Y` is the whole site `(Sch/S)`
because `Y` is final. Since a 2-fibre product over the site is invariant under equivalences of
the three corners (`CategoryTheory.TwoFibreProductOver.isEquivalence_mapCorners`), and
algebraicity is invariant under equivalence over the site (Stacks 03YQ), the claim follows.

## Main definitions

* `AlgebraicGeometry.Space.baseToTopOver`: the 1-morphism `𝒮_Y ⟶ (Sch/S)_fppf`, forgetting the
  morphism to `Y`.
* `AlgebraicGeometry.Space.overTopOverIsoOfCompForgetEq`: two functors to `(Sch/S)_fppf` which
  agree after forgetting to the site are isomorphic, by vertical isomorphisms.

## Main results

* `AlgebraicGeometry.Space.baseToTopOver_isEquivalence`: for `Y` final, `𝒮_Y ⟶ (Sch/S)_fppf` is
  an equivalence.
* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_restrictSquare_of_baseChange`:
  the restriction of a small model of `Complexes_{X/Y}` to `U` is algebraic when `Complexes` of
  the base change of `X` to `U` is.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 04X4](https://stacks.math.columbia.edu/tag/04X4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The 1-morphism `𝒮_Y ⟶ (Sch/S)_fppf`.** A test scheme `(T, T ⟶ Y)` goes to `T` with its
structure morphism to the final object `S/S` of the site; a morphism of test schemes goes to its
underlying morphism. -/
def baseToTopOver (Y : AlgebraicSpaces B S hS) :
    BaseObjects Y ⥤ Over (Stack.topOver B S hS) where
  obj A := Over.mk (Stack.homTopOver B S hS A.objDown.left)
  map m := Over.homMk m.down.left (Over.mkIdTerminal.hom_ext _ _)

/-- The 1-morphism `𝒮_Y ⟶ (Sch/S)_fppf` lies over the site. -/
theorem baseToTopOver_comp_forget (Y : AlgebraicSpaces B S hS) :
    baseToTopOver Y ⋙ Over.forget (Stack.topOver B S hS) = (baseBasedCategory Y).p :=
  rfl

/-- **For `Y` final, `𝒮_Y ⟶ (Sch/S)_fppf` is an equivalence**: a morphism from a test scheme to
the final object `Y` carries no information. -/
theorem baseToTopOver_isEquivalence {Y : AlgebraicSpaces B S hS} (hY : IsTerminal Y) :
    (baseToTopOver Y).IsEquivalence where
  faithful :=
    { map_injective := fun {_ _} {_ _} h =>
        (baseBasedCategory_faithful Y).map_injective (congrArg (fun φ => φ.left) h) }
  full :=
    { map_surjective := fun {_ _} φ =>
        ⟨ULift.up (CostructuredArrow.homMk φ.left (hY.hom_ext _ _)),
          Over.OverMorphism.ext rfl⟩ }
  essSurj :=
    { mem_essImage := fun W =>
        ⟨ULiftHom.objUp (CostructuredArrow.mk (hY.from ((schemeSpaceFunctor B S hS).obj W.left))),
          ⟨Over.isoMk (Iso.refl _) (Over.mkIdTerminal.hom_ext _ _)⟩⟩ }

/-- **Two functors to `(Sch/S)_fppf` which agree after forgetting to the site are isomorphic.**
An object of `(Sch/S)_fppf` is a scheme of the site together with its unique morphism to the
final object `S/S`, so it is determined by the scheme. -/
def overTopOverIsoOfCompForgetEq {𝒜 : Type*} [Category 𝒜]
    (H₁ H₂ : 𝒜 ⥤ Over (Stack.topOver B S hS))
    (h : H₁ ⋙ Over.forget (Stack.topOver B S hS) = H₂ ⋙ Over.forget (Stack.topOver B S hS)) :
    H₁ ≅ H₂ :=
  NatIso.ofComponents
    (fun x => Over.isoMk (eqToIso (Functor.congr_obj h x)) (Over.mkIdTerminal.hom_ext _ _))
    (fun {x y} f => by
      ext
      have hf := Functor.congr_hom h f
      simp only [Functor.comp_map, Over.forget_map] at hf
      simp [hf])

/-- The components of `AlgebraicGeometry.Space.overTopOverIsoOfCompForgetEq` lie over
identities of the site. -/
theorem overTopOverIsoOfCompForgetEq_isHomLift {𝒜 : Type*} [Category 𝒜]
    (H₁ H₂ : 𝒜 ⥤ Over (Stack.topOver B S hS))
    (h : H₁ ⋙ Over.forget (Stack.topOver B S hS) = H₂ ⋙ Over.forget (Stack.topOver B S hS))
    (x : 𝒜) :
    (Over.forget (Stack.topOver B S hS)).IsHomLift
      (𝟙 ((Over.forget (Stack.topOver B S hS)).obj (H₁.obj x)))
      ((overTopOverIsoOfCompForgetEq H₁ H₂ h).hom.app x) :=
  IsHomLift.of_fac' _ _ _ rfl (Functor.congr_obj h x).symm (by simp [overTopOverIsoOfCompForgetEq])

/-- Two composites through a middle category agree after the final projection when each factor
lies over a common base. -/
private theorem comp_forget_eq_of_w {𝒜 ℬ 𝒞 𝒯 𝒮 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    [Category 𝒯] [Category 𝒮] {F : 𝒜 ⥤ ℬ} {E : ℬ ⥤ 𝒯} {A : 𝒜 ⥤ 𝒞} {G : 𝒞 ⥤ 𝒯}
    {π : 𝒯 ⥤ 𝒮} {pa : 𝒜 ⥤ 𝒮} {pb : ℬ ⥤ 𝒮} {pc : 𝒞 ⥤ 𝒮}
    (hF : F ⋙ pb = pa) (hE : E ⋙ π = pb) (hA : A ⋙ pc = pa) (hG : G ⋙ π = pc) :
    (F ⋙ E) ⋙ π = (A ⋙ G) ⋙ π := by
  rw [Functor.assoc, Functor.assoc, hE, hG, hF, hA]

namespace ComplexesSituation

attribute [local instance] complexesCategory

/-- **The restriction of `Complexes_{X/T}` to a scheme `U` over `T` is algebraic when
`Complexes` of the base change to `U` is.** Let `D` be a situation of Stacks 0DLE over `T` whose
base `Y` is final, let `𝒴` be a small model of `Complexes_{X/Y}`, given by an equivalence over
the site, and let `g : U ⟶ Y` be the morphism from a scheme `U` over `T`. If
`Complexes_{X_U/U}` (of the base change `D.baseChange g`, read over `T`) is an algebraic stack,
then so is the restriction `𝒴 ×_{(Sch/T)_fppf} (Sch/U)_fppf`.

By Remark 0DLI the first is the 2-fibre product `Complexes_{X/Y} ×_{𝒮_Y} 𝒮_U`, and the cospan
`Complexes_{X/Y} ⟶ 𝒮_Y ⟵ 𝒮_U` is equivalent corner by corner to `𝒴 ⟶ (Sch/T) ⟵ (Sch/U)`, the
middle corner because `Y` is final. The hypothesis that `U ⟶ T` is an open immersion is not
used. -/
theorem isAlgebraicStack_restrictSquare_of_baseChange {T : Scheme.{u}} (hT : B.Contains T)
    (D : ComplexesSituation B T hT) (hY : Nonempty (IsTerminal D.Y))
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B T hT))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p (complexesBasedCategory D).p)
    (U : BigFppfOver B T hT) (_hU : AlgebraicGeometry.IsOpenImmersion (B.inclusion.map U.hom))
    (g : (schemeSpaceFunctor B T hT).obj U ⟶ D.Y)
    (halg : Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B T hT
      (complexesBasedCategory (D.baseChange g))) :
    Stack.IsAlgebraicStack.{u, z} B T hT (Stack.restrictSquare B T hT 𝒴 U).pt.val := by
  obtain ⟨hY⟩ := hY
  -- the square of Remark 0DLI, read in the 2-category of categories fibred in groupoids
  let 𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B T hT) :=
    CatFiberedInGroupoids.mk (complexesBasedCategory D) (complexesFunctor_isFiberedInGroupoids D)
  let 𝒳' : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B T hT) :=
    CatFiberedInGroupoids.mk (complexesBasedCategory (D.baseChange g))
      (complexesFunctor_isFiberedInGroupoids (D.baseChange g))
  let qC : 𝒳 ⟶ baseFibredCategory D.Y := Bicategory.InducedBicategory.mkHom (complexesToBase D)
  let P : Bicategory.TwoCommSq qC (baseFibredMap D.Y g) :=
    { pt := 𝒳'
      fst := Bicategory.InducedBicategory.mkHom (D.complexesBaseChangeMap g)
      snd := Bicategory.InducedBicategory.mkHom (complexesToBase (D.baseChange g))
      iso := Bicategory.InducedBicategory.isoMk (D.baseChangeSquare g).iso }
  have hP : Bicategory.IsTwoFibreProduct P :=
    Bicategory.isTwoFibreProduct_of_underlying (D.baseChangeSquare_isTwoFibreProduct g)
  -- so `Complexes_{X_U/U}` is equivalent to the canonical 2-fibre product over `𝒮_Y`
  have hQ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
    qC (baseFibredMap D.Y g)
  have hL := Bicategory.isEquivalence_of_isTwoFibreProduct hP hQ
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} qC
      (baseFibredMap D.Y g) P)
  have halgQ : Stack.IsAlgebraicStack.{u, z} B T hT
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} qC
        (baseFibredMap D.Y g)).pt.val :=
    (Stack.isAlgebraicStack_iff_of_isEquivalence B T hT
      (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} qC
        (baseFibredMap D.Y g) P).hom 𝒳'.property
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} qC
        (baseFibredMap D.Y g)).pt.property hL).1 halg
  -- the two cospans are equivalent corner by corner
  let ea := e.symm
  let eb := StacksRepresentableCFG.equivalenceOverOfIsEquivalence
    (baseBasedCategory_isFiberedInGroupoids ((schemeSpaceFunctor B T hT).obj U))
    (Stack.schemeFibredCategory B T hT U).property (baseToSlice (T := U)).toFunctor
    (baseToSlice (T := U)).w inferInstance
  let ec := StacksRepresentableCFG.equivalenceOverOfIsEquivalence
    (baseBasedCategory_isFiberedInGroupoids D.Y)
    (Stack.schemeFibredCategory B T hT (Stack.topOver B T hT)).property (baseToTopOver D.Y)
    (baseToTopOver_comp_forget D.Y) (baseToTopOver_isEquivalence hY)
  have hα := comp_forget_eq_of_w (complexesToBase D).w ec.hom.w ea.hom.w
    (Stack.toTopOver B T hT 𝒴).hom.w
  have hβ := comp_forget_eq_of_w (baseBasedMap g).w ec.hom.w eb.hom.w
    (Stack.schemeFibredCategoryMap B T hT (Stack.homTopOver B T hT U)).hom.w
  let α := overTopOverIsoOfCompForgetEq _ _ hα
  let β := overTopOverIsoOfCompForgetEq _ _ hβ
  have hM := TwoFibreProductOver.isEquivalence_mapCorners ea eb ec
    (Stack.toTopOver B T hT 𝒴).hom.w
    (Stack.schemeFibredCategoryMap B T hT (Stack.homTopOver B T hT U)).hom.w α β
    (overTopOverIsoOfCompForgetEq_isHomLift _ _ hα)
    (overTopOverIsoOfCompForgetEq_isHomLift _ _ hβ)
  exact Stack.isAlgebraicStack_of_equivalenceOver B T hT
    (StacksRepresentableCFG.equivalenceOverOfIsEquivalence
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} qC
        (baseFibredMap D.Y g)).pt.property
      (Stack.restrictSquare B T hT 𝒴 U).pt.property _
      (TwoFibreProductOver.mapCorners_comp_structureFunctor ..) hM) halgQ

end ComplexesSituation

end AlgebraicGeometry.Space

end
