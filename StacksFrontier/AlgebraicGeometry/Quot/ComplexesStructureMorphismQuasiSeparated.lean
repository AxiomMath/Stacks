module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerIsomLimit
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesRelativeDiagonalQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# `Complexes_{X/B} ⟶ B` is quasi-separated, given algebraicity

Let `f : X ⟶ B` be a proper, flat, finitely presented morphism of algebraic spaces over a scheme
`S`, and suppose `Complexes_{X/B}` is an algebraic stack. Assuming that `Isom(E, E')` is an
algebraic space of finite presentation over `T` for any two objects `(T, E)`, `(T, E')` of
`Complexes_{X/B}` over one test scheme (the hypothesis `hIsom`), the structure morphism
`AlgebraicGeometry.Space.ComplexesSituation.complexesStructureMorphism` of `Complexes_{X/B}` over
`B` is quasi-separated: its diagonal is quasi-compact and quasi-separated.

For a fully faithful functor `F : 𝒳' ⥤ 𝒳` strictly over the base into a category fibred in
groupoids, the presheaves `Mor(x, y)` and `Isom(x, y)` of `𝒳'` are identified with those of their
images in `𝒳`, up to universe lifts.

## Main definitions

* `AlgebraicGeometry.Stack.fiberImageOfComp`: the image of an object of a fibre under a functor
  strictly over the base.
* `AlgebraicGeometry.Stack.imageLiftSystem`: the images of the chosen cartesian lifts.
* `AlgebraicGeometry.Stack.morPresheafEquivOfFullyFaithful`: the sections of `Mor(x, y)` are
  those of `Mor(F x, F y)`.
* `AlgebraicGeometry.Stack.morPresheafULiftIsoOfFullyFaithful` and
  `AlgebraicGeometry.Stack.isomPresheafULiftIsoOfFullyFaithful`: the presheaves `Mor(x, y)` and
  `Isom(x, y)` are preserved by a fully faithful functor strictly over the base, up to universe
  lifts.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.exists_isomPresheaf_qcqs_smallModel_of_isom`: the
  isomorphism sheaves of the small model over one point of `B` are quasi-compact and
  quasi-separated, granted `hIsom`.
* `AlgebraicGeometry.Space.ComplexesSituation.isQuasiSeparated_complexesStructureMorphism_of_isom`:
  the structure morphism `Complexes_{X/B} ⟶ B` is quasi-separated, granted `hIsom`.

## References

* [Stacks Project, Tag 0DPX](https://stacks.math.columbia.edu/tag/0DPX)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u w v₁ v₂ v₃ u₁ u₂ u₃

namespace AlgebraicGeometry.Stack

section FullyFaithful

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒳' : Type u₃} [Category.{v₃} 𝒳'] {p : 𝒳 ⥤ 𝒮} {p' : 𝒳' ⥤ 𝒮} (F : 𝒳' ⥤ 𝒳)
  (hF : F ⋙ p = p') {U : 𝒮}

/-- The image of an object of the fibre of `p'` over `U` under a functor `F` with
`F ⋙ p = p'`, as an object of the fibre of `p` over `U`. -/
abbrev fiberImageOfComp (x : p'.Fiber U) : p.Fiber U :=
  ⟨F.obj x.1, (Functor.congr_obj hF x.1).trans x.2⟩

/-- **The images of the chosen cartesian lifts.** For a functor `F` with `F ⋙ p = p'` into a
category fibred in groupoids, the images under `F` of the chosen cartesian lifts of `x` form a
system of cartesian lifts of the image of `x`. -/
def imageLiftSystem [p'.IsFibered] (hp : p.IsFiberedInGroupoids) (x : p'.Fiber U) :
    Functor.CartesianLiftSystem p (fiberImageOfComp F hF x) where
  obj f := F.obj (Functor.pullbackFiber p' x f.hom).1
  hom f := F.map (Functor.IsPreFibered.pullbackMap x.2 f.hom)
  isStronglyCartesian f :=
    haveI := (isHomLift_map_iff_of_comp_eq hF f.hom
      (Functor.IsPreFibered.pullbackMap x.2 f.hom)).2 inferInstance
    hp.isStronglyCartesian_homLift _ _
  trans h := F.map (Functor.pullbackFiberMap p' x h)
  trans_isHomLift h := (isHomLift_map_iff_of_comp_eq hF _ _).2 inferInstance
  trans_hom h := by rw [← F.map_comp, Functor.pullbackFiberMap_fac]

variable [F.Full] [F.Faithful] [p'.IsFibered] [p.IsFibered] (hp : p.IsFiberedInGroupoids)

/-- **The sections of `Mor(x, y)` are those of `Mor(F x, F y)`**, for a fully faithful functor `F`
with `F ⋙ p = p'` into a category fibred in groupoids: both are the morphisms out of the chosen
lift of `x` along `f` into `y` lying over `f`, read in `𝒳'` and through `F` in `𝒳`. -/
def morPresheafEquivOfFullyFaithful (x y : p'.Fiber U) (f : Over U) :
    (Functor.pullbackFiber p' x f.hom ⟶ Functor.pullbackFiber p' y f.hom) ≃
      (Functor.pullbackFiber p (fiberImageOfComp F hF x) f.hom ⟶
        Functor.pullbackFiber p (fiberImageOfComp F hF y) f.hom) :=
  ((C1590Private.chosenLiftSystem p' x).morPresheafEquiv y f).trans
    ((Equiv.subtypeEquiv (Functor.FullyFaithful.ofFullyFaithful F).homEquiv
      (fun φ => (isHomLift_map_iff_of_comp_eq hF f.hom φ).symm)).trans
      ((imageLiftSystem F hF hp x).morPresheafEquiv (fiberImageOfComp F hF y) f).symm)

/-- The morphism out of the image of the chosen lift attached to the image of a section is the
image of the morphism attached to the section. -/
theorem morPresheafEquiv_morPresheafEquivOfFullyFaithful (x y : p'.Fiber U) (f : Over U)
    (m : Functor.pullbackFiber p' x f.hom ⟶ Functor.pullbackFiber p' y f.hom) :
    ((imageLiftSystem F hF hp x).morPresheafEquiv (fiberImageOfComp F hF y) f
        (morPresheafEquivOfFullyFaithful F hF hp x y f m)).1 =
      F.map ((C1590Private.chosenLiftSystem p' x).morPresheafEquiv y f m).1 :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- `AlgebraicGeometry.Stack.morPresheafEquivOfFullyFaithful` commutes with the restriction maps
of `Mor(x, y)` and `Mor(F x, F y)`. -/
theorem morPresheafEquivOfFullyFaithful_morRestrict (x y : p'.Fiber U) {f₁ f₂ : Over U}
    (h : f₁ ⟶ f₂)
    (m : Functor.pullbackFiber p' x f₂.hom ⟶ Functor.pullbackFiber p' y f₂.hom) :
    morPresheafEquivOfFullyFaithful F hF hp x y f₁ (Functor.morRestrict p' x y h m) =
      Functor.morRestrict p _ _ h (morPresheafEquivOfFullyFaithful F hF hp x y f₂ m) := by
  apply ((imageLiftSystem F hF hp x).morPresheafEquiv (fiberImageOfComp F hF y) f₁).injective
  apply Subtype.ext
  rw [Functor.CartesianLiftSystem.morPresheafEquiv_morRestrict,
    morPresheafEquiv_morPresheafEquivOfFullyFaithful,
    morPresheafEquiv_morPresheafEquivOfFullyFaithful,
    Functor.CartesianLiftSystem.morPresheafEquiv_morRestrict, F.map_comp]
  rfl

/-- **`Mor(x, y)` is preserved by a fully faithful functor strictly over the base** into a
category fibred in groupoids, up to universe lifts. -/
def morPresheafULiftIsoOfFullyFaithful (x y : p'.Fiber U) :
    Functor.morPresheaf p' x y ⋙ uliftFunctor.{v₂} ≅
      Functor.morPresheaf p (fiberImageOfComp F hF x) (fiberImageOfComp F hF y) ⋙
        uliftFunctor.{v₃} :=
  NatIso.ofComponents
    (fun f => Equiv.toIso (Equiv.ulift.trans
      ((morPresheafEquivOfFullyFaithful F hF hp x y f.unop).trans Equiv.ulift.symm)))
    (fun {f₂ f₁} h => by
      ext ⟨m⟩
      exact congrArg ULift.up (morPresheafEquivOfFullyFaithful_morRestrict F hF hp x y h.unop m))

/-- **`Isom(x, y)` is preserved by a fully faithful functor strictly over the base** between
categories fibred in groupoids, up to universe lifts: the isomorphism presheaf of `x` and `y`
is that of their images. -/
def isomPresheafULiftIsoOfFullyFaithful (hp' : p'.IsFiberedInGroupoids) (x y : p'.Fiber U) :
    p'.isomPresheaf x y ⋙ uliftFunctor.{v₂} ≅
      p.isomPresheaf (fiberImageOfComp F hF x) (fiberImageOfComp F hF y) ⋙ uliftFunctor.{v₃} :=
  Functor.isoWhiskerRight (isomPresheafIsoMorPresheaf p' hp' x y) _ ≪≫
    morPresheafULiftIsoOfFullyFaithful F hF hp x y ≪≫
    Functor.isoWhiskerRight (isomPresheafIsoMorPresheaf p hp _ _).symm _

end FullyFaithful

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory

/-- **The isomorphism sheaves of the small model of `Complexes_{X/B}` over one point of `B` are
quasi-compact and quasi-separated**, granted that `Isom(E, E')` is an algebraic space of finite
presentation over `T` for two objects `(T, E)`, `(T, E')` over one test scheme: for two objects
`x`, `x'` over `U` whose images in `B` are identified over `𝟙 U`, `Isom(x, x')` is, up to
universe lifts, an algebraic space over `U` which is quasi-compact and quasi-separated. -/
theorem exists_isomPresheaf_qcqs_smallModel_of_isom (D : ComplexesSituation B S hS)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (complexesBasedCategory D))
    (hIsom : ∀ (A : ComplexesObject D) (E' : derivedModules B S hS (D.space A.T)),
      D.IsRelativelyPerfect A.T E' → D.HasNoNegativeFibreExt A.T E' →
      IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
        (relativeDerivedIsomFunctor (D.projection A.T) A.E E')) :
    letI : (complexesAlgebraicStack D h).val.val.p.IsFibered :=
      (complexesAlgebraicStack D h).val.isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x x' : (complexesAlgebraicStack D h).val.val.p.Fiber U),
      (∃ φ : (complexesStructureMorphism D h).hom.hom.obj x.1 ⟶
          (complexesStructureMorphism D h).hom.hom.obj x'.1,
        (baseAlgebraicStack.{u, w} D.Y).val.val.p.IsHomLift (𝟙 U) φ) →
      ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (G ⋙ uliftFunctor.{u, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙
            (complexesAlgebraicStack D h).val.val.p.isomPresheaf x x') ⋙ uliftFunctor.{u, u}) ∧
        quasiCompactQuasiSeparated B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)) := by
  let : (complexesAlgebraicStack D h).val.val.p.IsFibered :=
    (complexesAlgebraicStack D h).val.isFiberedInGroupoids.isFibered
  let : (complexesCFG D).val.p.IsFibered := (complexesCFG D).isFiberedInGroupoids.isFibered
  rintro U x x' ⟨φ, hφ⟩
  let E := shrinkHomsComparison (complexesCFG D) h
  let Gc := testSchemesToElementsComparison D.Y
  have := Gc.full
  have := Gc.faithful
  have := E.full
  have := E.faithful
  let ψ : (complexesToBase D).obj (E.F.obj x.1) ⟶ (complexesToBase D).obj (E.F.obj x'.1) :=
    Gc.F.preimage (φ : Gc.F.obj ((complexesToBase D).obj (E.F.obj x.1)) ⟶
      Gc.F.obj ((complexesToBase D).obj (E.F.obj x'.1)))
  have hm : Gc.F.map ψ = φ := Gc.F.map_preimage _
  have hψ : (baseCFG D.Y).val.p.IsHomLift (𝟙 U) ψ :=
    (Gc.isHomLift_map_iff (𝟙 U) ψ).1 (cast (congrArg (fun k =>
      (Stack.fibredCategory B S hS D.Y.obj).val.p.IsHomLift (𝟙 U) k) hm.symm) hφ)
  obtain ⟨G, hG, ⟨e⟩, hP⟩ := exists_isomPresheaf_qcqs_of_isom D hIsom U
    (Stack.fiberImageOfComp E.F E.w x) (Stack.fiberImageOfComp E.F E.w x') ⟨ψ, hψ⟩
  let t := Stack.isomPresheafULiftIsoOfFullyFaithful E.F E.w
    (complexesCFG D).isFiberedInGroupoids (complexesAlgebraicStack D h).val.isFiberedInGroupoids
    x x'
  let e' : G ⋙ uliftFunctor.{u + 1, u} ≅ ((Over.iteratedSliceBackward U).op ⋙
      (complexesAlgebraicStack D h).val.val.p.isomPresheaf x x') ⋙ uliftFunctor.{u + 1, u} :=
    e ≪≫ Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ t.symm ≪≫
      (Functor.associator _ _ _).symm
  let e'' := ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight
    _).preimageIso e'
  exact ⟨G, hG, ⟨Functor.isoWhiskerRight e'' _⟩, hP⟩

/-- **`Complexes_{X/B} ⟶ B` is quasi-separated, given algebraicity**, granted that `Isom(E, E')`
is an algebraic space of finite presentation over `T` for any two objects `(T, E)`, `(T, E')` of
`Complexes_{X/B}` over one test scheme `T ⟶ B`. -/
theorem isQuasiSeparated_complexesStructureMorphism_of_isom (D : ComplexesSituation B S hS)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (complexesBasedCategory D))
    (hIsom : ∀ (A : ComplexesObject D) (E' : derivedModules B S hS (D.space A.T)),
      D.IsRelativelyPerfect A.T E' → D.HasNoNegativeFibreExt A.T E' →
      IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
        (relativeDerivedIsomFunctor (D.projection A.T) A.E E')) :
    Stack.AlgebraicStacks.IsQuasiSeparated B S hS (complexesStructureMorphism D h) := by
  have : (baseAlgebraicStack.{u, w} D.Y).val.val.p.Faithful :=
    Stack.faithful_fibredCategory_projection D.Y.obj
  obtain ⟨-, hP⟩ := Stack.exists_isRepresentable_and_prop_relativeDiagonal_of_faithful B S hS
    (complexesAlgebraicStack D h).val (baseAlgebraicStack.{u, w} D.Y).val
    (complexesStructureMorphism D h).hom.hom (quasiCompactQuasiSeparated B S hS)
    (exists_isomPresheaf_qcqs_smallModel_of_isom D h hIsom)
  exact (Stack.AlgebraicStacks.isQuasiSeparated_iff_forall B S hS _).2 hP

end AlgebraicGeometry.Space.ComplexesSituation

end
