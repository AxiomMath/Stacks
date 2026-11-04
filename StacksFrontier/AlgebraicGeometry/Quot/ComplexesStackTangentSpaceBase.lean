module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackTangentSpace
public import StacksFrontier.AlgebraicGeometry.Quot.BaseBasedCategoryElements
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineRelation
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityStack
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhEtaleSchemeSlices
public import StacksFrontier.Deformation.Artin.AlgebraicStackFiniteDimensional
public import StacksFrontier.Deformation.Artin.Versality.OpennessCounterexampleAxioms
public import StacksFrontier.Deformation.ArtinCriteria.DiagonalBaseChangeTangent
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessingerEquivalenceOver
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessingerStarEquivalenceOver
public import StacksFrontier.Deformation.Artin.RimSchlessinger.AlgebraicStackRSStar
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphismFromAlgebraicStack
public import StacksFrontier.Deformation.ArtinCriteria.TwoFibreProductFactorFiniteDimensional

/-!
# Paragraph 2 of the proof of Stacks 0DLL for `Complexes_{X/Y}`

The second paragraph of the proof of Stacks 0DLL reads: "the fibre `𝒳₀` of `𝒳 = Complexes_{X/B}`
over `Spec k ⟶ B` is the 2-fibre product `𝒳 ×_{(Sch/B)} (Sch/Spec k)`; by Lemma 07X2 we reduce to
proving that `B`, `Spec(k)` and `𝒳₀` have finite dimensional tangent spaces and infinitesimal
automorphism spaces". This file carries that reduction out for `Complexes_{X/Y}`, with the fibre
`𝒳₀` taken as a hypothesis, in the two cases where the base `Y` is a scheme locally of finite type
over `S`.

The data of the 2-fibre product are:

* `𝒴 = 𝒮_Y`, the category fibred in sets of the algebraic space `Y`
  (`AlgebraicGeometry.Space.baseBasedCategory`), and the forgetful 1-morphism
  `Φ : Complexes_{X/Y} ⟶ 𝒮_Y`, `(T, g, E) ↦ (T, g)`
  (`AlgebraicGeometry.Space.ComplexesSituation.complexesToBaseObjects`, the underlying functor
  of `AlgebraicGeometry.Space.ComplexesSituation.complexesToBase` of Remark 0DLI), which lies
  over the site on the nose;
* `𝒵 = (Sch/V)_{fppf}` for the object `V = Spec k` of the site under `x₀`, and the 1-morphism
  `Ψ : (Sch/V) ⟶ 𝒮_Y`, `(t : T ⟶ V) ↦ (T, g₀ ∘ t)`, of the point `g₀ : V ⟶ Y` of `x₀`
  (`AlgebraicGeometry.Space.schemePointToBase`);
* the object `w₀ = (x₀, id_V, id)` of `𝒲 = Complexes_{X/Y} ×_{𝒮_Y} (Sch/V)`
  (`AlgebraicGeometry.Space.ComplexesSituation.fibreBasePoint`).

The base `𝒮_Y` satisfies (RS), since it is equivalent over the site to the algebraic stack of `Y`
(Stacks 07WQ). It has no infinitesimal automorphisms, its fibres being sets. When `Y` is
isomorphic to a scheme `W` locally of finite type over `S`, its tangent spaces are those of
`(Sch/W)`, which are finite dimensional over every deformation base `Spec Λ ⟶ S` (the scheme case
of Stacks 07X1,
`Deformation.Artin.SliceTangent.finiteDimensional_artinianTangentSpace_sliceBased_anyBase`).
That covers the case `Y = S` of Stacks 0DLN, where `Y` is the final algebraic space.

For a general algebraic space `Y` locally of finite type over `S`, Stacks 07X1 handles the base
at the deformation bases of Section 07T2, the affine opens `Spec Λ ⊆ S` with `Λ → k` finite,
which is the setting of the statement of Stacks 0DLL. At other deformation bases, such as the
local rings of `S` at which Artin's criterion reads axiom [3], the library has Stacks 07X1 only
for schemes; there the reduction is stated with the tangent spaces of `𝒮_Y` as a hypothesis.

## Main results

The names below are in the namespace `AlgebraicGeometry.Space`.

* `ComplexesSituation.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_baseTangent`:
  the reduction for any algebraic space `Y`, with the tangent spaces of `𝒮_Y` over the deformation
  base as an explicit hypothesis (Stacks 07X1 at a deformation base which is not an open immersion,
  which the library lacks).
* `ComplexesSituation.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_isOpenImmersion`:
  the reduction in the setting of Section 07T2 (`Spec Λ ⊆ S` an affine open with `Λ → k` finite),
  for any `Y` locally of finite type over a locally Noetherian `S`, the base being handled by
  Stacks 07X1. This is the form of the statement of Stacks 0DLL.
* `ComplexesSituation.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_iso_scheme`:
  the vector spaces of Stacks 07WY of `Complexes_{X/Y}` at `x₀` are finite dimensional when `Y` is
  isomorphic to a scheme locally of finite type over `S`, granted the fibre `𝒲` at `w₀` and (RS)
  for `Complexes_{X/Y}` (Stacks 0DLK).
* `ComplexesSituation.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_isTerminal`:
  the case `Y = S`.
* `ComplexesSituation.finiteDimensional_tangentModuleAt_fibreBasePoint_snd`:
  the tangent spaces of the second factor `(Sch/Spec k)` of `𝒲` at `w₀`, over every deformation
  base, an input of the fibre computation.
* `ComplexesSituation.finiteDimensional_artinianTangentSpace_stalk_of_isTerminal`:
  in the case `Y = S`, the hypothesis `h0DLL` of
  `ComplexesSituation.isAlgebraicStack_of_artinCriterion`, granted the fibre at every field
  point.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
* [Stacks Project, Tag 07X2](https://stacks.math.columbia.edu/tag/07X2)
* [Stacks Project, Tag 07WY](https://stacks.math.columbia.edu/tag/07WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The base `𝒮_Y` -/

section Base

variable (Y : AlgebraicSpaces B S hS)

/-- The structure functor `(T, g) ↦ T` of `𝒮_Y`, on the objects `BaseObjects Y` themselves. It is
the structure functor of `AlgebraicGeometry.Space.baseBasedCategory`. Stating everything on
`BaseObjects Y` lets instance search find the category structures it needs. -/
abbrev baseProj : BaseObjects Y ⥤ BigFppfOver B S hS :=
  ULiftHom.down ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y

/-- `baseProj Y` is the structure functor of `𝒮_Y`. -/
theorem baseProj_eq : baseProj Y = (baseBasedCategory Y).p :=
  rfl

/-- `𝒮_Y` is fibred in groupoids. -/
theorem baseProj_isFiberedInGroupoids : (baseProj Y).IsFiberedInGroupoids :=
  baseBasedCategory_isFiberedInGroupoids Y

/-- The structure functor of `𝒮_Y` is faithful. -/
theorem baseProj_faithful : (baseProj Y).Faithful :=
  baseBasedCategory_faithful Y

/-- **`𝒮_Y` satisfies (RS).** It is equivalent over the site to the category of elements of `Y`,
the algebraic stack of the algebraic space `Y`, which satisfies (RS) by Stacks 07WQ. -/
theorem baseBasedCategory_satisfiesRS :
    SatisfiesRS B S hS (baseProj Y) (baseProj_isFiberedInGroupoids Y) :=
  satisfiesRS_of_equivalenceOver B S hS
    (Stack.algebraicSpaceStack.{u, u + 1} B S hS Y.obj Y.2).val.isFiberedInGroupoids
    (baseProj_isFiberedInGroupoids Y)
    (satisfiesRS_of_isAlgebraicStack B S hS
      (Stack.algebraicSpaceStack.{u, u + 1} B S hS Y.obj Y.2))
    (baseBasedElementsEquivalenceOver Y).symm

/-- **`𝒮_Y` satisfies (RS\*).** It is equivalent over the site to the category of elements of
`Y`, the algebraic stack of the algebraic space `Y`, which satisfies (RS\*) by Stacks 0CXP; (RS\*)
transports along the equivalence (`Deformation.Artin.satisfiesRSStar_of_equivalenceOver`). -/
theorem baseProj_satisfiesRSStar :
    SatisfiesRSStar B S hS (baseProj Y) (baseProj_isFiberedInGroupoids Y) :=
  satisfiesRSStar_of_equivalenceOver B S hS
    (Stack.fibredCategory B S hS Y.obj).isFiberedInGroupoids (baseProj_isFiberedInGroupoids Y)
    (satisfiesRSStar_of_isAlgebraicStack B S hS (Stack.fibredCategory B S hS Y.obj).val
      (Stack.isAlgebraicStack_fibredCategory.{u, u + 1} B S hS Y.obj Y.2) _)
    (baseBasedElementsEquivalenceOver Y).symm

/-- **`𝒮_Y` has no infinitesimal automorphisms.** Its structure functor is faithful, so the
fibres of each of its predeformation categories are thin, and the infinitesimal automorphisms at
any point of the special fibre vanish. -/
theorem finiteDimensional_inf_baseBasedCategory {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S) (y : BaseObjects Y)
    (hy : (baseProj Y ⋙ Over.post B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (baseProj Y ⋙ Over.post B.inclusion) y hy).projection)
    (x : (predeformationCategory iΛ (baseProj Y ⋙ Over.post B.inclusion) y
      hy).carrier)
    (P : ChosenPushforwardsAt (predeformationCategory iΛ
      (baseProj Y ⋙ Over.post B.inclusion) y hy).projection x) :
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
  let := naturalLocalizedTangentModule P hD.satisfiesRS
  have : (baseProj Y ⋙ Over.post B.inclusion).Faithful :=
    ⟨fun h => (baseProj_faithful Y).map_injective
      ((Over.post B.inclusion).map_injective h)⟩
  let Q := predeformationCategory iΛ (baseProj Y ⋙ Over.post B.inclusion) y hy
  let := Q.category
  have : Q.projection.Faithful := Q.faithful_projection
  have : Subsingleton (localizedAutomorphismFunctorTangent P) :=
    subsingleton_localizedAutomorphismFunctorTangent P
      (fun a b => subsingleton_fiber_hom_of_faithful Q.projection a b)
  infer_instance

/-- **The tangent spaces of `𝒮_Y` are finite dimensional over the deformation bases of
Section 07T2**, for `S` locally Noetherian and `Y` locally of finite type over `S`: affine opens
`Spec Λ ⊆ S` through which `Spec k ⟶ S` factors with `Λ → k` finite. This is Stacks 07X1, in the
form of Stacks 0DQW, for the algebraic stack of `Y`
(`AlgebraicGeometry.Stack.algebraicSpaceStack`), transported to `𝒮_Y` along the Yoneda
equivalence over the site `AlgebraicGeometry.Space.baseBasedElementsEquivalenceOver`. -/
theorem finiteDimensional_tangentModuleAt_baseBasedCategory_of_isOpenImmersion
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from Y.obj))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (y : BaseObjects Y)
    (hy : (baseProj Y ⋙ Over.post B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (baseProj Y ⋙ Over.post B.inclusion) y hy).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (baseProj Y ⋙ Over.post B.inclusion) y hy).projection) hD
        (FGModuleCat.of k k)) := by
  let e := baseBasedElementsEquivalenceOver Y
  let Φ : BaseObjects Y ⥤ (Stack.fibredCategory B S hS Y.obj).val.obj := baseObjectsToElements Y
  have hΦ : Φ ⋙ (Stack.fibredCategory B S hS Y.obj).val.p = baseProj Y := e.hom.w
  have : Φ.IsEquivalence := e.isEquivalence_hom_functor
  have hess : ∀ z : (Stack.fibredCategory B S hS Y.obj).val.obj,
      ∃ (x : BaseObjects Y) (f : z ≅ Φ.obj x),
        (Stack.fibredCategory B S hS Y.obj).val.p.IsHomLift
          (𝟙 ((Stack.fibredCategory B S hS Y.obj).val.p.obj z)) f.hom :=
    fun z => ⟨e.inv.functor.obj z, (e.counitIso.app z).symm, e.isHomLift_counitIso_inv_app z⟩
  have hy' := (transport_obj_eq B hS (baseProj Y) (Stack.fibredCategory B S hS Y.obj).val.p
    Φ hΦ y).trans hy
  obtain ⟨hp, hT, -⟩ := Stack.isFiniteDimensionalDeformationCategory_of_versalSituation
    { B := B, S := S, hS := hS, 𝒳 := Stack.algebraicSpaceStack.{u, u} B S hS Y.obj Y.2
      locallyFiniteType :=
        Stack.isLocallyOfFiniteType_structureMorphism_algebraicSpaceStack B S hS Y.obj Y.2 hft }
    iΛ hiΛ (Φ.obj y) hy' ⟨hfinite, hqc⟩
  let := (predeformationCategory iΛ
    ((Stack.fibredCategory B S hS Y.obj).val.p ⋙ Over.post B.inclusion) (Φ.obj y) hy').category
  have hA := Deformation.finiteDimensional_artinianTangentSpace_of_tangentSpaceArtinian
    (BasedCategory.ofFunctor (predeformationCategory iΛ
      ((Stack.fibredCategory B S hS Y.obj).val.p ⋙ Over.post B.inclusion) (Φ.obj y)
        hy').projection) hp.predeformation (tangentConditionS2 hp) hT
  exact (finiteDimensional_tangentModuleAt_iff_of_fullyFaithful B hS iΛ (baseProj Y)
    (Stack.fibredCategory B S hS Y.obj).val.p Φ hΦ
    (baseProj_isFiberedInGroupoids Y) (Stack.fibredCategory B S hS Y.obj).isFiberedInGroupoids
    hess y hy hD hp _).mpr
      ((finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hp).mp hA)

end Base

/-! ### The base `𝒮_Y` when `Y` is a scheme -/

section SchemeBase

variable {Y : AlgebraicSpaces B S hS} {W : BigFppfOver B S hS}
  (e : Y ≅ (schemeSpaceFunctor B S hS).obj W)

/-- The morphism `T ⟶ W` of the site that a test scheme `(T, g)` over `Y` names through an
isomorphism `Y ≅ W`. -/
def baseToSchemeHom (A : SchemesOver Y) : A.left ⟶ W :=
  (schemeSpaceFunctorFullyFaithful B hS).preimage (A.hom ≫ e.hom)

/-- The morphism `T ⟶ W` named by `(T, g)` is the one whose algebraic space map is `g` followed by
the isomorphism. -/
theorem schemeSpaceFunctor_map_baseToSchemeHom (A : SchemesOver Y) :
    (schemeSpaceFunctor B S hS).map (baseToSchemeHom e A) = A.hom ≫ e.hom :=
  (schemeSpaceFunctorFullyFaithful B hS).map_preimage _

/-- **`𝒮_Y` read as `(Sch/W)`**, for an isomorphism `Y ≅ W` with a scheme of the site: a test
scheme `(T, g)` over `Y` goes to the morphism `T ⟶ W` that `g` names. It lies over the site on the
nose. -/
def baseToScheme : BaseObjects Y ⥤ Over W where
  obj A := Over.mk (baseToSchemeHom e (ULiftHom.objDown.{u + 1, u + 1} A))
  map {A A'} m := Over.homMk (ULift.down m).left (by
    apply (schemeSpaceFunctorFullyFaithful B hS).map_injective
    change (schemeSpaceFunctor B S hS).map
        ((ULift.down m).left ≫ baseToSchemeHom e (ULiftHom.objDown.{u + 1, u + 1} A')) =
      (schemeSpaceFunctor B S hS).map (baseToSchemeHom e (ULiftHom.objDown.{u + 1, u + 1} A))
    rw [CategoryTheory.Functor.map_comp, schemeSpaceFunctor_map_baseToSchemeHom,
      schemeSpaceFunctor_map_baseToSchemeHom, ← Category.assoc, CostructuredArrow.w (ULift.down m)])
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `𝒮_Y ⟶ (Sch/W)` lies over the site on the nose. -/
theorem baseToScheme_comp_forget :
    baseToScheme e ⋙ Over.forget W = baseProj Y :=
  rfl

/-- The functor `𝒮_Y ⥤ (Sch/W)` is faithful. -/
instance baseToScheme_faithful : (baseToScheme e).Faithful where
  map_injective {_ _} _ _ h :=
    (baseProj_faithful Y).map_injective (congrArg (fun f => f.left) h)

/-- The functor `𝒮_Y ⥤ (Sch/W)` is full. -/
instance baseToScheme_full : (baseToScheme e).Full where
  map_surjective {A A'} h := by
    let g : (ULiftHom.objDown.{u + 1, u + 1} A).left ⟶
        (ULiftHom.objDown.{u + 1, u + 1} A').left := h.left
    have hw : g ≫ baseToSchemeHom e (ULiftHom.objDown.{u + 1, u + 1} A') =
        baseToSchemeHom e (ULiftHom.objDown.{u + 1, u + 1} A) := Over.w h
    refine ⟨ULift.up (CostructuredArrow.homMk g ((cancel_mono e.hom).1 ?_)), rfl⟩
    rw [Category.assoc,
      ← schemeSpaceFunctor_map_baseToSchemeHom e (ULiftHom.objDown.{u + 1, u + 1} A'),
      ← CategoryTheory.Functor.map_comp, hw, schemeSpaceFunctor_map_baseToSchemeHom]

/-- Every object of `(Sch/W)` is vertically isomorphic to the image of an object of `𝒮_Y`. -/
theorem exists_iso_baseToScheme_obj (V : Over W) :
    ∃ (A : BaseObjects Y) (f : V ≅ (baseToScheme e).obj A),
      (Over.forget W).IsHomLift (𝟙 ((Over.forget W).obj V)) f.hom := by
  let A : SchemesOver Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map V.hom ≫ e.inv)
  have hA : baseToSchemeHom e A = V.hom := by
    apply (schemeSpaceFunctorFullyFaithful B hS).map_injective
    rw [schemeSpaceFunctor_map_baseToSchemeHom]
    simp [A]
  let f : V ≅ (baseToScheme e).obj (ULiftHom.objUp.{u + 1, u + 1} A) :=
    Over.isoMk (Iso.refl V.left) ((Category.id_comp _).trans hA)
  exact ⟨ULiftHom.objUp.{u + 1, u + 1} A, f,
    inferInstanceAs ((Over.forget W).IsHomLift ((Over.forget W).map f.hom) f.hom)⟩

include e in
/-- **The tangent spaces of `𝒮_Y` are finite dimensional over every deformation base**, when `Y`
is isomorphic to a scheme `W` locally of finite type over `S`: `𝒮_Y` is equivalent over the site
to `(Sch/W)`, whose tangent spaces are finite dimensional over any deformation base by the
scheme case of Stacks 07X1. -/
theorem finiteDimensional_tangentModuleAt_baseBasedCategory_of_iso
    [LocallyOfFiniteType (B.inclusion.map W.hom)]
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (y : BaseObjects Y)
    (hy : (baseProj Y ⋙ Over.post B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (baseProj Y ⋙ Over.post B.inclusion) y hy).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (baseProj Y ⋙ Over.post B.inclusion) y
        hy).projection) hD (FGModuleCat.of k k)) := by
  have hy' := (transport_obj_eq B hS (baseProj Y) (Over.forget W) (baseToScheme e)
    (baseToScheme_comp_forget e) y).trans hy
  have hDW := isDeformationCategory_predeformationCategory B S hS (Over.forget W)
    (Functor.IsFiberedInGroupoids.over_forget W) (satisfiesRS_over_forget B S hS W) iΛ
    ((baseToScheme e).obj y) hy' hfinite hqc
  have hT := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hDW).mp
    (SliceTangent.finiteDimensional_artinianTangentSpace_sliceBased_anyBase hDW.predeformation
      (tangentConditionS2 hDW))
  exact (finiteDimensional_tangentModuleAt_iff_of_fullyFaithful B hS iΛ
    (baseProj Y) (Over.forget W) (baseToScheme e) (baseToScheme_comp_forget e)
    (baseProj_isFiberedInGroupoids Y) (Functor.IsFiberedInGroupoids.over_forget W)
    (exists_iso_baseToScheme_obj e) y hy hD hDW _).mpr hT

end SchemeBase

/-! ### The point `Ψ : (Sch/V) ⟶ 𝒮_Y` -/

section Point

variable (Y : AlgebraicSpaces B S hS) (V : BigFppfOver B S hS)
  (g : (schemeSpaceFunctor B S hS).obj V ⟶ Y)

/-- The structure morphism `T ⟶ V` of a scheme over `V`, as a morphism of the site over `S`. -/
abbrev overMapHom (t : BigFppfOver B V.left.1 V.left.2) : (Over.map V.hom).obj t ⟶ V :=
  Over.homMk t.hom

/-- **The 1-morphism `(Sch/V) ⟶ 𝒮_Y` of a point `g : V ⟶ Y`**: a scheme `t : T ⟶ V` over `V`
goes to the test scheme `(T, g ∘ t)` over `Y`. It lies over the site on the nose
(`AlgebraicGeometry.Space.schemePointToBase_comp`). -/
def schemePointToBase : BigFppfOver B V.left.1 V.left.2 ⥤ BaseObjects Y where
  obj t := ULiftHom.objUp.{u + 1, u + 1} (CostructuredArrow.mk
    ((schemeSpaceFunctor B S hS).map (overMapHom V t) ≫ g))
  map {t t'} f := ULift.up (CostructuredArrow.homMk ((Over.map V.hom).map f) (by
    change (schemeSpaceFunctor B S hS).map ((Over.map V.hom).map f) ≫
      (schemeSpaceFunctor B S hS).map (overMapHom V t') ≫ g =
      (schemeSpaceFunctor B S hS).map (overMapHom V t) ≫ g
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
    congr 2
    ext
    simp [Over.w f]))
  map_id t := ULift.ext _ _ (CostructuredArrow.hom_ext _ _ ((Over.map V.hom).map_id t))
  map_comp f f' := ULift.ext _ _ (CostructuredArrow.hom_ext _ _ ((Over.map V.hom).map_comp f f'))

/-- **`(Sch/V)_{fppf}` satisfies (RS\*)**, as a category over the big fppf site of `S` through
`Over.map V.hom`: it is an algebraic stack
(`AlgebraicGeometry.Stack.isAlgebraicStack_overMap`), and algebraic stacks satisfy (RS\*) by
Stacks 0CXP. -/
theorem overMap_satisfiesRSStar :
    SatisfiesRSStar B S hS (Over.map V.hom) (Functor.IsFiberedInGroupoids.over_map V.hom) :=
  satisfiesRSStar_of_isAlgebraicStack B S hS (BasedCategory.ofFunctor (Over.map V.hom))
    (Stack.isAlgebraicStack_overMap.{u, u + 1} B S hS V) _

/-- `(Sch/V) ⟶ 𝒮_Y` lies over the site on the nose. -/
theorem schemePointToBase_comp :
    schemePointToBase Y V g ⋙ baseProj Y = Over.map V.hom :=
  rfl

end Point

/-! ### The 2-fibre product for `Complexes_{X/Y}` -/

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- **The forgetful 1-morphism `Complexes_{X/Y} ⟶ 𝒮_Y`**, `(T, g, E) ↦ (T, g)`, as a functor into
`BaseObjects D.Y`: the underlying functor of the 1-morphism
`AlgebraicGeometry.Space.ComplexesSituation.complexesToBase` of Remark 0DLI, with its target read
as `BaseObjects D.Y`, so that instance search finds the category structures of the 2-fibre product
and of its predeformation categories. -/
abbrev complexesToBaseObjects :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    ComplexesObject D ⥤ BaseObjects D.Y :=
  (complexesToBase D).toFunctor

/-- `Complexes_{X/Y} ⟶ 𝒮_Y` lies over the site on the nose: it composes with the structure
functor of `𝒮_Y` to the functor `p` of Stacks 0DLE. -/
theorem complexesToBaseObjects_comp :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    complexesToBaseObjects D ⋙ baseProj D.Y = complexesFunctor D :=
  rfl

attribute [local instance] complexesCategory

/-- The 2-fibre product `𝒲 = Complexes_{X/Y} ×_{𝒮_Y} (Sch/V)` of the fibre of `Complexes_{X/Y}`
over the point `g₀ : V ⟶ Y` of an object `x₀` over `V`. -/
abbrev FibreAt (x₀ : ComplexesObject D) : Type _ :=
  TwoFibreProductOver (complexesFunctor D) (Over.map x₀.T.left.hom) (baseProj D.Y)
    (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom)

/-- The scheme `𝟙 : V ⟶ V` over `V` lies over `V`. -/
theorem overMap_obj_mk_id (V : BigFppfOver B S hS) :
    (Over.map V.hom).obj (Over.mk (𝟙 V.left)) = V := by
  show Over.mk (𝟙 V.left ≫ V.hom) = V
  rw [Category.id_comp]
  rfl

/-- The identification of `V` with the scheme `𝟙 : V ⟶ V` over `V`, followed by its structure
morphism, is the identity. -/
theorem eqToHom_comp_overMapHom_mk_id (V : BigFppfOver B S hS) :
    eqToHom (overMap_obj_mk_id V).symm ≫ overMapHom V (Over.mk (𝟙 V.left)) = 𝟙 V := by
  ext
  simp [Over.eqToHom_left]

/-- The comparison `Φ(x₀) ≅ Ψ(𝟙_V)` of the point `w₀`: the identity, read through the
identification of `(V, g₀)` with `(V, g₀ ∘ 𝟙)`. -/
def fibreBasePointIso (x₀ : ComplexesObject D) :
    (complexesToBaseObjects D).obj x₀ ≅
      (schemePointToBase D.Y x₀.T.left x₀.T.hom).obj (Over.mk (𝟙 x₀.T.left.left)) :=
  baseObjectsIsoUp D.Y (A := x₀.T) (A' := CostructuredArrow.mk
      ((schemeSpaceFunctor B S hS).map (overMapHom x₀.T.left (Over.mk (𝟙 x₀.T.left.left))) ≫
        x₀.T.hom))
    (CostructuredArrow.isoMk (eqToIso (overMap_obj_mk_id x₀.T.left).symm) (by
      change (schemeSpaceFunctor B S hS).map (eqToHom (overMap_obj_mk_id x₀.T.left).symm) ≫
        (schemeSpaceFunctor B S hS).map (overMapHom x₀.T.left (Over.mk (𝟙 x₀.T.left.left))) ≫
          x₀.T.hom = x₀.T.hom
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_comp_overMapHom_mk_id,
        CategoryTheory.Functor.map_id, Category.id_comp]))

/-- **The point `w₀ = (x₀, 𝟙_V, id)` of the fibre `𝒲`** over the point `g₀ : V ⟶ Y` of `x₀`. -/
def fibreBasePoint (x₀ : ComplexesObject D) : FibreAt D x₀ where
  base := x₀.T.left
  x := x₀
  y := Over.mk (𝟙 x₀.T.left.left)
  hx := rfl
  hy := overMap_obj_mk_id x₀.T.left
  iso := fibreBasePointIso D x₀
  vertical := by
    refine IsHomLift.of_fac' _ _ _ rfl (overMap_obj_mk_id x₀.T.left) ?_
    simp only [Category.id_comp]
    rfl

/-- The point `w₀` lies over the base of `x₀`. -/
theorem fibreBasePoint_base {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
      (baseProj D.Y) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom) ⋙ Over.post B.inclusion).obj
        (fibreBasePoint D x₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  hx₀

/-- The point `V = Spec k` of `x₀` is locally of finite type over `S` when `Spec k ⟶ S` is. -/
theorem locallyOfFiniteType_point {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    LocallyOfFiniteType (B.inclusion.map x₀.T.left.hom) := by
  show LocallyOfFiniteType ((complexesFunctor D ⋙ Over.post B.inclusion).obj x₀).hom
  rwa [hx₀]

/-- **The tangent spaces of the second factor `(Sch/V)` of the fibre are finite dimensional**, at
the second projection of `w₀` and over every deformation base: `V = Spec k` is a scheme locally
of finite type over `S`, and this is the scheme case of Stacks 07X1
(`Deformation.Artin.finiteDimensional_tangentModuleAt_overMap`). It is the input `hT𝒵` of
`Deformation.Artin.finiteDimensional_tangentModuleAt_twoFibreProduct_of_fibre` at `w₀`. -/
theorem finiteDimensional_tangentModuleAt_fibreBasePoint_snd {Λ k : Type u} [CommRing Λ]
    [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hz₀ : (Over.map x₀.T.left.hom ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.snd (complexesFunctor D) (Over.map x₀.T.left.hom) (baseProj D.Y)
          (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom)).obj
          (fibreBasePoint D x₀)) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (Over.map x₀.T.left.hom ⋙ Over.post B.inclusion)
      ((TwoFibreProductOver.snd (complexesFunctor D) (Over.map x₀.T.left.hom) (baseProj D.Y)
          (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom)).obj
          (fibreBasePoint D x₀)) hz₀).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (Over.map x₀.T.left.hom ⋙ Over.post B.inclusion)
        ((TwoFibreProductOver.snd (complexesFunctor D) (Over.map x₀.T.left.hom) (baseProj D.Y)
          (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom)).obj
          (fibreBasePoint D x₀)) hz₀).projection) hD (FGModuleCat.of k k)) := by
  have := locallyOfFiniteType_point D iΛ x₀ hx₀ hfinite
  exact finiteDimensional_tangentModuleAt_overMap B S hS x₀.T.left iΛ _ hz₀ hfinite hqc hD

/-- **The tangent-space hypothesis on the fibre**: the tangent space of the fibre
`𝒲 = Complexes_{X/Y} ×_{𝒮_Y} (Sch/V)` at `w₀` is finite dimensional, for every witness that
`𝓕_{𝒲,k,w₀}` is a deformation category. This is the hypothesis `hT𝒲` of
`Deformation.Artin.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_fst_twoFibreProduct` at
`w₀`: the content of the third and fourth paragraphs of the proof of Stacks 0DLL,
`T𝓕_{𝒳₀} = Ext¹(E₀, E₀)` (with the derivations of `k`). -/
abbrev FibreTangentFinite {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) : Prop :=
  ∀ hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom) ⋙ Over.post B.inclusion)
      (fibreBasePoint D x₀) (fibreBasePoint_base D iΛ x₀ hx₀)).projection,
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
          (baseProj D.Y) (complexesToBaseObjects D)
          (schemePointToBase D.Y x₀.T.left x₀.T.hom) ⋙ Over.post B.inclusion)
        (fibreBasePoint D x₀) (fibreBasePoint_base D iΛ x₀ hx₀)).projection) hD
      (FGModuleCat.of k k))

/-- **The infinitesimal-automorphism hypothesis on the fibre**: the infinitesimal automorphisms
of the fibre `𝒲` at every point of the special fibre of `𝓕_{𝒲,k,w₀}`, for every choice of
pushforwards, are finite dimensional. This is the hypothesis `hInf𝒲` of
`Deformation.Artin.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_fst_twoFibreProduct` at
`w₀`: the content of the third and fourth paragraphs of the proof of Stacks 0DLL,
`Inf(𝓕_{𝒳₀}) = Ext⁰(E₀, E₀)`. -/
abbrev FibreInfFinite {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) : Prop :=
  ∀ (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom) ⋙ Over.post B.inclusion)
      (fibreBasePoint D x₀) (fibreBasePoint_base D iΛ x₀ hx₀)).projection)
    (x : (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom) ⋙ Over.post B.inclusion)
      (fibreBasePoint D x₀) (fibreBasePoint_base D iΛ x₀ hx₀)).carrier)
    (_hx : (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom) ⋙ Over.post B.inclusion)
      (fibreBasePoint D x₀) (fibreBasePoint_base D iΛ x₀ hx₀)).projection.obj x =
        Deformation.residueFieldObject Λ k)
    (P : ChosenPushforwardsAt (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom) ⋙ Over.post B.inclusion)
      (fibreBasePoint D x₀) (fibreBasePoint_base D iΛ x₀ hx₀)).projection x),
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P)

/-- **Paragraph 2 of the proof of Stacks 0DLL for `Complexes_{X/Y}`, for any algebraic space `Y`,
with the tangent spaces of the base as a hypothesis.** Let `Complexes_{X/Y}` satisfy (RS)
(Stacks 0DLK, `h0DLK`). For a field point `x₀` of `Complexes_{X/Y}` over
`Spec k ⟶ Spec Λ ⟶ S`, with `Spec Λ ⟶ S` arbitrary, the tangent space `T𝓕_{𝒳,k,x₀}` and the
infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x₀})` of Stacks 07WY are finite dimensional as soon as
those of the fibre `𝒲 = Complexes_{X/Y} ×_{𝒮_Y} (Sch/Spec k)` at `w₀` are (`hT𝒲`, `hInf𝒲`) and
the tangent spaces of the base `𝒮_Y` over the same deformation base are (`hT𝒴`).

This is Stacks 07X2 for the 2-fibre product `𝒲`
(`Deformation.Artin.finiteDimensional_tangentSpaceModuleOfSatisfiesRS_fst_twoFibreProduct`); the
base `𝒮_Y` satisfies (RS) and has no infinitesimal automorphisms.

`hT𝒴` is Stacks 07X1 for the algebraic space `Y` (locally of finite type over `S`) at a
deformation base `Spec Λ ⟶ S` which need not be an open immersion. That is a gap in the library,
which has Stacks 07X1 only for open immersions `Spec Λ ⟶ S` with `Λ → k` finite. It holds when
`Y` is a scheme locally of finite type over `S`
(`AlgebraicGeometry.Space.finiteDimensional_tangentModuleAt_baseBasedCategory_of_iso`), which
gives `finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_iso_scheme`. -/
theorem finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_baseTangent
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLK : SatisfiesRS B S hS (complexesFunctor D) h0DLF)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT𝒴 : ∀ (y : BaseObjects D.Y) (hy : (baseProj D.Y ⋙ Over.post B.inclusion).obj y =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (baseProj D.Y ⋙ Over.post B.inclusion) y hy).projection),
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (baseProj D.Y ⋙ Over.post B.inclusion) y hy).projection) hD
        (FGModuleCat.of k k)))
    (hT𝒲 : FibreTangentFinite D iΛ x₀ hx₀) (hInf𝒲 : FibreInfFinite D iΛ x₀ hx₀) :
    FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS (complexesFunctor D) h0DLF
        h0DLK iΛ x₀ hx₀ hfinite hqc) ∧
      ∀ x P, FiniteDimensional k (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS
        (complexesFunctor D) h0DLF h0DLK iΛ x₀ hx₀ hfinite hqc x P) :=
  finiteDimensional_tangentSpaceModuleOfSatisfiesRS_fst_twoFibreProduct B S hS iΛ
    (complexesFunctor D) (baseProj D.Y) (Over.map x₀.T.left.hom)
    (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
    (fibreBasePoint_base D iΛ x₀ hx₀) (complexesToBaseObjects_comp D)
    (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom) h0DLF
    (baseProj_isFiberedInGroupoids D.Y)
    (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom) h0DLK
    (baseBasedCategory_satisfiesRS D.Y) (satisfiesRS_overMap B S hS x₀.T.left) hfinite hqc
    hT𝒲 (fun hy hD => hT𝒴 _ hy hD) hInf𝒲
    (fun hy hD x _ P => finiteDimensional_inf_baseBasedCategory D.Y iΛ _ hy hD x P)
    hx₀

/-- **Paragraph 2 of the proof of Stacks 0DLL for `Complexes_{X/Y}`, in the setting of
Section 07T2.** Let `S` be locally Noetherian, `Y` locally of finite type over `S` (Stacks 0DLL
assumes `B ⟶ S` locally of finite presentation), and let `Complexes_{X/Y}` satisfy (RS)
(Stacks 0DLK, `h0DLK`). For a field `k` of finite type over `S`, an affine open `Spec Λ ⊆ S`
through which `Spec k ⟶ S` factors with `Λ → k` finite, and an object `x₀` of `Complexes_{X/Y}`
over `Spec k`, the tangent space `T𝓕_{𝒳,k,x₀}` and the infinitesimal automorphisms
`Inf(𝓕_{𝒳,k,x₀})` of Stacks 07WY are finite dimensional as soon as those of the fibre
`𝒲 = Complexes_{X/Y} ×_{𝒮_Y} (Sch/Spec k)` at `w₀` are (`hT𝒲`, `hInf𝒲`).

This is `finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_baseTangent`, the tangent spaces
of the base `𝒮_Y` being finite dimensional by Stacks 07X1
(`Space.finiteDimensional_tangentModuleAt_baseBasedCategory_of_isOpenImmersion`). -/
theorem finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_isOpenImmersion
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from D.Y.obj))
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLK : SatisfiesRS B S hS (complexesFunctor D) h0DLF)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT𝒲 : FibreTangentFinite D iΛ x₀ hx₀) (hInf𝒲 : FibreInfFinite D iΛ x₀ hx₀) :
    FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS (complexesFunctor D) h0DLF
        h0DLK iΛ x₀ hx₀ hfinite hqc) ∧
      ∀ x P, FiniteDimensional k (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS
        (complexesFunctor D) h0DLF h0DLK iΛ x₀ hx₀ hfinite hqc x P) :=
  finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_baseTangent D h0DLF h0DLK iΛ x₀ hx₀
    hfinite hqc
    (fun y hy hD => finiteDimensional_tangentModuleAt_baseBasedCategory_of_isOpenImmersion D.Y
      hft iΛ hiΛ hfinite hqc y hy hD)
    hT𝒲 hInf𝒲

/-- **Paragraph 2 of the proof of Stacks 0DLL for `Complexes_{X/Y}`, when `Y` is a scheme.** Let
`Y` be isomorphic to a scheme `W` of the site locally of finite type over `S`, and let
`Complexes_{X/Y}` satisfy (RS) (Stacks 0DLK, `h0DLK`). For a field point `x₀` of
`Complexes_{X/Y}` over `Spec k ⟶ Spec Λ ⟶ S`, with `Spec Λ ⟶ S` arbitrary, the tangent space
`T𝓕_{𝒳,k,x₀}` and the infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x₀})` of Stacks 07WY are finite
dimensional as soon as those of the fibre `𝒲 = Complexes_{X/Y} ×_{𝒮_Y} (Sch/Spec k)` at `w₀`
are (`hT𝒲`, `hInf𝒲`).

This is `finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_baseTangent`, the base `𝒮_Y`
having finite-dimensional tangent spaces over every deformation base by the scheme case of
Stacks 07X1. -/
theorem finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_iso_scheme
    {W : BigFppfOver B S hS} [LocallyOfFiniteType (B.inclusion.map W.hom)]
    (e : D.Y ≅ (schemeSpaceFunctor B S hS).obj W)
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLK : SatisfiesRS B S hS (complexesFunctor D) h0DLF)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT𝒲 : FibreTangentFinite D iΛ x₀ hx₀) (hInf𝒲 : FibreInfFinite D iΛ x₀ hx₀) :
    FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS (complexesFunctor D) h0DLF
        h0DLK iΛ x₀ hx₀ hfinite hqc) ∧
      ∀ x P, FiniteDimensional k (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS
        (complexesFunctor D) h0DLF h0DLK iΛ x₀ hx₀ hfinite hqc x P) :=
  finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_baseTangent D h0DLF h0DLK iΛ x₀ hx₀
    hfinite hqc
    (fun y hy hD => finiteDimensional_tangentModuleAt_baseBasedCategory_of_iso e iΛ hfinite hqc
      y hy hD)
    hT𝒲 hInf𝒲

/-- `𝟙` of the final object of the site is locally of finite type. -/
instance locallyOfFiniteType_inclusion_map_id :
    LocallyOfFiniteType (B.inclusion.map (Over.mk (𝟙 (B.obj hS))).hom) := by
  change LocallyOfFiniteType (B.inclusion.map (𝟙 (B.obj hS)))
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- **Paragraph 2 of the proof of Stacks 0DLL for `Complexes_{X/Y}`, when `Y = S`**: the case of
`finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_iso_scheme` in which `Y` is the final
algebraic space over `S`, the case Stacks 0DLN reduces to. -/
theorem finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_isTerminal (hY : IsTerminal D.Y)
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLK : SatisfiesRS B S hS (complexesFunctor D) h0DLF)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT𝒲 : FibreTangentFinite D iΛ x₀ hx₀) (hInf𝒲 : FibreInfFinite D iΛ x₀ hx₀) :
    FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS (complexesFunctor D) h0DLF
        h0DLK iΛ x₀ hx₀ hfinite hqc) ∧
      ∀ x P, FiniteDimensional k (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS
        (complexesFunctor D) h0DLF h0DLK iΛ x₀ hx₀ hfinite hqc x P) :=
  finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_iso_scheme D
    (hY.uniqueUpToIso BeauvilleLaszlo.Space.isTerminal_schemeSpace_terminal) h0DLF h0DLK iΛ x₀
    hx₀ hfinite hqc hT𝒲 hInf𝒲

/-- **The hypothesis `h0DLL` of Artin's criterion for `Complexes_{X/Y}`, when `Y = S`.** Granted
(RS) (Stacks 0DLK) and, at every field point `x₀`, the finiteness of the tangent space and the
infinitesimal automorphisms of the fibre `𝒲` at `w₀`, the tangent spaces of
`Complexes_{X/Y}` at the stalks of `S` are finite dimensional, in the form of the hypothesis
`h0DLL` of `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`. -/
theorem finiteDimensional_artinianTangentSpace_stalk_of_isTerminal (hY : IsTerminal D.Y)
    (h0DLF : (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLK : SatisfiesRS B S hS (complexesFunctor D) h0DLF)
    (hT𝒲 : ∀ (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D) (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      FibreTangentFinite D iΛ x₀ hx₀)
    (hInf𝒲 : ∀ (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D) (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      FibreInfFinite D iΛ x₀ hx₀) :
    ∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ S) (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
      LocallyOfFiniteType i₀ → QuasiCompact i₀ →
      ∀ (s : S), i₀ (IsLocalRing.closedPoint k) = s →
      ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
        (_hΛstalk : Λ' = S.presheaf.stalk s)
        (iΛ : Spec (.of Λ') ⟶ S)
        (_hiΛ : HEq iΛ (S.fromSpecStalk s))
        (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
        let hx : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
          hx₀.trans (congrArg Over.mk hbase.symm)
        let P := predeformationCategory iΛ (complexesFunctor D ⋙ Over.post B.inclusion) x₀ hx
        letI : Category P.carrier := P.category
        ∀ hD : IsDeformationCategory P.projection,
          let 𝓕 := BasedCategory.ofFunctor P.projection
          let hS2 := schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
          letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
          letI : Fact (SchlessingerConditionS2
            (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
          let F := isomorphismClasses 𝓕 hD.predeformation.cofibered
          let T := artinianTangentSpace Λ' k F
          letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
          letI : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
          FiniteDimensional k T :=
  finiteDimensional_artinianTangentSpace_stalk_of_finiteDimensional (complexesFunctor D) h0DLF
    h0DLK (fun Λ k _ _ _ iΛ x₀ hx₀ hfinite hqc =>
      (finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_isTerminal D hY h0DLF h0DLK iΛ x₀
        hx₀ hfinite hqc (hT𝒲 Λ k iΛ x₀ hx₀ hfinite hqc)
        (hInf𝒲 Λ k iΛ x₀ hx₀ hfinite hqc)).1)

end ComplexesSituation

end AlgebraicGeometry.Space
