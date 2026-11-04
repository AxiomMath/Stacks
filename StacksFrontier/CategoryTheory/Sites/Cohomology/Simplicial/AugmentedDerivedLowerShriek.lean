module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.MooreComplexLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.LowerShriekBaseChange
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek on `D(A_•)` with values in `D(O)`, for an augmentation `A_• ⟶ O`

Let `C` be a site and let `ε : A_• ⟶ O` be an augmentation (Simplicial, Definition 018G) of a
simplicial sheaf of rings by a sheaf of rings, that is, a morphism from `A_•` to the constant
simplicial sheaf of rings `O`. Remark 09D3 defines an exact functor of triangulated categories

`Lπ_! : D(A_•) ⟶ D(O)`

as the composite of derived base change `- ⊗^L_{A_•} O : D(A_•) ⟶ D(Δ × C, π^{-1}O)` with the
functor `Lπ_! : D(Δ × C, π^{-1}O) ⟶ D(O)` of Remark 09CY. This file constructs it.

## Main definitions

* `Stacks.SimplicialModules.constCommRing`: a sheaf of commutative rings read as a constant
  simplicial sheaf of commutative rings.
* `Stacks.SimplicialModules.CommAugmentation`: an augmentation `A_• ⟶ O` in sheaves of rings.
* `Stacks.SimplicialModules.augmentedDerivedLowerShriek`: `Lπ_! : D(A_•) ⥤ D(O)`.
* `Stacks.SimplicialModules.augmentedAbelian` and `Stacks.SimplicialModules.InducesQuasiIso`: the
  augmented simplicial abelian sheaf `A_• ⟶ O`, and the hypothesis of the source that the induced
  map `s(A_•) ⟶ O` of chain complexes of abelian sheaves be a quasi-isomorphism.

## Main results

* `Stacks.SimplicialModules.augmentedDerivedLowerShriek_commShift` and
  `Stacks.SimplicialModules.augmentedDerivedLowerShriek_isTriangulated`: it is an exact functor of
  triangulated categories.
* `Stacks.SimplicialModules.isIso_derivedLowerShriek_map_ringAbelianSheafMap`: if `ε` induces a
  quasi-isomorphism `s(A_•) ⟶ O`, then `Lπ_!A_• ⟶ Lπ_!O` is an isomorphism in `D(C)`, which is the
  hypothesis of Lemma 09D2 for `A_• ⟶ O`. This uses that `Lπ_!` of a simplicial abelian sheaf is
  computed by its Moore complex (`MooreComplexLowerShriek.lean`).
* `Stacks.SimplicialModules.augmentedDerivedLowerShriekForgetIso`: if `ε` induces a
  quasi-isomorphism `s(A_•) ⟶ O`, then, naturally in `K`, forgetting the module structure of
  `Lπ_!(K)` for the functor of this file gives `Lπ_!` of the underlying complex of abelian sheaves
  of `K` — the `O`-module structure of the source, through Lemma 09D2
  (`Stacks.SimplicialModules.isIso_derivedBaseChangeComparison`).

## Implementation notes

Nothing is carried as a parameter. The first factor is
`Stacks.SimplicialModules.derivedBaseChange`, the derived pullback of Stacks 06YY along the change
of coefficient rings `A_• ⟶ π^{-1}O` on `Δ × C`; the second is
`Stacks.SimplicialModules.derivedModuleLowerShriek`, the left derived functor of `π_!` on
`π^{-1}O`-modules, which exists by Stacks 08PC part (3). The category of simplicial modules over
the constant simplicial sheaf of rings `O` *is* the category of `π^{-1}O`-modules on `Δ × C`: the
two sheaves of rings agree on the nose, so the composite needs no comparison.

Derived base change is exact because it is left adjoint to derived restriction of scalars, which
is induced by an exact functor; `Lπ_!` is exact for the same reason.

The rings are commutative and the site is small, with all universes equal, as required by the
derived tensor product of the library and as in the source.

The hypothesis of the source that `ε` induce a quasi-isomorphism `s(A_•) ⟶ O` is not needed to
form the composite or to prove it exact, so those statements are made without it; it is what
identifies `Lπ_!(K)` with `Lπ_!` of the underlying complex of abelian sheaves of `K` (the
`O`-module structure of the source), through Lemma 09D2.

## References

* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 018G](https://stacks.math.columbia.edu/tag/018G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

/- The abelian structure on sheaves of modules is the library's canonical
`AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules`, the one the derived functors used
here are built with; the alternative instance of `SiteModules` would produce a different derived
category. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.SimplicialModules

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- A sheaf of commutative rings, read as a constant simplicial sheaf of commutative rings. -/
abbrev constCommRing (O : Sheaf J CommRingCat.{u}) : SimplicialObject (Sheaf J CommRingCat.{u}) :=
  (Functor.const SimplexCategoryᵒᵖ).obj O

/-- **Simplicial, Definition 018G, in sheaves of rings.** An augmentation of a simplicial sheaf of
rings `A_•` by a sheaf of rings `O`: a morphism to the constant simplicial sheaf of rings `O`. -/
abbrev CommAugmentation (A : SimplicialObject (Sheaf J CommRingCat.{u}))
    (O : Sheaf J CommRingCat.{u}) :=
  A ⟶ constCommRing J O

variable {A : SimplicialObject (Sheaf J CommRingCat.{u})} {O : Sheaf J CommRingCat.{u}}

/-- Simplicial modules over the constant simplicial sheaf of rings `O` are modules over `π^{-1}O`
on `Δ × C`: the two sheaves of rings are equal. -/
theorem ringSheaf_commRingSheaf_constCommRing :
    Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J (constCommRing J O)) =
      simplicialProjectionRing J (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  rfl

/-- Derived base change commutes with the shift, being left adjoint to derived restriction of
scalars, which does. -/
instance derivedBaseChange_commShift {B : SimplicialObject (Sheaf J CommRingCat.{u})} (φ : A ⟶ B) :
    (derivedBaseChange J φ).CommShift ℤ :=
  (derivedBaseChangeAdjunction J φ).leftAdjointCommShift ℤ

/-- Derived base change is an exact functor of triangulated categories: it is left adjoint to
derived restriction of scalars, which is exact. -/
instance derivedBaseChange_isTriangulated {B : SimplicialObject (Sheaf J CommRingCat.{u})}
    (φ : A ⟶ B) : (derivedBaseChange J φ).IsTriangulated :=
  have : (derivedBaseChangeAdjunction J φ).CommShift ℤ :=
    (derivedBaseChangeAdjunction J φ).commShift_of_rightAdjoint ℤ
  (derivedBaseChangeAdjunction J φ).isTriangulated_leftAdjoint

/-- The functor `Lπ_!` of Remark 09CY, read on simplicial modules over the constant simplicial
sheaf of rings `O`. -/
abbrev constDerivedLowerShriek (O : Sheaf J CommRingCat.{u}) :
    DerivedCategory (Modules J (constCommRing J O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  derivedModuleLowerShriek J (Stacks.SheafOfModules.Tensor.ringSheaf O)

/-- The functor `constDerivedLowerShriek J O` commutes with the shift. -/
instance constDerivedLowerShriek_commShift (O : Sheaf J CommRingCat.{u}) :
    (constDerivedLowerShriek J O).CommShift ℤ :=
  derivedModuleLowerShriek_commShift J _

/-- The functor `constDerivedLowerShriek J O` is an exact functor of triangulated categories. -/
instance constDerivedLowerShriek_isTriangulated (O : Sheaf J CommRingCat.{u}) :
    (constDerivedLowerShriek J O).IsTriangulated :=
  derivedModuleLowerShriek_isTriangulated J _

/-- **Remark 09D3, the functor.** For an augmentation `ε : A_• ⟶ O` of a simplicial sheaf of rings
by a sheaf of rings, `Lπ_! : D(A_•) ⥤ D(O)` is the composite of derived base change
`- ⊗^L_{A_•} O : D(A_•) ⥤ D(Δ × C, π^{-1}O)` with the functor
`Lπ_! : D(Δ × C, π^{-1}O) ⥤ D(O)` of Remark 09CY. -/
@[stacks 09D3 "the functor `Lπ_! : D(A_•) ⟶ D(O)`, the composition of `- ⊗^L_{A_•} O` with the \
functor `Lπ_! : D(Δ × C, π^{-1}O) ⟶ D(O)` of Remark 09CY"]
def augmentedDerivedLowerShriek (ε : CommAugmentation J A O) :
    DerivedCategory (Modules J A) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  derivedBaseChange J ε ⋙ constDerivedLowerShriek J O

/-- **Remark 09D3, exactness: the functor commutes with the shift.** -/
@[stacks 09D3 "`Lπ_! : D(A_•) ⟶ D(O)` is a functor of triangulated categories: it commutes \
with the shift"]
instance augmentedDerivedLowerShriek_commShift (ε : CommAugmentation J A O) :
    (augmentedDerivedLowerShriek J ε).CommShift ℤ :=
  inferInstanceAs ((derivedBaseChange J ε ⋙ constDerivedLowerShriek J O).CommShift ℤ)

/-- **Remark 09D3, exactness: `Lπ_! : D(A_•) ⥤ D(O)` is an exact functor of triangulated
categories**, as a composite of two exact functors. -/
@[stacks 09D3 "`Lπ_! : D(A_•) ⟶ D(O)` is an exact functor of triangulated categories"]
instance augmentedDerivedLowerShriek_isTriangulated (ε : CommAugmentation J A O) :
    (augmentedDerivedLowerShriek J ε).IsTriangulated :=
  inferInstanceAs ((derivedBaseChange J ε ⋙ constDerivedLowerShriek J O).IsTriangulated)

/-! ### The hypothesis `s(A_•) ⟶ O` is a quasi-isomorphism -/

section Hypothesis

/-- A sheaf of commutative rings, read as an abelian sheaf. -/
abbrev toAbSheaf : Sheaf J CommRingCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J forgetToAddCommGrp

/-- The augmented simplicial abelian sheaf `A_• ⟶ O` underlying an augmentation of a simplicial
sheaf of rings. -/
def augmentedAbelian (ε : CommAugmentation J A O) :
    SimplicialObject.Augmented (Sheaf J AddCommGrpCat.{u}) where
  left := ((SimplicialObject.whiskering _ _).obj (toAbSheaf J)).obj A
  right := (toAbSheaf J).obj O
  hom := ((SimplicialObject.whiskering _ _).obj (toAbSheaf J)).map ε ≫
    (Functor.constComp _ O (toAbSheaf J)).hom

/-- **The hypothesis of Remark 09D3: `ε` induces a quasi-isomorphism `s(A_•) ⟶ O`.** Here
`s(A_•)` is the alternating face map complex of the simplicial abelian sheaf underlying `A_•`
(Simplicial, Section 0194) and the map is the one induced by the augmentation in degree zero. -/
def InducesQuasiIso (ε : CommAugmentation J A O) : Prop :=
  QuasiIso ((AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Sheaf J AddCommGrpCat.{u})).app
    (augmentedAbelian J ε))

omit [SmallCategory C] in
/-- An exact functor which carries a morphism of complexes to a quasi-isomorphism carries its
homology maps to isomorphisms. -/
lemma isIso_map_homologyMap_of_quasiIso_map {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ]
    [Abelian 𝒜] [Abelian ℬ] (F : 𝒜 ⥤ ℬ) [F.Additive] [F.PreservesHomology]
    {K L : ChainComplex 𝒜 ℕ} (φ : K ⟶ L)
    [QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)] (n : ℕ) :
    IsIso (F.map (HomologicalComplex.homologyMap φ n)) := by
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.down ℕ) n).map φ) F
  have : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance
  have h' : F.map (HomologicalComplex.homologyMap φ n) =
      ((K.sc n).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n ≫
          ((L.sc n).mapHomologyIso F).hom :=
    ((Iso.inv_comp_eq _).mpr h).symm
  rw [h']
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' this (Iso.isIso_hom _))

/-- Restriction maps of the abelian sheaf on `Δ × C` attached to `B_•`, in the `C`-direction. -/
lemma commRingSheaf_map_snd (B : SimplicialObject (Sheaf J CommRingCat.{u}))
    (n : SimplexCategoryᵒᵖ) {V W : Cᵒᵖ} (g : V ⟶ W) :
    ((sheafCompose (simplicialProjectionTopology J) forgetToAddCommGrp).obj
        (commRingSheaf J B)).obj.map
        ((Prod.mkHom (𝟙 n.unop) g.unop : ((n.unop, W.unop) : SimplexCategory × C) ⟶
          (n.unop, V.unop))).op =
      forgetToAddCommGrp.map ((B.obj n).obj.map g) := by
  show forgetToAddCommGrp.map ((commRingSheaf J B).obj.map _) = _
  simp [commRingSheaf, associatedCommRingPresheaf, prodOpEquiv]

/-- Restriction maps of the abelian sheaf on `Δ × C` attached to `B_•`, in the `Δ`-direction. -/
lemma commRingSheaf_map_fst (B : SimplicialObject (Sheaf J CommRingCat.{u}))
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (V : Cᵒᵖ) :
    ((sheafCompose (simplicialProjectionTopology J) forgetToAddCommGrp).obj
        (commRingSheaf J B)).obj.map
        ((Prod.mkHom α.unop (𝟙 V.unop) : ((m.unop, V.unop) : SimplexCategory × C) ⟶
          (n.unop, V.unop))).op =
      forgetToAddCommGrp.map ((B.map α).hom.app V) := by
  show forgetToAddCommGrp.map ((commRingSheaf J B).obj.map _) = _
  simp [commRingSheaf, associatedCommRingPresheaf, prodOpEquiv]

/-- The underlying abelian presheaf of the simplicial sheaf of rings `B_•`, read on `Δ × C`, is the
simplicial presheaf `n ↦ B_n` of `C` (`pointEvaluation` at `A_{•,V} = (⦋•⦌, V)`): the identity on
sections. -/
def pointEvaluationIso (B : SimplicialObject (Sheaf J CommRingCat.{u})) :
    ((SimplicialObject.whiskering _ _).obj (sheafToPresheaf J AddCommGrpCat.{u})).obj
        (((SimplicialObject.whiskering _ _).obj (toAbSheaf J)).obj B) ≅
      ((projectionSituation J).pointEvaluation (projectionCosimplicial (C := C))).obj
        ((sheafCompose (simplicialProjectionTopology J) forgetToAddCommGrp).obj
            (commRingSheaf J B)).obj :=
  NatIso.ofComponents (fun n => NatIso.ofComponents (fun V => Iso.refl _) (fun {V W} g => by
      simp only [Iso.refl_hom]
      exact (commRingSheaf_map_snd J B n g).symm))
    (fun {n m} α => by
      ext V : 2
      simp only [NatTrans.comp_app]
      exact (commRingSheaf_map_fst J B α V).symm)

/-- `pointEvaluationIso` is natural in `B_•`. -/
lemma pointEvaluationIso_naturality {B B' : SimplicialObject (Sheaf J CommRingCat.{u})}
    (φ : B ⟶ B') :
    ((SimplicialObject.whiskering _ _).obj (sheafToPresheaf J AddCommGrpCat.{u})).map
        (((SimplicialObject.whiskering _ _).obj (toAbSheaf J)).map φ) ≫
      (pointEvaluationIso J B').hom =
    (pointEvaluationIso J B).hom ≫
      ((projectionSituation J).pointEvaluation (projectionCosimplicial (C := C))).map
        ((sheafCompose (simplicialProjectionTopology J) forgetToAddCommGrp).map
          (commRingSheafMap J φ)).hom := by
  ext n V : 3
  simp only [NatTrans.comp_app, pointEvaluationIso, NatIso.ofComponents_hom_app]
  rfl

omit [SmallCategory C] in
/-- Two out of three for quasi-isomorphisms, with the hypotheses passed explicitly. -/
lemma quasiIso_of_comp_right_explicit {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    {K L M : ChainComplex 𝒜 ℕ} (φ : K ⟶ L) (φ' : L ⟶ M) (h₁ : QuasiIso φ')
    (h₂ : QuasiIso (φ ≫ φ')) : QuasiIso φ := by
  have := h₁
  have := h₂
  exact quasiIso_of_comp_right φ φ'

/-- If `ε` induces a quasi-isomorphism `s(A_•) ⟶ O`, then it induces a quasi-isomorphism
`s(A_•) ⟶ s(O)` of Moore complexes: `s(O) ⟶ O` is a homotopy equivalence, the constant
augmented simplicial object having an extra degeneracy. -/
lemma quasiIso_alternatingFaceMapComplex_map (ε : CommAugmentation J A O)
    (hε : InducesQuasiIso J ε) :
    QuasiIso ((alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map
      (((SimplicialObject.whiskering _ _).obj (toAbSheaf J)).map ε)) := by
  let X := augmentedAbelian J ε
  let ψ : X ⟶ SimplicialObject.Augmented.const.obj X.right :=
    { left := X.hom
      right := 𝟙 X.right
      w := by
        dsimp [SimplicialObject.Augmented.const]
        simp }
  have hnat := (AlgebraicTopology.AlternatingFaceMapComplex.ε
    (C := Sheaf J AddCommGrpCat.{u})).naturality ψ
  have : QuasiIso ((AlgebraicTopology.AlternatingFaceMapComplex.ε
      (C := Sheaf J AddCommGrpCat.{u})).app (SimplicialObject.Augmented.const.obj X.right)) :=
    inferInstanceAs (QuasiIso
      (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
        (SimplicialObject.Augmented.ExtraDegeneracy.const X.right)).hom)
  have e : (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map X.hom ≫
      (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Sheaf J AddCommGrpCat.{u})).app
        (SimplicialObject.Augmented.const.obj X.right) =
      (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Sheaf J AddCommGrpCat.{u})).app X := by
    rw [show (SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ _).map ψ = 𝟙 _ from
      (ChainComplex.single₀ _).map_id _] at hnat
    exact hnat.trans (Category.comp_id _)
  have hX : QuasiIso ((alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map X.hom) :=
    quasiIso_of_comp_right_explicit _ _ this (by rw [e]; exact hε)
  have hX' : (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map X.hom =
      (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map
        (((SimplicialObject.whiskering _ _).obj (toAbSheaf J)).map ε) ≫
      (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map
        (Functor.constComp _ O (toAbSheaf J)).hom :=
    Functor.map_comp _ _ _
  rw [hX'] at hX
  have hiso : IsIso ((alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map
      (Functor.constComp _ O (toAbSheaf J)).hom) :=
    (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map_isIso
      (Functor.constComp _ O (toAbSheaf J)).hom
  exact quasiIso_of_comp_right_explicit _ _ (@quasiIso_of_isIso _ _ _ _ _ _ _ _ hiso _ _) hX

/-- **The hypothesis of Remark 09D3 gives the hypothesis of Lemma 09D2 for `A_• ⟶ O`.** If `ε`
induces a quasi-isomorphism `s(A_•) ⟶ O`, then `Lπ_!A_• ⟶ Lπ_!O` is an isomorphism in `D(C)`:
`Lπ_!` of a simplicial abelian sheaf is computed by its Moore complex
(`isIso_derivedLowerShriek_map_single_of_isIso_homology`). -/
theorem isIso_derivedLowerShriek_map_ringAbelianSheafMap (ε : CommAugmentation J A O)
    (hε : InducesQuasiIso J ε) :
    IsIso ((derivedLowerShriek J).map
      ((DerivedCategory.singleFunctor _ 0).map (ringAbelianSheafMap J ε))) := by
  let Ψ := ((SimplicialObject.whiskering _ _).obj (toAbSheaf J)).map ε
  let a := ringAbelianSheafMap J ε
  let i := sheafToPresheaf J AddCommGrpCat.{u}
  let sh := presheafToSheaf J AddCommGrpCat.{u}
  -- `sh ∘ i ≅ 𝟭`, on complexes
  have h₂ : QuasiIso ((sh.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map Ψ))) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso
      (Functor.mapHomologicalComplexCompIso
        (asIso (sheafificationAdjunction J AddCommGrpCat.{u}).counit) (ComplexShape.down ℕ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (ComplexShape.down ℕ))
      (Arrow.mk ((alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map Ψ)))).mpr
        (quasiIso_alternatingFaceMapComplex_map J ε hε)
  -- the underlying presheaf complex is the Moore complex of `a`
  let e : Arrow.mk ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).map Ψ)) ≅
      Arrow.mk (((projectionSituation J).pointMooreComplex (projectionCosimplicial (C := C))).map
        a.hom) :=
    Arrow.isoOfNatIso (alternatingFaceMapComplexCompMapHomologicalComplexIso i) Ψ ≪≫
      Arrow.isoMk ((alternatingFaceMapComplex _).mapIso (pointEvaluationIso J A))
        ((alternatingFaceMapComplex _).mapIso (pointEvaluationIso J (constCommRing J O)))
        (by
          show (alternatingFaceMapComplex _).map _ ≫ (alternatingFaceMapComplex _).map _ =
            (alternatingFaceMapComplex _).map _ ≫ (alternatingFaceMapComplex _).map _
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg (alternatingFaceMapComplex _).map
            (pointEvaluationIso_naturality J ε).symm)
  have h₃ : QuasiIso ((sh.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (((projectionSituation J).pointMooreComplex (projectionCosimplicial (C := C))).map a.hom)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      ((sh.mapHomologicalComplex (ComplexShape.down ℕ)).mapArrow.mapIso e)).mp h₂
  exact isIso_derivedLowerShriek_map_single_of_isIso_homology J a
    (fun n => isIso_map_homologyMap_of_quasiIso_map sh _ n)

end Hypothesis

/-! ### The `O`-module structure on `Lπ_!(K)` -/

section ModuleStructure

/-- **The identification giving `Lπ_!(K)` its `O`-module structure**, granted that the canonical
map `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} O)` of Lemma 09D2 is invertible: forgetting the module structure,
the functor `Lπ_! : D(A_•) ⥤ D(O)` is `Lπ_!` on the underlying complexes of abelian sheaves. It is
Remark 09CY (`derivedModuleLowerShriekForgetIso`) followed by the inverse of the map of
Lemma 09D2. -/
def augmentedDerivedLowerShriekForgetIsoOfIsIso (ε : CommAugmentation J A O)
    [IsIso (derivedBaseChangeComparison J ε)] :
    augmentedDerivedLowerShriek J ε ⋙
        (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapDerivedCategory ≅
      moduleDerivedLowerShriek J A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedBaseChange J ε)
      (derivedModuleLowerShriekForgetIso J (Stacks.SheafOfModules.Tensor.ringSheaf O)).symm ≪≫
    (asIso (derivedBaseChangeComparison J ε)).symm

/-- **Lemma 09D2 for the augmentation.** If `ε` induces a quasi-isomorphism `s(A_•) ⟶ O`, the
canonical map `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} O)` is an isomorphism for every `K` in `D(A_•)`. -/
theorem isIso_derivedBaseChangeComparison_of_inducesQuasiIso (ε : CommAugmentation J A O)
    (hε : InducesQuasiIso J ε) : IsIso (derivedBaseChangeComparison J ε) :=
  isIso_derivedBaseChangeComparison J ε (isIso_derivedLowerShriek_map_ringAbelianSheafMap J ε hε)

/-- **Remark 09D3, the `O`-module structure on `Lπ_!(K)`.** Let `ε : A_• ⟶ O` be an augmentation
inducing a quasi-isomorphism `s(A_•) ⟶ O`. For `K` in `D(A_•)`, `Lπ_!(K)` is canonically and
functorially identified with `Lπ_!(K ⊗^L_{A_•} O)` by Lemma 09D2, and the latter is, by
Remark 09CY, the underlying complex of abelian sheaves of the object `Lπ_!(K)` of `D(O)` of
`augmentedDerivedLowerShriek`. So, naturally in `K`, forgetting the `O`-module structure of the
functor of the source gives back `Lπ_!(K)`. -/
@[stacks 09D3 "the `O`-module structure on `Lπ_!(K)`: under the hypothesis that `ε` induces a \
quasi-isomorphism `s(A_•) ⟶ O`, the canonical, functorial identification of `Lπ_!(K)` with \
`Lπ_!(K ⊗^L_{A_•} O)` of Lemma 09D2, read as the underlying complex of abelian sheaves of the \
object `Lπ_!(K)` of `D(O)`"]
def augmentedDerivedLowerShriekForgetIso (ε : CommAugmentation J A O)
    (hε : InducesQuasiIso J ε) :
    augmentedDerivedLowerShriek J ε ⋙
        (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapDerivedCategory ≅
      moduleDerivedLowerShriek J A :=
  have := isIso_derivedBaseChangeComparison_of_inducesQuasiIso J ε hε
  augmentedDerivedLowerShriekForgetIsoOfIsIso J ε

end ModuleStructure

end Stacks.SimplicialModules

end
