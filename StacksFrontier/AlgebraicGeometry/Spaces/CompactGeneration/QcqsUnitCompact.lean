module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExt
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# The structure sheaf is compact in `D_QCoh` of a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` contained in a
big fppf site `B`.  Then `𝒪_X`, placed in degree zero, is a compact object of `D_QCoh(𝒪_X)`:
morphisms out of it commute with direct sums, that is, `RΓ(X, -)` commutes with direct sums on
`D_QCoh(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.IsQcohCompact`: an object `K` of `D(𝒪_X)` is compact relative to
  `D_QCoh(𝒪_X)` when morphisms out of `K` commute with direct sums of objects of `D_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.isQcohCompact_lowerShriek`: extension by zero along an étale morphism
  preserves relative compactness.
* `AlgebraicGeometry.Space.isCompactObject_unitQuasicoherent_of_qcqs`: `𝒪_X[0]` is a compact object
  of `D_QCoh(𝒪_X)` for `X` quasi-compact and quasi-separated.

## Implementation notes

The proof is the induction principle of Stacks 08GP.  For an affine algebraic space compactness is
`AlgebraicGeometry.Space.isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent`.  For an
elementary distinguished square `(U ⊆ W, V → W)` the extension-by-zero sequence of Stacks 08GV,
`0 → j_{P!}𝒪_P → j_{U!}𝒪_U ⊕ j_{V!}𝒪_V → 𝒪_W → 0`, places `𝒪_W` in a distinguished triangle whose
other two vertices are compact relative to `D_QCoh(𝒪_W)`, because `j_!` is left adjoint to the
restriction `j^*`, which preserves direct sums and quasi-coherence.  The objects `j_!𝒪` do not lie
in `D_QCoh`, which is why compactness is first established relative to `D_QCoh` inside `D(𝒪_W)`.

## References

* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object `K` of `D(𝒪_W)` is *compact relative to `D_QCoh(𝒪_W)`* when, for every family of
objects of `D_QCoh(𝒪_W)` indexed by a type of the universe of the schemes and every direct sum of
it in `D(𝒪_W)`, the canonical map `⨁ i, Hom(K, E i) ⟶ Hom(K, ⨁ i, E i)` is bijective. -/
def IsQcohCompact (W : AlgebraicSpaces B S hS)
    (K : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) : Prop :=
  ∀ ⦃I : Type u⦄ [DecidableEq I] (E : I → DerivedCategory (Modules.{u, u} B S hS W.1 W.2)),
    (∀ i, QcohDerived B S hS W (E i)) →
      ∀ ⦃T : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)⦄ (j : ∀ i, E i ⟶ T),
        IsColimit (Cofan.mk T j) → Function.Bijective (cofanMap K j)

section General

variable {D : Type*} [Category D] [Preadditive D]

/-- The compactness maps of two objects are simultaneously bijective when they are intertwined by
additive equivalences of the hom groups. -/
private theorem bijective_cofanMap_iff_of_addEquiv {C₁ C₂ : Type*} [Category C₁] [Preadditive C₁]
    [Category C₂] [Preadditive C₂] {K : C₁} {K' : C₂} {I : Type*} [DecidableEq I] {A : I → C₁}
    {A' : I → C₂} {T : C₁} {T' : C₂} (j : ∀ i, A i ⟶ T) (j' : ∀ i, A' i ⟶ T')
    (e : ∀ i, (K ⟶ A i) ≃+ (K' ⟶ A' i)) (eT : (K ⟶ T) ≃+ (K' ⟶ T'))
    (h : ∀ i y, eT (y ≫ j i) = e i y ≫ j' i) :
    Function.Bijective (cofanMap K' j') ↔ Function.Bijective (cofanMap K j) := by
  let α : (DirectSum I fun i => (K ⟶ A i)) ≃+ DirectSum I fun i => (K' ⟶ A' i) :=
    DFinsupp.mapRange.addEquiv e
  have hcomm : ∀ x, cofanMap K' j' (α x) = eT (cofanMap K j x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i y =>
      have hα : α (DirectSum.of (fun i => K ⟶ A i) i y) =
          DirectSum.of (fun i => K' ⟶ A' i) i (e i y) := by
        simp only [α, DirectSum.of]
        exact DFinsupp.mapRange_single (hf := fun _ => map_zero _)
      rw [hα, cofanMap_of, cofanMap_of, h]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hcomp : (cofanMap K' j') ∘ α = eT ∘ cofanMap K j := funext hcomm
  rw [← Function.Bijective.of_comp_iff _ α.bijective, hcomp]
  exact ⟨fun h => (Function.Bijective.of_comp_iff' eT.bijective _).1 h,
    fun h => eT.bijective.comp h⟩

/-- The compactness map against a fixed cofan depends on the source only up to isomorphism. -/
theorem bijective_cofanMap_of_iso_source {K K' : D} (e : K ≅ K') {I : Type*} [DecidableEq I]
    {E : I → D} {T : D} (j : ∀ i, E i ⟶ T) (h : Function.Bijective (cofanMap K j)) :
    Function.Bijective (cofanMap K' j) := by
  let ε : ∀ M : D, (K ⟶ M) ≃+ (K' ⟶ M) := fun M =>
    { toFun := fun f => e.inv ≫ f
      invFun := fun f => e.hom ≫ f
      left_inv := fun f => by simp
      right_inv := fun f => by simp
      map_add' := fun f g => by simp }
  exact (bijective_cofanMap_iff_of_addEquiv j j (fun i => ε (E i)) (ε T)
    fun i y => by simp [ε]).2 h

variable {E' : Type*} [Category E'] [Preadditive E']

/-- Along an adjunction `L ⊣ G` of additive functors, the compactness map of `K` against the image
under `G` of a cofan is bijective exactly when that of `L.obj K` against the cofan is. -/
theorem bijective_cofanMap_map_iff_of_adjunction {L : D ⥤ E'} {G : E' ⥤ D} [L.Additive]
    [G.Additive] (adj : L ⊣ G) (K : D) {I : Type*} [DecidableEq I] {A : I → E'} {T : E'}
    (j : ∀ i, A i ⟶ T) :
    Function.Bijective (cofanMap K fun i => G.map (j i)) ↔
      Function.Bijective (cofanMap (L.obj K) j) :=
  bijective_cofanMap_iff_of_addEquiv j (fun i => G.map (j i))
    (fun i => adj.homAddEquiv K (A i)) (adj.homAddEquiv K T) fun i y => by
      simpa only [Adjunction.homAddEquiv_apply] using adj.homEquiv_naturality_right y (j i)

/-- Along a fully faithful additive functor, the compactness map of `F.obj K` against the image of a
cofan is bijective exactly when that of `K` against the cofan is. -/
theorem bijective_cofanMap_map_iff_of_fullyFaithful (F : D ⥤ E') [F.Additive] [F.Full]
    [F.Faithful] (K : D) {I : Type*} [DecidableEq I] {A : I → D} {T : D} (j : ∀ i, A i ⟶ T) :
    Function.Bijective (cofanMap (F.obj K) fun i => F.map (j i)) ↔
      Function.Bijective (cofanMap K j) := by
  let e : ∀ M : D, (K ⟶ M) ≃+ (F.obj K ⟶ F.obj M) := fun M =>
    AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩
  exact bijective_cofanMap_iff_of_addEquiv j (fun i => F.map (j i)) (fun i => e (A i)) (e T)
    fun i y => F.map_comp y (j i)

end General

/-! ### Relative compactness -/

attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- Restriction of modules along an étale morphism commutes with direct sums in the derived
categories. -/
theorem preservesColimitsOfShape_mapDerivedCategory_etaleModulePullback
    {Z W : AlgebraicSpaces B S hS} (j : Z ⟶ W) (hj : IsEtale B S hS j.hom) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory := by
  have : (etaleModulePullback.{u, u} B S hS j hj).IsLeftAdjoint :=
    (etaleModulePullbackAdjunction B S hS j hj).isLeftAdjoint
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
    (Modules.{u, u} B S hS W.1 W.2) I
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
    (Modules.{u, u} B S hS Z.1 Z.2) I
  have : PreservesColimitsOfShape (Discrete I)
      ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) := inferInstance
  have : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryFactors.symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q _ I

variable {B S hS}

/-- Relative compactness is invariant under isomorphism. -/
theorem IsQcohCompact.of_iso {W : AlgebraicSpaces B S hS}
    {K K' : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)} (e : K ≅ K')
    (h : IsQcohCompact B S hS W K) : IsQcohCompact B S hS W K' :=
  fun _ _ E hE _ j hj => bijective_cofanMap_of_iso_source e j (h E hE j hj)

/-- Relative compactness is stable under the shift. -/
theorem IsQcohCompact.shift {W : AlgebraicSpaces B S hS}
    {K : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)} (h : IsQcohCompact B S hS W K)
    (n : ℤ) : IsQcohCompact B S hS W (K⟦n⟧) := by
  intro I _ E hE T j hj
  have : (shiftEquiv (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) n).functor.Additive :=
    inferInstanceAs (shiftFunctor _ n).Additive
  have : (shiftEquiv (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) n).inverse.Additive :=
    inferInstanceAs (shiftFunctor _ (-n)).Additive
  refine (bijective_cofanMap_map_iff_of_adjunction
    (shiftEquiv (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) n).toAdjunction K j).1 ?_
  refine h (fun i => (E i)⟦-n⟧) (fun i => (QcohDerived B S hS W).le_shift (-n) _ (hE i))
    (fun i => (shiftFunctor _ (-n)).map (j i)) ?_
  exact (isColimitMapCoconeCofanMkEquiv (shiftFunctor _ (-n)) E j)
    (isColimitOfPreserves (shiftFunctor _ (-n)) hj)

/-- Relative compactness passes to the third vertex of a distinguished triangle. -/
theorem IsQcohCompact.obj₃ {W : AlgebraicSpaces B S hS}
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS W.1 W.2))) (hT : T ∈ distTriang _)
    (h₁ : IsQcohCompact B S hS W T.obj₁) (h₂ : IsQcohCompact B S hS W T.obj₂) :
    IsQcohCompact B S hS W T.obj₃ :=
  fun _ _ E hE _ j hj => bijective_cofanMap_obj₃ T hT j (h₁ E hE j hj) (h₂ E hE j hj)
    ((h₁.shift 1) E hE j hj) ((h₂.shift 1) E hE j hj)

/-- A direct sum of two relatively compact objects is relatively compact. -/
theorem IsQcohCompact.biprod {W : AlgebraicSpaces B S hS}
    {K L : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)} (hK : IsQcohCompact B S hS W K)
    (hL : IsQcohCompact B S hS W L) : IsQcohCompact B S hS W (K ⊞ L) :=
  IsQcohCompact.obj₃ _ (inv_rot_of_distTriang _ (binaryBiproductTriangle_distinguished K L))
    (hL.shift (-1)) hK

/-- Extension by zero preserves relative compactness: for an étale morphism `j : Z ⟶ W` and `K`
compact relative to `D_QCoh(𝒪_Z)`, the extension by zero `j_!K` is compact relative to
`D_QCoh(𝒪_W)`. -/
theorem isQcohCompact_lowerShriek {Z W : AlgebraicSpaces B S hS} (j : Z ⟶ W)
    (hj : IsEtale B S hS j.hom) {K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)}
    (hK : IsQcohCompact B S hS Z K) :
    IsQcohCompact B S hS W ((etaleModuleLowerShriek B S hS j hj).mapDerivedCategory.obj K) := by
  intro I _ E hE T ι hι
  have := preservesColimitsOfShape_mapDerivedCategory_etaleModulePullback B S hS j hj I
  refine (bijective_cofanMap_map_iff_of_adjunction
    (etaleModuleLowerShriekAdjunction B S hS j hj).mapDerivedCategory K ι).1 ?_
  exact hK _ (fun i => derivedQuasicoherent_etaleModulePullback B S hS j hj (E i) (hE i)) _
    ((isColimitMapCoconeCofanMkEquiv _ E ι) (isColimitOfPreserves _ hι))

/-- `𝒪_W[0]`, the structure sheaf of an algebraic space placed in degree zero. -/
abbrev unitDerived (W : AlgebraicSpaces B S hS) :
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2) :=
  (DerivedCategory.singleFunctor _ 0).obj (structureModule W)

variable (B S hS) in
/-- On an algebraic space, an `I`-indexed direct sum in `D(𝒪_W)` of objects of `D_QCoh(𝒪_W)` lies
in `D_QCoh(𝒪_W)`, for `I` in the universe of the schemes. -/
theorem isClosedUnderColimitsOfShape_qcohDerived (W : AlgebraicSpaces B S hS) (I : Type u) :
    (QcohDerived B S hS W).IsClosedUnderColimitsOfShape (Discrete I) :=
  isClosedUnderCoproducts_quasicoherentDerivedCategory B S hS W.1 W.2 I
    fun M hM => isQuasicoherentOnSite_sigma_of_h03DX B S hS W.1 W.2
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS W.1 W.2) M hM

/-- On an affine algebraic space `W`, `𝒪_W[0]` is compact relative to `D_QCoh(𝒪_W)`. -/
theorem isQcohCompact_unitDerived_of_isAffineSpace (W : AlgebraicSpaces B S hS)
    (hW : IsAffineSpace B S hS W.1) : IsQcohCompact B S hS W (unitDerived W) := by
  obtain ⟨hc, -⟩ :=
    isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent (X := W.1) (hX := W.2) hW
  intro I _ E hE T ι hι
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS W I
  have hT : QcohDerived B S hS W T :=
    (QcohDerived B S hS W).prop_of_isColimit hι fun i => hE i.as
  let E' : I → QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2 := fun i => ⟨E i, hE i⟩
  let T' : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2 := ⟨T, hT⟩
  let ι' : ∀ i, E' i ⟶ T' := fun i => ObjectProperty.homMk (ι i)
  have hι' : IsColimit (Cofan.mk T' ι') :=
    isColimitOfReflects (ObjectProperty.ι _)
      ((isColimitMapCoconeCofanMkEquiv (ObjectProperty.ι _) E' ι').symm hι)
  exact (bijective_cofanMap_map_iff_of_fullyFaithful (ObjectProperty.ι _) _ ι').2
    (bijective_cofanMap _ hc ι' hι')

section Square

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- For an étale morphism `j : Z ⟶ W`, `j_!(𝒪_W|_Z)[0]` is compact relative to `D_QCoh(𝒪_W)` as
soon as `𝒪_Z[0]` is compact relative to `D_QCoh(𝒪_Z)`. -/
theorem isQcohCompact_single_lowerShriek_unit {Z : AlgebraicSpaces B S hS} (j : Z ⟶ W)
    (hj : IsEtale B S hS j.hom) (hZ : IsQcohCompact B S hS Z (unitDerived Z)) :
    IsQcohCompact B S hS W ((DerivedCategory.singleFunctor _ 0).obj
      ((etaleModuleLowerShriek B S hS j hj).obj
        ((etaleModulePullback.{u, u} B S hS j hj).obj (structureModule W)))) :=
  (isQcohCompact_lowerShriek j hj hZ).of_iso
    (((etaleModuleLowerShriek B S hS j hj).mapDerivedCategorySingleFunctor 0).app
      (structureModule Z))

include hsq in
/-- For an elementary distinguished square `(U ⊆ W, V → W)` with intersection `P`, if
`𝒪_U[0]`, `𝒪_V[0]` and `𝒪_P[0]` are compact relative to `D_QCoh`, so is `𝒪_W[0]`. -/
theorem isQcohCompact_unitDerived_of_isElementaryDistinguishedSquare
    (hU : IsQcohCompact B S hS (edsOpen B S hS hsq) (unitDerived _))
    (hV : IsQcohCompact B S hS (edsEtale B S hS hsq) (unitDerived _))
    (hP : IsQcohCompact B S hS (edsInter B S hS hsq) (unitDerived _)) :
    IsQcohCompact B S hS W (unitDerived W) := by
  have hSE := (mayerVietoris_shortExact_and_mem_distTriang B S hS hsq).1
    (structureModule W)
  refine IsQcohCompact.obj₃ _ hSE.singleTriangle_distinguished ?_ ?_
  · exact isQcohCompact_single_lowerShriek_unit _ (isEtale_edsInterHom B S hS hsq) hP
  · have hsplit := (ShortComplex.Splitting.ofHasBinaryBiproduct
      ((etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).obj
        ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj (structureModule W)))
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj (structureModule W)))).shortExact
    exact IsQcohCompact.obj₃ _ (inv_rot_of_distTriang _ hsplit.singleTriangle_distinguished)
      ((isQcohCompact_single_lowerShriek_unit _ (isEtale_edsEtaleHom B S hS hsq) hV).shift (-1))
      (isQcohCompact_single_lowerShriek_unit _ (isEtale_edsOpenHom B S hS hsq) hU)

end Square

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- `𝒪_X[0]` is compact relative to `D_QCoh(𝒪_X)` on a quasi-compact quasi-separated algebraic
space. -/
theorem isQcohCompact_unitDerived (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    IsQcohCompact B S hS X (unitDerived X) :=
  qcqs_induction_on_self B S hS hZ X hqc hqs
    (fun Z _ => ∀ hZ' : IsAlgebraicSpace B S hS Z,
      IsQcohCompact B S hS ⟨Z, hZ'⟩ (unitDerived ⟨Z, hZ'⟩))
    (fun _V hV _ => isQcohCompact_unitDerived_of_isAffineSpace _ hV)
    (fun _ _ _ _ _ hsq _ _ _ _ hPU hPV hPP _ =>
      isQcohCompact_unitDerived_of_isElementaryDistinguishedSquare hsq (hPU _) (hPV _) (hPP _))
    X.2

/-- `𝒪_X[0]` is a compact object of `D_QCoh(𝒪_X)` for a quasi-compact and quasi-separated
algebraic space `X`: morphisms out of `𝒪_X[0]` commute with direct sums of objects of
`D_QCoh(𝒪_X)`. -/
theorem isCompactObject_unitQuasicoherent_of_qcqs (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    IsCompactObject.{u} (unitQuasicoherent X.2) := by
  constructor
  intro I _ E _
  have h := isQcohCompact_unitDerived hZ X hqc hqs
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS X I
  have : PreservesColimitsOfShape (Discrete I)
      (ObjectProperty.ι (QcohDerived B S hS X)) := inferInstance
  have hc : IsColimit (Cofan.mk ((ObjectProperty.ι _).obj (∐ E))
      fun i => (ObjectProperty.ι _).map (Sigma.ι E i)) :=
    (isColimitMapCoconeCofanMkEquiv (ObjectProperty.ι _) E (Sigma.ι E))
      (isColimitOfPreserves (ObjectProperty.ι _) (coproductIsCoproduct E))
  exact (bijective_cofanMap_map_iff_of_fullyFaithful (ObjectProperty.ι _) _ (Sigma.ι E)).1
    (h (fun i => (E i).obj) (fun i => (E i).property) _ hc)

end AlgebraicGeometry.Space

end
