module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusChangeOfBase
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.ChangeOfField.Equivalence
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Smooth.FullVertical
public import StacksFrontier.Deformation.Smooth.Unobstructed

/-!
# Base change of an algebraic stack along a morphism of base schemes

Let `g : S ⟶ S'` be a morphism of the big fppf site and `𝒳` an algebraic stack over `S'`. The
base change `𝒳_S = 𝒳 ×_{S'} S` is the 2-fibre product of the structure morphisms
`(Sch/S) ⟶ (Sch/S') ⟵ 𝒳` (Stacks 04T2), which comes with a 1-morphism to the stack represented by
`S/S'`, read as an algebraic stack over `S` by Construction B of Stacks 04X5.

The deformations of a point of `𝒳_S` over `S` are those of its image in `𝒳` over `S'`: an object
of `𝒳_S` over a scheme `T ⟶ S` is an object of `𝒳` over `T ⟶ S'` together with that
factorization through `g`, and an arrow of `𝒳` over an arrow of schemes over `S` lifts uniquely.

## Main definitions

* `AlgebraicGeometry.Stack.algebraicStackBaseChangeSquare`: the defining 2-fibre product square
  over `S'`.
* `AlgebraicGeometry.Stack.algebraicStackBaseChange`: the base change `𝒳_S`, an algebraic stack
  over `S`.
* `AlgebraicGeometry.Stack.algebraicStackBaseChangeLift`: the object of `𝒳_S` given by an object
  of `𝒳` and a factorization of its base through `g`.
* `Deformation.Artin.predeformationFunctorOfCompEqCompMap`: the functor of predeformation
  categories along a functor lying over `Over.map g`.

## Main results

* `AlgebraicGeometry.Stack.changeBaseAlgebraicStack_algebraicStackBaseChange`: Construction A of
  `𝒳_S` is the apex of the square.
* `Stack.exists_isSmoothLocus_changeBaseStructureMorphism_algebraicStackBaseChange`: a smooth
  locus of the first leg of the square is one of the structure 1-morphism of Construction A of
  `𝒳_S`, on the same objects.
* `Deformation.Artin.isSmooth_baseProjection_iff_of_comp_eq_comp_map`: unobstructedness of
  predeformation categories along a functor lying over `Over.map g`.
* `AlgebraicGeometry.Stack.isSmooth_baseProjection_algebraicStackBaseChange_iff`: a point of
  `𝒳_S` and its image in `𝒳` have the same unobstructedness.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS') (𝒳 : AlgebraicStacks.{u, w} B S' hS')

/-- The square defining the base change of `𝒳` along `g : S ⟶ S'`: the canonical 2-fibre product
of the structure morphisms of the stack represented by `S/S'` and of `𝒳`, in the 2-category of
algebraic stacks over `S'`. -/
abbrev algebraicStackBaseChangeSquare :
    Bicategory.TwoCommSq (structureMorphism B S' hS' (schemeStack.{u, w} B S' hS' (Over.mk g)))
      (structureMorphism B S' hS' 𝒳) :=
  twoFibreProductSquareAlgebraicStacks B S' hS' _ _

/-- The apex of `AlgebraicGeometry.Stack.algebraicStackBaseChangeSquare` together with its first
leg, the 1-morphism to the stack represented by `S/S'`. -/
abbrev algebraicStackBaseChangePair : AlgebraicStackPair.{u, w} B S S' hS hS' g :=
  ⟨(algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).pt,
    (algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).fst.hom⟩

/-- **The base change `𝒳_S = 𝒳 ×_{S'} S` of an algebraic stack `𝒳` over `S'` along
`g : S ⟶ S'`**, as an algebraic stack over `S`: Construction B of Stacks 04X5 applied to the
2-fibre product `(Sch/S) ×_{S'} 𝒳` with its projection to the stack represented by `S/S'`. -/
def algebraicStackBaseChange : AlgebraicStacks.{u, w} B S hS :=
  algebraicStackConstructionB B S S' hS hS' g (algebraicStackBaseChangePair B S S' hS hS' g 𝒳)

/-- Construction A of the base change is the defining pair. -/
theorem algebraicStackConstructionA_algebraicStackBaseChange :
    algebraicStackConstructionA B S S' hS hS' g (algebraicStackBaseChange B S S' hS hS' g 𝒳) =
      algebraicStackBaseChangePair B S S' hS hS' g 𝒳 :=
  (algebraicStackConstructionObjEquiv B S S' hS hS' g).right_inv _

/-- **Construction A of the base change `𝒳_S` is the 2-fibre product `(Sch/S) ×_{S'} 𝒳`.** -/
theorem changeBaseAlgebraicStack_algebraicStackBaseChange :
    changeBaseAlgebraicStack B S S' hS hS' g (algebraicStackBaseChange B S S' hS hS' g 𝒳) =
      (algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).pt :=
  congrArg Sigma.fst (algebraicStackConstructionA_algebraicStackBaseChange B S S' hS hS' g 𝒳)

/-- `AlgebraicGeometry.Stack.changeBaseAlgebraicStacks` of the base change `𝒳_S` is the 2-fibre
product `(Sch/S) ×_{S'} 𝒳`. -/
theorem changeBaseAlgebraicStacks_algebraicStackBaseChange :
    changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (algebraicStackBaseChange B S S' hS hS' g 𝒳) =
      (algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).pt :=
  changeBaseAlgebraicStack_algebraicStackBaseChange B S S' hS hS' g 𝒳

/-- The structure 1-morphism Construction A equips the base change with is the first leg of the
defining square, the two sources being identified by
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack_algebraicStackBaseChange`. -/
theorem changeBaseStructureHom_algebraicStackBaseChange :
    HEq (changeBaseStructureHom B S S' hS hS' g (algebraicStackBaseChange B S S' hS hS' g 𝒳))
      (algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).fst.hom :=
  (Sigma.mk.inj_iff.mp (algebraicStackConstructionA_algebraicStackBaseChange B S S' hS hS' g
    𝒳)).2

/-- A smooth locus of the 1-morphism of a pair to the stack represented by `S/S'` is a smooth
locus of the structure 1-morphism of Construction A of any algebraic stack over `S` that
Construction A sends to that pair. -/
theorem exists_isSmoothLocus_changeBaseStructureMorphism_of_eq (𝒳' : AlgebraicStacks.{u, w} B S hS)
    (X : AlgebraicStackPair.{u, w} B S S' hS hS' g)
    (h : algebraicStackConstructionA B S S' hS hS' g 𝒳' = X) (W' : OpenSubstack X.1)
    (hW' : IsSmoothLocus B S' hS'
      (Bicategory.InducedBicategory.mkHom X.2 : X.1 ⟶ schemeStack.{u, w} B S' hS' (Over.mk g)) W') :
    ∃ W'' : OpenSubstack (changeBaseAlgebraicStack B S S' hS hS' g 𝒳'),
      HEq W''.property W'.property ∧
        IsSmoothLocus B S' hS' (changeBaseStructureMorphism B S S' hS hS' g 𝒳') W'' := by
  subst h
  exact ⟨W', HEq.rfl, hW'⟩

/-- **The smooth locus of the first leg of the defining square is that of Construction A of the
base change.** A smooth locus `W'` of the projection `(Sch/S) ×_{S'} 𝒳 ⟶ (Sch/S)` cuts out a
smooth locus of the structure 1-morphism of Construction A of `𝒳_S` to the stack represented by
`S/S'`, on the same objects. -/
theorem exists_isSmoothLocus_changeBaseStructureMorphism_algebraicStackBaseChange
    (W' : OpenSubstack (algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).pt)
    (hW' : IsSmoothLocus B S' hS' (algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).fst W') :
    ∃ W'' : OpenSubstack
        (changeBaseAlgebraicStack B S S' hS hS' g (algebraicStackBaseChange B S S' hS hS' g 𝒳)),
      W''.property = W'.property ∧
        IsSmoothLocus B S' hS'
          (changeBaseStructureMorphism B S S' hS hS' g
            (algebraicStackBaseChange B S S' hS hS' g 𝒳)) W'' := by
  obtain ⟨W'', hp, hs⟩ := exists_isSmoothLocus_changeBaseStructureMorphism_of_eq B S S' hS hS' g
    (algebraicStackBaseChange B S S' hS hS' g 𝒳) (algebraicStackBaseChangePair B S S' hS hS' g 𝒳)
    (algebraicStackConstructionA_algebraicStackBaseChange B S S' hS hS' g 𝒳) W' hW'
  exact ⟨W'', eq_of_heq hp, hs⟩

end AlgebraicGeometry.Stack

/-! ### Predeformation categories along a functor over a change of base -/

namespace Deformation.Artin

open AlgebraicGeometry

universe u₁ v₁ u₂ v₂

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {S S' : Scheme.{u}} (iS : Spec (.of Λ) ⟶ S) (g' : S ⟶ S')
variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
variable (qX : X ⥤ Over S) (qY : Y ⥤ Over S') (Φ : X ⥤ Y)
  (hΦ : Φ ⋙ qY = qX ⋙ Over.map g')

/-- A functor `Φ` with `Φ ⋙ q_Y = q_X ⋙ Over.map g'` acts on the underlying morphisms of schemes
of arrows as `q_X` does, up to the identifications of the endpoints. -/
theorem map_left_eq_of_comp_eq_comp_map {a b : X} (f : a ⟶ b) :
    (qY.map (Φ.map f)).left =
      eqToHom (congrArg Over.left (Functor.congr_obj hΦ a)) ≫ (qX.map f).left ≫
        eqToHom (congrArg Over.left (Functor.congr_obj hΦ b)).symm := by
  have h := congrArg CommaMorphism.left (Functor.congr_hom hΦ f)
  simpa [Over.eqToHom_left] using h

include hΦ in
/-- The identity `map_left_eq_of_comp_eq_comp_map` with the endpoints identified with given
schemes on both sides. -/
theorem eqToHom_comp_map_left_comp_eqToHom_of_comp_eq_comp_map {a b : X} (f : a ⟶ b)
    {A A' : Scheme.{u}} (ha : (qX.obj a).left = A) (hb : (qX.obj b).left = A')
    (ha' : (qY.obj (Φ.obj a)).left = A) (hb' : (qY.obj (Φ.obj b)).left = A') :
    eqToHom ha'.symm ≫ (qY.map (Φ.map f)).left ≫ eqToHom hb' =
      eqToHom ha.symm ≫ (qX.map f).left ≫ eqToHom hb := by
  rw [map_left_eq_of_comp_eq_comp_map g' qX qY Φ hΦ f]
  simp

/-- `Spec` of a morphism of `𝒞_Λ` is a morphism over `Spec Λ`. -/
theorem spec_map_comp_spec_map_algebraMap {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (r : A ⟶ A') :
    Spec.map (CommRingCat.ofHom r.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact r.hom.comp_algebraMap

/-- `Spec` of the residue map of an object of `𝒞_Λ` is a morphism over `Spec Λ`. -/
theorem spec_map_residueMap_comp_spec_map_algebraMap (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Spec.map (CommRingCat.ofHom (residueMap A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residueMap_comp_algebraMap_self]

/-- A morphism `r` of schemes with `r ≫ a = b` is a morphism of slices `b ≫ i ⟶ a ≫ i`. -/
private def overMkHomMk {S U V W : Scheme.{u}} (i : W ⟶ S) (r : U ⟶ V) (a : V ⟶ W) (b : U ⟶ W)
    (h : r ≫ a = b) : Over.mk (b ≫ i) ⟶ Over.mk (a ≫ i) :=
  Over.homMk r (by simp [← h])

private theorem overMkHomMk_left {S U V W : Scheme.{u}} (i : W ⟶ S) (r : U ⟶ V) (a : V ⟶ W)
    (b : U ⟶ W) (h : r ≫ a = b) : Over.Hom.left (overMkHomMk i r a b h) = r :=
  rfl

variable (x₀ : X) (hx₀ : qX.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iS))
  (hy₀ : qY.obj (Φ.obj x₀) = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iS ≫ g'))

/-- The image under `Φ` of a deformation of `x₀`, a deformation of `Φ(x₀)` over `iS ≫ g'`. -/
def deformationObjectOfCompEqCompMap (d : DeformationObject iS qX x₀ hx₀) :
    DeformationObject (iS ≫ g') qY (Φ.obj x₀) hy₀ where
  algebra := d.algebra
  point := Φ.obj d.point
  arrow := Φ.map d.arrow
  base := (Functor.congr_obj hΦ d.point).trans ((congrArg (Over.map g').obj d.base).trans
    (congrArg Over.mk (Category.assoc _ _ _)))
  arrow_base := by
    refine (eqToHom_comp_map_left_comp_eqToHom_of_comp_eq_comp_map g' qX qY Φ hΦ d.arrow
      (congrArg Over.left hx₀) (congrArg Over.left d.base) (congrArg Over.left hy₀)
      (congrArg Over.left ((Functor.congr_obj hΦ d.point).trans
        (congrArg (Over.map g').obj d.base)))).trans d.arrow_base

/-- The image under `Φ` of a morphism of deformations of `x₀`. -/
def deformationMorphismOfCompEqCompMap {a b : DeformationObject iS qX x₀ hx₀}
    (m : DeformationMorphism iS qX x₀ hx₀ a b) :
    DeformationMorphism (iS ≫ g') qY (Φ.obj x₀) hy₀
      (deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀ a)
      (deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀ b) where
  ringHom := m.ringHom
  arrow := Φ.map m.arrow
  triangle := by
    change Φ.map b.arrow ≫ Φ.map m.arrow = Φ.map a.arrow
    rw [← Φ.map_comp, m.triangle]
  arrow_base := by
    refine (eqToHom_comp_map_left_comp_eqToHom_of_comp_eq_comp_map g' qX qY Φ hΦ m.arrow
      (congrArg Over.left b.base) (congrArg Over.left a.base)
      (congrArg Over.left ((Functor.congr_obj hΦ b.point).trans
        (congrArg (Over.map g').obj b.base)))
      (congrArg Over.left ((Functor.congr_obj hΦ a.point).trans
        (congrArg (Over.map g').obj a.base)))).trans m.arrow_base

/-- **The comparison of predeformation categories along `Φ`**: the functor
`𝓕_{X, k, x₀} ⥤ 𝓕_{Y, k, Φ(x₀)}` over `𝒞_Λ`, the first over `S` at `iS` and the second over
`S'` at `iS ≫ g'`. -/
def predeformationFunctorOfCompEqCompMap :
    letI := (predeformationCategory iS qX x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).category
    BasedFunctor (BasedCategory.ofFunctor (predeformationCategory iS qX x₀ hx₀).projection)
      (BasedCategory.ofFunctor (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).projection)
    where
  toFunctor :=
    { obj := deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀
      map := deformationMorphismOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀
      map_id _ := DeformationMorphism.ext_of_components _ _ _ _ rfl (Φ.map_id _)
      map_comp _ _ := DeformationMorphism.ext_of_components _ _ _ _ rfl (Φ.map_comp _ _) }
  w := rfl

/-- The comparison functor followed by the structure functor of `𝓕_{Y, k, Φ(x₀)}` is the structure
functor of `𝓕_{X, k, x₀}`. -/
theorem predeformationFunctorOfCompEqCompMap_comp_baseProjection :
    letI := (predeformationCategory iS qX x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).category
    BasedFunctor.comp (predeformationFunctorOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀)
        (baseProjection (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).projection) =
      baseProjection (predeformationCategory iS qX x₀ hx₀).projection :=
  rfl

/-- Lifting along `Φ` of an arrow of `Y` together with a compatible arrow of schemes over `S`
between the images under `q_X`. -/
abbrev LiftsCompEqCompMap : Prop :=
  ∀ {a b : X} (β : Φ.obj a ⟶ Φ.obj b) (γ : qX.obj a ⟶ qX.obj b),
    (qY.map β).left = eqToHom (congrArg Over.left (Functor.congr_obj hΦ a)) ≫ γ.left ≫
      eqToHom (congrArg Over.left (Functor.congr_obj hΦ b)).symm →
    ∃ α : a ⟶ b, Φ.map α = β ∧ qX.map α = γ

variable {g' qX qY Φ hΦ}

variable (hfull : LiftsCompEqCompMap g' qX qY Φ hΦ)
  (hobj : ∀ (y : Y) (T : Over S), qY.obj y = (Over.map g').obj T →
    ∃ x : X, Φ.obj x = y ∧ qX.obj x = T)

include hfull in
/-- **The comparison functor is full** when `Φ` is faithful and lifts arrows compatibly with a
given arrow of schemes over `S`. -/
theorem predeformationFunctorOfCompEqCompMap_full [Φ.Faithful] :
    letI := (predeformationCategory iS qX x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).category
    (predeformationFunctorOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀).toFunctor.Full := by
  let := (predeformationCategory iS qX x₀ hx₀).category
  let := (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).category
  refine ⟨fun {d₁ d₂} m' => ?_⟩
  let e₁ : DeformationObject iS qX x₀ hx₀ := d₁
  let e₂ : DeformationObject iS qX x₀ hx₀ := d₂
  let m'' : DeformationMorphism (iS ≫ g') qY (Φ.obj x₀) hy₀
      (deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀ e₁)
      (deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀ e₂) := m'
  let γ : qX.obj e₂.point ⟶ qX.obj e₁.point :=
    eqToHom e₂.base ≫ overMkHomMk iS _ (Spec.map (CommRingCat.ofHom (algebraMap Λ e₁.algebra))) _
      (spec_map_comp_spec_map_algebraMap m''.ringHom) ≫
      eqToHom e₁.base.symm
  have key : (qY.map m''.arrow).left =
      eqToHom (congrArg Over.left
        (deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀ e₂).base) ≫
        Spec.map (CommRingCat.ofHom m''.ringHom.hom.toRingHom) ≫
          eqToHom (congrArg Over.left
            (deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀ e₁).base).symm := by
    rw [← m''.arrow_base]
    simp
  obtain ⟨α, hα, hγ⟩ := hfull m''.arrow γ
    (key.trans (by simp [γ, Over.eqToHom_left]; try rfl))
  let m : DeformationMorphism iS qX x₀ hx₀ e₁ e₂ :=
    { ringHom := m''.ringHom
      arrow := α
      triangle := Φ.map_injective (by rw [Φ.map_comp, hα]; exact m''.triangle)
      arrow_base := by
        rw [hγ]
        simp [γ, Over.eqToHom_left]
        try rfl }
  exact ⟨m, DeformationMorphism.ext_of_components _ _ _ _ rfl hα⟩

include hfull hobj in
/-- **Every deformation of `Φ(x₀)` over `iS ≫ g'` is the image of a deformation of `x₀` over
`iS`**, when every object of `Y` with a factorization of its scheme through `g'` comes from `X`
compatibly with that factorization. -/
theorem exists_deformationObjectOfCompEqCompMap_eq
    (y : DeformationObject (iS ≫ g') qY (Φ.obj x₀) hy₀) :
    ∃ d : DeformationObject iS qX x₀ hx₀,
      deformationObjectOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀ d = y := by
  obtain ⟨A, yp, arr, base, ab⟩ := y
  obtain ⟨x, rfl, hxT⟩ := hobj yp (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iS))
    (base.trans (congrArg Over.mk (Category.assoc _ _ _).symm))
  let γ : qX.obj x₀ ⟶ qX.obj x :=
    eqToHom hx₀ ≫ overMkHomMk iS _ _ _ (spec_map_residueMap_comp_spec_map_algebraMap A) ≫
      eqToHom hxT.symm
  have key : (qY.map arr).left = eqToHom (congrArg Over.left hy₀) ≫
      Spec.map (CommRingCat.ofHom (residueMap A)) ≫ eqToHom (congrArg Over.left base).symm := by
    rw [← ab]
    simp
  obtain ⟨α, hα, hγ⟩ := hfull arr γ
    (key.trans (by simp [γ, overMkHomMk_left, Over.eqToHom_left]))
  refine ⟨⟨A, x, α, hxT, by rw [hγ]; simp [γ, overMkHomMk_left, Over.eqToHom_left]⟩, ?_⟩
  subst hα
  rfl

include hfull hobj in
/-- **Unobstructedness along a change of base.** Let `Φ : X ⥤ Y` be faithful with
`Φ ⋙ q_Y = q_X ⋙ Over.map g'`, lifting arrows compatibly with given arrows of schemes over `S`
and objects compatibly with given factorizations through `g'`. Then `𝓕_{X, k, x₀}` over `S` at
`iS` is unobstructed if and only if `𝓕_{Y, k, Φ(x₀)}` over `S'` at `iS ≫ g'` is. -/
theorem isSmooth_baseProjection_iff_of_comp_eq_comp_map [Φ.Faithful] :
    letI := (predeformationCategory iS qX x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).category
    IsSmooth (baseProjection (predeformationCategory iS qX x₀ hx₀).projection) ↔
      IsSmooth (baseProjection
        (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).projection) := by
  let := (predeformationCategory iS qX x₀ hx₀).category
  let := (predeformationCategory (iS ≫ g') qY (Φ.obj x₀) hy₀).category
  let Ψ := predeformationFunctorOfCompEqCompMap iS g' qX qY Φ hΦ x₀ hx₀ hy₀
  have hcomp := predeformationFunctorOfCompEqCompMap_comp_baseProjection iS g' qX qY Φ hΦ x₀ hx₀ hy₀
  have := predeformationFunctorOfCompEqCompMap_full iS x₀ hx₀ hy₀ (hΦ := hΦ) hfull
  have hex := exists_deformationObjectOfCompEqCompMap_eq iS x₀ hx₀ hy₀ (hΦ := hΦ) hfull hobj
  have : Ψ.toFunctor.EssSurj := ⟨fun y => by
    obtain ⟨d, hd⟩ := hex y
    exact ⟨d, ⟨eqToIso hd⟩⟩⟩
  constructor
  · intro h
    rw [← hcomp] at h
    exact isSmooth_of_essSurj_comp Ψ _ h
  · intro h
    rw [← hcomp]
    refine isSmooth_comp _ _ (isSmooth_of_full_of_exists_vertical Ψ fun y => ?_) h
    obtain ⟨d, hd⟩ := hex y
    subst hd
    exact ⟨d, 𝟙 _, IsHomLift.id rfl⟩

end Deformation.Artin

/-! ### The predeformation categories of the base change -/

namespace AlgebraicGeometry.Stack

open Deformation Deformation.Artin

/-- An object of a slice equal to another has structure morphism the other's, after identifying
the sources. -/
theorem _root_.CategoryTheory.Over.hom_eq_eqToHom_comp_hom_of_eq {C : Type*} [Category C] {Z : C}
    {A A' : Over Z} (h : A = A') : A.hom = eqToHom (congrArg Over.left h) ≫ A'.hom := by
  subst h
  simp

/-- Precomposing the structure morphism by an `eqToHom` does not change the object of the slice
up to equality. -/
theorem _root_.CategoryTheory.Over.mk_eqToHom_comp {C : Type*} [Category C] {Z : C} {A A' : C}
    (h : A = A') (f : A' ⟶ Z) : Over.mk (eqToHom h ≫ f) = Over.mk f := by
  subst h
  simp

/-- Conjugating `P = e₁ ≫ X ≫ e₂` by further canonical casts gives `X` conjugated by casts. -/
theorem _root_.CategoryTheory.eqToHom_comp_comp_eqToHom_eq_of_eq {C : Type*} [Category C]
    {a b c d e f : C} (X : c ⟶ d) (P : b ⟶ e) (f₁ : b = c) (f₂ : d = e)
    (hP : P = eqToHom f₁ ≫ X ≫ eqToHom f₂) (e₁ : a = b) (e₂ : e = f) (e₃ : a = c) (e₄ : d = f) :
    eqToHom e₁ ≫ P ≫ eqToHom e₂ = eqToHom e₃ ≫ X ≫ eqToHom e₄ := by
  subst hP
  simp

/-- A square whose two sides are a morphism and its conjugate by canonical casts commutes. -/
theorem _root_.CategoryTheory.comp_eq_comp_of_eq_eqToHom {C : Type*} [Category C] {b c d e : C}
    (X : c ⟶ d) (P : b ⟶ e) (f₁ : b = c) (f₂ : d = e) (hP : P = eqToHom f₁ ≫ X ≫ eqToHom f₂)
    (I : c ⟶ b) (J : d ⟶ e) (ea : c = b) (eb : d = e) (hI : I = eqToHom ea)
    (hJ : J = eqToHom eb) : X ≫ J = I ≫ P := by
  subst hP hI hJ
  simp

/-- A morphism of a slice which is a canonical cast composed with an identity has a canonical cast
as its underlying morphism. -/
theorem _root_.CategoryTheory.Over.left_eq_eqToHom_of_eq_eqToHom_comp_id_comp_eqToHom
    {C : Type*} [Category C] {Z : C} {A M B : Over Z} (u : A ⟶ B) (e₁ : A = M) (e₂ : M = B)
    (hu : u = eqToHom e₁ ≫ 𝟙 M ≫ eqToHom e₂) :
    u.left = eqToHom (congrArg Over.left (e₁.trans e₂)) := by
  subst hu e₁ e₂
  simp

/-- The underlying morphism of a morphism of a full subcategory conjugated by canonical casts. -/
theorem _root_.CategoryTheory.ObjectProperty.hom_eqToHom_comp_homMk_comp_eqToHom {C : Type*}
    [Category C] {P : ObjectProperty C} {X Y Z W : P.FullSubcategory} (e₁ : X = Y)
    (f : Y.obj ⟶ Z.obj) (e₂ : Z = W) :
    (eqToHom e₁ ≫ ObjectProperty.homMk f ≫ eqToHom e₂).hom =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj e₁) ≫ f ≫
        eqToHom (congrArg ObjectProperty.FullSubcategory.obj e₂) := by
  subst e₁ e₂
  simp

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS') (𝒳 : AlgebraicStacks.{u, w} B S' hS')

/-- The projection `𝒳_S ⥤ 𝒳` of the base change: the second leg of the defining square. -/
abbrev algebraicStackBaseChangeProjection :
    (algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.obj ⥤ 𝒳.val.val.obj :=
  (algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳).snd.hom.hom.toFunctor

/-- The projection `𝒳_S ⥤ 𝒳` lies over the relocalization `Over.map g`, read in the slices of
schemes. -/
theorem algebraicStackBaseChangeProjection_comp :
    algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳 ⋙ (𝒳.val.val.p ⋙ Over.post B.inclusion) =
      ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) ⋙
        Over.map (B.inclusion.map g) := by
  let P := algebraicStackBaseChangeSquare B S S' hS hS' g 𝒳
  have h1 : P.snd.hom.hom.toFunctor ⋙ 𝒳.val.val.p = P.pt.val.val.p := P.snd.hom.hom.w
  have h2 : P.fst.hom.hom.toFunctor ⋙ Over.forget (Over.mk g) = P.pt.val.val.p :=
    P.fst.hom.hom.w
  calc P.snd.hom.hom.toFunctor ⋙ (𝒳.val.val.p ⋙ Over.post B.inclusion)
      = (P.fst.hom.hom.toFunctor ⋙ Over.forget (Over.mk g)) ⋙ Over.post B.inclusion := by
        rw [← Functor.assoc, h1, h2]
    _ = _ := congrArg (· ⋙ Over.post B.inclusion)
      (Over.comp_iteratedSliceForward_comp_map g P.fst.hom.hom.toFunctor).symm

/-- The object of the base change `𝒳_S` given by an object `x` of `𝒳` together with a
factorization through `g` of the morphism of its base to `S'`. -/
def algebraicStackBaseChangeLift (x : 𝒳.val.val.obj) (φ : 𝒳.val.val.p.obj x ⟶ Over.mk g) :
    (algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.obj where
  base := 𝒳.val.val.p.obj x
  x := Over.mk φ
  y := x
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id (Functor.congr_obj (structureMorphism B S' hS' 𝒳).hom.hom.w x)

/-- The projection of `AlgebraicGeometry.Stack.algebraicStackBaseChangeLift` to `𝒳` is the given
object. -/
@[simp]
theorem algebraicStackBaseChangeProjection_obj_lift (x : 𝒳.val.val.obj)
    (φ : 𝒳.val.val.p.obj x ⟶ Over.mk g) :
    (algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj
      (algebraicStackBaseChangeLift B S S' hS hS' g 𝒳 x φ) = x :=
  rfl

/-- `AlgebraicGeometry.Stack.algebraicStackBaseChangeLift` lies over the factorization through
`g`. -/
theorem algebraicStackBaseChangeLift_post (x : 𝒳.val.val.obj)
    (φ : 𝒳.val.val.p.obj x ⟶ Over.mk g) :
    ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion).obj
      (algebraicStackBaseChangeLift B S S' hS hS' g 𝒳 x φ) = Over.mk (B.inclusion.map φ.left) :=
  rfl

/-- The factorization through `g` of the base of an object `y` of `𝒳` given by a scheme `T` over
`S` whose image over `S'` is the scheme of `y`. -/
def algebraicStackBaseChangeFactor (y : 𝒳.val.val.obj) (T : Over S)
    (hT : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj y = (Over.map (B.inclusion.map g)).obj T) :
    𝒳.val.val.p.obj y ⟶ Over.mk g :=
  Over.homMk (ObjectProperty.homMk (eqToHom (congrArg Over.left hT) ≫ T.hom)) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    change (eqToHom (congrArg Over.left hT) ≫ T.hom) ≫ B.inclusion.map g =
      ((𝒳.val.val.p ⋙ Over.post B.inclusion).obj y).hom
    rw [Over.hom_eq_eqToHom_comp_hom_of_eq hT, Category.assoc]
    rfl)

/-- The lift of `y` along `AlgebraicGeometry.Stack.algebraicStackBaseChangeFactor` lies over
`T`. -/
theorem algebraicStackBaseChangeLift_factor_post (y : 𝒳.val.val.obj) (T : Over S)
    (hT : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj y = (Over.map (B.inclusion.map g)).obj T) :
    ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion).obj
      (algebraicStackBaseChangeLift B S S' hS hS' g 𝒳 y
        (algebraicStackBaseChangeFactor B S S' hS hS' g 𝒳 y T hT)) = T := by
  rw [algebraicStackBaseChangeLift_post]
  exact Over.mk_eqToHom_comp _ _

/-- Every object of `𝒳` with a factorization through `g` of its scheme, read over `S'`, is the
projection of an object of `𝒳_S` over that factorization. -/
theorem exists_algebraicStackBaseChangeProjection_obj_eq (y : 𝒳.val.val.obj) (T : Over S)
    (hT : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj y = (Over.map (B.inclusion.map g)).obj T) :
    ∃ ξ : (algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.obj,
      (algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj ξ = y ∧
        ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion).obj ξ =
          T :=
  ⟨_, rfl, algebraicStackBaseChangeLift_factor_post B S S' hS hS' g 𝒳 y T hT⟩

/-- **The projection `𝒳_S ⥤ 𝒳` is faithful**: a morphism of the 2-fibre product is determined by
its component in `𝒳`, its component in the slice over `S/S'` lying over the same morphism. -/
instance algebraicStackBaseChangeProjection_faithful :
    (algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).Faithful where
  map_injective {ξ ξ'} {m₁ m₂} h := by
    obtain ⟨hb₁, a₁, b₁, ha₁, hb₁', w₁⟩ := m₁
    obtain ⟨hb₂, a₂, b₂, ha₂, hb₂', w₂⟩ := m₂
    change b₁ = b₂ at h
    subst h
    have k := (IsHomLift.fac' 𝒳.val.val.p hb₁ b₁).symm.trans (IsHomLift.fac' 𝒳.val.val.p hb₂ b₁)
    have hb : hb₁ = hb₂ := (cancel_mono _).1 ((cancel_epi _).1 k)
    subst hb
    have ka := (IsHomLift.fac' (schemeStack.{u, w} B S' hS' (Over.mk g)).val.val.p hb₁
      a₁).trans (IsHomLift.fac' (schemeStack.{u, w} B S' hS' (Over.mk g)).val.val.p hb₁ a₂).symm
    have ha : a₁ = a₂ := Over.OverMorphism.ext ka
    subst ha
    rfl

/-- **Arrows of `𝒳` lift to `𝒳_S` over given arrows of schemes over `S`**: an arrow `β` of `𝒳`
between projections of objects of `𝒳_S`, together with an arrow `γ` over `S` of their schemes
with the same underlying morphism, is the projection of an arrow of `𝒳_S` over `γ`. -/
theorem liftsCompEqCompMap_algebraicStackBaseChangeProjection :
    LiftsCompEqCompMap (B.inclusion.map g)
    ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion)
    (𝒳.val.val.p ⋙ Over.post B.inclusion) (algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳)
    (algebraicStackBaseChangeProjection_comp B S S' hS hS' g 𝒳) := by
  intro ξa ξb β γ hγ
  have hγB : (𝒳.val.val.p.map β).left =
      eqToHom (congrArg Over.left (ξa.hy.trans ξa.hx.symm)) ≫ ObjectProperty.homMk γ.left ≫
        eqToHom (congrArg Over.left (ξb.hy.trans ξb.hx.symm)).symm := by
    apply ObjectProperty.hom_ext
    exact hγ.trans (ObjectProperty.hom_eqToHom_comp_homMk_comp_eqToHom _ _ _).symm
  let aL : ξa.x.left ⟶ ξb.x.left := Over.homMk (ObjectProperty.homMk γ.left) (by
    apply B.inclusion.map_injective
    have hwa := Over.w ξa.x.hom
    have hwb := Over.w ξb.x.hom
    rw [← hwa, ← hwb]
    change γ.left ≫ (_ ≫ B.inclusion.map g) = _ ≫ B.inclusion.map g
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.inclusion.map g) (Over.w γ)))
  have hw : aL ≫ ξb.x.hom = ξa.x.hom :=
    Over.OverMorphism.ext (B.inclusion.map_injective (Over.w γ))
  let a : ξa.x ⟶ ξb.x := Over.homMk aL hw
  refine ⟨TwoFibreProductOver.Hom.mk' a β ?_ ?_, rfl, ?_⟩
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left]
    exact eqToHom_comp_comp_eqToHom_eq_of_eq _ _ _ _ hγB _ _ _ _
  · have k := fun ξ : (algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.obj =>
      have := ξ.vertical
      Over.left_eq_eqToHom_of_eq_eqToHom_comp_id_comp_eqToHom _ _ _ (IsHomLift.fac'
        (schemeStack.{u, w} B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.val.p (𝟙 ξ.base) ξ.iso.hom)
    exact Over.OverMorphism.ext <| Over.OverMorphism.ext <|
      comp_eq_comp_of_eq_eqToHom (ObjectProperty.homMk γ.left) (𝒳.val.val.p.map β).left _ _
        hγB _ _ _ _ (k ξa) (k ξb)
  · rfl

/-- **Unobstructedness of a point of the base change `𝒳_S`.** Let `x₀` be an object of `𝒳` with a
factorization `φ₀` through `g : S ⟶ S'` of the morphism of its base to `S'`, and let `x₀'` be the
corresponding object of `𝒳_S = 𝒳 ×_{S'} S`. If `x₀'` lies over `Spec k ⟶ Spec Λ ⟶ S` (and hence
`x₀` over `Spec k ⟶ Spec Λ ⟶ S ⟶ S'`), the predeformation category of `x₀'` over `𝒞_Λ` for the
stack `𝒳_S` over `S` is unobstructed exactly when that of `x₀` for the stack `𝒳` over `S'` is. -/
theorem isSmooth_baseProjection_algebraicStackBaseChange_iff {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] (iS : Spec (.of Λ) ⟶ S) (x₀ : 𝒳.val.val.obj)
    (φ₀ : 𝒳.val.val.p.obj x₀ ⟶ Over.mk g)
    (hx₀' : ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion).obj
      (algebraicStackBaseChangeLift B S S' hS hS' g 𝒳 x₀ φ₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iS))
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iS ≫ B.inclusion.map g)) :
    letI := (predeformationCategory iS
      ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion)
      (algebraicStackBaseChangeLift B S S' hS hS' g 𝒳 x₀ φ₀) hx₀').category
    letI := (predeformationCategory (iS ≫ B.inclusion.map g)
      (𝒳.val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
    IsSmooth (baseProjection (predeformationCategory iS
      ((algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion)
      (algebraicStackBaseChangeLift B S S' hS hS' g 𝒳 x₀ φ₀) hx₀').projection) ↔
    IsSmooth (baseProjection (predeformationCategory (iS ≫ B.inclusion.map g)
      (𝒳.val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :=
  isSmooth_baseProjection_iff_of_comp_eq_comp_map iS
    (hΦ := algebraicStackBaseChangeProjection_comp B S S' hS hS' g 𝒳)
    (algebraicStackBaseChangeLift B S S' hS hS' g 𝒳 x₀ φ₀) hx₀' hx₀
    (liftsCompEqCompMap_algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳)
    (exists_algebraicStackBaseChangeProjection_obj_eq B S S' hS hS' g 𝒳)

end AlgebraicGeometry.Stack

end
