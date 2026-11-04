module

public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceFormallySmooth
public import StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange

/-!
# A local retraction at a versal point

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `x` be an object of
`𝒳` over `U` and `ξ` an object over `U'`, and let the 2-fibre product
`𝒵 = (Sch/U') ×_{ξ, 𝒳, x} (Sch/U)` be represented over `U'` by an algebraic space `F`, through
an equivalence `e` over the site. An object `Q` of `𝒵` over `T` has a section of `F` over `T`,
and a section over `D` restricting along `f : T ⟶ D` to the section of `Q` receives an arrow of
`𝒵` from `Q` over `f`. An object of `𝒵` over `T` carries an arrow of `𝒳` from the pullback of
`ξ` to `T` into `x`, compatibly with restriction.

When `r : x ⟶ ξ` lies over a first-order thickening `U ⟶ U'` and `x` is versal at `u₀`, these
facts turn the smoothness of `F ⟶ U'` at the image of `u₀` (Stacks 0CXM) and the infinitesimal
lifting property of smooth morphisms of algebraic spaces (Stacks 04AM) into a retraction of `r`
over a neighbourhood of the image of `u₀`: the step shared by the proofs of Stacks 0G2K and
Stacks 0CXU.

## Main definitions

* `Deformation.Artin.BaseChange.sectionOf`: the section of `F` attached to an object of `𝒵`.
* `Deformation.Artin.BaseChange.toFirst`, `Deformation.Artin.BaseChange.toFirstOf`: the arrows of
  `𝒳` into `x` attached to an object of `𝒵` and to a section of `F`.
* `Deformation.Artin.BaseChange.objOfArrows`: the object of `𝒵` attached to arrows `z ⟶ x` and
  `z ⟶ ξ`.

## Main results

* `Deformation.Artin.BaseChange.map_sectionOf`,
  `Deformation.Artin.BaseChange.exists_hom_of_map_eq_sectionOf`: sections and arrows of `𝒵`.
* `AlgebraicGeometry.Space.exists_section_extension_of_isSmooth`: a section of a smooth open
  subspace of an algebraic space extends across a first-order thickening of the base, over a
  neighbourhood of a point.
* `Deformation.Artin.BaseChange.exists_localRetraction_of_isVersalAt`: the local retraction.

## Implementation notes

The source extends the section `U ⟶ Z` of `Z ⟶ U'` over all of `U'` after shrinking `U` to an
affine on which `Z ⟶ U'` is smooth; here the extension is made over an affine neighbourhood of
the image of `u₀`, which is all the contradiction derived in Stacks 0G2K and 0CXU uses.

## References

* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


/-! ### Extending a section of a smooth algebraic space across a first-order thickening -/

namespace AlgebraicGeometry.Space

universe u

section SectionExtension

variable {B : BigFppfSite.{u}} {Y : Scheme.{u}} {hY : B.Contains Y}

/-- Any two elements of a value of the terminal presheaf are equal. -/
lemma terminal_obj_subsingleton (T : BigFppfOver B Y hY)
    (a b : (⊤_ ((BigFppfOver B Y hY)ᵒᵖ ⥤ Type u)).obj (op T)) : a = b := by
  have h := terminal.hom_ext (yonedaEquiv.symm a) (yonedaEquiv.symm b)
  simpa using congrArg yonedaEquiv h

/-- **A section of a smooth open subspace extends across a first-order thickening.** Let `F` be
a presheaf on the big fppf site of `Y` with an open subspace `G` smooth over `Y`, let `T₀` be an
object of the site whose structure morphism `ρ : T₀ ⟶ Y` is a first-order thickening, and let
`s₀` be a section of `F` over `T₀` whose point at `u₀` lies in `G`. Then there is an open
neighbourhood `T' ⊆ Y` of `ρ u₀` and a section `z` of `F` over `T'` agreeing with `s₀` on every
object of the site mapping both to `T₀` and to `T'`.

This is Stacks 04AM (smooth implies formally smooth) applied to `G ⟶ Y` over the affine
neighbourhood `T'` and its preimage in `T₀`, which is a first-order thickening of it. -/
theorem exists_section_extension_of_isSmooth {F : (BigFppfOver B Y hY)ᵒᵖ ⥤ Type u}
    (G : Subfunctor F) (hG : IsOpenSubspace B Y hY G)
    (hsm : IsSmooth B Y hY (G.ι ≫ terminal.from F)) (T₀ : BigFppfOver B Y hY)
    (hT₀ : Stacks.Thickenings.IsFirstOrderThickening (B.inclusion.map T₀.hom))
    (s₀ : F.obj (op T₀)) (u₀ : (BigFppfOver.toScheme B Y hY).obj T₀)
    (hu₀ : pointsMap B Y hY (yoneda.obj T₀) (yonedaEquiv.symm s₀)
        ((schemePointRepresentative B Y hY T₀ u₀).class B Y hY (yoneda.obj T₀)) ∈
      Set.range (pointsMap B Y hY G.toFunctor G.ι)) :
    ∃ (T' : BigFppfOver B Y hY) (_ : AlgebraicGeometry.IsOpenImmersion (B.inclusion.map T'.hom))
      (t₀ : (BigFppfOver.toScheme B Y hY).obj T'),
      B.inclusion.map T'.hom t₀ = B.inclusion.map T₀.hom u₀ ∧
      ∃ z : F.obj (op T'), ∀ (T₁ : BigFppfOver B Y hY) (a : T₁ ⟶ T₀) (b : T₁ ⟶ T'),
        F.map a.op s₀ = F.map b.op z := by
  classical
  let V := BigFppfOver.toScheme B Y hY
  let ρ : V.obj T₀ ⟶ Y := B.inclusion.map T₀.hom
  let ι : yoneda.obj T₀ ⟶ F := yonedaEquiv.symm s₀
  obtain ⟨Vs, hVs⟩ := exists_opens_mem_iff_mem_range_pointsMap_ι B Y hY hG T₀ ι
  have hu₀Vs : u₀ ∈ Vs := by
    simpa only [schemePointRepresentative_point] using
      (hVs (schemePointRepresentative B Y hY T₀ u₀)).mp hu₀
  have : AlgebraicGeometry.IsClosedImmersion ρ := hT₀.1
  have homeo : IsHomeomorph ρ.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨ρ.isClosedEmbedding.isEmbedding, hT₀.isThickening.2⟩
  let Ω : Y.Opens := ⟨ρ.base '' (Vs : Set (V.obj T₀)), homeo.isOpenMap _ Vs.isOpen⟩
  obtain ⟨W', hW'aff, hW'mem, hW'Ω⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (U := Ω) (x := ρ.base u₀) ⟨u₀, hu₀Vs, rfl⟩
  let W : (V.obj T₀).Opens := ρ ⁻¹ᵁ W'
  have hWVs : (W : Set (V.obj T₀)) ⊆ Vs := by
    intro t ht
    obtain ⟨v, hv, hvt⟩ := hW'Ω ht
    rwa [homeo.injective hvt] at hv
  have hW'c : B.Contains W' := lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion W'.ι) hY
  have hWc : B.Contains W := lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion W.ι) T₀.left.2
  let T' : BigFppfOver B Y hY := Over.mk (ObjectProperty.homMk W'.ι : B.obj hW'c ⟶ B.obj hY)
  let T : BigFppfOver B Y hY :=
    Over.mk (ObjectProperty.homMk (W.ι ≫ ρ) : B.obj hWc ⟶ B.obj hY)
  let j : T ⟶ T₀ := Over.homMk (ObjectProperty.homMk W.ι : B.obj hWc ⟶ T₀.left) rfl
  let i : T ⟶ T' := Over.homMk (ObjectProperty.homMk (ρ ∣_ W') : B.obj hWc ⟶ B.obj hW'c)
    (ObjectProperty.hom_ext _ (morphismRestrict_ι ρ W'))
  have hfo : Stacks.Thickenings.IsFirstOrderThickening (ρ ∣_ W') :=
    Stacks.Smooth.isFirstOrderThickening_morphismRestrict hT₀ W'
  have : IsAffine (V.obj T') := hW'aff
  have : IsAffine W' := hW'aff
  have : AlgebraicGeometry.IsClosedImmersion (ρ ∣_ W') := hfo.1
  have : IsAffine (V.obj T) := isAffine_of_isAffineHom (ρ ∣_ W')
  obtain ⟨τ, hτ⟩ := exists_lift_of_range_pointsMap_subset (yoneda.map j ≫ ι) hG (by
    rintro _ ⟨pt, rfl⟩
    induction pt using Quot.ind with
    | mk q =>
      rw [pointsMap_comp, Function.comp_apply]
      show pointsMap B Y hY (yoneda.obj T₀) ι
        ((FieldValuedPoint.map B Y hY (yoneda.obj T) (yoneda.map j) q).class B Y hY _) ∈ _
      rw [hVs, schemePoint_map_yoneda]
      exact hWVs (show (V.map j).base (schemePoint B Y hY T q) ∈ W from
        (schemePoint B Y hY T q).2))
  have hFS := formallySmooth_of_isSmooth_unconditional hG.1 (isAlgebraicSpace_terminal B Y hY)
    (G.ι ≫ terminal.from F) hsm
  obtain ⟨z, hz, -⟩ := hFS T T' inferInstance inferInstance i ⟨hfo.1, hfo.2⟩
    (yonedaEquiv τ) ((terminal.from (yoneda.obj T')).app (op T') (𝟙 T'))
    (terminal_obj_subsingleton _ _ _)
  let zF : F.obj (op T') := G.ι.app (op T') z
  have hzF : F.map i.op zF = F.map j.op s₀ := by
    have h₁ := congrArg (G.ι.app (op T)) hz
    rw [NatTrans.naturality_apply] at h₁
    refine h₁.trans ?_
    have h₂ := congrArg (fun k => yonedaEquiv k) hτ
    simp only [yonedaEquiv_comp] at h₂
    refine h₂.trans ?_
    simp only [ι]
    rw [yonedaEquiv_yoneda_map]
    exact yonedaEquiv_symm_app_apply s₀ (op T) j
  refine ⟨T', inferInstanceAs (AlgebraicGeometry.IsOpenImmersion W'.ι), ⟨ρ.base u₀, hW'mem⟩, rfl,
    zF, ?_⟩
  intro T₁ a b
  have hw : V.map b ≫ W'.ι = V.map a ≫ ρ := by
    have h := congrArg B.inclusion.map ((Over.w b).trans (Over.w a).symm)
    rwa [B.inclusion.map_comp, B.inclusion.map_comp] at h
  let hpb := isPullback_morphismRestrict ρ W'
  let c₀ := hpb.lift (V.map b) (V.map a) hw
  let c : T₁ ⟶ T := Over.homMk (ObjectProperty.homMk c₀ : T₁.left ⟶ B.obj hWc) (by
    apply ObjectProperty.hom_ext
    show c₀ ≫ W.ι ≫ ρ = B.inclusion.map T₁.hom
    rw [← Category.assoc, hpb.lift_snd]
    exact (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w a)))
  have hca : c ≫ j = a :=
    Over.OverMorphism.ext <| ObjectProperty.hom_ext _ (hpb.lift_snd ..)
  have hcb : c ≫ i = b :=
    Over.OverMorphism.ext <| ObjectProperty.hom_ext _ (hpb.lift_fst ..)
  rw [← hca, ← hcb, op_comp, op_comp, FunctorToTypes.map_comp_apply,
    FunctorToTypes.map_comp_apply, hzF]

end SectionExtension

end AlgebraicGeometry.Space

namespace Deformation.Artin.BaseChange

universe u v w

attribute [local implicit_reducible] CategoryTheory.Over.post
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.TwoYoneda.liftBased
  CategoryTheory.Functor.TwoYoneda.liftFunctor
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.TwoFibreProductOver.snd
  CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc
  CategoryTheory.Pseudofunctor.CoGrothendieck.forget
  CategoryTheory.Bicategory.InducedBicategory

/-! ### Sections of a presheaf read as objects of its category of elements -/

section Elements

variable {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type u)

/-- The arrow of the category attached to a presheaf of sets between two of its objects, over a
morphism along which the second section restricts to the first. -/
def elementsHom (a b : (presheafOfCategories (F ⋙ typeToCat)).obj) (g : a.base ⟶ b.base)
    (h : F.map g.op b.fiber.as = a.fiber.as) : a ⟶ b :=
  ⟨g, Discrete.eqToHom' h.symm⟩

/-- The base of `elementsHom F a b g h` is `g`. -/
@[simp]
lemma elementsHom_base (a b : (presheafOfCategories (F ⋙ typeToCat)).obj) (g : a.base ⟶ b.base)
    (h : F.map g.op b.fiber.as = a.fiber.as) : (elementsHom F a b g h).base = g := rfl

/-- An arrow of the category attached to a presheaf of sets restricts the section of its target
to the section of its source. -/
lemma map_fiber_of_hom {a b : (presheafOfCategories (F ⋙ typeToCat)).obj} (m : a ⟶ b) :
    F.map m.base.op b.fiber.as = a.fiber.as :=
  (Discrete.eq_of_hom m.fiber).symm

end Elements


/-! ### The section of an object of the 2-fibre product -/

section Sections

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))
  {U V : AlgebraicGeometry.BigFppfOver B S hS} {x : 𝒳.val.obj} {hx : 𝒳.val.p.obj x = U}
  {y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj}
  {F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u}

/-- The 2-fibre product `(Sch/V) ×_{y, 𝒳, x} (Sch/U)` represented by
`Deformation.Artin.BaseChange.BaseChangeEquivalence`. -/
abbrev BaseChangeProduct (U V : AlgebraicGeometry.BigFppfOver B S hS) (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj) :=
  TwoFibreProductOver (Over.map V.hom) (Over.forget U) 𝒳.val.p y
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor

variable {B S hS 𝒳}

/-- The base of the object of the category attached to `F` which corresponds to an object of
the 2-fibre product is the base of that object. -/
lemma base_hom_obj (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (Q : BaseChangeProduct B S hS 𝒳 U V x hx y) : (e.hom.functor.obj Q).base = Q.x :=
  Functor.congr_obj e.hom.w Q

/-- The base of the object of the 2-fibre product attached to a section of `F` is the base of
that section. -/
lemma inv_obj_x (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (a : (presheafOfCategories (F ⋙ typeToCat)).obj) : (e.inv.functor.obj a).x = a.base :=
  Functor.congr_obj e.inv.w a

/-- The section of `F` attached to an object of the 2-fibre product. -/
def sectionOf (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (Q : BaseChangeProduct B S hS 𝒳 U V x hx y) : F.obj (op Q.x) :=
  F.map (eqToHom (base_hom_obj e Q).symm).op (e.hom.functor.obj Q).fiber.as

/-- The base morphism of the image of an arrow of the 2-fibre product. -/
lemma hom_map_base (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {Q Q' : BaseChangeProduct B S hS 𝒳 U V x hx y} (g : Q ⟶ Q') :
    (e.hom.functor.map g).base =
      eqToHom (base_hom_obj e Q) ≫ g.a ≫ eqToHom (base_hom_obj e Q').symm := by
  have h := Functor.congr_hom e.hom.w g
  exact h

/-- **Sections are compatible with arrows.** The section of the target of an arrow of the
2-fibre product restricts along its base morphism to the section of its source. -/
lemma map_sectionOf (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {Q Q' : BaseChangeProduct B S hS 𝒳 U V x hx y} (g : Q ⟶ Q') :
    F.map g.a.op (sectionOf e Q') = sectionOf e Q := by
  have h := map_fiber_of_hom F (e.hom.functor.map g)
  rw [hom_map_base] at h
  simp only [sectionOf, ← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [← h, ← FunctorToTypes.map_comp_apply, ← op_comp]
  simp

/-- The base morphism of the image of an arrow of the category attached to `F`. -/
lemma inv_map_a (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {a b : (presheafOfCategories (F ⋙ typeToCat)).obj} (m : a ⟶ b) :
    (e.inv.functor.map m).a =
      eqToHom (inv_obj_x e a) ≫ m.base ≫ eqToHom (inv_obj_x e b).symm := by
  have h := Functor.congr_hom e.inv.w m
  exact h

/-- The unit of the equivalence lies over identities. -/
lemma unit_app_a (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (Q : BaseChangeProduct B S hS 𝒳 U V x hx y) :
    (e.unitIso.hom.app Q).a = eqToHom ((base_hom_obj e Q).symm.trans
      (inv_obj_x e (e.hom.functor.obj Q)).symm) := by
  have h := congrArg (fun n => n.app Q) e.unit_over
  simp only [Functor.whiskerRight_app, eqToHom_app] at h
  exact h

/-- **Arrows from restrictions of sections.** If a section `z` of `F` over `D` restricts along
`f : T ⟶ D` to the section of an object `Q` of the 2-fibre product over `T`, then `Q` has an
arrow over `f` to the object attached to `z`. -/
lemma exists_hom_of_map_eq_sectionOf (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (Q : BaseChangeProduct B S hS 𝒳 U V x hx y) {D : AlgebraicGeometry.BigFppfOver B V.left.1
      V.left.2} (z : F.obj (op D)) (f : Q.x ⟶ D) (h : F.map f.op z = sectionOf e Q) :
    ∃ g : Q ⟶ e.inv.functor.obj ⟨D, ⟨z⟩⟩, g.a = f ≫ eqToHom (inv_obj_x e ⟨D, ⟨z⟩⟩).symm := by
  let t := e.hom.functor.obj Q
  have ht : t.base = Q.x := base_hom_obj e Q
  have h' : F.map (eqToHom ht ≫ f).op z = t.fiber.as := by
    rw [op_comp, FunctorToTypes.map_comp_apply, h, sectionOf, ← FunctorToTypes.map_comp_apply,
      ← op_comp]
    simp only [eqToHom_trans, eqToHom_refl, op_id]
    rw [F.map_id]
    rfl
  let m : t ⟶ ⟨D, ⟨z⟩⟩ := elementsHom F t ⟨D, ⟨z⟩⟩ (eqToHom ht ≫ f) h'
  refine ⟨e.unitIso.hom.app Q ≫ e.inv.functor.map m, ?_⟩
  show (e.unitIso.hom.app Q).a ≫ (e.inv.functor.map m).a = _
  rw [unit_app_a, inv_map_a]
  simp [m]

end Sections

/-! ### The arrow to `x` attached to an object of the 2-fibre product -/

section ToFirst

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS)}
  {U V : AlgebraicGeometry.BigFppfOver B S hS} {x : 𝒳.val.obj} {hx : 𝒳.val.p.obj x = U}
  {y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj}
  {F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u}

/-- The arrow of `𝒳` from the pullback of `y` to the base of an object of the 2-fibre product
into `x`: the comparison isomorphism of the object followed by the chosen arrow to `x`. -/
def toFirst (Q : BaseChangeProduct B S hS 𝒳 U V x hx y) : y.obj Q.x ⟶ x :=
  Q.iso.hom ≫ (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩ Q.y).φ

/-- The arrows to `x` are compatible with arrows of the 2-fibre product. -/
lemma map_a_toFirst {Q Q' : BaseChangeProduct B S hS 𝒳 U V x hx y} (g : Q ⟶ Q') :
    y.map g.a ≫ toFirst Q' = toFirst Q := by
  have hw := g.w
  simp only [toFirst]
  rw [← Category.assoc, hw, Category.assoc]
  congr 1
  exact Functor.IsStronglyCartesian.fac 𝒳.val.p Q'.y.hom
    (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩ Q'.y).φ
    (Over.w g.b).symm _

/-- The arrow to `x` attached to a section of `F`. -/
def toFirstOf (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2} (z : F.obj (op D)) : y.obj D ⟶ x :=
  y.map (eqToHom (inv_obj_x e ⟨D, ⟨z⟩⟩).symm) ≫ toFirst (e.inv.functor.obj ⟨D, ⟨z⟩⟩)

/-- **Restriction of sections.** The arrow attached to the restriction of a section along `g`
is the arrow attached to the section, precomposed with the pullback of `y` along `g`. -/
lemma map_toFirstOf (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {T D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2} (g : T ⟶ D) (z : F.obj (op D)) :
    y.map g ≫ toFirstOf e z = toFirstOf e (F.map g.op z) := by
  let m : (⟨T, ⟨F.map g.op z⟩⟩ : (presheafOfCategories (F ⋙ typeToCat)).obj) ⟶ ⟨D, ⟨z⟩⟩ :=
    elementsHom F _ _ g rfl
  have h := map_a_toFirst (e.inv.functor.map m)
  rw [inv_map_a] at h
  simp only [toFirstOf, ← h, ← Category.assoc, ← Functor.map_comp]
  congr 2
  simp [m]

/-- The arrow attached to the section of an object of the 2-fibre product is the arrow of that
object. -/
lemma toFirstOf_sectionOf (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (Q : BaseChangeProduct B S hS 𝒳 U V x hx y) : toFirstOf e (sectionOf e Q) = toFirst Q := by
  obtain ⟨g, hg⟩ := exists_hom_of_map_eq_sectionOf e Q (sectionOf e Q) (𝟙 Q.x) (by simp)
  have h := map_a_toFirst g
  rw [hg, Category.id_comp] at h
  exact h

/-- The base morphism of an arrow of the 2-fibre product whose first component is an `eqToHom`
is an `eqToHom`. -/
lemma exists_eq_eqToHom_b_left {Q Q' : BaseChangeProduct B S hS 𝒳 U V x hx y} (g : Q ⟶ Q')
    (hQ : Q.x = Q'.x) (hg : g.a = eqToHom hQ) : ∃ h, g.b.left = eqToHom h := by
  have h₁ : g.hbase = eqToHom (Q.hx.symm.trans ((congrArg (Over.map V.hom).obj hQ).trans
      Q'.hx)) := by
    have ha := g.ha
    have h := IsHomLift.fac (Over.map V.hom) g.hbase g.a
    simp only [hg, eqToHom_map, eqToHom_trans] at h
    exact h
  have hb := g.hb
  have h₂ := IsHomLift.fac' (Over.forget U) g.hbase g.b
  simp only [h₁, eqToHom_trans] at h₂
  exact ⟨_, h₂⟩

/-- **The projection at the section of an object.** The image in `U` of the section of `F`
attached to an object of the 2-fibre product is the structure morphism of its second
component. -/
private lemma baseChangeProjection_app_sectionOf (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (Q : BaseChangeProduct B S hS 𝒳 U V x hx y) :
    (baseChangeProjection B S hS 𝒳 U V x hx y F e).app ⟨Q.x, ⟨sectionOf e Q⟩⟩ =
      eqToHom (Q.hx.trans Q.hy.symm) ≫ Q.y.hom := by
  obtain ⟨g, hg⟩ := exists_hom_of_map_eq_sectionOf e Q (sectionOf e Q) (𝟙 Q.x) (by simp)
  rw [Category.id_comp] at hg
  obtain ⟨h, hb⟩ := exists_eq_eqToHom_b_left g _ hg
  have hw := Over.w g.b
  rw [hb] at hw
  rw [baseChangeProjection_app B S hS 𝒳 U V x hx y F e _ (inv_obj_x e _), ← hw]
  simp

end ToFirst

/-! ### The 2-Yoneda morphism of an object, and objects of the 2-fibre product from arrows -/

section FromArrows

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS)}
  {U V : AlgebraicGeometry.BigFppfOver B S hS} {x : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = U)
  {ξ : 𝒳.val.obj} (hξ : 𝒳.val.p.obj ξ = V)

/-- The 2-Yoneda morphism `(Sch/V) ⟶ 𝒳` of an object `ξ` over `V`, read on the big fppf site of
`V`. -/
abbrev yonedaSlice : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj :=
  Over.iteratedSliceBackward V ⋙
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids V ⟨ξ, hξ⟩).toFunctor

/-- The 2-Yoneda morphism of `ξ` lies over the slice functor. -/
lemma yonedaSlice_comp : yonedaSlice hξ ⋙ 𝒳.val.p = Over.map V.hom := by
  show Over.iteratedSliceBackward V ⋙
    ((Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids V ⟨ξ, hξ⟩).toFunctor ⋙
      𝒳.val.p) = _
  rw [show (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids V ⟨ξ, hξ⟩).toFunctor ⋙
      𝒳.val.p = Over.forget V from Functor.TwoYoneda.liftFunctor_w _ _ _ _]
  rfl

/-- The chosen arrow from the pullback of `ξ` to an object of the site of `V` into `ξ`. -/
abbrev toSecond (D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2) :
    (yonedaSlice hξ).obj D ⟶ ξ :=
  (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids V ⟨ξ, hξ⟩
    ((Over.iteratedSliceBackward V).obj D)).φ

/-- The chosen arrow `toSecond hξ D` into `ξ` is strongly cartesian. -/
instance (D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2) :
    𝒳.val.p.IsStronglyCartesian ((Over.iteratedSliceBackward V).obj D).hom (toSecond hξ D) :=
  (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids V ⟨ξ, hξ⟩
    ((Over.iteratedSliceBackward V).obj D)).isStronglyCartesian

/-- The chosen arrows into `ξ` are compatible with the 2-Yoneda morphism. -/
@[reassoc]
lemma map_toSecond {D D' : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2} (g : D ⟶ D') :
    (yonedaSlice hξ).map g ≫ toSecond hξ D' = toSecond hξ D :=
  Functor.IsStronglyCartesian.fac 𝒳.val.p ((Over.iteratedSliceBackward V).obj D').hom
    (toSecond hξ D') (Over.w ((Over.iteratedSliceBackward V).map g)).symm (toSecond hξ D)

variable {hx}

/-- The object of the site of `V` underlying an arrow `z ⟶ ξ`. -/
abbrev siteOverOf {z : 𝒳.val.obj} (d' : z ⟶ ξ) :
    AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 :=
  Over.mk (𝒳.val.p.map d' ≫ eqToHom hξ).left

/-- The object of the site of `V` underlying an arrow `z ⟶ ξ` has the base of `z` as image. -/
lemma map_siteOverOf {z : 𝒳.val.obj} (d' : z ⟶ ξ) :
    (Over.map V.hom).obj (siteOverOf hξ d') = 𝒳.val.p.obj z := by
  show Over.mk ((𝒳.val.p.map d' ≫ eqToHom hξ).left ≫ V.hom) = Over.mk (𝒳.val.p.obj z).hom
  congr 1
  exact Over.w (𝒳.val.p.map d' ≫ eqToHom hξ)

/-- The chosen arrow into `ξ` lies over the structure morphism of the object of the site. -/
lemma map_toSecond_eq (D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2) :
    𝒳.val.p.map (toSecond hξ D) =
      eqToHom (Functor.congr_obj (yonedaSlice_comp hξ) D) ≫
        ((Over.iteratedSliceBackward V).obj D).hom ≫ eqToHom hξ.symm := by
  have : 𝒳.val.p.IsHomLift ((Over.iteratedSliceBackward V).obj D).hom (toSecond hξ D) :=
    (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids V ⟨ξ, hξ⟩
      ((Over.iteratedSliceBackward V).obj D)).isStronglyCartesian.toIsHomLift
  exact IsHomLift.fac' 𝒳.val.p ((Over.iteratedSliceBackward V).obj D).hom (toSecond hξ D)

/-- An arrow of `𝒳` whose image is an isomorphism is an isomorphism. -/
lemma isIso_of_isIso_map {a b : 𝒳.val.obj} (φ : a ⟶ b) [IsIso (𝒳.val.p.map φ)] : IsIso φ := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝒳.val.p.map φ) φ

/-- The image of `toSecond hξ (siteOverOf hξ d')`, preceded by an `eqToHom`, is the image of
`d'`. -/
lemma toYonedaSlice_aux {z : 𝒳.val.obj} (d' : z ⟶ ξ) :
    eqToHom ((map_siteOverOf hξ d').symm.trans
        (Functor.congr_obj (yonedaSlice_comp hξ) (siteOverOf hξ d')).symm) ≫
      𝒳.val.p.map (toSecond hξ (siteOverOf hξ d')) = 𝒳.val.p.map d' := by
  rw [map_toSecond_eq]
  apply Over.OverMorphism.ext
  simp only [Over.iteratedSliceBackward, Over.comp_left, Over.eqToHom_left, Over.homMk_left,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id, Over.mk_hom,
    siteOverOf, Category.assoc, eqToHom_trans]

/-- The comparison arrow from `z` to the pullback of `ξ` along the morphism underlying an arrow
`d' : z ⟶ ξ`; it lies over an `eqToHom`, so it is an isomorphism. -/
def toYonedaSlice {z : 𝒳.val.obj} (d' : z ⟶ ξ) : z ⟶ (yonedaSlice hξ).obj (siteOverOf hξ d') :=
  (𝒳.isFiberedInGroupoids.unique_lift (toSecond hξ (siteOverOf hξ d')) d' _
    (toYonedaSlice_aux hξ d')).exists.choose

/-- `toYonedaSlice hξ d'` lies over an `eqToHom`. -/
lemma map_toYonedaSlice {z : 𝒳.val.obj} (d' : z ⟶ ξ) :
    𝒳.val.p.map (toYonedaSlice hξ d') = eqToHom ((map_siteOverOf hξ d').symm.trans
        (Functor.congr_obj (yonedaSlice_comp hξ) (siteOverOf hξ d')).symm) :=
  (𝒳.isFiberedInGroupoids.unique_lift (toSecond hξ (siteOverOf hξ d')) d' _
    (toYonedaSlice_aux hξ d')).exists.choose_spec.1

/-- `toYonedaSlice hξ d'` followed by the chosen arrow into `ξ` is `d'`. -/
@[reassoc (attr := simp)]
lemma toYonedaSlice_toSecond {z : 𝒳.val.obj} (d' : z ⟶ ξ) :
    toYonedaSlice hξ d' ≫ toSecond hξ (siteOverOf hξ d') = d' :=
  (𝒳.isFiberedInGroupoids.unique_lift (toSecond hξ (siteOverOf hξ d')) d' _
    (toYonedaSlice_aux hξ d')).exists.choose_spec.2

/-- `toYonedaSlice hξ d'` is an isomorphism. -/
instance isIso_toYonedaSlice {z : 𝒳.val.obj} (d' : z ⟶ ξ) : IsIso (toYonedaSlice hξ d') := by
  have : IsIso (𝒳.val.p.map (toYonedaSlice hξ d')) := by
    rw [map_toYonedaSlice]
    infer_instance
  exact isIso_of_isIso_map _

variable (hx)

/-- The object of `Over U` underlying an arrow `d : z ⟶ x`, over the base of `z` read through
`d' : z ⟶ ξ`. -/
abbrev overOf {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) : Over U :=
  Over.mk (eqToHom (map_siteOverOf hξ d') ≫ 𝒳.val.p.map d ≫ eqToHom hx)

/-- The chosen arrow into `x` from the chosen pullback along an object of `Over U`. -/
abbrev liftArrow (R : Over U) :
    (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩ R).y ⟶ x :=
  (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩ R).φ

/-- The chosen arrow into `x` lies over the structure morphism of the object of `Over U`. -/
lemma map_liftArrow (R : Over U) :
    𝒳.val.p.map (liftArrow hx R) =
      eqToHom (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w 𝒳.val.p
        𝒳.isFiberedInGroupoids U ⟨x, hx⟩) R) ≫ R.hom ≫ eqToHom hx.symm := by
  have : 𝒳.val.p.IsHomLift R.hom (liftArrow hx R) :=
    (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩
      R).isStronglyCartesian.toIsHomLift
  exact IsHomLift.fac' 𝒳.val.p R.hom (liftArrow hx R)

/-- The image of the chosen arrow `liftArrow hx (overOf hx hξ d d')` into `x`, preceded by an
`eqToHom`, is the image of `d`. -/
lemma toLift_aux {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    eqToHom ((map_siteOverOf hξ d').symm.trans (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w
        𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩) (overOf hx hξ d d')).symm) ≫
      𝒳.val.p.map (liftArrow hx (overOf hx hξ d d')) = 𝒳.val.p.map d := by
  rw [map_liftArrow]
  simp

/-- The comparison arrow from `z` to the chosen pullback of `x` along the morphism underlying
`d : z ⟶ x`. -/
def toLift {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    z ⟶ (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩
      (overOf hx hξ d d')).y :=
  (𝒳.isFiberedInGroupoids.unique_lift (liftArrow hx (overOf hx hξ d d')) d _
    (toLift_aux hx hξ d d')).exists.choose

/-- `toLift hx hξ d d'` lies over an `eqToHom`. -/
lemma map_toLift {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    𝒳.val.p.map (toLift hx hξ d d') = eqToHom ((map_siteOverOf hξ d').symm.trans
      (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w 𝒳.val.p 𝒳.isFiberedInGroupoids U
        ⟨x, hx⟩) (overOf hx hξ d d')).symm) :=
  (𝒳.isFiberedInGroupoids.unique_lift (liftArrow hx (overOf hx hξ d d')) d _
    (toLift_aux hx hξ d d')).exists.choose_spec.1

/-- `toLift hx hξ d d'` followed by the chosen arrow into `x` is `d`. -/
@[reassoc (attr := simp)]
lemma toLift_fac {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    toLift hx hξ d d' ≫ liftArrow hx (overOf hx hξ d d') = d :=
  (𝒳.isFiberedInGroupoids.unique_lift (liftArrow hx (overOf hx hξ d d')) d _
    (toLift_aux hx hξ d d')).exists.choose_spec.2

/-- `toLift hx hξ d d'` is an isomorphism. -/
instance {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) : IsIso (toLift hx hξ d d') := by
  have : IsIso (𝒳.val.p.map (toLift hx hξ d d')) := by
    rw [map_toLift]
    infer_instance
  exact isIso_of_isIso_map _

/-- **The object of the 2-fibre product attached to a pair of arrows** `d : z ⟶ x` and
`d' : z ⟶ ξ`: over the base of `z`, its comparison isomorphism identifies the two pullbacks with
`z`. -/
def objOfArrows {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    BaseChangeProduct B S hS 𝒳 U V x hx (yonedaSlice hξ) where
  base := (Over.map V.hom).obj (siteOverOf hξ d')
  x := siteOverOf hξ d'
  y := overOf hx hξ d d'
  hx := rfl
  hy := rfl
  iso := (asIso (toYonedaSlice hξ d')).symm ≪≫ asIso (toLift hx hξ d d')
  vertical := by
    change 𝒳.val.p.IsHomLift _ (inv (toYonedaSlice hξ d') ≫ toLift hx hξ d d')
    apply IsHomLift.of_fac' 𝒳.val.p _ _ (Functor.congr_obj (yonedaSlice_comp hξ) _)
      (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w 𝒳.val.p 𝒳.isFiberedInGroupoids U
        ⟨x, hx⟩) (overOf hx hξ d d'))
    simp [map_toYonedaSlice, map_toLift]

/-- The object of the site of `V` underlying `objOfArrows hx hξ d d'` is `siteOverOf hξ d'`. -/
@[simp]
lemma objOfArrows_x {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    (objOfArrows hx hξ d d').x = siteOverOf hξ d' := rfl

/-- The arrow to `x` of the object attached to `d` and `d'` is `d`, read from the pullback. -/
@[reassoc]
lemma toYonedaSlice_toFirst {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    toYonedaSlice hξ d' ≫ toFirst (objOfArrows hx hξ d d') = d := by
  show toYonedaSlice hξ d' ≫ (inv (toYonedaSlice hξ d') ≫ toLift hx hξ d d') ≫
    liftArrow hx (overOf hx hξ d d') = d
  simp

/-- The arrow to `x` of the object attached to `d` and `d'`. -/
lemma toFirst_objOfArrows {z : 𝒳.val.obj} (d : z ⟶ x) (d' : z ⟶ ξ) :
    toFirst (objOfArrows hx hξ d d') = inv (toYonedaSlice hξ d') ≫ d :=
  (IsIso.eq_inv_comp (toYonedaSlice hξ d')).mpr (toYonedaSlice_toFirst hx hξ d d')

/-- For the object attached to an arrow `r : x ⟶ ξ` and the identity of `x`, the arrow to `x`
followed by `r` is the chosen arrow into `ξ`. -/
@[reassoc]
lemma toFirst_objOfArrows_id_comp (r : x ⟶ ξ) :
    toFirst (objOfArrows hx hξ (𝟙 x) r) ≫ r = toSecond hξ (siteOverOf hξ r) := by
  rw [toFirst_objOfArrows, Category.comp_id]
  exact (IsIso.inv_comp_eq (toYonedaSlice hξ r)).mpr (toYonedaSlice_toSecond hξ r).symm

end FromArrows

/-! ### A local retraction at a versal point -/

section LocalRetraction

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))

/-- Arrows of `𝒳` into the source of an arrow whose underlying morphism of schemes is a
monomorphism are determined by their composites with it. -/
lemma cancel_of_mono {a b c : 𝒳.val.obj} (φ : a ⟶ b)
    (hφ : Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝒳.val.p.map φ)))
    {ψ₁ ψ₂ : c ⟶ a} (h : ψ₁ ≫ φ = ψ₂ ≫ φ) : ψ₁ = ψ₂ := by
  have hm : Mono (𝒳.val.p.map φ) :=
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).mono_of_mono_map hφ
  have hp : 𝒳.val.p.map ψ₁ = 𝒳.val.p.map ψ₂ := by
    rw [← cancel_mono (𝒳.val.p.map φ), ← Functor.map_comp, ← Functor.map_comp, h]
  exact (𝒳.isFiberedInGroupoids.unique_lift φ (ψ₂ ≫ φ) (𝒳.val.p.map ψ₂)
    (Functor.map_comp _ _ _).symm).unique ⟨hp, h⟩ ⟨rfl, rfl⟩

/-- **A local retraction at a versal point.** Let `𝒳` be a category fibred in groupoids over the
big fppf site of a locally Noetherian scheme `S`, with diagonal representable by algebraic
spaces and locally of finite type, satisfying (RS). Let `r : x ⟶ ξ` lie over a first-order
thickening `U ⟶ U'` of schemes locally of finite type over `S`, and let `x` be versal at a
finite type point `u₀` of `U`. Then there are an arrow `cw : w ⟶ ξ` over an open immersion whose
image contains the image of `u₀`, and an arrow `β : w ⟶ x` retracting `r` over it: `s' ≫ β = t'`
whenever `t' ≫ r = s' ≫ cw`.

This is the step shared by the proofs of Stacks 0G2K and Stacks 0CXU. The 2-fibre product
`Z = (Sch/U) ×_{x, 𝒳, ξ} (Sch/U')` is an algebraic space over `U'`; `r` gives a section of
`Z ⟶ U'` over `U`, at whose value at `u₀` the morphism `Z ⟶ U'` is smooth by Stacks 0CXM;
by Stacks 04AM the section extends over a neighbourhood of the image of `u₀`, and the
universal arrow of `Z` read at the extended section is the retraction. -/
theorem exists_localRetraction_of_isVersalAt [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hΔlft :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
        (a b : 𝒳.val.p.Fiber T)
        (G : (AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
        AlgebraicGeometry.IsAlgebraicSpace B T.left.1 T.left.2 G →
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
            uliftFunctor.{u, v}) →
        AlgebraicGeometry.Space.IsLocallyOfFiniteType B T.left.1 T.left.2
          (terminal.from G : G ⟶
            ⊤_ ((AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)))
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (x ξ : 𝒳.val.obj) (r : x ⟶ ξ)
    [LocallyOfFiniteType (B.inclusion.map (𝒳.val.p.obj x).hom)]
    [LocallyOfFiniteType (B.inclusion.map (𝒳.val.p.obj ξ).hom)]
    (hr : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝒳.val.p.map r)))
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (𝒳.val.p.obj x))
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (𝒳.val.p.obj x))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl) :
    ∃ (w : 𝒳.val.obj) (cw : w ⟶ ξ)
      (_ : AlgebraicGeometry.IsOpenImmersion
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝒳.val.p.map cw)))
      (w₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (𝒳.val.p.obj w))
      (_ : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝒳.val.p.map cw)).base w₀ =
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝒳.val.p.map r)).base u₀)
      (β : w ⟶ x),
      ∀ (z' : 𝒳.val.obj) (t' : z' ⟶ x) (s' : z' ⟶ w), t' ≫ r = s' ≫ cw → s' ≫ β = t' := by
  classical
  let p := 𝒳.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let VS := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let U := p.obj x
  let U' := p.obj ξ
  let y := yonedaSlice (𝒳 := 𝒳) (rfl : p.obj ξ = U')
  have hy : y ⋙ p = Over.map U'.hom := yonedaSlice_comp (𝒳 := 𝒳) rfl
  let f := Functor.TwoYoneda.liftBased p hp U ⟨x, rfl⟩
  have hrep : AlgebraicGeometry.IsRepresentableByAlgebraicSpaces B S hS f :=
    (AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes
      B S hS 𝒳).mp
      ((AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf
        B S hS 𝒳).mp hΔ) U f
  obtain ⟨F, hF, ⟨e₀⟩⟩ := hrep U' y hy
  let e : BaseChangeEquivalence B S hS 𝒳 U U' x rfl y F := e₀
  let Q₀ := objOfArrows (𝒳 := 𝒳) (rfl : p.obj x = U) (rfl : p.obj ξ = U') (𝟙 x) r
  let s₀ : F.obj (op Q₀.x) := sectionOf e Q₀
  have hrV : VS.map (p.map r) = B.inclusion.map Q₀.x.hom := by
    show B.inclusion.map (p.map r).left = B.inclusion.map (p.map r ≫ eqToHom rfl).left
    simp
  have hT₀ : Stacks.Thickenings.IsFirstOrderThickening (B.inclusion.map Q₀.x.hom) := by
    rw [← hrV]
    exact hr
  let ι : yoneda.obj Q₀.x ⟶ F := yonedaEquiv.symm s₀
  let q₀ := AlgebraicGeometry.Space.schemePointRepresentative B U'.left.1 U'.left.2 Q₀.x u₀
  let z₀ := AlgebraicGeometry.Space.FieldValuedPoint.map B U'.left.1 U'.left.2 _ ι q₀
  have hz₀ : AlgebraicGeometry.Space.IsFiniteTypePoint B U'.left.1 U'.left.2 F
      (z₀.class B U'.left.1 U'.left.2 F) := by
    refine ⟨z₀, rfl, ?_⟩
    have h₁ : yonedaEquiv.symm z₀.value = yoneda.map q₀.value ≫ ι := by
      rw [yonedaEquiv_symm_naturality_left]
      congr 1
    rw [h₁]
    refine AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp B U'.left.1 U'.left.2
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B U'.left.1 U'.left.2 _) hF
      (AlgebraicGeometry.Space.isAlgebraicSpace_terminal B U'.left.1 U'.left.2) _
      (terminal.from F) ?_
    rw [show (yoneda.map q₀.value ≫ ι) ≫ terminal.from F =
      terminal.from _ from terminal.hom_ext _ _]
    refine AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isTerminal B U'.left.1 U'.left.2
      ((Over.mkIdTerminal (X := B.obj U'.left.2)).isTerminalObj yoneda _) terminalIsTerminal
      (yoneda.map (Over.homMk q₀.siteObject.hom :
        q₀.siteObject ⟶ Over.mk (𝟙 (B.obj U'.left.2)))) _ ?_
    refine (AlgebraicGeometry.Space.isLocallyOfFiniteType_yoneda_map_iff B U'.left.1 U'.left.2
      _).mpr ?_
    have hbase : q₀.toBase = (VS.obj (p.obj x)).fromSpecResidueField u₀ ≫
        B.inclusion.map Q₀.x.hom := by
      show B.inclusion.map (B.inclusion.preimage _ ≫ Q₀.x.hom) = _
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      rfl
    have hfin : IsFinite (B.inclusion.map Q₀.x.hom) :=
      ((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mp hT₀.1).1
    show LocallyOfFiniteType q₀.toBase
    rw [hbase]
    exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ hu₀.1
      ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfin).2
  have hzu : let : Category (TwoFibreProductOver (Over.map U'.hom)
        (Over.forget U) 𝒳.val.p y
        (Functor.TwoYoneda.liftBased 𝒳.val.p
          𝒳.isFiberedInGroupoids U ⟨x, rfl⟩).toFunctor) :=
            TwoFibreProductOver.instCategory
      let P := e.inv.functor.obj ⟨z₀.siteObject, Discrete.mk z₀.value⟩
      ∃ hP : P.x = z₀.siteObject,
        (B.inclusion.map
          ((eqToHom (P.hx.trans P.hy.symm) ≫ P.y.hom).left))
          ((B.inclusion.map (eqToHom (congrArg Over.left hP).symm))
            (IsLocalRing.closedPoint z₀.carrier)) = u₀ := by
    refine ⟨inv_obj_x e _, ?_⟩
    have h1 := baseChangeProjection_point B S hS 𝒳 U U' x rfl y F e z₀ (inv_obj_x e _)
    simp only at h1
    rw [← h1]
    have h2 := projection_point_eq_chartPoint B S hS U U' F
      (baseChangeProjection B S hS 𝒳 U U' x rfl y F e) Q₀.x ι q₀
    simp only at h2
    rw [h2]
    have h3 : ι.app (op Q₀.x) (𝟙 Q₀.x) = s₀ := by
      simp [ι, yonedaEquiv_symm_app_apply]
    have h4 : B.inclusion.map q₀.value.left (IsLocalRing.closedPoint q₀.carrier) = u₀ :=
      AlgebraicGeometry.Space.schemePointRepresentative_point B U'.left.1 U'.left.2 Q₀.x u₀
    rw [h3, baseChangeProjection_app_sectionOf, h4]
    simp only [Q₀, objOfArrows, overOf, Over.mk_hom]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Over.comp_left, Over.eqToHom_left]
    show B.inclusion.map (𝟙 U.left ≫ 𝟙 U.left) u₀ = u₀
    simp
  have hsm := isSmoothAt_baseChange_of_isVersalAt B S hS 𝒳 hΔ hΔlft hRS U U' x rfl u₀ hu₀ y hy
    F hF e z₀ hz₀ hzu hvers
  obtain ⟨G, hG, x', hx', hGsm⟩ := hsm
  obtain ⟨T', hT'open, t₀, ht₀, z, hSE⟩ :=
    AlgebraicGeometry.Space.exists_section_extension_of_isSmooth G hG hGsm Q₀.x hT₀ s₀ u₀
      ⟨x', hx'⟩
  let cw : y.obj T' ⟶ ξ := toSecond (𝒳 := 𝒳) (rfl : p.obj ξ = U') T'
  have hyT' : p.obj (y.obj T') = (Over.map U'.hom).obj T' := Functor.congr_obj hy T'
  have hcwV : VS.map (p.map cw) = VS.map (eqToHom hyT') ≫ B.inclusion.map T'.hom := by
    rw [map_toSecond_eq]
    simp only [Functor.map_comp, eqToHom_refl]
    rfl
  have hcwopen : AlgebraicGeometry.IsOpenImmersion (VS.map (p.map cw)) := by
    rw [hcwV]
    infer_instance
  refine ⟨y.obj T', cw, hcwopen, (VS.map (eqToHom hyT'.symm)).base t₀, ?_, toFirstOf e z, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hcwV, ← Category.assoc, ← Functor.map_comp, eqToHom_trans,
      eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, hrV]
    exact ht₀
  intro z'' t' s' hts
  let T₁ := siteOverOf (𝒳 := 𝒳) (rfl : p.obj ξ = U') (s' ≫ cw)
  let θ := toYonedaSlice (𝒳 := 𝒳) (rfl : p.obj ξ = U') (s' ≫ cw)
  let b : T₁ ⟶ T' := Over.homMk (p.map s' ≫ eqToHom hyT').left (by
    show _ = (p.map (s' ≫ cw) ≫ eqToHom rfl).left
    rw [Functor.map_comp, map_toSecond_eq]
    simp only [Over.iteratedSliceBackward, Over.comp_left, Over.eqToHom_left, Over.homMk_left,
      eqToHom_refl, Category.comp_id, Category.assoc, Over.mk_hom])
  let a : T₁ ⟶ Q₀.x := Over.homMk (p.map t').left (by
    show (p.map t').left ≫ (p.map r ≫ eqToHom rfl).left = (p.map (s' ≫ cw) ≫ eqToHom rfl).left
    rw [← hts, Functor.map_comp]
    simp)
  have hab := hSE T₁ a b
  have hmono_cw : Mono (VS.map (p.map cw)) := inferInstance
  have hmono_r : Mono (VS.map (p.map r)) :=
    ((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mp hr.1).2
  have hA : s' = θ ≫ y.map b := by
    apply cancel_of_mono B S hS 𝒳 cw hmono_cw
    rw [Category.assoc, map_toSecond, toYonedaSlice_toSecond]
  have hB : t' = θ ≫ y.map a ≫ toFirstOf e s₀ := by
    apply cancel_of_mono B S hS 𝒳 r hmono_r
    rw [Category.assoc, Category.assoc, toFirstOf_sectionOf, toFirst_objOfArrows_id_comp]
    show _ = θ ≫ (y.map a ≫ toSecond (𝒳 := 𝒳) (rfl : p.obj ξ = U') Q₀.x)
    rw [map_toSecond, toYonedaSlice_toSecond, hts]
  rw [hA, Category.assoc, map_toFirstOf, ← hab, ← map_toFirstOf, hB]

end LocalRetraction

end Deformation.Artin.BaseChange

end
