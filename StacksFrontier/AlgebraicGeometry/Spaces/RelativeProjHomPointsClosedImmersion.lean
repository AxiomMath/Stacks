module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityEventual

/-!
# The morphism of relative Projs defined everywhere, on the fibres over the base

Let `S` be a scheme, `X` an algebraic space over `S` and `ψ : 𝒜 ⟶ ℬ` a map of quasi-coherent
graded `𝒪_X`-algebras, read over the scheme points of `X` as a
`AlgebraicGeometry.Space.RelativeProjHomPoints` between presentations of `P = Proj_X(𝒜)` and
`Q = Proj_X(ℬ)`.  When the open subspace `U(ψ) ⊆ Q` of Stacks 085F is all of `Q` — which is
Stacks 085H (1) as soon as `ψ` is surjective in high degrees — the morphism `r_ψ` of Stacks 085F
is a morphism `Q ⟶ P` over `X`.  This file reads that morphism on the fibres over the scheme
points of `X`, and deduces that it is a closed immersion of algebraic spaces as soon as it is one
over every scheme point, which is the global form of Stacks 085H (2).

For a scheme point `f : T ⟶ X` the presentations identify `T ×_X Q` with `Proj_T(ℬ|_T)` and
`T ×_X P` with `Proj_T(𝒜|_T)`.  The morphism `r_ψ` induces a morphism of the representing objects
over `T`; it sits in a cartesian square with `r_ψ`, and on schemes it is the morphism
`r_{ψ|_T}` of Stacks 07ZG.  The base change of `r_ψ` along an arbitrary scheme point
`g : T' ⟶ P` is then the base change of that morphism of schemes along the section of
`Proj_{T'}(𝒜|_{T'})` attached to `g`, so it is a closed immersion whenever `r_{ψ|_{T'}}` is.

The last section records the étale-local nature of closed subspaces of `P` used to identify a
closed subspace with `Proj_X(𝒜/ℱ𝒜)`: two subsheaves of `P` agree as soon as their pullbacks to
the fibre `T ×_X P` over a single surjective étale scheme point of `X` agree.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjHomPoints.totalHom`: the morphism `r_ψ : Q ⟶ P` when
  `U(ψ) = Q`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.totalHomFibreMap`: the morphism
  `T ×_X Q ⟶ T ×_X P` of representing objects it induces over a scheme point of the base.

## Main results

* `AlgebraicGeometry.Space.RelativeProjHomPoints.isPullback_totalHomFibreMap`: the fibre square of
  `r_ψ` over a scheme point of the base is cartesian.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.ι_comp_toScheme_map_totalHomFibreMap`: on
  schemes, the fibre of `r_ψ` is the morphism `r_{ψ|_T} : Proj_T(ℬ|_T) ⟶ Proj_T(𝒜|_T)` of
  Stacks 07ZG, through the identifications of Stacks 084B (2).
* `AlgebraicGeometry.Space.RelativeProjHomPoints.isClosedImmersion_totalHom` and
  `…isClosedImmersion_totalHom_of_eventually_epi`: `r_ψ : Q ⟶ P` is a closed immersion of
  algebraic spaces when every `r_{ψ|_T}` is, in particular when `ψ` is surjective in high degrees.
* `AlgebraicGeometry.Space.RelativeProjPoints.eq_of_preimage_fibreToSpace_eq`: two subsheaves of
  `P` with the same pullback to the fibre over a surjective étale scheme point of `X` are equal.

## References

* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 085H](https://stacks.math.columbia.edu/tag/085H)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X}

namespace RelativeProjPoints

variable (d : RelativeProjPoints B S hS πP)

/-- The point of `P` at the representing object of a fibre corresponds to the identity section,
as an equality of sections over the structure morphism of the fibre. -/
theorem pointEquivOver_fibreToSpace_eq_id (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    d.pointEquivOver T f (d.fibreHom T f) ⟨d.fibreToSpace T f, (d.isPullback T f).w⟩ =
      ⟨𝟙 _, Category.id_comp _⟩ := by
  refine (Equiv.eq_symm_apply _).1 ?_
  apply Subtype.ext
  change d.fibreToSpace T f = yoneda.map (𝟙 _) ≫ d.fibreToSpace T f
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- A point of `P` over a scheme point `f` factors through the fibre `T ×_X P`. -/
private theorem exists_yoneda_map_comp_fibreToSpace (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS} (r : T' ⟶ T) (v : yoneda.obj T' ⟶ P)
    (hv : v ≫ πP = yoneda.map r ≫ f) : ∃ σ, yoneda.map σ ≫ d.fibreToSpace T f = v :=
  ⟨_, d.map_pointEquivOver T f r ⟨v, hv⟩⟩

end RelativeProjPoints

namespace RelativeProjHomPoints

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
    (hψ : RelativeProjHomPoints dP dQ) (htop : hψ.relativeMapSubfunctor = ⊤)

/-! ### The morphism `r_ψ : Q ⟶ P` -/

/-- **The morphism `r_ψ : Q ⟶ P` of Stacks 085F, when `U(ψ) = Q`.** -/
def totalHom : Q ⟶ P :=
  Subfunctor.lift (𝟙 Q) (by rw [htop]; exact le_top) ≫ hψ.relativeMapSpaceHom

/-- `r_ψ : Q ⟶ P` is a morphism over `X`. -/
@[reassoc]
theorem totalHom_comp : hψ.totalHom htop ≫ πP = πQ := by
  rw [totalHom, Category.assoc, relativeMapSpaceHom_comp, Subfunctor.lift_ι_assoc,
    Category.id_comp]

include htop in
/-- Every point of `Q` is in the domain of definition when `U(ψ) = Q`. -/
theorem isDefined_of_eq_top (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ Q) :
    IsDefined dP dQ hψ.hom T u :=
  (hψ.mem_relativeMapSubfunctor_iff' T u).1 (by rw [htop]; trivial)

/-- **`r_ψ` on a point of `Q`** is the point of `P` induced through the scheme-level morphism
`r_{ψ|_T}` of Stacks 07ZG. -/
theorem comp_totalHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q)
    (hu : u ≫ πQ = yoneda.map r ≫ f) (hd : IsDefinedOn dP dQ hψ.hom T f r u hu) :
    u ≫ hψ.totalHom htop = pointHomOn dP dQ hψ.hom T f r u hu hd := by
  have hx : yonedaEquiv u ∈ hψ.relativeMapSubfunctor.obj (op T') := by rw [htop]; trivial
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, ← hψ.app_relativeMapSpaceHom T f r u hu hd hx]
  rfl

/-! ### The fibre of `r_ψ` over a scheme point of the base -/

variable (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)

/-- The image under `r_ψ` of the tautological point of `T ×_X Q` lies over `f`. -/
theorem fibreToSpace_comp_totalHom_comp :
    (dQ.fibreToSpace T f ≫ hψ.totalHom htop) ≫ πP = yoneda.map (dQ.fibreHom T f) ≫ f := by
  rw [Category.assoc, totalHom_comp, (dQ.isPullback T f).w]

/-- **The fibre of `r_ψ` over a scheme point `f : T ⟶ X`**: the morphism `T ×_X Q ⟶ T ×_X P` of
the representing objects of Stacks 084B (2), over `T`.  Here `r_ψ` is the everywhere defined
morphism `AlgebraicGeometry.Space.RelativeProjHomPoints.totalHom` of the case `U(ψ) = Q`. -/
def totalHomFibreMap : dQ.fibre T f ⟶ dP.fibre T f :=
  (dP.pointEquivOver T f (dQ.fibreHom T f)
    ⟨dQ.fibreToSpace T f ≫ hψ.totalHom htop, hψ.fibreToSpace_comp_totalHom_comp htop T f⟩).1

/-- The fibre of `r_ψ` is a morphism over `T`. -/
@[reassoc]
theorem totalHomFibreMap_comp_fibreHom :
    hψ.totalHomFibreMap htop T f ≫ dP.fibreHom T f = dQ.fibreHom T f :=
  (dP.pointEquivOver T f (dQ.fibreHom T f)
    ⟨dQ.fibreToSpace T f ≫ hψ.totalHom htop, hψ.fibreToSpace_comp_totalHom_comp htop T f⟩).2

/-- The fibre square of `r_ψ` commutes. -/
@[reassoc]
theorem yoneda_map_totalHomFibreMap_comp :
    yoneda.map (hψ.totalHomFibreMap htop T f) ≫ dP.fibreToSpace T f =
      dQ.fibreToSpace T f ≫ hψ.totalHom htop :=
  dP.map_pointEquivOver T f (dQ.fibreHom T f)
    ⟨dQ.fibreToSpace T f ≫ hψ.totalHom htop, hψ.fibreToSpace_comp_totalHom_comp htop T f⟩

/-- **The fibre square of `r_ψ` over a scheme point of the base is cartesian**: `T ×_X Q` is the
base change of `r_ψ : Q ⟶ P` along `T ×_X P ⟶ P`. -/
theorem isPullback_totalHomFibreMap :
    IsPullback (dQ.fibreToSpace T f) (yoneda.map (hψ.totalHomFibreMap htop T f)) (hψ.totalHom htop)
      (dP.fibreToSpace T f) := by
  refine IsPullback.of_bot ?_ (hψ.yoneda_map_totalHomFibreMap_comp htop T f).symm
    (dP.isPullback T f)
  rw [← CategoryTheory.Functor.map_comp, totalHomFibreMap_comp_fibreHom, totalHom_comp]
  exact dQ.isPullback T f

/-- The section of `Proj_T(𝒜|_T)` attached to the image of the tautological point of
`T ×_X Q` is the fibre of `r_ψ` read through the identification of Stacks 084B (2). -/
theorem sectionOfPoint_fibreToSpace_comp_totalHom :
    dP.sectionOfPoint T f (dQ.fibreHom T f) (dQ.fibreToSpace T f ≫ hψ.totalHom htop)
        (hψ.fibreToSpace_comp_totalHom_comp htop T f) =
      (BigFppfOver.toScheme B S hS).map (hψ.totalHomFibreMap htop T f) ≫ (dP.fibreIso T f).hom :=
  dP.pointEquivProjOver_apply T f (dQ.fibreHom T f) _

include htop in
/-- The tautological point of `T ×_X Q` is in the domain of definition of `ψ` over `f`, read off
`U(ψ) = Q`. -/
theorem isDefinedOn_fibreToSpace_of_eq_top :
    IsDefinedOn dP dQ hψ.hom T f (dQ.fibreHom T f) (dQ.fibreToSpace T f)
      (dQ.isPullback T f).w :=
  (hψ.isDefinedOn_iff T f (dQ.fibreHom T f) (dQ.fibreToSpace T f) (dQ.isPullback T f).w).2
    (hψ.isDefined_of_eq_top htop _ _)

include htop in
/-- **When `U(ψ) = Q`, the domain `U(ψ|_T)` of the scheme-level morphism of Stacks 07ZG is all
of `Proj_T(ℬ|_T)`**, at every scheme point of the base. -/
theorem relativeMapDomain_eq_top : (hψ.hom T f).relativeMapDomain = ⊤ := by
  have h := hψ.isDefinedOn_fibreToSpace_of_eq_top htop T f
  change dQ.sectionOfPoint T f (dQ.fibreHom T f) (dQ.fibreToSpace T f) _ ⁻¹ᵁ
    (hψ.hom T f).relativeMapDomain = ⊤ at h
  rw [RelativeProjPoints.sectionOfPoint_fibreToSpace] at h
  have hinv := congrArg (fun D => (dQ.fibreIso T f).inv ⁻¹ᵁ D) h
  simp only [Scheme.Hom.preimage_top] at hinv
  rwa [← Scheme.Hom.comp_preimage, Iso.inv_hom_id, Scheme.Hom.id_preimage] at hinv

/-- **On schemes, the fibre of `r_ψ` over `f : T ⟶ X` is the morphism
`r_{ψ|_T} : Proj_T(ℬ|_T) ⟶ Proj_T(𝒜|_T)` of Stacks 07ZG**, through the identifications
`T ×_X Q ≅ Proj_T(ℬ|_T)` and `T ×_X P ≅ Proj_T(𝒜|_T)` of Stacks 084B (2).  The domain
`U(ψ|_T)` of `r_{ψ|_T}` is all of `Proj_T(ℬ|_T)` by `relativeMapDomain_eq_top`. -/
theorem ι_comp_toScheme_map_totalHomFibreMap :
    (hψ.hom T f).relativeMapDomain.ι ≫ (dQ.fibreIso T f).inv ≫
        (BigFppfOver.toScheme B S hS).map (hψ.totalHomFibreMap htop T f) ≫ (dP.fibreIso T f).hom =
      relativeMapHom (hψ.hom T f) := by
  have hd := hψ.isDefinedOn_fibreToSpace_of_eq_top htop T f
  have key := sectionOfPoint_pointHomOn dP dQ hψ.hom T f (dQ.fibreHom T f)
    (dQ.fibreToSpace T f) (dQ.isPullback T f).w hd
  have hsec : dP.sectionOfPoint T f (dQ.fibreHom T f)
      (pointHomOn dP dQ hψ.hom T f (dQ.fibreHom T f) (dQ.fibreToSpace T f)
        (dQ.isPullback T f).w hd) (pointHomOn_comp dP dQ hψ.hom T f _ _ _ hd) =
      dP.sectionOfPoint T f (dQ.fibreHom T f) (dQ.fibreToSpace T f ≫ hψ.totalHom htop)
        (hψ.fibreToSpace_comp_totalHom_comp htop T f) := by
    congr 1
    exact (hψ.comp_totalHom htop T f (dQ.fibreHom T f) (dQ.fibreToSpace T f)
      (dQ.isPullback T f).w hd).symm
  rw [hsec, sectionOfPoint_fibreToSpace_comp_totalHom] at key
  have hlift : (hψ.hom T f).relativeMapDomain.ι ≫ (dQ.fibreIso T f).inv ≫
      liftToOpens (dQ.sectionOfPoint T f (dQ.fibreHom T f) (dQ.fibreToSpace T f)
        (dQ.isPullback T f).w) (hψ.hom T f).relativeMapDomain hd = 𝟙 _ := by
    refine (cancel_mono (hψ.hom T f).relativeMapDomain.ι).1 ?_
    rw [Category.assoc, Category.assoc, liftToOpens_comp_ι,
      RelativeProjPoints.sectionOfPoint_fibreToSpace, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp]
  rw [key, ← Category.assoc, ← Category.assoc, Category.assoc _ _ (liftToOpens _ _ _), hlift,
    Category.id_comp]

include htop in
/-- The inclusion of the domain of `r_{ψ|_T}` is an isomorphism when `U(ψ) = Q`. -/
theorem isIso_relativeMapDomain_ι : IsIso (hψ.hom T f).relativeMapDomain.ι := by
  rw [hψ.relativeMapDomain_eq_top htop T f, ← Scheme.topIso_hom]
  infer_instance

/-- **The fibre of `r_ψ` is a closed immersion of schemes** as soon as the scheme-level morphism
`r_{ψ|_T}` of Stacks 07ZG is one. -/
theorem isClosedImmersion_toScheme_map_totalHomFibreMap
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion (relativeMapHom (hψ.hom T f))) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hψ.totalHomFibreMap htop T f)) := by
  have hι := hψ.isIso_relativeMapDomain_ι htop T f
  have e : (BigFppfOver.toScheme B S hS).map (hψ.totalHomFibreMap htop T f) =
      (dQ.fibreIso T f).hom ≫ inv (hψ.hom T f).relativeMapDomain.ι ≫
        relativeMapHom (hψ.hom T f) ≫ (dP.fibreIso T f).inv := by
    rw [← hψ.ι_comp_toScheme_map_totalHomFibreMap htop T f]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, IsIso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc]
  rw [e]
  infer_instance

/-- **`r_ψ : Q ⟶ P` is a closed immersion of algebraic spaces** as soon as, over every scheme
point `T ⟶ X` of the base, the scheme-level morphism `r_{ψ|_T}` of Stacks 07ZG is a closed
immersion.  The base change of `r_ψ` along a scheme point `g : T' ⟶ P` is the base change of the
fibre of `r_ψ` over `g ≫ π` along the section of `T' ×_X P` attached to `g`. -/
theorem isClosedImmersion_totalHom
    (hci : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      _root_.AlgebraicGeometry.IsClosedImmersion (relativeMapHom (hψ.hom T f))) :
    IsClosedImmersion B S hS (hψ.totalHom htop) := by
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun a g => ?_
  obtain ⟨σ, hσ⟩ := dP.exists_yoneda_map_comp_fibreToSpace a (g ≫ πP) (𝟙 a) g
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp])
  have hc : IsClosedImmersion B S hS (yoneda.map (hψ.totalHomFibreMap htop a (g ≫ πP))) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _).2
      (hψ.isClosedImmersion_toScheme_map_totalHomFibreMap htop a (g ≫ πP) (hci a (g ≫ πP)))
  refine ⟨hc.rep.pullback (yoneda.map σ),
    hc.rep.fst (yoneda.map σ) ≫ dQ.fibreToSpace a (g ≫ πP), hc.rep.snd (yoneda.map σ), ?_,
    hc.property_snd _⟩
  have h := (hc.rep.isPullback (yoneda.map σ)).paste_horiz
    (hψ.isPullback_totalHomFibreMap htop a (g ≫ πP))
  rwa [hσ] at h

/-- **Stacks 085H (2), for the morphism of algebraic spaces.** If every restriction of `ψ` to a
scheme point of the base is an epimorphism in all sufficiently large degrees, then `U(ψ) = Q`
(Stacks 085H (1)) and `r_ψ : Q ⟶ P` is a closed immersion of algebraic spaces. -/
theorem isClosedImmersion_totalHom_of_eventually_epi
    (hsurj : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, Epi ((hψ.hom T f).app (d : ℤ))) :
    IsClosedImmersion B S hS
      (hψ.totalHom (hψ.relativeMapSubfunctor_eq_top_of_eventually_epi hsurj)) :=
  hψ.isClosedImmersion_totalHom _ fun T f =>
    isClosedImmersion_pointRelativeMapHom_of_eventually_epi hψ.hom hsurj T f

end RelativeProjHomPoints

/-! ### Subsheaves of `P` are determined on the fibre over a surjective étale chart -/

/-- The preimage of the range of a morphism along the base of a cartesian square is the range of
the opposite side. -/
theorem _root_.CategoryTheory.Subfunctor.preimage_range_of_isPullback {C : Type*} [Category C]
    {A₁ A₂ A₃ A₄ : Cᵒᵖ ⥤ Type u} {fst : A₁ ⟶ A₂} {snd : A₁ ⟶ A₃} {f : A₂ ⟶ A₄} {g : A₃ ⟶ A₄}
    (h : IsPullback fst snd f g) :
    (Subfunctor.range f).preimage g = Subfunctor.range snd := by
  ext Y y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨z, -, hz⟩ := Types.exists_of_isPullback (h.map ((evaluation Cᵒᵖ (Type u)).obj Y))
      x y hx
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨fst.app Y z, congrFun (congrArg (fun φ => φ.app Y) h.w) z⟩

namespace RelativeProjPoints

variable (d : RelativeProjPoints B S hS πP)

/-- **A subsheaf of `P` is determined by its pullback to the fibre over a surjective étale
scheme point of `X`, one inclusion at a time.**  A point `x` of `P` over `T` restricts, along the
surjective étale `T ×_X W ⟶ T`, to a point lying over the chart, which is the image of a point of
the fibre `W ×_X P`; membership in a subsheaf descends along that covering. -/
theorem le_of_preimage_fibreToSpace_le (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P)
    {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ X)
    (hwe : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (hws : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (G₁ G₂ : Subfunctor P)
    (hG₂ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G₂.toFunctor)
    (hle : G₁.preimage (d.fibreToSpace W w) ≤ G₂.preimage (d.fibreToSpace W w)) :
    G₁ ≤ G₂ := by
  intro Y x hx
  let u : yoneda.obj Y.unop ⟶ P := yonedaEquiv.symm x
  let f := u ≫ πP
  let T' := hwe.rep.pullback f
  let q : T' ⟶ Y.unop := hwe.rep.snd f
  let k : T' ⟶ W := hwe.rep.fst' f
  have hu : yoneda.map q ≫ u ≫ πP = yoneda.map k ≫ w := (hwe.rep.isPullback' f).w.symm
  obtain ⟨σ, hσ⟩ := d.exists_yoneda_map_comp_fibreToSpace W w k (yoneda.map q ≫ u)
    (by rw [Category.assoc, hu])
  have hres : P.map q.op x = (d.fibreToSpace W w).app (op T') σ := by
    have h1 := yonedaEquiv_yoneda_map_comp B S hS (d.fibreToSpace W w) σ
    rw [hσ] at h1
    exact (yonedaEquiv_symm_app_apply x (op T') q).symm.trans
      ((yonedaEquiv_yoneda_map_comp B S hS u q).symm.trans h1)
  refine mem_obj_of_surjective_etale B S hS hP G₂ hG₂ q (hws.property_snd f) (hwe.property_snd f)
    x ?_
  have h₁ : σ ∈ (G₁.preimage (d.fibreToSpace W w)).obj (op T') := by
    change (d.fibreToSpace W w).app (op T') σ ∈ G₁.obj (op T')
    rw [← hres]
    exact G₁.map q.op hx
  rw [hres]
  exact hle (op T') h₁

/-- **Two subsheaves of `P` with the same pullback to the fibre over a surjective étale scheme
point of `X` are equal.**  This is the descent step identifying two closed subspaces of the
relative Proj from their restrictions to the fibre over an étale chart. -/
theorem eq_of_preimage_fibreToSpace_eq (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P)
    {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ X)
    (hwe : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (hws : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (G₁ G₂ : Subfunctor P)
    (hG₁ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G₁.toFunctor)
    (hG₂ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G₂.toFunctor)
    (heq : G₁.preimage (d.fibreToSpace W w) = G₂.preimage (d.fibreToSpace W w)) :
    G₁ = G₂ :=
  le_antisymm (d.le_of_preimage_fibreToSpace_le hP w hwe hws G₁ G₂ hG₂ heq.le)
    (d.le_of_preimage_fibreToSpace_le hP w hwe hws G₂ G₁ hG₁ heq.ge)

end RelativeProjPoints

end AlgebraicGeometry.Space

end
