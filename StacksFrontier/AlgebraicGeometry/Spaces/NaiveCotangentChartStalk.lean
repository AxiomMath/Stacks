module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkIndEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageChartRingHom
public import StacksFrontier.CategoryTheory.Sites.Point.OverGerms
public import StacksFrontier.RingTheory.NaiveCotangent.H1IndEtaleSquare
public import StacksFrontier.RingTheory.NaiveCotangent.SquareMap

/-!
# The first homology of the naive cotangent complex of a chart diagram at a geometric point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a commutative
diagram of étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R`
of `Y`.  Localize the small étale site of `X` at `V`, and let `x` be a geometric point of `X`
with a lift `p` to `V`; it is a point of the localized site.  At that point the stalks of
`f⁻¹𝒪_Y` and of `𝒪_X` are filtered colimits of étale `R`-algebras and of étale `A`-algebras
respectively, and so the base change map

`(f⁻¹𝒪_Y)_x`-…: `𝒪_{X,x} ⊗_A H₁(L_{A/R}) ⟶ H₁(L_{𝒪_{X,x}/(f⁻¹𝒪_Y)_x})`

is bijective, by the degree `1` part of Stacks 0D08
(`Algebra.bijective_h1Cotangent_map_liftBaseChange_of_ind_etale`).

The ind-étaleness of the two stalks is that of the geometric stalks of the structure sheaves
(`AlgebraicGeometry.Space.geometricStalk_ind_etale`), carried to the localized site by Stacks
04H2 and, for `f⁻¹𝒪_Y`, along the fibre comparison of Stacks 04K2 (4), whose compatibility with
the unit of `f⁻¹ ⊣ f_*` on charts is
`AlgebraicGeometry.Space.toPresheafFiber_inverseImageChartUnit`.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramRingHom`: the ring map `R → A` of the diagram.
* `AlgebraicGeometry.Space.chartStalkPoint`: the point of the localized site.

## Main results

* `AlgebraicGeometry.Space.ind_etale_of_ringEquiv`: ind-étaleness transported along a ring
  isomorphism.
* `AlgebraicGeometry.Space.chartStalk_ind_etale` and
  `AlgebraicGeometry.Space.chartBaseStalk_ind_etale`: the two ind-étaleness statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite Algebra

universe u

namespace AlgebraicGeometry.Space

/-- **Ind-étaleness along a ring isomorphism.** -/
theorem ind_etale_of_ringEquiv {R B B' : Type u} [CommRing R] [CommRing B] [CommRing B']
    (φ : R →+* B) (φ' : R →+* B') (e : B ≃+* B') (he : ∀ r, e (φ r) = φ' r)
    (h : letI := φ.toAlgebra; (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R B)) :
    letI := φ'.toAlgebra; (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R B') := by
  let := φ.toAlgebra
  let := φ'.toAlgebra
  let e' : B ≃ₐ[R] B' := { e with commutes' := he }
  exact ((CommAlgCat.etale.{u} R).ind.{u}).prop_of_iso (CommAlgCat.isoMk e') h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-- The ring map `R = 𝒪_Y(W) → A = 𝒪_X(V)` of a diagram of étale scheme charts: pullback of
regular functions along its vertical morphism. -/
abbrev chartDiagramRingHom :
    ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) →+*
      ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)) :=
  (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g))).hom

variable {x : GeometricPoint B S hS X.1} (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj d.U)

/-- The point of the small étale site of `X` localized at `V` given by a geometric point with a
lift `p` to `V`. -/
abbrev chartStalkPoint : Point.{u} ((SmallEtale.topology B S hS X.1).over d.U) :=
  (etaleSitePoint B S hS X.1 x X.2).over p

/-- The lift `p`, as an element of the fibre of the localized point at the terminal object. -/
abbrev chartStalkPointTop : (chartStalkPoint B S hS f d p).fiber.obj (Over.mk (𝟙 d.U)) :=
  ⟨p, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 (by
    change (geometricFiber B S hS X.1 x).map (𝟙 d.U) p = p
    rw [CategoryTheory.Functor.map_id]
    rfl)⟩

/-- The structure sheaf of `X`, restricted to the localized site. -/
abbrev chartStructurePresheaf : (Over d.U)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget d.U).op ⋙ (smallEtaleRingedTopos B S hS X).O.obj

/-- `f⁻¹𝒪_Y`, restricted to the localized site. -/
abbrev chartBasePresheaf : (Over d.U)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget d.U).op ⋙ (inverseImageStructureSheaf B S hS f).obj

/-- The germ `A → 𝒪_{X,x}` at the terminal object of the localized site. -/
abbrev chartStalkGerm :
    ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)) →+*
      ToType (((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).obj
        (chartStructurePresheaf B S hS f d)) :=
  ((chartStalkPoint B S hS f d p).toPresheafFiber (Over.mk (𝟙 d.U))
    (chartStalkPointTop B S hS f d p) (chartStructurePresheaf B S hS f d)).hom

/-- The map `R → (f⁻¹𝒪_Y)_x`: the unit on charts followed by the germ at the terminal object of
the localized site. -/
abbrev chartBaseStalkGerm :
    ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) →+*
      ToType (((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).obj
        (chartBasePresheaf B S hS f d)) :=
  ((chartStalkPoint B S hS f d p).toPresheafFiber (Over.mk (𝟙 d.U))
    (chartStalkPointTop B S hS f d p) (chartBasePresheaf B S hS f d)).hom.comp
    (inverseImageChartUnitRingHom B S hS f d)

/-- The comparison of fibres along the localization carries the germ at the terminal object of the
localized site to the germ at `U`. -/
private theorem presheafFiberOverIso_germ
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ CommRingCat.{u}) (a : ToType (F.obj (op d.U))) :
    ((Point.presheafFiberOverIso (etaleSitePoint B S hS X.1 x X.2) p CommRingCat.{u}).app F).hom
      (((chartStalkPoint B S hS f d p).toPresheafFiber (Over.mk (𝟙 d.U))
        (chartStalkPointTop B S hS f d p) ((Over.forget d.U).op ⋙ F)).hom a) =
      ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber d.U p F).hom a :=
  ConcreteCategory.congr_hom
    (Point.toPresheafFiber_presheafFiberOverIso_hom (etaleSitePoint B S hS X.1 x X.2) p
      CommRingCat.{u} F (Over.mk (𝟙 d.U)) (chartStalkPointTop B S hS f d p)) a

/-- **The stalk of `𝒪_X` is ind-étale over `A`.** -/
theorem chartStalk_ind_etale
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U)) :
    letI := (chartStalkGerm B S hS f d p).toAlgebra
    (CommAlgCat.etale.{u} ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))).ind.{u}
      (CommAlgCat.of ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))
        (((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).obj
          (chartStructurePresheaf B S hS f d))) := by
  let e := ((Point.presheafFiberOverIso (etaleSitePoint B S hS X.1 x X.2) p CommRingCat.{u}).app
    (smallEtaleRingedTopos B S hS X).O.obj).commRingCatIsoToRingEquiv
  exact ind_etale_of_ringEquiv _ _ e.symm
    (fun a => e.symm_apply_eq.2 (presheafFiberOverIso_germ B S hS f d p _ a).symm)
    (geometricStalk_ind_etale B S hS X d.U hU x p)

/-- **The stalk of `f⁻¹𝒪_Y` is ind-étale over `R`.** -/
theorem chartBaseStalk_ind_etale
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := (chartBaseStalkGerm B S hS f d p).toAlgebra
    (CommAlgCat.etale.{u} ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))).ind.{u}
      (CommAlgCat.of ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))
        (((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).obj
          (chartBasePresheaf B S hS f d))) := by
  let e₁ := ((smallEtaleInverseImageFiberRingIso B S hS f x).app
    (smallEtaleRingedTopos B S hS Y).O).commRingCatIsoToRingEquiv
  let e₂ := ((Point.presheafFiberOverIso (etaleSitePoint B S hS X.1 x X.2) p CommRingCat.{u}).app
    (inverseImageStructureSheaf B S hS f).obj).commRingCatIsoToRingEquiv
  refine ind_etale_of_ringEquiv _ _ (e₁.trans e₂.symm) (fun r => ?_)
    (geometricStalk_ind_etale B S hS Y d.V hW (geometricPointMap f.hom x)
      (chartDiagramImageFiber B S hS f d p))
  apply e₂.injective
  refine (e₂.apply_symm_apply (e₁ _)).trans ?_
  refine Eq.trans ?_ (presheafFiberOverIso_germ B S hS f d p _ _).symm
  exact (toPresheafFiber_inverseImageChartUnit B S hS f d x p r).symm

end AlgebraicGeometry.Space

end
