module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap

/-!
# Specialization of geometric stalks of abelian étale sheaves

Let `S` be a scheme, `s` a geometric point of `S` and `t` a geometric point of
`Spec(𝒪^{sh}_{S,s})`, the strict henselization of `S` at `s`. Writing
`p : Spec(𝒪^{sh}_{S,s}) ⟶ S` for the structure morphism, the composite `t ≫ p` is a geometric
point of `S` which the image of `t` specializes from. For an abelian sheaf `F` on the small
étale site of `S` there is a *specialization map*

`sp : F_s ⟶ F_{t ≫ p}`

between the two geometric stalks: a germ at `s` of a section over an étale neighbourhood `W` of
`s` is sent to the germ at `t ≫ p` of the same section, over the same `W`, taken at the lift of
`t ≫ p` to `W` obtained from the canonical factorization `Spec(𝒪^{sh}_{S,s}) ⟶ W ⟶ S`.

## Main definitions

* `AlgebraicGeometry.geometricStalkToPullbackSectionsAb` — the canonical map
  `F_x ⟶ Γ(x, x⁻¹F)` from the stalk of an abelian étale sheaf at a geometric point `x` of `X`
  to the global sections of its inverse image on the spectrum of the residue field of `x`.
* `AlgebraicGeometry.specializationEtaleNeighborhoodLift` — the lift of `t ≫ p` to an étale
  neighbourhood `(W, v)` of `s`, namely `t` followed by the canonical morphism
  `Spec(𝒪^{sh}_{S,s}) ⟶ W`.
* `AlgebraicGeometry.smallEtaleSpecializationStalkAb` — the specialization map
  `sp : F_s ⟶ F_{t ≫ p}` on abelian étale sheaves, as a natural transformation of stalk
  functors.
* `AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAb` — the specialization map
  `sp : K_s ⟶ K_{t ≫ p}` in `D(Ab)` for `K` in the unbounded derived category of abelian
  sheaves on the small étale site of `S`.

## Main results

* `AlgebraicGeometry.smallEtaleStalkAb_hom_ext` — two maps out of a geometric stalk agree as
  soon as they agree on every germ.
* `AlgebraicGeometry.geometricStalkToPullbackSectionsAb_toPresheafFiber` — on the germ at `x` of
  a section over an étale neighbourhood, the comparison to sections on the geometric point is
  restriction of that section.
* `AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAb_app` — on every complex the
  specialization map on derived stalks is the degreewise specialization map.
* `AlgebraicGeometry.smallEtaleSpecializationStalkAb_toPresheafFiber` — the specialization map
  carries the germ at `s` of a section `σ` over an étale neighbourhood `(W, v)` to the germ at
  `t ≫ p` of `σ` over `(W, v')`, where `v'` is the lift of the specialized point.
* `AlgebraicGeometry.etaleStalkToSectionsAb_eq_smallEtaleSpecializationStalkAb` — one half of
  [Stacks, Tag 0GJ3]: composed with the comparison `F_{t ≫ p} ⟶ Γ(t, (t ≫ p)⁻¹F)` of Stacks
  03Q1, the specialization map is the canonical map `F_s ⟶ Γ(t, (t ≫ p)⁻¹F)` which restricts a
  germ at `s` along `t ⟶ Spec(𝒪^{sh}_{S,s}) ⟶ W`. The factorization of that canonical map
  through `Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is not part of the statement.

## References

* [Stacks Project, Tag 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
* [Stacks Project, Tag 0GJ3](https://stacks.math.columbia.edu/tag/0GJ3)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-! ### Sections of an inverse image on a geometric point -/

section PullbackSections

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- Two maps out of the stalk of an abelian étale sheaf at a geometric point agree as soon as they
agree on the germ of every section over every étale neighbourhood of that point. -/
theorem smallEtaleStalkAb_hom_ext (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) {T : Ab.{u + 1}}
    {f g : (smallEtaleStalkAb x).obj F ⟶ T}
    (h : ∀ (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W),
      (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫ f =
        (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫ g) :
    f = g :=
  (Scheme.pointSmallEtale x).presheafFiber_hom_ext h

/-- The germ-level map: restriction of a section of an abelian étale sheaf over an étale
neighbourhood `(W, v)` of a geometric point `x` of `X` to a global section over the spectrum of
the residue field of `x` of the inverse image of that sheaf, along the lift `v`. -/
def geometricStalkPullbackSectionsStage (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    F.obj.obj (op W) ⟶
      (smallEtalePullbackAb x ⋙ Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}).obj F :=
  (smallEtaleSectionsPullbackAb x W v.left (Over.w v)).app F

/-- The germ-level maps are compatible with restriction along a morphism of étale
neighbourhoods. -/
theorem map_comp_geometricStalkPullbackSectionsStage
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) {W V : X.Etale} (m : W ⟶ V)
    (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    F.obj.map m.op ≫ geometricStalkPullbackSectionsStage x F W v =
      geometricStalkPullbackSectionsStage x F V
        ((Scheme.pointSmallEtale x).fiber.map m v) := by
  have hleft : ((Scheme.pointSmallEtale x).fiber.map m v).left = v.left ≫ m.left := rfl
  have h := map_comp_smallEtaleSectionsPullbackAb x W v.left m (Over.w v)
    (hleft ▸ Over.w ((Scheme.pointSmallEtale x).fiber.map m v))
  exact congrArg (fun σ => NatTrans.app σ F)
    (h.trans (smallEtaleSectionsPullbackAb_congr x V (v.left ≫ m.left) _
      (Over.w ((Scheme.pointSmallEtale x).fiber.map m v)) hleft.symm))

/-- The naturality in the sheaf of the germ-level maps. -/
theorem geometricStalkPullbackSectionsStage_naturality
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (α : F ⟶ G) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    α.hom.app (op W) ≫ geometricStalkPullbackSectionsStage x G W v =
      geometricStalkPullbackSectionsStage x F W v ≫
        (smallEtalePullbackAb x ⋙
          Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}).map α :=
  (smallEtaleSectionsPullbackAb x W v.left (Over.w v)).naturality α

/-- The canonical map `F_x ⟶ Γ(x, x⁻¹F)` from the stalk of an abelian sheaf on the small étale site
of `X` at a geometric point `x` to the global sections of its inverse image on the spectrum of the
residue field of `x`. On the germ of a section over an étale neighbourhood of `x` it is restriction
of that section along the chosen lift of `x`. -/
def geometricStalkToPullbackSectionsAb :
    smallEtaleStalkAb x ⟶
      smallEtalePullbackAb x ⋙ Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1} :=
  smallEtaleStalkDesc x _ (geometricStalkPullbackSectionsStage x)
    (fun F _ _ m v => map_comp_geometricStalkPullbackSectionsStage x F m v)
    (fun α W v => geometricStalkPullbackSectionsStage_naturality x α W v)

/-- On the germ at `x` of a section over an étale neighbourhood `(W, v)`, the comparison to
sections on the geometric point is restriction of that section along `v`. -/
theorem geometricStalkToPullbackSectionsAb_toPresheafFiber
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj W) :
    (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫
        (geometricStalkToPullbackSectionsAb x).app F =
      (smallEtaleSectionsPullbackAb x W v.left (Over.w v)).app F :=
  toPresheafFiber_comp_smallEtaleStalkDesc x _ (geometricStalkPullbackSectionsStage x) _ _ F W v

end PullbackSections

/-! ### The specialization map on stalks -/

section Specialization

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- An étale neighbourhood `(W, v)` of a geometric point `s` of `S` is an étale neighbourhood of
the geometric point `t ≫ p` of `S` determined by a geometric point `t` of the strict
henselization at `s`: the lift of `t ≫ p` is `t` followed by the canonical morphism
`Spec(𝒪^{sh}_{S,s}) ⟶ W` over `S` which carries the canonical geometric point of the strict
henselization to `v`. -/
def specializationEtaleNeighborhoodLift (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    (Scheme.pointSmallEtale (t.hom ≫ strictHenselizationToBase B S hS s)).fiber.obj W :=
  Over.homMk (t.hom ≫ strictHenselizationNeighborhoodLift B S hS s W v) <| by
    change (t.hom ≫ strictHenselizationNeighborhoodLift B S hS s W v) ≫ W.hom =
      t.hom ≫ strictHenselizationToBase B S hS s
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]

/-- The lift of the specialized point to an étale neighbourhood is, as a morphism of schemes,
the geometric point of the strict henselization followed by the canonical morphism from the
strict henselization into that neighbourhood. -/
theorem specializationEtaleNeighborhoodLift_left (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    (specializationEtaleNeighborhoodLift B S hS s t W v).left =
      t.hom ≫ strictHenselizationNeighborhoodLift B S hS s W v :=
  rfl

/-- Passing from an étale neighbourhood of `s` to an étale neighbourhood of `t ≫ p` is compatible
with morphisms of neighbourhoods. -/
theorem specializationEtaleNeighborhoodLift_naturality {W V : S.Etale} (m : W ⟶ V)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    (Scheme.pointSmallEtale (t.hom ≫ strictHenselizationToBase B S hS s)).fiber.map m
        (specializationEtaleNeighborhoodLift B S hS s t W v) =
      specializationEtaleNeighborhoodLift B S hS s t V
        ((Scheme.pointSmallEtale s.hom).fiber.map m v) := by
  apply Over.OverMorphism.ext
  change (t.hom ≫ strictHenselizationNeighborhoodLift B S hS s W v) ≫ m.left =
    t.hom ≫ strictHenselizationNeighborhoodLift B S hS s V
      ((Scheme.pointSmallEtale s.hom).fiber.map m v)
  rw [Category.assoc, strictHenselizationNeighborhoodLift_comp_left]

/-- The germ-level map of the specialization map: the germ at `t ≫ p` of a section over an
étale neighbourhood `(W, v)` of `s`, taken at the lift of `t ≫ p` determined by `(W, v)`. -/
def specializationStalkStage (F : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    F.obj.obj (op W) ⟶
      (smallEtaleStalkAb (t.hom ≫ strictHenselizationToBase B S hS s)).obj F :=
  (Scheme.pointSmallEtale (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber W
    (specializationEtaleNeighborhoodLift B S hS s t W v) F.obj

/-- The germ-level maps of the specialization map are compatible with restriction along a morphism
of étale neighbourhoods. -/
theorem map_comp_specializationStalkStage (F : Sheaf (smallEtaleTopology S) Ab.{u + 1})
    {W V : S.Etale} (m : W ⟶ V) (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    F.obj.map m.op ≫ specializationStalkStage B S hS s t F W v =
      specializationStalkStage B S hS s t F V
        ((Scheme.pointSmallEtale s.hom).fiber.map m v) :=
  ((Scheme.pointSmallEtale (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber_w m
      (specializationEtaleNeighborhoodLift B S hS s t W v) F.obj).trans
    (congrArg
      (fun w => (Scheme.pointSmallEtale
        (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber V w F.obj)
      (specializationEtaleNeighborhoodLift_naturality B S hS s t m v))

/-- The naturality in the sheaf of the germ-level maps of the specialization map. -/
theorem specializationStalkStage_naturality
    {F G : Sheaf (smallEtaleTopology S) Ab.{u + 1}} (α : F ⟶ G) (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    α.hom.app (op W) ≫ specializationStalkStage B S hS s t G W v =
      specializationStalkStage B S hS s t F W v ≫
        (smallEtaleStalkAb (t.hom ≫ strictHenselizationToBase B S hS s)).map α :=
  ((Scheme.pointSmallEtale
    (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber_naturality α.hom W
      (specializationEtaleNeighborhoodLift B S hS s t W v)).symm

/-- **The specialization map on stalks.** For an abelian sheaf `F` on the small étale site of
`S`, a geometric point `s` of `S` and a geometric point `t` of the strict henselization of `S`
at `s`, the map `sp : F_s ⟶ F_{t ≫ p}` which carries the germ at `s` of a section over an étale
neighbourhood `(W, v)` of `s` to the germ at `t ≫ p` of the same section over the same `W`,
taken at the lift of `t ≫ p` determined by `(W, v)`. -/
def smallEtaleSpecializationStalkAb :
    smallEtaleStalkAb s.hom ⟶
      smallEtaleStalkAb (t.hom ≫ strictHenselizationToBase B S hS s) :=
  smallEtaleStalkDesc s.hom _ (specializationStalkStage B S hS s t)
    (fun F _ _ m v => map_comp_specializationStalkStage B S hS s t F m v)
    (fun α W v => specializationStalkStage_naturality B S hS s t α W v)

/-- The specialization map carries the germ at `s` of a section over an étale neighbourhood
`(W, v)` to the germ at `t ≫ p` of that section over `(W, v')`, where `v'` is the lift of the
specialized point determined by `(W, v)`. -/
theorem smallEtaleSpecializationStalkAb_toPresheafFiber
    (F : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    (Scheme.pointSmallEtale s.hom).toPresheafFiber W v F.obj ≫
        (smallEtaleSpecializationStalkAb B S hS s t).app F =
      specializationStalkStage B S hS s t F W v :=
  toPresheafFiber_comp_smallEtaleStalkDesc s.hom _ (specializationStalkStage B S hS s t)
    _ _ F W v

/-- **The specialization map is pullback by `t`.** Composed with the comparison
`F_{t ≫ p} ⟶ Γ(t, (t ≫ p)⁻¹F)` of Stacks 03Q1, the specialization map on stalks is the canonical
map `F_s ⟶ Γ(t, (t ≫ p)⁻¹F)` of Stacks 0GJN, which restricts the germ at `s` of a section over an
étale neighbourhood `W` along the composite `t ⟶ Spec(𝒪^{sh}_{S,s}) ⟶ W`. -/
@[stacks 0GJ3 "the specialization map is pullback by the geometric point of the strict
henselization, after the identification of the stalk at the specialized point with sections on
that point. The factorization of the left-hand side through sections over the strict
henselization itself is not proved here; see the module docstring."]
theorem etaleStalkToSectionsAb_eq_smallEtaleSpecializationStalkAb :
    etaleStalkToSectionsAb B S hS s t.hom =
      smallEtaleSpecializationStalkAb B S hS s t ≫
        geometricStalkToPullbackSectionsAb (t.hom ≫ strictHenselizationToBase B S hS s) := by
  ext F : 2
  refine smallEtaleStalkAb_hom_ext s.hom F fun W v => ?_
  rw [etaleStalkToSectionsAb_toPresheafFiber, NatTrans.comp_app]
  refine Eq.symm (Eq.trans (Eq.symm (Category.assoc
    ((Scheme.pointSmallEtale s.hom).toPresheafFiber W v F.obj)
    ((smallEtaleSpecializationStalkAb B S hS s t).app F)
    ((geometricStalkToPullbackSectionsAb
      (t.hom ≫ strictHenselizationToBase B S hS s)).app F))) ?_)
  rw [smallEtaleSpecializationStalkAb_toPresheafFiber]
  exact geometricStalkToPullbackSectionsAb_toPresheafFiber
    (t.hom ≫ strictHenselizationToBase B S hS s) F W
    (specializationEtaleNeighborhoodLift B S hS s t W v)

end Specialization

/-! ### The specialization map on unbounded derived categories -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- **The specialization map on derived stalks.** For an object `K` of the unbounded derived
category of abelian sheaves on the small étale site of `S`, the map `sp : K_s ⟶ K_{t ≫ p}` in
`D(Ab)`, natural in `K`. -/
def smallEtaleDerivedSpecializationStalkAb :
    smallEtaleDerivedStalkAb s.hom ⟶
      smallEtaleDerivedStalkAb (t.hom ≫ strictHenselizationToBase B S hS s) :=
  Localization.liftNatTrans DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology S) Ab.{u + 1}) (.up ℤ))
    ((smallEtaleStalkAb s.hom).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    ((smallEtaleStalkAb (t.hom ≫ strictHenselizationToBase B S hS s)).mapHomotopyCategory
      (.up ℤ) ⋙ DerivedCategory.Qh)
    (smallEtaleDerivedStalkAb s.hom)
    (smallEtaleDerivedStalkAb (t.hom ≫ strictHenselizationToBase B S hS s))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (smallEtaleSpecializationStalkAb B S hS s t) (.up ℤ))
      DerivedCategory.Qh)

/-- On every complex of abelian sheaves on the small étale site of `S`, the specialization map on
derived stalks is the degreewise specialization map, read through the identifications of the
degreewise actions of the two stalk functors with their actions on derived categories. -/
theorem smallEtaleDerivedSpecializationStalkAb_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology S) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedSpecializationStalkAb B S hS s t).app (DerivedCategory.Qh.obj J) =
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (smallEtaleSpecializationStalkAb B S hS s t) (.up ℤ)).app J) ≫
        (smallEtaleStalkAb
          (t.hom ≫ strictHenselizationToBase B S hS s)).mapDerivedCategoryFactorsh.inv.app J :=
  Localization.liftNatTrans_app DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology S) Ab.{u + 1}) (.up ℤ)) _ _ _ _ _ J

end Derived

end AlgebraicGeometry

end
