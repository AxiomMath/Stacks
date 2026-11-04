module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase

/-!
# The base change to the strict henselisation is the limit of the base changes

Let `B` be a big étale site containing a scheme `S`, let `s` be a geometric point of `S` and let
`f : X ⟶ S` be any morphism of schemes. The strict henselisation `Spec(𝒪^{sh}_{S,s})` is the
limit of the étale neighbourhoods of `s` (`AlgebraicGeometry.strictHenselizationConeIsLimit`),
and fibre products commute with limits, so

`X ×_S Spec(𝒪^{sh}_{S,s}) = lim_{(V, v)} X ×_S V`.

[Stacks, Tag 03Q9] identifies `(R^n f_* ℱ)_s` with `H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}ℱ)`;
its proof rests on the identification above.

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodStructureMaps` — the étale structure morphisms of the
  neighbourhoods of `s`, as a natural transformation to the constant functor `S`.
* `AlgebraicGeometry.etaleNeighborhoodOverDiagram` — the neighbourhoods as a diagram of schemes
  *over* `S`.
* `AlgebraicGeometry.strictHenselizationOverCone` — the strict henselisation with its structure
  morphism to `S`, as a cone on that diagram.
* `AlgebraicGeometry.etaleNeighborhoodBaseChangeDiagram` — the diagram `(V, v) ↦ X ×_S V`.
* `AlgebraicGeometry.strictHenselizationBaseChangeCone` — the cone on it with vertex
  `X ×_S Spec(𝒪^{sh}_{S,s})`.

## Main results

* `AlgebraicGeometry.isLimitStrictHenselizationOverCone` — the strict henselisation is the limit
  of the étale neighbourhoods in the category of schemes over `S`.
* `AlgebraicGeometry.isLimitStrictHenselizationBaseChangeCone` — `X ×_S Spec(𝒪^{sh}_{S,s})` is
  the limit of the `X ×_S V`.
* `AlgebraicGeometry.isLimitStrictHenselizationBaseChangeAffineCone` — the same limit over the
  small cofinal family of affine neighbourhoods.

## Implementation notes

The fibre product `X ×_S Spec(𝒪^{sh}_{S,s})` is spelled here with the strict henselisation in the
first position, as `Stacks.EtaleCohomology.strictHenselizationPullback` spells it;
`AlgebraicGeometry.strictHenselizationBaseChangeConePtIso` is the canonical symmetry onto the
other spelling, `AlgebraicGeometry.strictHenselizationBaseChange`.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The étale structure morphisms of the neighbourhoods of a geometric point `s` of `S`, as a
natural transformation from the neighbourhood diagram to the constant functor `S`. -/
def etaleNeighborhoodStructureMaps :
    etaleNeighborhoodDiagram B S hS s ⟶
      (Functor.const (geometricPointFiber B S hS s).Elements).obj S where
  app V := B.inclusion.map V.1.obj.hom
  naturality _ _ h := by simpa using SmallEtale.toScheme_map_comp B S hS h.1

/-- The étale neighbourhoods of a geometric point `s` of `S`, as a diagram of schemes over `S`. -/
abbrev etaleNeighborhoodOverDiagram :
    (geometricPointFiber B S hS s).Elements ⥤ Over S :=
  Over.lift (etaleNeighborhoodDiagram B S hS s) (etaleNeighborhoodStructureMaps B S hS s)

/-- The strict henselisation of `S` at `s`, with its structure morphism to `S`, as a cone on the
diagram of étale neighbourhoods of `s` in the category of schemes over `S`. -/
@[sga "7 XV 2.1.1" "partial"]
abbrev strictHenselizationOverCone : Cone (etaleNeighborhoodOverDiagram B S hS s) :=
  Over.liftCone (etaleNeighborhoodDiagram B S hS s) (etaleNeighborhoodStructureMaps B S hS s)
    (strictHenselizationCone B S hS s) (strictHenselizationToBase B S hS s)
    (strictHenselizationCone_π_comp_hom_eq B S hS s)

/-- The strict henselisation of `S` at `s` is the limit of the étale neighbourhoods of `s` in the
category of schemes over `S`. -/
def isLimitStrictHenselizationOverCone :
    IsLimit (strictHenselizationOverCone B S hS s) :=
  haveI : Nonempty (geometricPointFiber B S hS s).Elements := ⟨IsCofiltered.nonempty.some⟩
  Over.isLimitLiftCone _ _ _ _ _ (strictHenselizationConeIsLimit B S hS s)

section BaseChange

variable {X : Scheme.{u}} (f : X ⟶ S)

/-- The diagram `(V, v) ↦ X ×_S V` of base changes of `f` to the étale neighbourhoods of `s`. -/
abbrev etaleNeighborhoodBaseChangeDiagram :
    (geometricPointFiber B S hS s).Elements ⥤ Scheme.{u} :=
  etaleNeighborhoodOverDiagram B S hS s ⋙ Over.pullback f ⋙ Over.forget X

/-- The value of `etaleNeighborhoodBaseChangeDiagram` at a neighbourhood `(V, v)` is the fibre
product `V ×_S X`. -/
theorem etaleNeighborhoodBaseChangeDiagram_obj (V : (geometricPointFiber B S hS s).Elements) :
    (etaleNeighborhoodBaseChangeDiagram B S hS s f).obj V =
      pullback (B.inclusion.map V.1.obj.hom) f :=
  rfl

/-- The base change `X ×_S Spec(𝒪^{sh}_{S,s})`, as a cone on the diagram of the base changes
`X ×_S V`: on the neighbourhood factor the leg is the leg of the limit cone of the
neighbourhoods, on the `X` factor it is the identity. -/
abbrev strictHenselizationBaseChangeCone :
    Cone (etaleNeighborhoodBaseChangeDiagram B S hS s f) :=
  (Over.forget X).mapCone ((Over.pullback f).mapCone (strictHenselizationOverCone B S hS s))

/-- The vertex of `strictHenselizationBaseChangeCone` is the fibre product
`Spec(𝒪^{sh}_{S,s}) ×_S X`. -/
theorem strictHenselizationBaseChangeCone_pt :
    (strictHenselizationBaseChangeCone B S hS s f).pt =
      pullback (strictHenselizationToBase B S hS s) f :=
  rfl

/-- The leg of `strictHenselizationBaseChangeCone` at `(V, v)`, followed by the projection to
`V`, is the projection to `Spec(𝒪^{sh}_{S,s})` followed by the leg of the limit cone of the
neighbourhoods. -/
@[simp]
theorem strictHenselizationBaseChangeCone_π_app_comp_fst
    (V : (geometricPointFiber B S hS s).Elements) :
    (strictHenselizationBaseChangeCone B S hS s f).π.app V ≫
        pullback.fst (B.inclusion.map V.1.obj.hom) f =
      pullback.fst (strictHenselizationToBase B S hS s) f ≫
        (strictHenselizationCone B S hS s).π.app V :=
  pullback.lift_fst _ _ _

/-- The leg of `strictHenselizationBaseChangeCone` at `(V, v)`, followed by the projection to
`X`, is the projection to `X`. -/
@[simp]
theorem strictHenselizationBaseChangeCone_π_app_comp_snd
    (V : (geometricPointFiber B S hS s).Elements) :
    (strictHenselizationBaseChangeCone B S hS s f).π.app V ≫
        pullback.snd (B.inclusion.map V.1.obj.hom) f =
      pullback.snd (strictHenselizationToBase B S hS s) f :=
  pullback.lift_snd _ _ _

/-- The vertex of `strictHenselizationBaseChangeCone`, the fibre product with the strict
henselisation in the first position, is isomorphic to the fibre product with `X` in the first
position. -/
def strictHenselizationBaseChangeConePtIso :
    (strictHenselizationBaseChangeCone B S hS s f).pt ≅
      pullback f (strictHenselizationToBase B S hS s) :=
  pullbackSymmetry _ _

/-- For any morphism `f : X ⟶ S` and any geometric
point `s` of `S`, the base change `X ×_S Spec(𝒪^{sh}_{S,s})` is the limit of the base changes
`X ×_S V` over the étale neighbourhoods `(V, v)` of `s`. -/
def isLimitStrictHenselizationBaseChangeCone :
    IsLimit (strictHenselizationBaseChangeCone B S hS s f) :=
  haveI : IsConnected (geometricPointFiber B S hS s).Elements := IsCofiltered.isConnected _
  isLimitOfPreserves (Over.forget X)
    (isLimitOfPreserves (Over.pullback f) (isLimitStrictHenselizationOverCone B S hS s))

/-- The base change `X ×_S Spec(𝒪^{sh}_{S,s})` is the limit of the base changes `X ×_S V` over
the small cofinal family of *affine* étale neighbourhoods `(V, v)` of `s`. -/
def isLimitStrictHenselizationBaseChangeAffineCone :
    IsLimit ((strictHenselizationBaseChangeCone B S hS s f).whisker
      (etaleNeighborhoodAffineInclusion B S hS s)) :=
  (Functor.Initial.isLimitWhiskerEquiv (etaleNeighborhoodAffineInclusion B S hS s) _).symm
    (isLimitStrictHenselizationBaseChangeCone B S hS s f)

end BaseChange

end AlgebraicGeometry

end
