module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartModule

/-!
# Isomorphisms of the determinant on an affine chart

Let `X` be a scheme, `V` an affine open of `X` and `L`, `K` perfect objects of `D(𝒪_X)` of
Tor-amplitude in `[-1, 0]`. The determinant `AlgebraicGeometry.DeterminantTwoTerm.chartDet` of `L`
on `V` is the sheaf associated with the determinant module of the chart complex, pulled back along
`AlgebraicGeometry.IsAffineOpen.isoSpec`, so a linear equivalence of the two determinant modules
over `Γ(X, V)` induces an isomorphism of the determinants on `V`. This file names that induced
isomorphism and records that it is functorial: the identity goes to the identity and a composite to
the composite.

This is the chart-level half of the functoriality of the determinant on an arbitrary scheme: the
determinant of an isomorphism is glued from these.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecOfEquiv` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetOfEquiv`: **the isomorphism of determinants on a
  chart induced by a linear equivalence of the determinant modules**, on `Spec Γ(X, V)` and on the
  open subscheme `V`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetOfEquiv_refl` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetOfEquiv_trans`: the induced isomorphism is
  functorial in the linear equivalence.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecOfEquiv_chartDelta`: **a linear equivalence
  carrying the canonical element to the canonical element induces an isomorphism carrying the
  canonical global section on the chart to the canonical global section.**

## Implementation notes

Both steps are the image of a functor — `AlgebraicGeometry.tilde.functor` and
`AlgebraicGeometry.Scheme.Modules.pullback` — so functoriality is
`CategoryTheory.Functor.map_id` and `CategoryTheory.Functor.map_comp` once
`LinearEquiv.toModuleIso` is known to be functorial, and that is checked on the underlying linear
maps. `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpec_eq_tilde` says the determinant on a chart
is literally an associated sheaf, by definitional unfolding, which is what lets the source and
target of the induced isomorphism be spelled `chartDetSpec`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- The determinant module over `Γ(X, V)` of the chart complex of `L` on an affine open `V`: the
invertible module of More on Algebra, Section 0FJI whose associated sheaf is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpec`. -/
abbrev chartDetModule (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    ModuleCat.{u} Γ(X, (V.1 : X.Opens)) :=
  ((det Γ(X, (V.1 : X.Opens))).obj ⟨chartComplex L V⟩).of.obj

/-- **The isomorphism of the determinants on the spectrum of an affine open induced by a linear
equivalence of the determinant modules.** -/
def chartDetSpecOfEquiv {L K : PerfectTwoTermAmplitude X} (V : X.affineOpens)
    (e : chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V) :
    chartDetSpec L V ≅ chartDetSpec K V :=
  (tilde.functor Γ(X, (V.1 : X.Opens))).mapIso e.toModuleIso

/-- **The isomorphism of the determinants on an affine open induced by a linear equivalence of the
determinant modules**, obtained from `chartDetSpecOfEquiv` by pullback along
`AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
def chartDetOfEquiv {L K : PerfectTwoTermAmplitude X} (V : X.affineOpens)
    (e : chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V) :
    chartDet L V ≅ chartDet K V :=
  (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecOfEquiv V e)

/-- A functor sends an isomorphism equal to the identity to the identity. -/
private theorem mapIso_eq_refl {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A : C}
    {i : A ≅ A} (h : i = Iso.refl A) : F.mapIso i = Iso.refl _ :=
  (congrArg F.mapIso h).trans (F.mapIso_refl A)

/-- A functor sends an isomorphism equal to a composite to the composite of the images. -/
private theorem mapIso_eq_trans {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B A' : C}
    {i : A ≅ A'} (j : A ≅ B) (k : B ≅ A') (h : i = j ≪≫ k) :
    F.mapIso i = F.mapIso j ≪≫ F.mapIso k :=
  (congrArg F.mapIso h).trans (F.mapIso_trans j k)

/-- The identity linear equivalence induces the identity. -/
theorem chartDetSpecOfEquiv_refl (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    chartDetSpecOfEquiv V (LinearEquiv.refl Γ(X, (V.1 : X.Opens)) (chartDetModule L V)) =
      Iso.refl _ :=
  mapIso_eq_refl _ (Iso.ext (ModuleCat.hom_ext rfl))

/-- A composite of linear equivalences induces the composite isomorphism. -/
theorem chartDetSpecOfEquiv_trans {L K M : PerfectTwoTermAmplitude X} (V : X.affineOpens)
    (e : chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V)
    (f : chartDetModule K V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule M V) :
    chartDetSpecOfEquiv V (e ≪≫ₗ f) =
      chartDetSpecOfEquiv V e ≪≫ chartDetSpecOfEquiv V f :=
  mapIso_eq_trans _ _ _ (Iso.ext (ModuleCat.hom_ext rfl))

/-- The identity linear equivalence induces the identity on the affine open. -/
theorem chartDetOfEquiv_refl (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    chartDetOfEquiv V (LinearEquiv.refl Γ(X, (V.1 : X.Opens)) (chartDetModule L V)) =
      Iso.refl _ :=
  mapIso_eq_refl _ (chartDetSpecOfEquiv_refl L V)

/-- A composite of linear equivalences induces the composite isomorphism on the affine open. -/
theorem chartDetOfEquiv_trans {L K M : PerfectTwoTermAmplitude X} (V : X.affineOpens)
    (e : chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V)
    (f : chartDetModule K V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule M V) :
    chartDetOfEquiv V (e ≪≫ₗ f) = chartDetOfEquiv V e ≪≫ chartDetOfEquiv V f :=
  mapIso_eq_trans _ _ _ (chartDetSpecOfEquiv_trans V e f)

/-! ### The canonical element on a chart -/

/-- The canonical global section of the determinant of `L` on the spectrum of an affine open is
the canonical element of More on Algebra, Section 0FJI of the chart complex, read through
`AlgebraicGeometry.tilde.toOpen`. This holds by unfolding
`AlgebraicGeometry.DeterminantTwoTerm.chartDelta`, `specDelta` and `affineDelta`; the two
rank-zero hypotheses in sight are propositions and so are interchangeable. -/
theorem chartDelta_eq {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) :
    chartDelta hL V =
      (tilde.toOpen (chartDetModule L V) ⊤).hom (delta (chartComplex L V) (hL V)) :=
  rfl

/-- **A linear equivalence carrying the canonical element to the canonical element induces an
isomorphism carrying the canonical global section to the canonical global section.** For affine
opens of a rank-zero `L` and `K`, if a linear equivalence of the determinant modules over
`Γ(X, V)` carries the canonical element of More on Algebra, Section 0FJI of the chart complex of
`L` to that of `K`, then the induced isomorphism of the determinants on `Spec Γ(X, V)` carries
`AlgebraicGeometry.DeterminantTwoTerm.chartDelta` to `chartDelta`.

Both canonical global sections are `AlgebraicGeometry.tilde.toOpen` of a module element, and a map
of modules acts on such a section through the map itself, by
`AlgebraicGeometry.DeterminantTwoTerm.app_tilde_toOpen`. -/
theorem chartDetSpecOfEquiv_chartDelta {L K : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (hK : IsRankZeroOn K) (V : X.affineOpens)
    (e : chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V)
    (he : e (delta (chartComplex L V) (hL V)) = delta (chartComplex K V) (hK V)) :
    Scheme.Modules.Hom.app (chartDetSpecOfEquiv V e).hom ⊤ (chartDelta hL V) =
      chartDelta hK V :=
  (app_tilde_toOpen Γ(X, (V.1 : X.Opens)) e.toModuleIso.hom
      (delta (chartComplex L V) (hL V))).trans
    (congrArg (tilde.toOpen (chartDetModule K V) ⊤).hom he)

end AlgebraicGeometry.DeterminantTwoTerm

end
