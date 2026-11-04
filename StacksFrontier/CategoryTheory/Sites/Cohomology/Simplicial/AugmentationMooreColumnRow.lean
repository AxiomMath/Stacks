module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.MooreSheafLocalIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteBaseChangeStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.StdCoverResolution

/-!
# The column step and the row step of Stacks 08RX, fed to each other

Let `(C, J)` be a small site, let `Δ × C` be the simplicial site of [Stacks, Tag 09D0] and let
`θ : A₁ ⟶ A₂` be a homomorphism of presheaves of commutative rings on `Δ × C`. Write `s(-)` for
`Stacks.SimplicialModules.mooreSheafCochain`, the complex of abelian sheaves on `C` attached to a
simplicial module. Two facts about the Moore double complex enter:

* the **column step**,
  `Stacks.SimplicialModules.quasiIso_total_mooreSheafBicomplexBaseChangeMap_of_isStdCover`: on a
  complex `L^•` bounded above by `0` all of whose terms are standard covers the base-change unit
  `Tot s(L^•) ⟶ Tot s(L^• ⊗_{A₁} A₂)` is a quasi-isomorphism, granted the hypothesis `hθ` of
  [Stacks, Tag 09D2] that `s(A₁) ⟶ s(A₂)` be a quasi-isomorphism;
* the **row step**, `Stacks.SimplicialModules.quasiIso_total_map_mooreSheafBicomplex`: a
  quasi-isomorphism of complexes bounded above by `0` stays one on `Tot s(-)`.

This file feeds them to each other, as the triangle

`Tot s(L^•) ⟶ Tot s(L^• ⊗_{A₁} A₂) ⟶ Tot Z ⟶ Tot W`,

whose composite is the row step and whose first leg is the column step: granted an *invertible*
comparison `s(L^• ⊗_{A₁} A₂) ⟶ Z`, the remaining leg `Tot Z ⟶ Tot W` is a quasi-isomorphism. That
is `Stacks.SimplicialModules.quasiIso_total_map_of_column_row`.

## Main definitions

* `Stacks.SimplicialModules.changeOfRingsComplex`: `- ⊗_{A₁} A₂` on cochain complexes.
* `Stacks.SimplicialModules.changeOfRingsComplexUnit`: the base-change unit on cochain complexes.

## Main results

* `Stacks.SimplicialModules.quasiIso_total_map_of_column_row`: the two steps fed to each other.
* `Stacks.SimplicialModules.mooreSheafCochain_map_changeOfRingsComplexUnit`: `s(-)` of the
  base-change unit on cochain complexes is the base-change unit of the Moore double complexes.
* `Stacks.SimplicialModules.mooreSheafCochain_map_restrictScalars_map` and
  `Stacks.SimplicialModules.mooreSheafCochain_map_restrictScalars_map_obj`: `s(-)` of a
  restriction of scalars is `s(-)` over the target ring.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SimplicialModules

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  {A₁ A₂ : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)

/-- Restriction of scalars for presheaves of modules is additive: it changes neither the
underlying presheaf of abelian groups nor the addition of morphisms. -/
instance additive_restrictScalars : (restrictScalars θ :
    PresheafOfModules.{u} (ringPresheaf A₂) ⥤
      PresheafOfModules.{u} (ringPresheaf A₁)).Additive where
  map_add := by intros; rfl

/-- `- ⊗_{A₁} A₂` on cochain complexes of presheaves of modules on `Δ × C`, degreewise change of
rings. -/
abbrev changeOfRingsComplex :
    CochainComplex (PresheafOfModules.{u} (ringPresheaf A₁)) ℤ ⥤
      CochainComplex (PresheafOfModules.{u} (ringPresheaf A₂)) ℤ :=
  (changeOfRings θ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The base-change unit on cochain complexes, the unit of
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction` in each degree. -/
def changeOfRingsComplexUnit (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₁)) ℤ) :
    L ⟶ ((restrictScalars θ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((changeOfRingsComplex θ).obj L) :=
  (NatTrans.mapHomologicalComplex (changeOfRingsAdjunction θ).unit (ComplexShape.up ℤ)).app L

omit [HasWeakSheafify J AddCommGrpCat] in
/-- The base-change unit on cochain complexes is, after `s(-)`, the base-change unit of the Moore
double complexes. -/
lemma mooreSheafCochain_map_changeOfRingsComplexUnit
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₁)) ℤ) :
    ((mooreSheafCochain J A₁).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (changeOfRingsComplexUnit θ L) =
      mooreSheafBicomplexBaseChangeMap J θ L :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat] in
/-- The complex `s(-)` of a restriction of scalars is the complex `s(-)` over the target ring:
restriction of scalars changes neither the underlying abelian presheaf nor the map on it, so the
two Moore double complexes, and the two maps between them, are the same. -/
lemma mooreSheafCochain_map_restrictScalars_map
    {X Y : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₂)) ℤ} (f : X ⟶ Y) :
    ((mooreSheafCochain J A₁).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((restrictScalars θ).mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      ((mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ)).map f :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat] in
/-- `s(-)` of a restriction of scalars of a map of presheaves of modules is `s(-)` of that map over
the target ring. -/
lemma mooreSheafCochain_map_restrictScalars_map_obj
    {X Y : PresheafOfModules.{u} (ringPresheaf A₂)} (f : X ⟶ Y) :
    (mooreSheafCochain J A₁).map ((restrictScalars θ).map f) =
      (mooreSheafCochain J A₂).map f :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat] in
/-- The column step and the row step fed to each other.

Let `L^•` be a complex of presheaves of `A₁`-modules on `Δ × C`, bounded above by `0`, all of
whose terms are standard covers. Let `Z` and `W` be double complexes of abelian sheaves on `C`
with total complexes, let `c₁ : s(L^• ⊗_{A₁} A₂) ⟶ Z` be invertible, and let `c₂ : Z ⟶ W`. If the
base-change unit followed by `c₁ ≫ c₂` is a map `r : s(L^•) ⟶ W` whose total complex is a
quasi-isomorphism, then

`Tot c₂`

is a quasi-isomorphism. -/
theorem quasiIso_total_map_of_column_row
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₁)) ℤ) [L.IsStrictlyLE 0]
    (hP : ∀ p, PresheafOfModules.IsStdCover (L.X p))
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' θ)))
    {Z W : HomologicalComplex₂ (Sheaf J AddCommGrpCat.{u})
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [Z.HasTotal (ComplexShape.up ℤ)] [W.HasTotal (ComplexShape.up ℤ)]
    (c₁ : baseChangedMooreSheafBicomplex J θ L ⟶ Z) [IsIso c₁]
    (c₂ : Z ⟶ W)
    (r : mooreSheafBicomplex J L ⟶ W)
    (hr : QuasiIso (HomologicalComplex₂.total.map r (ComplexShape.up ℤ)))
    (hcomm : mooreSheafBicomplexBaseChangeMap J θ L ≫ c₁ ≫ c₂ = r) :
    QuasiIso (HomologicalComplex₂.total.map c₂ (ComplexShape.up ℤ)) := by
  have hcol := quasiIso_total_mooreSheafBicomplexBaseChangeMap_of_isStdCover J θ hθ L hP
  have hc₁ : IsIso (HomologicalComplex₂.total.map c₁ (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  have hcomp : QuasiIso (HomologicalComplex₂.total.map
        (mooreSheafBicomplexBaseChangeMap J θ L) (ComplexShape.up ℤ) ≫
      (HomologicalComplex₂.total.map c₁ (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map c₂ (ComplexShape.up ℤ))) := by
    rwa [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp, hcomm]
  have h₂ : QuasiIso (HomologicalComplex₂.total.map c₁ (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map c₂ (ComplexShape.up ℤ)) :=
    quasiIso_of_comp_left (HomologicalComplex₂.total.map
      (mooreSheafBicomplexBaseChangeMap J θ L) (ComplexShape.up ℤ)) _
  exact quasiIso_of_comp_left (HomologicalComplex₂.total.map c₁ (ComplexShape.up ℤ)) _

end Stacks.SimplicialModules

end
