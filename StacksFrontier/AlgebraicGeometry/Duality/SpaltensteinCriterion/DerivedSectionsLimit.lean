module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimitHomologySequence
public import StacksFrontier.CategoryTheory.Functor.KanExtension.Precomposition
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over an open commute with countable derived limits

Let `(X, 𝒪_X)` be a ringed space, let `U ⊆ X` be open and let `(Kₙ)` be an inverse system in
the unbounded derived category `D(𝒪_X)` with derived limit `L = R\lim Kₙ`. Then derived sections
over `U` carry the defining triangle of `L` to a derived-limit triangle in `D(Ab)`, so that
`R\Gamma(U, R\lim Kₙ) = R\lim R\Gamma(U, Kₙ)`; and the long exact cohomology sequence of that
triangle collapses to the Milnor short exact sequence

`0 ⟶ R¹\lim H^{m-1}(U, Kₙ) ⟶ H^m(U, R\lim Kₙ) ⟶ \lim H^m(U, Kₙ) ⟶ 0`.

Both assertions are Stacks 0D60, and both are obtained by composing two results that are
already available. The first is Stacks 08U1,
`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`,
which says that a right derived functor of an additive functor out of a Grothendieck abelian
category preserves derived limits as soon as it preserves countable products; sections over an
open preserve all limits, being an evaluation of a sheaf, and `𝒪_X`-modules are Grothendieck
abelian. The second is the long exact homology sequence of the transported triangle, whose outer
terms are identified with the product of the cohomologies by Stacks 07KC and whose difference
map is thereby identified with the difference map of the inverse system of cohomology groups;
the kernel of that difference map is `\lim`, by
`CategoryTheory.Limits.inverseSystemLimitKernelForkIsLimit`, and its cokernel in the previous
degree is `R¹\lim`.

Everything is stated at *free* `HasDerivedCategory` instances, one for `D(𝒪_X)` and one for
`D(Ab)`, rather than at `HasDerivedCategory.standard`. Nothing below is therefore a statement
about one model of the derived category which is not equally a statement about the locally small
model `SheafOfModules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the model the derived
Spec–`Γ` comparison of Stacks 06Z0 is set at.

## Main results

* `Stacks.Cohomology.DerivedLimitSections.isDerivedLimit_map_derivedSections` — derived sections
  over an open carry a countable derived limit to a derived limit.
* `Stacks.Cohomology.DerivedLimitSections.exists_shortExact_limOne_cohomology_derivedLimit` —
  the Milnor short exact sequence for the cohomology of a derived limit over an open.

## Implementation notes

Derived sections are not constructed: they are taken as an arbitrary total right derived functor
`RΓ(U, -)` of the additive-group-valued sections functor over `U`, presented by its
complex-level comparison map and its universal property. Every statement is therefore
independent of a choice of K-injective resolutions, and a caller holding any model of
`RΓ(U, -)` can use it. The hypothesis is given in the `DerivedCategory.Q` form — a natural
transformation out of `(-)^{\text{sections}} ⋙ Q` which exhibits `RΓ(U, -)` as a right derived
functor along `HomologicalComplex.quasiIso` — because that is the form in which the statements of
Stacks 0D61 and Stacks 0D62 above this one take it, whereas Stacks 08U1 is stated in the
`DerivedCategory.Qh` form. `derivedSectionsUnit` converts between them: precomposition with the
quotient functor to the homotopy category is fully faithful on natural transformations, so the
left Kan extension property transports across it.

`R¹\lim` is spelled as the cokernel of the difference map `1 - shift` on the product of the
cohomology groups. There is no inverse-limit functor on `D(Ab)` in play, and this cokernel
description is how `R¹\lim` is characterised in
`StacksFrontier/Homology/DerivedCategory/InverseSystem/Rlim.lean`
(`Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor`); it is also the spelling the
dependent statements of Stacks 0D61 use.

A derived limit is presented by its defining distinguished triangle with the structural map `p`
given, rather than through the predicate
`CategoryTheory.Pretriangulated.IsDerivedLimit`, in the second statement: the map to `\lim` is
characterised by its composites with the limit projections, which are the maps induced by the
given structural maps `L ⟶ Kₙ`, and that characterisation is lost if `p` is existentially
quantified. The first statement does use the predicate, since nothing there needs `p`.

## References

* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 08U5](https://stacks.math.columbia.edu/tag/08U5)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Pretriangulated Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.DerivedLimitSections

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- Sections over `U`, as an additive functor from `𝒪_X`-modules to abelian groups. -/
abbrev sections : SheafOfModules.{u} (structureSheafRing X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (structureSheafRing X) ⋙
    (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U)

/-- Sections over `U` form an additive functor. -/
instance sections_additive : (sections X U).Additive := ⟨fun {_ _ _ _} => rfl⟩

/-- Sections over `U` preserve countable products. -/
instance sections_preservesLimitsOfShape_discrete_nat :
    PreservesLimitsOfShape (Discrete ℕ) (sections X U) := by
  let e : (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}) ≅
      sections X U :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact preservesLimitsOfShape_of_natIso (J := Discrete ℕ) e

section

variable [HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{u} AddCommGrpCat.{u}]

/-- The homotopy-category presentation of the universal property of `RΓ(U, -)`: a functor which
is a right derived functor of sections over `U` in the `DerivedCategory.Q` presentation is one in
the `DerivedCategory.Qh` presentation, with the structure map obtained from the given comparison
by the full-and-faithfulness of precomposition with the quotient functor. -/
private lemma exists_derivedSectionsUnit
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison : (sections X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))) :
    ∃ α : (sections X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma,
      RGamma.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)) := by
  set A := SheafOfModules.{u} (structureSheafRing X)
  set F := sections X U
  set q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  set Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := AddCommGrpCat.{u})
  set eL := DerivedCategory.quotientCompQhIso A
  let eF : q ⋙ Fh ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := AddCommGrpCat.{u}) :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (C := AddCommGrpCat.{u}))
  let γ : q ⋙ Fh ⟶ (q ⋙ DerivedCategory.Qh (C := A)) ⋙ RGamma :=
    eF.hom ≫ comparison ≫ whiskerRight eL.inv RGamma
  refine ⟨((whiskeringLeft _ _ _).obj q).preimage (γ ≫ (Functor.associator _ _ _).hom), ?_⟩
  have hαpre : whiskerLeft q
      (((whiskeringLeft _ _ _).obj q).preimage (γ ≫ (Functor.associator _ _ _).hom)) ≫
      (Functor.associator _ _ _).inv = γ := by
    rw [← whiskeringLeft_obj_map, map_preimage]
    simp
  have hγ : RGamma.IsLeftKanExtension γ := by
    let Lq := q ⋙ DerivedCategory.Qh (C := A)
    let e : Lq ⋙ 𝟭 _ ≅ DerivedCategory.Q (C := A) :=
      (Functor.rightUnitor Lq).symm ≪≫ eL
    have hβ' : RGamma.IsLeftKanExtension
        (comparison ≫ whiskerRight e.inv RGamma ≫ (Functor.associator _ _ _).hom) :=
      (Functor.isLeftKanExtension_iff_postcomp₁
        (G := 𝟭 _) (e := e) (F' := RGamma) comparison).mp
          (Functor.IsRightDerivedFunctor.isLeftKanExtension RGamma comparison
            (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    exact (Functor.isLeftKanExtension_iff_of_iso₂ γ
      (comparison ≫ whiskerRight e.inv RGamma ≫ (Functor.associator _ _ _).hom)
      eF (Iso.refl _) (by ext Y; simp [γ, e, Lq, Category.assoc])).2 hβ'
  refine ⟨(isLeftKanExtension_iff_precomp_of_fullyFaithful q RGamma _).2 ?_⟩
  rw [hαpre]
  simpa [γ, eL] using hγ

/-- The transported derived-limit triangle, with its structural map pinned to the image of the
given one followed by the product comparison. -/
private theorem derivedSections_mappedTriangle
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison : (sections X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) ⟶ (RGamma.obj L)⟦(1 : ℤ)⟧,
        Triangle.mk (RGamma.map p ≫ piComparison RGamma (fun n : ℕ ↦ K.obj ⟨n⟩))
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) n -
              Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) (n + 1) ≫
                RGamma.map (K.map (homOfLE (Nat.le_succ n)).op)) δ ∈
          distTriang (DerivedCategory AddCommGrpCat.{u}) := by
  obtain ⟨α, _⟩ := exists_derivedSectionsUnit X U RGamma comparison hRGamma
  exact Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor (sections X U) RGamma α K L p hL

/-- Derived sections over an open of a ringed space carry a countable derived inverse limit to a
derived inverse limit: `RΓ(U, R\lim Kₙ) = R\lim RΓ(U, Kₙ)`. -/
@[stacks 0D60 "commutation with derived limits"]
theorem isDerivedLimit_map_derivedSections
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison : (sections X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      @IsDerivedLimit (DerivedCategory AddCommGrpCat.{u}) _ _ _ _ _ _
        (K ⋙ RGamma) h (RGamma.obj L) := by
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨h, δ', hT'⟩ :=
    derivedSections_mappedTriangle X U RGamma comparison hRGamma K L p ⟨δ, hT⟩
  exact ⟨h, RGamma.map p ≫ piComparison RGamma (fun n : ℕ ↦ K.obj ⟨n⟩), δ', hT'⟩

/-- The Milnor short exact sequence of a derived-limit triangle in `D(Ab)`, with the structural
map of the triangle given. The cokernel of the difference map in degree `m - 1` injects into
`H^m` of the limit with cokernel the inverse limit of the `H^m` of the terms, and the map to that
inverse limit is characterised by its composites with the limit projections. -/
private theorem milnor_shortExact_of_distinguishedTriangle
    (F : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u}) (K : DerivedCategory AddCommGrpCat.{u})
    [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (a : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) (b : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) b ∈
      distTriang (DerivedCategory AddCommGrpCat.{u}))
    (m : ℤ) :
    let Hprev := DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)
    let Hcur := DerivedCategory.homologyFunctor AddCommGrpCat.{u} m
    let Fprev := F ⋙ Hprev
    let Fcur := F ⋙ Hcur
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) :=
      Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
            Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel dprev ⟶ Hcur.obj K) (q : Hcur.obj K ⟶ limit Fcur) (zero : i ≫ q = 0),
      ((ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map a ≫ Hcur.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n)) := by
  obtain ⟨-, i, q, w, -, -, hq, hS⟩ :=
    DerivedCategory.homology_shortExact_of_distinguished F K a b hT m
  exact ⟨i, q, w, hS, hq⟩

/-- For every open `U` of a ringed space and every degree `m`, the cohomology of a countable
derived inverse limit lies in the Milnor short exact sequence

`0 ⟶ R¹\lim H^{m-1}(U, Kₙ) ⟶ H^m(U, R\lim Kₙ) ⟶ \lim H^m(U, Kₙ) ⟶ 0`.

Here `R¹\lim` is the cokernel of the difference map `1 - shift` on the product of the groups
`H^{m-1}(U, Kₙ)`. The map to the inverse limit is characterised by its composites with the limit
projections, which are the maps on cohomology induced by the given structural maps `L ⟶ Kₙ`. -/
@[stacks 0D60 "short exact sequence"]
theorem exists_shortExact_limOne_cohomology_derivedLimit
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison : (sections X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (m : ℤ) :
    let Hprev := DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)
    let Hcur := DerivedCategory.homologyFunctor AddCommGrpCat.{u} m
    let Fprev := K ⋙ RGamma ⋙ Hprev
    let Fcur := K ⋙ RGamma ⋙ Hcur
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) :=
      Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
            Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel dprev ⟶ Hcur.obj (RGamma.obj L))
      (q : Hcur.obj (RGamma.obj L) ⟶ limit Fcur) (zero : i ≫ q = 0),
      ((ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) := by
  intro Hprev Hcur Fprev Fcur dprev
  obtain ⟨hProduct, δ', hMappedTriangle⟩ :=
    derivedSections_mappedTriangle X U RGamma comparison hRGamma K L p hL
  have hProduct' : HasProduct fun n : ℕ ↦ (K ⋙ RGamma).obj ⟨n⟩ := hProduct
  let mappedArrow := RGamma.map p ≫ piComparison RGamma (fun n : ℕ ↦ K.obj ⟨n⟩)
  obtain ⟨i, q, zero, hShort, hProjection⟩ :=
    milnor_shortExact_of_distinguishedTriangle (K ⋙ RGamma) (RGamma.obj L)
      mappedArrow δ' hMappedTriangle m
  let eSystem := Functor.associator K RGamma Hcur
  let eLimit : limit ((K ⋙ RGamma) ⋙ Hcur) ≅ limit Fcur := HasLimit.isoOfNatIso eSystem
  let ePrevSystem := Functor.associator K RGamma Hprev
  let ePrevProduct := Pi.mapIso fun n : ℕ ↦ ePrevSystem.app ⟨n⟩
  let dprevLeft : (∏ᶜ fun n : ℕ ↦ ((K ⋙ RGamma) ⋙ Hprev).obj ⟨n⟩) ⟶
      ∏ᶜ fun n : ℕ ↦ ((K ⋙ RGamma) ⋙ Hprev).obj ⟨n⟩ := Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ ((K ⋙ RGamma) ⋙ Hprev).obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ ((K ⋙ RGamma) ⋙ Hprev).obj ⟨n⟩) (n + 1) ≫
        ((K ⋙ RGamma) ⋙ Hprev).map (homOfLE (Nat.le_succ n)).op
  have hePrevProduct : ePrevProduct.hom = 𝟙 _ := by
    ext n
    simp [ePrevProduct, ePrevSystem, Functor.associator, Functor.assoc]
  have hdprevEq : dprevLeft = dprev := by
    apply Pi.hom_ext
    intro n
    simp [dprevLeft, dprev, Fprev, Functor.assoc]
  have hdprev : dprevLeft ≫ ePrevProduct.hom = ePrevProduct.hom ≫ dprev := by
    rw [hePrevProduct, Category.id_comp, Category.comp_id, hdprevEq]
  let eCoker := cokernel.mapIso (f := dprevLeft) dprev ePrevProduct ePrevProduct hdprev
  refine ⟨eCoker.inv ≫ i, q ≫ eLimit.hom, ?_, ?_, ?_⟩
  · calc
      (eCoker.inv ≫ i) ≫ q ≫ eLimit.hom = eCoker.inv ≫ (i ≫ q) ≫ eLimit.hom := by cat_disch
      _ = 0 := by rw [zero]; simp
  · refine ShortComplex.shortExact_of_iso ?_ hShort
    exact ShortComplex.isoMk eCoker (Iso.refl _) eLimit (by simp) (by simp)
  · intro n
    calc
      (q ≫ eLimit.hom) ≫ limit.π Fcur ⟨n⟩ = q ≫ limit.π ((K ⋙ RGamma) ⋙ Hcur) ⟨n⟩ := by
        simp [eLimit, eSystem]
      _ = Hcur.map mappedArrow ≫
            Hcur.map (Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) n) := hProjection n
      _ = Hcur.map (mappedArrow ≫ Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) n) := by
        rw [← Hcur.map_comp]
      _ = Hcur.map (RGamma.map p ≫ RGamma.map (Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) := by
        congr 1
        simp [mappedArrow, Category.assoc, piComparison_comp_π]
      _ = Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) := by
        rw [← RGamma.map_comp]

end

end Stacks.Cohomology.DerivedLimitSections

end
