module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra

/-!
# The single-morphism comparison of descent data with coalgebras

Mathlib describes descent data for a pseudofunctor `F` in two ways.
`CategoryTheory.Pseudofunctor.DescentData` indexes the transition morphisms by an arbitrary
object mapping to two members of the covering family, so it needs no fibre products, while
`CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra` — available when `F` takes values in
the bicategory `CategoryTheory.Bicategory.Adj Cat` of adjunctions — describes them as
Eilenberg–Moore coalgebras, `obj i₁ ⟶ (f i₁)^* (f i₂)_* (obj i₂)`.

This file compares the two **on morphisms, for a one-element family**. Fix a morphism
`f : X ⟶ S` and a chosen pullback `sq` of `f` with itself, with projections `p₁, p₂`. For a
morphism `ψ : f^* M ⟶ f^* N`, the descent compatibility of
`CategoryTheory.Pseudofunctor.DescentData.Hom` — a priori a condition over *every* object
mapping to `X` twice over `S` — reduces to a single equation over `sq`
(`Pseudofunctor.descentComparison_comm_of_comm`), and that equation is the Eilenberg–Moore
coalgebra condition for the comonad `f^* f_*` composed with the base-change morphism
`f^* f_* ⟶ (p₁)_* p₂^*` (`Pseudofunctor.descentSquareApp_comm_iff`).  The coalgebra
condition therefore always implies the descent compatibility, and the converse holds as soon
as the base-change morphism is a monomorphism at `f^* N`.

## Main definitions

* `CategoryTheory.Pseudofunctor.descentSquare`: the canonical comparison `p₁^* f^* ≅ p₂^* f^*`.
* `CategoryTheory.Pseudofunctor.descentComparison`: its value at a general pair of morphisms
  `f₁, f₂ : Y ⟶ X` over `S`, which is the transition morphism of the canonical descent datum.
* `CategoryTheory.Pseudofunctor.descentBaseChange`: the base-change morphism
  `f^* f_* ⟶ (p₁)_* p₂^*`, defined as the mate of `descentSquare`.

## Main results

* `CategoryTheory.Pseudofunctor.descentComparison_comm_of_comm` reduces the descent
  compatibility to one equation over a chosen pullback.
* `CategoryTheory.Pseudofunctor.descentSquareApp_comm_iff` is the transposition of that
  equation across the adjunction along `p₁`.
* `CategoryTheory.Pseudofunctor.descentSquareApp_comm_of_coalgebra` and
  `CategoryTheory.Pseudofunctor.coalgebra_of_descentSquareApp_comm` are the two directions of
  the comparison, the second over the monomorphism hypothesis on the base change.
* `CategoryTheory.Pseudofunctor.bijective_toDescentData_map_of_bijective_comparison_map`
  transfers bijectivity on a hom-set from the Eilenberg–Moore comparison functor to
  `CategoryTheory.Pseudofunctor.toDescentData`.
* `CategoryTheory.Pseudofunctor.bijective_toDescentDataAsCoalgebra_map_iff` and
  `bijective_toDescentData_map_of_bijective_toDescentDataAsCoalgebra_map` are the same
  statements phrased with `DescentDataAsCoalgebra`, for a pseudofunctor to `Adj Cat`.

## Implementation notes

The comparison is named twice: as a natural transformation `descentSquare`, which is what the
mate construction `CategoryTheory.mateEquiv` consumes, and pointwise as `descentSquareApp`,
whose type is written at the iterated pullback `p₁^* (f^* M)` rather than at the composite
functor `(f^* ⋙ p₁^*) M`.  Only the second spelling is type-correct at `implicit`
transparency inside the goals that `DescentData.Hom.comm` produces, so only the second is
visible to `rw` and `simp` there; `descentSquare_app` identifies them.  The same applies to
`descentComparison`, which is the `hom` field of
`CategoryTheory.Pseudofunctor.DescentData.ofObj` for a constant family, by `rfl`.
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Opposite Bicategory Limits Pseudofunctor.LocallyDiscreteOpToCat


namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f)

section

/-- `p₁^* ∘ f^* ≅ p^*`, for a chosen pullback of `f` with itself. -/
noncomputable def descentPullbackIso₁ :
    F.map sq.p.op.toLoc ≅ F.map f.op.toLoc ≫ F.map sq.p₁.op.toLoc :=
  F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])

/-- `p₂^* ∘ f^* ≅ p^*`, for a chosen pullback of `f` with itself. -/
noncomputable def descentPullbackIso₂ :
    F.map sq.p.op.toLoc ≅ F.map f.op.toLoc ≫ F.map sq.p₂.op.toLoc :=
  F.mapComp' f.op.toLoc sq.p₂.op.toLoc sq.p.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₂])

/-- The canonical comparison `p₁^* f^* ≅ p₂^* f^*` over a chosen pullback of `f` with
itself. -/
noncomputable def descentSquare :
    (F.map f.op.toLoc).toFunctor ⋙ (F.map sq.p₁.op.toLoc).toFunctor ⟶
      (F.map f.op.toLoc).toFunctor ⋙ (F.map sq.p₂.op.toLoc).toFunctor :=
  (Cat.Hom.toNatIso (descentPullbackIso₁ sq)).inv ≫
    (Cat.Hom.toNatIso (descentPullbackIso₂ sq)).hom

/-- The component of `Pseudofunctor.descentSquare` at an object, written at the iterated
pullback `p₁^* (f^* M)` rather than at the composite functor `(f^* ⋙ p₁^*) M`. -/
noncomputable def descentSquareApp (M : F.obj (.mk (op S))) :
    (F.map sq.p₁.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj M) ⟶
      (F.map sq.p₂.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj M) :=
  (descentPullbackIso₁ sq).inv.toNatTrans.app M ≫ (descentPullbackIso₂ sq).hom.toNatTrans.app M

/-- The component of `Pseudofunctor.descentSquare` at `M` is `Pseudofunctor.descentSquareApp`. -/
@[simp]
lemma descentSquare_app (M : F.obj (.mk (op S))) :
    (descentSquare sq).app M = descentSquareApp sq M := rfl

/-- Naturality of `Pseudofunctor.descentSquareApp` in the object `M`. -/
@[reassoc]
lemma descentSquareApp_naturality {M N : F.obj (.mk (op S))} (α : M ⟶ N) :
    (F.map sq.p₁.op.toLoc).toFunctor.map ((F.map f.op.toLoc).toFunctor.map α) ≫
        descentSquareApp sq N =
      descentSquareApp sq M ≫
        (F.map sq.p₂.op.toLoc).toFunctor.map ((F.map f.op.toLoc).toFunctor.map α) :=
  (descentSquare sq).naturality α

end


section BaseChange

variable {Rf : F.obj (.mk (op X)) ⥤ F.obj (.mk (op S))}
  (adj : (F.map f.op.toLoc).toFunctor ⊣ Rf)
  {Rp : F.obj (.mk (op sq.pullback)) ⥤ F.obj (.mk (op X))}
  (adjp : (F.map sq.p₁.op.toLoc).toFunctor ⊣ Rp)

/-- The base-change morphism `f^* f_* ⟶ (p₁)_* p₂^*` attached to a chosen pullback of `f`
with itself: the mate of `Pseudofunctor.descentSquare`. -/
noncomputable def descentBaseChange :
    Rf ⋙ (F.map f.op.toLoc).toFunctor ⟶
      (F.map sq.p₂.op.toLoc).toFunctor ⋙ Rp :=
  mateEquiv adj adjp (descentSquare sq)

/-- The unit of `f^* ⊣ f_*` followed by the base-change morphism is the unit of the adjunction
along `p₁` followed by `(p₁)_*` applied to `Pseudofunctor.descentSquareApp`. -/
lemma unit_descentBaseChange (M : F.obj (.mk (op S))) :
    (F.map f.op.toLoc).toFunctor.map (adj.unit.app M) ≫
        (descentBaseChange sq adj adjp).app _ =
      adjp.unit.app _ ≫ Rp.map (descentSquareApp sq M) :=
  unit_mateEquiv adj adjp (descentSquare sq) M

end BaseChange

section DescentData

variable {ι : Type t}

/-- The canonical comparison `f₁^* f^* M ⟶ f₂^* f^* M` attached to two morphisms
`f₁, f₂ : Y ⟶ X` with `f₁ ≫ f = q = f₂ ≫ f`.  This is the transition morphism of the
canonical descent datum of `M` relative to a constant family `f`, written at the iterated
pullback rather than at a composite functor. -/
noncomputable def descentComparison (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S)
    (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) :
    (F.map f₁.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj M) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj M) :=
  (F.mapComp' f.op.toLoc f₁.op.toLoc q.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app M ≫
    (F.mapComp' f.op.toLoc f₂.op.toLoc q.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app M

/-- `Pseudofunctor.descentSquareApp` is `Pseudofunctor.descentComparison` at the two projections
of the chosen pullback. -/
lemma descentSquareApp_eq_descentComparison (M : F.obj (.mk (op S))) :
    descentSquareApp sq M = descentComparison M sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ := rfl

/-- The transition morphisms of the canonical descent datum
`CategoryTheory.Pseudofunctor.DescentData.ofObj` of `M` relative to a constant family are the
morphisms `Pseudofunctor.descentComparison`. -/
lemma ofObj_hom_eq_descentComparison (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S)
    (i₁ i₂ : ι) (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) :
    (DescentData.ofObj (f := fun _ : ι ↦ f) M).hom (i₁ := i₁) (i₂ := i₂) q f₁ f₂ hf₁ hf₂ =
      descentComparison M q f₁ f₂ hf₁ hf₂ := rfl

/-- `Pseudofunctor.descentComparison` is compatible with further pullback. -/
lemma pullHom_descentComparison (M : F.obj (.mk (op S))) ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q)
    (gf₁ gf₂ : Y' ⟶ X) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (descentComparison M q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂ =
      descentComparison M q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) := by
  simp only [descentComparison, pullHom, Functor.map_comp, Category.assoc,
    F.mapComp'₀₁₃_inv_app f.op.toLoc f₁.op.toLoc g.op.toLoc q.op.toLoc
      gf₁.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind),
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app f.op.toLoc f₂.op.toLoc g.op.toLoc
      q.op.toLoc gf₂.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind)]

/-- Compatibility of `ψ : f^* M ⟶ f^* N` with the canonical comparisons over **one** chosen
pullback of `f` with itself already implies it over every object mapping to `X` twice over
`S`. -/
lemma descentComparison_comm_of_comm {M N : F.obj (.mk (op S))}
    (ψ : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (hψ : (F.map sq.p₁.op.toLoc).toFunctor.map ψ ≫ descentSquareApp sq N =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map ψ)
    ⦃Y : C⦄ (q : Y ⟶ S) (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) :
    (F.map f₁.op.toLoc).toFunctor.map ψ ≫ descentComparison N q f₁ f₂ hf₁ hf₂ =
      descentComparison M q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map ψ := by
  obtain ⟨g, h₁, h₂⟩ := sq.isPullback.exists_lift f₁ f₂ (by rw [hf₁, hf₂])
  have hq : g ≫ sq.p = q := by rw [← sq.hp₁, reassoc_of% h₁, hf₁]
  simp only [descentSquareApp_eq_descentComparison] at hψ
  rw [← pullHom_descentComparison N g sq.p q hq sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ f₁ f₂ h₁ h₂,
    ← pullHom_descentComparison M g sq.p q hq sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ f₁ f₂ h₁ h₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, hψ, Functor.map_comp_assoc, mapComp'_inv_naturality]
  simp only [Category.assoc]

end DescentData

section Coalgebra

variable {Rf : F.obj (.mk (op X)) ⥤ F.obj (.mk (op S))}
  (adj : (F.map f.op.toLoc).toFunctor ⊣ Rf)
  {Rp : F.obj (.mk (op sq.pullback)) ⥤ F.obj (.mk (op X))}
  (adjp : (F.map sq.p₁.op.toLoc).toFunctor ⊣ Rp)

/-- Transposing the compatibility over a chosen pullback: a morphism `ψ : f^* M ⟶ f^* N`
satisfies the descent compatibility over `sq` if and only if, after composing with the
base-change morphism, it satisfies the Eilenberg–Moore coalgebra condition for the comonad
`f^* f_*`. -/
lemma descentSquareApp_comm_iff {M N : F.obj (.mk (op S))}
    (ψ : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N) :
    ((F.map sq.p₁.op.toLoc).toFunctor.map ψ ≫ descentSquareApp sq N =
        descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map ψ) ↔
      ((F.map f.op.toLoc).toFunctor.map (adj.unit.app M) ≫
          (F.map f.op.toLoc).toFunctor.map (Rf.map ψ)) ≫
          (descentBaseChange sq adj adjp).app ((F.map f.op.toLoc).toFunctor.obj N) =
        (ψ ≫ (F.map f.op.toLoc).toFunctor.map (adj.unit.app N)) ≫
          (descentBaseChange sq adj adjp).app ((F.map f.op.toLoc).toFunctor.obj N) := by
  have hnat := (descentBaseChange sq adj adjp).naturality ψ
  dsimp at hnat
  rw [← (adjp.homEquiv _ _).apply_eq_iff_eq, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, ← unit_descentBaseChange sq adj adjp N,
    ← unit_descentBaseChange sq adj adjp M, Category.assoc, ← hnat]
  simp only [Category.assoc]
  exact eq_comm

include adjp in
/-- A morphism satisfying the Eilenberg–Moore coalgebra condition for the comonad `f^* f_*`
satisfies the descent compatibility over a chosen pullback. -/
lemma descentSquareApp_comm_of_coalgebra {M N : F.obj (.mk (op S))}
    (ψ : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (hψ : (F.map f.op.toLoc).toFunctor.map (adj.unit.app M) ≫
        (F.map f.op.toLoc).toFunctor.map (Rf.map ψ) =
      ψ ≫ (F.map f.op.toLoc).toFunctor.map (adj.unit.app N)) :
    (F.map sq.p₁.op.toLoc).toFunctor.map ψ ≫ descentSquareApp sq N =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map ψ :=
  (descentSquareApp_comm_iff sq adj adjp ψ).2 (by rw [hψ])

/-- Conversely: if the base-change morphism `f^* f_* ⟶ (p₁)_* p₂^*` is a monomorphism at
`f^* N`, the descent compatibility over a chosen pullback implies the Eilenberg–Moore
coalgebra condition. -/
lemma coalgebra_of_descentSquareApp_comm {M N : F.obj (.mk (op S))}
    (ψ : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (hmono : Mono ((descentBaseChange sq adj adjp).app
      ((F.map f.op.toLoc).toFunctor.obj N)))
    (hψ : (F.map sq.p₁.op.toLoc).toFunctor.map ψ ≫ descentSquareApp sq N =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map ψ) :
    (F.map f.op.toLoc).toFunctor.map (adj.unit.app M) ≫
        (F.map f.op.toLoc).toFunctor.map (Rf.map ψ) =
      ψ ≫ (F.map f.op.toLoc).toFunctor.map (adj.unit.app N) :=
  (cancel_mono _).mp ((descentSquareApp_comm_iff sq adj adjp ψ).1 hψ)

include adjp in
/-- **Full faithfulness of `toDescentData` for a single morphism, from comonadicity.**
Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, let `f : X ⟶ S` admit a chosen pullback with itself,
and let the pullback functors along `f` and along the first projection admit right adjoints.
If the base-change morphism `f^* f_* ⟶ (p₁)_* p₂^*` is a monomorphism at `f^* N`, then the
descent-data comparison functor acts on morphisms `M ⟶ N` exactly as the Eilenberg–Moore
comparison functor of the adjunction `f^* ⊣ f_*` does. -/
theorem bijective_toDescentData_map_of_bijective_comparison_map
    {ι : Type t} [Unique ι] {M N : F.obj (.mk (op S))}
    (hmono : Mono ((descentBaseChange sq adj adjp).app
      ((F.map f.op.toLoc).toFunctor.obj N)))
    (h : Function.Bijective ((Comonad.comparison adj).map : (M ⟶ N) → _)) :
    Function.Bijective ((F.toDescentData (fun _ : ι ↦ f)).map : (M ⟶ N) → _) := by
  constructor
  · intro α α' hα
    refine h.1 (Comonad.Coalgebra.Hom.ext ?_)
    rw [Comonad.comparison_map_f, Comonad.comparison_map_f]
    exact congrArg (fun φ ↦ DescentData.Hom.hom φ default) hα
  · intro φ
    have hψ : (F.map sq.p₁.op.toLoc).toFunctor.map (DescentData.Hom.hom φ default) ≫
          descentSquareApp sq N =
        descentSquareApp sq M ≫
          (F.map sq.p₂.op.toLoc).toFunctor.map (DescentData.Hom.hom φ default) := by
      rw [descentSquareApp_eq_descentComparison, descentSquareApp_eq_descentComparison,
        ← ofObj_hom_eq_descentComparison (ι := ι) N sq.p default default,
        ← ofObj_hom_eq_descentComparison (ι := ι) M sq.p default default]
      exact φ.comm (q := sq.p) (i₁ := default) (i₂ := default) sq.p₁ sq.p₂ sq.hp₁ sq.hp₂
    obtain ⟨α, hα⟩ := h.2
      { f := DescentData.Hom.hom φ default
        h := coalgebra_of_descentSquareApp_comm sq adj adjp _ hmono hψ }
    refine ⟨α, DescentData.hom_ext fun i ↦ ?_⟩
    obtain rfl := Subsingleton.elim i default
    rw [toDescentData_map_hom]
    exact congrArg Comonad.Coalgebra.Hom.f hα

end Coalgebra

section AdjCat

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}} {X S : C} {f : X ⟶ S}

/-- For a one-element family, bijectivity on morphisms of
`CategoryTheory.Pseudofunctor.toDescentDataAsCoalgebra` is bijectivity on morphisms of the
Eilenberg–Moore comparison functor of the adjunction `f^* ⊣ f_*`. -/
lemma bijective_toDescentDataAsCoalgebra_map_iff (ι : Type t) [Unique ι]
    (M N : (F.obj (.mk (op S))).obj) :
    Function.Bijective ((F.toDescentDataAsCoalgebra (fun _ : ι ↦ f)).map : (M ⟶ N) → _) ↔
      Function.Bijective ((Comonad.comparison
        (Adjunction.ofCat (F.map f.op.toLoc).adj)).map : (M ⟶ N) → _) := by
  have hE : Function.Bijective
      ((DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor.map :
        ((F.toDescentDataAsCoalgebra (fun _ : ι ↦ f)).obj M ⟶
          (F.toDescentDataAsCoalgebra (fun _ : ι ↦ f)).obj N) → _) :=
    (Functor.FullyFaithful.nonempty_iff_map_bijective _).1
      ⟨(DescentDataAsCoalgebra.coalgebraEquivalence F ι f).fullyFaithfulFunctor⟩ _ _
  have key : ((Comonad.comparison
        (Adjunction.ofCat (F.map f.op.toLoc).adj)).map : (M ⟶ N) → _) =
      (DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor.map ∘
        ((F.toDescentDataAsCoalgebra (fun _ : ι ↦ f)).map) := rfl
  rw [key]
  exact (hE.of_comp_iff' _).symm

/-- **The single-morphism comparison of `DescentData` with `DescentDataAsCoalgebra`, on
morphisms.**  For a pseudofunctor to the bicategory of adjunctions in `Cat`, a one-element
family `f : X ⟶ S` with a chosen pullback of `f` with itself, and objects `M`, `N` over `S`:
if the base-change morphism `f^* f_* ⟶ (p₁)_* p₂^*` is a monomorphism at `f^* N`, then
bijectivity on `M ⟶ N` of the coalgebra comparison functor implies bijectivity of the
descent-data comparison functor. -/
theorem bijective_toDescentData_map_of_bijective_toDescentDataAsCoalgebra_map
    (sq : ChosenPullback f f) {ι : Type t} [Unique ι] {M N : (F.obj (.mk (op S))).obj}
    (hmono : Mono ((descentBaseChange (F := F.comp Adj.forget₁) sq
      (Adjunction.ofCat (F.map f.op.toLoc).adj)
      (Adjunction.ofCat (F.map sq.p₁.op.toLoc).adj)).app
        ((F.map f.op.toLoc).l.toFunctor.obj N)))
    (h : Function.Bijective ((F.toDescentDataAsCoalgebra (fun _ : ι ↦ f)).map :
      (M ⟶ N) → _)) :
    Function.Bijective
      (((F.comp Adj.forget₁).toDescentData (fun _ : ι ↦ f)).map : (M ⟶ N) → _) :=
  bijective_toDescentData_map_of_bijective_comparison_map (F := F.comp Adj.forget₁) sq
    (Adjunction.ofCat (F.map f.op.toLoc).adj)
    (Adjunction.ofCat (F.map sq.p₁.op.toLoc).adj) hmono
    ((bijective_toDescentDataAsCoalgebra_map_iff ι M N).1 h)

end AdjCat

end Pseudofunctor

end CategoryTheory

end
