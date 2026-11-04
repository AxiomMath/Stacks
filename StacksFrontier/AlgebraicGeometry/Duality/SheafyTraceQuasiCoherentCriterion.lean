module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTrace
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties

/-!
# Criteria for the sheafy trace of the right adjoint of pushforward to be an isomorphism

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and let `L` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)`. The
sheafy trace map of [Stacks, Tag 0B6H],

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

is a morphism of the unrestricted derived category `D(𝒪_Y)`: neither side need have
quasi-coherent cohomology. Write `DQ_Y : D(𝒪_Y) ⥤ D_QCoh(𝒪_Y)` for the coherator, a right
adjoint of the inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`. By [Stacks, Tag 0A9Q] the trace becomes an
isomorphism after applying `DQ_Y`. The content of [Stacks, Tag 0GEV] is that `DQ_Y` can be
*erased* as soon as both sides already lie in `D_QCoh(𝒪_Y)`:

* the right-hand side lies in `D_QCoh(𝒪_Y)` exactly when `R𝓗om_{𝒪_Y}(Rf_*L, K)` does;
* the left-hand side lies in `D_QCoh(𝒪_Y)` as soon as `R𝓗om_{𝒪_X}(L, a(K))` lies in
  `D_QCoh(𝒪_X)`, since `Rf_*` preserves quasi-coherence of cohomology — the identity
  `DQ_Y ∘ Rf_* = Rf_* ∘ DQ_X` of [Stacks, Tag 0CR1] in the source's formulation.

For an object of `D(𝒪_Y)` with quasi-coherent cohomology the counit `DQ_Y(−) ⟶ −` of the
coherator adjunction is an isomorphism, because the inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` is fully
faithful. Naturality of that counit at the trace then exhibits the trace as a composition of
three isomorphisms, so it is an isomorphism itself.

The two sufficient conditions of [Stacks, Tag 0GEV] put the two derived internal Homs in
`D_QCoh` by [Stacks, Tag 0A6H]:

1. `L` and `Rf_*L` are perfect — then `R𝓗om_{𝒪_X}(L, a(K))` and `R𝓗om_{𝒪_Y}(Rf_*L, K)` have
   quasi-coherent cohomology for any `K`, since `a(K)` and `K` already do;
2. `K` is bounded below and `L` and `Rf_*L` are pseudo-coherent — then `a(K)` is bounded below
   by [Stacks, Tag 0A9I], and the bounded-below half of [Stacks, Tag 0A6H] applies on both
   sides.

## Main results

* `Stacks.Duality.isIso_counit_app_of_prop` — for a right adjoint of the inclusion of a full
  subcategory, the counit at an object of the subcategory is an isomorphism.
* `Stacks.Duality.isIso_of_isIso_rightAdjoint_map` — a morphism between two objects at which the
  counit of such an adjunction is invertible is invertible as soon as the right adjoint sends it
  to an isomorphism.
* `Stacks.Duality.isIso_sheafyTrace_of_derivedCategoryB` — **[Stacks, Tag 0GEV], the
  quasi-coherence criterion**: the trace is an isomorphism when both derived internal Homs have
  quasi-coherent cohomology.
* `Stacks.Duality.isIso_sheafyTrace_of_isPerfect` — **[Stacks, Tag 0GEV] (1)**, the perfect case.
* `Stacks.Duality.isIso_sheafyTrace_of_isPseudoCoherent` — **[Stacks, Tag 0GEV] (2)**, the
  bounded-below pseudo-coherent case.

## Implementation notes

*The coherator is data.* The existence of a right adjoint `DQ_Y` of
`D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` is [Stacks, Tag 0CR0], which is not part of this development; the
functor and the adjunction are therefore arguments, exactly as they are of
`Stacks.Duality.coheratorDerivedPushforwardIso`. Nothing below uses anything about
`DQ_Y` other than the adjunction, so this restricts the statements to the schemes on which the
coherator exists and weakens nothing else.

*The right adjoint of `Rf_*` is a hypothesis*, as it is for the trace map itself; see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Duality/SheafyTrace.lean`.

*The three results the source cites are hypotheses, named for the tags they are.* None is proved
in this development, and each is an input to the argument, never its conclusion:

* `h0A9Q` is [Stacks, Tag 0A9Q]: the trace becomes an isomorphism after `DQ_Y`. This is strictly
  weaker than the conclusion — `DQ_Y` is not conservative, and the whole content of
  [Stacks, Tag 0GEV] is the extra input needed to pass from one to the other.
* `h0A6HX` and `h0A6HY` are the perfect part of [Stacks, Tag 0A6H] — the one that puts
  `R𝓗om(M, N)` in `D_QCoh` for `M` perfect and `N` in `D_QCoh`, with no bound on `N` — taken
  separately on `X` and on `Y`. Its bounded-below pseudo-coherent companion is proved in this
  development, as `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent`, and
  `Stacks.Duality.isIso_sheafyTrace_of_isPseudoCoherent` therefore needs no hypothesis of this
  kind; the perfect part, whose second argument is unbounded, is not available and stays a
  hypothesis of `Stacks.Duality.isIso_sheafyTrace_of_isPerfect`.
* `h0A9I` is [Stacks, Tag 0A9I] at the single object `K`: `a(K)` is bounded below when `K` is.

*Why `Rf_*` replaces [Stacks, Tag 0CR1].* The source erases `DQ_Y` on the left of the trace by
rewriting `DQ_Y(Rf_*−)` as `Rf_*(DQ_X−)`. What that rewriting is used for is the single
conclusion that `Rf_*R𝓗om_{𝒪_X}(L, a(K))` has quasi-coherent cohomology once
`R𝓗om_{𝒪_X}(L, a(K))` does, and that is exactly the hypothesis `hpush` already carried
throughout the `Stacks.Duality` namespace, which is [Stacks, Tag 08D5] part (1). The natural
isomorphism itself is `Stacks.Duality.coheratorDerivedPushforwardIso`, stated at the locally
small model of the derived categories; the trace map is stated at
`CategoryTheory.HasDerivedCategory.standard`, and a statement for one model says nothing about
the other, so it is the hypothesis and not the isomorphism that is used.

## References

* [Stacks Project, Tag 0GEV](https://stacks.math.columbia.edu/tag/0GEV)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

/-! ### Erasing a right adjoint of a fully faithful inclusion -/

section Erase

variable {C D : Type*} [Category C] [Category D]

/-- For a right adjoint `R` of the inclusion `ι : P.FullSubcategory ⥤ D` of a full subcategory,
the counit `ι(R A) ⟶ A` is an isomorphism at every object `A` of `D` satisfying `P`.

Indeed `A` is then the image under `ι` of an object of the subcategory, and the counit of an
adjunction whose left adjoint is fully faithful is invertible on the essential image of that
left adjoint. -/
theorem isIso_counit_app_of_prop {P : ObjectProperty D} {R : D ⥤ P.FullSubcategory}
    (adj : P.ι ⊣ R) {A : D} (hA : P A) : IsIso (adj.counit.app A) :=
  adj.isIso_counit_app_of_iso (Y := ⟨A, hA⟩) (Iso.refl A)

/-- **Erasing the right adjoint of a fully faithful inclusion.** Let `ι : C ⥤ D` be fully
faithful with right adjoint `R`, and let `g : A ⟶ B` in `D`. If `R g` is an isomorphism and the
counit of `ι ⊣ R` is an isomorphism at `A` and at `B`, then `g` is an isomorphism.

Naturality of the counit at `g` gives `ι(R g) ≫ ε_B = ε_A ≫ g`, so `g` is the composition of
the inverse of `ε_A`, the isomorphism `ι(R g)` and `ε_B`. -/
theorem isIso_of_isIso_rightAdjoint_map {ι : C ⥤ D} [ι.Full] [ι.Faithful] {R : D ⥤ C}
    (adj : ι ⊣ R) {A B : D} (g : A ⟶ B) (hA : IsIso (adj.counit.app A))
    (hB : IsIso (adj.counit.app B)) (hg : IsIso (R.map g)) : IsIso g := by
  have := hA
  have := hB
  have := hg
  have hnat : ι.map (R.map g) ≫ adj.counit.app B = adj.counit.app A ≫ g :=
    adj.counit.naturality g
  have hfac : g = inv (adj.counit.app A) ≫ ι.map (R.map g) ≫ adj.counit.app B := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  rw [hfac]
  infer_instance

end Erase

/-! ### The criteria of Tag 0GEV -/

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
  {DQY : DerivedCategory Y.Modules ⥤ quasiCoherentDerivedCategory Y}
  (adjY : (DerivedCategoryB.derivedCategoryB
    (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ⊣ DQY)
  (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)

include adjY in
/-- **[Stacks, Tag 0GEV], the quasi-coherence criterion.** Let `f : X ⟶ Y` be a morphism of
schemes along which `Rf_*` preserves quasi-coherence of cohomology, let `a` be a right adjoint
of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, let `DQ_Y` be a right adjoint of the inclusion
`D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`, and let `L` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)`. If
`R𝓗om_{𝒪_X}(L, a(K))` lies in `D_QCoh(𝒪_X)` and `R𝓗om_{𝒪_Y}(Rf_*L, K)` lies in `D_QCoh(𝒪_Y)`,
then the sheafy trace map

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`

of [Stacks, Tag 0B6H] is an isomorphism.

Both sides then lie in `D_QCoh(𝒪_Y)` — the left one because `Rf_*` preserves quasi-coherence of
cohomology, which is the content of the source's `DQ_Y ∘ Rf_* = Rf_* ∘ DQ_X` — so the counit of
the coherator adjunction is invertible at both, and the trace is an isomorphism because
[Stacks, Tag 0A9Q] makes it one after `DQ_Y`. -/
@[stacks 0GEV "the quasi-coherence criterion: the trace is an isomorphism once both derived \
internal Homs have quasi-coherent cohomology, granted Tag 0A9Q (the trace is an isomorphism \
after the coherator) as the explicit hypothesis h0A9Q, and the coherator of Tag 0CR0 as data"]
theorem isIso_sheafyTrace_of_derivedCategoryB
    (hsrc : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj))
    (htgt : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
        (op ((derivedPushforward f).obj L.obj))).obj K.obj))
    (h0A9Q : IsIso (DQY.map (sheafyTrace f DX DY hpush adj L K))) :
    IsIso (sheafyTrace f DX DY hpush adj L K) :=
  isIso_of_isIso_rightAdjoint_map adjY _
    (isIso_counit_app_of_prop adjY (hpush ⟨_, hsrc⟩)) (isIso_counit_app_of_prop adjY htgt) h0A9Q

include adjY in
/-- **[Stacks, Tag 0GEV] (1), the perfect case.** In the situation of
`Stacks.Duality.isIso_sheafyTrace_of_derivedCategoryB`, the sheafy trace map

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`

is an isomorphism whenever `L` and `Rf_*L` are perfect.

Since `a(K)` and `K` have quasi-coherent cohomology, the part of [Stacks, Tag 0A6H] for a
perfect first argument puts `R𝓗om_{𝒪_X}(L, a(K))` in `D_QCoh(𝒪_X)` and `R𝓗om_{𝒪_Y}(Rf_*L, K)`
in `D_QCoh(𝒪_Y)`, and the quasi-coherence criterion applies. No hypothesis on `K` beyond
quasi-coherence of its cohomology is needed. -/
@[stacks 0GEV "clause (1), the perfect case, granted Tag 0A9Q as the explicit hypothesis h0A9Q, \
the perfect half of Tag 0A6H as h0A6HX and h0A6HY, and the coherator of Tag 0CR0 as data"]
theorem isIso_sheafyTrace_of_isPerfect
    (h0A6HX : ∀ (M N : DerivedCategory X.Modules),
      RingedSpace.IsPerfect (X := X.toRingedSpace) M →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) N →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op M)).obj N))
    (h0A6HY : ∀ (M N : DerivedCategory Y.Modules),
      RingedSpace.IsPerfect (X := Y.toRingedSpace) M →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf) N →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
        (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op M)).obj N))
    (h0A9Q : IsIso (DQY.map (sheafyTrace f DX DY hpush adj L K))) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) L.obj →
    RingedSpace.IsPerfect (X := Y.toRingedSpace)
      ((quasiCoherentDerivedPushforward f hpush).obj L).obj →
    IsIso (sheafyTrace f DX DY hpush adj L K) := fun hL hRL =>
  isIso_sheafyTrace_of_derivedCategoryB f DX DY hpush adj adjY L K
    (h0A6HX L.obj (a.obj K).obj hL (a.obj K).property)
    (h0A6HY _ K.obj hRL K.property) h0A9Q

include adjY in
/-- **[Stacks, Tag 0GEV] (2), the bounded-below pseudo-coherent case.** In the situation of
`Stacks.Duality.isIso_sheafyTrace_of_derivedCategoryB`, the sheafy trace map

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`

is an isomorphism whenever `K` is bounded below and `L` and `Rf_*L` are pseudo-coherent.

The right adjoint `a` carries bounded-below complexes to bounded-below complexes by
[Stacks, Tag 0A9I], so `a(K)` lies in `D⁺_QCoh(𝒪_X)`; part (1) of [Stacks, Tag 0A6H], for a
pseudo-coherent first argument and a bounded-below second argument, then puts
`R𝓗om_{𝒪_X}(L, a(K))` in `D_QCoh(𝒪_X)` and `R𝓗om_{𝒪_Y}(Rf_*L, K)` in `D_QCoh(𝒪_Y)`, and the
quasi-coherence criterion applies. -/
@[stacks 0GEV "clause (2), the bounded-below pseudo-coherent case, granted Tag 0A9Q as the \
explicit hypothesis h0A9Q, Tag 0A9I as h0A9I, and the coherator of Tag 0CR0 as data"]
theorem isIso_sheafyTrace_of_isPseudoCoherent
    (h0A9I : DerivedCategoryB.IsBoundedBelow K.obj →
      DerivedCategoryB.IsBoundedBelow (a.obj K).obj)
    (h0A9Q : IsIso (DQY.map (sheafyTrace f DX DY hpush adj L K))) :
    DerivedCategoryB.IsBoundedBelow K.obj →
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) L.obj →
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((quasiCoherentDerivedPushforward f hpush).obj L).obj →
    IsIso (sheafyTrace f DX DY hpush adj L K) := fun hK hL hRL =>
  isIso_sheafyTrace_of_derivedCategoryB f DX DY hpush adj adjY L K
    (AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X L.obj
      (a.obj K).obj hL ⟨h0A9I hK, (a.obj K).property⟩)
    (AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent Y _ K.obj hRL
      ⟨hK, K.property⟩) h0A9Q

end Stacks.Duality

end
