module

public import StacksFrontier.LinearAlgebra.ExteriorPower.SemilinearDerived

/-!
# Long exact sequences of semilinear derived functors on arrows

Let `0 → F₁ → F₂ → F₃ → 0` be a sequence of functors `C ⥤ D` between abelian categories which is
short exact on every projective object of `C`. For a simplicial projective resolution `P` of an
object `X` of `C`, the simplicial objects `Fᵢ(P)` then form a degreewise short exact sequence, so
their alternating face map complexes form a short exact sequence of chain complexes, and the
homology sequence of the latter is a long exact sequence
`⋯ → Lⱼ₊₁F₃(X) → LⱼF₁(X) → LⱼF₂(X) → LⱼF₃(X) → Lⱼ₋₁F₁(X) → ⋯`
of simplicial left derived objects `LⱼFᵢ(X) = Hⱼ(s(Fᵢ(P)))`. Its connecting morphism
`δ : Lⱼ₊₁F₃(X) → LⱼF₁(X)` is natural in `X` and compatible with the comparison isomorphisms
between resolutions.

For a short exact sequence `0 → Φ₁ → Φ₂ → Φ₃ → 0` of semilinear functors on arrows of modules
(short exact on projective arrows over every commutative ring) the connecting morphisms commute
moreover with the derived semilinear maps along flat ring maps `φ : A → B`: both are computed
from one semilinear lift `P → φ^* Q`, which induces a morphism from the short exact sequence of
complexes `s(Φᵢ,A(P))` to the restriction of scalars of the short exact sequence `s(Φᵢ,B(Q))`,
and the connecting morphism of the homology sequence is natural and commutes with exact
functors such as restriction of scalars.

## Main definitions

* `Stacks.ShortExactOnProjectives`: a sequence `F₁ ⟶ F₂ ⟶ F₃` of functors which is short exact
  on projective objects.
* `Stacks.ShortExactOnProjectives.derivedδ`: the connecting morphism
  `Lⱼ₊₁F₃(X) ⟶ LⱼF₁(X)`, computed with a simplicial projective resolution of `X`.
* `Stacks.SemilinearArrowFunctor.ShortExact`: a short exact sequence of semilinear functors on
  arrows, short exact on projective arrows over every commutative ring.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.δ_comp_mapHomologyIso_hom`: the connecting morphism of
  the homology sequence of a short exact sequence of complexes commutes with every functor which
  preserves homology.
* `Stacks.ShortExactOnProjectives.exact_derivedHomologyMap`,
  `Stacks.ShortExactOnProjectives.exact_derivedHomologyMap_derivedδ` and
  `Stacks.ShortExactOnProjectives.exact_derivedδ_derivedHomologyMap`: exactness of the long exact
  sequence at its three kinds of terms, with `Function.Exact` forms for modules.
* `Stacks.ShortExactOnProjectives.derivedδ_comp_derivedMap` and
  `Stacks.ShortExactOnProjectives.derivedδ_comp_derivedIso_hom`: naturality of the connecting
  morphism and compatibility with the comparison isomorphisms between resolutions.
* `Stacks.ShortExactOnProjectives.derivedδ_comp_alternatingFaceMapHomologyMap`: naturality of
  the connecting morphism with respect to morphisms into the image under an exact functor.
* `Stacks.SemilinearArrowFunctor.ShortExact.derivedδ_comp_derivedMap` and
  `Stacks.SemilinearArrowFunctor.ShortExact.derivedSemilinearMap_derivedδ`: the connecting
  morphisms commute with the derived semilinear maps along flat ring maps.

## Implementation notes

Short exactness is only asked on projective objects: this is what the functors arising in
practice satisfy (for instance the sequence `0 → Λ²M' → Fil → M' ⊗ M'' → 0` attached to a split
monomorphism `M' → M`), and it is all that the simplicial derived functors see, since the terms
of a simplicial projective resolution are projective. The connecting morphism is that of Mathlib's
homology sequence `CategoryTheory.ShortComplex.ShortExact.δ` for the short exact sequence of
alternating face map complexes. That it commutes with an exact functor `H` is proved through the
characterization `CategoryTheory.ShortComplex.ShortExact.δ_eq'` of the connecting morphism of
`H(S)`, tested on the image under `H` of the fibre product through which the snake lemma
constructs the connecting morphism of `S`; for this the identifications of cycles and opcycles of
`H(K)` with the images of those of `K` are recorded in the form of
`HomologicalComplex.mapCyclesIso` and `HomologicalComplex.mapOpcyclesIso`.

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe u

/-! ### Exact functors, cycles, opcycles and homology -/

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (S : ShortComplex C) (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- The comparison isomorphism `S.mapOpcyclesIso F : (S.map F).opcycles ≅ F.obj S.opcycles` is
compatible with the projections onto the opcycles. -/
@[reassoc]
lemma pOpcycles_comp_mapOpcyclesIso_hom :
    (S.map F).pOpcycles ≫ (S.mapOpcyclesIso F).hom = F.map S.pOpcycles :=
  (S.rightHomologyData.map F).pOpcycles_comp_opcyclesIso_hom

/-- The inverse form of `ShortComplex.pOpcycles_comp_mapOpcyclesIso_hom`. -/
@[reassoc]
lemma map_pOpcycles_comp_mapOpcyclesIso_inv :
    F.map S.pOpcycles ≫ (S.mapOpcyclesIso F).inv = (S.map F).pOpcycles := by
  rw [← pOpcycles_comp_mapOpcyclesIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The comparison isomorphisms of homology and of opcycles are compatible with the inclusions
`homologyι` of homology into opcycles. -/
@[reassoc]
lemma mapHomologyIso_inv_comp_homologyι :
    (S.mapHomologyIso F).inv ≫ (S.map F).homologyι =
      F.map S.homologyι ≫ (S.mapOpcyclesIso F).inv := by
  have := F.preservesFiniteColimits_of_preservesHomology
  rw [← cancel_epi (F.map S.homologyπ), π_comp_mapHomologyIso_inv_assoc, homology_π_ι,
    ← F.map_comp_assoc, homology_π_ι, F.map_comp, Category.assoc,
    map_pOpcycles_comp_mapOpcyclesIso_inv, mapCyclesIso_inv_comp_iCycles_assoc]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {ι : Type*} {c : ComplexShape ι}

/-- For a functor `F` preserving homology, the cycles of the complex `F(K)` are `F` applied to
the cycles of `K`. -/
def mapCyclesIso (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (i : ι) : ((F.mapHomologicalComplex c).obj K).cycles i ≅ F.obj (K.cycles i) :=
  (K.sc i).mapCyclesIso F

/-- For a functor `F` preserving homology, the opcycles of the complex `F(K)` are `F` applied to
the opcycles of `K`. -/
def mapOpcyclesIso (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (i : ι) : ((F.mapHomologicalComplex c).obj K).opcycles i ≅ F.obj (K.opcycles i) :=
  (K.sc i).mapOpcyclesIso F

variable (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- The identification `mapCyclesIso` is compatible with the inclusions of the cycles. -/
@[reassoc]
lemma mapCyclesIso_inv_comp_iCycles (K : HomologicalComplex C c) (i : ι) :
    (K.mapCyclesIso F i).inv ≫ ((F.mapHomologicalComplex c).obj K).iCycles i =
      F.map (K.iCycles i) :=
  (K.sc i).mapCyclesIso_inv_comp_iCycles F

/-- The identification `mapOpcyclesIso` is compatible with the projections onto the opcycles. -/
@[reassoc]
lemma map_pOpcycles_comp_mapOpcyclesIso_inv (K : HomologicalComplex C c) (i : ι) :
    F.map (K.pOpcycles i) ≫ (K.mapOpcyclesIso F i).inv =
      ((F.mapHomologicalComplex c).obj K).pOpcycles i :=
  (K.sc i).map_pOpcycles_comp_mapOpcyclesIso_inv F

/-- The identifications `mapHomologyIso` and `mapOpcyclesIso` are compatible with the inclusions
of homology into opcycles. -/
@[reassoc]
lemma map_homologyι_comp_mapOpcyclesIso_inv (K : HomologicalComplex C c) (i : ι) :
    F.map (K.homologyι i) ≫ (K.mapOpcyclesIso F i).inv =
      (K.mapHomologyIso F i).inv ≫ ((F.mapHomologicalComplex c).obj K).homologyι i :=
  ((K.sc i).mapHomologyIso_inv_comp_homologyι F).symm

/-- The identifications `mapCyclesIso` and `mapHomologyIso` are compatible with the projections
of cycles onto homology. -/
@[reassoc]
lemma mapCyclesIso_inv_comp_homologyπ_comp_mapHomologyIso_hom (K : HomologicalComplex C c)
    (i : ι) :
    (K.mapCyclesIso F i).inv ≫ ((F.mapHomologicalComplex c).obj K).homologyπ i ≫
      (K.mapHomologyIso F i).hom = F.map (K.homologyπ i) :=
  (K.sc i).mapCyclesIso_inv_comp_homologyπ F

/-- The identification `mapCyclesIso` is natural in the complex. -/
@[reassoc]
lemma map_cyclesMap_comp_mapCyclesIso_inv {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι) :
    F.map (cyclesMap φ i) ≫ (L.mapCyclesIso F i).inv =
      (K.mapCyclesIso F i).inv ≫ cyclesMap ((F.mapHomologicalComplex c).map φ) i :=
  ShortComplex.mapCyclesIso_inv_naturality ((shortComplexFunctor C c i).map φ) F

/-- The identification `mapOpcyclesIso` is natural in the complex. -/
@[reassoc]
lemma map_opcyclesMap_comp_mapOpcyclesIso_inv {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (i : ι) :
    F.map (opcyclesMap φ i) ≫ (L.mapOpcyclesIso F i).inv =
      (K.mapOpcyclesIso F i).inv ≫ opcyclesMap ((F.mapHomologicalComplex c).map φ) i :=
  ShortComplex.mapOpcyclesIso_inv_naturality ((shortComplexFunctor C c i).map φ) F

/-- The identifications `mapOpcyclesIso` and `mapCyclesIso` are compatible with the morphisms
`opcyclesToCycles` from opcycles to cycles. -/
@[reassoc]
lemma map_opcyclesToCycles_comp_mapCyclesIso_inv (K : HomologicalComplex C c) (i j : ι) :
    F.map (K.opcyclesToCycles i j) ≫ (K.mapCyclesIso F j).inv =
      (K.mapOpcyclesIso F i).inv ≫ ((F.mapHomologicalComplex c).obj K).opcyclesToCycles i j := by
  have := F.preservesFiniteColimits_of_preservesHomology
  rw [← cancel_epi (F.map (K.pOpcycles i)),
    ← cancel_mono (((F.mapHomologicalComplex c).obj K).iCycles j)]
  simp only [Category.assoc, mapCyclesIso_inv_comp_iCycles,
    map_pOpcycles_comp_mapOpcyclesIso_inv_assoc, pOpcycles_opcyclesToCycles_iCycles]
  rw [← F.map_comp, ← F.map_comp, pOpcycles_opcyclesToCycles_iCycles]
  rfl

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)

include hS in
/-- A functor preserving homology carries a short exact sequence of complexes to a short exact
sequence of complexes. -/
lemma map_mapHomologicalComplex : (S.map (F.mapHomologicalComplex c)).ShortExact := by
  have := F.preservesFiniteLimits_of_preservesHomology
  have := F.preservesFiniteColimits_of_preservesHomology
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i).map_of_exact F

/-- **The connecting morphism commutes with exact functors.** For a functor `F` preserving
homology and a short exact sequence `S` of complexes, the connecting morphism of the homology
sequence of `F(S)` is `F` applied to that of `S`, under the identifications
`Hᵢ(F(K)) ≅ F(Hᵢ(K))`. -/
theorem δ_comp_mapHomologyIso_hom (hS' : (S.map (F.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    hS'.δ i j hij ≫ (S.X₁.mapHomologyIso F j).hom =
      (S.X₃.mapHomologyIso F i).hom ≫ F.map (hS.δ i j hij) := by
  have := F.preservesFiniteColimits_of_preservesHomology
  let E := HomologicalComplex.HomologySequence.snakeInput hS i j hij
  let p₁ : E.P ⟶ S.X₂.opcycles i := pullback.fst _ _
  let p₂ : E.P ⟶ S.X₃.homology i := pullback.snd _ _
  have hp : p₁ ≫ HomologicalComplex.opcyclesMap S.g i = p₂ ≫ S.X₃.homologyι i :=
    pullback.condition
  let q : E.P ⟶ S.X₁.cycles j := E.φ₁
  have hq : q ≫ HomologicalComplex.cyclesMap S.f j = p₁ ≫ S.X₂.opcyclesToCycles i j :=
    E.φ₁_L₂_f
  have hδ : p₂ ≫ hS.δ i j hij = q ≫ S.X₁.homologyπ j := E.snd_δ
  have : Epi p₂ := (inferInstance : Epi E.L₀'.g)
  have key := hS'.δ_eq' i j hij (F.map p₂ ≫ (S.X₃.mapHomologyIso F i).inv)
    (F.map p₁ ≫ (S.X₂.mapOpcyclesIso F i).inv) (F.map q ≫ (S.X₁.mapCyclesIso F j).inv)
    (by
      change _ ≫ HomologicalComplex.opcyclesMap ((F.mapHomologicalComplex c).map S.g) i = _
      rw [Category.assoc, ← HomologicalComplex.map_opcyclesMap_comp_mapOpcyclesIso_inv,
        ← F.map_comp_assoc, hp, F.map_comp_assoc,
        HomologicalComplex.map_homologyι_comp_mapOpcyclesIso_inv, Category.assoc]
      rfl)
    (by
      change _ ≫ HomologicalComplex.cyclesMap ((F.mapHomologicalComplex c).map S.f) j = _
      rw [Category.assoc, ← HomologicalComplex.map_cyclesMap_comp_mapCyclesIso_inv,
        ← F.map_comp_assoc, hq, F.map_comp_assoc,
        HomologicalComplex.map_opcyclesToCycles_comp_mapCyclesIso_inv, Category.assoc]
      rfl)
  simp only [Category.assoc] at key
  rw [← cancel_epi (S.X₃.mapHomologyIso F i).inv, Iso.inv_hom_id_assoc,
    ← cancel_epi (F.map p₂), ← F.map_comp, hδ, F.map_comp, reassoc_of% key]
  exact congrArg (F.map q ≫ ·)
    (HomologicalComplex.mapCyclesIso_inv_comp_homologyπ_comp_mapHomologyIso_hom F S.X₁ j)

end CategoryTheory.ShortComplex.ShortExact

/-! ### Sequences of functors which are short exact on projective objects -/

namespace Stacks

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {F₁ F₂ F₃ : C ⥤ D}

/-- A sequence `F₁ ⟶ F₂ ⟶ F₃` of functors between abelian categories is *short exact on
projective objects* if it composes to zero and `0 → F₁(X) → F₂(X) → F₃(X) → 0` is short exact for
every projective object `X`. -/
structure ShortExactOnProjectives (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) : Prop where
  /-- The sequence composes to zero. -/
  comp_eq_zero : α ≫ β = 0
  /-- The sequence is short exact on every projective object. -/
  shortExact (X : C) : Projective X →
    (ShortComplex.mk (α.app X) (β.app X)
      (by rw [← NatTrans.comp_app, comp_eq_zero, NatTrans.app_zero])).ShortExact

namespace ShortExactOnProjectives

open SimplicialProjectiveResolution

variable {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃} (h : ShortExactOnProjectives α β) {X Y : C}

omit [Abelian C] in
include h in
/-- The components of a sequence short exact on projective objects compose to zero. -/
@[reassoc]
lemma app_comp_app (X : C) : α.app X ≫ β.app X = 0 := by
  rw [← NatTrans.comp_app, h.comp_eq_zero, NatTrans.app_zero]

/-- The sequence of simplicial objects `F₁(P) ⟶ F₂(P) ⟶ F₃(P)` for a simplicial projective
resolution `P`. -/
abbrev simplicialShortComplex (P : SimplicialProjectiveResolution X) :
    ShortComplex (SimplicialObject D) :=
  ShortComplex.mk (Functor.whiskerLeft P.obj α) (Functor.whiskerLeft P.obj β)
    (by ext n : 2; exact h.app_comp_app _)

/-- The alternating face map complexes `s(F₁(P)) ⟶ s(F₂(P)) ⟶ s(F₃(P))` of a simplicial
projective resolution `P` form a short exact sequence, since the terms of `P` are projective. -/
lemma shortExact_derivedComplex (P : SimplicialProjectiveResolution X) :
    ((h.simplicialShortComplex P).map (alternatingFaceMapComplex D)).ShortExact :=
  ShortComplex.ShortExact.map_alternatingFaceMapComplex_of_app fun n =>
    h.shortExact _ (P.projective n)

/-- **The connecting morphism** `Lⱼ₊₁F₃(X) ⟶ LⱼF₁(X)` of the long exact sequence of simplicial
left derived objects, computed with a simplicial projective resolution `P` of `X`: the connecting
morphism of the homology sequence of `0 → s(F₁(P)) → s(F₂(P)) → s(F₃(P)) → 0`. -/
def derivedδ (P : SimplicialProjectiveResolution X) (j : ℕ) :
    P.derivedHomology F₃ (j + 1) ⟶ P.derivedHomology F₁ j :=
  (h.shortExact_derivedComplex P).δ (j + 1) j (by simp)

include h in
/-- Two consecutive maps of the long exact sequence compose to zero. -/
@[reassoc]
lemma derivedHomologyMap_comp_derivedHomologyMap (P : SimplicialProjectiveResolution X)
    (j : ℕ) : derivedHomologyMap α P j ≫ derivedHomologyMap β P j = 0 := by
  rw [derivedHomologyMap, derivedHomologyMap, ← HomologicalComplex.homologyMap_comp,
    ← Functor.map_comp, (h.simplicialShortComplex P).zero, Functor.map_zero,
    HomologicalComplex.homologyMap_zero]

/-- Two consecutive maps of the long exact sequence compose to zero. -/
@[reassoc (attr := simp)]
lemma derivedHomologyMap_comp_derivedδ (P : SimplicialProjectiveResolution X) (j : ℕ) :
    derivedHomologyMap β P (j + 1) ≫ h.derivedδ P j = 0 :=
  (h.shortExact_derivedComplex P).comp_δ _ _ _

/-- Two consecutive maps of the long exact sequence compose to zero. -/
@[reassoc (attr := simp)]
lemma derivedδ_comp_derivedHomologyMap (P : SimplicialProjectiveResolution X) (j : ℕ) :
    h.derivedδ P j ≫ derivedHomologyMap α P j = 0 :=
  (h.shortExact_derivedComplex P).δ_comp _ _ _

/-- **Exactness of the long exact sequence** at `LⱼF₂(X)`:
`LⱼF₁(X) ⟶ LⱼF₂(X) ⟶ LⱼF₃(X)` is exact. -/
theorem exact_derivedHomologyMap (P : SimplicialProjectiveResolution X) (j : ℕ) :
    (ShortComplex.mk _ _ (h.derivedHomologyMap_comp_derivedHomologyMap P j)).Exact :=
  (h.shortExact_derivedComplex P).homology_exact₂ j

/-- **Exactness of the long exact sequence** at `Lⱼ₊₁F₃(X)`:
`Lⱼ₊₁F₂(X) ⟶ Lⱼ₊₁F₃(X) ⟶ LⱼF₁(X)` is exact. -/
theorem exact_derivedHomologyMap_derivedδ (P : SimplicialProjectiveResolution X) (j : ℕ) :
    (ShortComplex.mk _ _ (h.derivedHomologyMap_comp_derivedδ P j)).Exact :=
  (h.shortExact_derivedComplex P).homology_exact₃ _ _ _

/-- **Exactness of the long exact sequence** at `LⱼF₁(X)`:
`Lⱼ₊₁F₃(X) ⟶ LⱼF₁(X) ⟶ LⱼF₂(X)` is exact. -/
theorem exact_derivedδ_derivedHomologyMap (P : SimplicialProjectiveResolution X) (j : ℕ) :
    (ShortComplex.mk _ _ (h.derivedδ_comp_derivedHomologyMap P j)).Exact :=
  (h.shortExact_derivedComplex P).homology_exact₁ _ _ _

/-- **Naturality of the connecting morphism.** For `g : X ⟶ Y`, the connecting morphisms
computed with resolutions `P` of `X` and `Q` of `Y` commute with the derived maps of `g`. -/
@[reassoc]
theorem derivedδ_comp_derivedMap (g : X ⟶ Y) (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    h.derivedδ P j ≫ derivedMap F₁ g P Q j = derivedMap F₃ g P Q (j + 1) ≫ h.derivedδ Q j := by
  obtain ⟨k, hk⟩ := exists_isLift P Q g
  let σ : h.simplicialShortComplex P ⟶ h.simplicialShortComplex Q :=
    { τ₁ := Functor.whiskerRight k F₁
      τ₂ := Functor.whiskerRight k F₂
      τ₃ := Functor.whiskerRight k F₃
      comm₁₂ := by ext n : 2; exact α.naturality (k.app n)
      comm₂₃ := by ext n : 2; exact β.naturality (k.app n) }
  rw [hk.derivedMap_eq, hk.derivedMap_eq]
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((alternatingFaceMapComplex D).mapShortComplex.map σ) (h.shortExact_derivedComplex P)
    (h.shortExact_derivedComplex Q) (j + 1) j (by simp)

/-- The connecting morphisms are compatible with the comparison isomorphisms between
resolutions. -/
@[reassoc]
theorem derivedδ_comp_derivedIso_hom (P P' : SimplicialProjectiveResolution X) (j : ℕ) :
    h.derivedδ P j ≫ (derivedIso F₁ P P' j).hom =
      (derivedIso F₃ P P' (j + 1)).hom ≫ h.derivedδ P' j :=
  h.derivedδ_comp_derivedMap (𝟙 X) P P' j

/-- The connecting morphisms are compatible with the comparison isomorphisms between
resolutions. -/
@[reassoc]
theorem derivedIso_inv_comp_derivedδ (P P' : SimplicialProjectiveResolution X) (j : ℕ) :
    (derivedIso F₃ P P' (j + 1)).inv ≫ h.derivedδ P j =
      h.derivedδ P' j ≫ (derivedIso F₁ P P' j).inv :=
  (h.derivedδ_comp_derivedMap (𝟙 X) P' P j).symm

/-- **Naturality of the connecting morphism with respect to an exact functor.** Let `H : D' ⥤ D`
preserve homology, let `F₁ ⟶ F₂ ⟶ F₃` on `C` and `G₁ ⟶ G₂ ⟶ G₃` on `C'` be short exact on
projective objects, and let `κᵢ : Fᵢ(P) ⟶ H(Gᵢ(Q))` be morphisms of simplicial objects compatible
with the two sequences. Then the connecting morphisms commute with the induced maps
`Hⱼ(s(Fᵢ(P))) ⟶ H(Hⱼ(s(Gᵢ(Q))))`. -/
theorem derivedδ_comp_alternatingFaceMapHomologyMap {C' : Type*} [Category C'] [Abelian C']
    {D' : Type*} [Category D'] [Abelian D'] {H : D' ⥤ D} [H.Additive] [H.PreservesHomology]
    {G₁ G₂ G₃ : C' ⥤ D'} {α' : G₁ ⟶ G₂} {β' : G₂ ⟶ G₃} (h' : ShortExactOnProjectives α' β')
    {Y' : C'} (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y')
    (κ₁ : P.obj ⋙ F₁ ⟶ (Q.obj ⋙ G₁) ⋙ H) (κ₂ : P.obj ⋙ F₂ ⟶ (Q.obj ⋙ G₂) ⋙ H)
    (κ₃ : P.obj ⋙ F₃ ⟶ (Q.obj ⋙ G₃) ⋙ H)
    (h₁₂ : Functor.whiskerLeft P.obj α ≫ κ₂ =
      κ₁ ≫ Functor.whiskerRight (Functor.whiskerLeft Q.obj α') H)
    (h₂₃ : Functor.whiskerLeft P.obj β ≫ κ₃ =
      κ₂ ≫ Functor.whiskerRight (Functor.whiskerLeft Q.obj β') H) (j : ℕ) :
    h.derivedδ P j ≫ alternatingFaceMapHomologyMap κ₁ j =
      alternatingFaceMapHomologyMap κ₃ (j + 1) ≫ H.map (h'.derivedδ Q j) := by
  have hT := h'.shortExact_derivedComplex Q
  have hT' := hT.map_mapHomologicalComplex H
  let ψ : (h.simplicialShortComplex P).map (alternatingFaceMapComplex D) ⟶
      ((h'.simplicialShortComplex Q).map (alternatingFaceMapComplex D')).map
        (H.mapHomologicalComplex _) :=
    { τ₁ := (alternatingFaceMapComplex D).map κ₁ ≫
        (alternatingFaceMapComplexCompIso (Q.obj ⋙ G₁) H).hom
      τ₂ := (alternatingFaceMapComplex D).map κ₂ ≫
        (alternatingFaceMapComplexCompIso (Q.obj ⋙ G₂) H).hom
      τ₃ := (alternatingFaceMapComplex D).map κ₃ ≫
        (alternatingFaceMapComplexCompIso (Q.obj ⋙ G₃) H).hom
      comm₁₂ := by
        ext n
        simpa using (NatTrans.congr_app h₁₂ (op ⦋n⦌)).symm
      comm₂₃ := by
        ext n
        simpa using (NatTrans.congr_app h₂₃ (op ⦋n⦌)).symm }
  have e₁ := HomologicalComplex.HomologySequence.δ_naturality ψ
    (h.shortExact_derivedComplex P) hT' (j + 1) j (by simp)
  have e₂ := hT.δ_comp_mapHomologyIso_hom H hT' (j + 1) j (by simp)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans (Category.assoc _ _ _).symm)))

end ShortExactOnProjectives

/-! ### Elementwise exactness for modules -/

namespace ShortExactOnProjectives

open SimplicialProjectiveResolution

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{u} R} {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃}
  (h : ShortExactOnProjectives α β) {X : C} (P : SimplicialProjectiveResolution X) (j : ℕ)

include h in
/-- **Exactness of the long exact sequence** at `LⱼF₂(X)`, elementwise. -/
theorem function_exact_derivedHomologyMap :
    Function.Exact (derivedHomologyMap α P j).hom (derivedHomologyMap β P j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (h.exact_derivedHomologyMap P j)

/-- **Exactness of the long exact sequence** at `Lⱼ₊₁F₃(X)`, elementwise. -/
theorem function_exact_derivedHomologyMap_derivedδ :
    Function.Exact (derivedHomologyMap β P (j + 1)).hom (h.derivedδ P j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (h.exact_derivedHomologyMap_derivedδ P j)

/-- **Exactness of the long exact sequence** at `LⱼF₁(X)`, elementwise. -/
theorem function_exact_derivedδ_derivedHomologyMap :
    Function.Exact (h.derivedδ P j).hom (derivedHomologyMap α P j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (h.exact_derivedδ_derivedHomologyMap P j)

end ShortExactOnProjectives

end Stacks

/-! ### Short exact sequences of semilinear functors on arrows -/

namespace Stacks.SemilinearArrowFunctor

open SimplicialProjectiveResolution

variable {Φ₁ Φ₂ Φ₃ : SemilinearArrowFunctor.{u}}

/-- A sequence `Φ₁ ⟶ Φ₂ ⟶ Φ₃` of semilinear functors on arrows is *short exact* if over every
commutative ring `A` the sequence `Φ₁,A ⟶ Φ₂,A ⟶ Φ₃,A` is short exact on projective arrows. -/
structure ShortExact (α : Φ₁ ⟶ Φ₂) (β : Φ₂ ⟶ Φ₃) : Prop where
  /-- Over every commutative ring the sequence is short exact on projective arrows. -/
  shortExactOnProjectives (A : CommRingCat.{u}) : ShortExactOnProjectives (α.app A) (β.app A)

variable {α : Φ₁ ⟶ Φ₂} {β : Φ₂ ⟶ Φ₃}

/-- Constructor for short exact sequences of semilinear functors on arrows: the sequence
composes to zero over every ring and is short exact on every projective arrow. -/
lemma ShortExact.mk' (hαβ : ∀ A : CommRingCat.{u}, α.app A ≫ β.app A = 0)
    (hS : ∀ (A : CommRingCat.{u}) (P : ComposableArrows (ModuleCat.{u} A) 1), Projective P →
      (ShortComplex.mk ((α.app A).app P) ((β.app A).app P)
        (by rw [← NatTrans.comp_app, hαβ, NatTrans.app_zero])).ShortExact) :
    ShortExact α β :=
  ⟨fun A => ⟨hαβ A, hS A⟩⟩

variable (h : ShortExact α β) {A B : CommRingCat.{u}} (φ : A ⟶ B) (hφ : φ.hom.Flat)
  {X : ComposableArrows (ModuleCat.{u} A) 1} {Y : ComposableArrows (ModuleCat.{u} B) 1}

/-- **The connecting morphisms commute with the derived semilinear maps.** For a flat ring map
`φ : A ⟶ B`, a morphism `f : X ⟶ φ^* Y` and simplicial projective resolutions `P` of `X` and `Q`
of `Y`, the square formed by the connecting morphisms `Lⱼ₊₁Φ₃(X) ⟶ LⱼΦ₁(X)`,
`Lⱼ₊₁Φ₃(Y) ⟶ LⱼΦ₁(Y)` and the derived semilinear maps commutes. -/
@[reassoc]
theorem ShortExact.derivedδ_comp_derivedMap (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    (h.shortExactOnProjectives A).derivedδ P j ≫ Φ₁.derivedMap φ hφ f P Q j =
      Φ₃.derivedMap φ hφ f P Q (j + 1) ≫
        (ModuleCat.restrictScalars φ.hom).map ((h.shortExactOnProjectives B).derivedδ Q j) := by
  obtain ⟨k, hk⟩ := exists_isLiftAlong φ hφ P Q f
  rw [Φ₁.derivedMap_eq φ hφ hk, Φ₃.derivedMap_eq φ hφ hk]
  exact (h.shortExactOnProjectives A).derivedδ_comp_alternatingFaceMapHomologyMap
    (h.shortExactOnProjectives B) P Q _ (Φ₂.simplicialMap φ k) _
    (Φ₁.simplicialMap_naturality φ α k) (Φ₂.simplicialMap_naturality φ β k) j

/-- **The connecting morphisms commute with the derived semilinear maps**, on elements: for
`x ∈ Lⱼ₊₁Φ₃(X)`, the derived semilinear map of `δ x` is `δ` of the derived semilinear map
of `x`. -/
theorem ShortExact.derivedSemilinearMap_derivedδ (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ)
    (x : P.derivedHomology (D := ModuleCat.{u} A) (Φ₃.obj A) (j + 1)) :
    Φ₁.derivedSemilinearMap φ hφ f P Q j (((h.shortExactOnProjectives A).derivedδ P j).hom x) =
      ((h.shortExactOnProjectives B).derivedδ Q j).hom
        (Φ₃.derivedSemilinearMap φ hφ f P Q (j + 1) x) :=
  congrArg (fun t => t.hom x) (h.derivedδ_comp_derivedMap φ hφ f P Q j)

end Stacks.SemilinearArrowFunctor
