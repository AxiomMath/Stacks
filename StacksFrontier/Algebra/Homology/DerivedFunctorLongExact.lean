module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# The long exact sequence of right derived functors

Let `F ⟶ G ⟶ H` be a short complex of additive functors between abelian categories which is
*short exact on injective objects*: for every injective `X`, the short complex
`F.obj X ⟶ G.obj X ⟶ H.obj X` is short exact.  Then the right derived functors of `F`, `G` and
`H` fit into a long exact sequence

`0 ⟶ R⁰F ⟶ R⁰G ⟶ R⁰H ⟶ R¹F ⟶ R¹G ⟶ R¹H ⟶ R²F ⟶ ⋯`

whose connecting morphisms are natural transformations `RⁿH ⟶ Rⁿ⁺¹F`.

The hypothesis is stated on injective objects only, rather than asking `G ⟶ H` to be an
epimorphism of functors; this is the form in which the hypothesis occurs in practice (sheaf
restriction maps are surjective only on injective sheaves).

## Main definitions

* `CategoryTheory.NatTrans.appShortComplex`: the short complex `F.obj X ⟶ G.obj X ⟶ H.obj X`.
* `CategoryTheory.NatTrans.mapHomologicalComplexShortComplex`: the short complex of homological
  complexes obtained by applying the two natural transformations degreewise.
* `CategoryTheory.rightDerivedDelta`: the connecting natural transformation
  `H.rightDerived n ⟶ F.rightDerived (n + 1)`.

## Main results

* `CategoryTheory.NatTrans.shortExact_mapHomologicalComplexShortComplex`: a short complex of
  functors which is short exact at every term of a homological complex `K` induces a short
  exact sequence of homological complexes.
* `CategoryTheory.mono_rightDerived_zero_app`: the sequence begins with `0 ⟶ R⁰F ⟶ R⁰G`.
* `CategoryTheory.exact_rightDerived_composableArrows₅`: exactness of every six-term window.
* `CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`: the long exact sequence.
* `CategoryTheory.triangleOfInjectiveCochainComplex_distinguished`: the same input produces a
  distinguished triangle in the derived category of `B` at every cochain complex of injective
  objects of `A`, with connecting morphism natural in the complex
  (`CategoryTheory.triangleOfInjectiveCochainComplexδ_naturality`).

## Implementation notes

`Functor.rightDerived` is computed from a chosen injective resolution, and the connecting
morphism is the snake-lemma connecting morphism
(`CategoryTheory.ShortComplex.ShortExact.δ`) of the short exact sequence of complexes obtained
by applying the functors to that resolution.  Naturality of the connecting morphism comes from
`HomologicalComplex.HomologySequence.δ_naturality` applied to the morphism of short exact
sequences of complexes induced by a comparison map of injective resolutions.

The long exact sequence and the distinguished triangle are two *packagings of the same
hypothesis*, not two packagings of the same proof: they share only
`NatTrans.shortExact_mapHomologicalComplexShortComplex`, the observation that applying the
functors degreewise to a complex of injectives gives a short exact sequence of complexes.  From
there the long exact sequence uses the snake lemma in `B` and Mathlib's
`Functor.rightDerived` (pointwise injective resolutions of *objects*), while the triangle uses
`DerivedCategory.triangleOfSES`.  Turning the triangle into one for *total* right derived
functors on the unbounded derived category additionally requires a functorial K-injective
resolution, which is not part of this file.

`InjectiveResolution.isoRightDerivedObj` has target
`(HomologicalComplex.homologyFunctor _ _ n).obj K`, whereas the homology sequence is stated
using `K.homology n`.  The two are definitionally equal but not syntactically so, and the
mismatch blocks `Category.assoc`; `InjectiveResolution.isoRightDerivedObj'` is the same
isomorphism with the second spelling, and the primed naturality lemmas are restatements of the
Mathlib ones in that spelling.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits ComposableArrows

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] {F G H : A ⥤ B}

/-- The short complex `F.obj X ⟶ G.obj X ⟶ H.obj X`. -/
@[simps]
def NatTrans.appShortComplex (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0) (X : A) :
    ShortComplex B :=
  ShortComplex.mk (i.app X) (q.app X) (by rw [← NatTrans.comp_app, hiq]; simp)

section

variable [HasInjectiveResolutions A] [F.Additive] [G.Additive] [H.Additive]
  (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0) {ι : Type*} (c : ComplexShape ι)

/-- The short complex of homological complexes obtained by applying `i` and `q` degreewise. -/
@[reducible]
def NatTrans.mapHomologicalComplexShortComplex (K : HomologicalComplex A c) :
    ShortComplex (HomologicalComplex B c) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex i c).app K)
    ((NatTrans.mapHomologicalComplex q c).app K) (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, hiq]
      ext n
      simp)

/-- Functoriality of `NatTrans.mapHomologicalComplexShortComplex` in the complex. -/
@[simps]
def NatTrans.mapHomologicalComplexShortComplexMap {K L : HomologicalComplex A c} (phi : K ⟶ L) :
    NatTrans.mapHomologicalComplexShortComplex i q hiq c K ⟶
      NatTrans.mapHomologicalComplexShortComplex i q hiq c L where
  τ₁ := (F.mapHomologicalComplex c).map phi
  τ₂ := (G.mapHomologicalComplex c).map phi
  τ₃ := (H.mapHomologicalComplex c).map phi
  comm₁₂ := (NatTrans.mapHomologicalComplex i c).naturality phi
  comm₂₃ := (NatTrans.mapHomologicalComplex q c).naturality phi

omit [HasInjectiveResolutions A] in
/-- If `0 → F(K^n) → G(K^n) → H(K^n) → 0` is short exact for every `n`, then the short
complex `NatTrans.mapHomologicalComplexShortComplex i q hiq c K` is short exact. -/
lemma NatTrans.shortExact_mapHomologicalComplexShortComplex (K : HomologicalComplex A c)
    (h : ∀ n, (NatTrans.appShortComplex i q hiq (K.X n)).ShortExact) :
    (NatTrans.mapHomologicalComplexShortComplex i q hiq c K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ h

end

section Derived

/-- The successor relation of the `ℕ`-indexed cochain complex shape, as a `Rel` proof. -/
lemma ComplexShape.up_rel_succ (n : ℕ) : (ComplexShape.up ℕ).Rel n (n + 1) := rfl

variable [HasInjectiveResolutions A] [F.Additive] [G.Additive] [H.Additive]

/-- `InjectiveResolution.isoRightDerivedObj`, with its target spelled as the homology of a
complex rather than as a value of the homology functor.  The two are definitionally equal,
but only the former lets `Category.assoc` fire. -/
noncomputable def InjectiveResolution.isoRightDerivedObj' {X : A} (P : InjectiveResolution X)
    (E : A ⥤ B) [E.Additive] (n : ℕ) :
    (E.rightDerived n).obj X ≅
      ((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex).homology n :=
  P.isoRightDerivedObj E n

/-- Naturality in the *functor* variable of `InjectiveResolution.isoRightDerivedObj'`. -/
lemma homologyMap_comp_isoRightDerivedObj'_inv (a : F ⟶ G) {X : A}
    (P : InjectiveResolution X) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex a (ComplexShape.up ℕ)).app P.cocomplex) n ≫
        (P.isoRightDerivedObj' G n).inv =
      (P.isoRightDerivedObj' F n).inv ≫ (NatTrans.rightDerived a n).app X := by
  have h : (HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex a (ComplexShape.up ℕ)).app P.cocomplex) ≫
        (P.isoRightDerivedObj G n).inv =
      (P.isoRightDerivedObj F n).inv ≫ (NatTrans.rightDerived a n).app X := by
    rw [P.rightDerived_app_eq a n, Iso.inv_hom_id_assoc]
  exact h

variable (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0)
  (hinj : ∀ X : A, Injective X → (NatTrans.appShortComplex i q hiq X).ShortExact)

include hinj

omit [HasInjectiveResolutions A] in
/-- The short exact sequence of complexes obtained from an injective resolution. -/
lemma InjectiveResolution.shortExact_map {X : A} (P : InjectiveResolution X) :
    (NatTrans.mapHomologicalComplexShortComplex i q hiq (ComplexShape.up ℕ)
      P.cocomplex).ShortExact :=
  NatTrans.shortExact_mapHomologicalComplexShortComplex i q hiq _ _
    fun n => hinj _ (P.injective n)

/-- The connecting morphism of the long exact sequence of right derived functors,
computed from an injective resolution. -/
noncomputable def InjectiveResolution.rightDerivedDelta {X : A} (P : InjectiveResolution X)
    (n : ℕ) : (H.rightDerived n).obj X ⟶ (F.rightDerived (n + 1)).obj X :=
  (P.isoRightDerivedObj' H n).hom ≫
    (InjectiveResolution.shortExact_map i q hiq hinj P).δ n (n + 1) (ComplexShape.up_rel_succ n) ≫
      (P.isoRightDerivedObj' F (n + 1)).inv

omit [HasInjectiveResolutions A] in
/-- Naturality of the snake-lemma connecting map for the resolved sequences, stated
with `homologyMap`. -/
@[reassoc]
lemma InjectiveResolution.delta_naturality {X Y : A}
    (P : InjectiveResolution X) (Q : InjectiveResolution Y)
    (phi : P.cocomplex ⟶ Q.cocomplex) (n : ℕ) :
    (InjectiveResolution.shortExact_map i q hiq hinj P).δ n (n + 1) (ComplexShape.up_rel_succ n) ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map phi) (n + 1) =
      HomologicalComplex.homologyMap
          ((H.mapHomologicalComplex (ComplexShape.up ℕ)).map phi) n ≫
        (InjectiveResolution.shortExact_map i q hiq hinj Q).δ n (n + 1)
          (ComplexShape.up_rel_succ n) :=
  HomologicalComplex.HomologySequence.δ_naturality
    (NatTrans.mapHomologicalComplexShortComplexMap i q hiq (ComplexShape.up ℕ) phi)
    (InjectiveResolution.shortExact_map i q hiq hinj P)
    (InjectiveResolution.shortExact_map i q hiq hinj Q) n (n + 1) (ComplexShape.up_rel_succ n)

/-- The connecting morphism is natural. -/
lemma InjectiveResolution.rightDerivedDelta_naturality {X Y : A} (f : X ⟶ Y)
    (P : InjectiveResolution X) (Q : InjectiveResolution Y)
    (phi : P.cocomplex ⟶ Q.cocomplex) (comm : P.ι.f 0 ≫ phi.f 0 = f ≫ Q.ι.f 0) (n : ℕ) :
    (H.rightDerived n).map f ≫ InjectiveResolution.rightDerivedDelta i q hiq hinj Q n =
      InjectiveResolution.rightDerivedDelta i q hiq hinj P n ≫
        (F.rightDerived (n + 1)).map f := by
  dsimp only [InjectiveResolution.rightDerivedDelta]
  simp only [Category.assoc]
  exact (InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc f P Q phi comm H n _).trans
    (_ ≫= ((InjectiveResolution.delta_naturality_assoc i q hiq hinj P Q phi n _).symm.trans
      (_ ≫= (InjectiveResolution.isoRightDerivedObj_inv_naturality f P Q phi comm F (n + 1)).symm)))

/-- The connecting morphism of the long exact sequence of right derived functors,
as a natural transformation. -/
noncomputable def rightDerivedDelta (n : ℕ) : H.rightDerived n ⟶ F.rightDerived (n + 1) where
  app X := InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n
  naturality _ _ f :=
    InjectiveResolution.rightDerivedDelta_naturality i q hiq hinj f _ _
      (InjectiveResolution.desc f _ _) (InjectiveResolution.desc_commutes_zero f _ _) n

/-- Exactness of the six-term window
`Rⁿ F X ⟶ Rⁿ G X ⟶ Rⁿ H X ⟶ Rⁿ⁺¹ F X ⟶ Rⁿ⁺¹ G X ⟶ Rⁿ⁺¹ H X`
of the long exact sequence of right derived functors. -/
lemma exact_rightDerived_composableArrows₅ {X : A} (P : InjectiveResolution X) (n : ℕ) :
    (ComposableArrows.mk₅
      ((NatTrans.rightDerived i n).app X) ((NatTrans.rightDerived q n).app X)
      (InjectiveResolution.rightDerivedDelta i q hiq hinj P n)
      ((NatTrans.rightDerived i (n + 1)).app X)
      ((NatTrans.rightDerived q (n + 1)).app X)).Exact :=
  ComposableArrows.exact_of_iso
    (ComposableArrows.isoMk₅
      (P.isoRightDerivedObj' F n).symm (P.isoRightDerivedObj' G n).symm
      (P.isoRightDerivedObj' H n).symm (P.isoRightDerivedObj' F (n + 1)).symm
      (P.isoRightDerivedObj' G (n + 1)).symm (P.isoRightDerivedObj' H (n + 1)).symm
      (homologyMap_comp_isoRightDerivedObj'_inv i P n)
      (homologyMap_comp_isoRightDerivedObj'_inv q P n)
      (Iso.inv_hom_id_assoc (P.isoRightDerivedObj' H n) _).symm
      (homologyMap_comp_isoRightDerivedObj'_inv i P (n + 1))
      (homologyMap_comp_isoRightDerivedObj'_inv q P (n + 1)))
    (HomologicalComplex.HomologySequence.composableArrows₅_exact
      (InjectiveResolution.shortExact_map i q hiq hinj P) n (n + 1)
      (ComplexShape.up_rel_succ n))

/-- The long exact sequence of right derived functors starts with `0 ⟶ R⁰F ⟶ R⁰G`. -/
lemma mono_rightDerived_zero_app (X : A) : Mono ((NatTrans.rightDerived i 0).app X) := by
  let P := injectiveResolution X
  let S := NatTrans.mapHomologicalComplexShortComplex i q hiq (ComplexShape.up ℕ) P.cocomplex
  have : Mono (S.f.f 0) := (hinj _ (P.injective 0)).mono_f
  have hc : Mono (HomologicalComplex.homologyMap S.f 0 ≫
      (CochainComplex.isoHomologyπ₀
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).inv) := by
    rw [CochainComplex.isoHomologyπ₀_inv_naturality]
    infer_instance
  have : Mono (HomologicalComplex.homologyMap S.f 0) :=
    mono_of_mono (HomologicalComplex.homologyMap S.f 0)
      (CochainComplex.isoHomologyπ₀
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).inv
  have : Mono ((HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) 0).map S.f) :=
    inferInstanceAs (Mono (HomologicalComplex.homologyMap S.f 0))
  rw [P.rightDerived_app_eq i 0]
  infer_instance

/-- **A short exact sequence of additive functors which is exact on injectives induces a
natural long exact sequence of right derived functors.** -/
theorem longExact_rightDerived_of_shortExact_on_injectives :
    ∃ delta : ∀ n : ℕ, H.rightDerived n ⟶ F.rightDerived (n + 1),
      (∀ X : A, Mono ((NatTrans.rightDerived i 0).app X)) ∧
        ∀ (n : ℕ) (X : A), (ComposableArrows.mk₅
          ((NatTrans.rightDerived i n).app X) ((NatTrans.rightDerived q n).app X)
          ((delta n).app X) ((NatTrans.rightDerived i (n + 1)).app X)
          ((NatTrans.rightDerived q (n + 1)).app X)).Exact :=
  ⟨rightDerivedDelta i q hiq hinj, mono_rightDerived_zero_app i q hiq hinj,
    fun n X => exact_rightDerived_composableArrows₅ i q hiq hinj (injectiveResolution X) n⟩

end Derived


section Triangle

open Pretriangulated

variable [HasDerivedCategory B] [F.Additive] [G.Additive] [H.Additive]
  (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0)
  (hinj : ∀ X : A, Injective X → (NatTrans.appShortComplex i q hiq X).ShortExact)

include hinj

omit [HasDerivedCategory B] in
/-- A cochain complex of injective objects of `A` to which the functors are applied gives a
short exact sequence of cochain complexes of `B`. -/
lemma NatTrans.shortExact_mapCochainComplex (K : CochainComplex A ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    (NatTrans.mapHomologicalComplexShortComplex i q hiq (ComplexShape.up ℤ) K).ShortExact :=
  NatTrans.shortExact_mapHomologicalComplexShortComplex i q hiq _ _ fun n => hinj _ (hK n)

/-- The triangle `F(K) ⟶ G(K) ⟶ H(K) ⟶ F(K)[1]` in the derived category of `B`, for `K` a
cochain complex of injective objects of `A`. -/
noncomputable def triangleOfInjectiveCochainComplex (K : CochainComplex A ℤ)
    (hK : ∀ n, Injective (K.X n)) : Triangle (DerivedCategory B) :=
  DerivedCategory.triangleOfSES (NatTrans.shortExact_mapCochainComplex i q hiq hinj K hK)

/-- **A short exact sequence of additive functors which is exact on injectives induces a
distinguished triangle of the applied functors at every cochain complex of injectives.** -/
lemma triangleOfInjectiveCochainComplex_distinguished (K : CochainComplex A ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    triangleOfInjectiveCochainComplex i q hiq hinj K hK ∈ distTriang (DerivedCategory B) :=
  DerivedCategory.triangleOfSES_distinguished _

/-- The connecting morphism of `triangleOfInjectiveCochainComplex` is natural in the complex. -/
lemma triangleOfInjectiveCochainComplexδ_naturality {K L : CochainComplex A ℤ}
    (hK : ∀ n, Injective (K.X n)) (hL : ∀ n, Injective (L.X n)) (phi : K ⟶ L) :
    (triangleOfInjectiveCochainComplex i q hiq hinj K hK).mor₃ ≫
        (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map phi))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map phi) ≫
        (triangleOfInjectiveCochainComplex i q hiq hinj L hL).mor₃ :=
  DerivedCategory.triangleOfSESδ_naturality
    (NatTrans.shortExact_mapCochainComplex i q hiq hinj K hK)
    (NatTrans.shortExact_mapCochainComplex i q hiq hinj L hL)
    (NatTrans.mapHomologicalComplexShortComplexMap i q hiq (ComplexShape.up ℤ) phi)

end Triangle

end CategoryTheory
