module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# A pushed-forward base change map is a projection-formula map

Consider a square of categories and functors

```
     Lf
  A ---→ B
Lg |     | Lg'
   v     v
  A' --→ B'
     Lf'
```

in which *all four* functors have right adjoints, `Lf ⊣ Rf`, `Lf' ⊣ Rf'`, `Lg ⊣ Rg` and
`Lg' ⊣ Rg'`, and in which the two composites around the square are identified with one functor
`Lc` by `eg : Lg ⋙ Lf' ≅ Lc` and `ef : Lf ⋙ Lg' ≅ Lc`.  The base change map of
`Stacks.CategoryTheory.BaseChange.map` is then a morphism `Lg (Rf K) ⟶ Rf' (Lg' K)`, and
applying `Rg` to it gives

`Rg (Lg (Rf K)) ⟶ Rg (Rf' (Lg' K))`.

This file identifies that morphism: it is a *projection-formula map*, namely the mate under
`Lf ⊣ Rf` of the canonical comparison

`Lf ⋙ (Lg ⋙ Rg) ⟶ (Lg' ⋙ Rg') ⋙ Lf`

obtained by pasting the base change map of the transposed square with the comparison of the two
composites, followed by the conjugate isomorphism `Rg' ⋙ Rf ≅ Rf' ⋙ Rg` of the right adjoints.
No hypothesis is needed.

In the geometric situation of [Stacks, Tag 08IB] — a Cartesian square of schemes with `g` affine
— the two endofunctors `Lg ⋙ Rg = Rg_* Lg^*` and `Lg' ⋙ Rg' = Rg'_* L(g')^*` are identified by
[Stacks, Tag 08I9] with `- ⊗^𝐋 g_*𝒪_{S'}` and `- ⊗^𝐋 g'_*𝒪_{X'}`, and under those two
identifications the mate below becomes the projection-formula map

`Rf_*K ⊗^𝐋_{𝒪_S} A ⟶ Rf_*(K ⊗^𝐋_{𝒪_X} Lf^*A)`

of [Stacks, Tag 08B53] at `A = g_*𝒪_{S'}`.  That last step is supplied here too:
`mateEquiv_tensorTwoSquare_app` says that the abstract projection-formula map
`CategoryTheory.adjunctionTensorMap` of a bifunctor comparison *is* a mate of exactly this
shape, and `pushforward_map_eq_adjunctionTensorMap` carries the identification out, the two
identifications of the endofunctors and their compatibility with the comparison being the data
it takes.

## Main definitions

All in the namespace `Stacks.CategoryTheory.BaseChange`.

* `pullbackComparisonIso` — the comparison `Lg ⋙ Lf' ≅ Lf ⋙ Lg'` of the two composites around
  the square, as an isomorphism; its forward map is
  `Stacks.CategoryTheory.BaseChange.pullbackComparison`.
* `transposedTwoSquare` — the base change morphism `Rg ⋙ Lf ⟶ Lf' ⋙ Rg'` of the *transposed*
  square, the mate of the inverse comparison under `Lg ⊣ Rg` and `Lg' ⊣ Rg'`.
* `pullbackPushforwardSquare` — the comparison `Lf ⋙ (Lg ⋙ Rg) ⟶ (Lg' ⋙ Rg') ⋙ Lf`, the
  horizontal pasting of the comparison of the two composites with the transposed base change
  morphism.
* `projectionTwoSquare` — its mate under `Lf ⊣ Rf`: the projection-formula morphism
  `Rf ⋙ (Lg ⋙ Rg) ⟶ (Lg' ⋙ Rg') ⋙ Rf`.
* `rightCompositeIso` — the conjugate isomorphism `Rg' ⋙ Rf ≅ Rf' ⋙ Rg` of the right adjoints
  of the two composites around the square.
* `tensorTwoSquare` — the comparison of a bifunctor on the source of an adjunction with one on
  its target, read at a fixed second argument as a 2-square.

## Main results

* `projectionTwoSquare_app` and `pushforward_map_eq` — **the coherence**: the projection-formula
  morphism at `K` is `Rg` of the base change map at `K` followed by the conjugate isomorphism,
  and conversely.  Neither carries a hypothesis.
* `isIso_pushforward_map_iff` — the same read as a transfer of invertibility, the conjugate
  isomorphism being invertible.
* `mateEquiv_tensorTwoSquare_app` — the abstract projection-formula map of a bifunctor
  comparison is the mate of that comparison read at a fixed second argument.
* `projectionTwoSquare_app_eq_mateEquiv` and `pushforward_map_eq_mateEquiv` — the coherence
  transported along two identifications of the two endofunctors.
* `pushforward_map_eq_adjunctionTensorMap` — the coherence with the two endofunctors presented
  by a bifunctor: `Rg` of the base change map, transported along the two identifications, is the
  projection-formula map `A(Rf K, H) ⟶ Rf (B(K, Lf H))`.
* `isIso_pushforward_map_of_isIso_adjunctionTensorMap` — and so invertibility of that
  projection-formula map gives invertibility of `Rg` of the base change map.
* `mateEquiv_whiskerTop_whiskerBottom` — taking mates turns whiskering the top and bottom of a
  2-square into whiskering the right and left of its mate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### Mates and whiskering of the top and the bottom of a 2-square -/

section Whisker

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}

/-- **Taking mates commutes with whiskering the horizontal functors of a 2-square.**  The two
functors the mate construction replaces are the vertical ones, so whiskering the top and the
bottom of a square passes to whiskering the right and the left of its mate, with no conjugate
appearing. -/
theorem mateEquiv_whiskerTop_whiskerBottom (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C₁ ⥤ C₃} {H H' : C₂ ⥤ C₄} (w : TwoSquare G L₁ L₂ H) (φ : G' ⟶ G) (ψ : H ⟶ H') :
    mateEquiv adj₁ adj₂ ((w.whiskerTop φ).whiskerBottom ψ) =
      ((mateEquiv adj₁ adj₂ w).whiskerRight φ).whiskerLeft ψ := by
  refine NatTrans.ext (funext fun d => ?_)
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, mateEquiv]

end Whisker

/-! ### The projection-formula map of a bifunctor comparison is a mate -/

section Tensor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- The comparison `α : A ⋙ L ⟶ (L × L) ⋙ B` of a bifunctor on the source of `L` with one on
its target, read at a fixed second argument `H` as a 2-square

`(A(-, H)) ⋙ L ⟶ L ⋙ (B(-, L H))`. -/
def tensorTwoSquare (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) :
    TwoSquare (Prod.sectL C H ⋙ A) L L (Prod.sectL D (L.obj H) ⋙ B) :=
  TwoSquare.mk _ _ _ _
    { app := fun E => α.app (E, H)
      naturality := fun _ _ h => by
        have h' := α.naturality (h ×ₘ 𝟙 H)
        simp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at h'
        exact h' }

/-- The component of `tensorTwoSquare A B α H` at `E` is the component of `α` at `(E, H)`. -/
@[simp]
lemma tensorTwoSquare_natTrans_app (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) (E : C) :
    (tensorTwoSquare A B α H).app E = α.app (E, H) :=
  rfl

/-- **The projection-formula map of an adjunction is a mate.**  The map
`A(R G, H) ⟶ R (B(G, L H))` of `CategoryTheory.adjunctionTensorMap` is the mate, under
`L ⊣ R` on both sides, of the comparison `α` read at the fixed second argument `H`. -/
theorem mateEquiv_tensorTwoSquare_app (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) (G : D) :
    (mateEquiv adj adj (tensorTwoSquare A B α H)).app G =
      CategoryTheory.adjunctionTensorMap adj A B α G H := by
  have key : ∀ u v : A.obj (R.obj G, H) ⟶ R.obj (B.obj (G, L.obj H)),
      L.map u ≫ adj.counit.app (B.obj (G, L.obj H)) =
        L.map v ≫ adj.counit.app (B.obj (G, L.obj H)) → u = v := fun u v h =>
    (adj.homEquiv _ _).symm.injective (by
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]; exact h)
  refine key _ _ ?_
  rw [CategoryTheory.map_adjunctionTensorMap_comp_counit]
  exact mateEquiv_counit adj adj (tensorTwoSquare A B α H) G

end Tensor

/-! ### The coherence -/

section Square

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'}

variable (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- The comparison `Lg ⋙ Lf' ≅ Lf ⋙ Lg'` of the two composites around the square, as an
isomorphism.  Its forward map is `Stacks.CategoryTheory.BaseChange.pullbackComparison`. -/
def pullbackComparisonIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg' := eg ≪≫ ef.symm

/-- The forward map of `pullbackComparisonIso eg ef` is the 2-square `pullbackComparison eg ef`. -/
lemma pullbackComparisonIso_hom :
    (pullbackComparisonIso eg ef).hom = pullbackComparison eg ef := rfl

/-- The base change morphism `Rg ⋙ Lf ⟶ Lf' ⋙ Rg'` of the **transposed** square: the mate,
under `Lg ⊣ Rg` and `Lg' ⊣ Rg'`, of the inverse comparison `Lf ⋙ Lg' ⟶ Lg ⋙ Lf'`. -/
def transposedTwoSquare : TwoSquare Rg Lf' Lf Rg' :=
  mateEquiv adjg adjg' (TwoSquare.mk _ _ _ _ (pullbackComparisonIso eg ef).inv)

/-- The comparison `Lf ⋙ (Lg ⋙ Rg) ⟶ (Lg' ⋙ Rg') ⋙ Lf` of the two endofunctors, obtained by
pasting the comparison of the two composites around the square with the base change morphism of
the transposed square. -/
def pullbackPushforwardSquare : TwoSquare (Lg ⋙ Rg) Lf Lf (Lg' ⋙ Rg') :=
  pullbackComparison eg ef ≫ₕ transposedTwoSquare adjg adjg' eg ef

/-- **The projection-formula morphism** `Rf ⋙ (Lg ⋙ Rg) ⟶ (Lg' ⋙ Rg') ⋙ Rf`: the mate, under
`Lf ⊣ Rf` on both sides, of `pullbackPushforwardSquare`. -/
def projectionTwoSquare : TwoSquare Rf (Lg' ⋙ Rg') (Lg ⋙ Rg) Rf :=
  mateEquiv adjf adjf (pullbackPushforwardSquare adjg adjg' eg ef)

/-- The conjugate isomorphism `Rg' ⋙ Rf ≅ Rf' ⋙ Rg` of the right adjoints of the two composites
around the square. -/
def rightCompositeIso : Rg' ⋙ Rf ≅ Rf' ⋙ Rg :=
  conjugateIsoEquiv (adjf.comp adjg') (adjg.comp adjf') (pullbackComparisonIso eg ef)

/-- The inverse of `rightCompositeIso` is the conjugate of the inverse of
`pullbackComparisonIso`. -/
lemma rightCompositeIso_inv :
    (rightCompositeIso adjf adjf' adjg adjg' eg ef).inv =
      conjugateEquiv (adjg.comp adjf') (adjf.comp adjg') (pullbackComparisonIso eg ef).inv :=
  rfl

/-- The mate, under `Lf' ⊣ Rf'` and `Lf ⊣ Rf`, of the transposed base change morphism is the
inverse of the conjugate isomorphism of the right adjoints of the two composites around the
square. -/
theorem mateEquiv_transposedTwoSquare :
    mateEquiv adjf' adjf (transposedTwoSquare adjg adjg' eg ef) =
      (rightCompositeIso adjf adjf' adjg adjg' eg ef).inv := by
  rw [rightCompositeIso_inv, transposedTwoSquare]
  exact iterated_mateEquiv_conjugateEquiv adjg adjg' adjf adjf'
    (TwoSquare.mk _ _ _ _ (pullbackComparisonIso eg ef).inv)

/-- **The coherence.**  The projection-formula morphism at `K` is `Rg` applied to the base change
map at `K`, followed by the conjugate isomorphism of the two iterated right adjoints. -/
theorem projectionTwoSquare_app (K : B) :
    (projectionTwoSquare adjf adjg adjg' eg ef).app K =
      Rg.map (map adjf adjf' eg ef K) ≫
        (rightCompositeIso adjf adjf' adjg adjg' eg ef).inv.app (Lg'.obj K) := by
  rw [projectionTwoSquare, pullbackPushforwardSquare,
    mateEquiv_vcomp adjf adjf' adjf (pullbackComparison eg ef)
      (transposedTwoSquare adjg adjg' eg ef),
    ← mateEquiv_transposedTwoSquare adjf adjf' adjg adjg' eg ef]
  simp [TwoSquare.vComp, map, twoSquare]

/-- **The coherence, solved for the pushed-forward base change map.**  `Rg` applied to the base
change map at `K` is the projection-formula morphism at `K` followed by the conjugate
isomorphism of the two iterated right adjoints. -/
theorem pushforward_map_eq (K : B) :
    Rg.map (map adjf adjf' eg ef K) =
      (projectionTwoSquare adjf adjg adjg' eg ef).app K ≫
        (rightCompositeIso adjf adjf' adjg adjg' eg ef).hom.app (Lg'.obj K) := by
  rw [projectionTwoSquare_app, Category.assoc,
    ← NatTrans.comp_app, (rightCompositeIso adjf adjf' adjg adjg' eg ef).inv_hom_id]
  simp

/-- **Invertibility transfers.**  `Rg` applied to the base change map at `K` is invertible exactly
when the projection-formula morphism is invertible at `K`: the two differ by the conjugate
isomorphism of the two iterated right adjoints. -/
theorem isIso_pushforward_map_iff (K : B) :
    IsIso (Rg.map (map adjf adjf' eg ef K)) ↔
      IsIso ((projectionTwoSquare adjf adjg adjg' eg ef).app K) := by
  have : IsIso ((rightCompositeIso adjf adjf' adjg adjg' eg ef).hom.app (Lg'.obj K)) :=
    inferInstanceAs
      (IsIso ((rightCompositeIso adjf adjf' adjg adjg' eg ef).app (Lg'.obj K)).hom)
  rw [pushforward_map_eq adjf adjf' adjg adjg' eg ef K, isIso_comp_right_iff]

end Square

/-! ### The coherence transported along two identifications of the endofunctors -/

section Transport

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'}
  {M : A ⥤ A} {M' : B ⥤ B}

variable (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (ι : Lg ⋙ Rg ≅ M) (ι' : Lg' ⋙ Rg' ≅ M') (ν : TwoSquare M Lf Lf M')

/-- **The projection-formula morphism, transported along two identifications of the two
endofunctors.**  Suppose `Lg ⋙ Rg` and `Lg' ⋙ Rg'` are identified by `ι` and `ι'` with
endofunctors `M` and `M'`, and that under those identifications the canonical comparison
`pullbackPushforwardSquare` becomes a given comparison `ν : M ⋙ Lf ⟶ Lf ⋙ M'`.  Then the
projection-formula morphism at `K` is the mate of `ν` at `K`, conjugated by `ι` and `ι'`. -/
theorem projectionTwoSquare_app_eq_mateEquiv
    (hcompat : pullbackPushforwardSquare adjg adjg' eg ef =
      ((ν.whiskerTop ι.hom).whiskerBottom ι'.inv))
    (K : B) :
    (projectionTwoSquare adjf adjg adjg' eg ef).app K =
      ι.hom.app (Rf.obj K) ≫ (mateEquiv adjf adjf ν).app K ≫
        Rf.map (ι'.inv.app K) := by
  rw [projectionTwoSquare, hcompat,
    mateEquiv_whiskerTop_whiskerBottom adjf adjf ν ι.hom ι'.inv]
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

/-- **The coherence, transported.**  `Rg` applied to the base change map at `K` is the mate of
the transported comparison `ν` at `K`, conjugated by `ι`, by `ι'` and by the conjugate
isomorphism of the two iterated right adjoints. -/
theorem pushforward_map_eq_mateEquiv
    (hcompat : pullbackPushforwardSquare adjg adjg' eg ef =
      ((ν.whiskerTop ι.hom).whiskerBottom ι'.inv))
    (K : B) :
    Rg.map (map adjf adjf' eg ef K) =
      ι.hom.app (Rf.obj K) ≫ (mateEquiv adjf adjf ν).app K ≫
        Rf.map (ι'.inv.app K) ≫
          (rightCompositeIso adjf adjf' adjg adjg' eg ef).hom.app (Lg'.obj K) := by
  rw [pushforward_map_eq adjf adjf' adjg adjg' eg ef K,
    projectionTwoSquare_app_eq_mateEquiv adjf adjg adjg' eg ef ι ι' ν hcompat K,
    Category.assoc, Category.assoc]

end Transport

/-! ### The coherence with the two endofunctors presented as tensor products -/

section TensorSquare

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'}

variable (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TA : A × A ⥤ A) (TB : B × B ⥤ B) (α : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (H : A)
  (ι : Lg ⋙ Rg ≅ Prod.sectL A H ⋙ TA)
  (ι' : Lg' ⋙ Rg' ≅ Prod.sectL B (Lf.obj H) ⋙ TB)

/-- **The coherence, with the two endofunctors presented as tensor products.**  Suppose the two
endofunctors `Lg ⋙ Rg` and `Lg' ⋙ Rg'` are identified by `ι` and `ι'` with tensoring by `H`
downstairs and by `Lf H` upstairs, compatibly with the canonical comparison
`pullbackPushforwardSquare`.  Then `Rg` applied to the base change map at `K`, transported along
those two identifications and along the conjugate isomorphism of the right adjoints, is the
projection-formula map

`TA (Rf K, H) ⟶ Rf (TB (K, Lf H))`

of `CategoryTheory.adjunctionTensorMap`. -/
theorem pushforward_map_eq_adjunctionTensorMap
    (hcompat : pullbackPushforwardSquare adjg adjg' eg ef =
      (((tensorTwoSquare TA TB α H).whiskerTop ι.hom).whiskerBottom ι'.inv))
    (K : B) :
    Rg.map (map adjf adjf' eg ef K) =
      ι.hom.app (Rf.obj K) ≫ CategoryTheory.adjunctionTensorMap adjf TA TB α K H ≫
        Rf.map (ι'.inv.app K) ≫
          (rightCompositeIso adjf adjf' adjg adjg' eg ef).hom.app (Lg'.obj K) := by
  rw [pushforward_map_eq_mateEquiv adjf adjf' adjg adjg' eg ef ι ι'
      (tensorTwoSquare TA TB α H) hcompat K,
    mateEquiv_tensorTwoSquare_app adjf TA TB α H K]
  rfl

/-- **Invertibility of the projection-formula map gives invertibility of the pushed-forward base
change map.** -/
theorem isIso_pushforward_map_of_isIso_adjunctionTensorMap
    (hcompat : pullbackPushforwardSquare adjg adjg' eg ef =
      (((tensorTwoSquare TA TB α H).whiskerTop ι.hom).whiskerBottom ι'.inv))
    (K : B) (h : IsIso (CategoryTheory.adjunctionTensorMap adjf TA TB α K H)) :
    IsIso (Rg.map (map adjf adjf' eg ef K)) := by
  have h₁ : IsIso (ι.hom.app (Rf.obj K)) := inferInstanceAs (IsIso (ι.app (Rf.obj K)).hom)
  have h₂ : IsIso (Rf.map (ι'.inv.app K)) :=
    inferInstanceAs (IsIso (Rf.mapIso (ι'.app K).symm).hom)
  have h₃ : IsIso ((rightCompositeIso adjf adjf' adjg adjg' eg ef).hom.app (Lg'.obj K)) :=
    inferInstanceAs
      (IsIso ((rightCompositeIso adjf adjf' adjg adjg' eg ef).app (Lg'.obj K)).hom)
  rw [pushforward_map_eq_adjunctionTensorMap adjf adjf' adjg adjg' eg ef TA TB α H ι ι'
    hcompat K]
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h (IsIso.comp_isIso' h₂ h₃))

end TensorSquare

end Stacks.CategoryTheory.BaseChange

end
