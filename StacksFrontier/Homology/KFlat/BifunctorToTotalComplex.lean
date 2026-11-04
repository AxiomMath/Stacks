module

public import StacksFrontier.Homology.KFlat.BifunctorOneSided

/-!
# The canonical map from a derived bifunctor to the total complex

For an additive bifunctor `F : A ⥤ B ⥤ D` whose derived descent
`CochainComplex.KFlatBifunctor.derivedBifunctor` exists, the one-sided comparison
`CochainComplex.KFlatBifunctor.comparisonRight` identifies the descent at `(K, L)` with the
total complex `Tot(F(K, L))` as soon as `L` is K-flat, with no hypothesis on `K`. For an
arbitrary `L` the two objects are no longer isomorphic, but there is still a canonical
morphism from the descent to the total complex, induced by any K-flat resolution of `L`.

## Main definitions

* `CochainComplex.KFlatBifunctor.toTensorAux`: `comparisonRight` at a K-flat `N` followed by
  the total complex of a morphism `N ⟶ L`.
* `CochainComplex.KFlatBifunctor.toTensorOfRes`: the canonical morphism computed from one
  K-flat resolution of `L`.
* `CochainComplex.KFlatBifunctor.toTensor`: the canonical morphism, at a chosen resolution.

## Main results

* `CochainComplex.KFlatBifunctor.toTensor_spec`: **the characterization.** For *every* K-flat
  `N` and *every* morphism `s : N ⟶ L` — not merely for resolutions — the descent of `s`
  followed by `toTensor` is `toTensorAux`. This both pins the value of `toTensor` down
  (so it is not an uncharacterized choice) and is the only input the two results below need.
* `CochainComplex.KFlatBifunctor.toTensor_eq_comparisonRight`: for a K-flat `L` the canonical
  morphism *is* the one-sided comparison isomorphism.
* `CochainComplex.KFlatBifunctor.toTensor_naturality`: the canonical morphism is natural in
  both variables, with no K-flatness hypothesis anywhere.

## Implementation notes

The canonical morphism cannot be obtained from a universal property of either localization:
its source inverts quasi-isomorphisms of the second variable and its target does not, so
there is no functor on `D(B)` for the universal property to apply to. It is therefore built
from a resolution, and the whole content of the construction is that the value does not
depend on which resolution is used — which, by `toTensor_spec`, is the same statement as the
existence of the natural transformation.

Independence is a *refinement* statement: two morphisms to a common target `L`, one of them
a quasi-isomorphism, are refined by a single K-flat complex mapping to both. The refinement
is the Ore square of the **right** calculus of fractions for the quasi-isomorphisms of
`K(B)` (`quasiIso_hasRightCalculusOfFractions`, the mirror of the left calculus that
`Tag06YUPieces` already uses), followed by a K-flat resolution of the apex. Two consequences
are worth recording:

* The square it produces commutes only **up to homotopy**, since it lives in `K(B)`. That is
  exactly enough: `Tot(F(K, -))` sends homotopic morphisms to homotopic ones
  (`HomologicalComplex.mapBifunctorMapHomotopy₂`) and `DerivedCategory.Q` identifies those
  (`Q_map_eq_of_homotopy`). A square commuting in `D(B)` would *not* be enough, for the same
  reason the universal property does not apply.
* No surjectivity is needed. The fibre-product refinement, which would use the termwise
  epimorphism clause of a K-flat resolution, needs in addition that the kernel of a
  surjective quasi-isomorphism is acyclic and that this is inherited by the pullback; the Ore
  square replaces all of that with one instance.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex.KFlatBifunctor

/-! ### The derived category identifies homotopic morphisms -/

section Homotopy

variable {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]

/-- Morphisms of cochain complexes with the same image in the homotopy category have the
same image in the derived category: having the same image there *is* being homotopic, and
`DerivedCategory.Q` is homotopy-invariant. -/
theorem Q_map_eq_of_quotient_map_eq {X Y : CochainComplex E ℤ} {f g : X ⟶ Y}
    (hq : (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map f =
      (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  DerivedCategory.Q_map_eq_of_homotopy _ (HomotopyCategory.homotopyOfEq _ _ hq)

omit [HasDerivedCategory E] in
/-- The quasi-isomorphisms of `K(E)` admit a **right** calculus of fractions: they are the
`trW` of the acyclic objects, which is a triangulated subcategory. This is the mirror of the
left calculus of fractions, and it is what supplies the Ore square below. -/
theorem quasiIso_hasRightCalculusOfFractions :
    (HomotopyCategory.quasiIso E (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

end Homotopy

section

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-! ### The refinement of two morphisms to a common target -/

/-- **The Ore refinement.** Given `s : N ⟶ L` and a quasi-isomorphism `q : N₀ ⟶ L`, there is a
K-flat complex `M` with a quasi-isomorphism `m₁ : M ⟶ N` and a morphism `m₂ : M ⟶ N₀` making
the square commute up to homotopy. The square is the Ore square of the right calculus of
fractions in `K(B)`, and `M` is a K-flat resolution of its apex. -/
theorem exists_kFlat_refinement
    (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
      KFlat F P ∧ QuasiIso f)
    {N N₀ L : CochainComplex B ℤ} (s : N ⟶ L) (q : N₀ ⟶ L) (hq : QuasiIso q) :
    ∃ (M : CochainComplex B ℤ) (m₁ : M ⟶ N) (m₂ : M ⟶ N₀),
      KFlat F M ∧ QuasiIso m₁ ∧
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (m₁ ≫ s) =
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (m₂ ≫ q) := by
  let _ := quasiIso_hasRightCalculusOfFractions (E := B)
  obtain ⟨ψ, hsq⟩ :=
    MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
      (W := HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      (X := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)
      (Y := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N₀)
      { f := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s
        s := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map q
        hs := (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq }
  obtain ⟨w₀, hw₀⟩ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_surjective
    (X := ψ.X'.as) (Y := N) ψ.s
  obtain ⟨t₀, ht₀⟩ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_surjective
    (X := ψ.X'.as) (Y := N₀) ψ.f
  obtain ⟨M, r, hM, hr⟩ := hres ψ.X'.as
  have : QuasiIso w₀ := (HomotopyCategory.quotient_map_mem_quasiIso_iff w₀).1 (hw₀ ▸ ψ.hs)
  refine ⟨M, r ≫ w₀, r ≫ t₀, hM, inferInstance, ?_⟩
  simp only [Functor.map_comp, Category.assoc, hw₀, ht₀]
  exact congrArg _ hsq

/-! ### The canonical morphism -/

/-- The two spellings of the total complex of `(f, g)` agree after applying `Q`. -/
private theorem Q_map_map₂_comp_eq_mapBifunctorMap [HasDerivedCategory D]
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L') :
    DerivedCategory.Q.map
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L ≫
          ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K').map g) =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g F (ComplexShape.up ℤ)) :=
  (DerivedCategory.Q.map_comp _ _).trans (Q_map_mapBifunctorMap_merge F f g)

section ToTensor

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- `comparisonRight_naturality` with the two one-variable total complexes merged into the
two-variable one, which is the spelling the ringed-site statement of Tag 06YU uses. The merge
is `Q_map_mapBifunctorMap_merge`, applied in term mode: the two spellings of the total
complex differ by the unfolding of `Functor.map₂HomologicalComplex`, which a rewrite cannot
see through. -/
theorem comparisonRight_naturality_merged
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L')
    (hL : KFlat F L) (hL' : KFlat F L') :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        (comparisonRight F K' L' hL').hom =
      (comparisonRight F K L hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g F (ComplexShape.up ℤ)) :=
  (comparisonRight_naturality F f g hL hL').trans
    (congrArg (fun t ↦ (comparisonRight F K L hL).hom ≫ t)
      (Q_map_map₂_comp_eq_mapBifunctorMap F f g))

/-- The one-sided comparison at a K-flat `N`, followed by the total complex of `s : N ⟶ L`. -/
def toTensorAux (K : CochainComplex A ℤ) {N L : CochainComplex B ℤ} (hN : KFlat F N)
    (s : N ⟶ L) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj N) ⟶
      DerivedCategory.Q.obj (totalComplex F K L) :=
  (comparisonRight F K N hN).hom ≫
    DerivedCategory.Q.map
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).map s)

/-- `toTensorAux` absorbs a morphism of K-flat complexes: this is naturality of
`comparisonRight` in its K-flat variable. -/
theorem toTensorAux_comp (K : CochainComplex A ℤ) {M N L : CochainComplex B ℤ}
    (hM : KFlat F M) (hN : KFlat F N) (t : M ⟶ N) (s : N ⟶ L) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map t) ≫
        toTensorAux F K hN s =
      toTensorAux F K hM (t ≫ s) := by
  rw [toTensorAux, toTensorAux, ← Category.assoc,
    comparisonRight_naturality_right F K t hM hN, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp]

/-- `toTensorAux` depends on `s` only through its homotopy class, because `Tot(F(K, -))`
sends homotopic morphisms to homotopic ones and `DerivedCategory.Q` identifies those. -/
theorem toTensorAux_congr (K : CochainComplex A ℤ) {M L : CochainComplex B ℤ}
    (hM : KFlat F M) {σ σ' : M ⟶ L}
    (h : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map σ =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map σ') :
    toTensorAux F K hM σ = toTensorAux F K hM σ' := by
  have h' : Homotopy (HomologicalComplex.mapBifunctorMap (𝟙 K) σ F (ComplexShape.up ℤ))
      (HomologicalComplex.mapBifunctorMap (𝟙 K) σ' F (ComplexShape.up ℤ)) :=
    HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K)
      (HomotopyCategory.homotopyOfEq _ _ h) F (ComplexShape.up ℤ)
  exact congrArg (fun u ↦ (comparisonRight F K M hM).hom ≫ u)
    (Q_map_eq_of_quotient_map_eq (HomotopyCategory.eq_of_homotopy _ _ h'))

/-- The derived bifunctor turns a quasi-isomorphism of the second variable into an
isomorphism — for an arbitrary first variable, since the quasi-isomorphism has already become
invertible in `D(B)`. -/
theorem isIso_derivedBifunctor_map_Q_map (K : CochainComplex A ℤ)
    {X Y : CochainComplex B ℤ} (g : X ⟶ Y) (hg : QuasiIso g) :
    IsIso (((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
      (DerivedCategory.Q.map g)) := by
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  infer_instance

/-- The canonical morphism to the total complex computed from one K-flat resolution
`q : N ⟶ L`. -/
def toTensorOfRes (K : CochainComplex A ℤ) {N L : CochainComplex B ℤ} (hN : KFlat F N)
    (q : N ⟶ L) (hq : QuasiIso q) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj (totalComplex F K L) :=
  letI := isIso_derivedBifunctor_map_Q_map F K q hq
  inv (((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map q)) ≫
    toTensorAux F K hN q

/-- **The characterization of the canonical morphism**, and with it the independence of the
chosen resolution: for *every* K-flat `N` and *every* `s : N ⟶ L` the descent of `s` followed
by `toTensorOfRes` is `toTensorAux`. The proof refines `s` and `q` by one K-flat complex. -/
theorem toTensorOfRes_spec
    (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
      KFlat F P ∧ QuasiIso f)
    (K : CochainComplex A ℤ) {N₀ L : CochainComplex B ℤ} (hN₀ : KFlat F N₀)
    (q : N₀ ⟶ L) (hq : QuasiIso q) {N : CochainComplex B ℤ} (hN : KFlat F N) (s : N ⟶ L) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map s) ≫
        toTensorOfRes F K hN₀ q hq = toTensorAux F K hN s := by
  obtain ⟨M, m₁, m₂, hM, hm₁, hh⟩ := exists_kFlat_refinement F hres s q hq
  have _ := isIso_derivedBifunctor_map_Q_map F K m₁ hm₁
  have _ := isIso_derivedBifunctor_map_Q_map F K q hq
  rw [← cancel_epi (((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
    (DerivedCategory.Q.map m₁))]
  calc ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map m₁) ≫
          ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
            (DerivedCategory.Q.map s) ≫ toTensorOfRes F K hN₀ q hq
      = ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
            (DerivedCategory.Q.map (m₂ ≫ q)) ≫ toTensorOfRes F K hN₀ q hq := by
        rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
          Q_map_eq_of_quotient_map_eq hh]
    _ = ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map m₂) ≫ toTensorAux F K hN₀ q := by
        rw [Functor.map_comp, Functor.map_comp, toTensorOfRes, Category.assoc,
          ← Category.assoc (((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
            (DerivedCategory.Q.map q)), IsIso.hom_inv_id, Category.id_comp]
    _ = toTensorAux F K hM (m₂ ≫ q) := toTensorAux_comp F K hM hN₀ m₂ q
    _ = toTensorAux F K hM (m₁ ≫ s) := (toTensorAux_congr F K hM hh).symm
    _ = ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map m₁) ≫ toTensorAux F K hN s :=
        (toTensorAux_comp F K hM hN m₁ s).symm

variable (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
  KFlat F P ∧ QuasiIso f)

/-- A chosen K-flat resolution of `L`. -/
def chosenRes (L : CochainComplex B ℤ) : CochainComplex B ℤ := (hres L).choose

/-- Its augmentation. -/
def chosenResMap (L : CochainComplex B ℤ) : chosenRes F hres L ⟶ L :=
  (hres L).choose_spec.choose

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- The chosen resolution `chosenRes F hres L` is K-flat. -/
theorem kFlat_chosenRes (L : CochainComplex B ℤ) : KFlat F (chosenRes F hres L) :=
  (hres L).choose_spec.choose_spec.1

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- The augmentation `chosenResMap F hres L : chosenRes F hres L ⟶ L` is a quasi-isomorphism. -/
theorem quasiIso_chosenResMap (L : CochainComplex B ℤ) :
    QuasiIso (chosenResMap F hres L) := (hres L).choose_spec.choose_spec.2

/-- The descent of the augmentation of the chosen resolution is an isomorphism. -/
private theorem isIso_derivedBifunctor_map_chosenResMap (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) :
    IsIso (((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
      (DerivedCategory.Q.map (chosenResMap F hres L))) :=
  isIso_derivedBifunctor_map_Q_map F K _ (quasiIso_chosenResMap F hres L)

/-- **The canonical morphism from the derived bifunctor to the total complex**, for arbitrary
complexes. It is `toTensor` of the ringed-site statement of Tag 06YU. -/
def toTensor (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj (totalComplex F K L) :=
  toTensorOfRes F K (kFlat_chosenRes F hres L) (chosenResMap F hres L)
    (quasiIso_chosenResMap F hres L)

/-- **The characterization of `toTensor`**: the descent of any morphism from a K-flat complex
to `L`, followed by `toTensor`, is `toTensorAux`. Everything below is a consequence. -/
theorem toTensor_spec (K : CochainComplex A ℤ) {N L : CochainComplex B ℤ}
    (hN : KFlat F N) (s : N ⟶ L) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map s) ≫
        toTensor F hres K L = toTensorAux F K hN s :=
  toTensorOfRes_spec F hres K _ _ _ hN s

/-- **A left K-flat left factor makes the canonical morphism invertible.** By `toTensor_spec`
at a resolution `q` of `L` the morphism is conjugate to `Tot(F(K, q))`, and for a left K-flat
`K` that is a quasi-isomorphism by `quasiIso_of_kFlatLeft` — so this needs no second
descent. It is what makes the left one-sided comparison of Tag 06YU available as
`asIso toTensor`, with its naturality and its agreement with the right comparison then free
rather than a second pair of theorems. -/
theorem isIso_toTensor_of_kFlatLeft {K : CochainComplex A ℤ} (hK : KFlatLeft F K)
    (L : CochainComplex B ℤ) : IsIso (toTensor F hres K L) := by
  have hq := quasiIso_chosenResMap F hres L
  have hN := kFlat_chosenRes F hres L
  have _ := isIso_derivedBifunctor_map_chosenResMap F hres K L
  have _ : IsIso (toTensorAux F K hN (chosenResMap F hres L)) := by
    have _ : IsIso (DerivedCategory.Q.map
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).map (chosenResMap F hres L))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_of_kFlatLeft F K hK _ hq)
    rw [toTensorAux]
    infer_instance
  exact IsIso.of_isIso_fac_left (toTensor_spec F hres K hN (chosenResMap F hres L))

/-- **For a K-flat right factor the canonical morphism is the one-sided comparison
isomorphism.** This is `toTensor_spec` at the identity of `L`. -/
theorem toTensor_eq_comparisonRight (K : CochainComplex A ℤ) {L : CochainComplex B ℤ}
    (hL : KFlat F L) :
    toTensor F hres K L = (comparisonRight F K L hL).hom := by
  have h := toTensor_spec F hres K hL (𝟙 L)
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    toTensorAux, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at h

/-- **The canonical morphism is natural in both variables**, in the two-one-variable spelling
of `comparisonRight_naturality`. Naturality in the second variable is not a square between
resolutions — there is no morphism of resolutions over an arbitrary `g` — but a consequence
of `toTensor_spec`, which applies to the composite of a resolution of `L` with `g`, a
morphism that is not a quasi-isomorphism. -/
theorem toTensor_naturality'
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        toTensor F hres K' L' =
      toTensor F hres K L ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).map f).app L ≫
            ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).obj K').map g) := by
  have hN := kFlat_chosenRes F hres L
  have _ := isIso_derivedBifunctor_map_chosenResMap F hres K L
  have hbif : ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).map f).app (chosenRes F hres L) ≫
        ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K').map (chosenResMap F hres L ≫ g) =
      ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K).map (chosenResMap F hres L) ≫
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L ≫
          ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K').map g) := by
    rw [reassoc_of% (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).map f).naturality (chosenResMap F hres L)), ← Functor.map_comp]
  refine (cancel_epi (((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
    (DerivedCategory.Q.map (chosenResMap F hres L)))).1 ?_
  rw [reassoc_of% (((derivedBifunctor F).map (DerivedCategory.Q.map f)).naturality
      (DerivedCategory.Q.map (chosenResMap F hres L))), ← Functor.map_comp_assoc,
    ← Functor.map_comp,
    toTensor_spec F hres K' hN (chosenResMap F hres L ≫ g),
    reassoc_of% (toTensor_spec F hres K hN (chosenResMap F hres L)), toTensorAux, toTensorAux,
    reassoc_of% (comparisonRight_naturality_left F f (chosenRes F hres L) hN),
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun t ↦ (comparisonRight F K (chosenRes F hres L) hN).hom ≫
    DerivedCategory.Q.map t) hbif

/-- **The canonical morphism is natural in both variables**, with the two one-variable total
complexes merged into the two-variable one. This is `toTensor_naturality` of the ringed-site
statement of Tag 06YU; the merge is `Q_map_mapBifunctorMap_merge`. -/
theorem toTensor_naturality
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        toTensor F hres K' L' =
      toTensor F hres K L ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g F (ComplexShape.up ℤ)) :=
  (toTensor_naturality' F hres f g).trans
    (congrArg (fun t ↦ toTensor F hres K L ≫ t)
      (Q_map_map₂_comp_eq_mapBifunctorMap F f g))

end ToTensor

end

end CochainComplex.KFlatBifunctor

end

end
