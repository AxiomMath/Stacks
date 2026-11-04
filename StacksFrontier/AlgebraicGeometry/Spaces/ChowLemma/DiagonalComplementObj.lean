module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FibrePowerSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.RepresentableFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# The complement of the diagonals as an object of the big fppf site

Let `X` be an algebraic space over `S` and `U` an object of the spaces-étale site of `X` whose
underlying algebraic space is representable. A nonempty finite self-product `U ×_X ⋯ ×_X U`, and
the complement `AlgebraicGeometry.Space.SpacesEtale.diagonalComplement` of all its diagonals,
are then representable. For an étale chart `W ⟶ X` from a representable presheaf, this makes the
complement `V` of the diagonals in `W ×_X ⋯ ×_X W` an object of `AlgebraicGeometry.BigFppfOver`,
with projections `V ⟶ W` and a morphism into a finite fibre power over the base.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.underlyingSelfProdOneIso`: the one-fold self-product is
  the chart.
* `AlgebraicGeometry.Space.SpacesEtale.chartObj`: an étale morphism from a representable
  presheaf, read as an object of the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementProj`: the `i`-th projection `V ⟶ W`
  of the complement of the diagonals, as a morphism of the big fppf category over `S`, given a
  site object `V` and an identification of the presheaf it represents with the complement of the
  diagonals.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementToOverProdObj`: the morphism
  `V ⟶ Y ×_S ⋯ ×_S Y` into the finite fibre power over the base, given a family of morphisms
  from the chart into the factors.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isRepresentable_underlying_selfProd_succ`: a nonempty
  finite self-product of a representable object of the spaces-étale site of `X` is
  representable.
* `AlgebraicGeometry.Space.SpacesEtale.isRepresentable_underlying_diagonalComplement`: so is
  the complement of its diagonals.
* `AlgebraicGeometry.Space.SpacesEtale.exists_siteObj_iso_underlying_diagonalComplement`: the
  complement of the diagonals is an object of the big fppf category over `S`.
* `AlgebraicGeometry.Space.SpacesEtale.exists_diagonalComplementObj`: the same, together with
  the `n + 1` projections to the chart, the morphism into the finite fibre power over the base,
  and quasi-compactness of the underlying scheme.
* `AlgebraicGeometry.Space.SpacesEtale.yoneda_map_diagonalComplementProj_comp_chart`: all the
  projections of the complement of the diagonals agree after composition with the chart.
* `AlgebraicGeometry.Space.SpacesEtale.isOpenImmersion_diagonalComplementObjι`: the inclusion
  of the complement of the diagonals into the self-product is an open immersion out of the
  presheaf represented by `V`.
* `AlgebraicGeometry.Space.SpacesEtale.compactSpace_of_iso_underlying_diagonalComplement`: the
  underlying scheme of `V` is quasi-compact.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Representability of the self-product and of the complement of its diagonals -/

/-- The one-fold self-product of an object of the spaces-étale site of `X` is that object. -/
def underlyingSelfProdOneIso (U : SpacesEtale B S hS X) :
    underlying B S hS X (selfProd B S hS X U 1) ≅ underlying B S hS X U :=
  (toSpaces B S hS X).mapIso (productUniqueIso fun _ : Fin 1 => U)

/-- A nonempty finite self-product of a representable object of the spaces-étale site of `X`
is representable. -/
theorem isRepresentable_underlying_selfProd_succ (U : SpacesEtale B S hS X)
    (hU : (underlying B S hS X U).obj.IsRepresentable) :
    ∀ n : ℕ, (underlying B S hS X (selfProd B S hS X U (n + 1))).obj.IsRepresentable
  | 0 =>
      isRepresentable_of_iso B S hS hU
        ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
          (underlyingSelfProdOneIso B S hS X U).symm)
  | n + 1 =>
      isRepresentable_of_iso B S hS
        (isRepresentable_pullback_algebraicSpaces B S hS hU
          (isRepresentable_underlying_selfProd_succ U hU n) _ _)
        ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
          (underlyingSelfProdSuccIso B S hS X U (n + 1))).symm

/-- The complement of the diagonals in a nonempty finite self-product of a representable
object of the spaces-étale site of `X` is representable. -/
theorem isRepresentable_underlying_diagonalComplement (U : SpacesEtale B S hS X)
    (hU : (underlying B S hS X U).obj.IsRepresentable) (n : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom) :
    (underlying B S hS X (diagonalComplement B S hS X U (n + 1) hsep)).obj.IsRepresentable :=
  isRepresentable_of_isOpenSubspace B S hS
    (isRepresentable_underlying_selfProd_succ B S hS X U hU n)
    (diagonalComplementSubspace B S hS X U (n + 1) hsep).1
    (diagonalComplementSubspace B S hS X U (n + 1) hsep).2

/-- The complement of the diagonals in a nonempty finite self-product of a representable
object of the spaces-étale site of `X` is represented by an object of the big fppf category
over `S`. -/
theorem exists_siteObj_iso_underlying_diagonalComplement (U : SpacesEtale B S hS X)
    (hU : (underlying B S hS X U).obj.IsRepresentable) (n : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom) :
    ∃ V : BigFppfOver B S hS, Nonempty (yoneda.obj V ≅
      (underlying B S hS X (diagonalComplement B S hS X U (n + 1) hsep)).obj) := by
  obtain ⟨V, ⟨r⟩⟩ :=
    (isRepresentable_underlying_diagonalComplement B S hS X U hU n hsep).has_representation
  exact ⟨V, ⟨r.toIso⟩⟩

/-! ### The projections of the complement of the diagonals -/

/-- The composite `U^n ∖ (diagonals) ⟶ U^n ⟶ U` picking out the factor of index `i`, as a
morphism of the spaces-étale site of `X`. -/
def diagonalComplementπ (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom) (i : Fin n) :
    diagonalComplement B S hS X U n hsep ⟶ U :=
  diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i

/-- Each projection of the complement of the diagonals is a morphism over `X`: its composite
with the structure morphism of `U` is the structure morphism of the complement. -/
theorem hom_toSpaces_map_diagonalComplementπ_comp (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom) (i : Fin n) :
    ((toSpaces B S hS X).map (diagonalComplementπ B S hS X U n hsep i)).hom ≫
        U.obj.hom.hom =
      (diagonalComplement B S hS X U n hsep).obj.hom.hom :=
  hom_toSpaces_map_comp_structure B S hS X (diagonalComplementπ B S hS X U n hsep i)

/-! ### The chart as an object of the spaces-étale site -/

/-- An étale morphism from a representable presheaf, read as an object of the spaces-étale
site of `X`. -/
def chartObj (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c) :
    SpacesEtale B S hS X :=
  ⟨Over.mk (ObjectProperty.homMk (P := algebraicSpaceProperty B S hS)
      (X := (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
      (Y := X) c), hc⟩

/-- The algebraic space underlying the chart object is the presheaf represented by the chart. -/
theorem chartObj_underlying (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj)
    (hc : IsEtale B S hS c) :
    (underlying B S hS X (chartObj B S hS X W c hc)).obj = yoneda.obj W :=
  rfl

/-- The structure morphism of the chart object is the given étale morphism. -/
theorem chartObj_hom (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj)
    (hc : IsEtale B S hS c) :
    (chartObj B S hS X W c hc).obj.hom.hom = c :=
  rfl

section Projections

variable (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep)).obj)

/-- The `i`-th projection `V ⟶ W` of the complement of the diagonals, as a morphism of the big
fppf category over `S`. Here `V` is an object of the site presented with an identification `e`
of the presheaf it represents with the complement of the diagonals in the `n`-fold self-product
of the chart over `X`; the morphism is the `i`-th projection of that self-product, read through
`e` and the full faithfulness of the Yoneda embedding. -/
def diagonalComplementProj (i : Fin n) : V ⟶ W :=
  yoneda.preimage ((e.hom ≫ ((toSpaces B S hS X).map
      (diagonalComplementπ B S hS X (chartObj B S hS X W c hc) n hsep i)).hom :
    yoneda.obj V ⟶ yoneda.obj W))

/-- The presheaf morphism underlying the `i`-th projection is the `i`-th projection of the
self-product read through `e`. -/
theorem yoneda_map_diagonalComplementProj (i : Fin n) :
    yoneda.map (diagonalComplementProj B S hS X W c hc hsep n V e i) =
      ((e.hom ≫ ((toSpaces B S hS X).map
          (diagonalComplementπ B S hS X (chartObj B S hS X W c hc) n hsep i)).hom :
        yoneda.obj V ⟶ yoneda.obj W)) :=
  yoneda.map_preimage _

/-- The composite of each projection of the complement of the diagonals with the chart is `e`
followed by the structure morphism of the complement of the diagonals. -/
theorem yoneda_map_diagonalComplementProj_comp_chart (i : Fin n) :
    yoneda.map (diagonalComplementProj B S hS X W c hc hsep n V e i) ≫ c =
      e.hom ≫ (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep).obj.hom.hom := by
  rw [yoneda_map_diagonalComplementProj]
  exact (Category.assoc _ _ _).trans (congrArg (fun k => e.hom ≫ k)
    (hom_toSpaces_map_diagonalComplementπ_comp B S hS X
      (chartObj B S hS X W c hc) n hsep i))

/-- The `n` projections of the complement of the diagonals agree over `X`. -/
theorem yoneda_map_diagonalComplementProj_comp_chart_eq (i i' : Fin n) :
    yoneda.map (diagonalComplementProj B S hS X W c hc hsep n V e i) ≫ c =
      yoneda.map (diagonalComplementProj B S hS X W c hc hsep n V e i') ≫ c := by
  rw [yoneda_map_diagonalComplementProj_comp_chart,
    yoneda_map_diagonalComplementProj_comp_chart]

/-- The morphism from `V` into the finite fibre power `AlgebraicGeometry.Space.overProdObj`
over the base whose `i`-th component is the `i`-th projection followed by `j i`, given a family
of morphisms `j` of the site from the chart into the factors. -/
def diagonalComplementToOverProdObj (Y : Fin n → BigFppfOver B S hS) (j : ∀ i, W ⟶ Y i) :
    V ⟶ overProdObj B S hS Y :=
  overProdObjLift B S hS Y V
    fun i => diagonalComplementProj B S hS X W c hc hsep n V e i ≫ j i

/-- The `i`-th component of the morphism into the finite fibre power over the base. -/
theorem diagonalComplementToOverProdObj_comp_π (Y : Fin n → BigFppfOver B S hS)
    (j : ∀ i, W ⟶ Y i) (i : Fin n) :
    diagonalComplementToOverProdObj B S hS X W c hc hsep n V e Y j ≫
        overProdObjπ B S hS Y i =
      diagonalComplementProj B S hS X W c hc hsep n V e i ≫ j i :=
  overProdObjLift_comp_π B S hS Y V _ i

/-- The inclusion of the complement of the diagonals into the self-product, precomposed with
`e`, is an open immersion out of the presheaf represented by `V`. -/
theorem isOpenImmersion_diagonalComplementObjι :
    IsOpenImmersion B S hS (e.hom ≫ ((toSpaces B S hS X).map
      (diagonalComplementι B S hS X (chartObj B S hS X W c hc) n hsep)).hom) :=
  isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS e.hom)
    (isOpenImmersion_diagonalComplementι B S hS X (chartObj B S hS X W c hc) n hsep)

include e in
/-- If `X` is quasi-compact and the chart is a quasi-compact morphism, the underlying scheme of
`V` is quasi-compact. -/
theorem compactSpace_of_iso_underlying_diagonalComplement
    (hXqc : IsQuasiCompactSpace B S hS X.obj) (hcqc : IsQuasiCompact B S hS c) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj V) :=
  compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (IsQuasiCompactSpace.of_iso B S hS
      (isQuasiCompactSpace_underlying_diagonalComplement B S hS X
        (chartObj B S hS X W c hc) hXqc hcqc n hsep) e.symm)

end Projections

/-! ### The complement of the diagonals with its structure -/

/-- Let `c : W ⟶ X` be an étale chart of a quasi-compact algebraic space over `S` which is
separated and quasi-compact as a morphism, and let `j` be a family of morphisms from the chart
into `n + 1` objects `Y i` of the site. Then there are:

* an object `V` of the big fppf category over `S`, the `(n+1)`-fold self-product of the chart
  over `X` with all its diagonals removed;
* its `n + 1` projections `p i : V ⟶ W`, which all lie over one and the same morphism
  `V ⟶ X`;
* the morphism `h : V ⟶ Y ×_S ⋯ ×_S Y` into the finite fibre power over the base whose `i`-th
  component is `p i` followed by `j i`;
* quasi-compactness of the underlying scheme of `V`. -/
theorem exists_diagonalComplementObj (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj)
    (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (hXqc : IsQuasiCompactSpace B S hS X.obj) (hcqc : IsQuasiCompact B S hS c) (n : ℕ)
    (Y : Fin (n + 1) → BigFppfOver B S hS) (j : ∀ i, W ⟶ Y i) :
    ∃ (V : BigFppfOver B S hS) (p : Fin (n + 1) → (V ⟶ W))
      (h : V ⟶ overProdObj B S hS Y),
      (∀ i, h ≫ overProdObjπ B S hS Y i = p i ≫ j i) ∧
        (∀ i i', yoneda.map (p i) ≫ c = yoneda.map (p i') ≫ c) ∧
        CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := by
  obtain ⟨V, ⟨e⟩⟩ := exists_siteObj_iso_underlying_diagonalComplement B S hS X
    (chartObj B S hS X W c hc) (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj W))) n hsep
  exact ⟨V, fun i => diagonalComplementProj B S hS X W c hc hsep (n + 1) V e i,
    diagonalComplementToOverProdObj B S hS X W c hc hsep (n + 1) V e Y j,
    diagonalComplementToOverProdObj_comp_π B S hS X W c hc hsep (n + 1) V e Y j,
    yoneda_map_diagonalComplementProj_comp_chart_eq B S hS X W c hc hsep (n + 1) V e,
    compactSpace_of_iso_underlying_diagonalComplement B S hS X W c hc hsep (n + 1) V e
      hXqc hcqc⟩

end AlgebraicGeometry.Space.SpacesEtale

end
