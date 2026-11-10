module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality.ChartGluing

/-!
# Functoriality of the conormal algebra: the canonical morphism

For a commutative square of schemes with immersions `i : Z ⟶ X` and `i' : Z' ⟶ X'`, this file
defines morphisms of the conormal graded algebras over the square, their affine
characterisation, and constructs the canonical one by gluing the chart maps of `ChartGluing`.

## Main definitions

* `AlgebraicGeometry.ConormalAlgebraHom`: a morphism of the conormal graded algebras over the
  square, presented by its maps on sections over compatible opens.
* `AlgebraicGeometry.ConormalAlgebraHom.IsCanonical`: the affine characterisation.
* `AlgebraicGeometry.CanonicalConormalAlgebraHom`: such a morphism satisfying the affine
  characterisation, together with its uniqueness.

## Main results

* `AlgebraicGeometry.conormalAlgebraHom`: **Stacks Tag 0634**, the unique morphism with the
  affine description.

## Implementation notes

A morphism of graded algebras out of a pullback is recorded here by its adjoint data: a family
of additive maps `𝒞_{Z'/X',n}(W) ⟶ 𝒞_{Z/X,n}(V)`, one for each pair of opens with
`V ⊆ f⁻¹W`, compatible with restriction in both arguments, semilinear over `f^♯`, and
multiplicative with the unit.  This avoids naming the pullback sheaf while constructing the
map; the sheaf-level form is recovered by the adjunction.

The map is built from its values on the affine charts.  Those charts cover any open of `Z`
(`conormalChart_cover`), two of them are refined by a common family of charts
(`conormalChartRefinement_cover`), and that is what glues the local maps and makes them
independent of the chart.  Negative degrees are zero on both sides, so the morphism there is
the zero map.

## References

* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u

namespace AlgebraicGeometry

private theorem sheaf_sections_ext_of_cover
    {T : TopCat.{u}} (G : TopCat.Sheaf Ab.{u} T) (V : TopologicalSpace.Opens T)
    {ι : Type u} (U : ι → TopologicalSpace.Opens T) (iUV : ∀ j, U j ⟶ V)
    (hcover : V ≤ ⨆ j, U j) (x y : G.1.obj (op V))
    (hxy : ∀ j, G.1.map (iUV j).op x = G.1.map (iUV j).op y) : x = y :=
  G.eq_of_locally_eq' U V iUV hcover x y hxy

/-- A morphism of the conormal graded algebras over a commutative square.
The sectionwise form is equivalent to a graded algebra morphism out of the
pullback along `f`. -/
structure ConormalAlgebraHom {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    [IsImmersion i] [IsImmersion i'] where
  /-- The homogeneous maps on compatible opens. -/
  map (n : ℤ) (V : Z.Opens) (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) :
    ((Stacks.Conormal.conormalAlgebra i').algebra.piece n).val.obj (op W) →+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.obj (op V)
  /-- Compatibility with restriction on the target. -/
  map_restrict_target (n : ℤ) (V V' : Z.Opens) (hV'V : V' ≤ V)
      (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) (a) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map
        (homOfLE hV'V).op (map n V W hVW a) =
      map n V' W (le_trans hV'V hVW) a
  /-- Compatibility with restriction on the source. -/
  map_restrict_source (n : ℤ) (V : Z.Opens) (W W' : Z'.Opens)
      (hW'W : W' ≤ W) (hVW' : V ≤ f ⁻¹ᵁ W')
      (hVW : V ≤ f ⁻¹ᵁ W) (a) :
    map n V W' hVW'
        (((Stacks.Conormal.conormalAlgebra i').algebra.piece n).val.map
          (homOfLE hW'W).op a) = map n V W hVW a
  /-- The map is linear over the structural map on functions. -/
  map_smul (n : ℤ) (V : Z.Opens) (W : Z'.Opens)
      (hVW : V ≤ f ⁻¹ᵁ W) (r : Γ(Z', W)) (a) :
    map n V W hVW
        ((show Z'.ringCatSheaf.obj.obj (op W) from r) • a) =
      (show Z.ringCatSheaf.obj.obj (op V) from
        Z.presheaf.map (homOfLE hVW).op ((f.app W).hom r)) •
        map n V W hVW a
  /-- Multiplication of homogeneous sections is preserved. -/
  map_mul (n m : ℤ) (V : Z.Opens) (W : Z'.Opens)
      (hVW : V ≤ f ⁻¹ᵁ W) (a b) :
    map (n + m) V W hVW
        (((Stacks.Conormal.conormalAlgebra i').algebra.mul n m).app (op W) a b) =
      ((Stacks.Conormal.conormalAlgebra i).algebra.mul n m).app (op V)
        (map n V W hVW a) (map m V W hVW b)
  /-- The global unit is preserved. -/
  map_one (V : Z.Opens) (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) :
      map 0 V W hVW ((Stacks.Conormal.conormalAlgebra i').algebra.one.eval (op W)) =
      (Stacks.Conormal.conormalAlgebra i).algebra.one.eval (op V)

private noncomputable def conormalAlgebraMapAt
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℕ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W) :
    ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W) →+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op V) := by
  classical
  let G : TopCat.Sheaf Ab (TopCat.of Z) :=
    ⟨((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.presheaf,
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).isSheaf⟩
  let charts := fun j : ConormalChartIndex i i' f g V W => conormalChartOpen j
  let inc := fun j => homOfLE (show charts j ≤ V from fun _ hz => j.source_subset hz)
  let cover := conormalChart_cover i i' f g comm V W hVW
  let maps := fun j => conormalChartHom i i' f g comm V W hVW n j
  exact gluingAddMonoidHom G V charts inc cover maps
    (fun a => conormalChartHom_compatible i i' f g comm V W hVW n a)

private lemma conormal_sections_ext {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (n : ℤ) (V : Z.Opens) {ι : Type u}
    (P : ι → Z.Opens) (hPV : ∀ j, P j ≤ V) (hcover : V ≤ ⨆ j, P j)
    (x y : ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.obj (op V))
    (hxy : ∀ j, ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map
      (homOfLE (hPV j)).op x =
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map
        (homOfLE (hPV j)).op y) : x = y := by
  let M := (Stacks.Conormal.conormalAlgebra i).algebra.piece n
  exact sheaf_sections_ext_of_cover ⟨M.val.presheaf, M.isSheaf⟩ V P
    (fun j => homOfLE (hPV j)) hcover x y hxy

/-- **Two homogeneous local sections of a conormal algebra agree as soon as they agree on the
affine charts of a commutative square.** Those charts cover the open in question
(`AlgebraicGeometry.conormalChart_cover`), and a homogeneous piece of the conormal algebra is a
sheaf. -/
private lemma conormal_sections_ext_charts
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℤ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W)
    (x y : ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.obj (op V))
    (hxy : ∀ j : ConormalChartIndex i i' f g V W,
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map
        (homOfLE j.source_subset).op x =
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map
        (homOfLE j.source_subset).op y) : x = y :=
  conormal_sections_ext i n V conormalChartOpen (fun j => j.source_subset)
    (conormalChart_cover i i' f g comm V W hVW) x y hxy

private theorem conormalAlgebraMapAt_restrict
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℕ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W) (j : ConormalChartIndex i i' f g V W) (a) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
      (homOfLE (show conormalChartOpen j ≤ V from j.source_subset)).op
      (conormalAlgebraMapAt i i' f g comm n V W hVW a) =
      conormalChartHom i i' f g comm V W hVW n j a := by
  let G : TopCat.Sheaf Ab (TopCat.of Z) :=
    ⟨((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.presheaf,
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).isSheaf⟩
  let charts := fun j : ConormalChartIndex i i' f g V W => conormalChartOpen j
  let inc := fun j => homOfLE (show charts j ≤ V from fun _ hz => j.source_subset hz)
  let cover := conormalChart_cover i i' f g comm V W hVW
  let maps := fun j => conormalChartHom i i' f g comm V W hVW n j
  dsimp [conormalAlgebraMapAt, G, charts, inc, cover, maps]
  exact gluingAddMonoidHom_map G V charts inc cover maps
    (fun a => conormalChartHom_compatible i i' f g comm V W hVW n a) j a

private theorem conormalAlgebraMapAt_restrict_source
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℕ) (V₀ V : Z.Opens) (W : Z'.Opens)
    (hV₀V : V₀ ≤ V) (hV₀W : V₀ ≤ f ⁻¹ᵁ W) (hVW : V ≤ f ⁻¹ᵁ W)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W)) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
      (homOfLE (show V₀ ≤ V from hV₀V)).op
      (conormalAlgebraMapAt i i' f g comm n V W hVW x) =
      conormalAlgebraMapAt i i' f g comm n V₀ W hV₀W x := by
  apply conormal_sections_ext_charts i i' f g comm (n : ℤ) V₀ W hV₀W
  intro j
  let jp : ConormalChartIndex i i' f g V W := { j with
    source_subset := fun _ hz => hV₀V (j.source_subset hz) }
  rw [← PresheafOfModules.map_comp_apply]
  exact (conormalAlgebraMapAt_restrict i i' f g comm n V W hVW jp x).trans
    (((conormalChartHom_apply i i' f g comm V W hVW n jp x).trans
      (conormalChartHom_apply i i' f g comm V₀ W hV₀W n j x).symm).trans
      (conormalAlgebraMapAt_restrict i i' f g comm n V₀ W hV₀W j x).symm)

private theorem conormalAlgebraMapAt_restrict_target
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℕ) (V : Z.Opens) (W₀ W : Z'.Opens)
    (hW₀W : W₀ ≤ W) (hVW₀ : V ≤ f ⁻¹ᵁ W₀) (hVW : V ≤ f ⁻¹ᵁ W)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W)) :
    conormalAlgebraMapAt i i' f g comm n V W₀ hVW₀
      (((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.map
        (homOfLE hW₀W).op x) =
    conormalAlgebraMapAt i i' f g comm n V W hVW x := by
  apply conormal_sections_ext_charts i i' f g comm (n : ℤ) V W₀ hVW₀
  intro j
  let jp : ConormalChartIndex i i' f g V W := { j with
    target_subset := le_trans j.target_subset hW₀W }
  refine (conormalAlgebraMapAt_restrict i i' f g comm n V W₀ hVW₀ j _).trans
    ((conormalChartHom_apply i i' f g comm V W₀ hVW₀ n j _).trans ?_)
  rw [← PresheafOfModules.map_comp_apply]
  exact ((conormalChartHom_apply i i' f g comm V W hVW n jp x).symm.trans
    (conormalAlgebraMapAt_restrict i i' f g comm n V W hVW jp x).symm)

private theorem conormalChartHom_smul
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (V : Z.Opens) (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) (n : ℕ)
    (j : ConormalChartIndex i i' f g V W) (r : Γ(Z', W))
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W)) :
    conormalChartHom i i' f g comm V W hVW n j
        ((show Z'.ringCatSheaf.obj.obj (op W) from r) • a) =
      (show Z.ringCatSheaf.obj.obj (op (conormalChartOpen j)) from
        Z.presheaf.map (homOfLE
          (square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
            j.ambient_compatible)).op
          ((f.app (i' ⁻¹ᵁ j.U'.1)).hom
            ((Z'.presheaf.map (homOfLE j.target_subset).op).hom r))) •
        conormalChartHom i i' f g comm V W hVW n j a := by
  rw [conormalChartHom_apply, conormalChartHom_apply]
  rw [PresheafOfModules.map_smul]
  exact chartConormalMap_smul i i' f g comm j.U j.U' j.ambient_compatible
    (isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder)
    (isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder)
    (square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
      j.ambient_compatible) n
    ((Z'.presheaf.map (homOfLE j.target_subset).op).hom r)
    ((((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.map
      (homOfLE j.target_subset).op).hom a)

private theorem ConormalAlgebraHom.ext
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'}
    [IsImmersion i] [IsImmersion i'] (H K : ConormalAlgebraHom i i' f)
    (hmap : ∀ (n : ℤ) (V : Z.Opens) (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) (x),
      H.map n V W hVW x = K.map n V W hVW x) : H = K := by
  cases H with
  | mk h₁ h₂ h₃ h₄ h₅ h₆ =>
    cases K with
    | mk k₁ k₂ k₃ k₄ k₅ k₆ =>
      have hm : h₁ = k₁ := by
        funext n V W hVW
        apply AddMonoidHom.ext
        intro x
        exact hmap n V W hVW x
      subst k₁
      rfl

/-- The affine quotient description of a map between conormal algebras. -/
def ConormalAlgebraHom.IsCanonical {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (H : ConormalAlgebraHom i i' f) : Prop :=
  ∀ (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : (i ⁻¹ᵁ U.1) ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1))
    (n : ℕ) (a : ↥(Stacks.Conormal.chartIdeal i' U' ^ n))
    (b : ↥(Stacks.Conormal.chartIdeal i U ^ n)),
      (b : Γ(X, U.1)) =
        X.presheaf.map (homOfLE hGU).op ((g.app U'.1).hom (a : Γ(X', U'.1))) →
      H.map (n : ℤ) (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ U'.1) hFU
          ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a) =
        (Stacks.Conormal.conormalAlgebra i).localMap U hZU n b

private theorem ConormalAlgebraHom.IsCanonical.map_eq_chartConormalMap
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (H : ConormalAlgebraHom i i' f)
    (hH : ConormalAlgebraHom.IsCanonical i i' f g H)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1))) :
    H.map (n : ℤ) (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ U'.1) hFU x =
      chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n x := by
  obtain ⟨a, rfl⟩ :=
    (Stacks.Conormal.conormalAlgebra i').localMap_surjective U' hZ'U' n x
  let b : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
    ⟨X.presheaf.map (homOfLE hGU).op ((g.app U'.1).hom (a : Γ(X', U'.1))),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩
  have hb : (b : Γ(X, U.1)) =
      X.presheaf.map (homOfLE hGU).op ((g.app U'.1).hom (a : Γ(X', U'.1))) := rfl
  let b' : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
    ⟨(g.appLE U'.1 U.1 hGU).hom (a : Γ(X', U'.1)),
      chartIdealPow_map_mem i i' f g comm U U' hGU hFU n a⟩
  have hb' : b = b' := by
    apply Subtype.ext
    change (g.app U'.1 ≫ X.presheaf.map (homOfLE hGU).op).hom
        (a : Γ(X', U'.1)) =
      (g.app U'.1 ≫ X.presheaf.map (homOfLE hGU).op).hom
        (a : Γ(X', U'.1))
    rfl
  calc
    H.map (n : ℤ) (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ U'.1) hFU
        ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a) =
      (Stacks.Conormal.conormalAlgebra i).localMap U hZU n b :=
        hH U U' hGU hZU hZ'U' hFU n a b hb
    _ = (Stacks.Conormal.conormalAlgebra i).localMap U hZU n b' := by rw [hb']
    _ = chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n
        ((Stacks.Conormal.conormalAlgebra i').localMap U' hZ'U' n a) :=
      (chartConormalMap_localMap i i' f g comm U U' hGU hZU hZ'U' hFU n a).symm

/-- The canonical graded algebra morphism induced by a commutative square of
immersions, together with its affine characterization and uniqueness. -/
structure CanonicalConormalAlgebraHom {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] where
  /-- The graded algebra morphism between the conormal algebras. -/
  hom : ConormalAlgebraHom i i' f
  /-- The ambient ring map carries every ideal power into the corresponding
  ideal power on compatible affine closed-immersion charts. -/
  map_ideal_pow (U : X.affineOpens) (U' : X'.affineOpens)
      (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
      (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
      (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
      (n : ℕ) (a : ↥(Stacks.Conormal.chartIdeal i' U' ^ n)) :
    X.presheaf.map (homOfLE hGU).op ((g.app U'.1).hom (a : Γ(X', U'.1))) ∈
      Stacks.Conormal.chartIdeal i U ^ n
  /-- On affine charts, `hom` is induced by the ring maps of `g`. -/
  chart : ConormalAlgebraHom.IsCanonical i i' f g hom
  /-- Every morphism with the affine characterization equals `hom`. -/
  unique (H : ConormalAlgebraHom i i' f) (hH : ConormalAlgebraHom.IsCanonical i i' f g H) : H = hom

private lemma conormalPiece_negative_subsingleton {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (n : ℤ) (hn : n < 0) (V : Z.Opens) :
    Subsingleton (((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.obj (op V)) := by
  let F := (Stacks.Conormal.conormalAlgebra i).algebra.piece n
  have hzero : CategoryTheory.Limits.IsZero ((Stacks.Conormal.conormalAlgebra i).algebra.piece n) :=
    (Stacks.Conormal.conormalAlgebra i).negative_isZero n hn
  have hid : 𝟙 F = 0 := (CategoryTheory.Limits.IsZero.iff_id_eq_zero F).mp hzero
  have hzeroVal : (0 : F ⟶ F).val = 0 := by
    change (SheafOfModules.forget Z.ringCatSheaf).map
      (0 : F ⟶ F) = 0
    exact (SheafOfModules.forget Z.ringCatSheaf).map_zero F F
  have hidVal : 𝟙 F.val = 0 := by
    have hval := congrArg (fun q : F ⟶ F => q.val) hid
    rw [SheafOfModules.id_val, hzeroVal] at hval
    exact hval
  refine ⟨fun x y => ?_⟩
  have hx : x = 0 := by
    have h := congrArg (fun q : F.val ⟶ F.val => (q.app (op V)).hom x) hidVal
    simpa using h
  have hy : y = 0 := by
    have h := congrArg (fun q : F.val ⟶ F.val => (q.app (op V)).hom y) hidVal
    simpa using h
  exact hx.trans hy.symm

/-- **Two homogeneous local sections of a conormal algebra agree as soon as they agree on the
affine charts of a commutative square**, with the charts spelled out: pairs of affine opens
`U ⊆ X` and `U' ⊆ X'` with `i⁻¹U ⊆ V` and `i'⁻¹U' ⊆ W`, on which both immersions restrict to
closed immersions and which `g` is compatible with. Those charts cover `V`
(`AlgebraicGeometry.conormalChart_cover`), and a homogeneous piece of the conormal algebra is a
sheaf. -/
lemma conormal_sections_ext_of_affineCharts
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℤ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W)
    (x y : ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.obj (op V))
    (hxy : ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : i ⁻¹ᵁ U.1 ≤ V)
      (_hU' : i' ⁻¹ᵁ U'.1 ≤ W) (_hcob : U.1 ≤ i.coborderRange)
      (_hcob' : U'.1 ≤ i'.coborderRange) (_hg : U.1 ≤ g ⁻¹ᵁ U'.1),
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map (homOfLE hU).op x =
        ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.map (homOfLE hU).op y) :
    x = y :=
  conormal_sections_ext_charts i i' f g comm n V W hVW x y fun j =>
    hxy j.U j.U' j.source_subset j.target_subset j.source_coborder j.target_coborder
      j.ambient_compatible

private lemma conormalAlgebraMapAt_smul
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℕ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W) (r : Γ(Z', W))
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W)) :
    conormalAlgebraMapAt i i' f g comm n V W hVW
        ((show Z'.ringCatSheaf.obj.obj (op W) from r) • a) =
      (show Z.ringCatSheaf.obj.obj (op V) from (f.appLE W V hVW).hom r) •
        conormalAlgebraMapAt i i' f g comm n V W hVW a := by
  apply conormal_sections_ext_charts i i' f g comm (n : ℤ) V W hVW
  intro j
  have heq : Z'.presheaf.map (homOfLE j.target_subset).op ≫
      f.appLE (i' ⁻¹ᵁ j.U'.1) (i ⁻¹ᵁ j.U.1)
        (square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
          j.ambient_compatible) =
      f.appLE W V hVW ≫ Z.presheaf.map (homOfLE j.source_subset).op := by
    rw [f.map_appLE, f.appLE_map]
  have hscal : (show Z.ringCatSheaf.obj.obj (op (conormalChartOpen j)) from
        Z.presheaf.map (homOfLE
            (square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
              j.ambient_compatible)).op
          ((f.app (i' ⁻¹ᵁ j.U'.1)).hom
            ((Z'.presheaf.map (homOfLE j.target_subset).op).hom r))) =
      Z.ringCatSheaf.obj.map (homOfLE j.source_subset).op
        (show Z.ringCatSheaf.obj.obj (op V) from (f.appLE W V hVW).hom r) :=
    congrArg (fun q : Γ(Z', W) ⟶ Γ(Z, i ⁻¹ᵁ j.U.1) => q.hom r) heq
  exact (conormalAlgebraMapAt_restrict i i' f g comm n V W hVW j _).trans
    ((conormalChartHom_smul i i' f g comm V W hVW n j r a).trans
      ((congrArg₂ (· • ·) hscal
          (conormalAlgebraMapAt_restrict i i' f g comm n V W hVW j a).symm).trans
        (PresheafOfModules.map_smul
          ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val
          (homOfLE j.source_subset).op
          (show Z.ringCatSheaf.obj.obj (op V) from (f.appLE W V hVW).hom r)
          (conormalAlgebraMapAt i i' f g comm n V W hVW a)).symm))

/-- Naturality of the degree-`(n, m)` product of the conormal graded algebra, with the target
degree written as the cast `((n + m : ℕ) : ℤ)` of a sum of natural numbers rather than as the
sum `(n : ℤ) + (m : ℤ)` of two casts. The two integers are definitionally equal, but only the
former spelling occurs in the goals coming from `conormalAlgebraMapAt`, which is indexed by a
natural number. -/
private theorem conormalMul_naturality_natCast
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (n m : ℕ)
    {U V : Z.Opensᵒᵖ} (h : U ⟶ V)
    (x : ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj U)
    (y : ((Stacks.Conormal.conormalAlgebra i).algebra.piece (m : ℤ)).val.obj U) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece ((n + m : ℕ) : ℤ)).val.map h
        (((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app U x y) =
      ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app V
        (((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map h x)
        (((Stacks.Conormal.conormalAlgebra i).algebra.piece (m : ℤ)).val.map h y) :=
  ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).naturality h x y

private lemma conormalAlgebraMapAt_mul
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n m : ℕ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W)
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W))
    (b : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (m : ℤ)).val.obj (op W)) :
    conormalAlgebraMapAt i i' f g comm (n + m) V W hVW
      (((Stacks.Conormal.conormalAlgebra i').algebra.mul (n : ℤ) (m : ℤ)).app (op W) a b) =
    ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app (op V)
      (conormalAlgebraMapAt i i' f g comm n V W hVW a)
      (conormalAlgebraMapAt i i' f g comm m V W hVW b) := by
  apply conormal_sections_ext_charts i i' f g comm ((n + m : ℕ) : ℤ) V W hVW
  intro j
  have hZU := isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder
  have hZ'U' := isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder
  have hFU := square_chart_preimage_le i i' f g comm j.U.1 j.U'.1 j.ambient_compatible
  have ha := (conormalAlgebraMapAt_restrict i i' f g comm n V W hVW j a).trans
    (conormalChartHom_apply i i' f g comm V W hVW n j a)
  have hb := (conormalAlgebraMapAt_restrict i i' f g comm m V W hVW j b).trans
    (conormalChartHom_apply i i' f g comm V W hVW m j b)
  exact (conormalAlgebraMapAt_restrict i i' f g comm (n + m) V W hVW j _).trans
    ((conormalChartHom_apply i i' f g comm V W hVW (n + m) j _).trans
      ((congrArg (fun x => chartConormalMap i i' f g comm j.U j.U' j.ambient_compatible
              hZU hZ'U' hFU (n + m) x)
            (((Stacks.Conormal.conormalAlgebra i').algebra.mul (n : ℤ) (m : ℤ)).naturality
              (homOfLE j.target_subset).op a b)).trans
        ((chartConormalMap_mul i i' f g comm j.U j.U' j.ambient_compatible
              hZU hZ'U' hFU n m _ _).trans
          ((congrArg₂ (fun x y =>
                ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app
                  (op (conormalChartOpen j)) x y) ha.symm hb.symm).trans
            (((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).naturality
              (homOfLE j.source_subset).op _ _).symm))))

private lemma conormalAlgebraMapAt_one
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W) :
    conormalAlgebraMapAt i i' f g comm 0 V W hVW
      ((Stacks.Conormal.conormalAlgebra i').algebra.one.eval (op W)) =
      (Stacks.Conormal.conormalAlgebra i).algebra.one.eval (op V) := by
  apply conormal_sections_ext_charts i i' f g comm 0 V W hVW
  intro j
  refine (conormalAlgebraMapAt_restrict i i' f g comm 0 V W hVW j _).trans
    ((conormalChartHom_apply i i' f g comm V W hVW 0 j _).trans ?_)
  simp only [PresheafOfModules.sections.eval, PresheafOfModules.sections_property]
  exact chartConormalMap_one i i' f g comm j.U j.U' j.ambient_compatible
    (isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder)
    (isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder)
    (square_chart_preimage_le i i' f g comm j.U.1 j.U'.1 j.ambient_compatible)

private lemma conormalAlgebraMapAt_chart
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g)
    (U : X.affineOpens) (U' : X'.affineOpens) (hGU : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hFU : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1)) (n : ℕ)
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1))) :
    conormalAlgebraMapAt i i' f g comm n (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ U'.1) hFU a =
      chartConormalMap i i' f g comm U U' hGU hZU hZ'U' hFU n a := by
  let J := ConormalChartRefinement i i' f g (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ U'.1) U.1 U'.1
  apply conormal_sections_ext i (n : ℤ) (i ⁻¹ᵁ U.1)
    (fun j : J => i ⁻¹ᵁ j.U.1) (fun j => j.source_subset)
    (conormalChartRefinement_cover i i' f g comm _ _ U.1 U'.1 le_rfl le_rfl hFU)
  intro j
  let c : ConormalChartIndex i i' f g (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ U'.1) := {
    U := j.U
    U' := j.U'
    source_subset := j.source_subset
    target_subset := j.target_subset
    source_coborder := j.source_coborder
    target_coborder := j.target_coborder
    ambient_compatible := j.ambient_compatible }
  exact (conormalAlgebraMapAt_restrict i i' f g comm n _ _ hFU c a).trans
    ((conormalChartHom_apply i i' f g comm _ _ hFU n c a).trans
      (chartConormalMap_restrict_both i i' f g comm U j.U U' j.U'
        j.source_refines j.target_refines hGU j.ambient_compatible hZU
        (isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder) hZ'U'
        (isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder) hFU
        (square_chart_preimage_le i i' f g comm j.U.1 j.U'.1 j.ambient_compatible)
        n a).symm)

private lemma ConormalAlgebraHom.IsCanonical.map_eq_glued
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (H : ConormalAlgebraHom i i' f)
    (hH : ConormalAlgebraHom.IsCanonical i i' f g H) (n : ℕ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W)
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W)) :
    H.map (n : ℤ) V W hVW a = conormalAlgebraMapAt i i' f g comm n V W hVW a := by
  apply conormal_sections_ext_charts i i' f g comm (n : ℤ) V W hVW
  intro j
  have hFU := square_chart_preimage_le i i' f g comm j.U.1 j.U'.1 j.ambient_compatible
  exact (H.map_restrict_target (n : ℤ) V (conormalChartOpen j) j.source_subset W hVW a).trans
    (((H.map_restrict_source (n : ℤ) (i ⁻¹ᵁ j.U.1) W (i' ⁻¹ᵁ j.U'.1) j.target_subset
          hFU (le_trans j.source_subset hVW) a).symm).trans
      ((ConormalAlgebraHom.IsCanonical.map_eq_chartConormalMap i i' f g comm H hH j.U j.U'
            j.ambient_compatible
            (isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder)
            (isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder)
            hFU n _).trans
        ((conormalAlgebraMapAt_restrict i i' f g comm n V W hVW j a).trans
          (conormalChartHom_apply i i' f g comm V W hVW n j a)).symm))

private noncomputable def conormalMapDegree
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) (n : ℤ) (V : Z.Opens) (W : Z'.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W) :
    ((Stacks.Conormal.conormalAlgebra i').algebra.piece n).val.obj (op W) →+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece n).val.obj (op V) :=
  match n with
  | .ofNat k => conormalAlgebraMapAt i i' f g comm k V W hVW
  | .negSucc _ => 0

private noncomputable def gluedConormalAlgebraHom
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') [IsImmersion i] [IsImmersion i']
    (comm : f ≫ i' = i ≫ g) : ConormalAlgebraHom i i' f where
  map := conormalMapDegree i i' f g comm
  map_restrict_target n V V' hV'V W hVW a := by
    cases n with
    | ofNat k =>
      exact conormalAlgebraMapAt_restrict_source
        i i' f g comm k V' V W hV'V (le_trans hV'V hVW) hVW a
    | negSucc k =>
      exact map_zero (((Stacks.Conormal.conormalAlgebra i).algebra.piece
        (Int.negSucc k)).val.map (homOfLE hV'V).op).hom
  map_restrict_source n V W W' hW'W hVW' hVW a := by
    cases n with
    | ofNat k =>
      exact conormalAlgebraMapAt_restrict_target
        i i' f g comm k V W' W hW'W hVW' hVW a
    | negSucc k => rfl
  map_smul n V W hVW r a := by
    cases n with
    | ofNat k => exact conormalAlgebraMapAt_smul i i' f g comm k V W hVW r a
    | negSucc k =>
      change (0 : ((Stacks.Conormal.conormalAlgebra i).algebra.piece
        (Int.negSucc k)).val.obj (op V)) = _ • 0
      exact (smul_zero _).symm
  map_mul n m V W hVW a b := by
    by_cases hn : n < 0
    · have := conormalPiece_negative_subsingleton i' n hn W
      have ha : a = 0 := Subsingleton.elim _ _
      rw [ha]
      simp only [map_zero, AddMonoidHom.zero_apply]
    · by_cases hm : m < 0
      · have := conormalPiece_negative_subsingleton i' m hm W
        have hb : b = 0 := Subsingleton.elim _ _
        rw [hb]
        simp only [map_zero]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hn)
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hm)
        exact conormalAlgebraMapAt_mul i i' f g comm n m V W hVW a b
  map_one V W hVW := conormalAlgebraMapAt_one i i' f g comm V W hVW

/-- **Stacks Project, Tag 0634.** The unique morphism of conormal graded
algebras over a commutative square of immersions is induced on every affine
closed-immersion chart by the ring map on ideal-power quotients. -/
@[stacks 0634]
noncomputable def conormalAlgebraHom {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g) :
    CanonicalConormalAlgebraHom i i' f g := Classical.choice (by
  refine ⟨?_⟩
  refine ⟨gluedConormalAlgebraHom i i' f g comm, ?_, ?_, ?_⟩
  · intro U U' hGU hZU hZ'U' n a
    exact chartIdealPow_map_mem i i' f g comm U U' hGU
      (square_chart_preimage_le i i' f g comm U.1 U'.1 hGU) n a
  · intro U U' hGU hZU hZ'U' hFU n a b hb
    change conormalAlgebraMapAt i i' f g comm n _ _ hFU _ = _
    rw [conormalAlgebraMapAt_chart i i' f g comm U U' hGU hZU hZ'U' hFU n,
      chartConormalMap_localMap]
    congr 1
    apply Subtype.ext
    exact hb.symm
  · intro H hH
    apply ConormalAlgebraHom.ext
    intro n V W hVW a
    cases n with
    | ofNat k => exact ConormalAlgebraHom.IsCanonical.map_eq_glued i i' f g comm H hH k V W hVW a
    | negSucc k =>
      have := conormalPiece_negative_subsingleton i (Int.negSucc k) (by simp) V
      exact Subsingleton.elim _ _)

end AlgebraicGeometry

end
